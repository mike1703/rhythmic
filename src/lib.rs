use std::thread;
use std::time::Duration;
use std::time::Instant;

/// `TimeInterval` allows waiting for regular intervals, regardless of task duration.
///
/// A `tick()` always waits at least until `last_interval_start + interval`.
///
/// The `overrun_behavior` determines how the interval reacts to overruns.
///
/// Example:
///
/// ```
/// use std::time::{Duration, Instant};
/// use rhythmic;
///
/// let interval = Duration::from_millis(10);
/// let mut time_interval = rhythmic::TimeInterval::new(interval);
/// // first tick() returns immediately
/// time_interval.tick();
/// let pre = Instant::now();
/// // second tick() returns after the interval
/// time_interval.tick();
/// let post = Instant::now();
/// assert_eq!(post.duration_since(pre).as_millis(), interval.as_millis());
/// ```
#[derive(Debug)]
pub struct TimeInterval {
    /// The interval between ticks.
    interval: Duration,
    /// The start time of the last interval that was used for the last tick().
    last_interval_start: Option<Instant>,
    /// The duration of the last sleep.
    last_sleep_duration: Option<Duration>,
    /// The behavior when an interval is overrun.
    overrun_behavior: OverrunBehavior,
}

/// Defines the behavior when an interval is overrun.
#[derive(Debug, Default)]
pub enum OverrunBehavior {
    #[default]
    /// Waits until the next regular interval start.
    AwaitNextInterval,
    /// Waits for the specified interval and adjusts the timing.
    WaitInterval,
    /// Returns immediately without waiting.
    ImmediateReturn,
}

impl TimeInterval {
    /// Creates a new `TimeInterval` with the default overrun behavior.
    #[must_use]
    pub fn new(interval: Duration) -> Self {
        Self {
            interval,
            last_interval_start: None,
            last_sleep_duration: None,
            overrun_behavior: OverrunBehavior::default(),
        }
    }

    /// Sets the interval.
    #[must_use]
    pub fn with_interval(mut self, interval: Duration) -> Self {
        self.interval = interval;
        self
    }

    /// Sets the overrun behavior.
    #[must_use]
    pub fn with_behavior(mut self, overrun_behavior: OverrunBehavior) -> Self {
        self.overrun_behavior = overrun_behavior;
        self
    }

    /// Rounds a duration down to the nearest multiple of the interval on microsecond resolution.
    ///
    /// `Duration(result_us) = value_us // interval_us * interval_us`
    ///
    /// Example:
    /// ```ignore
    /// use std::time::Duration;
    /// use rhythmic::TimeInterval;
    /// let value = Duration::from_secs(123);
    /// let interval = Duration::from_secs(10);
    /// assert_eq!(TimeInterval::round_to_interval_start(value, interval), Duration::from_secs(120));
    /// ```
    fn round_to_interval_start(value: Duration, interval: Duration) -> Duration {
        let value_us = value.as_micros();
        let interval_us = interval.as_micros();
        let interval_start = value_us / interval_us * interval_us;
        Duration::from_micros(
            interval_start
                .try_into()
                .expect("duration in us is too big"),
        )
    }

    /// Calculates the latest interval start that is less than or equal to `now`.
    /// `previous_interval_start = interval_start + n * interval <= now` for the biggest `n`.
    ///
    /// This should only be called if `interval_start` < `now`.
    ///
    /// Example:
    /// ```ignore
    /// use std::time::{Duration, Instant};
    /// use rhythmic::TimeInterval;
    /// let interval_start = Instant::now();
    /// let interval = Duration::from_secs(2);
    /// let now = interval_start + Duration::from_secs(5);
    /// assert_eq!(TimeInterval::previous_interval_start(interval_start, now, interval),
    ///            interval_start + Duration::from_secs(4));
    /// ```
    fn previous_interval_start(
        interval_start: Instant,
        now: Instant,
        interval: Duration,
    ) -> Instant {
        let duration_since_interval_start = now.duration_since(interval_start);
        let aligned_duration_since_interval_start =
            Self::round_to_interval_start(duration_since_interval_start, interval);
        // previous_interval_start + (duration_since_interval_start // interval * interval)
        // should be the last possible previous interval start
        let previous_interval_start = interval_start + aligned_duration_since_interval_start;
        debug_assert!(previous_interval_start <= now);
        debug_assert!(previous_interval_start > (now - interval));
        previous_interval_start
    }

    /// Calculates the target time and sleep duration for the next tick.
    ///   - time: when this tick should have returned, used as base for follow-up calls
    ///   - duration: how long should we sleep to reach the time (if the time is already
    ///               in the past, a overrun behavior is applied)
    /// Example:
    /// ```ignore
    /// use std::time::{Duration, Instant};
    /// use rhythmic::TimeInterval;
    /// let mut now = Instant::now();
    /// let interval = Duration::from_secs(2);
    /// let mut time_interval = TimeInterval::new(interval);
    /// // this does not modify any interval state
    /// let (time_a, duration_a) = time_interval.tick_time(now);
    /// // run the "outer function again to set the correct state
    /// time_interval.tick_with_current_time(now);
    /// assert_eq!(time_a, now);
    /// assert_eq!(duration_a, Duration::ZERO);
    /// // only run this "inner" function - this does not set state
    /// let (time_b, duration_b) = time_interval.tick_time(now);
    /// assert_eq!(time_b, now + interval);
    /// assert_eq!(duration_b, interval);
    /// ```
    fn tick_time(&self, now: Instant) -> (Instant, Duration) {
        let Some(last_interval_start) = self.last_interval_start else {
            // first run, this is the start of the regular intervals, don't sleep.
            return (now, Duration::ZERO);
        };
        // This is a follow up tick() call
        // calculate the next regular `last_interval_start`
        let next_interval_start = last_interval_start + self.interval;
        if next_interval_start >= now {
            // use the duration to the next start as `sleep_time`
            (next_interval_start, next_interval_start.duration_since(now))
        } else {
            // `next_interval_start` < `now` - apply configured `overrun_behavior`
            let last_missed_interval_start =
                Self::previous_interval_start(next_interval_start, now, self.interval);
            match self.overrun_behavior {
                // try to align the next run with the previous regular intervals
                OverrunBehavior::AwaitNextInterval => {
                    let next_regular_interval_start = last_missed_interval_start + self.interval;
                    // use the last missed interval start as new base and how long to sleep
                    // to the next interval start
                    (
                        next_regular_interval_start,
                        next_regular_interval_start.duration_since(now),
                    )
                }
                // wait for the configured interval, set now as new base
                OverrunBehavior::WaitInterval => (now + self.interval, self.interval),
                // no sleep for immediate return behavior but keep the interval alignment
                OverrunBehavior::ImmediateReturn => (last_missed_interval_start, Duration::ZERO),
            }
        }
    }

    /// Performs a tick, sleeping if necessary.
    /// Example:
    /// ```ignore
    /// use std::time::{Duration, Instant};
    /// use rhythmic::TimeInterval;
    /// let mut now = Instant::now();
    /// let interval = Duration::from_secs(2);
    /// let mut time_interval = TimeInterval::new(interval);
    /// time_interval.tick_with_current_time(now);
    /// println!("some work starting at <now>");
    /// time_interval.tick_with_current_time(now);
    /// println!("some work starting at <now+interval> as the function sleeps to the next interval");
    /// assert_eq!(time_interval.last_interval_start.unwrap(), now+interval);
    /// ```
    pub fn tick_with_current_time(&mut self, now: Instant) {
        let (next_last_interval_start, sleep_time) = self.tick_time(now);
        debug_assert!(next_last_interval_start <= now + self.interval);
        debug_assert!(sleep_time <= self.interval);
        thread::sleep(sleep_time);
        self.last_interval_start = Some(next_last_interval_start);
        self.last_sleep_duration = Some(sleep_time);
    }

    /// Waits for the next tick.
    pub fn tick(&mut self) {
        self.tick_with_current_time(Instant::now());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // the tests use the internal tick_with_current_time() function with a given
    // START_TIME to be able to precisely control the internal structure according
    // to the specified behavior. A regular user should always use this with
    // `time_interval.tick()` equivalent to time_interval.tick(Instant::now())

    /// a constant known start time for tests
    static START_TIME: std::sync::LazyLock<Instant> = std::sync::LazyLock::new(|| Instant::now());
    /// the regular interval for the tests
    static TEST_INTERVAL: Duration = Duration::from_millis(10);
    /// bigger than `TEST_INTERVAL` but less than `2*TEST_INTERVAL`
    static LONG_WORK_INTERVAL: Duration = Duration::from_millis(12);
    /// `2*TEST_INTERVAL - LONG_WORK_INTERVAL`
    static SHORT_SLEEP_AFTER_LONG_WORK: Duration = Duration::from_millis(8);

    #[test]
    fn test_tick() {
        // test the actual tick() function that should be used by users
        let mut time_interval = TimeInterval::new(TEST_INTERVAL);
        let start = Instant::now();
        time_interval.tick();
        let after_first_tick = Instant::now();
        // first tick returns almost immediately (not Zero because of run time for tick())
        assert!(after_first_tick.duration_since(start) < Duration::from_micros(10));
        time_interval.tick();
        let after_second_tick = Instant::now();
        // waited for `TEST_INTERVAL`
        assert!(after_second_tick.duration_since(after_first_tick) > TEST_INTERVAL);
    }

    #[test]
    fn test_first_immediate_tick() {
        let mut time_interval = TimeInterval::new(TEST_INTERVAL);
        assert_eq!(time_interval.interval, TEST_INTERVAL);
        assert_eq!(time_interval.last_interval_start, None);
        time_interval.tick_with_current_time(*START_TIME);
        // first tick returns immediately, `last_interval_start` is the current time
        assert_eq!(time_interval.last_interval_start, Some(*START_TIME));
        assert_eq!(time_interval.last_sleep_duration, Some(Duration::ZERO));
    }

    #[test]
    fn test_regular_second_tick() {
        let mut time_interval = TimeInterval::new(TEST_INTERVAL);
        // init - first tick returns immediately
        time_interval.tick_with_current_time(*START_TIME);
        assert_eq!(time_interval.last_interval_start, Some(*START_TIME));
        time_interval.tick_with_current_time(*START_TIME);
        // a regular second tick should have taken `TEST_INTERVAL` time
        assert_eq!(
            time_interval.last_interval_start,
            Some(*START_TIME + TEST_INTERVAL)
        );
        assert_eq!(time_interval.last_sleep_duration, Some(TEST_INTERVAL));
    }

    #[test]
    fn test_await_next_interval_behavior() {
        let mut time_interval = TimeInterval::new(TEST_INTERVAL);
        // init - first tick returns immediately
        time_interval.tick_with_current_time(*START_TIME);
        assert_eq!(time_interval.last_interval_start, Some(*START_TIME));
        // do some long work (longer than one test interval)
        time_interval.tick_with_current_time(*START_TIME + LONG_WORK_INTERVAL);
        // regular second tick was missed, so it sleeps until the next regular tick
        // which is less than a interval but `last_interval_start` is aligned to
        // the regular run interval
        assert_eq!(
            time_interval.last_interval_start,
            Some(*START_TIME + TEST_INTERVAL * 2)
        );
        assert_eq!(
            time_interval.last_sleep_duration,
            Some(SHORT_SLEEP_AFTER_LONG_WORK)
        );
        // test regular next tick - this should sleep for `TEST_INTERVAL` time
        time_interval.tick_with_current_time(*START_TIME + TEST_INTERVAL * 2);
        assert_eq!(
            time_interval.last_interval_start,
            Some(*START_TIME + TEST_INTERVAL * 3)
        );
        assert_eq!(time_interval.last_sleep_duration, Some(TEST_INTERVAL));
    }

    #[test]
    fn test_wait_interval_behavior() {
        let mut time_interval =
            TimeInterval::new(TEST_INTERVAL).with_behavior(OverrunBehavior::WaitInterval);
        // init - first tick returns immediately
        time_interval.tick_with_current_time(*START_TIME);
        // do some long work (longer than one test interval)
        time_interval.tick_with_current_time(*START_TIME + LONG_WORK_INTERVAL);
        // regular second tick was missed, but we expect `TEST_INTERVAL` time to be waited
        // the `last_interval_start` is adjusted to the new interval start
        assert_eq!(
            time_interval.last_interval_start,
            Some(*START_TIME + TEST_INTERVAL + LONG_WORK_INTERVAL)
        );
        assert_eq!(time_interval.last_sleep_duration, Some(TEST_INTERVAL));
        // test regular next tick - this should sleep for 1*TEST_INTERVAL time
        time_interval.tick_with_current_time(*START_TIME + LONG_WORK_INTERVAL + TEST_INTERVAL);
        assert_eq!(
            time_interval.last_interval_start,
            Some(*START_TIME + LONG_WORK_INTERVAL + TEST_INTERVAL * 2)
        );
        assert_eq!(time_interval.last_sleep_duration, Some(TEST_INTERVAL));
    }

    #[test]
    fn test_immediate_return_behavior() {
        let mut time_interval =
            TimeInterval::new(TEST_INTERVAL).with_behavior(OverrunBehavior::ImmediateReturn);
        // init - first tick returns immediately - see first_tick test
        time_interval.tick_with_current_time(*START_TIME);
        assert_eq!(time_interval.last_interval_start, Some(*START_TIME));
        // test overrun behavior - ImmediateReturn
        // do some long work (longer than one test interval)
        time_interval.tick_with_current_time(*START_TIME + LONG_WORK_INTERVAL);
        // regular second tick was missed, we expect no time to be waited to recover work
        // but the last_interval_start is set as we would have returned on the last interval start
        assert_eq!(
            time_interval.last_interval_start,
            Some(*START_TIME + TEST_INTERVAL)
        );
        assert_eq!(time_interval.last_sleep_duration, Some(Duration::ZERO));
        // test regular next tick - this should sleep for `SHORT_SLEEP_AFTER_LONG_WORK` time
        time_interval.tick_with_current_time(*START_TIME + LONG_WORK_INTERVAL);
        assert_eq!(
            time_interval.last_interval_start,
            Some(*START_TIME + TEST_INTERVAL * 2)
        );
        assert_eq!(
            time_interval.last_sleep_duration,
            Some(SHORT_SLEEP_AFTER_LONG_WORK)
        );
    }

    #[test]
    fn test_configure_new_interval() {
        let new_test_interval = TEST_INTERVAL * 2;
        let mut time_interval = TimeInterval::new(TEST_INTERVAL);
        time_interval = time_interval.with_interval(new_test_interval);
        time_interval.tick_with_current_time(*START_TIME);
        assert_eq!(time_interval.last_interval_start, Some(*START_TIME));
        // second tick should have used the new interval
        time_interval.tick_with_current_time(*START_TIME);
        assert_eq!(time_interval.last_sleep_duration, Some(new_test_interval));
        assert_eq!(
            time_interval.last_interval_start,
            Some(*START_TIME + new_test_interval)
        );
    }

    #[test]
    fn test_previous_interval_start() {
        // query the previous_interval_start after some missed intervals
        // if we are exactly on the start, the previous_interval_start should return this start
        let previous_interval_start_exact = TimeInterval::previous_interval_start(
            *START_TIME,
            *START_TIME + TEST_INTERVAL,
            TEST_INTERVAL,
        );
        assert_eq!(previous_interval_start_exact, *START_TIME + TEST_INTERVAL);

        // if later than the interval start, give the previous one
        let previous_interval_start_later = TimeInterval::previous_interval_start(
            *START_TIME,
            *START_TIME + LONG_WORK_INTERVAL,
            TEST_INTERVAL,
        );
        assert_eq!(previous_interval_start_later, *START_TIME + TEST_INTERVAL);
    }
}
