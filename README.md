# rhythmic

**rhythmic** is a Rust crate that provides a mechanism for executing code at regular intervals with robust overrun handling. It ensures consistent execution behavior even under varying workloads.

## Key Features

- **Regular Interval Execution**: Schedule tasks to run at specified time intervals.
- **Overrun Handling**: Choose from different overrun behaviors to manage situations where the previous interval execution took longer than expected.
  - `AwaitNextInterval`: Wait for the next regular interval start.
  - `WaitInterval`: Wait for the specified interval duration, adjusting the regular run time accordingly.
  - `ImmediateReturn`: Don't wait for the next interval and return immediately.

## Usage

### Add rhythmic as a dependency in your Cargo.toml file:

```toml filename=Cargo.toml
[dependencies]
rhythmic = "0.1.0"
```
### Import the crate and use the TimeInterval struct:

```rust
use rhythmic;
use std::thread;
use std::time::Duration;

fn main() {
    // Create a TimeInterval with a 1 second interval and AwaitNextInterval behavior
    let mut interval = rhythmic::TimeInterval::new(Duration::from_secs(1))
        .with_behavior(rhythmic::OverrunBehavior::AwaitNextInterval);
    loop {
        // Await the next interval - first time starts immediately
        interval.tick();
        // Perform your task here
        println!("Executing task...");
        thread::sleep(Duration::from_millis(500)); // Simulate work
    }
}
```

## Overrun Behavior

The `OverrunBehavior` enum allows you to specify how rhythmic handles situations where the previous interval execution took longer than the specified interval.

* `AwaitNextInterval`: This is the default behavior. It waits until the next regular interval start, aligning subsequent executions.
* `WaitInterval`: It waits for the specified interval duration, even if this overlaps with the next regular interval. This can lead to slightly jittery execution patterns.
* `ImmediateReturn`: It returns immediately without waiting for the next interval. This is useful when you don't want to delay subsequent executions due to overruns.

## Documentation

More extensive documentation, including detailed API descriptions and examples, will be available soon.

## Contributing

I welcome contributions to the rhythmic crate.

## License

This project is licensed under the MIT or Apache-2.0 License.
