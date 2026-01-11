#[cfg(feature = "metrics")]
use std::time::Instant;

#[cfg(feature = "metrics")]
pub struct Timer {
    name: &'static str,
    start: Instant,
}

#[cfg(feature = "metrics")]
impl Timer {
    pub fn new(name: &'static str) -> Self {
        Self {
            name,
            start: Instant::now(),
        }
    }
}

#[cfg(feature = "metrics")]
impl Drop for Timer {
    fn drop(&mut self) {
        let elapsed = self.start.elapsed();
        tracing::info!(
            target: "metrics",
            metric = "timer",
            name = self.name,
            ms = elapsed.as_secs_f64() * 1000.0
        );
    }
}

#[cfg(not(feature = "metrics"))]
pub struct Timer;

#[cfg(not(feature = "metrics"))]
impl Timer {
    pub fn new(_name: &'static str) -> Self {
        Timer
    }
}

pub fn timer(name: &'static str) -> Timer {
    Timer::new(name)
}

#[cfg(feature = "metrics")]
pub fn counter(name: &'static str, value: u64) {
    tracing::info!(target: "metrics", metric = "counter", name, value);
}

#[cfg(not(feature = "metrics"))]
pub fn counter(_name: &'static str, _value: u64) {}
