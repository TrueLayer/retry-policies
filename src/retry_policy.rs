use std::time::{Duration, SystemTime};

use rand::distributions::uniform::{UniformFloat, UniformSampler};

/// A policy for deciding whether and when to retry.
pub trait RetryPolicy {
    /// Determine if a task should be retried according to a retry policy.
    fn should_retry(&self, request_start_time: SystemTime, n_past_retries: u32) -> RetryDecision;
}

/// Outcome of evaluating a retry policy for a failed task.
#[derive(Debug)]
pub enum RetryDecision {
    /// Retry after the specified timestamp.
    Retry { execute_after: SystemTime },
    /// Give up.
    DoNotRetry,
}

/// How to apply jitter to the retry intervals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Jitter {
    /// Don't apply any jitter.
    None,
    /// Jitter between 0 and the calculated backoff duration.
    Full,
    /// Jitter between `min_retry_interval` and the calculated backoff duration.
    Bounded,
}

impl Jitter {
    pub(crate) fn apply(&self, interval: Duration, min_interval: Duration) -> Duration {
        match self {
            Jitter::None => interval,
            Jitter::Full => {
                let jitter_factor =
                    UniformFloat::<f64>::sample_single(0.0, 1.0, &mut rand::thread_rng());

                interval.mul_f64(jitter_factor)
            }
            Jitter::Bounded => {
                let jitter_factor =
                    UniformFloat::<f64>::sample_single(0.0, 1.0, &mut rand::thread_rng());

                let jittered_wait_for = (interval - min_interval).mul_f64(jitter_factor);

                jittered_wait_for + min_interval
            }
        }
    }
}
