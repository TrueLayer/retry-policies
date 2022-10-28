use chrono::{DateTime, Utc};

pub trait RetryPolicy {
    /// Determine if a task should be retried according to a retry policy.
    fn should_retry(&self, n_past_retries: u32) -> RetryDecision;
}

/// Outcome of evaluating a retry policy for a failed task.
#[derive(Debug)]
pub enum RetryDecision {
    /// Retry after the specified timestamp.
    Retry { execute_after: DateTime<Utc> },
    /// Give up.
    DoNotRetry,
}
