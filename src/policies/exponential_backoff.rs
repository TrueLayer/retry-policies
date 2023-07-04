use crate::{Jitter, RetryDecision, RetryPolicy};
use chrono::Utc;
use rand::distributions::uniform::{UniformFloat, UniformSampler};
use std::{
    cmp::{self, min},
    time::{Duration, Instant},
};

/// Exponential backoff with optional jitter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExponentialBackoff {
    /// Maximum number of allowed retries attempts.
    pub max_n_retries: Option<u32>,
    /// Maximum duration the retries can continue for, after which retries will stop.
    pub max_total_retry_duration: Option<Duration>,
    /// Minimum waiting time between two retry attempts (it can end up being lower when using full jitter).
    pub min_retry_interval: Duration,
    /// Maximum waiting time between two retry attempts.
    pub max_retry_interval: Duration,
    /// How we apply jitter to the calculated backoff intervals.
    pub jitter: Jitter,
}

/// Exponential backoff with a maximum retry duration.
pub struct ExponentialBackoffTimed {
    inner: ExponentialBackoff,
}

/// Exponential backoff with a maximum retry duration, for a task with a known start time.
pub struct ExponentialBackoffWithStart {
    inner: ExponentialBackoff,
    started_at: Instant,
}

/// Builds an exponential backoff policy.
///
/// # Example
///
/// ```rust
/// use retry_policies::{RetryDecision, RetryPolicy, Jitter};
/// use retry_policies::policies::ExponentialBackoff;
/// use std::time::{Duration, Instant};
///
/// let backoff = ExponentialBackoff::builder()
///     .retry_bounds(Duration::from_secs(1), Duration::from_secs(60))
///     .jitter(Jitter::Bounded)
///     .build_with_total_retry_duration(Duration::from_secs(24 * 60 * 60));
///
/// ```
pub struct ExponentialBackoffBuilder {
    min_retry_interval: Duration,
    max_retry_interval: Duration,
    jitter: Jitter,
}

impl ExponentialBackoff {
    /// Returns a builder.
    ///
    /// # Example
    /// ```
    /// use retry_policies::policies::ExponentialBackoff;
    /// use std::time::Duration;
    ///
    /// let backoff = ExponentialBackoff::builder()
    ///     .build_with_max_retries(5);
    ///
    /// assert_eq!(backoff.min_retry_interval, Duration::from_secs(1));
    /// assert_eq!(backoff.max_retry_interval, Duration::from_secs(30 * 60));
    /// assert_eq!(backoff.max_n_retries, Some(5));
    /// ```
    pub fn builder() -> ExponentialBackoffBuilder {
        <_>::default()
    }

    fn too_many_attempts(&self, n_past_retries: u32) -> bool {
        self.max_n_retries
            .is_some_and(|max_n| max_n <= n_past_retries)
    }
}

impl RetryPolicy for ExponentialBackoff {
    fn should_retry(&self, n_past_retries: u32) -> RetryDecision {
        if self.too_many_attempts(n_past_retries) {
            RetryDecision::DoNotRetry
        } else {
            let unjittered_wait_for = min(
                self.max_retry_interval,
                self.min_retry_interval * 2_u32.checked_pow(n_past_retries).unwrap_or(u32::MAX),
            );

            let jittered_wait_for = match self.jitter {
                Jitter::None => unjittered_wait_for,
                Jitter::Full => {
                    let jitter_factor =
                        UniformFloat::<f64>::sample_single(0.0, 1.0, &mut rand::thread_rng());

                    unjittered_wait_for.mul_f64(jitter_factor)
                }
                Jitter::Bounded => {
                    let jitter_factor =
                        UniformFloat::<f64>::sample_single(0.0, 1.0, &mut rand::thread_rng());

                    let jittered_wait_for =
                        (unjittered_wait_for - self.min_retry_interval).mul_f64(jitter_factor);

                    jittered_wait_for + self.min_retry_interval
                }
            };

            let execute_after =
                Utc::now() + clip_and_convert(jittered_wait_for, self.max_retry_interval);
            RetryDecision::Retry { execute_after }
        }
    }
}

impl ExponentialBackoffTimed {
    pub fn for_task_started_at(&self, started_at: Instant) -> ExponentialBackoffWithStart {
        ExponentialBackoffWithStart {
            inner: self.inner,
            started_at,
        }
    }
}

impl ExponentialBackoffWithStart {
    fn trying_for_too_long(&self) -> bool {
        self.inner
            .max_total_retry_duration
            .is_some_and(|max_d| max_d <= self.started_at.elapsed())
    }
}

impl RetryPolicy for ExponentialBackoffWithStart {
    fn should_retry(&self, n_past_retries: u32) -> RetryDecision {
        if self.trying_for_too_long() {
            RetryDecision::DoNotRetry
        } else {
            self.inner.should_retry(n_past_retries)
        }
    }
}

/// Clip to the maximum allowed retry interval and convert to chrono::Duration
fn clip_and_convert(duration: Duration, max_duration: Duration) -> chrono::Duration {
    // Unwrapping is fine given that we are guaranteed to never exceed the maximum retry interval
    // in magnitude and that is well within range for chrono::Duration
    chrono::Duration::from_std(cmp::min(duration, max_duration)).unwrap()
}

impl Default for ExponentialBackoffBuilder {
    fn default() -> Self {
        Self {
            min_retry_interval: Duration::from_secs(1),
            max_retry_interval: Duration::from_secs(30 * 60),
            jitter: Jitter::Full,
        }
    }
}

impl ExponentialBackoffBuilder {
    /// Add min & max retry interval bounds. _Default [1s, 30m]_.
    ///
    /// See [`ExponentialBackoff::min_retry_interval`], [`ExponentialBackoff::max_retry_interval`].
    ///
    /// Panics if `min_retry_interval` > `max_retry_interval`.
    pub fn retry_bounds(
        mut self,
        min_retry_interval: Duration,
        max_retry_interval: Duration,
    ) -> Self {
        assert!(
            min_retry_interval <= max_retry_interval,
            "The maximum interval between retries should be greater or equal than the minimum retry interval."
        );
        self.min_retry_interval = min_retry_interval;
        self.max_retry_interval = max_retry_interval;
        self
    }

    /// Set what type of jitter to apply.
    pub fn jitter(mut self, jitter: Jitter) -> Self {
        self.jitter = jitter;
        self
    }

    /// Builds an [`ExponentialBackoff`] with the given maximum retries.
    ///
    /// See [`ExponentialBackoff::max_n_retries`].
    pub fn build_with_max_retries(self, n: u32) -> ExponentialBackoff {
        ExponentialBackoff {
            min_retry_interval: self.min_retry_interval,
            max_retry_interval: self.max_retry_interval,
            max_n_retries: Some(n),
            max_total_retry_duration: None,
            jitter: self.jitter,
        }
    }

    /// Builds an [`ExponentialBackoff`] with the given maximum total duration for which retries will
    /// continue to be performed.
    ///
    /// Requires the use of [`ExponentialBackoffTimed::for_task_started_at()`].
    ///
    /// # Example
    ///
    /// ```rust
    /// use retry_policies::{RetryDecision, RetryPolicy};
    /// use retry_policies::policies::ExponentialBackoff;
    /// use std::time::{Duration, Instant};
    ///
    /// let backoff = ExponentialBackoff::builder()
    ///     .build_with_total_retry_duration(Duration::from_secs(24 * 60 * 60));
    ///
    /// let started_at = Instant::now()
    ///     .checked_sub(Duration::from_secs(25 * 60 * 60)).unwrap();
    ///
    /// backoff.for_task_started_at(started_at)
    ///     .should_retry(0); // RetryDecision::DoNotRetry
    /// ```
    pub fn build_with_total_retry_duration(
        self,
        total_duration: Duration,
    ) -> ExponentialBackoffTimed {
        ExponentialBackoffTimed {
            inner: ExponentialBackoff {
                min_retry_interval: self.min_retry_interval,
                max_retry_interval: self.max_retry_interval,
                max_n_retries: None,
                max_total_retry_duration: Some(total_duration),
                jitter: self.jitter,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fake::Fake;

    fn get_retry_policy() -> ExponentialBackoff {
        ExponentialBackoff {
            max_n_retries: Some(6),
            max_total_retry_duration: None,
            min_retry_interval: Duration::from_secs(1),
            max_retry_interval: Duration::from_secs(5 * 60),
            jitter: Jitter::Full,
        }
    }

    #[test]
    fn if_n_past_retries_is_below_maximum_it_decides_to_retry() {
        // Arrange
        let policy = get_retry_policy();
        let n_past_retries = (0..policy.max_n_retries.unwrap()).fake();
        assert!(n_past_retries < policy.max_n_retries.unwrap());

        // Act
        let decision = policy.should_retry(n_past_retries);

        // Assert
        matches!(decision, RetryDecision::Retry { .. });
    }

    #[test]
    fn if_n_past_retries_is_above_maximum_it_decides_to_mark_as_failed() {
        // Arrange
        let policy = get_retry_policy();
        let n_past_retries = (policy.max_n_retries.unwrap()..).fake();
        assert!(n_past_retries >= policy.max_n_retries.unwrap());

        // Act
        let decision = policy.should_retry(n_past_retries);

        // Assert
        matches!(decision, RetryDecision::DoNotRetry);
    }

    #[test]
    fn maximum_retry_interval_is_never_exceeded() {
        // Arrange
        let policy = get_retry_policy();
        let max_interval = chrono::Duration::from_std(policy.max_retry_interval).unwrap();

        // Act
        let decision = policy.should_retry(policy.max_n_retries.unwrap() - 1);

        // Assert
        match decision {
            RetryDecision::Retry { execute_after } => {
                assert!((execute_after - Utc::now()) <= max_interval)
            }
            RetryDecision::DoNotRetry => panic!("Expected Retry decision."),
        }
    }

    #[test]
    fn overflow_backoff_exponent_does_not_cause_a_panic() {
        let policy = ExponentialBackoff {
            max_n_retries: Some(u32::MAX),
            ..get_retry_policy()
        };
        let max_interval = chrono::Duration::from_std(policy.max_retry_interval).unwrap();
        let n_failed_attempts = u32::MAX - 1;

        // Act
        let decision = policy.should_retry(n_failed_attempts);

        // Assert
        match decision {
            RetryDecision::Retry { execute_after } => {
                assert!((execute_after - Utc::now()) <= max_interval)
            }
            RetryDecision::DoNotRetry => panic!("Expected Retry decision."),
        }
    }

    #[test]
    #[should_panic]
    fn builder_invalid_retry_bounds() {
        // bounds are the wrong way round or invalid
        ExponentialBackoff::builder().retry_bounds(Duration::from_secs(3), Duration::from_secs(2));
    }

    #[test]
    fn does_not_retry_after_total_retry_duration() {
        let backoff = ExponentialBackoff::builder()
            .build_with_total_retry_duration(Duration::from_secs(24 * 60 * 60));

        {
            let started_at = Instant::now()
                .checked_sub(Duration::from_secs(23 * 60 * 60))
                .unwrap();

            let decision = backoff.for_task_started_at(started_at).should_retry(0);

            match decision {
                RetryDecision::Retry { .. } => {}
                _ => panic!("should retry"),
            }
        }
        {
            let started_at = Instant::now()
                .checked_sub(Duration::from_secs(25 * 60 * 60))
                .unwrap();

            let decision = backoff.for_task_started_at(started_at).should_retry(0);

            match decision {
                RetryDecision::DoNotRetry => {}
                _ => panic!("should not retry"),
            }
        }
    }
}
