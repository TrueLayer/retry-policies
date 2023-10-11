use crate::{Jitter, RetryDecision, RetryPolicy};
use chrono::{DateTime, Utc};
use rand::distributions::uniform::{UniformFloat, UniformSampler};
use std::{
    cmp::{self, min},
    time::Duration,
};

/// Exponential backoff with optional jitter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExponentialBackoff {
    /// Maximum number of allowed retries attempts.
    pub max_n_retries: Option<u32>,
    /// Minimum waiting time between two retry attempts (it can end up being lower when using full jitter).
    pub min_retry_interval: Duration,
    /// Maximum waiting time between two retry attempts.
    pub max_retry_interval: Duration,
    /// How we apply jitter to the calculated backoff intervals.
    pub jitter: Jitter,
    /// Base of the exponential
    pub base: u32,
}

/// Exponential backoff with a maximum retry duration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExponentialBackoffTimed {
    /// Maximum duration the retries can continue for, after which retries will stop.
    max_total_retry_duration: Duration,

    backoff: ExponentialBackoff,
}

/// Exponential backoff with a maximum retry duration, for a task with a known start time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExponentialBackoffWithStart {
    started_at: DateTime<Utc>,

    inner: ExponentialBackoffTimed,
}

/// Builds an exponential backoff policy.
///
/// # Example
///
/// ```rust
/// use retry_policies::{RetryDecision, RetryPolicy, Jitter};
/// use retry_policies::policies::ExponentialBackoff;
/// use std::time::Duration;
///
/// let backoff = ExponentialBackoff::builder()
///     .retry_bounds(Duration::from_secs(1), Duration::from_secs(60))
///     .jitter(Jitter::Bounded)
///     .base(2)
///     .build_with_total_retry_duration(Duration::from_secs(24 * 60 * 60));
/// ```
pub struct ExponentialBackoffBuilder {
    min_retry_interval: Duration,
    max_retry_interval: Duration,
    jitter: Jitter,
    base: u32,
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
    /// assert_eq!(backoff.base, 2);
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
                self.min_retry_interval * calculate_exponential(self.base, n_past_retries),
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

/// Clip to the maximum allowed retry interval and convert to [`chrono::Duration`].
fn clip_and_convert(duration: Duration, max_duration: Duration) -> chrono::Duration {
    // Unwrapping is fine given that we are guaranteed to never exceed the maximum retry interval
    // in magnitude and that is well within range for chrono::Duration
    chrono::Duration::from_std(cmp::min(duration, max_duration)).unwrap()
}

/// Calculate exponential using base and number of past retries
fn calculate_exponential(base: u32, n_past_retries: u32) -> u32 {
    base.checked_pow(n_past_retries).unwrap_or(u32::MAX)
}

impl ExponentialBackoffTimed {
    /// Create a [`RetryPolicy`] for a task started at the given
    pub fn for_task_started_at(&self, started_at: DateTime<Utc>) -> ExponentialBackoffWithStart {
        ExponentialBackoffWithStart {
            inner: *self,
            started_at,
        }
    }

    /// Maximum number of allowed retries attempts.
    pub fn max_retries(&self) -> Option<u32> {
        self.backoff.max_n_retries
    }
}

impl ExponentialBackoffWithStart {
    fn trying_for_too_long(&self) -> bool {
        self.inner.max_total_retry_duration <= Self::elapsed(self.started_at)
    }

    fn elapsed(started_at: DateTime<Utc>) -> Duration {
        Utc::now()
            .signed_duration_since(started_at)
            .to_std()
            // If `started_at` is in the future then return a zero duration.
            .unwrap_or_default()
    }
}

impl RetryPolicy for ExponentialBackoffWithStart {
    fn should_retry(&self, n_past_retries: u32) -> RetryDecision {
        if self.trying_for_too_long() {
            RetryDecision::DoNotRetry
        } else {
            self.inner.backoff.should_retry(n_past_retries)
        }
    }
}

impl Default for ExponentialBackoffBuilder {
    fn default() -> Self {
        Self {
            min_retry_interval: Duration::from_secs(1),
            max_retry_interval: Duration::from_secs(30 * 60),
            jitter: Jitter::Full,
            base: 2,
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

    /// Set what base to use for the exponential.
    pub fn base(mut self, base: u32) -> Self {
        self.base = base;
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
            jitter: self.jitter,
            base: self.base,
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
    /// use chrono::{DateTime, Utc};
    /// use retry_policies::{RetryDecision, RetryPolicy};
    /// use retry_policies::policies::ExponentialBackoff;
    /// use std::time::Duration;
    ///
    /// let backoff = ExponentialBackoff::builder()
    ///     .build_with_total_retry_duration(Duration::from_secs(24 * 60 * 60));
    ///
    /// let started_at = Utc::now()
    ///     .checked_sub_signed(chrono::Duration::seconds(25 * 60 * 60))
    ///     .unwrap();
    ///
    /// let should_retry = backoff.for_task_started_at(started_at).should_retry(0);
    /// assert!(matches!(RetryDecision::DoNotRetry, should_retry));
    /// ```
    pub fn build_with_total_retry_duration(
        self,
        total_duration: Duration,
    ) -> ExponentialBackoffTimed {
        ExponentialBackoffTimed {
            max_total_retry_duration: total_duration,
            backoff: ExponentialBackoff {
                min_retry_interval: self.min_retry_interval,
                max_retry_interval: self.max_retry_interval,
                max_n_retries: None,
                jitter: self.jitter,
                base: self.base,
            },
        }
    }

    /// Builds an [`ExponentialBackoff`] with the given maximum total duration and calculates max
    /// retries that should happen applying no jitter.
    ///
    /// For example if we set total duration 24 hours, with retry bounds [1s, 24h] and 2 as base of the exponential,
    /// we would calculate 17 max retries, as 1s * pow(2, 16) = 65536s = ~18 hours and 18th attempt would be way
    /// after the 24 hours total duration.
    ///
    /// If the 17th retry ends up being scheduled after 10 hours due to jitter, [`ExponentialBackoff::should_retry`]
    /// will return false anyway: no retry will be allowed after total duration.
    ///
    /// If one of the 17 allowed retries for some reason (e.g. previous attempts taking a long time) ends up
    /// being scheduled after total duration, [`ExponentialBackoff::should_retry`] will return false.
    ///
    /// Basically we will enforce whatever comes first, max retries or total duration.
    ///
    /// Requires the use of [`ExponentialBackoffTimed::for_task_started_at()`].
    ///
    /// # Example
    ///
    /// ```rust
    /// use chrono::{DateTime, Utc};
    /// use retry_policies::{RetryDecision, RetryPolicy};
    /// use retry_policies::policies::ExponentialBackoff;
    /// use std::time::Duration;
    ///
    /// let exponential_backoff_timed = ExponentialBackoff::builder()
    ///     .retry_bounds(Duration::from_secs(1), Duration::from_secs(6 * 60 * 60))
    ///     .build_with_total_retry_duration_and_max_retries(Duration::from_secs(24 * 60 * 60));
    ///
    /// assert_eq!(exponential_backoff_timed.max_retries(), Some(17));
    ///
    /// let started_at = Utc::now()
    ///     .checked_sub_signed(chrono::Duration::seconds(25 * 60 * 60))
    ///     .unwrap();
    ///
    /// let should_retry = exponential_backoff_timed.for_task_started_at(started_at).should_retry(0);
    /// assert!(matches!(RetryDecision::DoNotRetry, should_retry));
    ///
    /// let started_at = Utc::now()
    ///     .checked_sub_signed(chrono::Duration::seconds(1 * 60 * 60))
    ///     .unwrap();
    ///
    /// let should_retry = exponential_backoff_timed.for_task_started_at(started_at).should_retry(18);
    /// assert!(matches!(RetryDecision::DoNotRetry, should_retry));
    ///
    /// ```
    pub fn build_with_total_retry_duration_and_max_retries(
        self,
        total_duration: Duration,
    ) -> ExponentialBackoffTimed {
        let mut max_n_retries = None;

        let delays = (0u32..).map(|n| {
            min(
                self.max_retry_interval,
                self.min_retry_interval * calculate_exponential(self.base, n),
            )
        });

        let mut total = Duration::from_secs(0);
        for (n, delay) in delays.enumerate() {
            total += delay;
            if total >= total_duration {
                max_n_retries = Some(n as _);
                break;
            }
        }

        ExponentialBackoffTimed {
            max_total_retry_duration: total_duration,
            backoff: ExponentialBackoff {
                min_retry_interval: self.min_retry_interval,
                max_retry_interval: self.max_retry_interval,
                max_n_retries,
                jitter: self.jitter,
                base: self.base,
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
            min_retry_interval: Duration::from_secs(1),
            max_retry_interval: Duration::from_secs(5 * 60),
            jitter: Jitter::Full,
            base: 2,
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
            let started_at = Utc::now()
                .checked_sub_signed(chrono::Duration::seconds(23 * 60 * 60))
                .unwrap();

            let decision = backoff.for_task_started_at(started_at).should_retry(0);

            match decision {
                RetryDecision::Retry { .. } => {}
                _ => panic!("should retry"),
            }
        }
        {
            let started_at = Utc::now()
                .checked_sub_signed(chrono::Duration::seconds(25 * 60 * 60))
                .unwrap();

            let decision = backoff.for_task_started_at(started_at).should_retry(0);

            match decision {
                RetryDecision::DoNotRetry => {}
                _ => panic!("should not retry"),
            }
        }
    }

    #[test]
    fn does_not_retry_before_total_retry_duration_if_max_retries_exceeded() {
        let backoff = ExponentialBackoff::builder()
            // This configuration should allow 17 max retries inside a 24h total duration
            .retry_bounds(Duration::from_secs(1), Duration::from_secs(6 * 60 * 60))
            .build_with_total_retry_duration_and_max_retries(Duration::from_secs(24 * 60 * 60));

        {
            let started_at = Utc::now()
                .checked_sub_signed(chrono::Duration::seconds(23 * 60 * 60))
                .unwrap();

            let decision = backoff.for_task_started_at(started_at).should_retry(0);

            match decision {
                RetryDecision::Retry { .. } => {}
                _ => panic!("should retry"),
            }
        }
        {
            let started_at = Utc::now()
                .checked_sub_signed(chrono::Duration::seconds(23 * 60 * 60))
                .unwrap();

            // Zero based, so this is the 18th retry
            let decision = backoff.for_task_started_at(started_at).should_retry(17);

            match decision {
                RetryDecision::DoNotRetry => {}
                _ => panic!("should not retry"),
            }
        }
        {
            let started_at = Utc::now()
                .checked_sub_signed(chrono::Duration::seconds(25 * 60 * 60))
                .unwrap();

            let decision = backoff.for_task_started_at(started_at).should_retry(0);

            match decision {
                RetryDecision::DoNotRetry => {}
                _ => panic!("should not retry"),
            }
        }
    }

    #[test]
    fn different_exponential_base_produce_different_max_retries_for_the_same_duration() {
        let backoff_base_2 = ExponentialBackoff::builder()
            .retry_bounds(Duration::from_secs(1), Duration::from_secs(60 * 60))
            .base(2)
            .build_with_total_retry_duration_and_max_retries(Duration::from_secs(60 * 60));

        let backoff_base_3 = ExponentialBackoff::builder()
            .retry_bounds(Duration::from_secs(1), Duration::from_secs(60 * 60))
            .base(3)
            .build_with_total_retry_duration_and_max_retries(Duration::from_secs(60 * 60));

        let backoff_base_4 = ExponentialBackoff::builder()
            .retry_bounds(Duration::from_secs(1), Duration::from_secs(60 * 60))
            .base(4)
            .build_with_total_retry_duration_and_max_retries(Duration::from_secs(60 * 60));

        assert_eq!(backoff_base_2.max_retries().unwrap(), 11);
        assert_eq!(backoff_base_3.max_retries().unwrap(), 8);
        assert_eq!(backoff_base_4.max_retries().unwrap(), 6);
    }
}
