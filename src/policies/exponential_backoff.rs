use crate::{RetryDecision, RetryPolicy};
use chrono::Utc;
use rand::distributions::uniform::{UniformFloat, UniformSampler};
use std::{cmp, time::Duration};

const MIN_JITTER: f64 = 0.0;
const MAX_JITTER: f64 = 3.0;

/// We are using the "decorrelated jitter" approach detailed here:
/// `<https://aws.amazon.com/blogs/architecture/exponential-backoff-and-jitter/>`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExponentialBackoff {
    /// Maximum number of allowed retries attempts.
    pub max_n_retries: u32,
    /// Minimum waiting time between two retry attempts (it can end up being lower due to jittering).
    pub min_retry_interval: Duration,
    /// Maximum waiting time between two retry attempts.
    pub max_retry_interval: Duration,
    /// Growing factor governing how fast the retry interval increases with respect to the number
    /// of failed attempts. If set to 3:
    /// - first retry: 3^0 = 1
    /// - second retry: 3^1 = 3
    /// - third retry: 3^2 = 9
    /// ...
    pub backoff_exponent: u32,
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
    ///     .build_with_total_retry_duration(Duration::from_secs(24 * 60 * 60));
    ///
    /// assert_eq!(backoff.backoff_exponent, 3);
    /// assert_eq!(backoff.min_retry_interval, Duration::from_secs(1));
    /// assert_eq!(backoff.max_retry_interval, Duration::from_secs(30 * 60));
    /// assert_eq!(backoff.max_n_retries, 55); // calculated
    /// ```
    pub fn builder() -> ExponentialBackoffBuilder {
        <_>::default()
    }
}

impl RetryPolicy for ExponentialBackoff {
    fn should_retry(&self, n_past_retries: u32) -> RetryDecision {
        if n_past_retries >= self.max_n_retries {
            RetryDecision::DoNotRetry
        } else {
            let unjittered_wait_for = self.min_retry_interval
                * self
                    .backoff_exponent
                    .checked_pow(n_past_retries)
                    .unwrap_or(u32::MAX);
            let jitter_factor =
                UniformFloat::<f64>::sample_single(MIN_JITTER, MAX_JITTER, &mut rand::thread_rng());
            let jittered_wait_for = unjittered_wait_for.mul_f64(jitter_factor);

            let execute_after =
                Utc::now() + clip_and_convert(jittered_wait_for, self.max_retry_interval);
            RetryDecision::Retry { execute_after }
        }
    }
}

/// Clip to the maximum allowed retry interval and convert to chrono::Duration
fn clip_and_convert(duration: Duration, max_duration: Duration) -> chrono::Duration {
    // Unwrapping is fine given that we are guaranteed to never exceed the maximum retry interval
    // in magnitude and that is well withing range for chrono::Duration
    chrono::Duration::from_std(cmp::min(duration, max_duration)).unwrap()
}

pub struct ExponentialBackoffBuilder {
    min_retry_interval: Duration,
    max_retry_interval: Duration,
    backoff_exponent: u32,
}

impl Default for ExponentialBackoffBuilder {
    fn default() -> Self {
        Self {
            min_retry_interval: Duration::from_secs(1),
            max_retry_interval: Duration::from_secs(30 * 60),
            backoff_exponent: 3,
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

    /// Set backoff exponent. _Default 3_.
    ///
    /// See [`ExponentialBackoff::backoff_exponent`].
    pub fn backoff_exponent(mut self, exponent: u32) -> Self {
        self.backoff_exponent = exponent;
        self
    }

    /// Builds a [`ExponentialBackoff`] with the given maximum retries.
    ///
    /// See [`ExponentialBackoff::max_n_retries`].
    pub fn build_with_max_retries(self, n: u32) -> ExponentialBackoff {
        ExponentialBackoff {
            min_retry_interval: self.min_retry_interval,
            max_retry_interval: self.max_retry_interval,
            backoff_exponent: self.backoff_exponent,
            max_n_retries: n,
        }
    }

    /// Builds a [`ExponentialBackoff`] with [`ExponentialBackoff::max_n_retries`] calculated
    /// from an approximate total duration. So that after the resultant `max_n_retries` we'll
    /// have (generally) retried past the given `total_duration`.
    ///
    /// The _actual_ duration will be approximate due to retry jitter, though this calculation
    /// is itself deterministic (based off mean jitter).
    ///
    /// # Example
    /// ```
    /// use retry_policies::policies::ExponentialBackoff;
    /// use std::time::Duration;
    ///
    /// let backoff = ExponentialBackoff::builder()
    ///     .backoff_exponent(2)
    ///     .retry_bounds(Duration::from_secs(1), Duration::from_secs(60 * 60))
    ///     // set a retry count so we retry for ~3 hours
    ///     .build_with_total_retry_duration(Duration::from_secs(3 * 60 * 60));
    ///
    /// // mean delay steps: 1.5s, 3s, 6s, 12s, 24s, 48s, 96s, 192s,
    /// //                   384s, 768s, 1536s, 3072s, 3600s, 3600s
    /// // expected total delay: 13342.5s = 3.7h (least number of retries >= 3h)
    /// assert_eq!(backoff.max_n_retries, 14);
    /// ```
    pub fn build_with_total_retry_duration(self, total_duration: Duration) -> ExponentialBackoff {
        let mut out = self.build_with_max_retries(0);

        const MEAN_JITTER: f64 = (MIN_JITTER + MAX_JITTER) / 2.0;

        let delays = (0u32..).into_iter().map(|n| {
            let min_interval = out.min_retry_interval;
            let backoff_factor = out.backoff_exponent.checked_pow(n).unwrap_or(u32::MAX);
            let n_delay = (min_interval * backoff_factor).mul_f64(MEAN_JITTER);
            cmp::min(n_delay, out.max_retry_interval)
        });

        let mut approx_total = Duration::from_secs(0);
        for (n, delay) in delays.enumerate() {
            approx_total += delay;
            if approx_total >= total_duration {
                out.max_n_retries = (n + 1) as _;
                break;
            } else if delay == out.max_retry_interval {
                // Optimisation: The delay aint changing now
                let remaining_s = (total_duration - approx_total).as_secs_f64();
                let additional_tries = (remaining_s / delay.as_secs_f64()).ceil() as usize;
                out.max_n_retries = (n + 1 + additional_tries) as _;
                break;
            }
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fake::Fake;

    fn get_retry_policy() -> ExponentialBackoff {
        ExponentialBackoff {
            max_n_retries: 6,
            min_retry_interval: Duration::from_secs(1),
            max_retry_interval: Duration::from_secs(5 * 60),
            backoff_exponent: 3,
        }
    }

    #[test]
    fn if_n_past_retries_is_below_maximum_it_decides_to_retry() {
        // Arrange
        let policy = get_retry_policy();
        let n_past_retries = (0..policy.max_n_retries).fake();
        assert!(n_past_retries < policy.max_n_retries);

        // Act
        let decision = policy.should_retry(n_past_retries);

        // Assert
        matches!(decision, RetryDecision::Retry { .. });
    }

    #[test]
    fn if_n_past_retries_is_above_maximum_it_decides_to_mark_as_failed() {
        // Arrange
        let policy = get_retry_policy();
        let n_past_retries = (policy.max_n_retries..).fake();
        assert!(n_past_retries >= policy.max_n_retries);

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
        let decision = policy.should_retry(policy.max_n_retries - 1);

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
            max_n_retries: u32::MAX,
            backoff_exponent: 2,
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
}
