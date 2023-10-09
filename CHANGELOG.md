# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.2.1] - 2023-10-09

### Added

- Total duration algorithm can now be configured to also consider max retries, calculated applying no jitter (1.0)
  - We enforce whatever comes first, total duration or max retries
- Exponential base is now configurable

## [0.2.0] - 2023-07-21

### Changed

- [Breaking] Change backoff and jitter algorithms
  - Change the backoff algorithm to a more conventional exponential backoff.
  - Replace the decorrelated jitter algorithm with an option of either none, full, or bounded. Defaults to full jitter.
- [Breaking] Remove `ExponentialBackoffBuilder::backoff_exponent()`
  - The number of attempts is now used as the exponent.
- [Breaking] Require a task start time when using a total retry duration
  - `ExponentialBackoffBuilder::build_with_total_retry_duration()` now returns `ExponentialBackoffTimed` which does not implement `RetryPolicy`.
- [Breaking] Mark `ExponentialBackoff` as `non_exhaustive`
  - Can no longer be constructed directly.

## [0.1.2] - 2022-10-28

### Added

- `Debug` derived for `RetryDecision`

## [0.1.1] - 2021-10-18

### Security

- remove time v0.1 dependency

## [0.1.0] - 2021-08-11

### Added

- `ExponentialBackoff` policy.
