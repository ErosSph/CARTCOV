# Table of contents
- [Project info](#project-info)
- [Quick start](#quick-start)
  - [Dependencies](#dependencies)
  - [Build](#build)
  - [Run](#run)
- [Usage](#usage)
- [Examples](#examples)
- [License](#license)

# Project info
CartCov is a platform that characterizes the relationship between assertions and code coverage by computing which RTL branches and statements are exercised by a given assertion. Starting from a design under verification (DUV), a set of assertions, and a bounded time horizon, CartCov encodes the assertion semantics together with branch/statement reachability conditions as a MaxSAT problem. By solving MaxSAT, the platform identifies a maximal set of coverage items (branches and statements) that can be simultaneously justified under the assertion constraints, and reports the corresponding covered locations and witnesses. In this way, CartCov helps verification engineers understand what structural behavior an assertion actually constrains or exercises, enabling coverage-guided assertion refinement, redundancy detection across assertions, and more systematic closure of functional and code coverage.
