/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the LICENSE file.
-/

import GameTheory.Concepts.Stochastic.QuittingTruncatedLedgerCapBoundary

/-!
# Compatibility import for the former reduced-cap conjecture module

The unconditional truncated-ledger producer formerly declared here is false.
The canonical interface, sound branch-relative compiler, and formal
counterexamples now live in `QuittingTruncatedLedgerCapBoundary`.

This module is retained only so downstream imports keep working.  New code
should import `QuittingTruncatedLedgerCapBoundary` directly.
-/
