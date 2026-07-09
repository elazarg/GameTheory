/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation.Examples
import GameTheory.Implementation.Exact
import GameTheory.Implementation.Informational
import GameTheory.Implementation.VCG

/-!
# k-implementation examples and counterexamples API

Curated import surface for concrete examples, counterexamples, and
paper-correction witnesses.

The imported declarations include:

* the introductory congestion selection example;
* the one-player singleton non-attainment counterexample;
* the Section 3.2 infinite-ascent counterexamples;
* the mixed-extension counterexample refuting the unrestricted converse of
  Theorem 3;
* the compact upper-set witness separating semantic selection-admissibility
  from analytic admissibility;
* the degenerate recommendation-device full-support necessity example,
  including the null-signal saturation obstruction;
* the Figure 3 informational-domination table and the Figure 4 signal-blind
  impossibility example;
* the optimal-perturbation exact-implementation counterexample;
* the VCG frugality-necessity example, bounded conformance witnesses, the
  strict frugal quasi-field witness, and the redundant-report transfer-class
  saturation witness.

This module is import-only and deliberately does not rename the witnesses.
-/
