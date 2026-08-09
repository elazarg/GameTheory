/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.Multivalued.SCCExecution
import UniformEquilibrium.Quitting.EssentialAPS.Multivalued.OccupationRegression

/-!
# Multivalued essential-APS execution

Public surface for:

* generic finite-terminal / coherent-infinite / typed-obstruction execution;
* exact SCC-internal execution from the named segment-subinvariance hypothesis;
* the separate charged-segment obstruction trichotomy and its conditional
  prefix-charge bounds; and
* the regression separating global occupation cancellation from one
  chronological recurrent path.

Graph strong connectivity and graph reachability are never promoted to exact
singleton-flow segments without an explicit segment-level hypothesis.
-/
