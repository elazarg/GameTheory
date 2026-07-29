/-
# `GameTheory.Core`

The static semantic core: signatures and profiles, finite-support laws, game
forms, preferences, utility evaluation, local deviation schemes, the single
equilibrium predicate, the profile-quantified response family, and potentials —
the one structure at this layer that makes a pure equilibrium exist.

Core imports no language front-end and no fixed-point or convexity theory.
Existence results and the heavier solution concepts are built on top of the core
rather than inside it, so that reading a definition never costs the machinery
some later theorem about it happens to need.
-/

import GameTheory.Core.Signature
import GameTheory.Core.Form
import GameTheory.Core.Preference
import GameTheory.Core.Deviation
import GameTheory.Core.Equilibrium
import GameTheory.Core.Utility
import GameTheory.Core.Response
import GameTheory.Core.Potential
import GameTheory.Core.Mixed
import GameTheory.Core.ZeroSum
import GameTheory.Core.SocialChoice
