/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCirculationUniformPayoffExamples
import GameTheory.Concepts.Stochastic.QuittingCirculationChiFloorBoundary
import GameTheory.Concepts.Stochastic.MultiOwnerFaceCirculationFiniteClosing

/-!
# Face-circulation tools for quitting games

Public umbrella for singleton and multi-owner face circulations.

The production branch defines circulation certificates, constructs forward
orbits, reverses compact finite prefixes into chronological support paths, and
compiles a punishment-valid floor into a uniform-equilibrium payoff.  It also
exports the alternative finite-charged closing route, which consumes the
original `∀ Q, ∃ finite orbit` producer without strengthening it to one orbit
working for every charge target, together with the scaled cyclic and repaired
four-player stress examples.

The boundary branch characterizes the two-coordinate certificate surface and
tests the lower `chi`-floor variant with explicit collision deterrence.  These
boundary results measure the mechanism class; they do not weaken the hypotheses
of the production orbit theorem or provide arbitrary-game certificate
existence.
-/
