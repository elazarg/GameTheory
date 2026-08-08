/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Adaptive.CertificateTargetPerturbation
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.TerminalChildAdaptivePotential
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Adaptive.PotentialFiniteTimeTargetBounds
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Adaptive.OwnerSeparatedAdaptivePotentialSystem

/-!
# Adaptive-potential system tools

Public facade for the reusable `AdaptivePotentialSystemAt` API.

The core structure and its certificate conversion are exported together with
target perturbation, profile transport for terminal children, enforcement-
ledger and finite-time target bounds, and owner-separated assembly.  These
operations transform or verify supplied systems; they do not construct the
local potentials, public responses, or credibility inequalities required by
an arbitrary stochastic game.

Higher public-stopping and response-architecture compilers remain separate
because they add causal-law and strategic-realization hypotheses rather than
mere structure-preserving operations on `AdaptivePotentialSystemAt`.
-/
