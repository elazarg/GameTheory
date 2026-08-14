/-
# Implementation by profile-observed transfers

This module connects mechanism design to the canonical static response layer.
A nonnegative transfer may depend on the chosen strategy profile. It changes
utility through `GameForm.recordProfile`, without changing strategy carriers
or introducing a second game or dominance semantics.

The implemented solution concept here is explicitly weak undominance. Nash,
mixed, correlated, and informational implementation require their own
consumer-backed theorem layers rather than an arbitrary solution-set wrapper.
-/

import GameTheory.Core.Response

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

variable {ι : Type uι}

namespace UtilityGame

/-- A real transfer to each player contingent on the chosen strategy profile. -/
abbrev ProfileTransfer (G : UtilityGame ι) := Profile G.form.sig → ι → ℝ

/-- Add a profile-contingent transfer while retaining the original outcome law.
The recorded profile is an outcome-evaluation device; it is not an information
claim about what the players observe. -/
@[reducible]
def withProfileTransfer (G : UtilityGame.{uι, us, uo} ι)
    (transfer : G.ProfileTransfer) : UtilityGame ι where
  form := G.form.recordProfile
  utility observed who := G.utility observed.2 who + transfer observed.1 who

@[simp]
theorem expectedUtility_withProfileTransfer (G : UtilityGame.{uι, us, uo} ι)
    (transfer : G.ProfileTransfer) (profile : Profile G.form.sig) (who : ι) :
    expectedUtility (G.withProfileTransfer transfer).utility who
        ((G.withProfileTransfer transfer).form.play profile) =
      expectedUtility G.utility who (G.form.play profile) + transfer profile who := by
  simp [withProfileTransfer, expectedUtility, FinDist.expect_add,
    FinDist.expect_const]

/-- Nonnegative transfers implement a target under weak undominance when the
transferred game has a weakly-undominated profile and every such profile lies
in the target. -/
def IsUndominatedImplementation [DecidableEq ι] (G : UtilityGame ι)
    (transfer : G.ProfileTransfer) (target : Set (Profile G.form.sig)) : Prop :=
  (∀ profile who, 0 ≤ transfer profile who) ∧
    {profile |
      IsWeaklyUndominatedProfile (G.withProfileTransfer transfer).form
        (G.withProfileTransfer transfer).preference profile}.Nonempty ∧
    ∀ profile,
      IsWeaklyUndominatedProfile (G.withProfileTransfer transfer).form
          (G.withProfileTransfer transfer).preference profile →
        profile ∈ target

/-- A `k`-implementation additionally bounds total transfer on every surviving
weakly-undominated profile. Profiles removed by the transfer do not consume the
budget. -/
def IsKUndominatedImplementation [DecidableEq ι] [Fintype ι]
    (G : UtilityGame ι) (transfer : G.ProfileTransfer)
    (target : Set (Profile G.form.sig)) (budget : ℝ) : Prop :=
  G.IsUndominatedImplementation transfer target ∧
    ∀ profile,
      IsWeaklyUndominatedProfile (G.withProfileTransfer transfer).form
          (G.withProfileTransfer transfer).preference profile →
        (∑ who, transfer profile who) ≤ budget

theorem IsUndominatedImplementation.mono_target [DecidableEq ι]
    {G : UtilityGame ι} {transfer : G.ProfileTransfer}
    {target larger : Set (Profile G.form.sig)}
    (h : G.IsUndominatedImplementation transfer target)
    (hsubset : target ⊆ larger) :
    G.IsUndominatedImplementation transfer larger :=
  ⟨h.1, h.2.1, fun profile hsurvives => hsubset (h.2.2 profile hsurvives)⟩

theorem IsKUndominatedImplementation.mono_target [DecidableEq ι] [Fintype ι]
    {G : UtilityGame ι} {transfer : G.ProfileTransfer}
    {target larger : Set (Profile G.form.sig)} {budget : ℝ}
    (h : G.IsKUndominatedImplementation transfer target budget)
    (hsubset : target ⊆ larger) :
    G.IsKUndominatedImplementation transfer larger budget :=
  ⟨h.1.mono_target hsubset, h.2⟩

end UtilityGame

end GameTheory
