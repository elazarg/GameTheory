/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Transport.Order
import GameTheory.Concepts.Transport.Oblivious
import Mathlib.Probability.Distributions.Uniform

/-!
# Finite separations of the transport axes

The incomparability half of the transport-criteria graph: for each axis, a small
finite game exhibits two adjacent points that no realization can bridge, so the
stronger fact is not derivable from the weaker one.

Because a `Realization` owns an arbitrary relation `rel`, the empty relation
inhabits every simulation vacuously; "no transport exists" is therefore only
meaningful once the realization is fixed. Every negative statement below fixes a
concrete correspondence relating a *designated pair* and shows the required
observed-law equality or backtranslation cannot hold for that pair; the positive
half fixes the same games and the same designated data.

* **O-separation** (`SeparationsO`): a serializer whose view leaks the
  serialization order admits no oblivious completion. Under the order-discarding
  view the two order traces share the observed law (`boolOrderSerializer`); under
  the order-observing identity view they do not, so no realization family can
  relate one source distribution to both traces.
* **U-separation** (`SeparationsU`): a coalition reaches an observed law no
  singleton can. The positive half law-matches every unilateral target deviation; the
  negative half is the same `coalitionConstantDeviationFamily` at the grand coalition,
  whose joint deviation to `(true, true)` lands on a target outcome unreachable by any
  source coalition deviation. Since that family's singleton restriction coincides with
  the unilateral family (via `constantToCoalitionHom` and its `deviate_eq`), the two
  halves differ only in the unit granularity.
* **P-separation** (`SeparationsP`): recommendation-dependence and constant
  replacement are incomparable across a fixed realization. One direction exhibits
  a constant target deviation matched only by recommendation-dependent source
  deviations (correlated transports, coarse-correlated fails); the other a
  recommendation-dependent target deviation outrunning every constant source
  deviation (coarse-correlated transports, correlated fails).
* **V-separation** (`SeparationsV`): the same games and designated pair transport
  under the coarse outcome view but not under a strictly richer view, and a
  view-contingent equilibrium fails to transport at the rich view.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type}

/-- Two distinct point masses are distinct distributions: they disagree at the
first point. A reusable discriminator for the finite separations, which compare
observed laws that reduce to point masses. -/
theorem pmf_pure_ne_pure {α : Type} {x y : α} (h : x ≠ y) :
    (PMF.pure x : PMF α) ≠ PMF.pure y := by
  intro heq
  have hx : (PMF.pure x : PMF α) x = (PMF.pure y : PMF α) x := by rw [heq]
  rw [PMF.pure_apply_self x, PMF.pure_apply_of_ne y x h] at hx
  exact one_ne_zero hx

/-! ## O-separation: a view that leaks the order blocks oblivious completion -/

namespace SeparationsO

open TransportExamples ObliviousExamples

/-- The **order-observing** view on the order-traced target: it observes the full
`(value, order)` pair rather than discarding the order component. -/
noncomputable def orderTracedIdView :
    ViewFamily orderTracedForm Unit (fun _ => Bool × Bool) :=
  ViewFamily.const id

/-- The designated source distribution: the pure profile that plays `true`. -/
noncomputable def designatedSource : PMF boolOutcomeForm.Profile :=
  PMF.pure (fun _ => true)

/-- Under the order-observing view, the two order traces of the designated source
have different observed laws: one records order `true`, the other order `false`. -/
theorem claw_orderTraced_ne :
    orderTracedIdView.claw () (boolOrderTrace true designatedSource) ≠
      orderTracedIdView.claw () (boolOrderTrace false designatedSource) := by
  have h : ((true, true) : Bool × Bool) ≠ (true, false) := by decide
  simpa [orderTracedIdView, ViewFamily.claw, ViewFamily.const, designatedSource,
    boolOrderTrace, orderTracedForm, PMF.pure_map] using pmf_pure_ne_pure h

/-- **Positive half.** Under the order-discarding view the two order traces share
the observed law: `boolOrderSerializer` is oblivious. -/
example (μG : PMF boolOutcomeForm.Profile) :
    orderTracedView.claw () (boolOrderTrace true μG) =
      orderTracedView.claw () (boolOrderTrace false μG) :=
  claw_index_independent (fun s => (boolOrderSerializer s).toRealization)
    (μH := fun s => boolOrderTrace s μG)
    (fun s => boolOrderSerializer_rel s μG) true false ()

/-- **Negative half.** No realization family — over *any* source view — can relate
the designated source distribution to both order traces under the order-observing
target view: `law_eq` would force the two observed laws equal, but they differ. -/
theorem no_oblivious_completion
    (VG : ViewFamily boolOutcomeForm Unit (fun _ => Bool × Bool))
    (R : Bool → Realization boolOutcomeForm orderTracedForm VG orderTracedIdView)
    (htrue : (R true).rel designatedSource (boolOrderTrace true designatedSource))
    (hfalse : (R false).rel designatedSource (boolOrderTrace false designatedSource)) :
    False :=
  claw_orderTraced_ne (((R true).law_eq htrue ()).symm.trans ((R false).law_eq hfalse ()))

end SeparationsO

/-! ## V-separation: a richer view breaks a transport that the coarse view admits -/

namespace SeparationsV

/-- Source game: the outcome pairs the strategy value with a fixed `false` bit. -/
noncomputable def srcForm : GameForm Unit where
  Strategy := fun _ => Bool
  Outcome := Bool × Bool
  outcomeKernel := fun σ => PMF.pure (σ (), false)

/-- Target game: the same strategy value, but a fixed `true` bit. The two games
agree on the value and disagree only on the extra bit. -/
noncomputable def tgtForm : GameForm Unit where
  Strategy := fun _ => Bool
  Outcome := Bool × Bool
  outcomeKernel := fun σ => PMF.pure (σ (), true)

/-- Coarse source view: observe only the value, discarding the extra bit. -/
noncomputable def coarseSrc : ViewFamily srcForm Unit (fun _ => Bool) :=
  ViewFamily.const Prod.fst

/-- Coarse target view: observe only the value. -/
noncomputable def coarseTgt : ViewFamily tgtForm Unit (fun _ => Bool) :=
  ViewFamily.const Prod.fst

/-- Rich source view: observe the whole `(value, bit)` outcome. -/
noncomputable def richSrc : ViewFamily srcForm Unit (fun _ => Bool × Bool) :=
  ViewFamily.const id

/-- Rich target view: observe the whole `(value, bit)` outcome. -/
noncomputable def richTgt : ViewFamily tgtForm Unit (fun _ => Bool × Bool) :=
  ViewFamily.const id

/-- The designated profile, playing `false`. -/
noncomputable def designatedProfile : srcForm.Profile := fun _ => false

/-- **Positive half.** The identity profile map is a transport at the coarse view:
it preserves the observed value law and backtranslates every constant deviation,
because the extra bit is invisible to the coarse view. -/
noncomputable def coarseTransport :
    Transport srcForm tgtForm coarseSrc coarseTgt
      srcForm.constantDeviationProfileFamily tgtForm.constantDeviationProfileFamily :=
  Transport.ofConstantProfileMap coarseSrc coarseTgt id
    (by
      intro i σ
      simp [coarseSrc, coarseTgt, ViewFamily.plaw, ViewFamily.const, srcForm, tgtForm,
        PMF.pure_map])
    (by
      intro who sH
      refine ⟨sH, ?_⟩
      intro σ
      cases who
      simp [coarseSrc, coarseTgt, ViewFamily.plaw, ViewFamily.const, srcForm, tgtForm,
        PMF.pure_map])

/-- **Negative half (law).** No realization at the rich view can relate the
designated pair: `law_eq` would force the observed `(value, bit)` laws equal, but
the source records bit `false` and the target bit `true`. -/
theorem rich_law_eq_fails
    (R : Realization srcForm tgtForm richSrc richTgt)
    (hrel : R.rel (PMF.pure designatedProfile) (PMF.pure designatedProfile)) : False := by
  have h := R.law_eq hrel ()
  simp only [ViewFamily.claw, richSrc, richTgt, ViewFamily.const_observe,
    correlatedOutcome_pure, srcForm, tgtForm, PMF.map_id, designatedProfile] at h
  exact pmf_pure_ne_pure (show ((false, false) : Bool × Bool) ≠ (false, true) by decide) h

/-- The rich-view preference under which a deviation is unprofitable unless its
observed law is the point mass at `(true, true)` — a preference legible only to
the extra bit. -/
def richPref : Unit → PMF (Bool × Bool) → PMF (Bool × Bool) → Prop :=
  fun _ _ new => new ≠ PMF.pure (true, true)

/-- **Negative half (equilibrium consequence).** The designated profile is a Nash
equilibrium in the source under the rich-view preference: every source deviation
keeps the bit at `false`, so no deviation reaches the point mass at `(true, true)`. -/
theorem source_nash_richPref :
    srcForm.IsNashFor (observedPref richSrc richPref) designatedProfile := by
  rw [isNashFor_iff]
  intro who s'
  simp only [observedPref, richSrc, ViewFamily.const_observe, srcForm, PMF.map_id,
    richPref]
  exact pmf_pure_ne_pure
    (show ((Function.update designatedProfile who s') (), false) ≠ (true, true) from
      fun heq => (by decide : (false : Bool) ≠ true) (congrArg Prod.snd heq))

/-- Its target image is **not** a Nash equilibrium under the rich-view preference:
deviating to `true` reaches the point mass at `(true, true)`. So the equilibrium
does not transport across the rich view, though the coarse view admits a transport. -/
theorem target_not_nash_richPref :
    ¬ tgtForm.IsNashFor (observedPref richTgt richPref) designatedProfile := by
  rw [isNashFor_iff]
  intro hN
  have hdev := hN () true
  simp only [observedPref, richTgt, ViewFamily.const_observe, tgtForm, PMF.map_id,
    richPref, Function.update_self] at hdev
  exact hdev rfl

end SeparationsV

/-! ## U-separation: a coalition reaches an observed law no singleton can -/

namespace SeparationsU

/-- Reroute the all-`true` joint outcome to `(true, false)`, fixing every other
pair: the source game can never produce `(true, true)`. -/
def redirect (p : Bool × Bool) : Bool × Bool :=
  if p = (true, true) then (true, false) else p

/-- The source game: two players with Boolean strategies whose outcome records both
moves but reroutes the all-`true` profile away from `(true, true)`. -/
noncomputable def srcForm : GameForm Bool where
  Strategy := fun _ => Bool
  Outcome := Bool × Bool
  outcomeKernel := fun σ => PMF.pure (redirect (σ true, σ false))

/-- The target game: the outcome records both moves faithfully. -/
noncomputable def tgtForm : GameForm Bool where
  Strategy := fun _ => Bool
  Outcome := Bool × Bool
  outcomeKernel := fun σ => PMF.pure (σ true, σ false)

/-- The status-quo profile: both players play `false`. -/
noncomputable def statusQuo : srcForm.Profile := fun _ => false

/-- The identity view for unilateral units: each player observes the whole outcome. -/
noncomputable def uniSrc : ViewFamily srcForm Bool (fun _ => Bool × Bool) :=
  ViewFamily.const id

/-- The identity view for unilateral units on the target. -/
noncomputable def uniTgt : ViewFamily tgtForm Bool (fun _ => Bool × Bool) :=
  ViewFamily.const id

/-- The identity view for coalition units: a coalition observes the whole outcome. -/
noncomputable def coalSrc : ViewFamily srcForm (Coalition Bool) (fun _ => Bool × Bool) :=
  ViewFamily.const id

/-- The identity view for coalition units on the target. -/
noncomputable def coalTgt : ViewFamily tgtForm (Coalition Bool) (fun _ => Bool × Bool) :=
  ViewFamily.const id

/-- The shared correspondence: the realization relates only the designated
status-quo pair. The same data instantiates the unilateral and coalition views. -/
def relSQ (μG : PMF srcForm.Profile) (μH : PMF tgtForm.Profile) : Prop :=
  μG = PMF.pure statusQuo ∧ μH = PMF.pure statusQuo

/-- The unilateral realization relating the designated pair. -/
noncomputable def uniRealization : Realization srcForm tgtForm uniSrc uniTgt where
  rel := relSQ
  law_eq := by
    rintro μG μH ⟨rfl, rfl⟩ u
    simp [ViewFamily.claw, uniSrc, uniTgt, correlatedOutcome_pure, srcForm, tgtForm,
      PMF.map_id, statusQuo, redirect]

/-- **Positive half.** Every unilateral target deviation is law-matched by the same
source deviation: a single player's move never reaches `(true, true)`, so the
source's reroute is invisible to it. -/
theorem unilateral_simulates :
    uniRealization.Simulates srcForm.constantDeviationProfileFamily
      tgtForm.constantDeviationProfileFamily := by
  rintro μG μH ⟨rfl, rfl⟩ u sH
  refine ⟨sH, ?_⟩
  cases u <;>
    simp [ViewFamily.claw, uniSrc, uniTgt, correlatedOutcome_pure, srcForm, tgtForm,
      PMF.map_id, constantDeviationProfileFamily_deviate, constDeviateDistributionFn_pure,
      statusQuo, redirect, Function.update]

/-- The grand coalition of both players. -/
def grandCoalition : Coalition Bool := ⟨Finset.univ, Finset.univ_nonempty⟩

/-- The coalition realization on the same designated pair. -/
noncomputable def coalRealization : Realization srcForm tgtForm coalSrc coalTgt where
  rel := relSQ
  law_eq := by
    rintro μG μH ⟨rfl, rfl⟩ u
    simp [ViewFamily.claw, coalSrc, coalTgt, correlatedOutcome_pure, srcForm, tgtForm,
      PMF.map_id, statusQuo, redirect]

/-- **Negative half.** The grand coalition's constant deviation setting both players
to `true` reaches the target outcome law `(true, true)`, which no source coalition
deviation matches: the source reroutes every all-`true` profile away from
`(true, true)`. So the coalition simulation fails at the designated pair — the same
`coalitionConstantDeviationFamily` that, restricted to singletons via
`constantToCoalitionHom`, coincides with the unilateral family of the positive half. -/
theorem coalition_simulates_fails :
    ¬ coalRealization.Simulates srcForm.coalitionConstantDeviationFamily
        tgtForm.coalitionConstantDeviationFamily := by
  intro h
  obtain ⟨dG, hdG⟩ :=
    h (show relSQ (PMF.pure statusQuo) (PMF.pure statusQuo) from ⟨rfl, rfl⟩)
      grandCoalition (fun _ _ => true)
  simp only [ViewFamily.claw, coalSrc, coalTgt, ViewFamily.const_observe,
    coalitionConstantDeviationFamily_deviate_pure, correlatedOutcome_pure,
    srcForm, tgtForm, PMF.map_id, statusQuo, grandCoalition, Finset.mem_univ, dite_true] at hdG
  have hne : ∀ p : Bool × Bool, redirect p ≠ (true, true) := by decide
  exact pmf_pure_ne_pure (hne _) hdG

end SeparationsU

/-! ## P-separation: recommendation-dependence and constant replacement are incomparable -/

namespace SeparationsP

/-- The perfectly correlated recommendation device: both players are handed the
same uniformly random bit. Under it, a constant deviation randomizes the outcome
against the context, while a recommendation-dependent deviation can stay locked to
it. -/
noncomputable def corr : PMF (Bool → Bool) :=
  (PMF.uniformOfFintype Bool).bind (fun b => PMF.pure (fun _ => b))

/-! ### Direction: correlated transports, coarse-correlated fails -/

namespace CE

/-- Source game: two players whose Boolean outcome is the parity of their moves.
On the correlated diagonal the parity is constant, but a constant deviation
randomizes it against the uniformly correlated context. -/
noncomputable def srcForm : GameForm Bool where
  Strategy := fun _ => Bool
  Outcome := Bool
  outcomeKernel := fun σ => PMF.pure (σ true ^^ σ false)

/-- Target game: the outcome is constantly `false`. -/
noncomputable def tgtForm : GameForm Bool where
  Strategy := fun _ => Bool
  Outcome := Bool
  outcomeKernel := fun _ => PMF.pure false

/-- Identity view: each unit observes the Boolean outcome. -/
noncomputable def viewSrc : ViewFamily srcForm Bool (fun _ => Bool) := ViewFamily.const id

/-- Identity view on the target. -/
noncomputable def viewTgt : ViewFamily tgtForm Bool (fun _ => Bool) := ViewFamily.const id

/-- Every observed law on the target is the point mass at `false`. -/
theorem claw_tgt_const (u : Bool) (μ : PMF tgtForm.Profile) :
    viewTgt.claw u μ = PMF.pure false := by
  simp only [ViewFamily.claw, viewTgt, ViewFamily.const_observe, PMF.map_id,
    GameForm.correlatedOutcome, Kernel.pushforward_apply, tgtForm, PMF.bind_const]

/-- The honest source law under the correlated device is the point mass at `false`:
the parity of two equal bits is `false`. -/
theorem claw_src_corr (u : Bool) : viewSrc.claw u corr = PMF.pure false := by
  simp only [ViewFamily.claw, viewSrc, ViewFamily.const_observe, PMF.map_id,
    GameForm.correlatedOutcome, Kernel.pushforward_apply, corr, srcForm,
    PMF.bind_bind, PMF.pure_bind, Bool.xor_self, PMF.bind_const]

/-- The realization relating only the designated correlated pair. -/
noncomputable def realization : Realization srcForm tgtForm viewSrc viewTgt where
  rel := fun μG μH => μG = corr ∧ μH = corr
  law_eq := by
    rintro μG μH ⟨rfl, rfl⟩ u
    rw [claw_src_corr, claw_tgt_const]

/-- **Positive half.** Every target recommendation deviation is law-matched by a
source recommendation deviation: the target is observationally constant, and the
source's honest (recommendation-preserving) play already reproduces its law. -/
theorem ce_transports :
    realization.Simulates srcForm.recommendationDeviationFamily
      tgtForm.recommendationDeviationFamily := by
  rintro μG μH ⟨rfl, rfl⟩ u dH
  refine ⟨id, ?_⟩
  rw [claw_tgt_const]
  have hid : srcForm.recommendationDeviationFamily.deviate corr u id = corr := by
    simp only [recommendationDeviationFamily_deviate, GameForm.deviateDistributionFn,
      GameForm.deviateProfileFn, id_eq, Function.update_eq_self, PMF.bind_pure]
  rw [hid, claw_src_corr]

/-- The source observed law after a constant deviation by player `true` is uniform:
replacing one player's move by a fixed bit decorrelates it from the context, so the
parity is uniform. -/
theorem src_claw_const (sG : Bool) :
    viewSrc.claw true (srcForm.constantDeviationProfileFamily.deviate corr true sG)
      = (PMF.uniformOfFintype Bool).bind (fun b => PMF.pure (sG ^^ b)) := by
  simp only [ViewFamily.claw, viewSrc, ViewFamily.const_observe, PMF.map_id,
    constantDeviationProfileFamily_deviate, GameForm.constDeviateDistributionFn,
    GameForm.correlatedOutcome, Kernel.pushforward_apply, corr, srcForm,
    PMF.bind_bind, PMF.pure_bind, Function.update_self,
    Function.update_of_ne (show (false : Bool) ≠ true by decide)]

/-- A uniform mixture through parity is not the point mass at `false`. -/
theorem mix_ne_pure (sG : Bool) :
    (PMF.uniformOfFintype Bool).bind (fun b => PMF.pure (sG ^^ b)) ≠ PMF.pure false := by
  intro heq
  have hval : ((PMF.uniformOfFintype Bool).bind (fun b => PMF.pure (sG ^^ b))) true
      = (PMF.pure false : PMF Bool) true := by rw [heq]
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool] at hval
  simp only [PMF.uniformOfFintype_apply, PMF.pure_apply, Fintype.card_bool] at hval
  cases sG <;> simp [ENNReal.inv_eq_zero] at hval

/-- **Negative half.** The constant target deviation of player `true` to `false`
observes `false`, but the only source deviation reproducing that law is the honest
recommendation-preserving one — every source *constant* deviation observes the
uniform law instead. So the coarse-correlated simulation fails at the designated
pair. -/
theorem cce_fails :
    ¬ realization.Simulates srcForm.constantDeviationProfileFamily
      tgtForm.constantDeviationProfileFamily := by
  intro h
  obtain ⟨sG, hsG⟩ :=
    h (show realization.rel corr corr from ⟨rfl, rfl⟩) true false
  rw [claw_tgt_const, src_claw_const] at hsG
  exact mix_ne_pure sG hsG

end CE

/-! ### Direction: coarse-correlated transports, correlated fails -/

namespace CCE

/-- Source game: the outcome is `true` exactly when player `false` plays `true`
against player `true` playing `false`. On the correlated diagonal it is `false`. -/
noncomputable def srcForm : GameForm Bool where
  Strategy := fun _ => Bool
  Outcome := Bool
  outcomeKernel := fun σ => PMF.pure (!σ true && σ false)

/-- Target game: the outcome is the parity of the two moves. -/
noncomputable def tgtForm : GameForm Bool where
  Strategy := fun _ => Bool
  Outcome := Bool
  outcomeKernel := fun σ => PMF.pure (σ true ^^ σ false)

/-- Identity view: each unit observes the Boolean outcome. -/
noncomputable def viewSrc : ViewFamily srcForm Bool (fun _ => Bool) := ViewFamily.const id

/-- Identity view on the target. -/
noncomputable def viewTgt : ViewFamily tgtForm Bool (fun _ => Bool) := ViewFamily.const id

/-- A uniform mixture composed with a parity flip is again uniform: parity by a
fixed bit is a bijection of `Bool`. -/
theorem bind_xor_uniform (s : Bool) :
    (PMF.uniformOfFintype Bool).bind (fun b => PMF.pure (s ^^ b)) = PMF.uniformOfFintype Bool := by
  ext x
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp only [PMF.uniformOfFintype_apply, PMF.pure_apply, Fintype.card_bool]
  cases s <;> cases x <;> simp

/-- The honest source law under the correlated device is the point mass at `false`. -/
theorem claw_src_corr (u : Bool) : viewSrc.claw u corr = PMF.pure false := by
  have h : (fun b => PMF.pure (!b && b) : Bool → PMF Bool) = fun _ => PMF.pure false := by
    funext b; cases b <;> rfl
  simp only [ViewFamily.claw, viewSrc, ViewFamily.const_observe, PMF.map_id,
    GameForm.correlatedOutcome, Kernel.pushforward_apply, corr, srcForm,
    PMF.bind_bind, PMF.pure_bind]
  rw [h, PMF.bind_const]

/-- The honest target law under the correlated device is the point mass at `false`. -/
theorem claw_tgt_corr (u : Bool) : viewTgt.claw u corr = PMF.pure false := by
  simp only [ViewFamily.claw, viewTgt, ViewFamily.const_observe, PMF.map_id,
    GameForm.correlatedOutcome, Kernel.pushforward_apply, corr, tgtForm,
    PMF.bind_bind, PMF.pure_bind, Bool.xor_self, PMF.bind_const]

/-- The realization relating only the designated correlated pair. -/
noncomputable def realization : Realization srcForm tgtForm viewSrc viewTgt where
  rel := fun μG μH => μG = corr ∧ μH = corr
  law_eq := by
    rintro μG μH ⟨rfl, rfl⟩ u
    rw [claw_src_corr, claw_tgt_corr]

/-- Every target constant deviation observes the uniform law: replacing one move
by a fixed bit decorrelates the parity. -/
theorem tgt_const_claw (u s : Bool) :
    viewTgt.claw u (tgtForm.constantDeviationProfileFamily.deviate corr u s)
      = PMF.uniformOfFintype Bool := by
  cases u
  · simp only [ViewFamily.claw, viewTgt, ViewFamily.const_observe, PMF.map_id,
      constantDeviationProfileFamily_deviate, GameForm.constDeviateDistributionFn,
      GameForm.correlatedOutcome, Kernel.pushforward_apply, corr, tgtForm,
      PMF.bind_bind, PMF.pure_bind, Function.update_self,
      Function.update_of_ne (show (true : Bool) ≠ false by decide)]
    rw [show (fun b => PMF.pure (b ^^ s)) = (fun b => PMF.pure (s ^^ b)) from by
      funext b; rw [Bool.xor_comm], bind_xor_uniform]
  · simp only [ViewFamily.claw, viewTgt, ViewFamily.const_observe, PMF.map_id,
      constantDeviationProfileFamily_deviate, GameForm.constDeviateDistributionFn,
      GameForm.correlatedOutcome, Kernel.pushforward_apply, corr, tgtForm,
      PMF.bind_bind, PMF.pure_bind, Function.update_self,
      Function.update_of_ne (show (false : Bool) ≠ true by decide)]
    rw [bind_xor_uniform]

/-- Player `true`'s constant deviation to `false` observes the uniform law in the
source: it always plays `false`, so the outcome tracks the uniform context. -/
theorem src_const_D_false :
    viewSrc.claw true (srcForm.constantDeviationProfileFamily.deviate corr true false)
      = PMF.uniformOfFintype Bool := by
  simp only [ViewFamily.claw, viewSrc, ViewFamily.const_observe, PMF.map_id,
    constantDeviationProfileFamily_deviate, GameForm.constDeviateDistributionFn,
    GameForm.correlatedOutcome, Kernel.pushforward_apply, corr, srcForm,
    PMF.bind_bind, PMF.pure_bind, Function.update_self,
    Function.update_of_ne (show (false : Bool) ≠ true by decide),
    Bool.not_false, Bool.true_and, PMF.bind_pure]

/-- Player `false`'s constant deviation to `true` observes the uniform law in the
source: the outcome becomes the negation of the uniform context. -/
theorem src_const_X_true :
    viewSrc.claw false (srcForm.constantDeviationProfileFamily.deviate corr false true)
      = PMF.uniformOfFintype Bool := by
  have h : (fun b => PMF.pure (!b) : Bool → PMF Bool) = fun b => PMF.pure (true ^^ b) := by
    funext b; rw [Bool.true_xor]
  simp only [ViewFamily.claw, viewSrc, ViewFamily.const_observe, PMF.map_id,
    constantDeviationProfileFamily_deviate, GameForm.constDeviateDistributionFn,
    GameForm.correlatedOutcome, Kernel.pushforward_apply, corr, srcForm,
    PMF.bind_bind, PMF.pure_bind, Function.update_self,
    Function.update_of_ne (show (true : Bool) ≠ false by decide),
    Bool.and_true]
  rw [h, bind_xor_uniform]

/-- **Positive half.** Every target constant deviation is law-matched by a source
constant deviation: both observe the uniform law, so coarse-correlated equilibrium
transports across the designated pair. -/
theorem cce_transports :
    realization.Simulates srcForm.constantDeviationProfileFamily
      tgtForm.constantDeviationProfileFamily := by
  rintro μG μH ⟨rfl, rfl⟩ u sH
  cases u
  · exact ⟨true, by rw [src_const_X_true, tgt_const_claw]⟩
  · exact ⟨false, by rw [src_const_D_false, tgt_const_claw]⟩

/-- The target recommendation deviation that anti-correlates with the recommendation
observes the point mass at `true`: flipping the recommended move makes the parity
constantly `true`. -/
theorem tgt_rec_not :
    viewTgt.claw true (tgtForm.recommendationDeviationFamily.deviate corr true (fun b => !b))
      = PMF.pure true := by
  have h : (fun b => PMF.pure (!b ^^ b) : Bool → PMF Bool) = fun _ => PMF.pure true := by
    funext b; cases b <;> rfl
  simp only [ViewFamily.claw, viewTgt, ViewFamily.const_observe, PMF.map_id,
    recommendationDeviationFamily_deviate, GameForm.deviateDistributionFn,
    GameForm.deviateProfileFn, GameForm.correlatedOutcome, Kernel.pushforward_apply,
    corr, tgtForm, PMF.bind_bind, PMF.pure_bind, Function.update_self,
    Function.update_of_ne (show (false : Bool) ≠ true by decide)]
  rw [h, PMF.bind_const]

/-- The source observed law after any recommendation deviation by player `true`. -/
theorem src_rec_claw (dG : Bool → Bool) :
    viewSrc.claw true (srcForm.recommendationDeviationFamily.deviate corr true dG)
      = (PMF.uniformOfFintype Bool).bind (fun b => PMF.pure (!(dG b) && b)) := by
  simp only [ViewFamily.claw, viewSrc, ViewFamily.const_observe, PMF.map_id,
    recommendationDeviationFamily_deviate, GameForm.deviateDistributionFn,
    GameForm.deviateProfileFn, GameForm.correlatedOutcome, Kernel.pushforward_apply,
    corr, srcForm, PMF.bind_bind, PMF.pure_bind, Function.update_self,
    Function.update_of_ne (show (false : Bool) ≠ true by decide)]

/-- **Negative half.** The target recommendation deviation observing `true` has no
matching source recommendation deviation: every source deviation keeps mass on
`false` at the branch where the context is `false`, so it cannot observe the point
mass at `true`. So the correlated simulation fails at the designated pair. -/
theorem ce_fails :
    ¬ realization.Simulates srcForm.recommendationDeviationFamily
      tgtForm.recommendationDeviationFamily := by
  intro h
  obtain ⟨dG, hdG⟩ :=
    h (show realization.rel corr corr from ⟨rfl, rfl⟩) true (fun b => !b)
  rw [tgt_rec_not, src_rec_claw] at hdG
  have hval : ((PMF.uniformOfFintype Bool).bind (fun b => PMF.pure (!(dG b) && b))) false
      = (PMF.pure true : PMF Bool) false := by rw [hdG]
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool] at hval
  simp only [PMF.uniformOfFintype_apply, PMF.pure_apply, Fintype.card_bool,
    Bool.and_false, Bool.and_true] at hval
  cases dG true <;> simp [ENNReal.inv_eq_zero] at hval

end CCE

end SeparationsP

end GameForm

end GameTheory
