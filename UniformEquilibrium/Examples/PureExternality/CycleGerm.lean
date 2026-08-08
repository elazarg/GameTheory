/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import UniformEquilibrium.VanishingDiscount.Analytic.Endpoint.Atlas
import UniformEquilibrium.Examples.PureExternality.Cycle

/-!
# Germ-level Bellman tagging of the pure-externality cycle

`PureExternalityCycleHolonomy.lean` reads the two unilateral deviation rows of
the two-state pure-externality cycle off the payoff table and explicitly
records that it does **not** formalize a germ-level tagging layer.  This file
supplies that layer, as a complete vertical slice: two **explicit**
`AnalyticBellmanGerm`s of `PureExternalityCycle.game`, each pushed through the
analytic hierarchy (`FiniteBiasSeed`, `FirstHierarchyResponse`) and the honest
endpoint atlas (`AnalyticEndpointAtlasLeaf`), with the resulting leaf
identified.

## What is instantiated

Both germs use ramification `q = 1` and radius `1`, so the curve parameter `t`
*is* the discount complement `λ = 1 - β`.

* `oneGerm` — the constant-`1` profile.  Assignment `mix s i a ↦ 1` at
  `a = 1` and `0` at `a = 0`, `val s i ↦ 1`, `disc ↦ t`; constant in `t`
  apart from the discount coordinate.
* `prescribedGerm` — the **prescribed** constant-`0` profile of the source
  note, whose discounted values genuinely move with the discount:
  `val s i ↦ (t / (2 - t)) · r s i` where `r s i = stagePayoffOf s i false`
  is `1` for the controller and `-1` for the other player.  This is the
  unique solution of the Bellman recursion `c = λ - (1 - λ) c` at `λ = t`,
  i.e. of `c · (2 - t) = t`.

Every field of `AnalyticBellmanGerm` is instantiated with this rational data:

* `analytic_assignment` — coordinatewise via `analyticAt_pi_iff`; the
  coordinates are constants, the identity, and `t / (2 - t)`, analytic at `0`
  because `2 - 0 ≠ 0`;
* `solution` — obtained from the **semantic** Bellman equilibrium via
  `isPolynomialBellmanSolution_bellmanAssignment`, so the polynomial
  equalities never have to be evaluated by hand.  The single semantic input is
  `discountedAuxEU_const`: against opponents playing the pure action `b`,
  player `who`'s auxiliary payoff at state `s` is
  `(1 - β) · stagePayoffOf s who b + β · V (!s) who`, whatever `who`
  themselves do.  That one identity covers the on-path profile *and* every
  unilateral deviation, because a player's own payoff at the state they
  control is action-independent (pure externality) and transitions ignore all
  actions.  Consequently every best-response inequality holds with **zero
  slack**, at every discount factor;
* `discountCoordinate` — `1 - (1 - t) = t ^ 1`.

## The identified leaf

`oneGerm` has a constant value curve, so its value increment vanishes and its
finite-bias factor is `0`: it is the degenerate finite-bias case, with
selected relative bias `H = 0`.  `prescribedGerm` has value increment
`t · (2 - t)⁻¹ · r`, so its finite-bias factor is `(2 - t)⁻¹ · r` and its
selected relative bias is `H s i = r s i / 2 ≠ 0` — a **nondegenerate**
finite-bias seed.

Both endpoint values are already certified uniform equilibrium payoffs of the
game (`isUniformEquilibriumPayoff_one`, `isUniformEquilibriumPayoff_zero`), so
in both cases the endpoint atlas leaf is the **semantic** leaf
`AnalyticEndpointAtlasLeaf.semanticClose`, whose `RequiredReconstructionAt` is
`PUnit` (every other branch of that definition names a nontrivial
reconstruction structure).  The consumption eliminator
`semanticClose_or_certificate_of_resolution` therefore returns on both germs
with no reconstruction hypothesis supplied.  In particular a nonzero finite
relative bias is, on this game, not an obstruction — the same message the
holonomy acceptance test carries for positive mixed holonomy.

## Main definitions

* `PureExternalityCycle.constMixedProfile` — the constant stationary profile
* `PureExternalityCycle.oneGerm`, `PureExternalityCycle.prescribedGerm` — the
  two explicit analytic Bellman germs
* `PureExternalityCycle.oneFiniteBiasSeed`,
  `PureExternalityCycle.prescribedFiniteBiasSeed` — their explicit finite-bias
  seeds, and `..FirstHierarchyResponse` the resulting hierarchy responses
* `PureExternalityCycle.oneEndpointLeaf`,
  `PureExternalityCycle.prescribedEndpointLeaf` — the identified atlas leaves,
  with their trivial resolutions `..EndpointResolution`

## Main results

* `PureExternalityCycle.discountedAuxEU_const` — the one-stage identity
* `PureExternalityCycle.isDiscountedStationaryBellmanEq_one`,
  `PureExternalityCycle.isDiscountedStationaryBellmanEq_prescribed` — the exact
  Bellman equalities and (zero-slack) best-response inequalities
* `PureExternalityCycle.oneGerm_endpointValue`,
  `PureExternalityCycle.prescribedGerm_endpointValue` — endpoint values
  `(1, 1)` and `(0, 0)`
* `PureExternalityCycle.prescribedFiniteBiasSeed_H_ne_zero` — the prescribed
  germ has nonzero finite relative bias
* `PureExternalityCycle.nonempty_oneEndpointLeaf`,
  `PureExternalityCycle.nonempty_prescribedEndpointLeaf` — the existing
  classification path `ofFirstHierarchyResponse` run on the explicit germs
* `PureExternalityCycle.germ_endpointLeaf_isSemanticClose` — **the capstone**

## Scope and gap

Only stationary *pure* profiles are tagged, and only the two whose endpoint
payoffs the game file already certifies.  Nothing here resolves any
nonsemantic leaf, and no claim is made that the classification path
`ofFirstHierarchyResponse` *chooses* the semantic leaf: it returns
`Nonempty`, and the semantic leaf is exhibited separately.
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

namespace PureExternalityCycle

open Math.Probability Math.PMFProduct

/-! ## The constant stationary profiles and the one-stage identity -/

/-- The stationary mixed profile in which every player plays the pure action
`b` at every state. -/
def constMixedProfile (b : Bool) : game.StationaryMixedProfile :=
  fun _ _ => PMF.pure b

@[simp] theorem constMixedProfile_apply (b : Bool) (s : Bool) (i : Player) :
    constMixedProfile b s i = PMF.pure b :=
  rfl

/-- After a unilateral deviation by `who`, the component of the constant
profile at a state `who` does not control is still the pure action `b`. -/
theorem update_constMixedProfile_apply (b : Bool) (s : Bool) (who : Player)
    (d : PMF (game.Act who)) (hne : who ≠ s) :
    Function.update (constMixedProfile b s) who d s = PMF.pure b :=
  Function.update_of_ne (Ne.symm hne) d (constMixedProfile b s)

/-- **The one-stage identity.**  Suppose the stage randomization `m` puts the
pure action `b` on the *controller* of state `s` whenever that controller is
not `who` themselves.  Then player `who`'s discounted auxiliary payoff with
continuation vector `V` is the deterministic value below — it does not mention
`m who` at all.

Both the on-path profile and every unilateral deviation satisfy the
hypothesis: at the state `who` controls, `who`'s own payoff is
action-independent (pure externality), and at the other state `who` is not the
controller.  Transitions ignore all actions, so the continuation is read at
the flipped state. -/
theorem discountedAuxEU_const (β : ℝ) (V : Bool → Payoff Player) (b : Bool)
    (s : Bool) (who : Player) (m : ∀ i : Player, PMF (game.Act i))
    (hm : who ≠ s → m s = PMF.pure b) :
    game.discountedAuxEU β V s m who =
      (1 - β) * stagePayoffOf s who b + β * V (!s) who := by
  have hcoord : ∀ u : Bool → ℝ,
      expect (pmfPi m) (fun a : game.JointAct => u (a s)) = expect (m s) u := by
    intro u
    have hmap :
        PMF.map (fun a : game.JointAct => a s) (pmfPi m) = m s :=
      pmfPi_push_coord m s
    calc expect (pmfPi m) (fun a : game.JointAct => u (a s))
        = expect (PMF.map (fun a : game.JointAct => a s) (pmfPi m)) u :=
          (expect_map _ _ _).symm
      _ = expect (m s) u := by rw [hmap]
  have hstage :
      expect (pmfPi m) (fun a : game.JointAct => game.stagePayoff s a who) =
        stagePayoffOf s who b := by
    have hrw : (fun a : game.JointAct => game.stagePayoff s a who) =
        fun a : game.JointAct => stagePayoffOf s who (a s) := rfl
    rw [hrw, hcoord (fun c => stagePayoffOf s who c)]
    by_cases hs : who = s
    · have hconst : (fun c : Bool => stagePayoffOf s who c) = fun _ => (1 : ℝ) := by
        funext c
        simp [stagePayoffOf, hs]
      rw [hconst, expect_const]
      simp [stagePayoffOf, hs]
    · rw [hm hs, expect_pure]
  have hcont :
      expect (pmfPi m) (fun a : game.JointAct =>
        expect (game.transition s a) (fun s' => V s' who)) = V (!s) who := by
    have hinner : ∀ a : game.JointAct,
        expect (game.transition s a) (fun s' => V s' who) = V (!s) who := by
      intro a
      rw [transition_eq, expect_pure]
    simp_rw [hinner]
    exact expect_const _ _
  rw [game.discountedAuxEU_eq, hstage, hcont]

/-! ## The constant-`1` germ -/

/-- The constant payoff vector `(1, 1)` at every state: the discounted value
of the constant-`1` profile, at every discount factor. -/
def oneValue : Bool → Payoff Player := fun _ _ => 1

@[simp] theorem oneValue_apply (s : Bool) (i : Player) : oneValue s i = 1 := rfl

/-- **The exact Bellman data of the constant-`1` profile.**  At every discount
factor the constant-`1` stationary profile together with the constant value
`1` is a discounted stationary Bellman equilibrium: the value equalities hold
exactly, and every pure unilateral deviation attains exactly the same value,
so every best-response inequality holds with zero slack. -/
theorem isDiscountedStationaryBellmanEq_one (β : ℝ) :
    game.IsDiscountedStationaryBellmanEq β (constMixedProfile true) oneValue := by
  have key : ∀ (s : Bool) (who : Player) (m : ∀ i : Player, PMF (game.Act i)),
      (who ≠ s → m s = PMF.pure true) →
      game.discountedAuxEU β oneValue s m who = 1 := by
    intro s who m hm
    rw [discountedAuxEU_const β oneValue true s who m hm, stagePayoffOf_true,
      oneValue_apply]
    ring
  refine ⟨fun s who d => ?_, fun s who => ?_⟩
  · have hdev :
        game.discountedAuxEU β oneValue s
          (Function.update (constMixedProfile true s) who d) who = 1 :=
      key s who _ (fun hne => update_constMixedProfile_apply true s who d hne)
    have hon :
        game.discountedAuxEU β oneValue s (constMixedProfile true s) who = 1 :=
      key s who _ (fun _ => rfl)
    rw [hdev, hon]
  · exact key s who _ (fun _ => rfl)

/-- The Bellman assignment curve of the constant-`1` germ. -/
def oneAssignment (t : ℝ) : BellmanVar game → ℝ :=
  game.bellmanAssignment (constMixedProfile true) oneValue (1 - t)

@[simp] theorem oneAssignment_disc (t : ℝ) :
    oneAssignment t BellmanVar.disc = t := by
  change (1 : ℝ) - (1 - t) = t
  ring

@[simp] theorem oneAssignment_val (t : ℝ) (s : Bool) (i : Player) :
    oneAssignment t (BellmanVar.val s i) = 1 :=
  rfl

theorem analyticAt_oneAssignment : AnalyticAt ℝ oneAssignment 0 := by
  rw [analyticAt_pi_iff]
  intro v
  cases v with
  | mix s i a => exact analyticAt_const
  | val s i => exact analyticAt_const
  | disc =>
      have hrw : (fun t : ℝ => oneAssignment t BellmanVar.disc) = fun t : ℝ => t := by
        funext t
        exact oneAssignment_disc t
      rw [hrw]
      exact analyticAt_id

/-- **The constant-`1` analytic Bellman germ of the pure-externality cycle.** -/
def oneGerm : game.AnalyticBellmanGerm where
  ramification := 1
  radius := 1
  assignment := oneAssignment
  ramification_pos := Nat.one_pos
  radius_pos := one_pos
  analytic_assignment := analyticAt_oneAssignment
  solution := fun t _ =>
    game.isPolynomialBellmanSolution_bellmanAssignment
      (isDiscountedStationaryBellmanEq_one (1 - t))
  discountCoordinate := fun t _ => by
    rw [oneAssignment_disc, pow_one]

@[simp] theorem oneGerm_ramification : oneGerm.ramification = 1 := rfl

@[simp] theorem oneGerm_radius : oneGerm.radius = 1 := rfl

/-- The decoded value curve of the constant-`1` germ is constant. -/
theorem oneGerm_valueCurve (t : ℝ) : oneGerm.valueCurve t = oneValue := rfl

/-- The endpoint value of the constant-`1` germ is the payoff `(1, 1)`. -/
theorem oneGerm_endpointValue : oneGerm.endpointValue = fun _ _ => (1 : ℝ) := rfl

/-- The value increment of the constant-`1` germ vanishes identically. -/
theorem oneGerm_valueIncrement (t : ℝ) : oneGerm.valueIncrement t = 0 := by
  change oneGerm.valueCurve t - oneGerm.endpointValue = 0
  rw [oneGerm_valueCurve, oneGerm_endpointValue]
  funext s i
  simp

/-- The constant-`1` germ is the degenerate finite-bias case: the value
increment vanishes, so the relative-bias curve extends by the zero factor. -/
def oneFiniteBiasSeed : oneGerm.FiniteBiasSeed where
  factor := fun _ => 0
  analytic_factor := analyticAt_const
  valueIncrement_eq := Filter.Eventually.of_forall fun t => by
    rw [oneGerm_valueIncrement, smul_zero]

/-- The selected finite relative bias of the constant-`1` germ is `0`. -/
theorem oneFiniteBiasSeed_H : oneFiniteBiasSeed.H = 0 :=
  oneFiniteBiasSeed.extension_zero

/-- The explicit canonical first hierarchy response of the constant-`1` germ,
relative to the empty processed harmonic span. -/
def oneFirstHierarchyResponse :
    oneGerm.FirstHierarchyResponse
      (AnalyticBellmanGerm.EndpointHarmonicJetSpan.empty oneGerm) :=
  .finiteBias oneFiniteBiasSeed

/-- The existing endpoint classification path runs on the explicit
constant-`1` germ. -/
theorem nonempty_oneEndpointLeaf (entry : Bool) :
    Nonempty
      (oneGerm.AnalyticEndpointAtlasLeaf
        (AnalyticBellmanGerm.EndpointHarmonicJetSpan.empty oneGerm) entry) :=
  AnalyticBellmanGerm.AnalyticEndpointAtlasLeaf.ofFirstHierarchyResponse
    (entry := entry) oneFirstHierarchyResponse

/-- The endpoint value of the constant-`1` germ is a uniform equilibrium
payoff of the pure-externality cycle. -/
theorem oneGerm_isUniformEquilibriumPayoff (entry : Bool) :
    game.IsUniformEquilibriumPayoff entry (oneGerm.endpointValue entry) := by
  rw [oneGerm_endpointValue]
  exact isUniformEquilibriumPayoff_one entry

/-- **The identified leaf of the constant-`1` germ**: the semantic leaf. -/
def oneEndpointLeaf (entry : Bool) :
    oneGerm.AnalyticEndpointAtlasLeaf
      (AnalyticBellmanGerm.EndpointHarmonicJetSpan.empty oneGerm) entry :=
  .semanticClose (oneGerm_isUniformEquilibriumPayoff entry)

/-- The semantic leaf carries no reconstruction obligation. -/
def oneEndpointResolution (entry : Bool) (error : ℝ) :
    (oneEndpointLeaf entry).ResolutionAt error :=
  PUnit.unit

/-! ## The prescribed constant-`0` germ -/

/-- The discounted bias scale of the prescribed profile: the unique solution
`c` of the Bellman recursion `c = λ - (1 - λ) c`, i.e. of `c · (2 - λ) = λ`. -/
def biasScale (t : ℝ) : ℝ := t / (2 - t)

@[simp] theorem biasScale_zero : biasScale 0 = 0 := by
  unfold biasScale
  norm_num

/-- The defining identity of the bias scale, away from the pole `t = 2`. -/
theorem biasScale_mul_two_sub {t : ℝ} (ht : t ≠ 2) :
    biasScale t * (2 - t) = t := by
  have h : (2 : ℝ) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  unfold biasScale
  field_simp

theorem analyticAt_biasScale : AnalyticAt ℝ biasScale 0 := by
  have hden : AnalyticAt ℝ (fun t : ℝ => 2 - t) 0 :=
    analyticAt_const.sub analyticAt_id
  have h0 : (2 : ℝ) - 0 ≠ 0 := by norm_num
  have hinv : AnalyticAt ℝ (fun t : ℝ => (2 - t)⁻¹) 0 :=
    AnalyticAt.fun_inv hden h0
  have hrw : biasScale = fun t : ℝ => t * (2 - t)⁻¹ := by
    funext t
    unfold biasScale
    rw [div_eq_mul_inv]
  rw [hrw]
  exact analyticAt_id.mul hinv

/-- The discounted value vector of the prescribed constant-`0` profile:
`biasScale t` times the prescribed stage payoff `1` for the controller of the
state and `-1` for the other player. -/
def prescribedValue (t : ℝ) : Bool → Payoff Player :=
  fun s i => biasScale t * stagePayoffOf s i false

@[simp] theorem prescribedValue_apply (t : ℝ) (s : Bool) (i : Player) :
    prescribedValue t s i = biasScale t * stagePayoffOf s i false :=
  rfl

/-- **The exact Bellman data of the prescribed profile.**  At discount factor
`β = 1 - t` (any `t ≠ 2`) the prescribed constant-`0` stationary profile
together with the value `biasScale t · r` is a discounted stationary Bellman
equilibrium.  Again every pure unilateral deviation attains exactly the same
value, so every best-response inequality holds with zero slack. -/
theorem isDiscountedStationaryBellmanEq_prescribed {t : ℝ} (ht : t ≠ 2) :
    game.IsDiscountedStationaryBellmanEq (1 - t) (constMixedProfile false)
      (prescribedValue t) := by
  have hc : biasScale t * (2 - t) = t := biasScale_mul_two_sub ht
  have key : ∀ (s : Bool) (who : Player) (m : ∀ i : Player, PMF (game.Act i)),
      (who ≠ s → m s = PMF.pure false) →
      game.discountedAuxEU (1 - t) (prescribedValue t) s m who =
        prescribedValue t s who := by
    intro s who m hm
    rw [discountedAuxEU_const (1 - t) (prescribedValue t) false s who m hm,
      prescribedValue_apply, prescribedValue_apply, stagePayoffOf_not]
    linear_combination (-(stagePayoffOf s who false)) * hc
  refine ⟨fun s who d => ?_, fun s who => ?_⟩
  · have hdev :
        game.discountedAuxEU (1 - t) (prescribedValue t) s
            (Function.update (constMixedProfile false s) who d) who =
          prescribedValue t s who :=
      key s who _ (fun hne => update_constMixedProfile_apply false s who d hne)
    have hon :
        game.discountedAuxEU (1 - t) (prescribedValue t) s
            (constMixedProfile false s) who =
          prescribedValue t s who :=
      key s who _ (fun _ => rfl)
    rw [hdev, hon]
  · exact key s who _ (fun _ => rfl)

/-- The Bellman assignment curve of the prescribed germ. -/
def prescribedAssignment (t : ℝ) : BellmanVar game → ℝ :=
  game.bellmanAssignment (constMixedProfile false) (prescribedValue t) (1 - t)

@[simp] theorem prescribedAssignment_disc (t : ℝ) :
    prescribedAssignment t BellmanVar.disc = t := by
  change (1 : ℝ) - (1 - t) = t
  ring

@[simp] theorem prescribedAssignment_val (t : ℝ) (s : Bool) (i : Player) :
    prescribedAssignment t (BellmanVar.val s i) =
      biasScale t * stagePayoffOf s i false :=
  rfl

theorem analyticAt_prescribedAssignment : AnalyticAt ℝ prescribedAssignment 0 := by
  rw [analyticAt_pi_iff]
  intro v
  cases v with
  | mix s i a => exact analyticAt_const
  | val s i =>
      have hrw : (fun t : ℝ => prescribedAssignment t (BellmanVar.val s i)) =
          fun t : ℝ => biasScale t * stagePayoffOf s i false := by
        funext t
        exact prescribedAssignment_val t s i
      rw [hrw]
      exact analyticAt_biasScale.mul analyticAt_const
  | disc =>
      have hrw :
          (fun t : ℝ => prescribedAssignment t BellmanVar.disc) = fun t : ℝ => t := by
        funext t
        exact prescribedAssignment_disc t
      rw [hrw]
      exact analyticAt_id

/-- **The prescribed analytic Bellman germ of the pure-externality cycle.**
Unlike `oneGerm`, its value curve genuinely moves with the discount. -/
def prescribedGerm : game.AnalyticBellmanGerm where
  ramification := 1
  radius := 1
  assignment := prescribedAssignment
  ramification_pos := Nat.one_pos
  radius_pos := one_pos
  analytic_assignment := analyticAt_prescribedAssignment
  solution := fun t ht =>
    game.isPolynomialBellmanSolution_bellmanAssignment
      (isDiscountedStationaryBellmanEq_prescribed
        (ne_of_lt (ht.2.trans one_lt_two)))
  discountCoordinate := fun t _ => by
    rw [prescribedAssignment_disc, pow_one]

@[simp] theorem prescribedGerm_ramification : prescribedGerm.ramification = 1 := rfl

@[simp] theorem prescribedGerm_radius : prescribedGerm.radius = 1 := rfl

/-- The decoded value curve of the prescribed germ. -/
theorem prescribedGerm_valueCurve (t : ℝ) :
    prescribedGerm.valueCurve t = prescribedValue t :=
  rfl

/-- The endpoint value of the prescribed germ is the payoff `(0, 0)`. -/
theorem prescribedGerm_endpointValue :
    prescribedGerm.endpointValue = fun _ _ => (0 : ℝ) := by
  have h : prescribedGerm.endpointValue = prescribedValue 0 := rfl
  rw [h]
  funext s i
  simp

/-- The value increment of the prescribed germ is its whole value curve. -/
theorem prescribedGerm_valueIncrement (t : ℝ) :
    prescribedGerm.valueIncrement t = prescribedValue t := by
  change prescribedGerm.valueCurve t - prescribedGerm.endpointValue =
    prescribedValue t
  rw [prescribedGerm_valueCurve, prescribedGerm_endpointValue]
  funext s i
  simp

/-- The finite-bias factor of the prescribed germ: the value increment divided
by the discount complement `t`. -/
def prescribedBiasFactor (t : ℝ) : Bool → Payoff Player :=
  fun s i => (2 - t)⁻¹ * stagePayoffOf s i false

theorem analyticAt_prescribedBiasFactor :
    AnalyticAt ℝ prescribedBiasFactor 0 := by
  rw [analyticAt_pi_iff]
  intro s
  rw [analyticAt_pi_iff]
  intro i
  have hrw : (fun t : ℝ => prescribedBiasFactor t s i) =
      fun t : ℝ => (2 - t)⁻¹ * stagePayoffOf s i false := rfl
  rw [hrw]
  exact
    (AnalyticAt.fun_inv (analyticAt_const.sub analyticAt_id) (by norm_num)).mul
      analyticAt_const

/-- The prescribed germ is a **nondegenerate** finite-bias case: the value
increment is exactly `t` times the analytic factor `(2 - t)⁻¹ · r`. -/
def prescribedFiniteBiasSeed : prescribedGerm.FiniteBiasSeed where
  factor := prescribedBiasFactor
  analytic_factor := analyticAt_prescribedBiasFactor
  valueIncrement_eq := Filter.Eventually.of_forall fun t => by
    rw [prescribedGerm_valueIncrement]
    funext s i
    simp only [Pi.smul_apply, smul_eq_mul, prescribedValue_apply,
      prescribedBiasFactor, biasScale, prescribedGerm_ramification, pow_one]
    ring

/-- The selected finite relative bias of the prescribed germ is `r / 2`. -/
theorem prescribedFiniteBiasSeed_H :
    prescribedFiniteBiasSeed.H =
      fun s i => (2 : ℝ)⁻¹ * stagePayoffOf s i false := by
  have h : prescribedFiniteBiasSeed.H = prescribedBiasFactor 0 :=
    prescribedFiniteBiasSeed.extension_zero
  rw [h]
  funext s i
  simp [prescribedBiasFactor]

/-- The prescribed germ's finite relative bias is **not** zero: this is a
genuinely nondegenerate finite-bias seed. -/
theorem prescribedFiniteBiasSeed_H_ne_zero : prescribedFiniteBiasSeed.H ≠ 0 := by
  intro hzero
  have h : prescribedFiniteBiasSeed.H x x = 0 := by simp [hzero]
  rw [prescribedFiniteBiasSeed_H] at h
  norm_num [stagePayoffOf] at h

/-- The explicit canonical first hierarchy response of the prescribed germ. -/
def prescribedFirstHierarchyResponse :
    prescribedGerm.FirstHierarchyResponse
      (AnalyticBellmanGerm.EndpointHarmonicJetSpan.empty prescribedGerm) :=
  .finiteBias prescribedFiniteBiasSeed

/-- The existing endpoint classification path runs on the explicit prescribed
germ. -/
theorem nonempty_prescribedEndpointLeaf (entry : Bool) :
    Nonempty
      (prescribedGerm.AnalyticEndpointAtlasLeaf
        (AnalyticBellmanGerm.EndpointHarmonicJetSpan.empty prescribedGerm)
        entry) :=
  AnalyticBellmanGerm.AnalyticEndpointAtlasLeaf.ofFirstHierarchyResponse
    (entry := entry) prescribedFirstHierarchyResponse

/-- The endpoint value of the prescribed germ is a uniform equilibrium payoff
of the pure-externality cycle: it is exactly the `(0, 0)` capstone. -/
theorem prescribedGerm_isUniformEquilibriumPayoff (entry : Bool) :
    game.IsUniformEquilibriumPayoff entry (prescribedGerm.endpointValue entry) := by
  rw [prescribedGerm_endpointValue]
  exact isUniformEquilibriumPayoff_zero entry

/-- **The identified leaf of the prescribed germ**: the semantic leaf, despite
its nonzero finite relative bias. -/
def prescribedEndpointLeaf (entry : Bool) :
    prescribedGerm.AnalyticEndpointAtlasLeaf
      (AnalyticBellmanGerm.EndpointHarmonicJetSpan.empty prescribedGerm) entry :=
  .semanticClose (prescribedGerm_isUniformEquilibriumPayoff entry)

/-- The semantic leaf carries no reconstruction obligation. -/
def prescribedEndpointResolution (entry : Bool) (error : ℝ) :
    (prescribedEndpointLeaf entry).ResolutionAt error :=
  PUnit.unit

/-! ## Running the atlas consumption eliminator -/

/-- The atlas consumption eliminator, run on the constant-`1` germ with no
reconstruction hypothesis supplied, returns the semantic disjunct. -/
theorem oneGerm_semanticClose_or_certificate (entry : Bool) (error : ℝ) :
    game.IsUniformEquilibriumPayoff entry (oneGerm.endpointValue entry) ∨
      game.IsAdaptivePotentialCertificateAt entry
        (oneGerm.endpointValue entry) error :=
  AnalyticBellmanGerm.AnalyticEndpointAtlasLeaf.semanticClose_or_certificate_of_resolution
    (oneEndpointLeaf entry) error (oneEndpointResolution entry error)

/-- The atlas consumption eliminator, run on the prescribed germ with no
reconstruction hypothesis supplied, returns the semantic disjunct. -/
theorem prescribedGerm_semanticClose_or_certificate (entry : Bool) (error : ℝ) :
    game.IsUniformEquilibriumPayoff entry (prescribedGerm.endpointValue entry) ∨
      game.IsAdaptivePotentialCertificateAt entry
        (prescribedGerm.endpointValue entry) error :=
  AnalyticBellmanGerm.AnalyticEndpointAtlasLeaf.semanticClose_or_certificate_of_resolution
    (prescribedEndpointLeaf entry) error (prescribedEndpointResolution entry error)

/-! ## Capstone -/

/-- **Capstone: the vertical analytic slice of the pure-externality cycle.**

`oneGerm` and `prescribedGerm` are explicit analytic Bellman germs of
`PureExternalityCycle.game`, both of ramification `1`.  Their endpoint values
are the constant payoffs `(1, 1)` and `(0, 0)`.  Their canonical first
hierarchy responses are finite-bias seeds with selected relative bias `0` and
`r / 2 ≠ 0` respectively.  At every public entry state both endpoint atlas
leaves are the semantic leaf `semanticClose`, and both are resolved at every
accuracy with no reconstruction supplied. -/
theorem germ_endpointLeaf_isSemanticClose (entry : Bool) :
    (oneGerm.ramification = 1 ∧ prescribedGerm.ramification = 1) ∧
      oneGerm.endpointValue = (fun _ _ => (1 : ℝ)) ∧
      prescribedGerm.endpointValue = (fun _ _ => (0 : ℝ)) ∧
      oneFiniteBiasSeed.H = 0 ∧
      prescribedFiniteBiasSeed.H ≠ 0 ∧
      oneEndpointLeaf entry =
        AnalyticBellmanGerm.AnalyticEndpointAtlasLeaf.semanticClose
          (oneGerm_isUniformEquilibriumPayoff entry) ∧
      prescribedEndpointLeaf entry =
        AnalyticBellmanGerm.AnalyticEndpointAtlasLeaf.semanticClose
          (prescribedGerm_isUniformEquilibriumPayoff entry) ∧
      (∀ error : ℝ,
        Nonempty ((oneEndpointLeaf entry).RequiredReconstructionAt error) ∧
          Nonempty
            ((prescribedEndpointLeaf entry).RequiredReconstructionAt error)) :=
  ⟨⟨oneGerm_ramification, prescribedGerm_ramification⟩,
    oneGerm_endpointValue, prescribedGerm_endpointValue,
    oneFiniteBiasSeed_H, prescribedFiniteBiasSeed_H_ne_zero, rfl, rfl,
    fun error =>
      ⟨⟨oneEndpointResolution entry error⟩,
        ⟨prescribedEndpointResolution entry error⟩⟩⟩

/-- The existential form of the slice: the pure-externality cycle has analytic
Bellman germs at both of its certified uniform equilibrium payoffs, each with
an inhabited endpoint atlas leaf at every entry state. -/
theorem exists_analyticBellmanGerm_endpointLeaf (entry : Bool) (v : ℝ)
    (hv : v = 0 ∨ v = 1) :
    ∃ g : game.AnalyticBellmanGerm,
      g.endpointValue = (fun _ _ => v) ∧
        Nonempty
          (g.AnalyticEndpointAtlasLeaf
            (AnalyticBellmanGerm.EndpointHarmonicJetSpan.empty g) entry) := by
  rcases hv with hv | hv
  · subst hv
    exact ⟨prescribedGerm, prescribedGerm_endpointValue,
      ⟨prescribedEndpointLeaf entry⟩⟩
  · subst hv
    exact ⟨oneGerm, oneGerm_endpointValue, ⟨oneEndpointLeaf entry⟩⟩

end PureExternalityCycle

end StochasticGame

end GameTheory
