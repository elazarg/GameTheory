/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# PMF Utilities

Canonical home for generic PMF utilities: pushforward, bind congruence, support
extensionality, conditioning (`condOn`), and sequential fold/bind composition.
Does not cover product structure (see `PMFProduct.lean`).
-/

set_option autoImplicit false

namespace Math
namespace ProbabilityMassFunction

variable {α β γ : Type*}

noncomputable def pushforward (μ : PMF α) (f : α → β) : PMF β :=
  μ.map f

theorem pushforward_comp
    (μ : PMF α) (f : α → β) (g : β → γ) :
    pushforward (pushforward μ f) g = pushforward μ (g ∘ f) := by
  exact PMF.map_comp (p := μ) (f := f) g

theorem pushforward_pushforward
    (μ : PMF α) (f : α → β) (g : β → γ) :
    pushforward (pushforward μ f) g = pushforward μ (g ∘ f) :=
  pushforward_comp μ f g

theorem pushforward_id (μ : PMF α) :
    pushforward μ id = μ := by
  exact PMF.map_id μ

theorem pushforward_pure (a : α) (f : α → β) :
    pushforward (PMF.pure a) f = PMF.pure (f a) := by
  exact PMF.pure_map f a

theorem bind_pure_eq_pushforward
    (μ : PMF α) (f : α → β) :
    μ.bind (fun a => PMF.pure (f a)) = pushforward μ f := by
  exact PMF.bind_pure_comp f μ

theorem bind_assoc
    (μ : PMF α) (f : α → PMF β) (g : β → PMF γ) :
    (μ.bind f).bind g = μ.bind (fun a => (f a).bind g) := by
  exact PMF.bind_bind (p := μ) (f := f) (g := g)

theorem pushforward_bind
    (μ : PMF α) (k : α → PMF β) (f : β → γ) :
    pushforward (μ.bind k) f = μ.bind (fun a => pushforward (k a) f) := by
  exact PMF.map_bind (p := μ) (q := k) f

theorem sum_coe_fintype [Fintype α] (μ : PMF α) :
    ∑ a : α, μ a = 1 := by
  have h := PMF.tsum_coe μ
  rwa [tsum_eq_sum (s := Finset.univ)
    (fun x hx => absurd (Finset.mem_univ x) hx)] at h

theorem sum_mul_pmf_le_one {α : Type*} [Fintype α]
    (d : PMF α) (w : α → ENNReal) (hw : ∀ a, w a ≤ 1) :
    ∑ a, d a * w a ≤ 1 := by
  calc
    ∑ a, d a * w a ≤ ∑ a, d a := by
      refine Finset.sum_le_sum ?_
      intro a _
      exact mul_le_of_le_one_right zero_le (hw a)
    _ = 1 := sum_coe_fintype d

theorem sum_mul_pmf_ne_top {α : Type*} [Fintype α]
    (d : PMF α) (w : α → ENNReal) (hw : ∀ a, w a ≤ 1) :
    ∑ a, d a * w a ≠ ⊤ :=
  ne_of_lt ((sum_mul_pmf_le_one d w hw).trans_lt ENNReal.one_lt_top)

theorem sum_mul_pmf_eq_zero_iff_of_weight_ne_zero_iff
    {α : Type*} [Fintype α] (d : PMF α) {w₁ w₂ : α → ENNReal}
    (hiff : ∀ a, w₁ a ≠ 0 ↔ w₂ a ≠ 0) :
    (∑ a, d a * w₁ a = 0) ↔ (∑ a, d a * w₂ a = 0) := by
  simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies, mul_eq_zero]
  constructor
  · intro h a
    rcases h a with hda | hw
    · exact Or.inl hda
    · exact Or.inr (of_not_not (mt (hiff a).mpr (not_not.mpr hw)))
  · intro h a
    rcases h a with hda | hw
    · exact Or.inl hda
    · exact Or.inr (of_not_not (mt (hiff a).mp (not_not.mpr hw)))

theorem sum_mul_pmf_ne_zero_of_ne_zero
    {α : Type*} [Fintype α] (d : PMF α) (w : α → ENNReal) {a : α}
    (hd : d a ≠ 0) (hw : w a ≠ 0) :
    ∑ x, d x * w x ≠ 0 := by
  apply ne_of_gt
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero hd hw))
    (Finset.single_le_sum (f := fun x => d x * w x)
      (fun _ _ => zero_le) (Finset.mem_univ a))

/-- Binary independent product of two PMFs. -/
noncomputable def prod (μ : PMF α) (ν : PMF β) : PMF (α × β) :=
  μ.bind (fun a => ν.map (fun b => (a, b)))

theorem prod_map_fst (μ : PMF α) (ν : PMF β) :
    (prod μ ν).map Prod.fst = μ := by
  unfold prod
  rw [PMF.map_bind]
  conv_lhs =>
    enter [2, a]
    rw [PMF.map_comp]
    rw [show (Prod.fst ∘ fun b : β => (a, b)) = Function.const β a from rfl]
    rw [PMF.map_const]
  rw [PMF.bind_pure]

theorem prod_map_snd (μ : PMF α) (ν : PMF β) :
    (prod μ ν).map Prod.snd = ν := by
  unfold prod
  rw [PMF.map_bind]
  conv_lhs =>
    enter [2, a]
    rw [PMF.map_comp]
    rw [show (Prod.snd ∘ fun b : β => (a, b)) = (id : β → β) from rfl]
    rw [PMF.map_id]
  exact PMF.bind_const _ _

section ReweightPMF

variable [Fintype α]

open Classical in
/-- Reweight a finitely-supported PMF by an `ENNReal` weight function.
Falls back to `μ` when the total weight is zero or infinite. -/
noncomputable def reweightPMF (μ : PMF α) (w : α → ENNReal) : PMF α :=
  let C := ∑ a : α, μ a * w a
  if h : C = 0 ∨ C = ⊤ then μ
  else
    have hne0 : C ≠ 0 := fun h0 => h (Or.inl h0)
    have hneTop : C ≠ ⊤ := fun ht => h (Or.inr ht)
    PMF.ofFintype (fun a => μ a * w a / C) (by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      exact ENNReal.mul_inv_cancel hne0 hneTop)

open Classical in
theorem reweightPMF_apply (μ : PMF α) (w : α → ENNReal) (a : α)
    (hC : ∑ a' : α, μ a' * w a' ≠ 0)
    (hCtop : ∑ a' : α, μ a' * w a' ≠ ⊤) :
    reweightPMF μ w a = μ a * w a / (∑ a' : α, μ a' * w a') := by
  unfold reweightPMF
  dsimp only
  split_ifs with h
  · exact absurd h (not_or.mpr ⟨hC, hCtop⟩)
  · exact PMF.ofFintype_apply _ a

open Classical in
theorem reweightPMF_support_subset (μ : PMF α) (w : α → ENNReal) :
    (reweightPMF μ w).support ⊆ μ.support := by
  intro a ha
  rw [PMF.mem_support_iff] at ha ⊢
  intro hμ
  unfold reweightPMF at ha
  dsimp only at ha
  split_ifs at ha with hdeg
  · exact ha hμ
  · apply ha
    rw [PMF.ofFintype_apply, hμ]
    simp

theorem reweightPMF_fallback (μ : PMF α) (w : α → ENNReal)
    (hC : ∑ a : α, μ a * w a = 0) :
    reweightPMF μ w = μ := by
  unfold reweightPMF
  dsimp only
  split_ifs with h
  · rfl
  · exact absurd (Or.inl hC) h

theorem reweightPMF_degenerate (μ : PMF α) (w : α → ENNReal)
    (hC : (∑ a : α, μ a * w a) = 0 ∨ (∑ a : α, μ a * w a) = ⊤) :
    reweightPMF μ w = μ := by
  unfold reweightPMF
  exact dif_pos hC

open Classical in
/-- Scaling the weight function by a finite nonzero constant doesn't change
the reweighted PMF because the constant cancels in the normalization. -/
theorem reweightPMF_scale (μ : PMF α) (w : α → ENNReal) (c : ENNReal)
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    reweightPMF μ (fun a => c * w a) = reweightPMF μ w := by
  have hfact : ∀ a', μ a' * (c * w a') = c * (μ a' * w a') := fun a' => by ring
  have hCeq : ∑ a' : α, μ a' * (c * w a') = c * ∑ a' : α, μ a' * w a' := by
    simp_rw [hfact, ← Finset.mul_sum]
  by_cases hC0 : ∑ a' : α, μ a' * w a' = 0
  · exact (reweightPMF_degenerate μ _ (Or.inl (by rw [hCeq, hC0, mul_zero]))).trans
      (reweightPMF_degenerate μ _ (Or.inl hC0)).symm
  by_cases hCtop : ∑ a' : α, μ a' * w a' = ⊤
  · exact (reweightPMF_degenerate μ _ (Or.inr (by rw [hCeq, hCtop, ENNReal.mul_top hc0]))).trans
      (reweightPMF_degenerate μ _ (Or.inr hCtop)).symm
  · have hC0' : ∑ a' : α, μ a' * (c * w a') ≠ 0 := by
      rw [hCeq]; exact mul_ne_zero hc0 hC0
    have hCtop' : ∑ a' : α, μ a' * (c * w a') ≠ ⊤ := by
      rw [hCeq]; exact ENNReal.mul_ne_top hctop.lt_top.ne hCtop
    ext a
    rw [reweightPMF_apply μ _ a hC0' hCtop', reweightPMF_apply μ _ a hC0 hCtop]
    rw [show μ a * (c * w a) = c * (μ a * w a) from by ring, hCeq]
    exact ENNReal.mul_div_mul_left _ _ hc0 hctop

open Classical in
/-- If weights satisfy a cross-multiplication identity
`∀ a, w₁ a * C₂ = w₂ a * C₁`, the reweighted PMFs are equal. -/
theorem reweightPMF_eq_of_cross_mul (μ : PMF α) (w₁ w₂ : α → ENNReal)
    (hC₁ : ∑ a' : α, μ a' * w₁ a' ≠ 0)
    (hC₁top : ∑ a' : α, μ a' * w₁ a' ≠ ⊤)
    (hC₂ : ∑ a' : α, μ a' * w₂ a' ≠ 0)
    (hC₂top : ∑ a' : α, μ a' * w₂ a' ≠ ⊤)
    (hcross : ∀ a, w₁ a * (∑ a' : α, μ a' * w₂ a') =
                    w₂ a * (∑ a' : α, μ a' * w₁ a')) :
    reweightPMF μ w₁ = reweightPMF μ w₂ := by
  ext a
  rw [reweightPMF_apply μ w₁ a hC₁ hC₁top, reweightPMF_apply μ w₂ a hC₂ hC₂top]
  rw [ENNReal.div_eq_div_iff hC₂ hC₂top hC₁ hC₁top]
  calc (∑ a', μ a' * w₂ a') * (μ a * w₁ a)
      = μ a * (w₁ a * (∑ a', μ a' * w₂ a')) := by ac_rfl
    _ = μ a * (w₂ a * (∑ a', μ a' * w₁ a')) := by rw [hcross a]
    _ = (∑ a', μ a' * w₁ a') * (μ a * w₂ a) := by ac_rfl

end ReweightPMF

open Classical in
/-- Mask a PMF by an event, as an `ENNReal`-valued function. -/
noncomputable def pmfMask (μ : PMF α) (E : α → Prop) : α → ENNReal :=
  fun a => if E a then μ a else 0

/-- Total mass assigned by a PMF to an event. This is `tsum`-based and does not
require the underlying type to be finite. -/
noncomputable def pmfMass (μ : PMF α) (E : α → Prop) : ENNReal :=
  ∑' a : α, pmfMask (μ := μ) E a

theorem pmfMass_ne_top (μ : PMF α) (E : α → Prop) :
    pmfMass (μ := μ) E ≠ ⊤ := by
  classical
  simpa [pmfMass, pmfMask, Set.indicator, Set.mem_setOf_eq] using
    μ.tsum_coe_indicator_ne_top {a | E a}

theorem pmfMass_eq_toOuterMeasure (μ : PMF α) (E : α → Prop) :
    pmfMass (μ := μ) E = μ.toOuterMeasure {a | E a} := by
  classical
  rw [PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro a
  simp [pmfMask, Set.indicator]

/-- Pushforward mass of an event is the mass of its preimage. -/
theorem pmfMass_pushforward
    (μ : PMF α) (f : α → β) (E : β → Prop) :
    pmfMass (μ := pushforward μ f) E = pmfMass (μ := μ) (fun a => E (f a)) := by
  rw [pmfMass_eq_toOuterMeasure, pmfMass_eq_toOuterMeasure]
  exact PMF.toOuterMeasure_map_apply f μ {b | E b}

/-- Pushforward probability at a value equals the mass of its fiber. -/
theorem pushforward_apply_eq_pmfMass
    (μ : PMF α) (f : α → β) (b : β) :
    pushforward μ f b = pmfMass (μ := μ) (fun a => f a = b) := by
  calc
    pushforward μ f b = (pushforward μ f).toOuterMeasure {b} :=
      (PMF.toOuterMeasure_apply_singleton (pushforward μ f) b).symm
    _ = pmfMass (μ := pushforward μ f) (fun x => x = b) :=
      (pmfMass_eq_toOuterMeasure (pushforward μ f) (fun x => x = b)).symm
    _ = pmfMass (μ := μ) (fun a => f a = b) := by
      simpa using pmfMass_pushforward μ f (fun x => x = b)

open Classical in
/-- Condition a PMF on an event with nonzero mass. -/
noncomputable def pmfCond (μ : PMF α) (E : α → Prop)
    (h : pmfMass (μ := μ) E ≠ 0) : PMF α :=
  PMF.normalize (pmfMask (μ := μ) E) h (pmfMass_ne_top μ E)

@[simp] theorem pmfCond_apply (μ : PMF α) (E : α → Prop)
    (h : pmfMass (μ := μ) E ≠ 0) (a : α) :
    pmfCond (μ := μ) E h a = pmfMask (μ := μ) E a / pmfMass (μ := μ) E := by
  simp [pmfCond, pmfMass, div_eq_mul_inv]

theorem pmfCond_ne_zero_implies
    (μ : PMF α) (E : α → Prop)
    (h : pmfMass (μ := μ) E ≠ 0) {a : α}
    (ha : pmfCond (μ := μ) E h a ≠ 0) :
    E a := by
  classical
  by_contra hEa
  have : pmfCond (μ := μ) E h a = 0 := by
    simp [pmfMask, hEa]
  exact ha this

theorem pmfCond_ne_zero_iff
    (μ : PMF α) (E : α → Prop)
    (h : pmfMass (μ := μ) E ≠ 0) {a : α} :
    pmfCond (μ := μ) E h a ≠ 0 ↔ E a ∧ μ a ≠ 0 := by
  classical
  constructor
  · intro ha
    refine ⟨pmfCond_ne_zero_implies μ E h ha, ?_⟩
    by_contra hμ
    exact ha (by simp [pmfMask, hμ])
  · rintro ⟨hEa, hμ⟩
    rw [pmfCond_apply]
    simp [pmfMask, hEa, hμ, pmfMass_ne_top μ E]

open Classical in
theorem pmfMass_true (μ : PMF α) :
    pmfMass (μ := μ) (fun _ : α => True) = 1 := by
  simp [pmfMass, pmfMask, PMF.tsum_coe]

open Classical in
theorem pmfMass_mono (μ : PMF α) {E F : α → Prop}
    (hEF : ∀ a, E a → F a) :
    pmfMass (μ := μ) E ≤ pmfMass (μ := μ) F := by
  simp only [pmfMass, pmfMask]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases hE : E a
  · simp [hE, hEF a hE]
  · by_cases hF : F a <;> simp [hE, hF]

open Classical in
theorem pmfMass_and_eq_zero_of_left_zero
    (μ : PMF α) (E F : α → Prop)
    (hE : pmfMass (μ := μ) E = 0) :
    pmfMass (μ := μ) (fun a => E a ∧ F a) = 0 := by
  have hle : pmfMass (μ := μ) (fun a => E a ∧ F a) ≤ pmfMass (μ := μ) E :=
    pmfMass_mono μ (fun _ h => h.1)
  exact le_antisymm (by simpa [hE] using hle) bot_le

open Classical in
theorem pmfMass_and_eq_mul_cond
    (μ : PMF α) (E F : α → Prop)
    (hE : pmfMass (μ := μ) E ≠ 0) :
    pmfMass (μ := μ) (fun a => E a ∧ F a) =
      pmfMass (μ := μ) E * pmfMass (μ := pmfCond (μ := μ) E hE) F := by
  have hE_top : pmfMass (μ := μ) E ≠ ⊤ := pmfMass_ne_top μ E
  symm
  simp only [pmfMass, pmfMask, pmfCond_apply]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro a
  by_cases hEa : E a
  · by_cases hFa : F a
    · simp only [hEa, hFa, true_and, ↓reduceIte, div_eq_mul_inv]
      calc
        (∑' a : α, if E a then μ a else 0) *
            (μ a * (∑' a : α, if E a then μ a else 0)⁻¹)
            = μ a * ((∑' a : α, if E a then μ a else 0) *
                (∑' a : α, if E a then μ a else 0)⁻¹) := by
              ac_rfl
        _ = μ a := by
              have hcancel :
                  (∑' a : α, if E a then μ a else 0) *
                      (∑' a : α, if E a then μ a else 0)⁻¹ = 1 := by
                simpa [pmfMass, pmfMask] using ENNReal.mul_inv_cancel hE hE_top
              rw [hcancel, mul_one]
    · simp [hEa, hFa]
  · simp [hEa]

/-- Conjunction of a finite list of events. -/
def allEvents (events : List (α → Prop)) (a : α) : Prop :=
  ∀ E ∈ events, E a

@[simp] theorem allEvents_nil :
    allEvents ([] : List (α → Prop)) = fun _ : α => True := by
  funext a
  simp [allEvents]

@[simp] theorem allEvents_cons (E : α → Prop) (events : List (α → Prop)) :
    allEvents (E :: events) = fun a => E a ∧ allEvents events a := by
  funext a
  apply propext
  simp [allEvents]

theorem allEvents_append_singleton (events : List (α → Prop)) (E : α → Prop) :
    allEvents (events ++ [E]) = fun a => allEvents events a ∧ E a := by
  funext a
  apply propext
  constructor
  · intro h
    constructor
    · intro F hF
      exact h F (by simp [hF])
    · exact h E (by simp)
  · intro h F hF
    rw [List.mem_append, List.mem_singleton] at hF
    rcases hF with hF | rfl
    · exact h.1 F hF
    · exact h.2

open Classical in
/-- Conditional factor for extending a past event by one more event. If the
    past has zero mass, the supplied fallback value is used; chain products
    remain correct because the accumulated past mass is already zero. -/
noncomputable def condEventFactor (μ : PMF α) (past event : α → Prop)
    (fallback : ENNReal) : ENNReal :=
  if h : pmfMass (μ := μ) past ≠ 0 then
    pmfMass (μ := pmfCond (μ := μ) past h) event
  else
    fallback

open Classical in
/-- Product of conditional factors for a list of events, starting from a
    supplied past event. -/
noncomputable def condEventChainProduct (μ : PMF α)
    (past : α → Prop) : List (α → Prop) → (List (α → Prop) → (α → Prop) → ENNReal) → ENNReal
  | [], _ => 1
  | E :: Es, fallback =>
      condEventFactor μ past E (fallback [] E) *
        condEventChainProduct μ (fun a => past a ∧ E a) Es
          (fun pref F => fallback (E :: pref) F)

open Classical in
theorem pmfMass_event_chain_aux (μ : PMF α)
    (past : α → Prop) (events : List (α → Prop))
    (fallback : List (α → Prop) → (α → Prop) → ENNReal) :
    pmfMass (μ := μ) (fun a => past a ∧ allEvents events a) =
      pmfMass (μ := μ) past *
        condEventChainProduct μ past events fallback := by
  induction events generalizing past fallback with
  | nil =>
      simp [condEventChainProduct, allEvents]
  | cons E Es ih =>
      by_cases hpast : pmfMass (μ := μ) past = 0
      · have hleft :
            pmfMass (μ := μ) (fun a => past a ∧ allEvents (E :: Es) a) = 0 :=
          pmfMass_and_eq_zero_of_left_zero μ past (fun a => allEvents (E :: Es) a) hpast
        have hleft' :
            pmfMass (μ := μ) (fun a => past a ∧ E a ∧ allEvents Es a) = 0 := by
          calc
            pmfMass (μ := μ) (fun a => past a ∧ E a ∧ allEvents Es a)
                = pmfMass (μ := μ) (fun a => past a ∧ allEvents (E :: Es) a) := by
                    apply congrArg
                    funext a
                    simp [allEvents]
            _ = 0 := hleft
        simp [condEventChainProduct, condEventFactor, hpast, hleft']
      · have hpast_ne : pmfMass (μ := μ) past ≠ 0 := hpast
        have hstep :
            pmfMass (μ := μ) (fun a => past a ∧ E a) =
              pmfMass (μ := μ) past *
                pmfMass (μ := pmfCond (μ := μ) past hpast_ne) E :=
          pmfMass_and_eq_mul_cond μ past E hpast_ne
        have htail := ih (fun a => past a ∧ E a)
          (fun pref F => fallback (E :: pref) F)
        calc
          pmfMass (μ := μ) (fun a => past a ∧ allEvents (E :: Es) a)
              = pmfMass (μ := μ)
                  (fun a => (past a ∧ E a) ∧ allEvents Es a) := by
                    apply congrArg
                    funext a
                    simp [allEvents, and_assoc]
          _ = pmfMass (μ := μ) (fun a => past a ∧ E a) *
                condEventChainProduct μ (fun a => past a ∧ E a) Es
                  (fun pref F => fallback (E :: pref) F) := htail
          _ = pmfMass (μ := μ) past *
                condEventChainProduct μ past (E :: Es) fallback := by
                  simp [condEventChainProduct, condEventFactor, hpast_ne, hstep,
                    mul_assoc]

open Classical in
/-- Finite chain rule for event masses. -/
theorem pmfMass_event_chain (μ : PMF α) (events : List (α → Prop))
    (fallback : List (α → Prop) → (α → Prop) → ENNReal) :
    pmfMass (μ := μ) (allEvents events) =
      condEventChainProduct μ (fun _ : α => True) events fallback := by
  have h := pmfMass_event_chain_aux μ (fun _ : α => True) events fallback
  simpa [pmfMass_true] using h

theorem bind_congr_on_support
    (μ : PMF α) (f g : α → PMF β)
    (hfg : ∀ a, a ∈ μ.support → f a = g a) :
    μ.bind f = μ.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr (fun a => ?_)
  by_cases ha0 : μ a = 0
  · simp [ha0]
  · have haS : a ∈ μ.support := by
      simpa [PMF.mem_support_iff] using ha0
    rw [hfg a haS]

theorem bind_congr_of_ne_zero
    (μ : PMF α) (f g : α → PMF β)
    (hfg : ∀ a, μ a ≠ 0 → f a = g a) :
    μ.bind f = μ.bind g := by
  exact bind_congr_on_support μ f g (fun a ha => hfg a (by simpa [PMF.mem_support_iff] using ha))

theorem pmf_eq_of_subsingleton
    {α : Type*} [Subsingleton α] (p q : PMF α) : p = q := by
  classical
  rcases p.support_nonempty with ⟨a, ha⟩
  have hp_support : p.support = ({a} : Set α) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      simpa using (Subsingleton.elim x a)
    · intro x hx
      have hx' : x = a := by simpa using hx
      exact hx' ▸ ha
  have hq_support : q.support = ({a} : Set α) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      simpa using (Subsingleton.elim x a)
    · intro x hx
      have hx' : x = a := by simpa using hx
      rcases q.support_nonempty with ⟨b, hb⟩
      have hba : b = a := Subsingleton.elim b a
      exact hx' ▸ (hba.symm ▸ hb)
  have hp : p a = 1 := (p.apply_eq_one_iff a).2 hp_support
  have hq : q a = 1 := (q.apply_eq_one_iff a).2 hq_support
  refine PMF.ext ?_
  intro x
  have hx : x = a := Subsingleton.elim x a
  subst hx
  exact hp.trans hq.symm

theorem expect_congr_on_support
    {Ω : Type*} (μ : PMF Ω) (f g : Ω → ℝ)
    (hfg : ∀ a, a ∈ μ.support → f a = g a) :
    Math.Probability.expect μ f = Math.Probability.expect μ g := by
  unfold Math.Probability.expect
  refine tsum_congr (fun a => ?_)
  by_cases ha0 : μ a = 0
  · simp [ha0]
  · have haS : a ∈ μ.support := by
      simpa [PMF.mem_support_iff] using ha0
    rw [hfg a haS]

theorem expect_congr_of_ne_zero
    {Ω : Type*} (μ : PMF Ω) (f g : Ω → ℝ)
    (hfg : ∀ a, μ a ≠ 0 → f a = g a) :
    Math.Probability.expect μ f = Math.Probability.expect μ g := by
  exact expect_congr_on_support μ f g (fun a ha => hfg a (by simpa [PMF.mem_support_iff] using ha))

theorem expect_pushforward
    {Ω Ξ : Type*} [Finite Ξ]
    (μ : PMF Ω) (f : Ω → Ξ) (φ : Ξ → ℝ) :
    Math.Probability.expect (pushforward μ f) φ =
      Math.Probability.expect μ (fun a => φ (f a)) := by
  classical
  letI : Fintype Ξ := Fintype.ofFinite Ξ
  exact Math.Probability.expect_map_fintype_target μ f φ

/-- `expect` along a pushforward, under a bounded-`φ` hypothesis (countable source/target). -/
theorem expect_pushforward_of_bounded
    {Ω Ξ : Type*}
    (μ : PMF Ω) (f : Ω → Ξ) (φ : Ξ → ℝ) {C : ℝ} (hbd : ∀ x, |φ x| ≤ C) :
    Math.Probability.expect (pushforward μ f) φ =
      Math.Probability.expect μ (fun a => φ (f a)) := by
  have h_eq : pushforward μ f = μ.bind (fun a => PMF.pure (f a)) :=
    (PMF.bind_pure_comp f μ).symm
  rw [h_eq, Math.Probability.expect_bind_of_bounded
    (p := μ) (q := fun a => PMF.pure (f a)) (f := φ) hbd]
  apply tsum_congr; intro a
  congr 1
  simp [Math.Probability.expect_pure]

/-- `expect` along a pushforward when the observable is bounded on the source
image of the pushed distribution. This is weaker than bounding `φ` on all of
the target type. -/
theorem expect_pushforward_of_bounded_on_source
    {Ω Ξ : Type*}
    (μ : PMF Ω) (f : Ω → Ξ) (φ : Ξ → ℝ) {C : ℝ}
    (hbd : ∀ ω, |φ (f ω)| ≤ C) :
    Math.Probability.expect (pushforward μ f) φ =
      Math.Probability.expect μ (fun ω => φ (f ω)) := by
  classical
  let ψ : Ξ → ℝ := fun x =>
    if ∃ ω, μ ω ≠ 0 ∧ f ω = x then φ x else 0
  obtain ⟨ω₀, _hω₀⟩ := μ.support_nonempty
  have hC_nonneg : 0 ≤ C := le_trans (abs_nonneg (φ (f ω₀))) (hbd ω₀)
  have hψ_bounded : ∀ x, |ψ x| ≤ C := by
    intro x
    by_cases hx : ∃ ω, μ ω ≠ 0 ∧ f ω = x
    · rcases hx with ⟨ω, _hω, rfl⟩
      have hx_self : ∃ ω', μ ω' ≠ 0 ∧ f ω' = f ω := ⟨ω, _hω, rfl⟩
      simpa [ψ, hx_self] using hbd ω
    · simp [ψ, hx, hC_nonneg]
  have hleft :
      Math.Probability.expect (pushforward μ f) φ =
        Math.Probability.expect (pushforward μ f) ψ := by
    refine expect_congr_on_support (pushforward μ f) φ ψ ?_
    intro x hx
    have hx' : ∃ ω, μ ω ≠ 0 ∧ f ω = x := by
      rcases (PMF.mem_support_map_iff (f := f) (p := μ) (b := x)).1
          (by simpa [pushforward] using hx) with ⟨ω, hω, hfx⟩
      exact ⟨ω, by simpa [PMF.mem_support_iff] using hω, hfx⟩
    simp [ψ, hx']
  have hright :
      Math.Probability.expect μ (fun ω => ψ (f ω)) =
        Math.Probability.expect μ (fun ω => φ (f ω)) := by
    refine expect_congr_on_support μ (fun ω => ψ (f ω)) (fun ω => φ (f ω)) ?_
    intro ω hω
    have hx : ∃ ω', μ ω' ≠ 0 ∧ f ω' = f ω :=
      ⟨ω, by simpa [PMF.mem_support_iff] using hω, rfl⟩
    simp [ψ, hx]
  calc
    Math.Probability.expect (pushforward μ f) φ
        = Math.Probability.expect (pushforward μ f) ψ := hleft
    _ = Math.Probability.expect μ (fun ω => ψ (f ω)) := by
          exact expect_pushforward_of_bounded μ f ψ hψ_bounded
    _ = Math.Probability.expect μ (fun ω => φ (f ω)) := hright

theorem expect_bind_congr_on_support
    {Ω Ξ : Type*}
    (μ : PMF Ω) (k₁ k₂ : Ω → PMF Ξ) (φ : Ξ → ℝ)
    (hk : ∀ a, a ∈ μ.support → k₁ a = k₂ a) :
    Math.Probability.expect (μ.bind k₁) φ =
      Math.Probability.expect (μ.bind k₂) φ := by
  rw [bind_congr_on_support (μ := μ) (f := k₁) (g := k₂) hk]

open Classical in
theorem bind_apply_eq_sum_sum_fiber
    {β γ : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (proj : α → β) (g : α → PMF γ) (x : γ) :
    (μ.bind g) x =
      ∑ b : β, ∑ a : α, (if proj a = b then μ a else 0) * g a x := by
  simp only [PMF.bind_apply, tsum_fintype]
  rw [show ∑ a, μ a * g a x =
      ∑ a, ∑ b : β, if proj a = b then μ a * g a x else 0 from by
    congr 1
    funext a
    exact Eq.symm (Fintype.sum_ite_eq (proj a) (fun _ => μ a * (g a) x))]
  rw [Finset.sum_comm]
  congr 1
  funext b
  congr 1
  funext a
  split_ifs <;> ring

theorem le_pushforward_apply
    {β : Type*} [Finite α]
    (μ : PMF α) (proj : α → β) (a : α) :
    μ a ≤ pushforward μ proj (proj a) := by
  letI : Fintype α := Fintype.ofFinite α
  classical
  have hle :
      (if proj a = proj a then (μ a : ENNReal) else 0) ≤
        ∑ t : α, if proj a = proj t then (μ t : ENNReal) else 0 := by
    exact Finset.single_le_sum
      (f := fun t : α => if proj a = proj t then (μ t : ENNReal) else 0)
      (fun _ _ => by positivity)
      (Finset.mem_univ a)
  simpa [pushforward, PMF.map_apply, tsum_fintype, eq_comm] using hle

theorem eq_zero_of_pushforward_eq_zero
    {β : Type*} [Finite α]
    (μ : PMF α) (proj : α → β) {b : β}
    (hb : pushforward μ proj b = 0)
    {a : α} (ha : proj a = b) :
    μ a = 0 := by
  have hle : μ a ≤ pushforward μ proj b := by
    simpa [ha] using le_pushforward_apply (μ := μ) (proj := proj) a
  rw [hb] at hle
  exact le_antisymm hle bot_le

/-- If `b` is in the support of `pushforward μ proj`, then the fibre
    `{a | proj a = b}` meets the support of `μ`. -/
theorem pushforward_support_fibre
    {β : Type*} (μ : PMF α) (proj : α → β) (b : β)
    (hb : b ∈ (pushforward μ proj).support) :
    ∃ a ∈ ({a | proj a = b} : Set α), a ∈ μ.support := by
  change b ∈ (PMF.map proj μ).support at hb
  rcases (PMF.mem_support_map_iff proj μ b).1 hb with ⟨a, ha, hab⟩
  exact ⟨a, hab, ha⟩

open Classical in
noncomputable def condOn
    {β : Type*}
    (μ : PMF α) (proj : α → β) (b : β) : PMF α :=
  if h : ∃ a ∈ ({a | b = proj a} : Set α), a ∈ μ.support then
    μ.filter {a | b = proj a} h
  else
    μ

open Classical in
theorem condOn_apply
    {β : Type*}
    (μ : PMF α) (proj : α → β) (b : β)
    (a : α) (hb : pushforward μ proj b ≠ 0) :
    condOn μ proj b a = if proj a = b then μ a / pushforward μ proj b else 0 := by
  have hb_support : b ∈ (pushforward μ proj).support := by
    simpa [PMF.mem_support_iff] using hb
  have hs : ∃ a ∈ ({a | b = proj a} : Set α), a ∈ μ.support := by
    rcases pushforward_support_fibre μ proj b hb_support with ⟨a, ha, hμa⟩
    exact ⟨a, ha.symm, hμa⟩
  change (if h : ∃ a ∈ ({a | b = proj a} : Set α), a ∈ μ.support then
      μ.filter {a | b = proj a} h else μ) a =
    if proj a = b then μ a / pushforward μ proj b else 0
  rw [dif_pos hs]
  simp [pushforward, PMF.map_apply, Set.indicator, div_eq_mul_inv, eq_comm]
  rfl

theorem bind_pushforward_condOn
    {β : Type*} [Finite α] [Finite β]
    (μ : PMF α) (proj : α → β) (g : α → PMF γ) :
    μ.bind g = (pushforward μ proj).bind (fun b => (condOn μ proj b).bind g) := by
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype β := Fintype.ofFinite β
  classical
  ext x
  have hL :=
    bind_apply_eq_sum_sum_fiber (μ := μ) (proj := proj) (g := g) (x := x)
  rw [hL]
  simp only [PMF.bind_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro b hb_mem
  by_cases hpb : pushforward μ proj b = 0
  · have hz : ∀ a : α, proj a = b → μ a = 0 := by
      intro a ha
      exact eq_zero_of_pushforward_eq_zero (μ := μ) (proj := proj) hpb ha
    have hinner_zero :
        ∑ a : α, (if proj a = b then μ a else 0) * g a x = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      by_cases hab : proj a = b
      · simp [hab, hz a hab]
      · simp [hab]
    have hrhs_zero :
        (pushforward μ proj b) *
            ∑ a : α, condOn μ proj b a * g a x = 0 := by
      simp [hpb]
    calc
      ∑ a : α, (if proj a = b then μ a else 0) * g a x = 0 := hinner_zero
      _ = (pushforward μ proj b) * ∑ a : α, condOn μ proj b a * g a x := by
        simp [hpb]
  · have hpb_top : pushforward μ proj b ≠ ⊤ :=
      PMF.apply_ne_top (pushforward μ proj) b
    have hterm :
        (pushforward μ proj b) *
            (∑ a : α, condOn μ proj b a * g a x)
          =
        ∑ a : α, (if proj a = b then μ a else 0) * g a x := by
      simp_rw [condOn_apply (μ := μ) (proj := proj) (b := b) (hb := hpb)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a ha
      by_cases hab : proj a = b
      · simp [hab, div_eq_mul_inv, mul_left_comm, mul_comm,
          ENNReal.mul_inv_cancel hpb hpb_top]
      · simp [hab, mul_comm]
    exact hterm.symm

/-- Self-disintegration: a finite PMF can be sampled by first sampling the law
of a projection, then sampling the original law conditioned on that projected
value. -/
theorem bind_pushforward_condOn_pure
    {β : Type*} [Finite α] [Finite β]
    (μ : PMF α) (proj : α → β) :
    μ = (pushforward μ proj).bind (fun b => condOn μ proj b) := by
  simpa [PMF.bind_pure] using
    bind_pushforward_condOn (μ := μ) (proj := proj)
      (g := fun a => PMF.pure a)

/-- Two-step self-disintegration.  A finite PMF can be sampled by first
sampling one finite projection, then sampling a second finite projection from
the conditioned remainder, then sampling the twice-conditioned remainder.

This is the basic serialisation law used when one simultaneous frontier action
is replayed by two source-order observations. -/
theorem bind_pushforward_condOn_pure_two
    {β γ : Type*} [Finite α] [Finite β] [Finite γ]
    (μ : PMF α) (first : α → β) (second : α → γ) :
    μ =
      (pushforward μ first).bind fun firstValue =>
        (pushforward (condOn μ first firstValue) second).bind
          fun secondValue =>
            condOn (condOn μ first firstValue) second secondValue := by
  calc
    μ = (pushforward μ first).bind fun firstValue =>
        condOn μ first firstValue :=
      bind_pushforward_condOn_pure (μ := μ) (proj := first)
    _ =
      (pushforward μ first).bind fun firstValue =>
        (pushforward (condOn μ first firstValue) second).bind
          fun secondValue =>
            condOn (condOn μ first firstValue) second secondValue := by
        ext a
        simp only [PMF.bind_apply]
        apply tsum_congr
        intro firstValue
        have h :=
          bind_pushforward_condOn_pure
            (μ := condOn μ first firstValue) (proj := second)
        exact
          congrArg
            (fun dist : PMF α => (pushforward μ first) firstValue * dist a)
            h

/-- Conditioning on a projected value restricts support to the corresponding
fiber whenever that projected value has positive mass. -/
theorem condOn_support_project
    {β : Type*}
    (μ : PMF α) (proj : α → β) (b : β)
    (hb : pushforward μ proj b ≠ 0)
    {a : α} (ha : a ∈ (condOn μ proj b).support) :
    proj a = b := by
  have hmass : condOn μ proj b a ≠ 0 := by
    simpa [PMF.mem_support_iff] using ha
  by_contra hne
  have hzero : condOn μ proj b a = 0 := by
    simp [condOn_apply (μ := μ) (proj := proj) (b := b) (a := a) hb,
      hne]
  exact hmass hzero

theorem foldl_bind_append
    {δ : Type*}
    (l₁ l₂ : List δ) (μ : PMF α) (k : δ → α → PMF α) :
    (l₁ ++ l₂).foldl (fun dist b => dist.bind (k b)) μ =
      l₂.foldl (fun dist b => dist.bind (k b))
        (l₁.foldl (fun dist b => dist.bind (k b)) μ) := by
  induction l₁ generalizing μ with
  | nil =>
      simp
  | cons b rest ih =>
      exact ih (μ.bind (k b))

theorem foldl_bind_congr
    {δ : Type*}
    (l : List δ) (μ : PMF α) (k₁ k₂ : δ → α → PMF α)
    (hk : ∀ b a, k₁ b a = k₂ b a) :
    l.foldl (fun dist b => dist.bind (k₁ b)) μ =
      l.foldl (fun dist b => dist.bind (k₂ b)) μ := by
  induction l generalizing μ with
  | nil =>
      simp
  | cons b rest ih =>
      have hbind : μ.bind (k₁ b) = μ.bind (k₂ b) := by
        exact bind_congr_on_support μ (k₁ b) (k₂ b) (fun a _ => hk b a)
      simpa [hbind] using ih (μ.bind (k₁ b))

theorem foldl_bind_eq_bind_foldl_pure
    {δ : Type*}
    (l : List δ) (μ : PMF α) (k : δ → α → PMF α) :
    l.foldl (fun dist b => dist.bind (k b)) μ =
      μ.bind (fun a => l.foldl (fun dist b => dist.bind (k b)) (PMF.pure a)) := by
  induction l generalizing μ with
  | nil =>
      simp [PMF.bind_pure]
  | cons b rest ih =>
      simp only [List.foldl]
      rw [ih, PMF.bind_bind]
      congr 1
      funext a
      simpa using (ih (k b a)).symm

theorem expect_mono_of_pointwise
    {Ω : Type*} [Finite Ω]
    (d : PMF Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω, f ω ≤ g ω) :
    Math.Probability.expect d f ≤ Math.Probability.expect d g := by
  letI : Fintype Ω := Fintype.ofFinite Ω
  simpa [Math.Probability.expect_eq_sum] using
    (Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) ENNReal.toReal_nonneg))

/-- Pointwise monotonicity of `expect` for countable types: integrand on either side
    must be summable (sufficient when `f`, `g` are bounded). -/
theorem expect_mono_of_pointwise_summable
    {Ω : Type*}
    (d : PMF Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω, f ω ≤ g ω)
    (hf : Summable (fun ω => (d ω).toReal * f ω))
    (hg : Summable (fun ω => (d ω).toReal * g ω)) :
    Math.Probability.expect d f ≤ Math.Probability.expect d g := by
  unfold Math.Probability.expect
  exact hf.tsum_le_tsum
    (fun ω => mul_le_mul_of_nonneg_left (hfg ω) ENNReal.toReal_nonneg) hg

/-- Pointwise monotonicity of `expect` for bounded `f`, `g`. -/
theorem expect_mono_of_pointwise_bounded
    {Ω : Type*}
    (d : PMF Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω, f ω ≤ g ω)
    {C : ℝ} (hf : ∀ ω, |f ω| ≤ C) (hg : ∀ ω, |g ω| ≤ C) :
    Math.Probability.expect d f ≤ Math.Probability.expect d g :=
  expect_mono_of_pointwise_summable d f g hfg
    (Math.Probability.expect_summable_of_bounded d f hf)
    (Math.Probability.expect_summable_of_bounded d g hg)

/-- If a non-positive summable payoff has zero expectation, then every point
    receiving positive probability has zero payoff. -/
theorem eq_zero_of_expect_eq_zero_of_nonpos_of_pos
    {Ω : Type*} (d : PMF Ω) (f : Ω → ℝ)
    (h_nonpos : ∀ ω, f ω ≤ 0)
    (h_expect : Math.Probability.expect d f = 0)
    (h_summable : Summable (fun ω => (d ω).toReal * f ω))
    {ω : Ω} (hpos : d ω ≠ 0) :
    f ω = 0 := by
  classical
  refine le_antisymm (h_nonpos ω) ?_
  by_contra hnot
  have hlt : f ω < 0 := lt_of_not_ge hnot
  have hdpos : 0 < (d ω).toReal := ENNReal.toReal_pos hpos (PMF.apply_ne_top d ω)
  have hterm_neg : (d ω).toReal * f ω < 0 := mul_neg_of_pos_of_neg hdpos hlt
  let g : Ω → ℝ := fun x => if x = ω then (d ω).toReal * f ω else 0
  have hg : Summable g := by
    exact summable_of_hasFiniteSupport ((Set.finite_singleton ω).subset (by
      intro x hx
      simp only [Function.mem_support, g] at hx
      simp only [Set.mem_singleton_iff]
      by_contra hne
      simp [hne] at hx))
  have hle : ∀ x, (d x).toReal * f x ≤ g x := by
    intro x
    by_cases hx : x = ω
    · subst hx
      simp [g]
    · have hmul : (d x).toReal * f x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg (h_nonpos x)
      simpa [g, hx] using hmul
  have htsum_le : Math.Probability.expect d f ≤ ∑' x, g x := by
    unfold Math.Probability.expect
    exact h_summable.tsum_le_tsum hle hg
  have hg_tsum : (∑' x, g x) = (d ω).toReal * f ω := by
    rw [tsum_eq_single ω]
    · simp [g]
    · intro x hx
      simp [g, hx]
  have hle_neg : (0 : ℝ) ≤ (d ω).toReal * f ω := by
    simpa [h_expect, hg_tsum] using htsum_le
  exact (not_le_of_gt hterm_neg) hle_neg

-- ============================================================================
-- HEq lemmas for PMF
-- ============================================================================

universe u in
theorem pure_heq {α β : Type u} {a : α} {b : β} (h : HEq a b) :
    HEq (PMF.pure a) (PMF.pure b) := by
  cases h; exact HEq.rfl

universe u in
theorem bind_heq {α : Type*} {β γ : Type u} (μ : PMF α)
    {f : α → PMF β} {g : α → PMF γ}
    (htype : β = γ) (h : ∀ a, HEq (f a) (g a)) :
    HEq (μ.bind f) (μ.bind g) := by
  subst htype
  exact heq_of_eq (congrArg (μ.bind ·) (funext fun a => eq_of_heq (h a)))

universe u in
theorem bind_heq_of_eq {α : Type*} {β γ : Type u} (htype : β = γ)
    (μ ν : PMF α) (hμ : μ = ν)
    (f : α → PMF β) (g : α → PMF γ)
    (h : ∀ a, HEq (f a) (g a)) :
    HEq (μ.bind f) (ν.bind g) := by
  subst hμ
  exact bind_heq μ htype h

end ProbabilityMassFunction
end Math
