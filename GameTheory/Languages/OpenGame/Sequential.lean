/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.OpenGame.Compile

/-!
# Finite-Horizon Sequential Open-Game Shapes

`ShapeSeq n A` is the direct perfect-information shape for `n` ordered
decisions with a common action type `A` and one decision owner per stage.
The strategy of stage `i` is a contingent plan `(Fin i → A) → A`, so it sees
exactly the preceding action history.  Playing a profile recursively realizes
the complete `Fin n → A` path.

The plain equilibrium predicate is the strategic-form Nash predicate on
contingent plans.  In particular, a deviation at an early stage is followed by
the fixed later plans reacting to the changed history.  The conditioned
variant additionally tests a one-stage deviation after every counterfactual
predecessor profile, giving the intrinsic finite-horizon one-shot condition.

`ShapeSeq` is the convenient homogeneous-action front end. `ShapeSeqDep`
supplies stage-specific action types: its dependent history at `i` contains
exactly the actions at indices strictly before `i`, and its realization uses
well-founded recursion on the stage index.
-/

namespace OpenGames

namespace ShapeSeq

/-- Histories available at stage `i`. -/
abbrev History (A : Type) (i : Nat) := Fin i → A

/-- A contingent plan at stage `i`. -/
abbrev StageStrategy (A : Type) (i : Nat) := History A i → A

/-- A profile containing one contingent plan for every stage. -/
abbrev Strategy (n : Nat) (A : Type) :=
  ∀ i : Fin n, StageStrategy A i.val

/-- Realize a complete path from an ordered profile of contingent plans. -/
def realize {A : Type} : (n : Nat) → Strategy n A → Fin n → A
  | 0, _ => Fin.elim0
  | n + 1, σ =>
      let prior := realize n (fun i => σ i.castSucc)
      Fin.snoc prior (σ (Fin.last n) prior)

end ShapeSeq

/-- The direct finite-horizon sequential shape. -/
def ShapeSeq (n : Nat) (A : Type) :
    OpenGame Unit Unit (Fin n → A) (Fin n → ℝ) where
  Strategy := ShapeSeq.Strategy n A
  play := fun σ _ => ShapeSeq.realize n σ
  coplay := fun _ _ _ => ()
  IsEquilibriumIn := fun _ k σ =>
    ∀ i (deviation : ShapeSeq.StageStrategy A i.val),
      k (ShapeSeq.realize n (Function.update σ i deviation)) i ≤
        k (ShapeSeq.realize n σ) i

namespace ShapeSeq

@[simp] theorem realize_succ_castSucc {A : Type} {n : Nat}
    (σ : Strategy (n + 1) A) (i : Fin n) :
    realize (n + 1) σ i.castSucc =
      realize n (fun j => σ j.castSucc) i := by
  simp [realize]

@[simp] theorem realize_succ_last {A : Type} {n : Nat}
    (σ : Strategy (n + 1) A) :
    realize (n + 1) σ (Fin.last n) =
      σ (Fin.last n) (realize n fun j => σ j.castSucc) := by
  simp [realize]

/-- The strategic-form game induced by an n-stage closing continuation. -/
def actionNFG (n : Nat) (A : Type) (k : (Fin n → A) → Fin n → ℝ) :
    NFG.NFGGame (Fin n) (fun i => StageStrategy A i.val) where
  Outcome := Fin n → A
  outcome := realize n
  utility := k

/-- Compile the n-stage strategic form through the existing NFG bridge. -/
noncomputable def compileAction (n : Nat) (A : Type)
    (k : (Fin n → A) → Fin n → ℝ) : GameTheory.KernelGame (Fin n) :=
  (actionNFG n A k).toKernelGame

/-- Plain n-stage equilibrium is exactly pure Nash equilibrium of the induced
strategic form. -/
theorem isEquilibriumIn_iff_isNashPure {n : Nat} {A : Type}
    (k : (Fin n → A) → Fin n → ℝ) (σ : Strategy n A) :
    (ShapeSeq n A).IsEquilibriumIn () k σ ↔
      NFG.IsNashPure (actionNFG n A k) σ := by
  rfl

/-- Kernel-level correctness of n-stage compilation. -/
theorem isEquilibriumIn_iff_isNash {n : Nat} {A : Type}
    (k : (Fin n → A) → Fin n → ℝ) (σ : Strategy n A) :
    (ShapeSeq n A).IsEquilibriumIn () k σ ↔
      (compileAction n A k).IsNash σ := by
  rw [isEquilibriumIn_iff_isNashPure]
  exact NFG.IsNashPure_iff_kernelGame (actionNFG n A k) σ

/-! ## Compatibility with the direct two-stage shape -/

/-- A two-coordinate finite function as a binary product. -/
def finTwoEquiv (A : Type) : (Fin 2 → A) ≃ A × A where
  toFun f := (f 0, f 1)
  invFun p := Fin.cases p.1 fun _ => p.2
  left_inv f := by
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl

@[simp] theorem finTwoEquiv_apply_fst (f : Fin 2 → A) :
    (finTwoEquiv A f).1 = f 0 := rfl

@[simp] theorem finTwoEquiv_apply_snd (f : Fin 2 → A) :
    (finTwoEquiv A f).2 = f 1 := rfl

@[simp] theorem finTwoEquiv_symm_zero (p : A × A) :
    (finTwoEquiv A).symm p 0 = p.1 := rfl

@[simp] theorem finTwoEquiv_symm_one (p : A × A) :
    (finTwoEquiv A).symm p 1 = p.2 := rfl

@[simp] theorem finTwoEquiv_snoc (f : Fin 1 → A) (a : A) :
    finTwoEquiv A (Fin.snoc f a) = (f 0, a) := by
  rfl

@[simp] theorem snoc_empty {A : Type} (a : A) :
    (Fin.snoc Fin.elim0 a : Fin 1 → A) = fun _ => a := by
  funext i
  fin_cases i
  rfl

/-- Two ordered contingent plans are a leader action and a follower plan. -/
def twoStrategyEquiv (A : Type) : Strategy 2 A ≃ A × (A → A) where
  toFun σ := (σ 0 Fin.elim0, fun a => σ 1 fun _ => a)
  invFun p := fun i =>
    Fin.cases (fun _ => p.1)
      (fun j h => p.2 (h (Fin.last j.val))) i
  left_inv σ := by
    apply funext
    intro i
    apply funext
    intro h
    fin_cases i
    · change σ 0 Fin.elim0 = σ 0 h
      apply congrArg (σ 0)
      funext j
      exact Fin.elim0 j
    · change σ 1 (fun _ => h (Fin.last 0)) = σ 1 h
      apply congrArg (σ 1)
      funext j
      fin_cases j
      rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · funext a
      rfl

@[simp] theorem twoStrategyEquiv_apply_fst (σ : Strategy 2 A) :
    (twoStrategyEquiv A σ).1 = σ 0 Fin.elim0 := rfl

@[simp] theorem twoStrategyEquiv_apply_snd (σ : Strategy 2 A) (a : A) :
    (twoStrategyEquiv A σ).2 a = σ 1 (fun _ => a) := rfl

/-- At horizon two, `ShapeSeq` is the existing direct two-stage shape, up to
the canonical function/product presentations of outcomes and cooutcomes. -/
def twoStageIso (A : Type) :
    OpenGameIso (ShapeSeq 2 A) (ShapeS A A) where
  eX := Equiv.refl _
  eS := Equiv.refl _
  eY := finTwoEquiv A
  eR := finTwoEquiv ℝ
  stratEquiv := twoStrategyEquiv A
  play_preserved := by
    intro σ x
    cases x
    rfl
  coplay_preserved := by
    intro σ x r
    cases x
    rfl
  equilibrium_preserved := by
    intro x k σ
    cases x
    change
      ((∀ a,
          (k (a, σ 1 (fun _ => a))).1 ≤
            (k (σ 0 Fin.elim0,
              σ 1 (fun _ => σ 0 Fin.elim0))).1) ∧
        ∀ a,
          (k (σ 0 Fin.elim0, a)).2 ≤
            (k (σ 0 Fin.elim0,
              σ 1 (fun _ => σ 0 Fin.elim0))).2) ↔
        ∀ i (deviation : StageStrategy A i.val),
          (finTwoEquiv ℝ).symm
              (k (finTwoEquiv A
                (realize 2 (Function.update σ i deviation)))) i ≤
            (finTwoEquiv ℝ).symm
              (k (finTwoEquiv A (realize 2 σ))) i
    constructor
    · rintro ⟨hleader, hfollower⟩ i deviation
      fin_cases i
      · simpa [realize, Function.update, Fin.snoc] using
          hleader (deviation Fin.elim0)
      · simpa [realize, Function.update, Fin.snoc] using
          hfollower (deviation fun _ => σ 0 Fin.elim0)
    · intro hn
      constructor
      · intro a
        let deviation : StageStrategy A 0 := fun _ => a
        simpa [realize, Function.update, Fin.snoc, deviation] using
          hn 0 deviation
      · intro a
        let deviation : StageStrategy A 1 := fun _ => a
        simpa [realize, Function.update, Fin.snoc, deviation] using
          hn 1 deviation

end ShapeSeq

/-! ## Heterogeneous finite horizons -/

namespace ShapeSeqDep

/-- Embed a coordinate of the prefix before `i` into the full horizon. -/
def priorIndex {n : Nat} (i : Fin n) (j : Fin i.val) : Fin n :=
  ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

/-- A dependent prefix containing precisely the actions before stage `i`. -/
abbrev History {n : Nat} (A : Fin n → Type) (i : Fin n) :=
  ∀ j : Fin i.val, A (priorIndex i j)

/-- One contingent plan for each stage-specific action type. -/
abbrev Strategy {n : Nat} (A : Fin n → Type) :=
  ∀ i, History A i → A i

/-- Realize stage `i`; recursive calls are confined to its strict prefix. -/
def realizeAt {n : Nat} {A : Fin n → Type} (σ : Strategy A)
    (i : Fin n) : A i :=
  σ i fun j => realizeAt σ (priorIndex i j)
termination_by i.val
decreasing_by exact j.isLt

/-- Realize the complete dependent action path. -/
def realize {n : Nat} {A : Fin n → Type} (σ : Strategy A) : ∀ i, A i :=
  fun i => realizeAt σ i

/-- The realized action at a stage is the contingent action selected from the
realized strict prefix. -/
theorem realize_eq {n : Nat} {A : Fin n → Type} (σ : Strategy A)
    (i : Fin n) :
    realize σ i = σ i (fun j => realize σ (priorIndex i j)) := by
  change realizeAt σ i = σ i (fun j => realizeAt σ (priorIndex i j))
  rw [realizeAt]

/-- Replacing a later-stage plan cannot change an earlier realized action. -/
theorem realizeAt_update_of_lt {n : Nat} {A : Fin n → Type}
    (σ : Strategy A) (i : Fin n) (deviation : History A i → A i)
    (j : Fin n) (hji : j.val < i.val) :
    realizeAt (Function.update σ i deviation) j = realizeAt σ j := by
  rw [realizeAt, realizeAt]
  have hne : j ≠ i := fun h => by subst h; omega
  rw [Function.update_of_ne hne]
  congr 1
  funext q
  exact realizeAt_update_of_lt σ i deviation (priorIndex j q)
    (Nat.lt_trans q.isLt hji)
termination_by j.val
decreasing_by exact q.isLt

/-- Coordinatewise form of `realize_update_eq_of_eq_at_reached_history`. -/
theorem realizeAt_updates_eq_of_eq_at_reached_history {n : Nat}
    {A : Fin n → Type} (σ : Strategy A) (i : Fin n)
    (deviation deviation' : History A i → A i)
    (hdev : deviation (fun j => realize σ (priorIndex i j)) =
      deviation' (fun j => realize σ (priorIndex i j))) (j : Fin n) :
    realizeAt (Function.update σ i deviation) j =
      realizeAt (Function.update σ i deviation') j := by
  rw [realizeAt, realizeAt]
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
    have hprefix : (fun q =>
        realizeAt (Function.update σ i deviation) (priorIndex i q)) =
        fun q => realize σ (priorIndex i q) := by
      funext q
      exact realizeAt_update_of_lt σ i deviation (priorIndex i q) q.isLt
    have hprefix' : (fun q =>
        realizeAt (Function.update σ i deviation') (priorIndex i q)) =
        fun q => realize σ (priorIndex i q) := by
      funext q
      exact realizeAt_update_of_lt σ i deviation' (priorIndex i q) q.isLt
    rw [hprefix, hprefix', hdev]
  · rw [Function.update_of_ne hji, Function.update_of_ne hji]
    congr 1
    funext q
    exact realizeAt_updates_eq_of_eq_at_reached_history σ i deviation
      deviation' hdev (priorIndex j q)
termination_by j.val
decreasing_by exact q.isLt

/-- Two replacements of the same stage have the same complete realization
when they choose the same action at the history reached before that stage.
Off-path values of a contingent deviation are therefore irrelevant. -/
theorem realize_update_eq_of_eq_at_reached_history {n : Nat}
    {A : Fin n → Type} (σ : Strategy A) (i : Fin n)
    (deviation deviation' : History A i → A i)
    (hdev : deviation (fun j => realize σ (priorIndex i j)) =
      deviation' (fun j => realize σ (priorIndex i j))) :
    realize (Function.update σ i deviation) =
      realize (Function.update σ i deviation') := by
  funext j
  exact realizeAt_updates_eq_of_eq_at_reached_history σ i deviation
    deviation' hdev j

end ShapeSeqDep

/-- A finite-horizon sequential shape with stage-specific action types. -/
def ShapeSeqDep {n : Nat} (A : Fin n → Type) :
    OpenGame Unit Unit (∀ i, A i) (Fin n → ℝ) where
  Strategy := ShapeSeqDep.Strategy A
  play := fun σ _ => ShapeSeqDep.realize σ
  coplay := fun _ _ _ => ()
  IsEquilibriumIn := fun _ k σ =>
    ∀ i (deviation : ShapeSeqDep.History A i → A i),
      k (ShapeSeqDep.realize (Function.update σ i deviation)) i ≤
        k (ShapeSeqDep.realize σ) i

namespace ShapeSeqDep

/-- The strategic form induced by a heterogeneous sequential shape. -/
def actionNFG {n : Nat} (A : Fin n → Type)
    (k : (∀ i, A i) → Fin n → ℝ) : NFG.NFGGame (Fin n) (fun i =>
      History A i → A i) where
  Outcome := ∀ i, A i
  outcome := realize
  utility := k

/-- Compile the heterogeneous horizon through the NFG bridge. -/
noncomputable def compileAction {n : Nat} (A : Fin n → Type)
    (k : (∀ i, A i) → Fin n → ℝ) : GameTheory.KernelGame (Fin n) :=
  (actionNFG A k).toKernelGame

/-- Open-game equilibrium is definitionally strategic-form Nash. -/
theorem isEquilibriumIn_iff_isNashPure {n : Nat} {A : Fin n → Type}
    (k : (∀ i, A i) → Fin n → ℝ) (σ : Strategy A) :
    (ShapeSeqDep A).IsEquilibriumIn () k σ ↔
      NFG.IsNashPure (actionNFG A k) σ := by
  rfl

/-- Kernel-level correctness for heterogeneous finite horizons. -/
theorem isEquilibriumIn_iff_isNash {n : Nat} {A : Fin n → Type}
    (k : (∀ i, A i) → Fin n → ℝ) (σ : Strategy A) :
    (ShapeSeqDep A).IsEquilibriumIn () k σ ↔
      (compileAction A k).IsNash σ := by
  rw [isEquilibriumIn_iff_isNashPure]
  exact NFG.IsNashPure_iff_kernelGame (actionNFG A k) σ

/-! ## Conditioning at every finite history -/

/-- A profile `τ` presents a counterfactual history at stage `i` when its
current and later plans agree with the reference profile `σ`.  Only the plans
strictly before `i` may differ, so realizing `τ` reaches a counterfactual
prefix and then continues according to `σ`.

Quantifying over predecessor profiles rather than explicitly packaging
dependent histories avoids transports while covering exactly the histories
generated by earlier pure choices. -/
def IsConditionedEquilibrium {n : Nat} {A : Fin n → Type}
    (k : (∀ i, A i) → Fin n → ℝ) (σ : Strategy A) : Prop :=
  ∀ (i : Fin n) (τ : Strategy A),
    (∀ j, i.val ≤ j.val → τ j = σ j) →
    ∀ deviation : History A i → A i,
      k (realize (Function.update τ i deviation)) i ≤ k (realize τ) i

/-- One-shot presentation of finite-horizon conditioning: at every
counterfactual predecessor profile, changing only the action selected at the
reached information set is unprofitable. -/
def IsOneShotConditionedEquilibrium {n : Nat} {A : Fin n → Type}
    (k : (∀ i, A i) → Fin n → ℝ) (σ : Strategy A) : Prop :=
  ∀ (i : Fin n) (τ : Strategy A),
    (∀ j, i.val ≤ j.val → τ j = σ j) →
    ∀ action : A i,
      k (realize (Function.update τ i (fun _ => action))) i ≤ k (realize τ) i

/-- Arbitrary contingent replacements and one-shot action changes are exactly
equivalent in the conditioned predicate: only the deviation's value at the
reached history can affect play. -/
theorem isConditionedEquilibrium_iff_isOneShot {n : Nat}
    {A : Fin n → Type} (k : (∀ i, A i) → Fin n → ℝ)
    (σ : Strategy A) :
    IsConditionedEquilibrium k σ ↔ IsOneShotConditionedEquilibrium k σ := by
  constructor
  · intro h i τ hagree action
    exact h i τ hagree (fun _ => action)
  · intro h i τ hagree deviation
    let history : History A i := fun j => realize τ (priorIndex i j)
    have hone := h i τ hagree (deviation history)
    have hrealize : realize (Function.update τ i deviation) =
        realize (Function.update τ i (fun _ => deviation history)) := by
      apply realize_update_eq_of_eq_at_reached_history
      rfl
    rw [hrealize]
    exact hone

/-- The finite-horizon sequential shape conditioned at every counterfactual
history.  It has the same strategies, play, and boundaries as `ShapeSeqDep`;
only its equilibrium predicate is strengthened. -/
def conditioned {n : Nat} (A : Fin n → Type) :
    OpenGame Unit Unit (∀ i, A i) (Fin n → ℝ) where
  Strategy := Strategy A
  play := fun σ _ => realize σ
  coplay := fun _ _ _ => ()
  IsEquilibriumIn := fun _ k σ => IsConditionedEquilibrium k σ

/-- Unfolding the conditioned shape exposes its intrinsic one-shot
inequalities at every counterfactual predecessor profile. -/
theorem conditioned_isEquilibriumIn_iff {n : Nat} {A : Fin n → Type}
    (k : (∀ i, A i) → Fin n → ℝ) (σ : Strategy A) :
    (conditioned A).IsEquilibriumIn () k σ ↔
      IsConditionedEquilibrium k σ :=
  Iff.rfl

/-- The conditioned open game is equivalently characterized by one action
change at every counterfactual reached information set. -/
theorem conditioned_isEquilibriumIn_iff_oneShot {n : Nat}
    {A : Fin n → Type} (k : (∀ i, A i) → Fin n → ℝ)
    (σ : Strategy A) :
    (conditioned A).IsEquilibriumIn () k σ ↔
      IsOneShotConditionedEquilibrium k σ :=
  isConditionedEquilibrium_iff_isOneShot k σ

/-- Conditioning strengthens the plain agent-form equilibrium predicate. -/
theorem conditioned_implies_plain {n : Nat} {A : Fin n → Type}
    (k : (∀ i, A i) → Fin n → ℝ) (σ : Strategy A)
    (hσ : (conditioned A).IsEquilibriumIn () k σ) :
    (ShapeSeqDep A).IsEquilibriumIn () k σ := by
  intro i deviation
  exact hσ i σ (fun _ _ => rfl) deviation

/-- Read an abstract prefix history at the corresponding full-horizon stage. -/
def historyAction {n : Nat} {A : Fin n → Type} {i : Fin n}
    (h : History A i) (j : Fin n) (hj : j.val < i.val) : A j := by
  let q : Fin i.val := ⟨j.val, hj⟩
  have hq : priorIndex i q = j := by
    apply Fin.ext
    rfl
  rw [← hq]
  exact h q

/-- Force a counterfactual prefix using constant earlier plans, while retaining
the reference profile from stage `i` onward. -/
def profileForHistory {n : Nat} {A : Fin n → Type}
    (σ : Strategy A) (i : Fin n) (h : History A i) : Strategy A :=
  fun j history => if hj : j.val < i.val then historyAction h j hj else σ j history

theorem profileForHistory_eq_of_le {n : Nat} {A : Fin n → Type}
    (σ : Strategy A) (i : Fin n) (h : History A i)
    (j : Fin n) (hij : i.val ≤ j.val) :
    profileForHistory σ i h j = σ j := by
  funext history
  simp [profileForHistory, Nat.not_lt.mpr hij]

@[simp] theorem realize_profileForHistory_prior {n : Nat}
    {A : Fin n → Type} (σ : Strategy A) (i : Fin n) (h : History A i)
    (j : Fin i.val) :
    realize (profileForHistory σ i h) (priorIndex i j) = h j := by
  change realizeAt (profileForHistory σ i h) (priorIndex i j) = h j
  rw [realizeAt]
  simp only [profileForHistory]
  split
  · next hj =>
      unfold historyAction
      apply eq_of_heq
      rfl
  · next hj =>
      exact absurd j.isLt hj

/-- Predecessor-profile quantification covers every abstract dependent
history: constant earlier plans realize the requested prefix, and the profile
agrees with `σ` at the current and all later stages. -/
theorem exists_profile_realizing_history {n : Nat} {A : Fin n → Type}
    (σ : Strategy A) (i : Fin n) (h : History A i) :
    ∃ τ : Strategy A,
      (∀ j, i.val ≤ j.val → τ j = σ j) ∧
      ∀ j, realize τ (priorIndex i j) = h j := by
  refine ⟨profileForHistory σ i h, profileForHistory_eq_of_le σ i h, ?_⟩
  exact realize_profileForHistory_prior σ i h

end ShapeSeqDep

end OpenGames
