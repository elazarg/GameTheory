/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation.Exact
import Math.LinearProgramming.Certificates

/-!
# Exact set prices via dominance skeletons

Finite exact implementation of a target set is fundamentally a product-set
problem: `undominatedProfiles` is the product of the players' undominated
strategy sets.  This module packages that observation as a dominance-skeleton
certificate theory.  A skeleton chooses, for every strategy outside the desired
coordinate set, a dominator; a transfer realizes the skeleton when target
strategies are undominated and excluded strategies are dominated by their
chosen dominators.  A branch certificate then expands the semantic skeleton
into explicit payoff-inequality branches: strict witness columns for excluded
strategies and finite disjunctive certificates that target strategies are not
dominated.

The resulting cost set is definitionally the finite skeleton-search surface behind
exact set prices: exact costs for a nonempty rectangular target coincide with
costs certified by some dominance skeleton, equivalently by some branch
certificate over such a skeleton.
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- Payment variables for profile-observed transfers: one coordinate for each
realized profile and player. -/
abbrev PaymentVar (G : KernelGame ι) := Profile G × ι

/-- Payment variables plus one explicit budget coordinate. -/
abbrev BudgetPaymentVar (G : KernelGame ι) := Unit ⊕ G.PaymentVar

/-- Read a vector over payment variables as a transfer scheme. -/
def vectorTransfer (G : KernelGame ι) (x : G.PaymentVar → ℝ) :
    Profile G → Payoff ι :=
  fun σ i => x (σ, i)

/-- The budget coordinate of a budget/payment vector. -/
def budgetOfVector (G : KernelGame ι) (x : G.BudgetPaymentVar → ℝ) : ℝ :=
  x (Sum.inl ())

/-- The payment coordinates of a budget/payment vector. -/
def paymentOfBudgetVector (G : KernelGame ι)
    (x : G.BudgetPaymentVar → ℝ) : G.PaymentVar → ℝ :=
  fun q => x (Sum.inr q)

namespace BranchLinear

open Math.LinearProgramming

/-- Coefficients for the transfer difference `V target i - V dev i`. -/
noncomputable def diffCoeff (G : KernelGame ι) (i : ι)
    (target dev : Profile G) : G.PaymentVar → ℝ :=
  open Classical in
  fun q =>
    (if q = (target, i) then (1 : ℝ) else 0) -
      if q = (dev, i) then (1 : ℝ) else 0

/-- Coefficients for the negative total payment at a profile,
`-∑ i, V σ i`. -/
noncomputable def costCoeff (G : KernelGame ι) (σ : Profile G) :
    G.PaymentVar → ℝ :=
  open Classical in
  fun q => if q.1 = σ then (-1 : ℝ) else 0

theorem rowEval_diffCoeff [Fintype ι] [Fintype (Profile G)]
    {Row : Type} (r : Row) (x : G.PaymentVar → ℝ)
    (i : ι) (target dev : Profile G) :
    rowEval (fun _ q => diffCoeff G i target dev q) x r =
      x (target, i) - x (dev, i) := by
  classical
  dsimp [rowEval]
  simp [diffCoeff, sub_mul, Finset.sum_sub_distrib]

theorem rowEval_costCoeff [Fintype ι] [Fintype (Profile G)]
    {Row : Type} (r : Row)
    (x : G.PaymentVar → ℝ) (σ : Profile G) :
    rowEval (fun _ q => costCoeff G σ q) x r =
      -∑ i : ι, x (σ, i) := by
  classical
  dsimp [rowEval]
  calc
    (∑ q : G.PaymentVar, costCoeff G σ q * x q)
        = ∑ p : Profile G, ∑ i : ι, costCoeff G σ (p, i) * x (p, i) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ i : ι, (-1 : ℝ) * x (σ, i) := by
          simp [costCoeff]
    _ = -∑ i : ι, x (σ, i) := by
          rw [← Finset.sum_neg_distrib]
          simp

end BranchLinear

/-- Rectangular/product target set determined by desired coordinate sets. -/
def rect (G : KernelGame ι) (S : ∀ i, Set (G.Strategy i)) : Set (Profile G) :=
  {σ | ∀ i, σ i ∈ S i}

@[simp] theorem mem_rect {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)}
    {σ : Profile G} :
    σ ∈ G.rect S ↔ ∀ i, σ i ∈ S i := Iff.rfl

theorem rect_nonempty_of_forall_nonempty {G : KernelGame ι}
    {S : ∀ i, Set (G.Strategy i)} (hS : ∀ i, (S i).Nonempty) :
    (G.rect S).Nonempty := by
  classical
  refine ⟨fun i => Classical.choose (hS i), ?_⟩
  intro i
  exact Classical.choose_spec (hS i)

/-- A set of profiles is rectangular when it is a product of coordinate sets. -/
def IsRectangular (G : KernelGame ι) (O : Set (Profile G)) : Prop :=
  ∃ S : ∀ i, Set (G.Strategy i), O = G.rect S

variable [DecidableEq ι]

/-- The undominated profile set is the rectangle of the coordinatewise
undominated strategy sets. -/
theorem undominatedProfiles_eq_rect_undominatedStrategies (G : KernelGame ι) :
    G.undominatedProfiles =
      G.rect (fun i => {s : G.Strategy i | G.IsUndominated i s}) := by
  rfl

/-- Exact implementation can only produce rectangular targets. -/
theorem IsExactImplementation.target_rectangular {G : KernelGame ι}
    {V : Profile G → Payoff ι} {O : Set (Profile G)}
    (h : G.IsExactImplementation V O) :
    G.IsRectangular O := by
  refine ⟨fun i => {s : (G.subsidize V).Strategy i |
      (G.subsidize V).IsUndominated i s}, ?_⟩
  rw [← h.undominatedProfiles_eq]
  rfl

/-- A dominance skeleton for exact implementation of `G.rect S`: every
coordinate strategy outside `S i` is assigned a proposed dominator. -/
structure ExactDominanceSkeleton (G : KernelGame ι)
    (S : ∀ i, Set (G.Strategy i)) where
  excludedDominator :
    ∀ i, {s : G.Strategy i // s ∉ S i} → G.Strategy i

namespace ExactDominanceSkeleton

/-- A finite branch explaining why `t` does not dominate target strategy `s`.
Either `t` fails weak dominance at one profile, or `s` weakly dominates `t`
everywhere, so no strict witness for `t` over `s` can exist. -/
inductive TargetNonDominationCertificate {G : KernelGame ι} (i : ι)
    (s t : G.Strategy i) : Type where
  | weakFailure (σ : Profile G)
  | noStrict

namespace TargetNonDominationCertificate

/-- A transfer realizes a target non-domination branch in the subsidized game. -/
def RealizedBy {G : KernelGame ι} {i : ι} {s t : G.Strategy i}
    (c : TargetNonDominationCertificate i s t) (V : Profile G → Payoff ι) :
    Prop :=
  match c with
  | weakFailure σ =>
      (G.subsidize V).eu (Function.update σ i s) i >
        (G.subsidize V).eu (Function.update σ i t) i
  | noStrict =>
      ∀ σ : Profile G,
        (G.subsidize V).eu (Function.update σ i s) i ≥
          (G.subsidize V).eu (Function.update σ i t) i

/-- A realized target non-domination branch refutes weak dominance with a
strict witness by the rival strategy. -/
theorem RealizedBy.not_weaklyStrictlyDominates {G : KernelGame ι}
    {V : Profile G → Payoff ι} {i : ι} {s t : G.Strategy i}
    {c : TargetNonDominationCertificate i s t}
    (h : c.RealizedBy V) :
    ¬ (G.subsidize V).WeaklyStrictlyDominates i t s := by
  cases c with
  | weakFailure σ =>
      intro hdom
      have hweak := hdom.toWeaklyDominates σ
      dsimp [RealizedBy] at h
      exact (not_le_of_gt h) hweak
  | noStrict =>
      intro hdom
      obtain ⟨σ, hstrict⟩ := hdom.strict_witness
      have hle := h σ
      exact (not_le_of_gt hstrict) hle

end TargetNonDominationCertificate

/-- A transfer realizes a dominance skeleton when it is nonnegative, target
coordinate strategies are undominated, and every excluded coordinate strategy
is dominated by the skeleton's chosen dominator. -/
def RealizedBy {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)}
    (sk : G.ExactDominanceSkeleton S) (V : Profile G → Payoff ι) : Prop :=
  (∀ σ i, 0 ≤ V σ i) ∧
    (∀ i (s : G.Strategy i), s ∈ S i → (G.subsidize V).IsUndominated i s) ∧
      ∀ i (s : {s : G.Strategy i // s ∉ S i}),
        (G.subsidize V).WeaklyStrictlyDominates i
          (sk.excludedDominator i s) s.1

/-- A branch certificate for a dominance skeleton: strict witness columns for
excluded strategies, and target-side branches explaining why no rival dominates
each target strategy. -/
structure BranchCertificate {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)}
    (sk : G.ExactDominanceSkeleton S) where
  excludedStrictWitness :
    ∀ i (_ : {s : G.Strategy i // s ∉ S i}), Profile G
  targetCertificate :
    ∀ i (s : {s : G.Strategy i // s ∈ S i}) (t : G.Strategy i),
      TargetNonDominationCertificate i s.1 t

namespace BranchCertificate

/-- A transfer realizes the explicit branch expansion of a dominance skeleton. -/
def RealizedBy {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate)
    (V : Profile G → Payoff ι) : Prop :=
  (∀ σ i, 0 ≤ V σ i) ∧
    (∀ i (s : {s : G.Strategy i // s ∈ S i}) (t : G.Strategy i),
      (br.targetCertificate i s t).RealizedBy V) ∧
      (∀ i (s : {s : G.Strategy i // s ∉ S i}) (σ : Profile G),
        (G.subsidize V).eu
            (Function.update σ i (sk.excludedDominator i s)) i ≥
          (G.subsidize V).eu (Function.update σ i s.1) i) ∧
        ∀ i (s : {s : G.Strategy i // s ∉ S i}),
          (G.subsidize V).eu
              (Function.update (br.excludedStrictWitness i s) i
                (sk.excludedDominator i s)) i >
            (G.subsidize V).eu
              (Function.update (br.excludedStrictWitness i s) i s.1) i

theorem RealizedBy.nonneg {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {br : sk.BranchCertificate}
    {V : Profile G → Payoff ι} (h : br.RealizedBy V) :
    ∀ σ i, 0 ≤ V σ i :=
  h.1

theorem RealizedBy.to_realizedBy {G : KernelGame ι}
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {br : sk.BranchCertificate}
    {V : Profile G → Payoff ι} (h : br.RealizedBy V) :
    sk.RealizedBy V := by
  refine ⟨h.nonneg, ?_, ?_⟩
  · intro i s hs t hdom
    exact (h.2.1 i ⟨s, hs⟩ t).not_weaklyStrictlyDominates hdom
  · intro i s
    refine ⟨?_, ?_⟩
    · intro σ
      exact h.2.2.1 i s σ
    · exact ⟨br.excludedStrictWitness i s, h.2.2.2 i s⟩

/-- Weak linear rows for a fixed branch certificate.  Target rows use target
coordinate strategies, excluded rows use excluded coordinate strategies, and
cost rows use target profiles. -/
abbrev WeakRow {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (_br : sk.BranchCertificate) : Type :=
  (Σ i : ι, {s : G.Strategy i // s ∈ S i} × G.Strategy i × Profile G) ⊕
    ((Σ i : ι, {s : G.Strategy i // s ∉ S i} × Profile G) ⊕
      {σ : Profile G // σ ∈ G.rect S})

/-- Strict linear rows for a fixed branch certificate.  Target no-strict rows
are interpreted as the tautology `-1 < 0`; weak-failure rows and excluded rows
carry the strict witness inequalities. -/
abbrev StrictRow {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (_br : sk.BranchCertificate) : Type :=
  (Σ i : ι, {s : G.Strategy i // s ∈ S i} × G.Strategy i) ⊕
    (Σ i : ι, {s : G.Strategy i // s ∉ S i})

namespace Matrix

open Math.LinearProgramming

/-- Weak-row coefficient matrix for a fixed branch certificate. -/
noncomputable def weakA {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate) :
    WeakRow br → G.PaymentVar → ℝ :=
  fun row =>
    match row with
    | Sum.inl ⟨i, s, t, σ⟩ =>
        match br.targetCertificate i s t with
        | TargetNonDominationCertificate.noStrict =>
            BranchLinear.diffCoeff G i (Function.update σ i s.1) (Function.update σ i t)
        | TargetNonDominationCertificate.weakFailure _ => fun _ => 0
    | Sum.inr (Sum.inl ⟨i, s, σ⟩) =>
        BranchLinear.diffCoeff G i
          (Function.update σ i (sk.excludedDominator i s))
          (Function.update σ i s.1)
    | Sum.inr (Sum.inr σ) => BranchLinear.costCoeff G σ.1

/-- Weak-row right-hand side for a fixed branch certificate and budget. -/
noncomputable def weakB {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate) (k : ℝ) :
    WeakRow br → ℝ :=
  fun row =>
    match row with
    | Sum.inl ⟨i, s, t, σ⟩ =>
        match br.targetCertificate i s t with
        | TargetNonDominationCertificate.noStrict =>
            G.eu (Function.update σ i t) i - G.eu (Function.update σ i s.1) i
        | TargetNonDominationCertificate.weakFailure _ => 0
    | Sum.inr (Sum.inl ⟨i, s, σ⟩) =>
        G.eu (Function.update σ i s.1) i -
          G.eu (Function.update σ i (sk.excludedDominator i s)) i
    | Sum.inr (Sum.inr _σ) => -k

/-- Strict-row coefficient matrix for a fixed branch certificate. -/
noncomputable def strictA {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate) :
    StrictRow br → G.PaymentVar → ℝ :=
  fun row =>
    match row with
    | Sum.inl ⟨i, s, t⟩ =>
        match br.targetCertificate i s t with
        | TargetNonDominationCertificate.weakFailure σ =>
            BranchLinear.diffCoeff G i (Function.update σ i s.1) (Function.update σ i t)
        | TargetNonDominationCertificate.noStrict => fun _ => 0
    | Sum.inr ⟨i, s⟩ =>
        BranchLinear.diffCoeff G i
          (Function.update (br.excludedStrictWitness i s) i
            (sk.excludedDominator i s))
          (Function.update (br.excludedStrictWitness i s) i s.1)

/-- Strict-row right-hand side for a fixed branch certificate. -/
noncomputable def strictB {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate) :
    StrictRow br → ℝ :=
  fun row =>
    match row with
    | Sum.inl ⟨i, s, t⟩ =>
        match br.targetCertificate i s t with
        | TargetNonDominationCertificate.weakFailure σ =>
            G.eu (Function.update σ i t) i - G.eu (Function.update σ i s.1) i
        | TargetNonDominationCertificate.noStrict => -1
    | Sum.inr ⟨i, s⟩ =>
        G.eu (Function.update (br.excludedStrictWitness i s) i s.1) i -
          G.eu
            (Function.update (br.excludedStrictWitness i s) i
              (sk.excludedDominator i s)) i

/-- Feasibility of the matrix system associated with a fixed branch
certificate.  Weak rows form a standard-form LP; strict rows are the open
halfspaces recording strict dominance witnesses. -/
def Feasible {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate) (k : ℝ)
    [Fintype (WeakRow br)] [Fintype (StrictRow br)]
    (x : G.PaymentVar → ℝ) : Prop :=
  MinPrimalFeasible (weakA br) (weakB br k) x ∧
    ∀ row : StrictRow br, strictB br row < rowEval (strictA br) x row

/-- Standard-form objective: minimize the explicit budget coordinate. -/
noncomputable def budgetC {G : KernelGame ι} :
    G.BudgetPaymentVar → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => 0

/-- Weak-row matrix with an explicit nonnegative budget variable.  Cost rows
become `K - ∑ᵢ V(σ,i) ≥ 0`; all dominance rows ignore the budget coordinate. -/
noncomputable def weakBudgetA {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate)
    [Fintype (WeakRow br)] :
    WeakRow br → G.BudgetPaymentVar → ℝ
  | Sum.inr (Sum.inr _), Sum.inl _ => 1
  | _, Sum.inl _ => 0
  | row, Sum.inr q => weakA br row q

/-- Strict-row matrix lifted to the explicit-budget column space.  Strict
dominance witnesses do not mention the budget coordinate. -/
noncomputable def strictBudgetA
    {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate)
    [Fintype (StrictRow br)] :
    StrictRow br → G.BudgetPaymentVar → ℝ
  | _, Sum.inl _ => 0
  | row, Sum.inr q => strictA br row q

/-- Fixed-branch feasibility as a standard-form minimization LP with objective
`budgetC`, plus the same open strict-witness rows as before. -/
def BudgetFeasible {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate)
    [Fintype (WeakRow br)] [Fintype (StrictRow br)]
    (x : G.BudgetPaymentVar → ℝ) : Prop :=
  MinPrimalFeasible (weakBudgetA br) (weakB br 0) x ∧
    ∀ row : StrictRow br, strictB br row < rowEval (strictBudgetA br) x row

omit [DecidableEq ι] in
theorem minPrimalValue_budgetC
    {G : KernelGame ι} [Fintype G.PaymentVar]
    (x : G.BudgetPaymentVar → ℝ) :
    minPrimalValue budgetC x = G.budgetOfVector x := by
  classical
  simp [minPrimalValue, dot, budgetC, budgetOfVector]

theorem rowEval_weakBudgetA
    {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate)
    [Fintype (WeakRow br)]
    (x : G.BudgetPaymentVar → ℝ) (row : WeakRow br) :
    rowEval (weakBudgetA br) x row =
      (match row with
        | Sum.inr (Sum.inr _) => G.budgetOfVector x
        | _ => 0) +
        rowEval (weakA br) (G.paymentOfBudgetVector x) row := by
  classical
  cases row with
  | inl targetRow =>
      simp [rowEval, weakBudgetA, paymentOfBudgetVector]
  | inr rest =>
      cases rest with
      | inl excludedRow =>
          simp [rowEval, weakBudgetA, paymentOfBudgetVector]
      | inr σ =>
          simp [rowEval, weakBudgetA, paymentOfBudgetVector, budgetOfVector,
            Fintype.sum_sum_type]

theorem rowEval_strictBudgetA
    {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate)
    [Fintype (StrictRow br)]
    (x : G.BudgetPaymentVar → ℝ) (row : StrictRow br) :
    rowEval (strictBudgetA br) x row =
      rowEval (strictA br) (G.paymentOfBudgetVector x) row := by
  classical
  simp [rowEval, strictBudgetA, paymentOfBudgetVector, Fintype.sum_sum_type]

theorem BudgetFeasible.to_feasible
    {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    {br : sk.BranchCertificate} [Fintype (WeakRow br)] [Fintype (StrictRow br)]
    {x : G.BudgetPaymentVar → ℝ} (h : BudgetFeasible br x) :
    Feasible br (G.budgetOfVector x) (G.paymentOfBudgetVector x) := by
  classical
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro q
      exact h.1.1 (Sum.inr q)
    · intro row
      have hrow := h.1.2 row
      rw [rowEval_weakBudgetA br x row] at hrow
      cases row with
      | inl targetRow =>
          simpa [weakB.eq_def] using hrow
      | inr rest =>
          cases rest with
          | inl excludedRow =>
              simpa [weakB.eq_def] using hrow
          | inr σ =>
              have hrow0 :
                  0 ≤ G.budgetOfVector x +
                    rowEval (weakA br) (G.paymentOfBudgetVector x)
                      (Sum.inr (Sum.inr σ)) := by
                simpa [weakB.eq_def] using hrow
              have hlin :
                  -G.budgetOfVector x ≤
                    rowEval (weakA br) (G.paymentOfBudgetVector x)
                      (Sum.inr (Sum.inr σ)) := by
                linarith
              simpa [weakB.eq_def] using hlin
  · intro row
    have hrow := h.2 row
    rwa [rowEval_strictBudgetA br x row] at hrow


/-- Standard-form Farkas certificate for infeasibility of the closed weak rows
of a fixed branch certificate.  The open strict rows are handled separately by
strict-slack lemmas. -/
theorem not_exists_weakFeasible_iff_exists_dual_certificate
    {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate)
    [Fintype (WeakRow br)] {k : ℝ} :
    (¬ ∃ x : G.PaymentVar → ℝ, MinPrimalFeasible (weakA br) (weakB br k) x) ↔
      ∃ y : WeakRow br → ℝ,
        Nonnegative y ∧
          (∀ q : G.PaymentVar, colEval (weakA br) y q ≤ 0) ∧
            0 < dot (weakB br k) y :=
  not_exists_minPrimalFeasible_iff_exists_dual_certificate

/-- Strict slack of a strict branch row at a payment vector. -/
noncomputable def strictSlack {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate)
    (x : G.PaymentVar → ℝ) (row : StrictRow br) : ℝ :=
  rowEval (strictA br) x row - strictB br row

/-- Fixed-branch matrix feasibility is monotone in the budget. -/
theorem Feasible.mono_budget
    {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    {br : sk.BranchCertificate} [Fintype (WeakRow br)] [Fintype (StrictRow br)]
    {k l : ℝ} {x : G.PaymentVar → ℝ}
    (h : Feasible br k x) (hkl : k ≤ l) :
    Feasible br l x := by
  classical
  refine ⟨⟨h.1.1, ?_⟩, h.2⟩
  intro row
  have hrow := h.1.2 row
  cases row with
  | inl targetRow =>
      rcases targetRow with ⟨i, s, t, σ⟩
      simpa [weakB.eq_def] using hrow
  | inr rest =>
      cases rest with
      | inl excludedRow =>
          rcases excludedRow with ⟨i, s, σ⟩
          simpa [weakB.eq_def] using hrow
      | inr σ =>
          have hk : -l ≤ -k := by linarith
          simpa [weakB.eq_def] using hk.trans hrow

theorem Feasible.strictSlack_pos
    {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    {br : sk.BranchCertificate} [Fintype (WeakRow br)] [Fintype (StrictRow br)]
    {k : ℝ} {x : G.PaymentVar → ℝ} (h : Feasible br k x) (row : StrictRow br) :
    0 < strictSlack br x row := by
  dsimp [strictSlack]
  linarith [h.2 row]

/-- A feasible finite branch system has a uniform positive margin on all strict
rows.  This is the finite-open-constraints fact behind rational approximation
and boundary analyses. -/
theorem Feasible.exists_pos_le_strictSlack
    {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    {br : sk.BranchCertificate} [Fintype (WeakRow br)] [Fintype (StrictRow br)]
    {k : ℝ} {x : G.PaymentVar → ℝ} (h : Feasible br k x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ row : StrictRow br, ε ≤ strictSlack br x row := by
  classical
  by_cases hne : (Finset.univ : Finset (StrictRow br)).Nonempty
  · let m : ℝ := Finset.univ.inf' hne (strictSlack br x)
    have hm_pos : 0 < m := by
      rw [Finset.lt_inf'_iff]
      intro row _hrow
      exact h.strictSlack_pos row
    refine ⟨m / 2, by linarith, ?_⟩
    intro row
    have hm_le : m ≤ strictSlack br x row :=
      Finset.inf'_le (f := strictSlack br x) (Finset.mem_univ row)
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro row
    exfalso
    exact hne ⟨row, Finset.mem_univ row⟩

theorem rowEval_weakA_target_noStrict
    {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    (br : sk.BranchCertificate) [Fintype G.PaymentVar]
    (x : G.PaymentVar → ℝ) (i : ι) (s : {s : G.Strategy i // s ∈ S i})
    (t : G.Strategy i) (σ : Profile G)
    (hc : br.targetCertificate i s t = TargetNonDominationCertificate.noStrict) :
    rowEval (weakA br) x (Sum.inl ⟨i, s, t, σ⟩) =
      x (Function.update σ i s.1, i) - x (Function.update σ i t, i) := by
  classical
  dsimp [rowEval]
  simp [weakA.eq_def, hc, BranchLinear.diffCoeff, sub_mul, Finset.sum_sub_distrib]

theorem rowEval_strictA_target_weakFailure
    {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    (br : sk.BranchCertificate) [Fintype G.PaymentVar]
    (x : G.PaymentVar → ℝ) (i : ι) (s : {s : G.Strategy i // s ∈ S i})
    (t : G.Strategy i) (σ : Profile G)
    (hc : br.targetCertificate i s t = TargetNonDominationCertificate.weakFailure σ) :
    rowEval (strictA br) x (Sum.inl ⟨i, s, t⟩) =
      x (Function.update σ i s.1, i) - x (Function.update σ i t, i) := by
  classical
  dsimp [rowEval]
  simp [strictA.eq_def, hc, BranchLinear.diffCoeff, sub_mul, Finset.sum_sub_distrib]

theorem rowEval_weakA_excluded
    {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    (br : sk.BranchCertificate) [Fintype G.PaymentVar]
    (x : G.PaymentVar → ℝ) (i : ι) (s : {s : G.Strategy i // s ∉ S i})
    (σ : Profile G) :
    rowEval (weakA br) x (Sum.inr (Sum.inl ⟨i, s, σ⟩)) =
      x (Function.update σ i (sk.excludedDominator i s), i) -
        x (Function.update σ i s.1, i) := by
  classical
  dsimp [rowEval]
  simp [weakA.eq_def, BranchLinear.diffCoeff, sub_mul, Finset.sum_sub_distrib]

theorem rowEval_strictA_excluded
    {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    (br : sk.BranchCertificate) [Fintype G.PaymentVar]
    (x : G.PaymentVar → ℝ) (i : ι) (s : {s : G.Strategy i // s ∉ S i}) :
    rowEval (strictA br) x (Sum.inr ⟨i, s⟩) =
      x (Function.update (br.excludedStrictWitness i s) i
          (sk.excludedDominator i s), i) -
        x (Function.update (br.excludedStrictWitness i s) i s.1, i) := by
  classical
  dsimp [rowEval]
  simp [strictA.eq_def, BranchLinear.diffCoeff, sub_mul, Finset.sum_sub_distrib]

theorem rowEval_weakA_cost
    {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    (br : sk.BranchCertificate)
    (x : G.PaymentVar → ℝ) (σ : {σ : Profile G // σ ∈ G.rect S}) :
    rowEval (weakA br) x (Sum.inr (Sum.inr σ)) =
      -∑ i : ι, x (σ.1, i) := by
  classical
  dsimp [rowEval]
  calc
    (∑ q : G.PaymentVar, weakA br (Sum.inr (Sum.inr σ)) q * x q)
        = ∑ q : G.PaymentVar, BranchLinear.costCoeff G σ.1 q * x q := by
          simp [weakA.eq_def]
    _ = -∑ i : ι, x (σ.1, i) := by
          simpa [rowEval] using
            (BranchLinear.rowEval_costCoeff
              (r := (Sum.inr (Sum.inr σ) : WeakRow br)) x σ.1)

theorem Feasible.exists_budgetFeasible
    {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    {br : sk.BranchCertificate} [Fintype (WeakRow br)] [Fintype (StrictRow br)]
    {k : ℝ} {x : G.PaymentVar → ℝ} (hS : (G.rect S).Nonempty)
    (h : Feasible br k x) :
    ∃ z : G.BudgetPaymentVar → ℝ,
      BudgetFeasible br z ∧ G.budgetOfVector z = k ∧
        G.paymentOfBudgetVector z = x := by
  classical
  have hk_nonneg : 0 ≤ k := by
    rcases hS with ⟨σ, hσ⟩
    have hrow := h.1.2 (Sum.inr (Sum.inr ⟨σ, hσ⟩))
    rw [rowEval_weakA_cost br x ⟨σ, hσ⟩] at hrow
    have hsum_nonneg : 0 ≤ ∑ i : ι, x (σ, i) :=
      Finset.sum_nonneg fun i _ => h.1.1 (σ, i)
    have hk : ∑ i : ι, x (σ, i) ≤ k := by
      simpa [weakB.eq_def] using neg_le_neg hrow
    exact hsum_nonneg.trans hk
  let z : G.BudgetPaymentVar → ℝ
    | Sum.inl _ => k
    | Sum.inr q => x q
  have hzpay : G.paymentOfBudgetVector z = x := by
    ext q
    rfl
  refine ⟨z, ?_, rfl, hzpay⟩
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro q
      cases q with
      | inl _ => exact hk_nonneg
      | inr q => exact h.1.1 q
    · intro row
      rw [rowEval_weakBudgetA br z row, hzpay]
      cases row with
      | inl targetRow =>
          simpa [weakB.eq_def] using h.1.2 (Sum.inl targetRow)
      | inr rest =>
          cases rest with
          | inl excludedRow =>
              simpa [weakB.eq_def] using h.1.2 (Sum.inr (Sum.inl excludedRow))
          | inr σ =>
              have hrow := h.1.2 (Sum.inr (Sum.inr σ))
              have hlin : 0 ≤ k + rowEval (weakA br) x (Sum.inr (Sum.inr σ)) := by
                have hraw : -k ≤ rowEval (weakA br) x (Sum.inr (Sum.inr σ)) := by
                  simpa [weakB.eq_def] using hrow
                linarith
              simpa [weakB.eq_def, z, budgetOfVector] using hlin
  · intro row
    rw [rowEval_strictBudgetA br z row, hzpay]
    exact h.2 row

/-- The fixed-branch matrix system is exactly the linearized form of branch
realization plus the target-profile budget bound. -/
theorem feasible_iff_realizedBy_vectorTransfer_and_cost
    {G : KernelGame ι} [Fintype ι] [Fintype (Profile G)] [Finite G.Outcome]
    {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    (br : sk.BranchCertificate) [Fintype (WeakRow br)] [Fintype (StrictRow br)]
    {k : ℝ} {x : G.PaymentVar → ℝ} :
    Feasible br k x ↔
      br.RealizedBy (G.vectorTransfer x) ∧
        ∀ σ : Profile G, σ ∈ G.rect S → (∑ i, G.vectorTransfer x σ i) ≤ k := by
  classical
  constructor
  · rintro ⟨hweak, hstrict⟩
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro σ i
        exact hweak.1 (σ, i)
      · intro i s t
        cases hc : br.targetCertificate i s t with
        | weakFailure σ =>
            have hrow := hstrict (Sum.inl ⟨i, s, t⟩)
            have hlin :
                G.eu (Function.update σ i t) i - G.eu (Function.update σ i s.1) i <
                  x (Function.update σ i s.1, i) -
                    x (Function.update σ i t, i) := by
              rw [rowEval_strictA_target_weakFailure br x i s t σ hc] at hrow
              simpa [strictB.eq_def, hc] using hrow
            dsimp [TargetNonDominationCertificate.RealizedBy]
            simp [vectorTransfer]
            linarith
        | noStrict =>
            dsimp [TargetNonDominationCertificate.RealizedBy]
            intro σ
            have hrow := hweak.2 (Sum.inl ⟨i, s, t, σ⟩)
            have hlin :
                G.eu (Function.update σ i t) i - G.eu (Function.update σ i s.1) i ≤
                  x (Function.update σ i s.1, i) -
                    x (Function.update σ i t, i) := by
              rw [rowEval_weakA_target_noStrict br x i s t σ hc] at hrow
              simpa [weakB.eq_def, hc] using hrow
            simp [vectorTransfer]
            linarith
      · constructor
        · intro i s σ
          have hrow := hweak.2 (Sum.inr (Sum.inl ⟨i, s, σ⟩))
          have hlin :
              G.eu (Function.update σ i s.1) i -
                  G.eu (Function.update σ i (sk.excludedDominator i s)) i ≤
                x (Function.update σ i (sk.excludedDominator i s), i) -
                  x (Function.update σ i s.1, i) := by
            rw [weakB.eq_def, rowEval_weakA_excluded br x i s σ] at hrow
            simpa using hrow
          simp [vectorTransfer]
          linarith
        · intro i s
          have hrow := hstrict (Sum.inr ⟨i, s⟩)
          have hlin :
              G.eu (Function.update (br.excludedStrictWitness i s) i s.1) i -
                  G.eu
                    (Function.update (br.excludedStrictWitness i s) i
                      (sk.excludedDominator i s)) i <
                x (Function.update (br.excludedStrictWitness i s) i
                    (sk.excludedDominator i s), i) -
                  x (Function.update (br.excludedStrictWitness i s) i s.1, i) := by
            rw [rowEval_strictA_excluded br x i s] at hrow
            simpa [strictB.eq_def] using hrow
          simp [vectorTransfer]
          linarith
    · intro σ hσ
      have hrow := hweak.2 (Sum.inr (Sum.inr ⟨σ, hσ⟩))
      have hlin : -k ≤ -∑ i : ι, x (σ, i) := by
        rw [rowEval_weakA_cost br x ⟨σ, hσ⟩] at hrow
        simpa [weakB.eq_def] using hrow
      simp [vectorTransfer]
      linarith
  · rintro ⟨hbr, hcost⟩
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro q
        exact hbr.nonneg q.1 q.2
      · intro row
        cases row with
        | inl targetRow =>
            rcases targetRow with ⟨i, s, t, σ⟩
            cases hc : br.targetCertificate i s t with
            | weakFailure σw =>
                simp [weakA.eq_def, weakB.eq_def, hc, rowEval]
            | noStrict =>
                have hreal := hbr.2.1 i s t
                rw [hc] at hreal
                have hineq := hreal σ
                have hlin :
                    G.eu (Function.update σ i t) i - G.eu (Function.update σ i s.1) i ≤
                      x (Function.update σ i s.1, i) -
                        x (Function.update σ i t, i) := by
                  dsimp [TargetNonDominationCertificate.RealizedBy] at hineq
                  simp [vectorTransfer] at hineq
                  linarith
                rw [rowEval_weakA_target_noStrict br x i s t σ hc]
                simpa [weakB.eq_def, hc] using hlin
        | inr rest =>
            cases rest with
            | inl excludedRow =>
                rcases excludedRow with ⟨i, s, σ⟩
                have hineq := hbr.2.2.1 i s σ
                have hlin :
                    G.eu (Function.update σ i s.1) i -
                        G.eu (Function.update σ i (sk.excludedDominator i s)) i ≤
                      x (Function.update σ i (sk.excludedDominator i s), i) -
                        x (Function.update σ i s.1, i) := by
                  simp [vectorTransfer] at hineq
                  linarith
                rw [rowEval_weakA_excluded br x i s σ]
                simpa [weakB.eq_def] using hlin
            | inr σ =>
                have hk := hcost σ.1 σ.2
                have hlin : -k ≤ -∑ i : ι, x (σ.1, i) := by
                  simp [vectorTransfer] at hk
                  linarith
                rw [rowEval_weakA_cost br x σ]
                simpa [weakB.eq_def] using hlin
    · intro row
      cases row with
      | inl targetRow =>
          rcases targetRow with ⟨i, s, t⟩
          cases hc : br.targetCertificate i s t with
          | weakFailure σ =>
              have hreal := hbr.2.1 i s t
              rw [hc] at hreal
              have hlin :
                  G.eu (Function.update σ i t) i - G.eu (Function.update σ i s.1) i <
                    x (Function.update σ i s.1, i) -
                      x (Function.update σ i t, i) := by
                dsimp [TargetNonDominationCertificate.RealizedBy] at hreal
                simp [vectorTransfer] at hreal
                linarith
              rw [rowEval_strictA_target_weakFailure br x i s t σ hc]
              simpa [strictB.eq_def, hc] using hlin
          | noStrict =>
              simp [strictA.eq_def, strictB.eq_def, hc, rowEval]
      | inr excludedRow =>
          rcases excludedRow with ⟨i, s⟩
          have hineq := hbr.2.2.2 i s
          have hlin :
              G.eu (Function.update (br.excludedStrictWitness i s) i s.1) i -
                  G.eu
                    (Function.update (br.excludedStrictWitness i s) i
                      (sk.excludedDominator i s)) i <
                x (Function.update (br.excludedStrictWitness i s) i
                    (sk.excludedDominator i s), i) -
                  x (Function.update (br.excludedStrictWitness i s) i s.1, i) := by
            simp [vectorTransfer] at hineq
            linarith
          rw [rowEval_strictA_excluded br x i s]
          simpa [strictB.eq_def] using hlin

end Matrix

end BranchCertificate

theorem RealizedBy.nonneg {G : KernelGame ι} {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {V : Profile G → Payoff ι}
    (h : sk.RealizedBy V) :
    ∀ σ i, 0 ≤ V σ i :=
  h.1

theorem RealizedBy.target_undominated {G : KernelGame ι}
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {V : Profile G → Payoff ι}
    (h : sk.RealizedBy V) {i : ι} {s : G.Strategy i}
    (hs : s ∈ S i) :
    (G.subsidize V).IsUndominated i s :=
  h.2.1 i s hs

theorem RealizedBy.excluded_dominated {G : KernelGame ι}
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {V : Profile G → Payoff ι}
    (h : sk.RealizedBy V) (i : ι)
    (s : {s : G.Strategy i // s ∉ S i}) :
    (G.subsidize V).WeaklyStrictlyDominates i
      (sk.excludedDominator i s) s.1 :=
  h.2.2 i s

/-- Every semantic realization of a dominance skeleton has an explicit branch
certificate.  This is the finite-search layer behind the skeleton statement:
the remaining constraints are payoff inequalities once the branches are fixed.
-/
theorem RealizedBy.exists_branchCertificate {G : KernelGame ι}
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {V : Profile G → Payoff ι}
    (h : sk.RealizedBy V) :
    ∃ br : sk.BranchCertificate, br.RealizedBy V := by
  classical
  have htarget :
      ∀ i (s : {s : G.Strategy i // s ∈ S i}) (t : G.Strategy i),
        ∃ c : TargetNonDominationCertificate i s.1 t, c.RealizedBy V := by
    intro i s t
    have hnot : ¬ (G.subsidize V).WeaklyStrictlyDominates i t s.1 :=
      h.target_undominated s.2 t
    by_cases hweak : (G.subsidize V).WeaklyDominates i t s.1
    · refine ⟨TargetNonDominationCertificate.noStrict, ?_⟩
      intro σ
      by_contra hlt
      have hstrict :
          (G.subsidize V).eu (Function.update σ i t) i >
            (G.subsidize V).eu (Function.update σ i s.1) i :=
        lt_of_not_ge hlt
      exact hnot ⟨hweak, ⟨σ, hstrict⟩⟩
    · unfold WeaklyDominates at hweak
      rw [not_forall] at hweak
      obtain ⟨σ, hσ⟩ := hweak
      refine ⟨TargetNonDominationCertificate.weakFailure σ, ?_⟩
      exact lt_of_not_ge hσ
  have hstrict :
      ∀ i (s : {s : G.Strategy i // s ∉ S i}),
        ∃ σ : Profile G,
          (G.subsidize V).eu
              (Function.update σ i (sk.excludedDominator i s)) i >
            (G.subsidize V).eu (Function.update σ i s.1) i := by
    intro i s
    exact (h.excluded_dominated i s).strict_witness
  choose targetCertificate htarget_realized using htarget
  choose excludedStrictWitness hstrict_realized using hstrict
  let br : sk.BranchCertificate :=
    { excludedStrictWitness := excludedStrictWitness
      targetCertificate := targetCertificate }
  refine ⟨br, ?_⟩
  refine ⟨h.nonneg, ?_, ?_⟩
  · exact htarget_realized
  · constructor
    · intro i s σ
      exact (h.excluded_dominated i s).toWeaklyDominates σ
    · exact hstrict_realized

theorem realizedBy_iff_exists_branchCertificate {G : KernelGame ι}
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {V : Profile G → Payoff ι} :
    sk.RealizedBy V ↔ ∃ br : sk.BranchCertificate, br.RealizedBy V :=
  ⟨RealizedBy.exists_branchCertificate,
    fun h => by
      rcases h with ⟨br, hbr⟩
      exact hbr.to_realizedBy⟩

/-- A realized skeleton gives the desired coordinatewise undominated sets. -/
theorem RealizedBy.isUndominated_iff {G : KernelGame ι}
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {V : Profile G → Payoff ι}
    (h : sk.RealizedBy V) (i : ι) (s : G.Strategy i) :
    (G.subsidize V).IsUndominated i s ↔ s ∈ S i := by
  constructor
  · intro hs
    by_contra hsS
    exact hs (sk.excludedDominator i ⟨s, hsS⟩)
      (h.excluded_dominated i ⟨s, hsS⟩)
  · intro hsS
    exact h.target_undominated hsS

/-- A realized skeleton gives exactly the target rectangle as the undominated
profile set. -/
theorem RealizedBy.undominatedProfiles_eq_rect {G : KernelGame ι}
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {V : Profile G → Payoff ι}
    (h : sk.RealizedBy V) :
    (G.subsidize V).undominatedProfiles = G.rect S := by
  ext σ
  constructor
  · intro hσ i
    exact (h.isUndominated_iff i (σ i)).mp (hσ i)
  · intro hσ i
    exact (h.isUndominated_iff i (σ i)).mpr (hσ i)

theorem RealizedBy.isExactImplementation_rect {G : KernelGame ι}
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {V : Profile G → Payoff ι}
    (h : sk.RealizedBy V) :
    G.IsExactImplementation V (G.rect S) :=
  ⟨h.nonneg, h.undominatedProfiles_eq_rect⟩

theorem RealizedBy.isExactKImplementation_rect {G : KernelGame ι} [Fintype ι]
    {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {V : Profile G → Payoff ι} {k : ℝ}
    (h : sk.RealizedBy V)
    (hcost : ∀ σ : Profile G, σ ∈ G.rect S → (∑ i, V σ i) ≤ k) :
    G.IsExactKImplementation V (G.rect S) k :=
  ⟨h.isExactImplementation_rect, hcost⟩

end ExactDominanceSkeleton

namespace IsExactImplementation

/-- For a nonempty rectangle, exact implementation is equivalent to realizing
some dominance skeleton. -/
theorem exists_exactDominanceSkeleton_realized_rect {G : KernelGame ι}
    {S : ∀ i, Set (G.Strategy i)} {V : Profile G → Payoff ι}
    (h : G.IsExactImplementation V (G.rect S)) (hS : (G.rect S).Nonempty) :
    ∃ sk : G.ExactDominanceSkeleton S, sk.RealizedBy V := by
  classical
  have hundom_iff :
      ∀ i (s : G.Strategy i), (G.subsidize V).IsUndominated i s ↔ s ∈ S i := by
    intro i s
    constructor
    · intro hs
      obtain ⟨τ, hτS⟩ := hS
      let σ : Profile G := Function.update τ i s
      have hσundom : σ ∈ (G.subsidize V).undominatedProfiles := by
        intro j
        by_cases hji : j = i
        · subst hji
          simpa [σ]
        · have hτundom : τ ∈ (G.subsidize V).undominatedProfiles := by
            rw [h.undominatedProfiles_eq]
            exact hτS
          simpa [σ, Function.update_of_ne hji] using hτundom j
      have hσS : σ ∈ G.rect S := by
        rw [← h.undominatedProfiles_eq]
        exact hσundom
      simpa [σ] using hσS i
    · intro hsS
      obtain ⟨τ, hτS⟩ := hS
      let σ : Profile G := Function.update τ i s
      have hσS : σ ∈ G.rect S := by
        intro j
        by_cases hji : j = i
        · subst hji
          simpa [σ] using hsS
        · simpa [σ, Function.update_of_ne hji] using hτS j
      have hσundom : σ ∈ (G.subsidize V).undominatedProfiles := by
        rw [h.undominatedProfiles_eq]
        exact hσS
      simpa [σ] using hσundom i
  have hdominated :
      ∀ i (s : {s : G.Strategy i // s ∉ S i}),
        ∃ t : G.Strategy i,
          (G.subsidize V).WeaklyStrictlyDominates i t s.1 := by
    intro i s
    have hnot : ¬ (G.subsidize V).IsUndominated i s.1 := by
      intro hs
      exact s.2 ((hundom_iff i s.1).mp hs)
    unfold IsUndominated at hnot
    push Not at hnot
    exact hnot
  let sk : G.ExactDominanceSkeleton S :=
    { excludedDominator := fun i s => Classical.choose (hdominated i s) }
  refine ⟨sk, ?_⟩
  refine ⟨h.nonneg, ?_, ?_⟩
  · intro i s hsS
    exact (hundom_iff i s).mpr hsS
  · intro i s
    exact Classical.choose_spec (hdominated i s)

end IsExactImplementation

/-- Costs certified by a dominance skeleton for the exact rectangular target. -/
def skeletonExactImplementationCosts (G : KernelGame ι) [Fintype ι]
    (S : ∀ i, Set (G.Strategy i)) : Set ℝ :=
  {k | ∃ (sk : G.ExactDominanceSkeleton S) (V : Profile G → Payoff ι),
    sk.RealizedBy V ∧
      ∀ σ : Profile G, σ ∈ G.rect S → (∑ i, V σ i) ≤ k}

/-- Costs certified by an explicit branch expansion of a dominance skeleton. -/
def branchSkeletonExactImplementationCosts (G : KernelGame ι) [Fintype ι]
    (S : ∀ i, Set (G.Strategy i)) : Set ℝ :=
  {k | ∃ (sk : G.ExactDominanceSkeleton S) (br : sk.BranchCertificate)
      (V : Profile G → Payoff ι),
    br.RealizedBy V ∧
      ∀ σ : Profile G, σ ∈ G.rect S → (∑ i, V σ i) ≤ k}

/-- Costs certified by the finite matrix system of some branch expansion.
This is the linear-algebraic surface of rectangular exact implementation:
closed rows are standard-form LP constraints and strict rows remain open
witness inequalities. -/
noncomputable def branchMatrixExactImplementationCosts (G : KernelGame ι)
    [Fintype ι] [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)]
    (S : ∀ i, Set (G.Strategy i)) : Set ℝ := by
  classical
  exact {k | ∃ (sk : G.ExactDominanceSkeleton S) (br : sk.BranchCertificate)
      (x : G.PaymentVar → ℝ),
    ExactDominanceSkeleton.BranchCertificate.Matrix.Feasible br k x}

/-- Exact branch costs through a standard-form LP with an explicit budget
variable.  The LP objective is the budget coordinate; open strict-witness rows
remain outside the closed standard-form constraints. -/
noncomputable def branchBudgetLPExactImplementationCosts (G : KernelGame ι)
    [Fintype ι] [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)]
    (S : ∀ i, Set (G.Strategy i)) : Set ℝ := by
  classical
  exact {k | ∃ (sk : G.ExactDominanceSkeleton S) (br : sk.BranchCertificate)
      (x : G.BudgetPaymentVar → ℝ),
    ExactDominanceSkeleton.BranchCertificate.Matrix.BudgetFeasible br x ∧
      Math.LinearProgramming.minPrimalValue
        ExactDominanceSkeleton.BranchCertificate.Matrix.budgetC x ≤ k}

theorem branchSkeletonExactImplementationCosts_eq_skeletonExactImplementationCosts
    (G : KernelGame ι) [Fintype ι] (S : ∀ i, Set (G.Strategy i)) :
    G.branchSkeletonExactImplementationCosts S =
      G.skeletonExactImplementationCosts S := by
  ext k
  constructor
  · rintro ⟨sk, br, V, hbr, hcost⟩
    exact ⟨sk, V, hbr.to_realizedBy, hcost⟩
  · rintro ⟨sk, V, hsk, hcost⟩
    rcases hsk.exists_branchCertificate with ⟨br, hbr⟩
    exact ⟨sk, br, V, hbr, hcost⟩

/-- The union of the fixed-branch matrix systems is exactly the
branch-certificate exact-cost set. -/
theorem branchMatrixExactImplementationCosts_eq_branchSkeletonExactImplementationCosts
    (G : KernelGame ι) [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    [Fintype (Profile G)] [Finite G.Outcome]
    (S : ∀ i, Set (G.Strategy i)) :
    G.branchMatrixExactImplementationCosts S =
      G.branchSkeletonExactImplementationCosts S := by
  classical
  ext k
  constructor
  · rintro ⟨sk, br, x, hx⟩
    exact open ExactDominanceSkeleton.BranchCertificate.Matrix in
      ⟨sk, br, G.vectorTransfer x,
        (feasible_iff_realizedBy_vectorTransfer_and_cost br).mp hx⟩
  · rintro ⟨sk, br, V, hbr, hcost⟩
    let x : G.PaymentVar → ℝ := fun q => V q.1 q.2
    have hxV : G.vectorTransfer x = V := by
      ext σ i
      rfl
    have hreal : br.RealizedBy (G.vectorTransfer x) := by
      rw [hxV]
      exact hbr
    have hbudget :
        ∀ σ : Profile G, σ ∈ G.rect S →
          (∑ i, G.vectorTransfer x σ i) ≤ k := by
      intro σ hσ
      rw [hxV]
      exact hcost σ hσ
    exact open ExactDominanceSkeleton.BranchCertificate.Matrix in
      ⟨sk, br, x,
        (feasible_iff_realizedBy_vectorTransfer_and_cost br).mpr ⟨hreal, hbudget⟩⟩

/-- For a nonempty rectangle, the explicit-budget LP surface is equivalent to
the parameterized branch-matrix cost set. -/
theorem branchBudgetLPExactImplementationCosts_eq_branchMatrixExactImplementationCosts
    (G : KernelGame ι) [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    [Fintype (Profile G)] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty) :
    G.branchBudgetLPExactImplementationCosts S =
      G.branchMatrixExactImplementationCosts S := by
  classical
  ext k
  constructor
  · rintro ⟨sk, br, x, hx, hxk⟩
    have hfeas :
        ExactDominanceSkeleton.BranchCertificate.Matrix.Feasible br
          (G.budgetOfVector x) (G.paymentOfBudgetVector x) :=
      hx.to_feasible
    have hbudget : G.budgetOfVector x ≤ k := by
      simpa [ExactDominanceSkeleton.BranchCertificate.Matrix.minPrimalValue_budgetC]
        using hxk
    exact ⟨sk, br, G.paymentOfBudgetVector x, hfeas.mono_budget hbudget⟩
  · rintro ⟨sk, br, x, hx⟩
    obtain ⟨z, hz, hzbudget, _hzpay⟩ := hx.exists_budgetFeasible hS
    refine ⟨sk, br, z, hz, ?_⟩
    simp [ExactDominanceSkeleton.BranchCertificate.Matrix.minPrimalValue_budgetC,
      hzbudget]

/-- Exact costs for a nonempty rectangle are exactly the costs certified by
some dominance skeleton. -/
theorem skeletonExactImplementationCosts_eq_exactImplementationCosts_rect
    (G : KernelGame ι) [Fintype ι] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty) :
    G.skeletonExactImplementationCosts S =
      G.exactImplementationCosts (G.rect S) := by
  ext k
  constructor
  · rintro ⟨sk, V, hsk, hcost⟩
    exact ⟨V, hsk.isExactKImplementation_rect hcost⟩
  · rintro ⟨V, hV⟩
    rcases hV.exactImplementation.exists_exactDominanceSkeleton_realized_rect hS
      with ⟨sk, hsk⟩
    exact ⟨sk, V, hsk, hV.cost_bound⟩

/-- Exact costs for a nonempty rectangle are exactly the costs certified by
some explicit branch expansion of a dominance skeleton. -/
theorem branchSkeletonExactImplementationCosts_eq_exactImplementationCosts_rect
    (G : KernelGame ι) [Fintype ι] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty) :
    G.branchSkeletonExactImplementationCosts S =
      G.exactImplementationCosts (G.rect S) := by
  rw [G.branchSkeletonExactImplementationCosts_eq_skeletonExactImplementationCosts S,
    G.skeletonExactImplementationCosts_eq_exactImplementationCosts_rect hS]

/-- Matrix-certified exact costs coincide with ordinary exact costs for
nonempty rectangles in finite games. -/
theorem branchMatrixExactImplementationCosts_eq_exactImplementationCosts_rect
    (G : KernelGame ι) [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    [Fintype (Profile G)] [Finite G.Outcome] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty) :
    G.branchMatrixExactImplementationCosts S =
      G.exactImplementationCosts (G.rect S) := by
  rw [G.branchMatrixExactImplementationCosts_eq_branchSkeletonExactImplementationCosts S,
    G.branchSkeletonExactImplementationCosts_eq_exactImplementationCosts_rect hS]

/-- Exact costs for a nonempty rectangle are also the union of the explicit
budget-LP branch systems. -/
theorem branchBudgetLPExactImplementationCosts_eq_exactImplementationCosts_rect
    (G : KernelGame ι) [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    [Fintype (Profile G)] [Finite G.Outcome] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty) :
    G.branchBudgetLPExactImplementationCosts S =
      G.exactImplementationCosts (G.rect S) := by
  rw [G.branchBudgetLPExactImplementationCosts_eq_branchMatrixExactImplementationCosts hS,
    G.branchMatrixExactImplementationCosts_eq_exactImplementationCosts_rect hS]

/-- Skeleton-certified exact costs are upward closed. -/
theorem skeletonExactImplementationCosts_upward_closed
    {G : KernelGame ι} [Fintype ι] {S : ∀ i, Set (G.Strategy i)} {k l : ℝ}
    (hk : k ∈ G.skeletonExactImplementationCosts S) (hkl : k ≤ l) :
    l ∈ G.skeletonExactImplementationCosts S := by
  rcases hk with ⟨sk, V, hsk, hcost⟩
  exact ⟨sk, V, hsk, fun σ hσ => (hcost σ hσ).trans hkl⟩

/-- Branch-certified exact costs are upward closed. -/
theorem branchSkeletonExactImplementationCosts_upward_closed
    {G : KernelGame ι} [Fintype ι] {S : ∀ i, Set (G.Strategy i)} {k l : ℝ}
    (hk : k ∈ G.branchSkeletonExactImplementationCosts S) (hkl : k ≤ l) :
    l ∈ G.branchSkeletonExactImplementationCosts S := by
  rcases hk with ⟨sk, br, V, hbr, hcost⟩
  exact ⟨sk, br, V, hbr, fun σ hσ => (hcost σ hσ).trans hkl⟩

/-- Matrix-certified exact costs are upward closed. -/
theorem branchMatrixExactImplementationCosts_upward_closed
    {G : KernelGame ι} [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    [Fintype (Profile G)] {S : ∀ i, Set (G.Strategy i)} {k l : ℝ}
    (hk : k ∈ G.branchMatrixExactImplementationCosts S) (hkl : k ≤ l) :
    l ∈ G.branchMatrixExactImplementationCosts S := by
  classical
  rcases hk with ⟨sk, br, x, hx⟩
  exact ⟨sk, br, x, hx.mono_budget hkl⟩

/-- Explicit-budget-LP exact costs are upward closed. -/
theorem branchBudgetLPExactImplementationCosts_upward_closed
    {G : KernelGame ι} [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    [Fintype (Profile G)] {S : ∀ i, Set (G.Strategy i)} {k l : ℝ}
    (hk : k ∈ G.branchBudgetLPExactImplementationCosts S) (hkl : k ≤ l) :
    l ∈ G.branchBudgetLPExactImplementationCosts S := by
  rcases hk with ⟨sk, br, x, hx, hxk⟩
  exact ⟨sk, br, x, hx, hxk.trans hkl⟩

/-- Infimum over dominance-skeleton costs. -/
noncomputable def skeletonExactImplPrice (G : KernelGame ι) [Fintype ι]
    (S : ∀ i, Set (G.Strategy i)) : ℝ :=
  sInf (G.skeletonExactImplementationCosts S)

/-- Infimum over branch-expanded dominance-skeleton costs. -/
noncomputable def branchSkeletonExactImplPrice (G : KernelGame ι) [Fintype ι]
    (S : ∀ i, Set (G.Strategy i)) : ℝ :=
  sInf (G.branchSkeletonExactImplementationCosts S)

/-- Infimum over matrix-certified branch costs. -/
noncomputable def branchMatrixExactImplPrice (G : KernelGame ι) [Fintype ι]
    [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)]
    (S : ∀ i, Set (G.Strategy i)) : ℝ :=
  sInf (G.branchMatrixExactImplementationCosts S)

/-- Infimum over explicit-budget LP branch costs. -/
noncomputable def branchBudgetLPExactImplPrice (G : KernelGame ι) [Fintype ι]
    [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)]
    (S : ∀ i, Set (G.Strategy i)) : ℝ :=
  sInf (G.branchBudgetLPExactImplementationCosts S)

theorem branchSkeletonExactImplPrice_eq_skeletonExactImplPrice
    (G : KernelGame ι) [Fintype ι] (S : ∀ i, Set (G.Strategy i)) :
    G.branchSkeletonExactImplPrice S = G.skeletonExactImplPrice S := by
  rw [branchSkeletonExactImplPrice, skeletonExactImplPrice,
    G.branchSkeletonExactImplementationCosts_eq_skeletonExactImplementationCosts S]

theorem branchMatrixExactImplPrice_eq_branchSkeletonExactImplPrice
    (G : KernelGame ι) [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    [Fintype (Profile G)] [Finite G.Outcome] (S : ∀ i, Set (G.Strategy i)) :
    G.branchMatrixExactImplPrice S = G.branchSkeletonExactImplPrice S := by
  rw [branchMatrixExactImplPrice, branchSkeletonExactImplPrice,
    G.branchMatrixExactImplementationCosts_eq_branchSkeletonExactImplementationCosts S]

theorem branchBudgetLPExactImplPrice_eq_branchMatrixExactImplPrice
    (G : KernelGame ι) [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    [Fintype (Profile G)] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty) :
    G.branchBudgetLPExactImplPrice S = G.branchMatrixExactImplPrice S := by
  rw [branchBudgetLPExactImplPrice, branchMatrixExactImplPrice,
    G.branchBudgetLPExactImplementationCosts_eq_branchMatrixExactImplementationCosts hS]

theorem skeletonExactImplPrice_eq_exactImplPrice_rect
    (G : KernelGame ι) [Fintype ι] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty) :
    G.skeletonExactImplPrice S = G.exactImplPrice (G.rect S) := by
  rw [skeletonExactImplPrice, exactImplPrice,
    G.skeletonExactImplementationCosts_eq_exactImplementationCosts_rect hS]

theorem branchSkeletonExactImplPrice_eq_exactImplPrice_rect
    (G : KernelGame ι) [Fintype ι] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty) :
    G.branchSkeletonExactImplPrice S = G.exactImplPrice (G.rect S) := by
  rw [G.branchSkeletonExactImplPrice_eq_skeletonExactImplPrice S,
    G.skeletonExactImplPrice_eq_exactImplPrice_rect hS]

theorem branchMatrixExactImplPrice_eq_exactImplPrice_rect
    (G : KernelGame ι) [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    [Fintype (Profile G)] [Finite G.Outcome] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty) :
    G.branchMatrixExactImplPrice S = G.exactImplPrice (G.rect S) := by
  rw [G.branchMatrixExactImplPrice_eq_branchSkeletonExactImplPrice S,
    G.branchSkeletonExactImplPrice_eq_exactImplPrice_rect hS]

theorem branchBudgetLPExactImplPrice_eq_exactImplPrice_rect
    (G : KernelGame ι) [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    [Fintype (Profile G)] [Finite G.Outcome] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty) :
    G.branchBudgetLPExactImplPrice S = G.exactImplPrice (G.rect S) := by
  rw [G.branchBudgetLPExactImplPrice_eq_branchMatrixExactImplPrice hS,
    G.branchMatrixExactImplPrice_eq_exactImplPrice_rect hS]

/-- If the skeleton infimum is feasible, skeleton-certified costs are exactly
the ray above the skeleton price. -/
theorem skeletonExactImplementationCosts_eq_Ici_skeletonExactImplPrice_of_mem
    (G : KernelGame ι) [Fintype ι] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty)
    (hmem : G.skeletonExactImplPrice S ∈ G.skeletonExactImplementationCosts S) :
    G.skeletonExactImplementationCosts S = Set.Ici (G.skeletonExactImplPrice S) := by
  have hmemExact :
      G.exactImplPrice (G.rect S) ∈ G.exactImplementationCosts (G.rect S) := by
    rw [← G.skeletonExactImplPrice_eq_exactImplPrice_rect hS,
      ← G.skeletonExactImplementationCosts_eq_exactImplementationCosts_rect hS]
    exact hmem
  rw [G.skeletonExactImplementationCosts_eq_exactImplementationCosts_rect hS,
    G.skeletonExactImplPrice_eq_exactImplPrice_rect hS,
    G.exactImplementationCosts_eq_Ici_exactImplPrice_of_mem hS hmemExact]

/-- If the branch infimum is feasible, branch-certified costs are exactly the
ray above the branch price. -/
theorem branchSkeletonExactImplementationCosts_eq_Ici_branchSkeletonExactImplPrice_of_mem
    (G : KernelGame ι) [Fintype ι] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty)
    (hmem :
      G.branchSkeletonExactImplPrice S ∈ G.branchSkeletonExactImplementationCosts S) :
    G.branchSkeletonExactImplementationCosts S =
      Set.Ici (G.branchSkeletonExactImplPrice S) := by
  have hmemExact :
      G.exactImplPrice (G.rect S) ∈ G.exactImplementationCosts (G.rect S) := by
    rw [← G.branchSkeletonExactImplPrice_eq_exactImplPrice_rect hS,
      ← G.branchSkeletonExactImplementationCosts_eq_exactImplementationCosts_rect hS]
    exact hmem
  rw [G.branchSkeletonExactImplementationCosts_eq_exactImplementationCosts_rect hS,
    G.branchSkeletonExactImplPrice_eq_exactImplPrice_rect hS,
    G.exactImplementationCosts_eq_Ici_exactImplPrice_of_mem hS hmemExact]

/-- If the matrix infimum is feasible, matrix-certified costs are exactly the
ray above the matrix price.  This isolates the boundary question: proving
attainment is precisely proving membership of the infimum in the matrix cost
set. -/
theorem branchMatrixExactImplementationCosts_eq_Ici_branchMatrixExactImplPrice_of_mem
    (G : KernelGame ι) [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    [Fintype (Profile G)] [Finite G.Outcome] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty)
    (hmem : G.branchMatrixExactImplPrice S ∈ G.branchMatrixExactImplementationCosts S) :
    G.branchMatrixExactImplementationCosts S = Set.Ici (G.branchMatrixExactImplPrice S) := by
  have hmemExact :
      G.exactImplPrice (G.rect S) ∈ G.exactImplementationCosts (G.rect S) := by
    rw [← G.branchMatrixExactImplPrice_eq_exactImplPrice_rect hS,
      ← G.branchMatrixExactImplementationCosts_eq_exactImplementationCosts_rect hS]
    exact hmem
  rw [G.branchMatrixExactImplementationCosts_eq_exactImplementationCosts_rect hS,
    G.branchMatrixExactImplPrice_eq_exactImplPrice_rect hS,
    G.exactImplementationCosts_eq_Ici_exactImplPrice_of_mem hS hmemExact]

/-- If the explicit-budget LP infimum is feasible, budget-LP-certified costs
are exactly the ray above the budget-LP price. -/
theorem branchBudgetLPExactImplementationCosts_eq_Ici_branchBudgetLPExactImplPrice_of_mem
    (G : KernelGame ι) [Fintype ι] [∀ i, Fintype (G.Strategy i)]
    [Fintype (Profile G)] [Finite G.Outcome] {S : ∀ i, Set (G.Strategy i)}
    (hS : (G.rect S).Nonempty)
    (hmem :
      G.branchBudgetLPExactImplPrice S ∈ G.branchBudgetLPExactImplementationCosts S) :
    G.branchBudgetLPExactImplementationCosts S =
      Set.Ici (G.branchBudgetLPExactImplPrice S) := by
  have hmemExact :
      G.exactImplPrice (G.rect S) ∈ G.exactImplementationCosts (G.rect S) := by
    rw [← G.branchBudgetLPExactImplPrice_eq_exactImplPrice_rect hS,
      ← G.branchBudgetLPExactImplementationCosts_eq_exactImplementationCosts_rect hS]
    exact hmem
  rw [G.branchBudgetLPExactImplementationCosts_eq_exactImplementationCosts_rect hS,
    G.branchBudgetLPExactImplPrice_eq_exactImplPrice_rect hS,
    G.exactImplementationCosts_eq_Ici_exactImplPrice_of_mem hS hmemExact]

end KernelGame

end GameTheory
