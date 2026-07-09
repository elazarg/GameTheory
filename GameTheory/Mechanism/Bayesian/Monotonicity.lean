/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.Probability

/-!
# Weak monotonicity and dominant-strategy implementability

The monotonicity characterization of truthful (dominant-strategy incentive
compatible) mechanisms in quasilinear domains. A truthful mechanism's allocation
rule must be **weakly monotone** (Bikhchandani–Chatterji–Lavi–Mu'alem–Nisan–Sen,
*Econometrica* 2006; Monderer). This is the multi-dimensional analogue of Myerson's
monotonicity and the necessary half of the implementability characterization.

Unlike `Mechanism` (which is payoff-only), this layer exposes the **chosen
alternative**, so monotonicity of the *allocation rule* can be stated.

## Main definitions

* `SCFWithPayments` — a deterministic social choice function with quasilinear payments
* `SCFWithPayments.IsDSIC` — dominant-strategy incentive compatibility
* `SCFWithPayments.IsWeaklyMonotone` — weak monotonicity of the allocation rule

## Main result

* `SCFWithPayments.weaklyMonotone_of_dsic` — DSIC ⇒ weak monotonicity (necessity)

The converse (weak monotonicity ⇒ DSIC-implementable on convex domains) is the
harder, domain-dependent direction and is not formalized here.
-/

namespace GameTheory

variable {ι Alt : Type} [DecidableEq ι]

/-- A deterministic social choice function with quasilinear payments: agents report
types, the rule picks an `Alt`ernative and charges each agent a payment, and agent
`i`'s value for an alternative depends on its reported type. -/
structure SCFWithPayments (ι Alt : Type) where
  /-- Type (private valuation parameter) space for each agent. -/
  Θ : ι → Type
  /-- Agent `i`'s value for an alternative, as a function of its type. -/
  value : (i : ι) → Θ i → Alt → ℝ
  /-- The chosen alternative as a function of reports. -/
  choice : (∀ i, Θ i) → Alt
  /-- The payment charged to each agent as a function of reports. -/
  payment : (∀ i, Θ i) → ι → ℝ

namespace SCFWithPayments

variable (M : SCFWithPayments ι Alt)

/-- Agent `i`'s quasilinear utility (true type `θᵢ`) from a report profile:
value of the chosen alternative minus the payment. -/
def utility (report : ∀ i, M.Θ i) (i : ι) (θᵢ : M.Θ i) : ℝ :=
  M.value i θᵢ (M.choice report) - M.payment report i

/-- **Dominant-strategy incentive compatibility (DSIC).** For every agent, truthful
reporting weakly maximizes quasilinear utility, regardless of others' reports. -/
def IsDSIC : Prop :=
  ∀ (i : ι) (θ : ∀ j, M.Θ j) (θ'ᵢ : M.Θ i),
    M.utility θ i (θ i) ≥ M.utility (Function.update θ i θ'ᵢ) i (θ i)

/-- **Weak monotonicity** of the allocation rule: holding others' reports fixed,
agent `i`'s value gain from the alternative chosen at `θᵢ` over the one chosen at
`θ'ᵢ` is larger under type `θᵢ` than under type `θ'ᵢ`. -/
def IsWeaklyMonotone : Prop :=
  ∀ (i : ι) (θ : ∀ j, M.Θ j) (θ'ᵢ : M.Θ i),
    M.value i (θ i) (M.choice θ) - M.value i (θ i) (M.choice (Function.update θ i θ'ᵢ)) ≥
      M.value i θ'ᵢ (M.choice θ) - M.value i θ'ᵢ (M.choice (Function.update θ i θ'ᵢ))

/-- **Weak monotonicity is necessary for truthfulness.** Every DSIC mechanism has a
weakly monotone allocation rule: the payments cancel when the two relevant incentive
constraints (`i` of type `θᵢ` not wanting to report `θ'ᵢ`, and `i` of type `θ'ᵢ` not
wanting to report `θᵢ`) are added. -/
theorem weaklyMonotone_of_dsic (h : M.IsDSIC) : M.IsWeaklyMonotone := by
  intro i θ θ'ᵢ
  have I := h i θ θ'ᵢ
  have II := h i (Function.update θ i θ'ᵢ) (θ i)
  simp only [utility, Function.update_self, Function.update_idem,
    Function.update_eq_self] at I II
  linarith [I, II]

end SCFWithPayments

end GameTheory
