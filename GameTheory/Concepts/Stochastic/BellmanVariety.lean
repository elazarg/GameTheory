/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Fink
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# The Bellman Variety: A Polynomial Presentation of Discounted Stationary Equilibria

This file gives an explicit finite polynomial presentation of the discounted
stationary Bellman equilibrium conditions `IsDiscountedStationaryBellmanEq`
from `GameTheory.Concepts.Stochastic.Fink`.  It is the "W1" layer of the
uniform-equilibrium roadmap: a bridge from the probabilistic formulation of
Fink's theorem to real-algebraic geometry.

## The variables

`BellmanVar G` collects three kinds of real unknowns:

* `mix s i a` — the mixing probability that player `i` plays action `a` at
  state `s`;
* `val s i` — the continuation value of player `i` at state `s`;
* `disc` — a single discount-complement unknown `λ`, meant to be bound to
  `1 - β`.

## The polynomials

For every `(s, i)` we write down:

* `simplexSumPoly s i`, `simplexNonnegPoly s i a` — the simplex constraints
  `Σ_a x_{s,i,a} = 1` and `x_{s,i,a} ≥ 0` cutting out valid mixed actions;
* `bellmanPoly s i` — the Bellman value-consistency equation.  With `λ`
  bound to `1 - β`, Fink's auxiliary payoff decomposition
  `(1 - β) · stage + β · continuation` becomes `λ · stage + (1 - λ) ·
  continuation`, so `bellmanPoly` is `V_{s,i} - (λ · stagePoly s i +
  (1 - λ) · contPoly s i)`.  The transition probabilities
  `(G.transition s a s').toReal` appear only as *constant* coefficients;
  the only variables are the mixing weights, the values, and `λ`.  Since
  `stagePoly`/`contPoly` are sums of degree-`|ι|` monomials in the mixing
  variables (one factor per player) times a degree-`≤ 1` factor in the
  value variables, `bellmanPoly` has total degree at most `|ι| + 2`;

* `bestResponsePoly s i b`, for every *pure* action `b : G.Act i` — the
  best-response inequality for a unilateral pure deviation to `b`, written
  with the same `λ`/`(1 - λ)` split against the deviation payoff
  `devStagePoly`/`devContPoly` (which omit player `i`'s own mixing factor,
  since it has been fixed to the pure action `b`).  These have total degree
  at most `|ι| + 1`.

Best response against *pure* deviations is exactly what
`IsDiscountedAuxNash` (via `PMF.pure`) already demands verbatim; the
converse — recovering the inequality against every *mixed* deviation from
the finite family of pure inequalities — is a one-line consequence of the
affine dependence of expected utility on one player's own mixed strategy,
proved here as `discountedAuxEU_update_le_of_forall_pure` by reducing to
`KernelGame.mixedExtension_eu_update`.

## Main definitions

* `StochasticGame.BellmanVar` — the finite-per-state variable index type
* `StochasticGame.bellmanPoly`, `StochasticGame.bestResponsePoly` — the
  Bellman-equality and best-response polynomials
* `StochasticGame.IsPolynomialBellmanSolution` — the conjunction of all
  equality/inequality conditions cut out by the polynomial family: the
  **Bellman variety** (together with the open best-response cone)
* `StochasticGame.bellmanAssignment` — encodes a candidate `(x, V, β)` as a
  point of `BellmanVar G → ℝ`
* `StochasticGame.bellmanDecodeProfile`/`bellmanDecodeValue`/
  `bellmanDecodeDiscount` — decode an arbitrary real point of the variety
  back into a stationary mixed profile (via
  `Math.ProbabilityMassFunction.ofVector`), a value vector, and a discount
  factor

## Main results

* `StochasticGame.isPolynomialBellmanSolution_bellmanAssignment` — encoding:
  every discounted stationary Bellman equilibrium encodes to a point of the
  variety
* `StochasticGame.isDiscountedStationaryBellmanEq_bellmanDecode` — decoding:
  every point of the variety decodes to a discounted stationary Bellman
  equilibrium
* `StochasticGame.isDiscountedStationaryBellmanEq_iff_isPolynomialBellmanSolution`
  — the two directions combine into the full characterization: for
  `x`, `V`, `β`, `IsDiscountedStationaryBellmanEq β x V` holds iff the
  encoded point `bellmanAssignment x V β` lies on the variety

## Why this matters

This presentation is the interface between the probabilistic proof of
Fink's theorem and real-algebraic methods for the vanishing-discount limit
that the uniform-equilibrium program ultimately needs: `bellmanPoly` and
`bestResponsePoly` are polynomial in `λ`, so a discounted equilibrium
selection `β ↦ (x_β, V_β)` becomes, after this encoding, a section of the
real variety cut out by finitely many polynomials over the parameter
`λ = 1 - β`.  Existence of a Puiseux-series germ of such a section as
`λ → 0⁺` (Shapley/Bewley–Kohlberg-style semialgebraic selection) and
resultant-based elimination of the mixing and value variables (Mathlib's
`RingTheory.Polynomial.Resultant`) are the next steps of the "W" layers of
the roadmap; this file only sets up the exact polynomial data they act on.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {ι : Type} (G : StochasticGame ι)
  [Fintype G.State] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (G.Act i)]
  [∀ i, DecidableEq (G.Act i)]

/-- The finite index type of the real unknowns in the Bellman polynomial
presentation: a mixing-probability variable `mix s i a` per state, player,
and action; a value variable `val s i` per state and player; and a single
shared discount-complement variable `disc`, meant to be bound to `1 - β`. -/
inductive BellmanVar (G : StochasticGame ι) : Type where
  /-- The mixing-probability variable for player `i` playing action `a` at
  state `s`. -/
  | mix (s : G.State) (i : ι) (a : G.Act i) : BellmanVar G
  /-- The continuation-value variable of player `i` at state `s`. -/
  | val (s : G.State) (i : ι) : BellmanVar G
  /-- The shared discount-complement variable, bound to `1 - β`. -/
  | disc : BellmanVar G

/-- The simplex equality `Σ_a x_{s,i,a} - 1`, forced to vanish. -/
def simplexSumPoly (s : G.State) (i : ι) : MvPolynomial (BellmanVar G) ℝ :=
  (∑ a : G.Act i, MvPolynomial.X (BellmanVar.mix s i a)) - MvPolynomial.C 1

/-- The simplex inequality generator `x_{s,i,a}`, forced to be nonnegative. -/
def simplexNonnegPoly (s : G.State) (i : ι) (a : G.Act i) :
    MvPolynomial (BellmanVar G) ℝ :=
  MvPolynomial.X (BellmanVar.mix s i a)

/-- The on-profile stage-payoff polynomial at `(s, i)`: the multilinear form
`Σ_a (Π_j x_{s,j,a j}) · G.stagePayoff s a i` in the mixing variables, with
the stage payoffs as constant coefficients. -/
def stagePoly (s : G.State) (i : ι) : MvPolynomial (BellmanVar G) ℝ :=
  ∑ a : G.JointAct, (∏ j, MvPolynomial.X (BellmanVar.mix s j (a j))) *
    MvPolynomial.C (G.stagePayoff s a i)

/-- The on-profile continuation-value polynomial at `(s, i)`: the mixing
monomials times the transition-weighted sum of value variables at successor
states, with the transition probabilities as constant coefficients. -/
def contPoly (s : G.State) (i : ι) : MvPolynomial (BellmanVar G) ℝ :=
  ∑ a : G.JointAct, (∏ j, MvPolynomial.X (BellmanVar.mix s j (a j))) *
    ∑ s' : G.State,
      MvPolynomial.C (G.transition s a s').toReal * MvPolynomial.X (BellmanVar.val s' i)

/-- The Bellman value-consistency polynomial at `(s, i)`.  With `disc`
bound to `λ = 1 - β`, this is `V_{s,i} - (λ · stagePoly + (1 - λ) ·
contPoly)`, matching Fink's decomposition `(1 - β) · stage + β ·
continuation` of `discountedAuxPayoff` after substituting `β = 1 - λ`.
Total degree at most `|ι| + 2`. -/
def bellmanPoly (s : G.State) (i : ι) : MvPolynomial (BellmanVar G) ℝ :=
  MvPolynomial.X (BellmanVar.val s i) -
    (MvPolynomial.X BellmanVar.disc * G.stagePoly s i +
      (MvPolynomial.C 1 - MvPolynomial.X BellmanVar.disc) * G.contPoly s i)

/-- The pure-deviation stage-payoff polynomial at `(s, i, b)`: like
`stagePoly`, but player `i`'s own mixing factor is dropped (their action is
pinned to the pure action `b`, encoded by the indicator `if a i = b then
... else 0` on the constant coefficient). -/
def devStagePoly (s : G.State) (i : ι) (b : G.Act i) :
    MvPolynomial (BellmanVar G) ℝ :=
  ∑ a : G.JointAct,
    (∏ j ∈ Finset.univ.erase i, MvPolynomial.X (BellmanVar.mix s j (a j))) *
      MvPolynomial.C (if a i = b then G.stagePayoff s a i else 0)

/-- The pure-deviation continuation-value polynomial at `(s, i, b)`, the
`devStagePoly` analogue of `contPoly`. -/
def devContPoly (s : G.State) (i : ι) (b : G.Act i) :
    MvPolynomial (BellmanVar G) ℝ :=
  ∑ a : G.JointAct,
    (∏ j ∈ Finset.univ.erase i, MvPolynomial.X (BellmanVar.mix s j (a j))) *
      (if a i = b then
        ∑ s' : G.State,
          MvPolynomial.C (G.transition s a s').toReal * MvPolynomial.X (BellmanVar.val s' i)
       else 0)

/-- The best-response polynomial at `(s, i, b)`: the value `V_{s,i}` minus
the `λ`/`(1 - λ)` deviation payoff of playing the pure action `b` against
the mixing variables of every other player, forced to be nonnegative.
Total degree at most `|ι| + 1`. -/
def bestResponsePoly (s : G.State) (i : ι) (b : G.Act i) :
    MvPolynomial (BellmanVar G) ℝ :=
  MvPolynomial.X (BellmanVar.val s i) -
    (MvPolynomial.X BellmanVar.disc * G.devStagePoly s i b +
      (MvPolynomial.C 1 - MvPolynomial.X BellmanVar.disc) * G.devContPoly s i b)

/-- A real assignment of the Bellman variables is a **polynomial Bellman
solution** when it lies on the simplex constraints, satisfies every Bellman
value-consistency equation, and satisfies every pure best-response
inequality.  This is the finite polynomial certificate characterizing
`IsDiscountedStationaryBellmanEq` (see
`isDiscountedStationaryBellmanEq_iff_isPolynomialBellmanSolution`). -/
def IsPolynomialBellmanSolution (assign : BellmanVar G → ℝ) : Prop :=
  (∀ s i, MvPolynomial.eval assign (G.simplexSumPoly s i) = 0) ∧
    (∀ s i a, 0 ≤ MvPolynomial.eval assign (G.simplexNonnegPoly s i a)) ∧
    (∀ s i, MvPolynomial.eval assign (G.bellmanPoly s i) = 0) ∧
    (∀ s i b, 0 ≤ MvPolynomial.eval assign (G.bestResponsePoly s i b))

/-- The point of the Bellman variety encoding a candidate stationary
profile `x`, continuation value `V`, and discount factor `β`: mixing
variables get `x`'s real coordinates, value variables get `V`, and `disc`
gets `1 - β`. -/
def bellmanAssignment (x : G.StationaryMixedProfile) (V : G.State → Payoff ι)
    (β : ℝ) : BellmanVar G → ℝ
  | .mix s i a => (x s i a).toReal
  | .val s i => V s i
  | .disc => 1 - β

/-! ### Plumbing: evaluating the polynomials against a candidate profile -/

omit [Fintype G.State] [∀ i, DecidableEq (G.Act i)] in
/-- Evaluating `stagePoly` against any assignment agreeing with `x` on the
mixing coordinates recovers the on-profile expected stage payoff. -/
theorem eval_stagePoly {assign : BellmanVar G → ℝ} {x : G.StationaryMixedProfile}
    (hx : ∀ s i a, assign (BellmanVar.mix s i a) = (x s i a).toReal)
    (s : G.State) (i : ι) :
    MvPolynomial.eval assign (G.stagePoly s i) =
      expect (pmfPi (x s)) (fun a => G.stagePayoff s a i) := by
  classical
  rw [stagePoly, expect_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul, MvPolynomial.eval_prod, MvPolynomial.eval_C, MvPolynomial.eval_X, hx,
    pmfPi_apply, ENNReal.toReal_prod]

omit [∀ i, DecidableEq (G.Act i)] in
/-- Evaluating `contPoly` against any assignment agreeing with `(x, V)` on
the mixing/value coordinates recovers the on-profile expected continuation
value. -/
theorem eval_contPoly {assign : BellmanVar G → ℝ} {x : G.StationaryMixedProfile}
    {V : G.State → Payoff ι}
    (hx : ∀ s i a, assign (BellmanVar.mix s i a) = (x s i a).toReal)
    (hV : ∀ s i, assign (BellmanVar.val s i) = V s i) (s : G.State) (i : ι) :
    MvPolynomial.eval assign (G.contPoly s i) =
      expect (pmfPi (x s)) (fun a => expect (G.transition s a) (fun s' => V s' i)) := by
  classical
  rw [contPoly, expect_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul, MvPolynomial.eval_prod, MvPolynomial.eval_X, hx, pmfPi_apply,
    ENNReal.toReal_prod, map_sum]
  congr 1
  rw [expect_eq_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  simp [hV, mul_comm]

omit [∀ i, DecidableEq (G.Act i)] in
/-- Evaluating `bellmanPoly` against any assignment agreeing with `(x, V)`
on the mixing/value coordinates recovers the (unnormalized) Bellman
residual `V - discountedAuxEU`, at the discount factor read off the `disc`
coordinate. -/
theorem eval_bellmanPoly {assign : BellmanVar G → ℝ} {x : G.StationaryMixedProfile}
    {V : G.State → Payoff ι}
    (hx : ∀ s i a, assign (BellmanVar.mix s i a) = (x s i a).toReal)
    (hV : ∀ s i, assign (BellmanVar.val s i) = V s i) (s : G.State) (i : ι) :
    MvPolynomial.eval assign (G.bellmanPoly s i) =
      V s i - G.discountedAuxEU (1 - assign BellmanVar.disc) V s (x s) i := by
  rw [bellmanPoly]
  simp only [map_sub, map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    G.eval_stagePoly hx, G.eval_contPoly hx hV, hV s i]
  rw [G.discountedAuxEU_eq]
  ring

omit [Fintype G.State] in
/-- Evaluating `devStagePoly` against any assignment agreeing with `x` on
the mixing coordinates recovers the pure-deviation expected stage payoff. -/
theorem eval_devStagePoly {assign : BellmanVar G → ℝ} {x : G.StationaryMixedProfile}
    (hx : ∀ s i a, assign (BellmanVar.mix s i a) = (x s i a).toReal)
    (s : G.State) (i : ι) (b : G.Act i) :
    MvPolynomial.eval assign (G.devStagePoly s i b) =
      expect (pmfPi (Function.update (x s) i (PMF.pure b))) (fun a => G.stagePayoff s a i) := by
  classical
  rw [devStagePoly, expect_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul, MvPolynomial.eval_prod, MvPolynomial.eval_C, MvPolynomial.eval_X, hx,
    pmfPi_apply_update_family, ENNReal.toReal_mul, ENNReal.toReal_prod, PMF.pure_apply]
  split_ifs with hab <;> simp

/-- Evaluating `devContPoly` against any assignment agreeing with `(x, V)`
on the mixing/value coordinates recovers the pure-deviation expected
continuation value. -/
theorem eval_devContPoly {assign : BellmanVar G → ℝ} {x : G.StationaryMixedProfile}
    {V : G.State → Payoff ι}
    (hx : ∀ s i a, assign (BellmanVar.mix s i a) = (x s i a).toReal)
    (hV : ∀ s i, assign (BellmanVar.val s i) = V s i) (s : G.State) (i : ι) (b : G.Act i) :
    MvPolynomial.eval assign (G.devContPoly s i b) =
      expect (pmfPi (Function.update (x s) i (PMF.pure b)))
        (fun a => expect (G.transition s a) (fun s' => V s' i)) := by
  classical
  rw [devContPoly, expect_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hab : a i = b
  · simp only [hab, if_true]
    rw [map_mul, MvPolynomial.eval_prod]
    simp only [MvPolynomial.eval_X, hx]
    rw [map_sum]
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, hV]
    rw [pmfPi_apply_update_family]
    simp only [PMF.pure_apply, hab, if_true, one_mul, ENNReal.toReal_prod]
    rw [expect_eq_sum]
  · have hzero : pmfPi (Function.update (x s) i (PMF.pure b)) a = 0 := by
      rw [pmfPi_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hab])
    simp [hab, hzero]

/-- Evaluating `bestResponsePoly` against any assignment agreeing with
`(x, V)` on the mixing/value coordinates recovers the pure-deviation
Bellman residual `V - discountedAuxEU (update ... (pure b))`, at the
discount factor read off the `disc` coordinate. -/
theorem eval_bestResponsePoly {assign : BellmanVar G → ℝ} {x : G.StationaryMixedProfile}
    {V : G.State → Payoff ι}
    (hx : ∀ s i a, assign (BellmanVar.mix s i a) = (x s i a).toReal)
    (hV : ∀ s i, assign (BellmanVar.val s i) = V s i) (s : G.State) (i : ι) (b : G.Act i) :
    MvPolynomial.eval assign (G.bestResponsePoly s i b) =
      V s i -
        G.discountedAuxEU (1 - assign BellmanVar.disc) V s
          (Function.update (x s) i (PMF.pure b)) i := by
  rw [bestResponsePoly]
  simp only [map_sub, map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    G.eval_devStagePoly hx, G.eval_devContPoly hx hV, hV s i]
  rw [G.discountedAuxEU_eq]
  ring

/-! ### Encoding: a semantic equilibrium is a point of the variety -/

/-- **Encoding.**  Every discounted stationary Bellman equilibrium encodes
to a point of the Bellman variety: the simplex constraints hold because `x`
is genuinely a stationary mixed profile, the Bellman equalities hold by
value consistency, and the best-response inequalities hold because
`IsDiscountedAuxNash` already quantifies over the pure deviations
`PMF.pure b`. -/
theorem isPolynomialBellmanSolution_bellmanAssignment {β : ℝ}
    {x : G.StationaryMixedProfile} {V : G.State → Payoff ι}
    (hF : G.IsDiscountedStationaryBellmanEq β x V) :
    G.IsPolynomialBellmanSolution (G.bellmanAssignment x V β) := by
  have hx : ∀ s i a, G.bellmanAssignment x V β (BellmanVar.mix s i a) = (x s i a).toReal :=
    fun _ _ _ => rfl
  have hV : ∀ s i, G.bellmanAssignment x V β (BellmanVar.val s i) = V s i := fun _ _ => rfl
  have hdisc : G.bellmanAssignment x V β BellmanVar.disc = 1 - β := rfl
  have hβ' : (1 : ℝ) - (1 - β) = β := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s i
    rw [simplexSumPoly, map_sub, map_sum, MvPolynomial.eval_C]
    simp only [MvPolynomial.eval_X, hx]
    rw [Math.Probability.pmf_toReal_sum_one (x s i)]
    ring
  · intro s i a
    rw [simplexNonnegPoly, MvPolynomial.eval_X, hx]
    exact ENNReal.toReal_nonneg
  · intro s i
    rw [G.eval_bellmanPoly hx hV, hdisc, hβ', hF.2 s i]
    ring
  · intro s i b
    rw [G.eval_bestResponsePoly hx hV, hdisc, hβ']
    have := hF.1 s i (PMF.pure b)
    linarith [hF.2 s i]

/-! ### Decoding: a point of the variety is a semantic equilibrium -/

/-- The mixing coordinates of a polynomial Bellman solution at `(s, i)`
form a genuine point of the standard simplex, so `Math.
ProbabilityMassFunction.ofVector` can turn them into a `PMF`. -/
theorem mem_stdSimplex_of_isPolynomialBellmanSolution {assign : BellmanVar G → ℝ}
    (hSol : G.IsPolynomialBellmanSolution assign) (s : G.State) (i : ι) :
    (fun a => assign (BellmanVar.mix s i a)) ∈ stdSimplex ℝ (G.Act i) := by
  refine ⟨fun a => ?_, ?_⟩
  · have := hSol.2.1 s i a
    simpa [simplexNonnegPoly] using this
  · have := hSol.1 s i
    simp only [simplexSumPoly, map_sub, map_sum, MvPolynomial.eval_X, MvPolynomial.eval_C] at this
    linarith

/-- Decode the stationary mixed profile represented by a polynomial Bellman
solution: at every `(s, i)`, the mixing coordinates form a simplex point,
turned into a `PMF` via `Math.ProbabilityMassFunction.ofVector`. -/
def bellmanDecodeProfile {assign : BellmanVar G → ℝ}
    (hSol : G.IsPolynomialBellmanSolution assign) : G.StationaryMixedProfile :=
  fun s i =>
    Math.ProbabilityMassFunction.ofVector (fun a => assign (BellmanVar.mix s i a))
      (G.mem_stdSimplex_of_isPolynomialBellmanSolution hSol s i)

/-- The decoded profile's real coordinates are literally the assignment's
mixing coordinates. -/
theorem bellmanDecodeProfile_apply_toReal {assign : BellmanVar G → ℝ}
    (hSol : G.IsPolynomialBellmanSolution assign) (s : G.State) (i : ι) (a : G.Act i) :
    ((G.bellmanDecodeProfile hSol s i) a).toReal = assign (BellmanVar.mix s i a) := by
  unfold bellmanDecodeProfile
  rw [Math.ProbabilityMassFunction.ofVector_toReal]

/-- Decode the continuation value represented by a polynomial Bellman
solution: read off the value coordinates directly. -/
def bellmanDecodeValue (assign : BellmanVar G → ℝ) : G.State → Payoff ι :=
  fun s i => assign (BellmanVar.val s i)

/-- Decode the discount factor represented by a polynomial Bellman
solution: `β = 1 - λ`, where `λ` is the `disc` coordinate. -/
def bellmanDecodeDiscount (assign : BellmanVar G → ℝ) : ℝ :=
  1 - assign BellmanVar.disc

omit [∀ i, DecidableEq (G.Act i)] in
/-- Best-response gain against an arbitrary mixed deviation `d` is the
expectation, under `d`, of the pure-deviation gains — the affine-in-own-
strategy fact that reduces the mixed best-response condition to its pure
instances. -/
theorem discountedAuxEU_update_eq_expect_pure (β : ℝ) (V : G.State → Payoff ι)
    (x : G.StationaryMixedProfile) (s : G.State) (who : ι) (d : PMF (G.Act who)) :
    G.discountedAuxEU β V s (Function.update (x s) who d) who =
      expect d (fun b => G.discountedAuxEU β V s (Function.update (x s) who (PMF.pure b)) who) := by
  haveI : Finite (G.discountedAuxGame β V s).Outcome := inferInstanceAs (Finite G.JointAct)
  have hstep := (G.discountedAuxGame β V s).mixedExtension_eu_update (x s) who d
  simp only [G.mixedExtension_eu_discountedAuxGame] at hstep
  exact hstep

omit [∀ i, DecidableEq (G.Act i)] in
/-- If no pure deviation of player `who` at state `s` improves on the
current auxiliary payoff, neither does any mixed deviation: mixed best
response follows from the finite family of pure best-response
inequalities. -/
theorem discountedAuxEU_update_le_of_forall_pure {β : ℝ} {V : G.State → Payoff ι}
    {x : G.StationaryMixedProfile} {s : G.State} {who : ι}
    (hpure : ∀ b : G.Act who,
      G.discountedAuxEU β V s (Function.update (x s) who (PMF.pure b)) who ≤
        G.discountedAuxEU β V s (x s) who)
    (d : PMF (G.Act who)) :
    G.discountedAuxEU β V s (Function.update (x s) who d) who ≤
      G.discountedAuxEU β V s (x s) who := by
  rw [G.discountedAuxEU_update_eq_expect_pure β V x s who d]
  calc
    expect d (fun b => G.discountedAuxEU β V s (Function.update (x s) who (PMF.pure b)) who)
        ≤ expect d (fun _ => G.discountedAuxEU β V s (x s) who) := expect_mono _ _ _ hpure
    _ = G.discountedAuxEU β V s (x s) who := expect_const _ _

/-- **Decoding.**  Every point of the Bellman variety decodes to a
discounted stationary Bellman equilibrium: the Bellman equalities transfer
directly, and the best-response inequalities transfer from the pure
polynomial family to arbitrary mixed deviations via
`discountedAuxEU_update_le_of_forall_pure`. -/
theorem isDiscountedStationaryBellmanEq_bellmanDecode {assign : BellmanVar G → ℝ}
    (hSol : G.IsPolynomialBellmanSolution assign) :
    G.IsDiscountedStationaryBellmanEq (G.bellmanDecodeDiscount assign)
      (G.bellmanDecodeProfile hSol) (G.bellmanDecodeValue assign) := by
  have hx : ∀ s i a,
      assign (BellmanVar.mix s i a) = ((G.bellmanDecodeProfile hSol s i) a).toReal :=
    fun s i a => (G.bellmanDecodeProfile_apply_toReal hSol s i a).symm
  have hV : ∀ s i, assign (BellmanVar.val s i) = G.bellmanDecodeValue assign s i :=
    fun _ _ => rfl
  unfold bellmanDecodeDiscount
  constructor
  · intro s who d
    apply G.discountedAuxEU_update_le_of_forall_pure
    intro b
    have hev := G.eval_bestResponsePoly hx hV s who b
    have hIneqb := hSol.2.2.2 s who b
    rw [hev] at hIneqb
    have hEqsi := hSol.2.2.1 s who
    rw [G.eval_bellmanPoly hx hV] at hEqsi
    linarith
  · intro s who
    have hEqsi := hSol.2.2.1 s who
    rw [G.eval_bellmanPoly hx hV] at hEqsi
    linarith

/-! ### Round trip and the full characterization -/

omit [Fintype G.State] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (G.Act i)]
  [∀ i, DecidableEq (G.Act i)] in
/-- Decoding the value vector out of an encoded assignment recovers the
original value vector. -/
theorem bellmanDecodeValue_bellmanAssignment (x : G.StationaryMixedProfile)
    (V : G.State → Payoff ι) (β : ℝ) : G.bellmanDecodeValue (G.bellmanAssignment x V β) = V :=
  rfl

omit [Fintype G.State] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (G.Act i)]
  [∀ i, DecidableEq (G.Act i)] in
/-- Decoding the discount factor out of an encoded assignment recovers the
original discount factor. -/
theorem bellmanDecodeDiscount_bellmanAssignment (x : G.StationaryMixedProfile)
    (V : G.State → Payoff ι) (β : ℝ) :
    G.bellmanDecodeDiscount (G.bellmanAssignment x V β) = β := by
  unfold bellmanDecodeDiscount bellmanAssignment
  ring

/-- Decoding the stationary profile out of an encoded assignment recovers
the original profile: `ofVector` inverts `toVector` on simplex points. -/
theorem bellmanDecodeProfile_bellmanAssignment {β : ℝ} {x : G.StationaryMixedProfile}
    {V : G.State → Payoff ι}
    (hSol : G.IsPolynomialBellmanSolution (G.bellmanAssignment x V β)) :
    G.bellmanDecodeProfile hSol = x := by
  funext s i
  unfold bellmanDecodeProfile
  apply Math.ProbabilityMassFunction.toVector_injective
  rw [Math.ProbabilityMassFunction.toVector_ofVector]
  rfl

/-- **Characterization (encoding ↔ decoding).**  For `β ∈ [0, 1)` (indeed
for any real `β`), `IsDiscountedStationaryBellmanEq β x V` holds exactly
when the point of `BellmanVar G → ℝ` sending mixing coordinates to `x`'s
real weights, value coordinates to `V`, and the discount coordinate to
`1 - β` satisfies every equality polynomial exactly and every inequality
polynomial nonnegatively. -/
theorem isDiscountedStationaryBellmanEq_iff_isPolynomialBellmanSolution
    (β : ℝ) (x : G.StationaryMixedProfile) (V : G.State → Payoff ι) :
    G.IsDiscountedStationaryBellmanEq β x V ↔
      G.IsPolynomialBellmanSolution (G.bellmanAssignment x V β) := by
  constructor
  · exact G.isPolynomialBellmanSolution_bellmanAssignment
  · intro hSol
    have hdec := G.isDiscountedStationaryBellmanEq_bellmanDecode hSol
    rwa [G.bellmanDecodeProfile_bellmanAssignment hSol, G.bellmanDecodeValue_bellmanAssignment,
      G.bellmanDecodeDiscount_bellmanAssignment] at hdec

end StochasticGame
end GameTheory
