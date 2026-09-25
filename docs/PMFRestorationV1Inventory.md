# v1 PMF restoration inventory

Read-only source survey for the `v1-final` annotated tag (tag object
`9a97eb703249436707e1fffcc4efd5ead30d6754`, peeled commit
`02898a2d8b918f9b106a683420ca78c99867560e`) against the pre-restoration Lean
4.34.0 baseline `1dba33272108204204758c6eaa5ef8ce49a428c5`. References to
"current" and FinDist below describe that historical comparison, not the
restored API. Current coverage is in the [delivery ledger](DeliveryLedger.md).
Counts below are **top-level declaration lines matched by**
`^(theorem|lemma|def|noncomputable def|structure|class|instance|private theorem|private def|abbrev)`;
they are orientation counts, not independent theorem counts, and exclude local,
scoped, `@[simp] lemma`, and nested declarations. No old proof was recompiled
against this checkout.

## Semantic foundation and expectation

| v1 source | Count | Concrete reusable material | Treatment |
| --- | ---: | --- | --- |
| `v1-final:Math/Probability.lean` | 61 | `pmf_toReal_tsum_one` (183), `pmf_toReal_summable` (229), `expect_summable_of_bounded` (235), bounded pointwise convergence (382), `expect_add_of_summable` (496), bounded bind/Fubini (794, 833), change of variables and summability transport (1023–1135) | Adapt proofs to Mathlib `PMF.toMeasure` integral with explicit integrability, or keep a named weighted-sum bridge with a summability certificate. Finite laws already belong to `FinDist.expect`. |
| `v1-final:Math/ProbabilityMassFunction.lean` | 97 | Arbitrary-carrier event mass `pmfMass` (314), equality to `toOuterMeasure` (323), positive-event `pmfCond` (369), support-dependent bind congruence (568), expectation congruence on support (654), finite fiber conditioning/disintegration (1166–1378), countable bounded monotonicity (1438–1458), geometric-series interchange (1464) | Recover targeted missing theorem statements, usually on `PMF`/`PMF.toMeasure`; use existing Mathlib constructors. Generalize finite hypotheses only after a real infinite-support proof. |
| `v1-final:Math/ProbabilityMassFunction/{Distinguishing,Simplex,TotalVariation}.lean` | 16, 15, 10 | TV/test duality (finite), `PMF α ≃ stdSimplex ℝ α` for `[Fintype α]`, TV data processing and expectation bounds (finite) | Useful finite analysis; largely recover through current `FinDist` and simplex layer rather than a second PMF-facing finite API. |
| `v1-final:Math/PMFIter.lean` | 16 | PMF kernel iteration (36–190), finite harmonic/step expectation laws (199, 212) | Recover if a countable stochastic-process consumer needs them; iteration is general but expectation conclusions are finite. |

The old real expectation is **defined** at `v1-final:Math/Probability.lean:121`
as `∑' ω, (d ω).toReal * f ω` for every `f : Ω → ℝ`. Lean's real `tsum`
equals zero when the summand is not summable. Thus a divergent nonnegative
utility can have old `expect = 0`; it is not a real-valued expectation in the
usual probabilistic sense without integrability. This is an API semantic
hazard, **not evidence that the proved equalities are false**. In particular,
`expect_map` (1103) handles the nonsummable case by establishing that
summability is preserved by pushforward and then applying
`tsum_eq_zero_of_not_summable` on both sides. `expect_add_of_summable` explicitly
documents why additivity needs hypotheses. `expect_const_mul` and `expect_neg`
are identities of totalized `tsum` and are not, alone, an integrability API.
Bounded lemmas and finite-carrier lemmas have the needed control. The
finite-source/target map lemmas (900, 964), strict/ordinary monotonicity (558,
566), and finite `expect_bind` (889) have explicit finiteness in their
statements. The separate arbitrary-carrier `expect_bind_of_bounded` (833) does
the actual absolute-summability/Fubini work. The finite `expect_bind` proof
gets boundedness from `[Finite β]`, even if source `α` is infinite.

Current Mathlib already supplies `PMF.bind`, `bind_apply`, `support_bind`,
`bindOnSupport` and its support/associativity laws
(`Mathlib/Probability/ProbabilityMassFunction/Monad.lean:113–270`), `PMF.map`,
`ofFinset`, `normalize`, `filter` and support formulas
(`.../Constructions.lean:45–80,164–290`), `PMF.toMeasure` and event mass
(`.../Basic.lean:214–287`), and `PMF.integral_eq_tsum` given integrability
(`.../Integrals.lean:32`). The current
`GameTheory/Experimental/PostArchitecture/CountablePMFExpectation.lean:28–41`
already proves bounded PMF integral = weighted real `tsum` and the bridge from
finite-support `FinDist.expect`. It tests an actual infinite-support stopping
law at lines 59–95. This is the safest seed for the restored countable
expectation API.

## Dependent products, independence, and conditioning

The eight v1 `Math/PMFProduct/` files have **88 matched declarations**: Basic
31, Bind 10, Bool 2, CoalitionMass 8, Conditioning 5, Independence 13,
TotalVariation 2, Update 17. Their proof density is much larger than the
declaration count (Independence and Update contain long specialized proofs).

* `Basic.lean:34–77` proves `ENNReal_tsum_pi_fin` and `ENNReal_tsum_pi`; `pmfPi`
  (141) constructs a dependent product of *arbitrary* `PMF (A i)` over a
  **finite index** `ι`. The coordinate carriers need not be finite. Pointwise
  convergence of product masses is at 157 and 174, pure products at 184.
  `Ignores`/`Ignores₂` (234–381) formalize coordinate independence of a
  continuation. Current `GameTheory/Math/Probability/FinDist.lean:1626–1658`
  has the analogous finite-support `pmfPi`/`FinDist.pi`, but cannot produce an
  infinite-support factor/product. This v1 product is a genuine missing
  general-PMF capability.
* `Bind.lean:49` has `tsum_pmfPi_factor`, a general `ENNReal` coordinate
  factorization. Yet `pmfPi_bind_factor` (144), `pmfPi_bind_eval` (161),
  `pmfPi_push_coord` (220), and coordinate mass (232) all assume
  `[∀ i, Finite (A i)]`. Their proofs install `Fintype.ofFinite` or depend on a
  finite lemma. `pmfPi_push_coordwise` (195) genuinely uses arbitrary
  coordinate PMFs and `ENNReal_tsum_pi`. A countable restoration should prove
  general marginalization directly from the `tsum` factorization.
* `Conditioning.lean:56` factors coordinate event mass for arbitrary coordinate
  PMFs; its coordinate mass lemma (39), coordinate conditional product (74),
  and untouched marginal (112) impose finite coordinates. The explicit
  `bindOnSupport` disintegration (145) has `[Finite α] [Finite β]` and converts
  both to `Fintype`; it is not a countable disintegration theorem.
* `Independence.lean:100,251,371,447,480,556,575` contains coordinate
  independence, expectation, reweighting, and map/bind lemmas; check each
  hypothesis before recovery. For example the early `pmfPi_bind_indep` has
  `[∀ i, Finite (A i)]`, `pmfPi_expect_indep` has
  `[∀ i, Fintype (A i)]`. `Update.lean` proves specialized update/bind and
  event-ratio invariances, much of it also finite-coordinate. Restore only
  when a game or protocol theorem needs those statements; v2's profile
  transport invariant also forbids copying old direct `Function.update` uses
  into the new public layer.
* `TotalVariation.lean` has two finite update/TV expectation lemmas.
  `CoalitionMass.lean` is finite-player real product algebra, not PMF
  infrastructure.

## Conditioning, support-dependent bind, and finite projection trap

`v1-final:Math/ProbabilityMassFunction.lean:309–429` gives event mask, event
mass and `pmfCond` with a proof of positive mass. `pmfMass` is genuinely
countable/arbitrary-carrier: it equals `PMF.toOuterMeasure` event mass.
`pmfCond` delegates to `PMF.normalize`. Mathlib's current `PMF.filter`
already expresses positive-event conditioning and has exact support
(`Constructions.lean:267–290`); a new public `pmfCond` should be a thin
specialization only if its event-mass interface is needed.

The old `condOn` (`ProbabilityMassFunction.lean:1166`) instead takes a projected
value and **falls back to the original law** when its fiber has zero mass.
Its ratio law requires positive projected mass (1175). The self-disintegration
family (1192–1378) has `[Finite α] [Finite β]`, `FiniteProjection` (1292) stores
a finite codomain, and `iterCondOn` (1301) requires a finite source. These
are finite serialization results, not evidence of countable disintegration.
Mathlib `PMF.bindOnSupport` is a better way to avoid specifying impossible
zero-mass fibers; v1's explicit `pmf_bind_disintegrate` used it but still
assumed both carriers finite. Current `FinDist` has support-dependent bind and
conditioning proofs in `GameTheory/Math/Probability/FinDist.lean`; these are
valid finite-support counterparts, not general PMF disintegration.
The v1 search found no separate PMF-on-support-subtype constructor in these
mathematics files: its support-dependent operation is Mathlib's
`PMF.bindOnSupport`, used explicitly in `PMFProduct/Conditioning.lean:149`.

## Finite simplex, convergence, and existing v2 overlap

`v1-final:Math/ProbabilityMassFunction/Simplex.lean:29–133` constructs and
proves a full `PMF α ≃ stdSimplex ℝ α` for `[Fintype α]`; its expectation
weighted-sum bridge is at 123. This is sound finite geometry. Current
`GameTheory/Math/Probability/Simplex.lean:20–75` already gives the equivalent
`FinDist` simplex bridge. `v1-final:Math/Probability.lean:253–417` additionally
has bounded expectation convergence under pointwise PMF convergence for
arbitrary carrier (via overlap/dominated convergence), which the current
`GameTheory/Math/Probability/Convergence.lean:32–69` only handles with
`[Fintype α]`. A general-PMF restoration therefore needs this theorem family
or a Mathlib integral/measure counterpart; finite simplex compactness does
not give countable compactness. Current
`GameTheory/Math/Probability/Compactness.lean:21–41` remains finite-family
`FinDist` compactness.
The pointwise convergence predicate itself lives in
`v1-final:GameTheory/Concepts/Foundations/Convergence.lean:43`, and downstream
v1 mixed and assessment modules import it; it is a small predicate, not the
substantive bounded convergence theorem.

## Game interfaces and sequential meaning

The old `v1-final:GameTheory/Concepts/Mixed/SequentialAssessment.lean:37–56`
uses `PMF` for continuation outcomes and beliefs; `euOutcomePref` at 395–399
compares the old totalized real expectations with no payoff boundedness or
integrability certificate. Its generic limit-consistency extension points are
at 112–146 and 357–386. But default `IsSequentialEqFor` at 389–392 uses
`WeaklyConsistentAssessment`, defined at 103 as belief support plus **on-path**
Bayes rule. The EU-specialized `IsSequentialEq` at 406–409 inherits this weak
default. The source itself says stronger Kreps–Wilson consistency must be
provided through the generic predicate. Restoring v1's default under a strong
sequential-equilibrium name would change the intended theorem meaning.

Current `GameTheory/Core/Deviation.lean:35–87` and
`GameTheory/Protocol/Assessment.lean:46–151` use `FinDist` in deviation,
outcome and value interfaces. Current
`GameTheory/Protocol/BehavioralAssessment.lean:104–109,211–228,240–314`
separates strategy/belief records, generic limit consistency, reach mass and
Bayes consistency. Replacing their law type with `PMF` changes API and proof
obligations; reuse v1 mathematical lemmas beneath these interfaces first,
then introduce a countable semantic slice with an integrable or bounded
payoff certificate and an explicitly chosen consistency predicate.

## Decision supported by the survey

The claim that v1 contains **substantial** general-PMF infrastructure is
supported: arbitrary-carrier PMF event mass/conditioning, bounded expectation
and convergence, and dependent PMF products with finite index but possibly
infinite-support factors are real proved bodies, not names alone. The claim
that the **vast majority of the required restored implementation** is already
there is not quantifiable from this inventory and is too broad for the
countable downstream target: central product marginal, conditional product,
disintegration, and independence results often require finite coordinate or
source types; the old real `expect` totalizes nonsummability; the old EU
assessment omits integrability; and the old default sequential predicate is
weak consistency. A narrow pilot should use the existing infinite-support
`halfStoppingLaw : PMF (Option ℕ)`, prove a bounded nonconstant `bind` tower
using Mathlib `toMeasure` integral/`PMF.integral_eq_tsum`, and then test a
two-coordinate product with an infinite-support factor plus its marginal.
This would measure actual proof reuse and isolate missing countable theorems.
