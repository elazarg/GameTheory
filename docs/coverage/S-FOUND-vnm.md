# S-FOUND: finite-law von Neumann--Morgenstern representation

Title: Finite-outcome expected-utility representation over canonical finite laws
Family ID: S-FOUND
Pinned root: `GameTheory/Concepts/Foundations/VNM/Basic.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `b223ee7`
Canonical destination: `GameTheory.Core.Rank`; `GameTheory.Probability.FinDist`; `GameTheory.Core.VNM`; `GameTheoryMath.AffineUtility`
Domain contract / decision: D2, D4, D9, D41; EXP-074
Owner: Wave 2 / foundations
Status: complete file; all 66 declarations reviewed with no deferred rows
Last verified: 2026-08-09

The successor states vNM independence and continuity on the existing
`WeakPreference` family over canonical `FinDist`.  Expected-utility
representation is family-wide, produces an index `Outcome → Agent → ℝ`, and
adds no second lottery carrier or preference relation.  The converse needs
only a finite outcome type; agent finiteness is absent and the empty-outcome
case is discharged without leaking a public nonemptiness assumption.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Foundations/VNM/Basic.lean` | `Lottery` | abbrev | retired | canonical `FinDist` | D2 audit | No PMF compatibility carrier. |
| same | `expectedValue` | def | subsumed | `FinDist.expect` | focused build | Canonical finite-law expectation. |
| same | `expectedValue_pure` | theorem | subsumed | `FinDist.expect_pure` | focused build | Generic probability API. |
| same | `expectedValue_eq_sum` | theorem | subsumed | `FinDist.expect_eq_sum` | focused build | Generic probability API. |
| same | `expectedValue_mono` | theorem | subsumed | `FinDist.expect_mono` | focused build | Generic probability API. |
| same | `expectedValue_add` | theorem | subsumed | `FinDist.expect_add` | focused build | Generic probability API. |
| same | `expectedValue_const_mul` | theorem | subsumed | `FinDist.expect_smul` | focused build | Generic probability API. |
| same | `expectedValue_const` | theorem | subsumed | `FinDist.expect_const` | focused build | Generic probability API. |
| same | `expectedValue_affine` | theorem | subsumed | `FinDist.expect_add`, `FinDist.expect_smul`, `FinDist.expect_const` | focused build | Kept compositional. |
| same | `expectedValue_sub` | theorem | subsumed | `FinDist.expect_sub` | focused build | Generic probability API. |
| same | `expectedValue_one_sub` | theorem | subsumed | `FinDist.expect_sub`, `FinDist.expect_const` | focused build | Kept compositional. |
| same | `expectedValue_bind` | theorem | subsumed | `FinDist.expect_bind` | compound fixture | Canonical compound-law identity. |
| same | `mix` | def | subsumed | `FinDist.mix` | D2 audit | One finite-law convex combination. |
| same | `expectedValue_binaryMix` | theorem | subsumed | `FinDist.expect_bind`; `FinDist.expect_eq_sum` on `Bool` | focused build | Arbitrary Bool laws need no named binary wrapper. |
| same | `expectedValue_mix` | theorem | subsumed | `FinDist.expect_mix` | focused build | Canonical affine law. |
| same | `IsLinearLotteryFunctional` | def | retired | direct `FinDist.expect_bind` use | API audit | No wrapper without an independent consumer. |
| same | `expectedValue_isLinearLotteryFunctional` | theorem | retired | `FinDist.expect_bind` | API audit | Wrapper theorem is redundant. |
| same | `sureThingPrinciple` | theorem | retired | direct `FinDist.expect_mono`/`expect_bind` composition | API audit | No parallel certificate surface. |
| same | `strict` | def | subsumed | `Rank.strict`; `Preference.strict` | focused build | Probability-free owner. |
| same | `indiff` | def | adapt | `Rank.Indifferent` | focused build | Probability-free owner. |
| same | `Completeness` | def | subsumed | `Rank.Total`; `Preference.Total` | focused build | Canonical naming. |
| same | `Transitivity` | def | subsumed | `Rank.Transitive`; `Preference.Transitive` | focused build | Canonical naming. |
| same | `Independence` | def | adapt | `Preference.MixtureIndependent` | zero-weight regression | Positive mixture weight is explicit. |
| same | `Continuity` | def | adapt | `Preference.MixtureContinuous` | lexicographic fixture | Relation-level mixture continuity. |
| same | `RepresentsExpectedUtility` | def | adapt | `Preference.RepresentsExpectedUtility` | EU fixture | Family-wide canonical expectation. |
| same | `RepresentsExpectedUtility.completeness` | theorem | adapt | `Preference.RepresentsExpectedUtility.total` | focused build | Uses canonical totality. |
| same | `RepresentsExpectedUtility.transitivity` | theorem | adapt | `Preference.RepresentsExpectedUtility.transitive` | focused build | Family-wide result. |
| same | `RepresentsExpectedUtility.independence` | theorem | adapt | `Preference.RepresentsExpectedUtility.mixtureIndependent` | EU fixture | No carrier finiteness needed. |
| same | `RepresentsExpectedUtility.continuity` | theorem | adapt | `Preference.RepresentsExpectedUtility.mixtureContinuous` | interior certainty equivalent | No carrier finiteness needed. |
| same | `RepresentsExpectedUtility.vnmAxioms` | theorem | adapt | `Preference.RepresentsExpectedUtility.vnmAxioms` | focused build | Packages the canonical four laws transparently. |
| same | `probOf` | def | subsumed | `FinDist.prob` | source audit | No probability-coordinate wrapper. |
| same | `probOf_pure_self` | theorem | subsumed | `FinDist.prob_pure_self` | focused build | Generic probability API. |
| same | `probOf_pure_ne` | theorem | subsumed | `FinDist.prob_pure_of_ne` | focused build | Generic probability API. |
| same | `expectedValue_indicator` | theorem | subsumed | `FinDist.expect_indicator_eq_probOf` | EXP-074 | Public conditioning waist. |
| same | `probOf_mix` | theorem | subsumed | `FinDist.prob_mix` | focused build | Generic probability API. |
| same | `probOf_bind` | theorem | subsumed | `FinDist.prob_bind` | focused build | Generic probability API. |
| same | `standardLottery` | def | retired | private vNM proof construction | source audit | Not a second public lottery API. |
| same | `standardLottery_apply_best` | theorem | retired | private proof algebra | theorem build | Representation scaffolding. |
| same | `standardLottery_apply_worst` | theorem | retired | private proof algebra | theorem build | Representation scaffolding. |
| same | `standardLottery_apply_ne` | theorem | retired | private proof algebra | theorem build | Representation scaffolding. |
| same | `mix_self` | theorem | subsumed | `FinDist.mix_self` | focused build | Reusable finite-law algebra. |
| same | `mix_zero` | theorem | subsumed | `FinDist.mix_zero` | focused build | Reusable finite-law algebra. |
| same | `mix_one` | theorem | subsumed | `FinDist.mix_one` | focused build | Reusable finite-law algebra. |
| same | `mix_swap` | theorem | subsumed | `FinDist.mix_swap` | focused build | Reusable finite-law algebra. |
| same | `standardLottery_one` | theorem | retired | private proof algebra | theorem build | Representation scaffolding. |
| same | `standardLottery_zero` | theorem | retired | private proof algebra | theorem build | Representation scaffolding. |
| same | `standardLottery_eq_mix_best_standard` | theorem | retired | private proof algebra | theorem build | Representation scaffolding. |
| same | `standardLottery_eq_mix_best_standard_of_le` | theorem | retired | private proof algebra | theorem build | One private direction suffices. |
| same | `standardLottery_order_of_independence` | theorem | retired | private standard-lottery order proof | hostile theorem build | No public standard-lottery surface. |
| same | `bind_bool_eq_mix` | theorem | retired | direct `FinDist.mix` | EXP-074 | Bool encoding is obsolete. |
| same | `bool_compoundIndifference_of_independence` | theorem | retired | private support induction | EXP-074 | Arbitrary finite support is proved directly. |
| same | `expectedValue_nonneg_of_nonneg` | theorem | subsumed | `FinDist.expect_mono` | focused build | Direct generic consequence. |
| same | `expectedValue_le_one_of_le_one` | theorem | subsumed | `FinDist.expect_mono` | focused build | Direct generic consequence. |
| same | `bind_standardLottery_eq_standard_expectedValue` | theorem | retired | private representation proof | theorem build | No public standard-lottery API. |
| same | `CompoundIndifference` | def | retired | private theorem consequence | D41 API audit | No new public certificate concept. |
| same | `compoundIndifference_of_independence` | theorem | retired | private finite-support induction | EXP-074 | Uses public `FinDist` only. |
| same | `representsExpectedUtility_of_standardLottery_certaintyEquivalents` | theorem | retired | private representation proof | theorem build | Proof scaffolding. |
| same | `exists_representsExpectedUtility_of_compoundIndifference_and_standardLottery_order` | theorem | retired | private representation proof | theorem build | Proof scaffolding. |
| same | `exists_representsExpectedUtility_of_vnmAxioms_of_compoundIndifference` | theorem | retired | private representation proof | theorem build | Proof scaffolding. |
| same | `exists_representsExpectedUtility_of_vnmAxioms` | theorem | adapt | `Preference.exists_representsExpectedUtility` | hostile theorem application | Empty outcomes handled publicly. |
| same | `vnmAxioms_iff_exists_representsExpectedUtility` | theorem | adapt | `Preference.vnmAxioms_iff_exists_representsExpectedUtility` | hostile theorem application | Family-wide characterization. |
| same | `strict_mix_common_iff_of_independence` | theorem | adapt | `Preference.MixtureIndependent.strict_mix_common_iff` | focused build | Canonical strict preference. |
| same | `IsAffineUtility` | def | adapt | `GameTheoryMath.IsAffineUtility` | math build | Game-independent owner. |
| same | `IsRiskNeutral` | def | adapt | `GameTheoryMath.IsRiskNeutral` | math build | Game-independent owner. |
| same | `IsAffineUtility.isRiskNeutral` | theorem | adapt | `GameTheoryMath.IsAffineUtility.isRiskNeutral` | math build | Exact finite-mixture law. |
| same | `IsRiskNeutral.isAffine` | theorem | adapt | `GameTheoryMath.IsRiskNeutral.isAffine` | math build | Full real affine converse. |

Disposition count: 16 adapted, 29 subsumed, and 21 retired.

EXP-074 falsified the first draft's nonnegative independence coefficient:
weight zero collapses both mixtures to the common branch and would trivialize
every reflexive preference.  The corrected public axiom requires `0 < t`.
Its decisive support induction conditions on the complement of a supported
point, proves the exact Bernoulli decomposition and a strict support decrease,
and derives arbitrary finite compound substitution without authored use of
`PMF`, `toPMF`, `ENNReal`, `toReal`, or `Fintype.ofFinite`.

The hostile `Fin 3` fixture has utility values `3, 1, -1`: its half-best,
half-worst law is genuinely indifferent to the middle point mass, and a
positive interior mixture exercises independence.  A lexicographic order on
the first two coordinate masses is total, transitive, and mixture-independent
but not mixture-continuous, so it admits no expected-utility representation.
The tests also exercise multiple agents, empty outcomes, and the rejected
zero-weight formulation.

Attribution: the pinned file supplies the standard-lottery representation
argument and risk-neutrality theorem.  The successor replaces its PMF and Bool
decomposition machinery with canonical `FinDist` support conditioning and
keeps all standard-lottery/certainty-equivalent scaffolding private.

Validation: the focused VNM, Core-root, game-independent affine-utility, and
hostile-test targets build warning-free.  The full structural audit reaches all
eight intended VNM inputs through `GameTheory.Core`, rejects all six strategic,
Protocol, and analytic boundaries from the focused leaf, reaches all four
affine/risk-neutral declarations through `GameTheoryMath`, and rejects both
game and probability semantics from the math leaf.  Authored VNM source has
zero representation escape tokens, `Fintype.ofFinite`, raw updates,
transports, placeholders, or custom axioms.  Representative theorems depend
only on `propext`, `Classical.choice`, and `Quot.sound`.  Exact coverage returns
`VERIFIED=1` at 70 ledgers and 2,747/8,324 claimed rows; the warning-clean
default build completes all 3,542 jobs.
