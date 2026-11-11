# D91: bundle rationality and contract substitution are separate

- **Status:** semantic distinction and direct composition validated; no new GameTheory arena or choice record.
- **Date:** 2026-11-11
- **Experiment:** EXP-186

## Actual consumer and competition

The MathEconLib reference at
`58f602847d7f131994d32ca7a8cc1af35b7e2dbe` already owns set-valued
`ChoiceFunction`, exact substitutes, consistency/IRC and path independence,
and their relationships. Its `Matching.Contracts.Basic` reduces joint blocking
to singleton blocking using substitutes. These are actual consumer operations,
not a proposed new taxonomy. The checkout is inspected read-only; there is no
new dependency or external source edit.

Compare these operations with interpreting an item-level greatest-choice
correspondence as joint acceptance, or inferring substitutes from rational
choice among whole bundles. Direct set maps suffice to test the competition.

## Positive and negative evidence

Quota two on three contracts with priority `0,1,2` satisfies the consumer's
exact contraction/Chernoff, rejection-monotonicity substitutes, IRC and path
independence formulas. Yet its accepted items fail `FiniteChoice.WeakAxiom`
and Sen's expansion formula `C(S) ∩ C(T) ⊆ C(S ∪ T)`. Contract 2 is accepted
alongside either higher-priority contract and rejected when both are offered.

The *same* acceptance map is the uniquely maximizing quota-feasible bundle
under weights `4,2,1`. `Institution.quota_coe` proves identity between the
set-based map and finite bundle representation. Canonical `FiniteChoice.best`
on bundle alternatives satisfies WARP. Thus item WARP and bundle WARP have
different domains even for ordinary responsive quota behavior.

Complementary Boolean contracts provide the converse control: accept both
together and reject either alone. Scores pair=2, empty=1, singleton=0 uniquely
rationalize this whole-bundle choice, with global bundle-menu WARP. The set and
finite maps are again proved identical. It fails substitutes and the actual
joint-to-singleton implication: the pair is accepted together while no proposed
contract is accepted alone. Rational bundle choice is insufficient for that
institutional composition step.

Both rationalizations choose the empty **bundle** from an empty offer. Their
correspondence is nonempty; returning no contracts is not returning no winning
alternative. All finite menus retain ties by definition; these consumers have
proved unique winners, and never form a union of tied bundles. D84's separate
tie-union rejection remains in validation.

## Decision and extraction boundary

Keep the direct generic contraction-to-singleton proof and controls under
`Experimental.Exp186`. MathEconLib already supplies the general institutional
owner, including `PairwiseStable.stable_of_substitutable`; do not duplicate it
as a stable GameTheory framework. A full matching-market compiler was not
implemented or validated. The quota behavior is compatible with the existing
responsive-capacity scope, but this is not a translation theorem for arbitrary
`CapacitatedMarket` values.

`ChoiceFunction.ofBundleOrder` uses a linear order on represented bundle
indices, so antisymmetry makes all maximizing witnesses the same bundle.
Finite-choice extraction must supply actual feasible-index enumeration and a
unique optimum or a separately validated tie rule. It does not replace the
consumer's choice record, imply substitutes/IRC, or license flattening ties.

## Validation

Focused strict builds pass 782 jobs, including both set/finite identity bridges.
The finite membership checks use kernel `decide`, not `native_decide`; public
lint boundaries are unchanged and every evidence module is in the axiom driver.
Source checks and full integration are recorded in EXP-186. No competing record
was implemented or timed; there is no elaboration-performance claim.

Reference files: [choice conditions](https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/Choice/Conditions.lean),
[represented bundles](https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/Choice/Induced.lean),
[contract stability](https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/Matching/Contracts/Basic.lean).
