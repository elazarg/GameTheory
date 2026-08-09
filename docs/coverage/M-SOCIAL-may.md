# M-SOCIAL: May's theorem

Title: Binary majority characterization with indifferent ballots
Family ID: M-SOCIAL
Pinned root: `GameTheory/Mechanism/SocialChoice/May.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `f6b89fc`
Canonical destination: `GameTheory.May`
Domain contract / decision: D4; post-architecture M-SOCIAL BFS gate
Owner: Wave 4 / Core social choice
Status: complete; all 15 declarations adapted with no deferred rows
Last verified: 2026-08-09

The successor keeps May's theorem at the ranking-free binary social-choice
layer.  Ballots and verdicts are `SignType`; the result does not pass through
lottery preferences, utilities, mechanisms, or strategic compilation.  An
anonymous, neutral, positively responsive rule is exactly majority, including
ties and empty electorates.  The three-voter fixture exercises a strict
two-to-one majority and the generic characterization.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Mechanism/SocialChoice/May.lean` | `tally` | def | adapt | `May.tally` | focused Core build | Signed support uses Mathlib's `SignType`. |
| same | `majority` | def | adapt | `May.majority` | focused Core build | The sign of the tally includes an indifferent verdict. |
| same | `IsAnonymous` | def | adapt | `May.IsAnonymous` | focused Core build | Voter relabeling is expressed by permutations. |
| same | `IsNeutral` | def | adapt | `May.IsNeutral` | focused Core build | Alternative exchange negates ballots and verdict. |
| same | `IsPositivelyResponsive` | def | adapt | `May.IsPositivelyResponsive` | focused Core build | Strict improvement from a nonnegative verdict yields acceptance. |
| same | `majority_isAnonymous` | theorem | adapt | `May.majority_isAnonymous` | focused Core build | Majority is permutation invariant. |
| same | `majority_isNeutral` | theorem | adapt | `May.majority_isNeutral` | focused Core build | Tally commutes with negation. |
| same | `majority_isPositivelyResponsive` | theorem | adapt | `May.majority_isPositivelyResponsive` | focused Core build | A nontrivial pointwise improvement strictly raises the integer tally. |
| same | `tally_eq_card_sub` | theorem | adapt | `May.tally_eq_card_sub` | focused Core build | Support-minus-opposition counting identity. |
| same | `card_pos_eq_card_neg` | theorem | adapt | `May.card_pos_eq_card_neg` | focused Core build | A tied tally has equal strict-support blocks. |
| same | `exists_neg_perm` | theorem | adapt | `May.exists_neg_perm` | focused Core build | The tied strict-support blocks are exchanged by an involutive permutation. |
| same | `eq_zero_of_tally_zero` | theorem | adapt | `May.eq_zero_of_tally_zero` | focused Core build | Anonymity and neutrality force a tied verdict. |
| same | `eq_one_of_tally_pos` | theorem | adapt | `May.eq_one_of_tally_pos` | focused Core build | Lowering a finite positive block constructs the comparison tie. |
| same | `eq_neg_one_of_tally_neg` | theorem | adapt | `May.eq_neg_one_of_tally_neg` | focused Core build | Neutrality reduces the negative case to the positive one. |
| same | `may_theorem` | theorem | adapt | `May.characterization` | focused Core and hostile example build | Majority is characterized exactly by the three axioms. |

Attribution: the predecessor supplied the complete finite May theorem proof
spine.  The successor preserves the mathematics while placing it directly in
the existing Core social-choice branch and using current Mathlib finite-sum
lemmas.

This bounded ledger does not close M-SOCIAL.  The ranking foundations,
Gibbard--Satterthwaite, Sen, and median-voter families remain separate BFS
gates; they must reuse the existing ranking and Arrow surfaces rather than
introduce a second social-choice carrier.

The characterization, positive-responsiveness theorem, and strict-majority
fixture depend only on `propext`, `Classical.choice`, and `Quot.sound`.  Source
checks find no raw `Function.update`, source transport, placeholder, custom
axiom, native evaluation, or build-output command.

Validation:

```text
lake build GameTheory.Core.May GameTheory.Tests.May GameTheory.Core
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
lake build
git diff --check
```
