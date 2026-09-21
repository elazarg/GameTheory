# Lean 4.34 / Mathlib v4.34.0: bump lessons for clients

This records the completed GameTheory bump from 4.33.1 to 4.34.0 and the
changes downstream clients can reuse. Most edits were conditional-lemma
renames. The two changes requiring early API review were the simplex
representation and the nonmeasurable fallback of `Measure.map`.

The finished changes are in [GameTheory commit f2a01b30](https://github.com/elazarg/GameTheory/commit/f2a01b3015aec84605443e0275e822c2cdf7c5fc)
and [fixed-point-theorems commit d9c3aba7](https://github.com/elazarg/fixed-point-theorems-lean4/commit/d9c3aba7340f21a13df59c61d92bfe9622e40da2).
All six fixed-point theorem source files compiled unchanged. The fixed-point
package needed only toolchain, dependency, manifest, and package-version updates.

## Dependency pins

These are the published revisions used for the successful builds:

| Component | Pin |
|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.34.0` |
| Mathlib requirement | `v4.34.0` |
| Resolved Mathlib commit | `5ed2965256430c3649e86755f9576b54eca72435` |
| GameTheory commit | `f2a01b3015aec84605443e0275e822c2cdf7c5fc` |
| fixed-point-theorems commit | `d9c3aba7340f21a13df59c61d92bfe9622e40da2` |

At completion of this bump, GameTheory's 4.34 result was published on `main`
without a `v4.34.0` tag. A client can pin the tested commit explicitly:

```lean
require "elazarg" / "GameTheory" @ git
  "f2a01b3015aec84605443e0275e822c2cdf7c5fc"
```

Set the client's `lean-toolchain` to the value above and update any direct
Mathlib requirement to `v4.34.0`. GameTheory already supplies the fixed-point
dependency. If the client also requires it directly, align that existing pin;
otherwise no extra direct requirement is needed. Then run from the client root:

```text
lake update
lake env lean --version
lake exe cache get
```

Check the Lake-generated manifest resolves the intended GameTheory and
fixed-point commits and exactly one Mathlib at the revision above. Commit the
generated manifest with the dependency changes. Resolve pin conflicts in the
authored Lake configuration; do not edit the manifest or dependency sources
by hand. A cache download failure is an environment issue to resolve before
interpreting build failures. A successful download does not validate the client.

GameTheory and fixed-point-theorems use package versions matching their
toolchain. A client's own product version can follow its existing policy.

## Mechanical changes

These replacements compiled in this port. Match complete identifier or import
tokens in authored sources; avoid replacing substrings, comments, and strings.

| Old | Replacement |
|---|---|
| `if_pos` | `ite_eq_left` |
| `if_neg` | `ite_eq_right` |
| `dif_pos` | `dite_eq_left` |
| `dif_neg` | `dite_eq_right` |
| `if_true` | `ite_true` |
| `if_false` | `ite_false` |
| `Mathlib.Data.Real.Basic` | `Mathlib.Basic.Real.Basic` |
| `Mathlib.Data.Sign.Basic` | `Mathlib.Basic.Sign.Basic` |
| `Finset.prod_lt_prod_of_nonempty` with the old positive-factor arguments | `Finset.prod_lt_prod_of_nonempty₀` |

There were 309 conditional-lemma token replacements in GameTheory. Establishing
the mappings once let the remaining instances be repaired mechanically.
For the product theorem, preserve the subscript `₀`: the old arguments prove
positive left factors, strict pointwise inequality, and nonemptiness. The new
unsuffixed theorem has different assumptions. Compare the actual signatures,
as in [the upstream change](https://github.com/leanprover-community/mathlib4/commit/a78f66ab84d18caad4f74f242218038874bfd5ad).

The [deprecation helper](../scripts/lean-deprecations.py) turns compiler
diagnostics into reviewed, position-specific edits. Its
[regression tests](../scripts/tests/test_lean_deprecations.py) cover Unicode
columns, Windows paths, CRLF/BOM preservation, duplicate diagnostics, full
namespace replacements, and rejection of stale or ambiguous edits.

**Client limitation:** the helper currently accepts tracked sources only under
`GameTheory/` and `lint/`. Passing another repository with `--root` does not
change that allowlist. To reuse it for a client such as VegasCore, adapt both
`tracked_sources` and `source_path` to the client's authored source roots and
run the regression tests with a client-root case. Keep dependency, untracked,
and external paths excluded. The commands below describe the current helper's
workflow; they do not make it a generic client tool.

```text
python scripts/lean-deprecations.py plan --root . --log build.log --out renames.json
python scripts/lean-deprecations.py apply --root . --plan renames.json
python -B -m unittest discover -s scripts/tests -p test_lean_deprecations.py -v
```

Choose local paths for the log and JSON proposal and keep both uncommitted.
Finish the build before generating the proposal. Review its `files`, `unmatched`,
and `remaining_diagnostics` entries before applying it. The latter two contain
the manual work. The helper rejects diagnostics whose continuation says the
replacement has a **different type**, even if another occurrence omitted that
note. It prevalidates every source hash and edit position before writing and
preserves the full replacement namespace. An interrupted apply is only atomic
per file; freeze the source until apply completes, then rebuild.

## Changes requiring review

### Simplex: coordinate set versus simplex elements

Old `stdSimplex ℝ α` was a set of coordinate functions on a finite carrier.
`Convexity.StdSimplex ℝ α` is a type of finitely supported simplex elements.
The compiler's suggested replacement therefore cannot be applied as a rename.

For a client using real coordinate vectors, reuse the canonical view in
[`GameTheory.Math.Probability.Simplex`](../GameTheory/Math/Probability/Simplex.lean):

```lean
import GameTheory.Math.Probability.Simplex

open GameTheory.Math.Probability

example {α : Type*} [Fintype α] {x : α → ℝ}
    (hx : x ∈ simplexWeights α) : ∑ a, x a = 1 :=
  (mem_simplexWeights.mp hx).2
```

`simplexWeights α` is the range of the canonical simplex's weights in `α → ℝ`.
`mem_simplexWeights` gives the familiar nonnegativity-and-total-one criterion.
Membership is no longer a pair by definition: obtain its components through
this theorem before using `.1` or `.2`.

| Old GameTheory API | Current API, in `GameTheory.Math.Probability` |
|---|---|
| `FinDist.prob_mem_stdSimplex` | `FinDist.prob_mem_simplexWeights` |
| `FinDist.stdSimplex_nonempty` | `FinDist.simplexWeights_nonempty` |
| `FinDist.ofSimplex`, `prob_ofSimplex`, `ofSimplex_prob` | Same names, now using membership in `simplexWeights` |

Use `convex_simplexWeights`, `isClosed_simplexWeights`, and
`isCompact_simplexWeights` for the coordinate view. Do not introduce a local
alias for the deprecated `stdSimplex` or duplicate this view in each client.
For code that actually uses simplex elements, use `Convexity.StdSimplex`
directly and its `weights`, `weights_nonneg`, `total_of_fintype`, and `single`
API. The port of the independent
[PMF experiment](../GameTheory/Experimental/Phase1/D2/FiniteSupportPMF.lean)
shows that route without coupling its representation to `FinDist`.

The new coordinate view needs no finiteness assumption just to be defined.
Consequently `mixedPolytope` and the Fink domain and coordinate accessors lost
unnecessary `Fintype` assumptions. Retain finiteness on the sums, conversions,
and finite-dimensional results that need it. Check downstream explicit
argument applications and unused-section-variable warnings after this change.

### Measures: probability instances and the nonmeasurable fallback

Mathlib changed `Measure.map f μ` for non-a.e.-measurable `f`: it now returns an
arbitrary Dirac mass when `μ ≠ 0`, while mapping the zero measure still gives
zero. Mapping a probability measure therefore has an unconditional probability
instance. See [Mathlib PR #42322](https://github.com/leanprover-community/mathlib4/pull/42322).

The deleted `Measure.isProbabilityMeasure_map` was used at eleven GameTheory
sites. For a local `IsProbabilityMeasure (Measure.map f μ)` instance, use
`inferInstance`. For a named measure wrapper, unfold the wrapper and use
`infer_instance`. The completed repairs are in
[`Math/Probability/Measure.lean`](../GameTheory/Math/Probability/Measure.lean)
and [`Protocol/PolicyMeasure.lean`](../GameTheory/Protocol/PolicyMeasure.lean).

Keep the measurability proofs used by `map_apply`, `map_map`, and `integral_map`.
The unconditional probability instance does not establish those identities.
Search client uses of `map_of_not_aemeasurable`, `of_map_ne_zero`, `map_smul`,
`map_eq_zero`, `ae_map_mem_range`, `isProbabilityMeasure_of_map`, and
`measure_preimage_of_map_eq_self` and check their new hypotheses. In particular,
probability of a mapped measure alone no longer proves probability of its
source without a measurability condition.

GameTheory had no uses of those old fallback lemmas. Its proved measurable
bridges survived the port, but raw map/bind expressions outside that regime
inherit the changed fallback. Check a client's use of that regime separately.
Read the pinned definitions when semantics matter: the module introduction of
Mathlib's `Measure/Map.lean` at this revision still describes the old zero
fallback, while the actual `map` definition and its declaration docstring
describe the new behavior.

### Tactics, lint, and architecture checks

Some `norm_num` calls now close a goal earlier. At a "No goals to be solved"
error, remove the unreachable proof tail after confirming which tactic finished
the goal. This removed thirteen lines across six GameTheory test and experiment
files without changing their statements. Inspect unused simp arguments
individually; deleting every reported argument together can break a proof.

Run the environment linter as well as the compiler. The completed build still
exposed four missing docstrings and unused section assumptions during
`lake lint`; these were fixed before the final commit. The 4.33 transparency
and enum-deriving workarounds in [the historical notes](../CLAUDE.md#toolchain-bump-lessons-lean-433--mathlib-v4331)
are evidence for that release. This bump did not need another blanket round of
those changes: `Core/Signature`, `Core/Equilibrium`, `Core/MatrixGame`, and
the fixed-point theorem sources compiled unchanged.

Update architecture audit sentinels when names disappear. GameTheory's deep
import checks now use `Convexity.StdSimplex`, and test both its absence from the
core and its presence in the analytic root. A negative check for an obsolete
name can pass vacuously. Source-level transport counts also decreased where
redundant `change` steps became `rfl`; audit the actual diffs before updating
expected counts.

## Repeatable build discipline

Start by searching the client's authored Lean roots for the simplex and measure
sites above. Repair a representative consumer of each shared API early, so
these changes are visible while the routine renames proceed. A failed first
build only reports modules whose dependencies are available; it does not
enumerate every downstream failure.

Repair modules with many consumers first, then run the narrowest affected
Lake target. Keep one build active per checkout and finish source edits before
starting it. Rebuild an edited imported module before checking a consumer with
`lake env lean`: that command reads compiled imports, not their edited source.
Repeat diagnostic collection after each integrated batch.

At the end, build all client library, test, example, executable, and lint
targets that its CI promises. A default target may not cover them all. Run its
environment linter and boundary checks, and inspect axioms for changed theorem
bridges where applicable. Commit the final compiling source, dependency pins,
and generated manifest. Keep planning notes and raw logs local; durable lessons
should link to committed sources and upstream changes, without requiring a
particular worktree or generated dependency directory.

For reference, the completed GameTheory validation was:

```text
lake --wfail build GameTheory GameTheory.Math GameTheory.LintAll
lake lint
pwsh -NoProfile -File scripts/check-release-version.ps1
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -DeepReachability
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected -DeepReachability
```

The GameTheory build passed with 4,133 jobs; the separate fixed-point package
build passed with 3,142. Lint and all three audits passed. Axiom probes of Nash,
Fink, the compact coordinate view, and the finite conditioning measure bridge
reported only `propext`, `Classical.choice`, and `Quot.sound`. The deprecation
helper passed ten regression tests and a real Lean 4.34 diagnostic/apply/build
smoke check. These are results for the pinned libraries; clients need their
own final checks.

## Release metadata lesson

The `v4.33.1` tag originally contained package version `0.1.0`. Fixing `main`
did not fix that existing tag. The repaired tag points to
`809e91b7a482f6f6f34b6986c7b07aca9e4478a3`, with only the package-version
correction, and its tracked tree has no `0.1.0` occurrence.

[`check-release-version.ps1`](../scripts/check-release-version.ps1) now checks
GameTheory's package, toolchain, Mathlib requirement, and manifest input
revision; CI also supplies the version tag when applicable. Validate the
tagged tree and release metadata as well as the branch. Adapt the equality
policy before copying this check into a client with independent product
versioning.
