# S-ZERO: matrix security and value waist

Title: Canonical matrix security, saddle points, and selected value
Family ID: S-ZERO
Pinned root: `GameTheory/Concepts/ZeroSum/MatrixGame.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `d10c8d8`
Canonical destinations: `GameTheory.Core.MatrixGame`;
`GameTheory.Analysis.MatrixValue`
Domain contract / decision: D4, D5, D12, D23
Owner: Wave 2 / finite zero-sum theory
Status: complete bounded slice; 40/40 selected declarations reviewed
Last verified: 2026-08-09

The static matrix compiler, mixed row/column profile, payoff, saddle/Nash
equivalence, guarantees, and caps live in Core.  Analysis selects a value and
proves nonempty optimal strategy sets from the existing finite mixed-Nash
theorem.  No `KernelGame`, PMF, second saddle predicate, or parallel equilibrium
surface survives.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/ZeroSum/MatrixGame.lean` | `toKernelGame` | def | adapt | `GameTheory.MatrixGame.form`; `utility` | Core matrix build | Matrix data compile directly to canonical `GameForm`; utility remains separate. |
| same | `toKernelGame_payoff_row` | theorem | adapt | `GameTheory.MatrixGame.utility_zero` | focused Core build | Row utility is the matrix entry. |
| same | `toKernelGame_payoff_col` | theorem | adapt | `GameTheory.MatrixGame.utility_one` | focused Core build | Column utility is the negated entry. |
| same | `toKernelGame_eu_row` | theorem | adapt | `GameTheory.MatrixGame.expectedUtility_zero_mixedProfile` | focused Core build | Canonical `expectedUtility` equals the named row payoff. |
| same | `toKernelGame_eu_col` | theorem | adapt | `GameTheory.MatrixGame.expectedUtility_one_mixedProfile` | focused Core build | Zero-sum negation gives the column identity. |
| same | `toKernelGame_isZeroSum` | theorem | adapt | `GameTheory.MatrixGame.utility_isZeroSum` | focused Core build | Direct pointwise sum proof. |
| same | `profilePairEquiv` | def | retired | `GameTheory.MatrixGame.pureProfile` | owner comparison | A direct canonical constructor plus projections replaces the wrapper equivalence. |
| same | `mixedProfile` | def | adapt | `GameTheory.MatrixGame.mixedProfile` | nonconstant matrix fixture | Independent `FinDist` row and column laws form the canonical mixed profile. |
| same | `mixedProfile_zero` | theorem | adapt | same name under `GameTheory.MatrixGame` | focused Core build | Exact row projection. |
| same | `mixedProfile_one` | theorem | adapt | same name under `GameTheory.MatrixGame` | focused Core build | Exact column projection. |
| same | `mixedExtension_eu_row_eq_expectedPayoff` | theorem | adapt | `GameTheory.MatrixGame.expectedUtility_zero_mixedProfile` | focused Core build | No parallel mixed-extension evaluator. |
| same | `mixedExtension_eu_col_eq_neg_expectedPayoff` | theorem | adapt | `GameTheory.MatrixGame.expectedUtility_one_mixedProfile` | focused Core build | No parallel mixed-extension evaluator. |
| same | `IsSaddlePoint` | def | subsumed | `GameTheory.IsSaddlePoint` | D5/Core owner | The canonical two-player mixed-profile predicate is reused unchanged. |
| same | `IsSaddlePoint.row_le` | theorem | subsumed | first projection of `GameTheory.IsSaddlePoint` | source comparison | No duplicate matrix method is needed. |
| same | `IsSaddlePoint.le_col` | theorem | subsumed | second projection of `GameTheory.IsSaddlePoint` | source comparison | No duplicate matrix method is needed. |
| same | `update_mixedProfile_row` | private theorem | adapt | `GameTheory.MatrixGame.mixedProfile_update_zero` | source-transport audit | Uses canonical `Profile.update`; no raw function update. |
| same | `update_mixedProfile_col` | private theorem | adapt | `GameTheory.MatrixGame.mixedProfile_update_one` | source-transport audit | Uses canonical `Profile.update`; no raw function update. |
| same | `mixedNash_iff_isSaddlePoint` | theorem | adapt | `GameTheory.isNash_iff_isSaddlePoint`; `MatrixGame.utility_isZeroSum` | hostile pure saddle/Nash witness | The equivalence is proved once for every two-player zero-sum `GameForm`. |
| same | `kernel_isSaddlePoint_iff_isSaddlePoint` | theorem | retired | one canonical `GameTheory.IsSaddlePoint` | D5 owner comparison | The old statement compared two duplicate saddle predicates. |
| same | `exists_saddlePoint` | theorem | adapt | `GameTheory.exists_isSaddlePoint`; `MatrixGame.valueProfile_isSaddlePoint` | focused Analysis build | Existence stays behind the fixed-point boundary. |
| same | `exists_saddlePoint_pair` | private theorem | subsumed | `MatrixGame.valueProfile` | focused Analysis build | The selected canonical profile already carries both laws. |
| same | `selectedSaddlePoint` | private def | adapt | `GameTheory.MatrixGame.valueProfile` | focused Analysis build | One selected canonical profile. |
| same | `selectedSaddlePoint_isSaddlePoint` | private theorem | adapt | `GameTheory.MatrixGame.valueProfile_isSaddlePoint` | focused Analysis build | Selected-profile certificate. |
| same | `value` | def | adapt | `GameTheory.MatrixGame.value` | D23 live stochastic consumer | Selected from the existing generic minimax theorem. |
| same | `value_eq_of_saddlePoint` | theorem | adapt | `GameTheory.MatrixGame.expectedPayoff_eq_value_of_isSaddlePoint` | hostile value-one fixture | Every canonical saddle realizes the selected value. |
| same | `RowGuarantees` | def | adapt | `GameTheory.MatrixGame.RowGuarantees` | Core reachability probe | Topology-free static predicate. |
| same | `ColumnCaps` | def | adapt | `GameTheory.MatrixGame.ColumnCaps` | Core reachability probe | Topology-free static predicate. |
| same | `IsPlayerIGuarantee` | def | adapt | `GameTheory.MatrixGame.IsRowGuarantee` | hostile common certificate | Clear role-based name. |
| same | `IsPlayerIIGuarantee` | def | adapt | `GameTheory.MatrixGame.IsColumnCap` | hostile common certificate | Clear role-based name. |
| same | `common_guarantee_eq_value` | theorem | adapt | `GameTheory.MatrixGame.common_guarantee_eq_value` | explicit value-one fixture; axiom audit | Opposing certificates squeeze the selected value. |
| same | `optimalRowStrategies` | def | adapt | same name under `GameTheory.MatrixGame` | focused Analysis build | Rows guaranteeing the value. |
| same | `optimalColumnStrategies` | def | adapt | same name under `GameTheory.MatrixGame` | focused Analysis build | Columns capping at the value. |
| same | `mem_optimalRowStrategies_iff_expectedPayoff_ge` | theorem | adapt | `GameTheory.MatrixGame.mem_optimalRowStrategies_iff` | focused Analysis build | Transparent membership theorem. |
| same | `mem_optimalColumnStrategies_iff_expectedPayoff_le` | theorem | adapt | `GameTheory.MatrixGame.mem_optimalColumnStrategies_iff` | focused Analysis build | Transparent membership theorem. |
| same | `optimal_pairs_iff_saddle_point` | theorem | adapt | `GameTheory.MatrixGame.optimal_pairs_iff_isSaddlePoint` | focused Analysis build | Targets the sole saddle predicate. |
| same | `optimal_pairs_iff_mixedNash` | theorem | adapt | `GameTheory.MatrixGame.optimal_pairs_iff_isNash` | hostile saddle/Nash witness | Targets ordinary `IsNash` on the canonical mixed form. |
| same | `optimal_pairs_iff_kernel_saddlePoint` | theorem | retired | `optimal_pairs_iff_isSaddlePoint` | D5 owner comparison | The old second saddle surface is absent. |
| same | `value_eq_mixedExtension_eu_of_mixedNash` | theorem | adapt | `GameTheory.MatrixGame.expectedPayoff_eq_value_of_isNash` | focused Analysis build | Direct canonical payoff/value equality. |
| same | `optimalRowStrategies_nonempty` | theorem | adapt | same name under `GameTheory.MatrixGame` | focused Analysis build; axiom audit | Selected value row supplies the witness. |
| same | `optimalColumnStrategies_nonempty` | theorem | adapt | same name under `GameTheory.MatrixGame` | focused Analysis build; axiom audit | Selected value column supplies the witness. |

Disposition count: 33 adapted, 4 subsumed, 3 retired.

The remaining 11 declarations in the pinned matrix file are deliberately not
claimed here: support complementarity, antisymmetry, and their geometric
corollaries retain separate BFS gates.  The hostile matrix
`![![2, 0], ![3, 1]]` has a strict bottom-row/right-column saddle and forces the
abstract selected value to the nonzero scalar `1` through explicit row and
column security certificates.

Validation: the focused Core/Analysis/stochastic-consumer build completed
3,139 jobs warning-free.  The full reachability audit returned `VERIFIED=1`:
all five Core matrix inputs were reached and all three Analysis-boundary probes
were rejected; all five Analysis value inputs were reached and both
Protocol/Repeated probes were rejected.  The saddle/Nash equivalence,
guarantee/cap characterization, common-value theorem, optimal-row existence,
and hostile value-one witness depend only on `propext`, `Classical.choice`, and
`Quot.sound`.  Exact coverage returned `VERIFIED=1` with all 40 selected rows
accounted for, and the warning-clean default build completed all 3,527 jobs.
