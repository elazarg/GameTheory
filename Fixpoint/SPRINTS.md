# Sprint Log (Fixpoint)

## Sprint 1
Delivered:
- `Fixpoint/ApproximateToExact.lean`
- Theorem: `exists_fixedPoint_of_approx_on_compact`

Measurable outcome:
- Fully checked theorem proving compactness limit step:
  approximate fixed points at scales `1/(n+1)` + continuity => exact fixed point.

## Sprint 2
Delivered:
- `Fixpoint/ProductSimplexCore.lean`
- Definition: `MixedSimplex`
- Theorems:
  - `isCompact_univ_mixedSimplex`
  - `exists_fixedPoint_of_approx_on_mixedSimplex`

Measurable outcome:
- Fixed-point limit engine now applies directly to mixed-profile product simplex domain.

## Sprint 3
Delivered:
- `Fixpoint/BrouwerFromApprox.lean`
- Theorem: `exists_fixedPoint_of_approx_on_stdSimplex`
- Aggregator: `Fixpoint.lean`

Measurable outcome:
- Endgame theorem specialized to `stdSimplex` is done; once Sperner supplies approximate fixed points, Brouwer follows immediately.

## Remaining Critical Path
- Build finite subdivision + admissible labeling machinery.
- Prove Sperner (existence of fully labeled simplex in each refinement).
- Derive approximate fixed points from full labels and mesh bounds.
- Plug into `exists_fixedPoint_of_approx_on_stdSimplex`.
- Transport to mixed Nash map and remove existence axiom in `GameTheory/MixedNashExistence.lean`.

## Sprint 4
Delivered:
- `Fixpoint/GridSimplex.lean`
- Definition: `GridPoint ι m = {w : ι -> ℕ // sum w = m}`
- Construction: `GridPoint.toStdSimplex`

Measurable outcome:
- Formal bridge from integer simplex grids to real simplex points is now proved.
- This is a core building block for subdivision/labeling and Sperner extraction.

## Sprint 5
Delivered:
- `Fixpoint/SpernerLabeling.lean`
- Definitions:
  - `positiveSupport`
  - `argmaxOnPositiveSupport`
  - `spernerLabel`
- Theorems:
  - `positiveSupport_nonempty`
  - `spernerLabel_ne_of_coord_eq_zero`
  - `sum_sub_nonneg_on_positiveSupport`
  - `exists_nonneg_sub_on_positiveSupport`
  - `sub_nonneg_at_spernerLabel`

Measurable outcome:
- Built and LSP-checked a Sperner-compatible labeling core with boundary admissibility and
  nonnegative label displacement.
- This closes a key combinatorial-analysis interface needed for approximate fixed-point extraction.

## Sprint 6
Delivered:
- `Fixpoint/SpernerGridLabel.lean`
- Definition:
  - `gridLabel` (grid-vertex label induced from simplex Sperner label)
- Theorem:
  - `gridLabel_ne_of_coord_eq_zero`

Measurable outcome:
- Boundary admissibility is now transported from simplex points to integer grid vertices.
- This is the exact shape needed to apply Sperner counting on triangulated grids.

## Sprint 7
Delivered:
- `Fixpoint/CoordinateApprox.lean`
- Theorems:
  - `dist_le_of_forall_coord_dist_le`
  - `dist_le_of_forall_coord_abs_sub_le`
  - `hasApproxFixedPoints_of_coordwise_bounds`

Measurable outcome:
- Established a reusable metric bridge from coordinatewise error bounds to
  global approximate fixed-point bounds on `stdSimplex`.

## Sprint 8
Delivered:
- `Fixpoint/UniformCoordControl.lean`
- `Fixpoint/BrouwerFromCoordApprox.lean`
- Theorems:
  - `uniformContinuous_coordDisplacement`
  - `exists_delta_coordDisplacement_lt`
  - `exists_fixedPoint_of_coordwiseApprox_on_stdSimplex`

Measurable outcome:
- Added quantitative continuity control for coordinate displacement maps and
  a direct fixed-point theorem reducing Brouwer to coordinatewise approximants.

## Sprint 9
Delivered:
- Extended `Fixpoint/UniformCoordControl.lean` with:
  - `abs_le_card_mul_of_sum_eq_zero_of_lower_bound`
  - `exists_coordwiseApprox_of_labeled_cluster`
  - `exists_fixedPoint_of_arbitrarilyFine_labeled_clusters`

Measurable outcome:
- Closed a major abstract reduction:
  labeled `δ`-clusters for every `δ > 0` now imply a fixed point, with full proof and no
  axioms/sorries in this layer.

## Sprint 10
Delivered:
- `Fixpoint/KuhnSubdivision.lean`
- `Fixpoint/SpernerParity.lean` (core interfaces + extraction lemmas)
- Theorems:
  - `KuhnSubdivision.dist_toPoint_le_inv_of_coordDiffLeOne`
  - `SpernerParity.exists_reindexed_nonneg_displacement`
  - `SpernerParity.exists_labeled_cluster_le_inv_of_fullyLabeled_mesh`
  - `SpernerParity.exists_cluster_family_at_scales_of_fullyLabeled_mesh`

Measurable outcome:
- Built the combinatorial-to-analytic handoff layer:
  mesh-controlled fully-labeled families now produce scale-indexed labeled clusters in theorem form.

## Sprint 11
Delivered:
- Extended `Fixpoint/UniformCoordControl.lean` with:
  - `exists_fixedPoint_of_labeled_clusters_at_scales`
- Extended `Fixpoint/SpernerParity.lean` with:
  - `labelSet`
  - `fullyLabeled_iff_labelSet_univ`

Measurable outcome:
- Closed the scale-to-`δ` conversion as a standalone theorem.
- Added finite-label-set characterizations useful for future parity/counting proofs.

## Sprint 12
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with:
  - `chainVertex1`
  - `exists_fullyLabeled_pair_dim1`

Measurable outcome:
- Proved a concrete one-dimensional Sperner existence theorem (boundary-admissible labeling
  implies a fully-labeled edge), fully checked with LSP.
- This validates the minimal-index extraction pattern that will be generalized for higher dimensions.

## Sprint 13
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with:
  - `exists_fullyLabeled_pair_dim1_gridLabel`

Measurable outcome:
- Connected the 1D Sperner existence theorem directly to the canonical `gridLabel` used in the
  Brouwer/Nash pipeline.

## Sprint 14
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with general cell abstractions:
  - `Cell`
  - `IsMeshCell`
  - `CellFullyLabeled`
- Theorems:
  - `exists_cluster_le_inv_of_gridLabel_cell`
  - `exists_cluster_family_at_scales_of_gridLabel_cells`

Measurable outcome:
- Strengthened the higher-dimensional handoff layer:
  any fully-labeled mesh cell for `gridLabel` now yields a quantitative `1/m` cluster in a
  reusable theorem form.

## Sprint 15
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with counting/parity extraction helpers:
  - `fullyLabeledCells`
  - `mem_fullyLabeledCells`
  - `exists_of_odd_card_fullyLabeledCells`
  - `exists_cluster_le_inv_of_odd_card_fullyLabeledCells`

Measurable outcome:
- Added the direct odd-cardinality bridge:
  once parity yields an odd number of fully-labeled mesh cells, cluster extraction is immediate.

## Sprint 16
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with:
  - `exists_cluster_family_at_scales_of_odd_card_fullyLabeledCells`

Measurable outcome:
- Reduced the remaining gap to a single combinatorial target:
  prove odd cardinality of fully-labeled mesh cells for each subdivision level.

## Sprint 17
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with:
  - `exists_fixedPoint_of_odd_card_fullyLabeledCells_at_scales`

Measurable outcome:
- Closed the full analytic composition path:
  odd-cardinality fully-labeled mesh-cell data at every scale now implies an
  actual fixed point theorem in one step, using `UniformCoordControl`.
- Remaining blocker is now purely combinatorial:
  construct/prove the odd-cardinality cell family theorem for each subdivision scale.

## Sprint 18
Delivered:
- Extended `Fixpoint/SpernerParity.lean` (dimension 1 combinatorial closure):
  - `chainVertex1_coord0`, `chainVertex1_coord1`
  - `coordDiffLeOne_chainVertex1_pred_succ`
  - `exists_fullyLabeled_mesh_pair_dim1`
  - `exists_fullyLabeled_mesh_pair_dim1_gridLabel`
  - `exists_odd_data_dim1_gridLabel`
  - `exists_fixedPoint_dim1_of_continuous`

Measurable outcome:
- Proved the odd-cardinality-at-scales hypothesis constructively in dimension 1
  (singleton fully-labeled mesh edge at each scale).
- Obtained a full end-to-end fixed-point theorem for `Idx 1` through the same
  odd-cardinality pipeline used for higher dimensions.
- This validates the final-boss composition on a complete nontrivial case; the
  remaining gap is specifically higher-dimensional Sperner parity.

## Sprint 19
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with `ZMod 2` parity infrastructure:
  - `cellFullyLabeledIndicatorZ2`
  - `card_fullyLabeledCells_eq_sum_indicator_zmod2`
  - `card_fullyLabeledCells_eq_one_zmod2_of_weight_parity`
  - `exists_of_card_eq_one_zmod2_fullyLabeledCells`
  - `exists_cluster_le_inv_of_card_eq_one_zmod2_fullyLabeledCells`

Measurable outcome:
- Added a reusable parity-transfer layer for higher-dimensional Sperner:
  if one supplies a mod-2 incidence weight identity, oddness of fully-labeled
  cells now follows immediately in theorem form.
- This converts the remaining high-dimensional blocker into a cleaner target:
  prove the relevant incidence-weight parity identity for Kuhn subdivision cells.

## Sprint 20
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with:
  - `exists_cluster_family_at_scales_of_card_eq_one_zmod2_fullyLabeledCells`
  - `exists_fixedPoint_of_card_eq_one_zmod2_fullyLabeledCells_at_scales`
  - `exists_fixedPoint_of_weightParity_at_scales`

Measurable outcome:
- Completed the `ZMod 2` composition chain all the way to fixed-point existence.
- The final gap is now explicit and minimal: construct per-scale cell families and
  weights satisfying mesh condition, indicator-parity identity, and total parity `= 1`.

## Sprint 21
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with abstract incidence parity machinery:
  - `cellIncidenceCount`
  - `faceIncidenceCount`
  - `sum_cellIncidenceCount_eq_sum_faceIncidenceCount_zmod2`
  - `sum_cellIncidenceCount_eq_one_zmod2_of_faceParity`

Measurable outcome:
- Formalized the core double-counting algebra needed for higher-dimensional Sperner parity.
- Remaining work is now geometric/combinatorial specialization:
  instantiate `cells`, `faces`, and incidence relation `I` for Kuhn subdivision and prove
  the face-parity hypothesis needed by `sum_cellIncidenceCount_eq_one_zmod2_of_faceParity`.

## Sprint 22
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with:
  - `exists_fixedPoint_of_incidenceParity_at_scales`

Measurable outcome:
- Closed the final abstract bridge from incidence-parity hypotheses to fixed-point existence.
- The remaining gap is now fully concrete and local:
  build the Kuhn subdivision incidence package (`cells/faces/I/b`) and prove its parity hypotheses.

## Sprint 23
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with structured parity-data APIs:
  - `IncidenceParityScaleData`
  - `IncidenceParityFamilyData`
  - `exists_fixedPoint_of_incidenceParityFamily`

Measurable outcome:
- Converted the final theorem input from a large nested existential into explicit
  reusable structures.
- Final remaining work is now straightforwardly codable:
  instantiate these structures from Kuhn subdivision and discharge each field proof.

## Sprint 24
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with partitioned-face incidence tools:
  - `sum_cellIncidenceCount_eq_one_zmod2_of_partitionedFaces`
  - `exists_fixedPoint_of_partitionedIncidenceParity_at_scales`

Measurable outcome:
- Matched the formal pipeline to the classic Sperner interior/boundary parity decomposition.
- Remaining work is now exactly the concrete Kuhn proof obligations:
  provide interior/boundary face sets and prove the corresponding parity hypotheses.

## Sprint 25
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with concrete face partition utilities:
  - `IsBoundaryFace`
  - `boundaryFaces`
  - `interiorFaces`
  - `interior_union_boundary_faces`
  - `disjoint_interior_boundary_faces`
  - `exists_fixedPoint_of_boundaryInteriorFaceParity_at_scales`

Measurable outcome:
- Eliminated manual partition bookkeeping from the final theorem interface.
- Remaining gap is now fully geometric:
  construct a Kuhn face family + incidence relation and prove interior parity `0`
  and boundary parity sum `1` under this canonical boundary/interior split.

## Sprint 26
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with Kuhn-facing face/incidence scaffolding:
  - `cellVertices`
  - `cellFacet`
  - `FaceIncidentByFacet`
  - `facetFamily`
  - `mem_facetFamily_iff`
  - `faceIncidentByFacet_of_mem_facetFamily`
  - `mem_boundaryFaces_iff`
  - `mem_interiorFaces_iff`
  - `interior_or_boundary_of_mem_faces`

Measurable outcome:
- Established concrete finite objects for facet-based incidence counting.
- Reduced the remaining implementation task to proving parity-count statements on
  `facetFamily` under `FaceIncidentByFacet`.

## Sprint 27
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with facet-incidence count lemmas:
  - `cellFacet_mem_facetFamily`
  - `cellIncidenceCount_facetFamily_pos`

Measurable outcome:
- Proved each selected cell contributes at least one incident facet in the canonical
  facet-family incidence model.
- This sets up concrete counting arguments needed for the final parity proof.

## Sprint 28
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with:
  - `exists_fixedPoint_of_kuhnFacetParity_at_scales`

Measurable outcome:
- Specialised the final fixed-point bridge to the concrete Kuhn facet model
  (`faces := facetFamily cells`, `incidence := FaceIncidentByFacet`).
- Final gap is now the explicit parity proof obligations for this one concrete model
  (interior facets parity `0`, boundary facet class sum `1`).

## Sprint 29
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with count-to-parity bridges:
  - `faceIncidenceParity_zero_of_even`
  - `faceIncidenceParity_eq_class_of_splitCount`
  - `exists_fixedPoint_of_kuhnFacetCounts_at_scales`

Measurable outcome:
- Reduced final Kuhn obligations from parity equalities to concrete counting equalities:
  prove interior facet counts are even and boundary facet counts decompose as `bit + 2k`.
- This makes the last step fully arithmetic/combinatorial with no remaining parity algebra work.

## Sprint 30
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with additional concrete incidence-count lemmas:
  - `faceIncidenceCount_pos_of_witness`
  - `faceIncidenceCount_facetFamily_pos_of_mem`
- Extended `GameTheory/NashExistenceMixed.lean` with:
  - `mixed_nash_exists_of_nashMap_fixed_point`
  - refactored `mixed_nash_exists` to call the above theorem.

Measurable outcome:
- Tightened the final Kuhn counting toolbox around `facetFamily`.
- Isolated the game-facing dependence on fixed-point existence into a reusable theorem;
  once the constructive fixed-point witness is provided, mixed Nash follows without
  further game-theoretic proof work.

## Sprint 31
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with:
  - `faceIncidence_even_of_eq_two`
  - `exists_fixedPoint_of_kuhnFacetTwoInteriorCounts_at_scales`

Measurable outcome:
- Reduced interior-facet obligations to the strongest common combinatorial statement
  (`faceIncidenceCount = 2`), which now directly feeds the fixed-point pipeline.
- Remaining final obligations are boundary-side count decomposition and sum-`1` proof
  for the concrete Kuhn subdivision.

## Sprint 32
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with boundary-side final-cut reductions:
  - `boundary_sum_one_of_unique_marked_face`
  - `exists_fixedPoint_of_kuhnFacetUniqueBoundaryMark_at_scales`

Measurable outcome:
- Reduced the global boundary sum obligation to a single marked-boundary-face criterion.
- The remaining gap is now fully local and geometric:
  prove interior count `= 2`, boundary split counts, and identify the unique marked
  boundary facet in the concrete Kuhn subdivision.

## Sprint 33
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with most-concrete boundary indicator reduction:
  - `boundaryMarkClass`
  - `exists_fixedPoint_of_kuhnFacetBoundaryIndicator_at_scales`

Measurable outcome:
- Removed free choice of boundary class function `b`; it is now canonically the
  indicator of a single marked boundary facet.
- Remaining gap is narrowed to constructive geometry/counting only:
  produce interior `=2` incidences, boundary split counts against indicator,
  and a witness marked boundary facet in Kuhn subdivision.

## Sprint 34
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with concrete witness-to-count helpers:
  - `faceIncidenceCount_eq_two_of_pair_witness`
  - `faceIncidenceCount_eq_one_of_unique_witness`
  - `faceIncidenceCount_eq_zero_of_no_witness`
  - `splitCount_of_eq_one`
  - `splitCount_of_eq_zero`

Measurable outcome:
- Reduced final counting obligations to local witness patterns (pair/unique/none),
  which are exactly the shape expected from geometric adjacency arguments in Kuhn subdivision.
- This removes remaining arithmetic overhead from the final geometric step.

## Sprint 35
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with further final-cut reductions:
  - `exists_fixedPoint_of_kuhnFacetTwoInteriorCounts_at_scales`
  - `boundary_sum_one_of_unique_marked_face`
  - `boundaryMarkClass`
  - `exists_fixedPoint_of_kuhnFacetBoundaryIndicator_at_scales`

Measurable outcome:
- Reduced global parity obligations to the most concrete indicator-form statement:
  interior counts are exactly `2`, boundary counts split against one marked face indicator.
- Remaining work is now purely geometric witness construction on Kuhn adjacency.

## Sprint 36
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with:
  - `exists_fixedPoint_of_kuhnFacetWitnessPattern_at_scales`

Measurable outcome:
- Collapsed the boundary-indicator/count obligations to explicit local witness data:
  interior faces have exactly two incidence witnesses, one marked boundary face has
  a unique witness, and all other boundary faces have none.
- This eliminates the last arithmetic/count-conversion layer between geometric witness
  construction and the fixed-point conclusion.

## Sprint 37
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with new grid-move primitives:
  - `incrementCoord`
  - `incrementCoord_apply_same`
  - `incrementCoord_apply_other`
  - `abs_sub_le_one_incrementCoord`
- Extended `Fixpoint/SpernerParity.lean` with:
  - `exists_fixedPoint_of_gridLabel_cells_at_scales`

Measurable outcome:
- Added a concrete, LSP-clean combinatorial operation on simplex grid vertices to support
  upcoming canonical-cell constructions.
- Added a direct fixed-point endpoint from per-scale fully-labeled mesh cells, reducing
  future closure work to proving those cells exist for each scale.

## Sprint 38
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with structured witness interface:
  - `KuhnFacetWitnessScaleData`
  - `exists_fixedPoint_of_kuhnFacetWitnessScaleData_at_scales`

Measurable outcome:
- Converted the remaining high-dimensional closure task into a single concrete target:
  build per-scale instances of `KuhnFacetWitnessScaleData`.
- This isolates geometry/incidence construction from the fixed-point endgame and enables
  direct, checkable progress on the final Kuhn witness obligations.

## Sprint 39
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with same-denominator grid move machinery:
  - `decrementCoord`
  - `decrementCoord_apply_same`
  - `decrementCoord_apply_other`
  - `abs_sub_le_one_decrementCoord`
  - `transferUnit`
  - `transferUnit_apply_left`
  - `transferUnit_apply_right`
  - `transferUnit_apply_other`

Measurable outcome:
- Established a compile-checked primitive for moving one lattice unit between coordinates
  while preserving the simplex denominator sum.
- This is a core building block for concrete Kuhn adjacency and facet-incidence witness
  construction required by `KuhnFacetWitnessScaleData`.

## Sprint 40
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with:
  - `coordDiffLeOne_transferUnit`

Measurable outcome:
- Proved that transfer moves are mesh-local (`CoordDiffLeOne`), giving the exact adjacency
  control needed for local Kuhn-cell witness construction.

## Sprint 41
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with concrete local Kuhn-cell scaffolding:
  - `coordDiffLeOne_symm`
  - `coordDiffLeOne_transferUnit_pair`
  - `Cell`
  - `IsMeshCell`
  - `starCell`
  - `starCell_apply_source`
  - `starCell_apply_other`
  - `isMeshCell_starCell`

Measurable outcome:
- Added a canonical mesh cell constructor (`starCell`) and fully proved pairwise mesh
  adjacency among its vertices.
- This gives an immediately usable concrete cell object for assembling scale-indexed
  finite cell families in the remaining `KuhnFacetWitnessScaleData` construction.

## Sprint 42
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with finite rooted cell-family helpers:
  - `positiveCoords`
  - `mem_positiveCoords_iff`
  - `starCellsFrom`
  - `mem_starCellsFrom_iff`
  - `isMeshCell_of_mem_starCellsFrom`

Measurable outcome:
- Built an explicit finite family of concrete Kuhn-style cells from any root grid vertex,
  with a direct membership characterization and mesh guarantee for every member.
- This supplies a concrete, enumerable unit for assembling the final per-scale witness data.

## Sprint 43
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with finite family assembly over root sets:
  - `cellsFromRoots`
  - `mem_cellsFromRoots_iff`
  - `isMeshCell_of_mem_cellsFromRoots`

Measurable outcome:
- Upgraded from single-root star families to arbitrary finite root collections while
  preserving explicit membership decomposition and mesh guarantees.
- This provides the concrete finite-cell container needed to build scale-indexed
  candidate Kuhn families and discharge `mesh` obligations in witness packages.

## Sprint 44
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with concrete scale-level family definitions:
  - `allGridVertices`
  - `cellsAtScale`
  - `isMeshCell_of_mem_cellsAtScale`

Measurable outcome:
- Landed a concrete finite triangulation candidate family at each scale:
  all roots are explicitly enumerated (bounded coordinate functions filtered by total sum),
  and induced cells are guaranteed mesh cells.
- This removes the abstract “unknown finite root set” gap and sets up direct incidence
  counting on a concrete per-scale family.

## Sprint 45
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with enumeration-correctness infrastructure:
  - `boundedVertexCodes`
  - `exactSumCodes`
  - `decodeExactSumCode`
  - `mem_allGridVertices`

Measurable outcome:
- Proved that the concrete finite root enumeration is complete: every grid vertex belongs
  to `allGridVertices`.
- This closes the key soundness/completeness gap for the root-set side of the concrete
  triangulation candidate used by `cellsAtScale`.

## Sprint 46
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with scale-positivity/nonemptiness lemmas:
  - `exists_positiveCoord`
  - `starCellsFrom_nonempty`
  - `cellsAtScale_nonempty`

Measurable outcome:
- Established nonemptiness of rooted and global concrete cell families at every positive
  scale `m`, using explicit root construction.
- This provides concrete existence of cells needed before proving interior/boundary
  incidence witness theorems on `cellsAtScale`.

## Sprint 47
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with facet-side combinatorics primitives:
  - `cellVertices`
  - `cellFacet`
  - `mem_cellVertices_starCell_source`
  - `mem_cellVertices_starCell_transfer`

Measurable outcome:
- Added concrete vertex/facet operators on constructed cells and proved key membership
  lemmas for star-cell vertices (source and transfer vertices).
- This is the direct starting point for explicit facet-incidence witness proofs on
  `cellsAtScale`.

## Sprint 48
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with direct facet-incidence membership lemmas:
  - `source_mem_cellFacet_starCell_of_ne`
  - `transfer_mem_cellFacet_starCell_of_ne`

Measurable outcome:
- Proved concrete membership of source/transfer vertices in star-cell facets under
  explicit index inequalities.
- These are immediate local incidence facts needed to build interior/boundary witness
  arguments for the concrete triangulation family.

## Sprint 49
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with high-value combinatorial incidence lemmas:
  - `starCell_injective`
  - `mem_cellFacet_starCell_iff`
  - `transferUnit_pos_left`
  - `transferUnit_transferUnit_eq`
  - `cellFacet_starCell_source_eq_transfer`

Measurable outcome:
- Closed a core Kuhn-adjacency gap by proving an explicit shared-facet identity between
  neighboring star cells (built from a transfer move).
- This directly enables interior pair-witness construction for facet incidences, moving
  the remaining work from interface setup to concrete witness counting on `cellsAtScale`.

## Sprint 50
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with transfer-cancellation and cell-identity lemmas:
  - `transferUnit_cancel_opposite`
  - `starCell_eq_starCell_transfer_source`

Measurable outcome:
- Proved that the same geometric star cell can be represented from adjacent roots/sources.
- This makes the remaining counting target sharper: interior `=2` witnesses cannot come from
  duplicate star-cell encodings alone and must use genuinely distinct simplices in the final
  Kuhn triangulation layer.

## Sprint 51
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with source-facet uniqueness machinery:
  - `not_mem_cellFacet_starCell_source`
  - `sourceFacet_eq_imp_eq_source`
  - `unique_sourceFacet_incidence_in_starCellsFrom`
  - `faceIncident_sourceFacet_starCell`
  - `unique_sourceFacet_faceIncident_in_starCellsFrom`

Measurable outcome:
- Proved strict uniqueness of source-facet incidence inside rooted star families.
- This gives a concrete, reusable uniqueness block for boundary witness obligations and
  clarifies that the unresolved interior `=2` block requires non-star (genuinely distinct)
  Kuhn simplices.

## Sprint 52
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with a direct unique-witness theorem:
  - `sourceFacet_uniqueWitness_starCellsFrom`

Measurable outcome:
- Produced a ready-to-use `∃ c₀, ... ∀ c, ... → c = c₀` incidence package for source facets
  over rooted star families, matching the shape required by the marked-boundary witness field
  in `KuhnFacetWitnessScaleData`.

## Sprint 53
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with ordered-permutation transfer-chain primitives:
  - `permStepSource`
  - `permStepTarget`
  - `permStep_source_ne_target`
  - `permStepTransfer`
  - `permStepTransfer_pos_target`
  - `permStepSource_succ_eq_permStepTarget`
  - `permTwoStepTransfer`

Measurable outcome:
- Added the first concrete machinery for Kuhn ordered chains where positivity propagates
  step-to-step via `source(r+1) = target(r)`.
- This is the direct technical foundation for constructing genuine permutation simplices
  (distinct cells with shared interior facets), which is the remaining hard block for
  interior pair witnesses.

## Sprint 54
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with recursive full-chain state construction:
  - `permChainStateWithPos`
  - `permChainVertex`
  - `permChainVertex_zero`
  - `permChainVertex_pos_at_index`

Measurable outcome:
- Built a compile-checked recursion that carries positivity at each chain index along
  a permutation-ordered transfer walk from `0` to `n`.
- This removes the main local obstruction to defining full ordered Kuhn simplices:
  we now have a concrete vertex generator with the right positivity invariant available
  at every step.

## Sprint 55
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with permutation-cell recurrence/adjacency lemmas:
  - `permChainVertex_succ_eq_permStepTransfer`
  - `permChainCell`
  - `coordDiffLeOne_permChainCell_succ`

Measurable outcome:
- Proved an explicit one-step recurrence for chain vertices and derived concrete
  consecutive-edge mesh control for permutation cells.
- This is a direct prerequisite for the remaining hard step: proving full pairwise
  mesh (`IsMeshCell`) and then constructing interior two-cell facet witnesses from
  distinct permutation cells.

## Sprint 56
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with stepwise coordinate transition lemmas:
  - `permChainCell_succ_apply_target`
  - `permChainCell_succ_apply_source`
  - `permChainCell_succ_apply_other`

Measurable outcome:
- Made the permutation-cell dynamics explicit at each step: one source coordinate
  decrements, one target increments, all others are unchanged.
- This is the exact local algebra needed to derive closed-form coordinate formulas
  for chain vertices, which is the next required step to prove full pairwise mesh
  and unlock interior pair-witness construction from distinct permutation cells.

## Sprint 57
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with additional recurrence-facing lemmas:
  - `permChainCell_succ_apply_sigma_other`
  - `permChainCell_succ_apply_sigma_cases`
  - `permChainCell_one_apply_sigma0`
  - `permChainCell_succ_apply_sigma0_of_pos`

Measurable outcome:
- Added a single piecewise transition rule at `σ k` plus concrete control of the
  special `σ 0` coordinate (initial drop and subsequent stability for positive steps).
- This narrows the remaining proof to closed-form coordinate characterization and
  final all-pairs mesh bounds for permutation cells.

## Sprint 58
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with a closed-form and quantitative bound for
  the special coordinate:
  - `permChainCell_apply_sigma0_nat`
  - `abs_sub_le_one_permChainCell_sigma0`

Measurable outcome:
- Fully settled the `σ 0` coordinate contribution to mesh bounds:
  explicit time formula and direct `abs ≤ 1` bound between any two chain vertices.
- Remaining mesh work is now concentrated on coordinates `σ k` with `k > 0`.

## Sprint 59
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with core positive-coordinate anchor lemmas:
  - `permChainCell_apply_sigma_pos_of_lt`
  - `permChainCell_apply_sigma_pos_at_self`
  - `permChainCell_apply_sigma_pos_at_succ`

Measurable outcome:
- Established the main `k>0` coordinate milestones:
  baseline before `k`, spike `+1` at `k`, and return to baseline at `k+1`.
- This reduces the remaining positive-coordinate work to extending baseline stability
  for all `t > k+1`, then lifting to global all-pairs `abs ≤ 1`.

## Sprint 60
Delivered:
- Completed the positive-coordinate closure and global mesh package for permutation chains:
  - `permChainCell_apply_sigma_pos_of_ge_succ`
  - `permChainCell_apply_sigma_pos_of_gt`
  - `permChainCell_apply_sigma_pos_nat`
  - `abs_sub_le_one_permChainCell_sigma_pos`
  - `coordDiffLeOne_permChainCell`
  - `isMeshCell_permChainCell`

Measurable outcome:
- Proved full coordinatewise `abs ≤ 1` between any two vertices of a permutation-chain cell,
  then packaged it as `IsMeshCell`.
- This is a decisive closure of the geometric mesh side for non-star (ordered permutation)
  cells and directly advances the interior pair-witness construction target.

## Sprint 61
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with a concrete nondegeneracy lemma:
  - `permChainCell_succ_ne`

Measurable outcome:
- Proved consecutive vertices in permutation-chain cells are distinct.
- This is a direct combinatorial prerequisite for facet-incidence counting with genuinely
  distinct simplices (avoiding degenerate equal-vertex artifacts).

## Sprint 62
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with full vertex nondegeneracy lemmas:
  - `permChainCell_ne_of_lt`
  - `permChainCell_injective`

Measurable outcome:
- Upgraded from local consecutive distinctness to global injectivity of permutation-chain
  vertex maps.
- This gives a concrete tool for future facet/cardinality arguments where distinct
  `(n+1)`-vertex simplex structure must be enforced for incidence counting.

## Sprint 63
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with injective-cell facet combinatorics:
  - `mem_cellFacet_iff`
  - `mem_cellFacet_permChainCell_iff`
  - `cellFacet_ne_of_ne`
  - `cellFacet_permChainCell_ne_of_ne`

Measurable outcome:
- Added the exact finite-set interface needed for incidence counting proofs on
  permutation cells: explicit facet membership (`erase` as indexed-vertex complement)
  and distinct-facet non-collision under injectivity.
- This directly strengthens the remaining `interior 2-incidence` and boundary
  counting steps by removing low-level `Finset`/facet ambiguity.

## Sprint 64
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with cyclic-shifted permutation-chain
  alignment primitives:
  - `permStepSource_mul_finRotate`
  - `permStepTarget_mul_finRotate_of_lt`
  - `permChainCell_pos_at_shiftedSource_zero`

Measurable outcome:
- Established compile-checked step-index identities under `σ * finRotate (n+1)`,
  exactly matching the intended chain shift (`source(r)` aligns with original `target(r)`).
- Added the concrete positivity handoff at the shifted chain root (`t = 1` of the
  original chain), which is the key local precondition for facet-sharing proofs
  between adjacent permutation-chain cells.

## Sprint 65
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with proof-irrelevance lemmas for transfer
  operations:
  - `transferUnit_proof_irrel`
  - `permStepTransfer_proof_irrel`

Measurable outcome:
- Removed a key dependent-argument friction point in chain-alignment proofs:
  transfer results are now explicitly invariant under choice of positivity witness.
- This directly enables rewriting/comparing shifted-vs-original transfer steps
  without being blocked on proof-term mismatch.

## Sprint 66
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with a concrete shifted-step equality:
  - `permStepTransfer_mul_finRotate_zero_eq`

Measurable outcome:
- Proved that (for `n ≥ 2`) step `0` under `σ * finRotate (n+1)` equals step `1`
  under `σ` on the same root vertex, modulo positivity-witness irrelevance.
- This closes the exact algebraic gap needed to align shifted-chain and original-chain
  vertices in the first nontrivial interior-incidence comparison.

## Sprint 67
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with a first shifted-chain vertex-alignment
  corollary:
  - `permChainCell_shifted_one_eq_original_two`

Measurable outcome:
- Proved a concrete chain-level identity (for `n ≥ 2`): after re-rooting at original
  `t=1` and rotating permutation order by `finRotate`, the shifted chain's `t=1` vertex
  equals original `t=2`.
- This is the first compile-checked nontrivial vertex-alignment needed for eventual
  facet equality and interior two-incidence witnesses.

## Sprint 68
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with the full shifted-chain induction layer:
  - `permStepTransfer_congr_root`
  - `permChainCell_shifted_eq_original_succ`

Measurable outcome:
- Closed the core missing induction piece: for all `t < n`, the shifted chain
  (re-rooted at original `t=1` with `σ * finRotate (n+1)`) satisfies
  `shifted[t] = original[t+1]`.
- This is the exact end-to-end alignment needed to turn local step identities into
  facet-level equalities for interior incidence counting.

## Sprint 69
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with a typed corollary of the global shift:
  - `permChainCell_shifted_eq_original_succ_idx`

Measurable outcome:
- Exposed the global alignment in `Fin n` index form (`shifted[k] = original[k+1]`),
  which is the exact shape required for facet-membership and incidence proofs.
- This removes repeated nat/fin coercion overhead in the next facet-equality stage.

## Sprint 70
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with a facet-level shifted/original bridge:
  - `cellFacet_permChainCell_shifted_last_eq_original_zero`

Measurable outcome:
- Proved a concrete shared-facet identity between two distinct permutation-chain
  constructions (original vs shifted/re-rooted):
  shifted facet removing `last` equals original facet removing `0`.
- This is a direct interior-incidence building block: it gives an explicit common
  interior face candidate with two incidence routes.

## Sprint 71
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with incidence-packaged 2-cell witness theorems:
  - `exists_twoIncidence_witness_in_permCellsAtScale`
  - `global_twoIncidence_witness_permCellsAtScale`

Measurable outcome:
- Wrapped the shared-facet construction into `FaceIncidentByFacet`/`facetFamily` form,
  with distinct cells and membership in `permCellsAtScale`.
- Upgraded from one local construction to a quantified global seed-wise statement.

## Sprint 72
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with boundary/assembly packaging:
  - `rooted_sourceFacet_uniqueWitness_in_cellsAtScale`
  - `scale_incidence_boundary_blocks`

Measurable outcome:
- Added a rooted boundary-style unique-witness characterization in `cellsAtScale`.
- Assembled both proved blocks (global 2-incidence + boundary uniqueness) into a
  single scale-level theorem, ready for downstream bridge integration.

## Sprint 73
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with concrete boundary witness extraction:
  - `exists_rootedBoundaryWitness_cellsAtScale`

Measurable outcome:
- Upgraded boundary characterization from schematic quantified form to an explicit
  per-scale existence theorem (`hm > 0`) that constructs a root/index/witness tuple
  inside `cellsAtScale`.
- This provides a concrete marked-boundary seed suitable for downstream final assembly
  without additional existence plumbing.

## Sprint 74
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with one-shot concrete assembly:
  - `scale_incidence_boundary_blocks_concrete`

Measurable outcome:
- Combined:
  1) global two-incidence witness block (`n > 1`), and
  2) explicit rooted boundary witness extraction (`m > 0`)
  into a single scale-level theorem.
- This is the current best local “final assembly” package before translating to
  full `KuhnFacetWitnessScaleData` obligations in `SpernerParity`.

## Sprint 75
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with concrete marked-face packaging and
  source-facet coordinate control:
  - `exists_markedFacet_uniqueWitness_cellsAtScale`
  - `coord_source_eq_sub_one_of_mem_cellFacet_starCell_source`
  - `coord_source_eq_zero_of_mem_cellFacet_starCell_source`

Measurable outcome:
- Upgraded rooted boundary witness output to include an explicit marked face `f0`
  in `facetFamily (cellsAtScale)` together with its unique witness cell.
- Added direct coordinate formulas on source facets, giving the boundary-hyperface
  handle needed for the next step: proving marked-face boundary membership
  (`boundaryFaces`) under concrete coordinate hypotheses.

## Sprint 76
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with a packaged boundary-hyperface criterion:
  - `all_sourceFacet_coords_zero_of_coord_one`

Measurable outcome:
- Lifted pointwise source-facet coordinate control to a whole-face statement:
  when `p_j = 1`, all vertices of `cellFacet (starCell p j hj) j` satisfy `x_j = 0`.
- This is the exact local condition needed to prove `IsBoundaryFace` membership
  once connected to `SpernerParity.boundaryFaces`.

## Sprint 77
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with concrete `p_j = 1` construction and
  a strengthened marked-face package:
  - `exists_coord_eq_one`
  - `exists_markedFacet_coordZero_uniqueWitness_cellsAtScale`

Measurable outcome:
- Added an explicit scale-level witness (`n > 0`, `m > 0`) of a grid vertex with a
  coordinate exactly `1`, built by one `transferUnit` step from a root vertex.
- Upgraded marked-face output with a concrete hyperface condition
  `∀ v ∈ f0, v_j = 0`, i.e. a direct boundary-geometry witness for the marked facet,
  while keeping unique rooted incidence packaging.

## Sprint 78
Delivered:
- Extended `Fixpoint/SpernerParity.lean` with a concrete cross-file boundary bridge:
  - `exists_markedBoundary_uniqueWitness_cellsAtScale_from_kuhn`

Measurable outcome:
- Imported `Fixpoint.KuhnSubdivision` into the parity layer and proved that the
  marked face produced by Kuhn data is not only in `facetFamily`, but actually
  in `SpernerParity.boundaryFaces` via the explicit hyperface witness.
- This closes the local boundary-membership translation gap between subdivision
  witness data and parity-side boundary APIs.

## Sprint 79
Delivered:
- Added direct existence corollary in `Fixpoint/SpernerParity.lean`:
  - `exists_boundaryFace_in_cellsAtScale_from_kuhn`

Measurable outcome:
- Established immediate nonemptiness of boundary faces for Kuhn scale cells
  (`n > 0`, `m > 0`) through the new bridge theorem.
- This removes another packaging step for downstream parity arguments that need
  a concrete `f0 ∈ boundaryFaces (...)` witness.

## Sprint 80
Delivered:
- Added boundary incidence-count strengthening in `Fixpoint/SpernerParity.lean`:
  - `exists_boundaryFace_posIncidence_in_cellsAtScale_from_kuhn`

Measurable outcome:
- Upgraded boundary witness extraction from plain membership
  (`f0 ∈ boundaryFaces`) to strict positive incidence count on `cellsAtScale`.
- This gives direct count-side data feeding the parity/count bridge.

## Sprint 81
Delivered:
- Added hard count-control theorem in `Fixpoint/SpernerParity.lean`:
  - `exists_boundaryFace_countOne_on_rootStarSlice_from_kuhn`

Measurable outcome:
- Constructed an explicit marked boundary face with exact incidence count `1`
  on a concrete rooted slice
  `cellsAtScale.filter (· ∈ starCellsFrom p)`.
- This upgrades boundary data from existence/positivity to an exact cardinality
  statement, which is the right shape for final parity/count assembly.

## Sprint 82
Delivered:
- Added generic and interior-focused count-control tools in `Fixpoint/SpernerParity.lean`:
  - `faceIncidenceCount_eq_two_of_pair_witness_generic`
  - `exists_sharedFacet_countTwo_on_pairSlice_from_kuhn`

Measurable outcome:
- Generalized exact-two incidence counting to arbitrary incidence predicates `I`,
  removing a namespace bottleneck for cross-file Kuhn bridges.
- Proved exact count `2` on a concrete two-cell slice extracted from Kuhn shared-facet
  witnesses in `permCellsAtScale` (`n > 1`, `m > 0`), directly attacking the interior
  side with nontrivial count control.

## Sprint 83
Delivered:
- Added global-family interior lower-bound theorem in `Fixpoint/SpernerParity.lean`:
  - `exists_sharedFacet_countAtLeastTwo_in_permCellsAtScale_from_kuhn`

Measurable outcome:
- Lifted interior evidence from a two-cell slice to the full `permCellsAtScale`
  family: there exists a shared facet in `facetFamily permCellsAtScale` with
  incidence count at least `2`.
- This is a concrete globalization step on the interior side (lower bound proved;
  upper bound / no-third-incidence still pending).

## Sprint 84
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with canonicalization lemmas for
  permutation-scale incidence:
  - `exists_permSeed_of_mem_permCellsAtScale`
  - `exists_permSeed_facetIndex_of_faceIncident_mem_permCellsAtScale`

Measurable outcome:
- Any cell (or incident cell-face pair) in `permCellsAtScale` can now be reduced to
  explicit `(p, σ, i)` chain/facet data.
- This removes ad-hoc unpacking and gives a concrete normal form for the pending
  no-third-incidence interior globalization proof.

## Sprint 85
Delivered:
- Added permutation-facet index elimination/normalization lemmas in
  `Fixpoint/KuhnSubdivision.lean`:
  - `not_mem_cellFacet_permChainCell_zero`
  - `root_mem_cellFacet_permChainCell_of_ne_zero`
  - `facetIndex_eq_zero_of_sameRoot_eq_zeroFacet`
  - `sameRoot_incident_zeroFacet_normalForm`

Measurable outcome:
- For same-root permutation chains, incidence to a `0`-facet now forces the
  incident index to be `0`.
- This directly narrows candidate incident cells in the hard interior
  no-third-incidence step and turns same-root elimination into reusable lemmas.

## Sprint 86
Delivered:
- Added single-family boundary witness theorem in `Fixpoint/SpernerParity.lean`:
  - `exists_boundaryFace_in_permCellsAtScale_from_kuhn`
- Added supporting permutation `0`-facet coordinate lemmas in
  `Fixpoint/KuhnSubdivision.lean`:
  - `permChainCell_apply_sigma0_of_ne_zero`
  - `all_zeroFacet_coords_zero_permChainCell_of_coord_one`

Measurable outcome:
- Established boundary-face existence directly on `permCellsAtScale`, removing the
  family mismatch for this boundary-existence component.
- This is a concrete unification move toward a single-cell-family final bridge.

## Sprint 87
Delivered:
- Repaired and completed the new permutation-chain embedding lemma in
  `Fixpoint/KuhnSubdivision.lean`:
  - `permChainCell_eq_transfer_of_pos`
- Added a `0`-facet transfer normal form in `Fixpoint/KuhnSubdivision.lean`:
  - `mem_cellFacet_permChainCell_zero_iff_transfer`

Measurable outcome:
- For every positive chain index `k`, the chain vertex is now canonically identified
  as one transfer from source `σ 0` to target `σ k` in root `p`.
- This gives a direct closed form for positive-index vertices, which is the exact
  normalization needed for subsequent star-to-perm embedding and incidence-equality
  arguments.
- `0`-facet membership is now normalized directly to transfer witnesses indexed by
  positive chain positions, removing an extra indirection through raw chain vertices.

## Sprint 88
Delivered:
- Added split-integration assembly layer in `Fixpoint/SpernerParity.lean`:
  - `kuhnFacetWitnessScaleData_of_blocks` (direct constructor)
  - `exists_kuhnFacetWitnessScaleData_at_scales_of_blocks` (all-scales constructor)
  - `exists_fixedPoint_of_kuhnBlocks_at_scales` (fixed-point wrapper)

Measurable outcome:
- Interior and boundary proofs can now be developed independently and plugged into
  one stable interface without reworking downstream fixed-point wiring.
- Once both blocks are supplied on a common cell family, the path to
  `exists_fixedPoint_of_kuhnFacetWitnessScaleData_at_scales` is immediate.

## Sprint 89
Delivered:
- Pivoted away from the `KuhnFacetWitnessScaleData` completion route after
  identifying its obligations as structurally unsuitable for nontrivial
  triangulation labeling.
- Removed the temporary SplitAssembly layer from `Fixpoint/SpernerParity.lean`
  (`kuhnFacetWitnessScaleData_of_blocks`, `exists_kuhnFacetWitnessScaleData_at_scales_of_blocks`,
  `exists_fixedPoint_of_kuhnBlocks_at_scales`) to avoid maintaining a dead-end API.

Measurable outcome:
- `Fixpoint/SpernerParity.lean` is back to a clean, compiling state (warnings only)
  with focus returned to the odd-cardinality / incidence-parity pipeline.
- Development target is now aligned with the already-proved
  `exists_fixedPoint_of_odd_card_fullyLabeledCells_at_scales` bridge.

## Sprint 90
Delivered:
- Extended `Fixpoint/KuhnSubdivision.lean` with `cellsAtScale` normalization lemmas:
  - `exists_starSeed_of_mem_cellsAtScale`
  - `exists_starSeed_facetIndex_of_faceIncident_mem_cellsAtScale`

Measurable outcome:
- Any cell in `cellsAtScale` now has a canonical rooted-star decomposition.
- Any incident pair `(c, face)` in `cellsAtScale` can be reduced to explicit
  star-root/source/facet-index data.
- This is the direct normalization layer needed for upcoming interior/boundary
  incidence-sharing proofs on the chosen triangulation family.

## Sprint 91
Delivered:
- Added rooted exact-count lemma in `Fixpoint/SpernerParity.lean`:
  - `faceIncidenceCount_eq_one_on_starCellsFrom_sourceFacet`

Measurable outcome:
- Established exact source-facet incidence count `= 1` on the pure rooted family
  `starCellsFrom p` (no ambient-family filtering needed).
- This gives a reusable local boundary-count primitive for lifting to larger
  finite families in the odd/rainbow counting route.

## Sprint 92
Delivered:
- Added root-slice lift in `Fixpoint/SpernerParity.lean`:
  - `faceIncidenceCount_eq_one_on_cellsAtScale_rootSlice_sourceFacet`

Measurable outcome:
- Proven that exact count `= 1` survives the passage from pure rooted family
  `starCellsFrom p` to the concrete scale-family slice
  `(cellsAtScale).filter (· ∈ starCellsFrom p)`.
- This removes a recurring normalization step in later scale-level boundary
  incidence arguments.

## Sprint 93
Delivered:
- Added rooted-family/filter normalization lemma in `Fixpoint/KuhnSubdivision.lean`:
  - `starCellsFrom_eq_filter_cellsAtScale`

Measurable outcome:
- Canonical identity between `starCellsFrom p` and its `cellsAtScale`-filtered
  form is now available as a reusable theorem.
- This removes repeated ext/filter proof boilerplate in rooted-slice counting
  arguments and tightens the local-to-scale bridge.
