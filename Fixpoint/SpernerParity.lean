import Mathlib
import Fixpoint.GridSimplex
import Fixpoint.SpernerGridLabel
import Fixpoint.UniformCoordControl
import Fixpoint.KuhnSubdivision

set_option autoImplicit false

namespace Fixpoint

namespace SpernerParity

/-- Canonical finite simplex index type of dimension `n`. -/
abbrev Idx (n : ℕ) := Fin (n + 1)

/-- Integer grid vertices for the `n`-simplex with denominator `m`. -/
abbrev GridVertex (n m : ℕ) : Type := GridPoint (Idx n) m

/-- Normalized embedding of a grid vertex into the real standard simplex. -/
noncomputable def toPoint {n m : ℕ} (hm : 0 < m) :
    GridVertex n m → stdSimplex ℝ (Idx n) :=
  GridPoint.toStdSimplex (ι := Idx n) hm

/-- Coordinatewise mesh condition (`<= 1`) between grid vertices. -/
def CoordDiffLeOne {n m : ℕ} (p q : GridVertex n m) : Prop :=
  ∀ i : Idx n, |((p.1 i : ℝ) - (q.1 i : ℝ))| ≤ 1

/-- Under coordinate mesh bound `<= 1`, normalized vertices are at distance `<= 1/m`. -/
theorem dist_toPoint_le_inv_of_coordDiffLeOne
    {n m : ℕ} (hm : 0 < m) (p q : GridVertex n m)
    (hmesh : CoordDiffLeOne p q) :
    dist (toPoint hm p) (toPoint hm q) ≤ (1 : ℝ) / m := by
  have hmRpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hcoord : ∀ i : Idx n,
      dist ((toPoint hm p : Idx n → ℝ) i) ((toPoint hm q : Idx n → ℝ) i) ≤ (1 : ℝ) / m := by
    intro i
    have hmesh_i : |((p.1 i : ℝ) - (q.1 i : ℝ))| ≤ 1 := hmesh i
    have hdiv : |((p.1 i : ℝ) - (q.1 i : ℝ))| / m ≤ 1 / m :=
      div_le_div_of_nonneg_right hmesh_i (le_of_lt hmRpos)
    calc
      dist ((toPoint hm p : Idx n → ℝ) i) ((toPoint hm q : Idx n → ℝ) i)
          = |((p.1 i : ℝ) / m) - ((q.1 i : ℝ) / m)| := by
              simp [toPoint, GridPoint.toStdSimplex_apply, Real.dist_eq]
      _ = |((p.1 i : ℝ) - (q.1 i : ℝ)) / m| := by ring_nf
      _ = |((p.1 i : ℝ) - (q.1 i : ℝ))| / m := by
            rw [abs_div, abs_of_pos hmRpos]
      _ ≤ 1 / m := hdiv
  have hnonneg : 0 ≤ (1 : ℝ) / m := by positivity
  simpa [Subtype.dist_eq] using (dist_pi_le_iff hnonneg).2 hcoord

/-- A labeling on grid vertices of a subdivided simplex. -/
abbrev Labeling (n m : ℕ) : Type := GridVertex n m → Idx n

/-- Boundary admissibility: vertices with zero `i`-coordinate cannot carry label `i`. -/
def BoundaryAdmissible {n m : ℕ} (L : Labeling n m) : Prop :=
  ∀ (p : GridVertex n m) (i : Idx n), p.1 i = 0 → L p ≠ i

/-- Full labeling on a finite vertex family (`Idx n`-indexed). -/
def FullyLabeled {n m : ℕ} (L : Labeling n m) (v : Idx n → GridVertex n m) : Prop :=
  ∀ i : Idx n, ∃ j : Idx n, L (v j) = i

/-- The set of labels realized by a finite vertex family. -/
def labelSet {n m : ℕ} (L : Labeling n m) (v : Idx n → GridVertex n m) : Finset (Idx n) :=
  Finset.univ.image (fun j : Idx n => L (v j))

/-- Equivalent formulation of full labeling using surjectivity. -/
theorem fullyLabeled_iff_surjective {n m : ℕ}
    (L : Labeling n m) (v : Idx n → GridVertex n m) :
    FullyLabeled L v ↔ Function.Surjective (fun j : Idx n => L (v j)) := by
  constructor
  · intro hfull i
    rcases hfull i with ⟨j, hj⟩
    exact ⟨j, hj⟩
  · intro hsurj i
    exact hsurj i

/-- A family is fully-labeled iff its realized label set is all labels. -/
theorem fullyLabeled_iff_labelSet_univ {n m : ℕ}
    (L : Labeling n m) (v : Idx n → GridVertex n m) :
    FullyLabeled L v ↔ labelSet L v = Finset.univ := by
  constructor
  · intro hfull
    refine Finset.eq_univ_iff_forall.2 ?_
    intro i
    rcases hfull i with ⟨j, hj⟩
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ j, hj⟩
  · intro hset i
    have hi : i ∈ labelSet L v := by simp [hset]
    rcases Finset.mem_image.1 hi with ⟨j, _hjU, hj⟩
    exact ⟨j, hj⟩

/-- For `Idx n`, full labeling makes the label map a bijection. -/
theorem fullyLabeled_bijective_labelMap {n m : ℕ}
    (L : Labeling n m) (v : Idx n → GridVertex n m)
    (hfull : FullyLabeled L v) :
    Function.Bijective (fun j : Idx n => L (v j)) := by
  have hsurj : Function.Surjective (fun j : Idx n => L (v j)) :=
    (fullyLabeled_iff_surjective L v).1 hfull
  have hinj : Function.Injective (fun j : Idx n => L (v j)) :=
    (Finite.injective_iff_surjective).2 hsurj
  exact ⟨hinj, hsurj⟩

/-- A permutation induced by full labeling. -/
noncomputable def labelEquivOfFullyLabeled {n m : ℕ}
    (L : Labeling n m) (v : Idx n → GridVertex n m)
    (hfull : FullyLabeled L v) : Idx n ≃ Idx n :=
  Equiv.ofBijective (fun j : Idx n => L (v j)) (fullyLabeled_bijective_labelMap L v hfull)

@[simp] theorem labelEquivOfFullyLabeled_apply {n m : ℕ}
    (L : Labeling n m) (v : Idx n → GridVertex n m)
    (hfull : FullyLabeled L v) (j : Idx n) :
    labelEquivOfFullyLabeled L v hfull j = L (v j) := rfl

/-- From a fully-labeled family, choose an index per label. -/
theorem exists_label_selector {n m : ℕ}
    (L : Labeling n m) (v : Idx n → GridVertex n m)
    (hfull : FullyLabeled L v) :
    ∃ σ : Idx n → Idx n, ∀ i : Idx n, L (v (σ i)) = i := by
  classical
  refine ⟨fun i => Classical.choose (hfull i), ?_⟩
  intro i
  exact Classical.choose_spec (hfull i)

/-- Reindexing preserves pairwise distance bounds on normalized points. -/
theorem pairwise_dist_lt_reindex {n m : ℕ} (hm : 0 < m)
    (v : Idx n → GridVertex n m) (σ : Idx n → Idx n) {δ : ℝ}
    (hpair : ∀ i j : Idx n,
      dist (toPoint hm (v i)) (toPoint hm (v j)) < δ) :
    ∀ i j : Idx n,
      dist (toPoint hm (v (σ i))) (toPoint hm (v (σ j))) < δ := by
  intro i j
  exact hpair (σ i) (σ j)

/-- The canonical `gridLabel` is boundary-admissible. -/
theorem boundaryAdmissible_gridLabel
    {n m : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hm : 0 < m) :
    BoundaryAdmissible (fun p : GridVertex n m => gridLabel f hm p) := by
  intro p i hpi
  exact gridLabel_ne_of_coord_eq_zero (f := f) hm p i hpi

/-- From full labeling, pick one vertex per label with nonnegative own-coordinate displacement. -/
theorem exists_reindexed_nonneg_displacement
    {n m : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hm : 0 < m) (v : Idx n → GridVertex n m)
    (hfull : FullyLabeled (fun p : GridVertex n m => gridLabel f hm p) v) :
    ∃ σ : Idx n → Idx n,
      ∀ i : Idx n,
        0 ≤ (toPoint hm (v (σ i))) i - f (toPoint hm (v (σ i))) i := by
  rcases exists_label_selector (L := fun p : GridVertex n m => gridLabel f hm p) v hfull
    with ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro i
  have hraw :
      0 ≤
        (toPoint hm (v (σ i))) (gridLabel f hm (v (σ i)))
          - f (toPoint hm (v (σ i))) (gridLabel f hm (v (σ i))) := by
    simpa [gridLabel] using
      (sub_nonneg_at_spernerLabel
        (f := f)
        (x := toPoint hm (v (σ i))))
  simpa [hσ i] using hraw

/-- Reindexed fully-labeled family yields a cluster with own-coordinate nonnegative displacement. -/
theorem exists_labeled_cluster_of_fullyLabeled
    {n m : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hm : 0 < m) (v : Idx n → GridVertex n m)
    {δ : ℝ}
    (hpair : ∀ i j : Idx n, dist (toPoint hm (v i)) (toPoint hm (v j)) < δ)
    (hfull : FullyLabeled (fun p : GridVertex n m => gridLabel f hm p) v) :
    ∃ x : Idx n → stdSimplex ℝ (Idx n),
      (∀ i j : Idx n, dist (x i) (x j) < δ) ∧
      (∀ i : Idx n, 0 ≤ x i i - f (x i) i) := by
  rcases exists_reindexed_nonneg_displacement (f := f) hm v hfull with ⟨σ, hnonneg⟩
  refine ⟨fun i => toPoint hm (v (σ i)), ?_, ?_⟩
  · intro i j
    exact hpair (σ i) (σ j)
  · intro i
    simpa using hnonneg i

/-- Mesh-controlled fully-labeled families yield clusters at scale `<= 1/m`. -/
theorem exists_labeled_cluster_le_inv_of_fullyLabeled_mesh
    {n m : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hm : 0 < m) (v : Idx n → GridVertex n m)
    (hmesh : ∀ i j : Idx n, CoordDiffLeOne (v i) (v j))
    (hfull : FullyLabeled (fun p : GridVertex n m => gridLabel f hm p) v) :
    ∃ x : Idx n → stdSimplex ℝ (Idx n),
      (∀ i j : Idx n, dist (x i) (x j) ≤ (1 : ℝ) / m) ∧
      (∀ i : Idx n, 0 ≤ x i i - f (x i) i) := by
  rcases exists_reindexed_nonneg_displacement (f := f) hm v hfull with ⟨σ, hnonneg⟩
  refine ⟨fun i => toPoint hm (v (σ i)), ?_, ?_⟩
  · intro i j
    exact dist_toPoint_le_inv_of_coordDiffLeOne hm (v (σ i)) (v (σ j)) (hmesh (σ i) (σ j))
  · intro i
    simpa using hnonneg i

/--
If each subdivision level `m` provides a mesh-controlled fully-labeled family,
then we obtain labeled clusters at all scales `1/m`.
-/
theorem exists_cluster_family_at_scales_of_fullyLabeled_mesh
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hfam :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ v : Idx n → GridVertex n m,
          (∀ i j : Idx n, CoordDiffLeOne (v i) (v j)) ∧
          FullyLabeled (fun p : GridVertex n m => gridLabel f hm p) v) :
    ∀ m : ℕ, 0 < m →
      ∃ x : Idx n → stdSimplex ℝ (Idx n),
        (∀ i j : Idx n, dist (x i) (x j) ≤ (1 : ℝ) / m) ∧
        (∀ i : Idx n, 0 ≤ x i i - f (x i) i) := by
  intro m hm
  rcases hfam m hm with ⟨v, hmesh, hfull⟩
  exact exists_labeled_cluster_le_inv_of_fullyLabeled_mesh (f := f) hm v hmesh hfull

section Cell

/-- A candidate `n`-simplex cell represented by `n+1` grid vertices. -/
abbrev Cell (n m : ℕ) : Type := Idx n → GridVertex n m

/-- Mesh condition for a cell: all vertex pairs differ by at most one per coordinate. -/
def IsMeshCell {n m : ℕ} (c : Cell n m) : Prop :=
  ∀ i j : Idx n, CoordDiffLeOne (c i) (c j)

/-- Labeling is full on a cell when every label appears among its vertices. -/
def CellFullyLabeled {n m : ℕ} (L : Labeling n m) (c : Cell n m) : Prop :=
  FullyLabeled L c

/-- A fully-labeled mesh cell for `gridLabel` yields a quantitative cluster at scale `1/m`. -/
theorem exists_cluster_le_inv_of_gridLabel_cell
    {n m : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hm : 0 < m) (c : Cell n m)
    (hmesh : IsMeshCell c)
    (hfull : CellFullyLabeled (fun p : GridVertex n m => gridLabel f hm p) c) :
    ∃ x : Idx n → stdSimplex ℝ (Idx n),
      (∀ i j : Idx n, dist (x i) (x j) ≤ (1 : ℝ) / m) ∧
      (∀ i : Idx n, 0 ≤ x i i - f (x i) i) := by
  exact exists_labeled_cluster_le_inv_of_fullyLabeled_mesh (f := f) hm c hmesh hfull

/-- Scale-indexed fully-labeled mesh cells for `gridLabel` produce scale-indexed clusters. -/
theorem exists_cluster_family_at_scales_of_gridLabel_cells
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcell :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ c : Cell n m,
          IsMeshCell c ∧
          CellFullyLabeled (fun p : GridVertex n m => gridLabel f hm p) c) :
    ∀ m : ℕ, 0 < m →
      ∃ x : Idx n → stdSimplex ℝ (Idx n),
        (∀ i j : Idx n, dist (x i) (x j) ≤ (1 : ℝ) / m) ∧
        (∀ i : Idx n, 0 ≤ x i i - f (x i) i) := by
  intro m hm
  rcases hcell m hm with ⟨c, hcmesh, hcfull⟩
  exact exists_cluster_le_inv_of_gridLabel_cell (f := f) hm c hcmesh hcfull

/--
Fully-labeled mesh cells at every scale for `gridLabel` imply a fixed point.
-/
theorem exists_fixedPoint_of_gridLabel_cells_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (hcell :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ c : Cell n m,
          IsMeshCell c ∧
          CellFullyLabeled (fun p : GridVertex n m => gridLabel f hm p) c) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  exact exists_fixedPoint_of_labeled_clusters_at_scales (ι := Idx n) (f := f) hcont
    (exists_cluster_family_at_scales_of_gridLabel_cells (f := f) hcell)

/-- Finset of fully-labeled cells among a finite cell family. -/
noncomputable def fullyLabeledCells {n m : ℕ}
    (L : Labeling n m) (cells : Finset (Cell n m)) : Finset (Cell n m) :=
  by
    classical
    let hdec : DecidablePred (fun c : Cell n m => CellFullyLabeled L c) := Classical.decPred _
    exact cells.filter (fun c => CellFullyLabeled L c)

/-- `ZMod 2` indicator of full labeling on a cell. -/
noncomputable def cellFullyLabeledIndicatorZ2 {n m : ℕ}
    (L : Labeling n m) : Cell n m → ZMod 2 := by
  classical
  exact fun c => if CellFullyLabeled L c then 1 else 0

@[simp] theorem mem_fullyLabeledCells {n m : ℕ}
    (L : Labeling n m) (cells : Finset (Cell n m)) (c : Cell n m) :
    c ∈ fullyLabeledCells L cells ↔ c ∈ cells ∧ CellFullyLabeled L c := by
  classical
  simp [fullyLabeledCells]

/--
Mod-2 cardinality of fully-labeled cells as an indicator sum over a finite cell family.
-/
theorem card_fullyLabeledCells_eq_sum_indicator_zmod2 {n m : ℕ}
    (L : Labeling n m) (cells : Finset (Cell n m)) :
    ((fullyLabeledCells L cells).card : ZMod 2)
      = Finset.sum cells (fun c => cellFullyLabeledIndicatorZ2 L c) := by
  classical
  calc
    ((fullyLabeledCells L cells).card : ZMod 2)
        = Finset.sum (fullyLabeledCells L cells) (fun _ => (1 : ZMod 2)) := by simp
    _ = Finset.sum cells (fun c => cellFullyLabeledIndicatorZ2 L c) := by
          simp [fullyLabeledCells, cellFullyLabeledIndicatorZ2]

/--
Parity-transfer principle:
if a weight function has the same mod-2 parity as the fully-labeled indicator on each cell,
then its total mod-2 sum determines fully-labeled-cell parity.
-/
theorem card_fullyLabeledCells_eq_one_zmod2_of_weight_parity {n m : ℕ}
    (L : Labeling n m) (cells : Finset (Cell n m)) (w : Cell n m → ℕ)
    (hpar :
      ∀ c ∈ cells, ((w c : ZMod 2) = cellFullyLabeledIndicatorZ2 L c))
    (hsum : Finset.sum cells (fun c => (w c : ZMod 2)) = 1) :
    ((fullyLabeledCells L cells).card : ZMod 2) = 1 := by
  have hind :
      Finset.sum cells (fun c => cellFullyLabeledIndicatorZ2 L c)
        = Finset.sum cells (fun c => (w c : ZMod 2)) := by
    refine Finset.sum_congr rfl ?_
    intro c hc
    symm
    exact hpar c hc
  calc
    ((fullyLabeledCells L cells).card : ZMod 2)
        = Finset.sum cells (fun c => cellFullyLabeledIndicatorZ2 L c) :=
          card_fullyLabeledCells_eq_sum_indicator_zmod2 L cells
    _ = Finset.sum cells (fun c => (w c : ZMod 2)) := hind
    _ = 1 := hsum

/--
Existence of a fully-labeled cell from mod-2 cardinality equality in `ZMod 2`.
-/
theorem exists_of_card_eq_one_zmod2_fullyLabeledCells {n m : ℕ}
    (L : Labeling n m) (cells : Finset (Cell n m))
    (hodd : ((fullyLabeledCells L cells).card : ZMod 2) = 1) :
    ∃ c, c ∈ cells ∧ CellFullyLabeled L c := by
  classical
  have hcard_ne_zero : (fullyLabeledCells L cells).card ≠ 0 := by
    intro hzero
    have hcast0 : ((fullyLabeledCells L cells).card : ZMod 2) = 0 := by simp [hzero]
    have : (0 : ZMod 2) = 1 := by
      rw [hcast0] at hodd
      exact hodd
    exact zero_ne_one this
  rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hcard_ne_zero) with ⟨c, hc⟩
  exact ⟨c, (mem_fullyLabeledCells L cells c).1 hc⟩

/-- If the number of fully-labeled cells is odd, then at least one exists. -/
theorem exists_of_odd_card_fullyLabeledCells {n m : ℕ}
    (L : Labeling n m) (cells : Finset (Cell n m))
    (hodd : (fullyLabeledCells L cells).card % 2 = 1) :
    ∃ c, c ∈ cells ∧ CellFullyLabeled L c := by
  classical
  have hcard_pos : 0 < (fullyLabeledCells L cells).card := by
    have hmod_pos : 0 < (fullyLabeledCells L cells).card % 2 := by
      simp [hodd]
    exact Nat.pos_of_ne_zero (by
      intro hzero
      simp [hzero] at hmod_pos)
  rcases Finset.card_pos.mp hcard_pos with ⟨c, hc⟩
  exact ⟨c, (mem_fullyLabeledCells L cells c).1 hc⟩

/--
Odd-cell cluster extraction from mod-2 fully-labeled-cardinality equality in `ZMod 2`.
-/
theorem exists_cluster_le_inv_of_card_eq_one_zmod2_fullyLabeledCells
    {n m : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hm : 0 < m) (cells : Finset (Cell n m))
    (hmeshFam : ∀ c ∈ cells, IsMeshCell c)
    (hodd :
      ((fullyLabeledCells (fun p : GridVertex n m => gridLabel f hm p) cells).card : ZMod 2) = 1) :
    ∃ x : Idx n → stdSimplex ℝ (Idx n),
      (∀ i j : Idx n, dist (x i) (x j) ≤ (1 : ℝ) / m) ∧
      (∀ i : Idx n, 0 ≤ x i i - f (x i) i) := by
  rcases exists_of_card_eq_one_zmod2_fullyLabeledCells
      (L := fun p : GridVertex n m => gridLabel f hm p) cells hodd with
      ⟨c, hcMem, hcFull⟩
  exact exists_cluster_le_inv_of_gridLabel_cell (f := f) hm c (hmeshFam c hcMem) hcFull

/--
Scale-indexed mod-2 cardinality assumptions yield scale-indexed quantitative clusters.
-/
theorem exists_cluster_family_at_scales_of_card_eq_one_zmod2_fullyLabeledCells
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
          (∀ c ∈ cells, IsMeshCell c) ∧
          ((fullyLabeledCells
              (fun p : GridVertex n m => gridLabel f hm p) cells).card : ZMod 2) = 1) :
    ∀ m : ℕ, 0 < m →
      ∃ x : Idx n → stdSimplex ℝ (Idx n),
        (∀ i j : Idx n, dist (x i) (x j) ≤ (1 : ℝ) / m) ∧
        (∀ i : Idx n, 0 ≤ x i i - f (x i) i) := by
  intro m hm
  rcases hdata m hm with ⟨cells, hmeshFam, hodd⟩
  exact exists_cluster_le_inv_of_card_eq_one_zmod2_fullyLabeledCells (f := f) hm cells hmeshFam hodd

/--
Final composition for the mod-2 parity route:
`ZMod 2` oddness of fully-labeled mesh cells at all scales implies a fixed point.
-/
theorem exists_fixedPoint_of_card_eq_one_zmod2_fullyLabeledCells_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
          (∀ c ∈ cells, IsMeshCell c) ∧
          ((fullyLabeledCells
              (fun p : GridVertex n m => gridLabel f hm p) cells).card : ZMod 2) = 1) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  exact exists_fixedPoint_of_labeled_clusters_at_scales (ι := Idx n) (f := f) hcont
    (exists_cluster_family_at_scales_of_card_eq_one_zmod2_fullyLabeledCells (f := f) hdata)

/--
Combinatorial parity package:
if each scale provides cell-weights whose parity matches full-label indicators
and whose total mod-2 sum is `1`, then `f` has a fixed point.
-/
theorem exists_fixedPoint_of_weightParity_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m), ∃ w : Cell n m → ℕ,
          (∀ c ∈ cells, IsMeshCell c) ∧
          (∀ c ∈ cells,
            ((w c : ZMod 2) =
              cellFullyLabeledIndicatorZ2
                (fun p : GridVertex n m => gridLabel f hm p) c)) ∧
          Finset.sum cells (fun c => (w c : ZMod 2)) = 1) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_card_eq_one_zmod2_fullyLabeledCells_at_scales
    (f := f) hcont ?_
  intro m hm
  rcases hdata m hm with ⟨cells, w, hmesh, hpar, hsum⟩
  refine ⟨cells, hmesh, ?_⟩
  exact card_fullyLabeledCells_eq_one_zmod2_of_weight_parity
    (L := fun p : GridVertex n m => gridLabel f hm p) cells w hpar hsum

section IncidenceParity

variable {α β : Type*}

/-- Number of incident faces in `faces` for a given cell `c`. -/
noncomputable def cellIncidenceCount
    (faces : Finset β) (I : α → β → Prop) (c : α) : ℕ := by
  classical
  let hdec : DecidablePred (fun f : β => I c f) := Classical.decPred _
  exact (faces.filter fun f => I c f).card

/-- Number of incident cells in `cells` for a given face `f`. -/
noncomputable def faceIncidenceCount
    (cells : Finset α) (I : α → β → Prop) (f : β) : ℕ := by
  classical
  let hdec : DecidablePred (fun c : α => I c f) := Classical.decPred _
  exact (cells.filter fun c => I c f).card

/--
Mod-2 double-counting identity:
sum of cell incidences equals sum of face incidences.
-/
theorem sum_cellIncidenceCount_eq_sum_faceIncidenceCount_zmod2
    (cells : Finset α) (faces : Finset β) (I : α → β → Prop) :
    Finset.sum cells (fun c => (cellIncidenceCount faces I c : ZMod 2))
      = Finset.sum faces (fun f => (faceIncidenceCount cells I f : ZMod 2)) := by
  classical
  calc
    Finset.sum cells (fun c => (cellIncidenceCount faces I c : ZMod 2))
        = Finset.sum cells (fun c =>
            Finset.sum faces (fun f => if I c f then (1 : ZMod 2) else 0)) := by
            simp [cellIncidenceCount]
    _ = Finset.sum faces (fun f =>
          Finset.sum cells (fun c => if I c f then (1 : ZMod 2) else 0)) := by
          rw [Finset.sum_comm]
    _ = Finset.sum faces (fun f => (faceIncidenceCount cells I f : ZMod 2)) := by
          simp [faceIncidenceCount]

/--
If face-incidence parity is prescribed by `b` and `b` sums to `1`,
then total cell-incidence parity is `1`.
-/
theorem sum_cellIncidenceCount_eq_one_zmod2_of_faceParity
    (cells : Finset α) (faces : Finset β) (I : α → β → Prop)
    (b : β → ZMod 2)
    (hface : ∀ f ∈ faces, ((faceIncidenceCount cells I f : ZMod 2) = b f))
    (hbsum : Finset.sum faces b = 1) :
    Finset.sum cells (fun c => (cellIncidenceCount faces I c : ZMod 2)) = 1 := by
  have hfaceSum :
      Finset.sum faces (fun f => (faceIncidenceCount cells I f : ZMod 2))
        = Finset.sum faces b := by
    refine Finset.sum_congr rfl ?_
    intro f hf
    exact hface f hf
  calc
    Finset.sum cells (fun c => (cellIncidenceCount faces I c : ZMod 2))
        = Finset.sum faces (fun f => (faceIncidenceCount cells I f : ZMod 2)) :=
          sum_cellIncidenceCount_eq_sum_faceIncidenceCount_zmod2 cells faces I
    _ = Finset.sum faces b := hfaceSum
    _ = 1 := hbsum

/--
Partitioned-face parity variant of incidence double counting.

If `faces` is split into disjoint `interior ∪ boundary`, with:
- even incidence parity (`0`) on all interior faces,
- prescribed parity class `b` on boundary faces summing to `1`,
then total cell-incidence parity is `1`.
-/
theorem sum_cellIncidenceCount_eq_one_zmod2_of_partitionedFaces
    [DecidableEq β]
    (cells : Finset α) (faces interior boundary : Finset β)
    (I : α → β → Prop) (b : β → ZMod 2)
    (hcover : faces = interior ∪ boundary)
    (hdisj : Disjoint interior boundary)
    (hinterior : ∀ face ∈ interior, (faceIncidenceCount cells I face : ZMod 2) = 0)
    (hboundary : ∀ face ∈ boundary, (faceIncidenceCount cells I face : ZMod 2) = b face)
    (hbsum : Finset.sum boundary b = 1) :
    Finset.sum cells (fun c => (cellIncidenceCount faces I c : ZMod 2)) = 1 := by
  have hdouble :
      Finset.sum cells (fun c => (cellIncidenceCount faces I c : ZMod 2))
        = Finset.sum faces (fun f => (faceIncidenceCount cells I f : ZMod 2)) :=
    sum_cellIncidenceCount_eq_sum_faceIncidenceCount_zmod2 cells faces I
  have hsplit :
      Finset.sum faces (fun f => (faceIncidenceCount cells I f : ZMod 2))
        = Finset.sum interior (fun f => (faceIncidenceCount cells I f : ZMod 2))
          + Finset.sum boundary (fun f => (faceIncidenceCount cells I f : ZMod 2)) := by
    subst hcover
    simpa using (Finset.sum_union hdisj)
  have hinterior0 :
      Finset.sum interior (fun f => (faceIncidenceCount cells I f : ZMod 2)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro face hface
    exact hinterior face hface
  have hboundary1 :
      Finset.sum boundary (fun f => (faceIncidenceCount cells I f : ZMod 2)) = 1 := by
    calc
      Finset.sum boundary (fun f => (faceIncidenceCount cells I f : ZMod 2))
          = Finset.sum boundary b := by
              refine Finset.sum_congr rfl ?_
              intro face hface
              exact hboundary face hface
      _ = 1 := hbsum
  calc
    Finset.sum cells (fun c => (cellIncidenceCount faces I c : ZMod 2))
        = Finset.sum faces (fun f => (faceIncidenceCount cells I f : ZMod 2)) := hdouble
    _ = Finset.sum interior (fun f => (faceIncidenceCount cells I f : ZMod 2))
          + Finset.sum boundary (fun f => (faceIncidenceCount cells I f : ZMod 2)) := hsplit
    _ = 0 + 1 := by rw [hinterior0, hboundary1]
    _ = 1 := by simp

end IncidenceParity

/--
A finite face (represented as a finite set of grid vertices) is boundary if all
its vertices lie on some coordinate hyperface `x_i = 0`.
-/
def IsBoundaryFace {n m : ℕ}
    (face : Finset (GridVertex n m)) : Prop :=
  ∃ i : Idx n, ∀ v ∈ face, v.1 i = 0

/-- Boundary-part of a finite face family. -/
noncomputable def boundaryFaces {n m : ℕ}
    (faces : Finset (Finset (GridVertex n m))) : Finset (Finset (GridVertex n m)) := by
  classical
  let hdec :
      DecidablePred (fun f : Finset (GridVertex n m) => IsBoundaryFace f) := Classical.decPred _
  exact faces.filter (fun f => IsBoundaryFace f)

/-- Interior-part of a finite face family (complement of boundary faces inside `faces`). -/
noncomputable def interiorFaces {n m : ℕ}
    (faces : Finset (Finset (GridVertex n m))) : Finset (Finset (GridVertex n m)) := by
  classical
  let hdec :
      DecidablePred (fun f : Finset (GridVertex n m) => IsBoundaryFace f) := Classical.decPred _
  exact faces.filter (fun f => ¬ IsBoundaryFace f)

@[simp] theorem mem_boundaryFaces_iff {n m : ℕ}
    (faces : Finset (Finset (GridVertex n m))) (face : Finset (GridVertex n m)) :
    face ∈ boundaryFaces faces ↔ face ∈ faces ∧ IsBoundaryFace face := by
  classical
  simp [boundaryFaces]

@[simp] theorem mem_interiorFaces_iff {n m : ℕ}
    (faces : Finset (Finset (GridVertex n m))) (face : Finset (GridVertex n m)) :
    face ∈ interiorFaces faces ↔ face ∈ faces ∧ ¬ IsBoundaryFace face := by
  classical
  simp [interiorFaces]

/-- `interiorFaces` and `boundaryFaces` partition a finite face family. -/
theorem interior_union_boundary_faces {n m : ℕ}
    (faces : Finset (Finset (GridVertex n m))) :
    interiorFaces faces ∪ boundaryFaces faces = faces := by
  classical
  ext face
  constructor
  · intro hmem
    exact (Finset.mem_union.1 hmem).elim
      (fun hInt => (Finset.mem_filter.1 hInt).1)
      (fun hBnd => (Finset.mem_filter.1 hBnd).1)
  · intro hmem
    by_cases h : IsBoundaryFace face
    · exact Finset.mem_union.2 <| Or.inr (Finset.mem_filter.2 ⟨hmem, h⟩)
    · exact Finset.mem_union.2 <| Or.inl (Finset.mem_filter.2 ⟨hmem, h⟩)

/-- The partition pieces `interiorFaces` and `boundaryFaces` are disjoint. -/
theorem disjoint_interior_boundary_faces {n m : ℕ}
    (faces : Finset (Finset (GridVertex n m))) :
    Disjoint (interiorFaces faces) (boundaryFaces faces) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro face hInt hBnd
  have hNot : ¬ IsBoundaryFace face := (Finset.mem_filter.1 hInt).2
  have hYes : IsBoundaryFace face := (Finset.mem_filter.1 hBnd).2
  exact hNot hYes

theorem interior_or_boundary_of_mem_faces {n m : ℕ}
    {faces : Finset (Finset (GridVertex n m))}
    {face : Finset (GridVertex n m)}
    (hface : face ∈ faces) :
    face ∈ interiorFaces faces ∨ face ∈ boundaryFaces faces := by
  classical
  by_cases hB : IsBoundaryFace face
  · right
    exact (mem_boundaryFaces_iff faces face).2 ⟨hface, hB⟩
  · left
    exact (mem_interiorFaces_iff faces face).2 ⟨hface, hB⟩

section KuhnIncidence

/-- Finite vertex-set of a cell. -/
noncomputable def cellVertices {n m : ℕ}
    (c : Cell n m) : Finset (GridVertex n m) := by
  classical
  exact Finset.univ.image c

/-- Facet obtained by removing the `i`-th vertex from a cell's vertex-set. -/
noncomputable def cellFacet {n m : ℕ}
    (c : Cell n m) (i : Idx n) : Finset (GridVertex n m) := by
  classical
  exact (cellVertices c).erase (c i)

/-- Incidence relation: a face is a facet of a cell. -/
def FaceIncidentByFacet {n m : ℕ}
    (c : Cell n m) (face : Finset (GridVertex n m)) : Prop :=
  ∃ i : Idx n, cellFacet c i = face

/-- The facet family generated by a finite set of cells. -/
noncomputable def facetFamily {n m : ℕ}
    (cells : Finset (Cell n m)) : Finset (Finset (GridVertex n m)) := by
  classical
  exact cells.biUnion (fun c => Finset.univ.image (fun i : Idx n => cellFacet c i))

theorem mem_facetFamily_iff {n m : ℕ}
    (cells : Finset (Cell n m)) (face : Finset (GridVertex n m)) :
    face ∈ facetFamily cells
      ↔ ∃ c ∈ cells, ∃ i : Idx n, cellFacet c i = face := by
  classical
  constructor
  · intro hface
    rcases Finset.mem_biUnion.1 hface with ⟨c, hc, hmem⟩
    rcases Finset.mem_image.1 hmem with ⟨i, _hi, hEq⟩
    exact ⟨c, hc, i, hEq⟩
  · rintro ⟨c, hc, i, hEq⟩
    refine Finset.mem_biUnion.2 ?_
    refine ⟨c, hc, ?_⟩
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, hEq⟩

theorem faceIncidentByFacet_of_mem_facetFamily {n m : ℕ}
    {cells : Finset (Cell n m)} {face : Finset (GridVertex n m)}
    (hface : face ∈ facetFamily cells) :
    ∃ c ∈ cells, FaceIncidentByFacet c face := by
  rcases (mem_facetFamily_iff cells face).1 hface with ⟨c, hc, i, hEq⟩
  exact ⟨c, hc, ⟨i, hEq⟩⟩

theorem cellFacet_mem_facetFamily {n m : ℕ}
    {cells : Finset (Cell n m)} {c : Cell n m}
    (hc : c ∈ cells) (i : Idx n) :
    cellFacet c i ∈ facetFamily cells := by
  exact (mem_facetFamily_iff cells (cellFacet c i)).2 ⟨c, hc, i, rfl⟩

theorem cellIncidenceCount_facetFamily_pos {n m : ℕ}
    {cells : Finset (Cell n m)} {c : Cell n m}
    (hc : c ∈ cells) :
    0 < cellIncidenceCount (facetFamily cells) FaceIncidentByFacet c := by
  classical
  let i0 : Idx n := ⟨0, Nat.succ_pos _⟩
  have hmemFace : cellFacet c i0 ∈ facetFamily cells :=
    cellFacet_mem_facetFamily hc i0
  have hinc : FaceIncidentByFacet c (cellFacet c i0) := ⟨i0, rfl⟩
  have hmemFilter :
      cellFacet c i0 ∈ (facetFamily cells).filter (fun face => FaceIncidentByFacet c face) := by
    exact Finset.mem_filter.2 ⟨hmemFace, hinc⟩
  simpa [cellIncidenceCount] using
    Finset.card_pos.mpr ⟨cellFacet c i0, hmemFilter⟩

/-- Generic positivity criterion for face incidence counts. -/
theorem faceIncidenceCount_pos_of_witness {n m : ℕ}
    (cells : Finset (Cell n m))
    (I : Cell n m → Finset (GridVertex n m) → Prop)
    (face : Finset (GridVertex n m))
    (hex : ∃ c ∈ cells, I c face) :
    0 < faceIncidenceCount cells I face := by
  classical
  rcases hex with ⟨c, hcMem, hcInc⟩
  have hmemFilter : c ∈ cells.filter (fun c' => I c' face) := by
    exact Finset.mem_filter.2 ⟨hcMem, hcInc⟩
  simpa [faceIncidenceCount] using Finset.card_pos.mpr ⟨c, hmemFilter⟩

/-- Every face in `facetFamily cells` has positive facet-incidence count. -/
theorem faceIncidenceCount_facetFamily_pos_of_mem {n m : ℕ}
    (cells : Finset (Cell n m))
    (face : Finset (GridVertex n m))
    (hface : face ∈ facetFamily cells) :
    0 < faceIncidenceCount cells FaceIncidentByFacet face := by
  rcases faceIncidentByFacet_of_mem_facetFamily (cells := cells) hface with ⟨c, hcMem, hInc⟩
  exact faceIncidenceCount_pos_of_witness cells FaceIncidentByFacet face ⟨c, hcMem, hInc⟩

/--
Pair-witness criterion for exact two incidence count.
-/
theorem faceIncidenceCount_eq_two_of_pair_witness_generic
    {n m : ℕ}
    (cells : Finset (Cell n m))
    (I : Cell n m → Finset (GridVertex n m) → Prop)
    (face : Finset (GridVertex n m))
    (c₁ c₂ : Cell n m)
    (hc₁ : c₁ ∈ cells) (hI₁ : I c₁ face)
    (hc₂ : c₂ ∈ cells) (hI₂ : I c₂ face)
    (hneq : c₁ ≠ c₂)
    (hcover : ∀ c ∈ cells, I c face → c = c₁ ∨ c = c₂) :
    faceIncidenceCount cells I face = 2 := by
  classical
  let S : Finset (Cell n m) := cells.filter (fun c => I c face)
  have hc₁S : c₁ ∈ S := Finset.mem_filter.2 ⟨hc₁, hI₁⟩
  have hc₂S : c₂ ∈ S := Finset.mem_filter.2 ⟨hc₂, hI₂⟩
  have hS : S = ({c₁, c₂} : Finset (Cell n m)) := by
    ext c
    constructor
    · intro hc
      have hcCells : c ∈ cells := (Finset.mem_filter.1 hc).1
      have hcInc : I c face := (Finset.mem_filter.1 hc).2
      rcases hcover c hcCells hcInc with rfl | rfl <;> simp
    · intro hc
      rcases Finset.mem_insert.1 hc with rfl | hc'
      · exact hc₁S
      · have : c = c₂ := by simpa using hc'
        subst this
        exact hc₂S
  have hcardS : S.card = 2 := by
    rw [hS]
    simp [hneq]
  simpa [faceIncidenceCount, S] using hcardS

/--
Pair-witness criterion for exact two incidence count.
-/
theorem faceIncidenceCount_eq_two_of_pair_witness
    {n m : ℕ}
    (cells : Finset (Cell n m))
    (face : Finset (GridVertex n m))
    (c₁ c₂ : Cell n m)
    (hc₁ : c₁ ∈ cells) (hI₁ : FaceIncidentByFacet c₁ face)
    (hc₂ : c₂ ∈ cells) (hI₂ : FaceIncidentByFacet c₂ face)
    (hneq : c₁ ≠ c₂)
    (hcover : ∀ c ∈ cells, FaceIncidentByFacet c face → c = c₁ ∨ c = c₂) :
    faceIncidenceCount cells FaceIncidentByFacet face = 2 := by
  exact faceIncidenceCount_eq_two_of_pair_witness_generic
    cells FaceIncidentByFacet face c₁ c₂ hc₁ hI₁ hc₂ hI₂ hneq hcover

/-- Unique-witness criterion for exact one incidence count. -/
theorem faceIncidenceCount_eq_one_of_unique_witness
    {n m : ℕ}
    (cells : Finset (Cell n m))
    (face : Finset (GridVertex n m))
    (c₀ : Cell n m)
    (hc₀ : c₀ ∈ cells) (hI₀ : FaceIncidentByFacet c₀ face)
    (huniq : ∀ c ∈ cells, FaceIncidentByFacet c face → c = c₀) :
    faceIncidenceCount cells FaceIncidentByFacet face = 1 := by
  classical
  let S : Finset (Cell n m) := cells.filter (fun c => FaceIncidentByFacet c face)
  have hc₀S : c₀ ∈ S := Finset.mem_filter.2 ⟨hc₀, hI₀⟩
  have hS : S = ({c₀} : Finset (Cell n m)) := by
    ext c
    constructor
    · intro hc
      have hcEq : c = c₀ := huniq c (Finset.mem_filter.1 hc).1 (Finset.mem_filter.1 hc).2
      simp [hcEq]
    · intro hc
      have hcEq : c = c₀ := by simpa using hc
      subst hcEq
      exact hc₀S
  have hcardS : S.card = 1 := by
    rw [hS]
    simp
  simpa [faceIncidenceCount, S] using hcardS

/-- Zero-incidence criterion from pointwise exclusion. -/
theorem faceIncidenceCount_eq_zero_of_no_witness
    {n m : ℕ}
    (cells : Finset (Cell n m))
    (face : Finset (GridVertex n m))
    (hnone : ∀ c ∈ cells, ¬ FaceIncidentByFacet c face) :
    faceIncidenceCount cells FaceIncidentByFacet face = 0 := by
  classical
  have hfilter : cells.filter (fun c => FaceIncidentByFacet c face) = ∅ := by
    ext c
    constructor
    · intro hc
      exact False.elim ((hnone c (Finset.mem_filter.1 hc).1) (Finset.mem_filter.1 hc).2)
    · intro hc
      simp at hc
  simp [faceIncidenceCount, hfilter]

/-- Count `1` gives split form `1 + 2*k` (with `k = 0`). -/
theorem splitCount_of_eq_one
    {n m : ℕ}
    (cells : Finset (Cell n m))
    (face : Finset (GridVertex n m))
    (hcount : faceIncidenceCount cells FaceIncidentByFacet face = 1) :
    ∃ k : ℕ, faceIncidenceCount cells FaceIncidentByFacet face = 1 + 2 * k := by
  refine ⟨0, ?_⟩
  simp [hcount]

/-- Count `0` gives split form `0 + 2*k` (with `k = 0`). -/
theorem splitCount_of_eq_zero
    {n m : ℕ}
    (cells : Finset (Cell n m))
    (face : Finset (GridVertex n m))
    (hcount : faceIncidenceCount cells FaceIncidentByFacet face = 0) :
    ∃ k : ℕ, faceIncidenceCount cells FaceIncidentByFacet face = 0 + 2 * k := by
  refine ⟨0, ?_⟩
  simp [hcount]

/-- Exact two-incidence implies the even-count form used by parity bridges. -/
theorem faceIncidence_even_of_eq_two {n m : ℕ}
    (cells : Finset (Cell n m))
    (face : Finset (GridVertex n m))
    (hcount : faceIncidenceCount cells FaceIncidentByFacet face = 2) :
    ∃ k : ℕ, faceIncidenceCount cells FaceIncidentByFacet face = 2 * k := by
  refine ⟨1, ?_⟩
  simpa using hcount

/--
Scale-level reduction:
if interior facets have exactly two incidences and boundary facets admit split counts,
then the Kuhn-facet count bridge yields a fixed point.
-/
theorem exists_fixedPoint_of_kuhnFacetTwoInteriorCounts_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
        ∃ b : Finset (GridVertex n m) → ZMod 2,
          (∀ c ∈ cells, IsMeshCell c) ∧
          (∀ c ∈ cells,
            ((cellIncidenceCount (facetFamily cells) FaceIncidentByFacet c : ZMod 2) =
              cellFullyLabeledIndicatorZ2
                (fun p : GridVertex n m => gridLabel f hm p) c)) ∧
          (∀ face ∈ interiorFaces (facetFamily cells),
            faceIncidenceCount cells FaceIncidentByFacet face = 2) ∧
          (∀ face ∈ boundaryFaces (facetFamily cells),
            ∃ k : ℕ,
              faceIncidenceCount cells FaceIncidentByFacet face = (b face).val + 2 * k) ∧
          Finset.sum (boundaryFaces (facetFamily cells)) b = 1) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_weightParity_at_scales (f := f) hcont ?_
  intro m hm
  rcases hdata m hm with ⟨cells, b, hmesh, hcellPar, hinteriorTwo, hboundaryCount, hbsum⟩
  refine ⟨cells, (fun c => cellIncidenceCount (facetFamily cells) FaceIncidentByFacet c),
    hmesh, hcellPar, ?_⟩
  have hinteriorParity :
      ∀ face ∈ interiorFaces (facetFamily cells),
        (faceIncidenceCount cells FaceIncidentByFacet face : ZMod 2) = 0 := by
    intro face hface
    rw [hinteriorTwo face hface]
    exact (by decide : ((2 : ℕ) : ZMod 2) = 0)
  have hboundaryParity :
      ∀ face ∈ boundaryFaces (facetFamily cells),
        (faceIncidenceCount cells FaceIncidentByFacet face : ZMod 2) = b face := by
    intro face hface
    rcases hboundaryCount face hface with ⟨k, hk⟩
    rw [hk, Nat.cast_add, Nat.cast_mul]
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, add_zero]
    exact ZMod.natCast_zmod_val (b face)
  exact sum_cellIncidenceCount_eq_one_zmod2_of_partitionedFaces
    cells (facetFamily cells)
    (interiorFaces (facetFamily cells))
    (boundaryFaces (facetFamily cells))
    FaceIncidentByFacet b
    (interior_union_boundary_faces (facetFamily cells)).symm
    (disjoint_interior_boundary_faces (facetFamily cells))
    hinteriorParity hboundaryParity hbsum

/-- Boundary class sum is `1` when exactly one boundary face carries class `1`. -/
theorem boundary_sum_one_of_unique_marked_face {n m : ℕ}
    (faces : Finset (Finset (GridVertex n m)))
    (b : Finset (GridVertex n m) → ZMod 2)
    (f0 : Finset (GridVertex n m))
    (hf0 : f0 ∈ boundaryFaces faces)
    (hmark : b f0 = 1)
    (hrest : ∀ face ∈ boundaryFaces faces, face ≠ f0 → b face = 0) :
    Finset.sum (boundaryFaces faces) b = 1 := by
  classical
  have hsplit :
      Finset.sum ((boundaryFaces faces).erase f0) b + b f0
        = Finset.sum (boundaryFaces faces) b := by
    exact Finset.sum_erase_add (s := boundaryFaces faces) (a := f0) (f := b) hf0
  calc
    Finset.sum (boundaryFaces faces) b
        = b f0 + Finset.sum ((boundaryFaces faces).erase f0) b := by
            simpa [add_comm] using hsplit.symm
    _ = 1 + Finset.sum ((boundaryFaces faces).erase f0) b := by rw [hmark]
    _ = 1 + 0 := by
          congr
          refine Finset.sum_eq_zero ?_
          intro face hface
          have hmem : face ∈ boundaryFaces faces := Finset.mem_of_mem_erase hface
          have hne : face ≠ f0 := Finset.ne_of_mem_erase hface
          exact hrest face hmem hne
    _ = 1 := by simp

/--
Convenient final-cut variant:
interior counts are exactly `2`, boundary counts split by `b`,
and `b` is supported at one marked boundary face.
-/
theorem exists_fixedPoint_of_kuhnFacetUniqueBoundaryMark_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
        ∃ b : Finset (GridVertex n m) → ZMod 2,
        ∃ f0 : Finset (GridVertex n m),
          (∀ c ∈ cells, IsMeshCell c) ∧
          (∀ c ∈ cells,
            ((cellIncidenceCount (facetFamily cells) FaceIncidentByFacet c : ZMod 2) =
              cellFullyLabeledIndicatorZ2
                (fun p : GridVertex n m => gridLabel f hm p) c)) ∧
          (∀ face ∈ interiorFaces (facetFamily cells),
            faceIncidenceCount cells FaceIncidentByFacet face = 2) ∧
          (∀ face ∈ boundaryFaces (facetFamily cells),
            ∃ k : ℕ,
              faceIncidenceCount cells FaceIncidentByFacet face = (b face).val + 2 * k) ∧
          f0 ∈ boundaryFaces (facetFamily cells) ∧
          b f0 = 1 ∧
          (∀ face ∈ boundaryFaces (facetFamily cells), face ≠ f0 → b face = 0)) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_kuhnFacetTwoInteriorCounts_at_scales (f := f) hcont ?_
  intro m hm
  rcases hdata m hm with
    ⟨cells, b, f0, hmesh, hcellPar, hinteriorTwo, hboundaryCount, hf0, hmark, hrest⟩
  refine ⟨cells, b, hmesh, hcellPar, hinteriorTwo, hboundaryCount, ?_⟩
  exact boundary_sum_one_of_unique_marked_face (faces := facetFamily cells) b f0 hf0 hmark hrest

/-- Boundary class as indicator of equality to a marked face. -/
noncomputable def boundaryMarkClass {n m : ℕ}
    (f0 : Finset (GridVertex n m)) :
    Finset (GridVertex n m) → ZMod 2 := by
  classical
  exact fun face => if face = f0 then 1 else 0

/--
Most concrete boundary variant: class is the indicator of one marked boundary face.
-/
theorem exists_fixedPoint_of_kuhnFacetBoundaryIndicator_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
        ∃ f0 : Finset (GridVertex n m),
          (∀ c ∈ cells, IsMeshCell c) ∧
          (∀ c ∈ cells,
            ((cellIncidenceCount (facetFamily cells) FaceIncidentByFacet c : ZMod 2) =
              cellFullyLabeledIndicatorZ2
                (fun p : GridVertex n m => gridLabel f hm p) c)) ∧
          (∀ face ∈ interiorFaces (facetFamily cells),
            faceIncidenceCount cells FaceIncidentByFacet face = 2) ∧
          (∀ face ∈ boundaryFaces (facetFamily cells),
            ∃ k : ℕ,
              faceIncidenceCount cells FaceIncidentByFacet face =
                (if face = f0 then 1 else 0) + 2 * k) ∧
          f0 ∈ boundaryFaces (facetFamily cells)) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_kuhnFacetUniqueBoundaryMark_at_scales (f := f) hcont ?_
  intro m hm
  rcases hdata m hm with ⟨cells, f0, hmesh, hcellPar, hinteriorTwo, hboundaryCount, hf0⟩
  let b : Finset (GridVertex n m) → ZMod 2 := boundaryMarkClass f0
  refine ⟨cells, b, f0, hmesh, hcellPar, hinteriorTwo, ?_, hf0, ?_, ?_⟩
  · intro face hface
    rcases hboundaryCount face hface with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    by_cases hEq : face = f0
    · subst hEq
      simpa [b, boundaryMarkClass] using hk
    · simpa [b, boundaryMarkClass, hEq] using hk
  · simp [b, boundaryMarkClass]
  · intro face hface hne
    simp [b, boundaryMarkClass, hne]

/--
Witness-pattern variant:
interior facets come with explicit two-cell incidence witnesses;
boundary facets are split by one marked face with unique witness and no witnesses elsewhere.
-/
theorem exists_fixedPoint_of_kuhnFacetWitnessPattern_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
        ∃ f0 : Finset (GridVertex n m),
          (∀ c ∈ cells, IsMeshCell c) ∧
          (∀ c ∈ cells,
            ((cellIncidenceCount (facetFamily cells) FaceIncidentByFacet c : ZMod 2) =
              cellFullyLabeledIndicatorZ2
                (fun p : GridVertex n m => gridLabel f hm p) c)) ∧
          (∀ face ∈ interiorFaces (facetFamily cells),
            ∃ c₁ c₂,
              c₁ ∈ cells ∧ FaceIncidentByFacet c₁ face ∧
              c₂ ∈ cells ∧ FaceIncidentByFacet c₂ face ∧
              c₁ ≠ c₂ ∧
              (∀ c ∈ cells, FaceIncidentByFacet c face → c = c₁ ∨ c = c₂)) ∧
          f0 ∈ boundaryFaces (facetFamily cells) ∧
          (∃ c₀, c₀ ∈ cells ∧ FaceIncidentByFacet c₀ f0 ∧
            (∀ c ∈ cells, FaceIncidentByFacet c f0 → c = c₀)) ∧
          (∀ face ∈ boundaryFaces (facetFamily cells), face ≠ f0 →
            ∀ c ∈ cells, ¬ FaceIncidentByFacet c face)) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_kuhnFacetBoundaryIndicator_at_scales (f := f) hcont ?_
  intro m hm
  rcases hdata m hm with
    ⟨cells, f0, hmesh, hcellPar, hinteriorWit, hf0, hmarkedUnique, hboundaryNone⟩
  refine ⟨cells, f0, hmesh, hcellPar, ?_, ?_, hf0⟩
  · intro face hface
    rcases hinteriorWit face hface with
      ⟨c₁, c₂, hc₁, hI₁, hc₂, hI₂, hneq, hcover⟩
    exact faceIncidenceCount_eq_two_of_pair_witness
      cells face c₁ c₂ hc₁ hI₁ hc₂ hI₂ hneq hcover
  · intro face hface
    by_cases hEq : face = f0
    · subst hEq
      rcases hmarkedUnique with ⟨c₀, hc₀, hI₀, huniq⟩
      rcases splitCount_of_eq_one cells face
        (faceIncidenceCount_eq_one_of_unique_witness cells face c₀ hc₀ hI₀ huniq) with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simpa using hk
    · rcases splitCount_of_eq_zero cells face
        (faceIncidenceCount_eq_zero_of_no_witness cells face
          (hboundaryNone face hface hEq)) with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simpa [hEq] using hk

/-- Even incidence count implies zero parity in `ZMod 2`. -/
theorem faceIncidenceParity_zero_of_even {n m : ℕ}
    (cells : Finset (Cell n m))
    (face : Finset (GridVertex n m))
    (k : ℕ)
    (hcount : faceIncidenceCount cells FaceIncidentByFacet face = 2 * k) :
    (faceIncidenceCount cells FaceIncidentByFacet face : ZMod 2) = 0 := by
  rw [hcount, Nat.cast_mul]
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [h2, zero_mul]

/-- Count represented by a parity class (`0` or `1`) implies matching parity. -/
theorem faceIncidenceParity_eq_class_of_splitCount {n m : ℕ}
    (cells : Finset (Cell n m))
    (face : Finset (GridVertex n m))
    (bit : ZMod 2) (k : ℕ)
    (hcount : faceIncidenceCount cells FaceIncidentByFacet face = bit.val + 2 * k) :
    (faceIncidenceCount cells FaceIncidentByFacet face : ZMod 2) = bit := by
  rw [hcount, Nat.cast_add, Nat.cast_mul]
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [h2, zero_mul, add_zero]
  exact ZMod.natCast_zmod_val bit

/--
Kuhn-facet-specialized parity-to-fixed-point bridge.

This fixes the face set to `facetFamily cells` and incidence to `FaceIncidentByFacet`,
leaving only the concrete parity obligations for the subdivision.
-/
theorem exists_fixedPoint_of_kuhnFacetParity_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
        ∃ b : Finset (GridVertex n m) → ZMod 2,
          (∀ c ∈ cells, IsMeshCell c) ∧
          (∀ c ∈ cells,
            ((cellIncidenceCount (facetFamily cells) FaceIncidentByFacet c : ZMod 2) =
              cellFullyLabeledIndicatorZ2
                (fun p : GridVertex n m => gridLabel f hm p) c)) ∧
          (∀ face ∈ interiorFaces (facetFamily cells),
            (faceIncidenceCount cells FaceIncidentByFacet face : ZMod 2) = 0) ∧
          (∀ face ∈ boundaryFaces (facetFamily cells),
            (faceIncidenceCount cells FaceIncidentByFacet face : ZMod 2) = b face) ∧
          Finset.sum (boundaryFaces (facetFamily cells)) b = 1) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_weightParity_at_scales (f := f) hcont ?_
  intro m hm
  rcases hdata m hm with ⟨cells, b, hmesh, hcellPar, hinterior, hboundary, hbsum⟩
  refine ⟨cells, (fun c => cellIncidenceCount (facetFamily cells) FaceIncidentByFacet c),
    hmesh, hcellPar, ?_⟩
  exact sum_cellIncidenceCount_eq_one_zmod2_of_partitionedFaces
    cells (facetFamily cells)
    (interiorFaces (facetFamily cells))
    (boundaryFaces (facetFamily cells))
    FaceIncidentByFacet b
    (interior_union_boundary_faces (facetFamily cells)).symm
    (disjoint_interior_boundary_faces (facetFamily cells))
    hinterior hboundary hbsum

/--
Count-form variant of `exists_fixedPoint_of_kuhnFacetParity_at_scales`.

If interior facet incidence counts are even and boundary facet incidence counts
split as `bit + 2k`, with boundary-bit sum `1`, then `f` has a fixed point.
-/
theorem exists_fixedPoint_of_kuhnFacetCounts_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
        ∃ b : Finset (GridVertex n m) → ZMod 2,
          (∀ c ∈ cells, IsMeshCell c) ∧
          (∀ c ∈ cells,
            ((cellIncidenceCount (facetFamily cells) FaceIncidentByFacet c : ZMod 2) =
              cellFullyLabeledIndicatorZ2
                (fun p : GridVertex n m => gridLabel f hm p) c)) ∧
          (∀ face ∈ interiorFaces (facetFamily cells),
            ∃ k : ℕ,
              faceIncidenceCount cells FaceIncidentByFacet face = 2 * k) ∧
          (∀ face ∈ boundaryFaces (facetFamily cells),
            ∃ k : ℕ,
              faceIncidenceCount cells FaceIncidentByFacet face = (b face).val + 2 * k) ∧
          Finset.sum (boundaryFaces (facetFamily cells)) b = 1) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_kuhnFacetParity_at_scales (f := f) hcont ?_
  intro m hm
  rcases hdata m hm with ⟨cells, b, hmesh, hcellPar, hinteriorCount, hboundaryCount, hbsum⟩
  refine ⟨cells, b, hmesh, hcellPar, ?_, ?_, hbsum⟩
  · intro face hface
    rcases hinteriorCount face hface with ⟨k, hk⟩
    exact faceIncidenceParity_zero_of_even cells face k hk
  · intro face hface
    rcases hboundaryCount face hface with ⟨k, hk⟩
    exact faceIncidenceParity_eq_class_of_splitCount cells face (b face) k hk

end KuhnIncidence

/--
Specialized partitioned-incidence bridge using the canonical
`interiorFaces` / `boundaryFaces` split.
-/
theorem exists_fixedPoint_of_boundaryInteriorFaceParity_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
        ∃ faces : Finset (Finset (GridVertex n m)),
        ∃ I : Cell n m → Finset (GridVertex n m) → Prop,
        ∃ b : Finset (GridVertex n m) → ZMod 2,
          (∀ c ∈ cells, IsMeshCell c) ∧
          (∀ c ∈ cells,
            ((cellIncidenceCount faces I c : ZMod 2) =
              cellFullyLabeledIndicatorZ2
                (fun p : GridVertex n m => gridLabel f hm p) c)) ∧
          (∀ face ∈ interiorFaces faces, (faceIncidenceCount cells I face : ZMod 2) = 0) ∧
          (∀ face ∈ boundaryFaces faces, (faceIncidenceCount cells I face : ZMod 2) = b face) ∧
          Finset.sum (boundaryFaces faces) b = 1) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_weightParity_at_scales (f := f) hcont ?_
  intro m hm
  rcases hdata m hm with ⟨cells, faces, I, b, hmesh, hcellPar, hinterior, hboundary, hbsum⟩
  refine ⟨cells, (fun c => cellIncidenceCount faces I c), hmesh, hcellPar, ?_⟩
  exact sum_cellIncidenceCount_eq_one_zmod2_of_partitionedFaces
    cells faces (interiorFaces faces) (boundaryFaces faces) I b
    (interior_union_boundary_faces faces).symm (disjoint_interior_boundary_faces faces)
    hinterior hboundary hbsum

/--
Incidence-parity-to-fixed-point bridge.

If each scale supplies:
- mesh cells,
- a face incidence relation,
- cell incidence parity matching the fully-labeled indicator,
- face incidence parity summing to `1` in `ZMod 2`,
then `f` has a fixed point.
-/
theorem exists_fixedPoint_of_incidenceParity_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (β : ℕ → Type*)
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
        ∃ faces : Finset (β m),
        ∃ I : Cell n m → β m → Prop,
        ∃ b : β m → ZMod 2,
          (∀ c ∈ cells, IsMeshCell c) ∧
          (∀ c ∈ cells,
            ((cellIncidenceCount faces I c : ZMod 2) =
              cellFullyLabeledIndicatorZ2
                (fun p : GridVertex n m => gridLabel f hm p) c)) ∧
          (∀ face ∈ faces, ((faceIncidenceCount cells I face : ZMod 2) = b face)) ∧
          Finset.sum faces b = 1) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_weightParity_at_scales (f := f) hcont ?_
  intro m hm
  rcases hdata m hm with ⟨cells, faces, I, b, hmesh, hcellPar, hfacePar, hbsum⟩
  refine ⟨cells, (fun c => cellIncidenceCount faces I c), hmesh, hcellPar, ?_⟩
  exact sum_cellIncidenceCount_eq_one_zmod2_of_faceParity cells faces I b hfacePar hbsum

/-- Incidence parity data for one fixed scale `m`. -/
structure IncidenceParityScaleData
    (n m : ℕ)
    (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hm : 0 < m)
    (β : Type*) where
  cells : Finset (Cell n m)
  faces : Finset β
  incidence : Cell n m → β → Prop
  faceClass : β → ZMod 2
  mesh : ∀ c ∈ cells, IsMeshCell c
  cellParity :
    ∀ c ∈ cells,
      ((cellIncidenceCount faces incidence c : ZMod 2) =
        cellFullyLabeledIndicatorZ2
          (fun p : GridVertex n m => gridLabel f hm p) c)
  faceParity :
    ∀ face ∈ faces, ((faceIncidenceCount cells incidence face : ZMod 2) = faceClass face)
  faceClassSum : Finset.sum faces faceClass = 1

/-- Incidence parity data at all scales. -/
structure IncidenceParityFamilyData
    (n : ℕ)
    (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (β : ℕ → Type*) where
  scale :
    ∀ (m : ℕ) (hm : 0 < m), IncidenceParityScaleData n m f hm (β m)

/--
Structured-input version of `exists_fixedPoint_of_incidenceParity_at_scales`.
-/
theorem exists_fixedPoint_of_incidenceParityFamily
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (β : ℕ → Type*)
    (data : IncidenceParityFamilyData n f β) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_incidenceParity_at_scales
    (f := f) hcont β ?_
  intro m hm
  let d : IncidenceParityScaleData n m f hm (β m) := data.scale m hm
  exact ⟨d.cells, d.faces, d.incidence, d.faceClass,
    d.mesh, d.cellParity, d.faceParity, d.faceClassSum⟩

/--
Partitioned-incidence parity bridge at all scales.

This is tailored to the standard Sperner counting pattern:
interior faces contribute parity `0`, boundary faces contribute a class sum `1`.
-/
theorem exists_fixedPoint_of_partitionedIncidenceParity_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (β : ℕ → Type*) [∀ m, DecidableEq (β m)]
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
        ∃ faces interior boundary : Finset (β m),
        ∃ I : Cell n m → β m → Prop,
        ∃ b : β m → ZMod 2,
          faces = interior ∪ boundary ∧
          Disjoint interior boundary ∧
          (∀ c ∈ cells, IsMeshCell c) ∧
          (∀ c ∈ cells,
            ((cellIncidenceCount faces I c : ZMod 2) =
              cellFullyLabeledIndicatorZ2
                (fun p : GridVertex n m => gridLabel f hm p) c)) ∧
          (∀ face ∈ interior, (faceIncidenceCount cells I face : ZMod 2) = 0) ∧
          (∀ face ∈ boundary, (faceIncidenceCount cells I face : ZMod 2) = b face) ∧
          Finset.sum boundary b = 1) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_weightParity_at_scales (f := f) hcont ?_
  intro m hm
  rcases hdata m hm with
    ⟨cells, faces, interior, boundary, I, b, hcover, hdisj,
      hmesh, hcellPar, hinterior, hboundary, hbsum⟩
  refine ⟨cells, (fun c => cellIncidenceCount faces I c), hmesh, hcellPar, ?_⟩
  exact sum_cellIncidenceCount_eq_one_zmod2_of_partitionedFaces
    cells faces interior boundary I b hcover hdisj hinterior hboundary hbsum

/--
Odd cardinality of fully-labeled cells in a mesh family yields a quantitative cluster.
-/
theorem exists_cluster_le_inv_of_odd_card_fullyLabeledCells
    {n m : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hm : 0 < m) (cells : Finset (Cell n m))
    (hmeshFam : ∀ c ∈ cells, IsMeshCell c)
    (hodd :
      (fullyLabeledCells (fun p : GridVertex n m => gridLabel f hm p) cells).card % 2 = 1) :
    ∃ x : Idx n → stdSimplex ℝ (Idx n),
      (∀ i j : Idx n, dist (x i) (x j) ≤ (1 : ℝ) / m) ∧
      (∀ i : Idx n, 0 ≤ x i i - f (x i) i) := by
  rcases exists_of_odd_card_fullyLabeledCells
      (L := fun p : GridVertex n m => gridLabel f hm p) cells hodd with
      ⟨c, hcMem, hcFull⟩
  exact exists_cluster_le_inv_of_gridLabel_cell (f := f) hm c (hmeshFam c hcMem) hcFull

/--
Scale-indexed odd-cardinality assumptions yield scale-indexed quantitative clusters.
-/
theorem exists_cluster_family_at_scales_of_odd_card_fullyLabeledCells
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
          (∀ c ∈ cells, IsMeshCell c) ∧
          (fullyLabeledCells (fun p : GridVertex n m => gridLabel f hm p) cells).card % 2 = 1) :
    ∀ m : ℕ, 0 < m →
      ∃ x : Idx n → stdSimplex ℝ (Idx n),
        (∀ i j : Idx n, dist (x i) (x j) ≤ (1 : ℝ) / m) ∧
        (∀ i : Idx n, 0 ≤ x i i - f (x i) i) := by
  intro m hm
  rcases hdata m hm with ⟨cells, hmeshFam, hodd⟩
  exact exists_cluster_le_inv_of_odd_card_fullyLabeledCells (f := f) hm cells hmeshFam hodd

/--
If each subdivision scale has an odd number of fully-labeled mesh cells (for `gridLabel`),
then the map has a fixed point.
-/
theorem exists_fixedPoint_of_odd_card_fullyLabeledCells_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        ∃ cells : Finset (Cell n m),
          (∀ c ∈ cells, IsMeshCell c) ∧
          (fullyLabeledCells (fun p : GridVertex n m => gridLabel f hm p) cells).card % 2 = 1) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  exact exists_fixedPoint_of_labeled_clusters_at_scales (ι := Idx n) (f := f) hcont
    (exists_cluster_family_at_scales_of_odd_card_fullyLabeledCells (f := f) hdata)

/--
Per-scale concrete witness package for the Kuhn facet fixed-point bridge.

This is the exact data shape needed by
`exists_fixedPoint_of_kuhnFacetWitnessPattern_at_scales`.
-/
structure KuhnFacetWitnessScaleData {n m : ℕ}
    (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hm : 0 < m) where
  cells : Finset (Cell n m)
  f0 : Finset (GridVertex n m)
  mesh :
    ∀ c ∈ cells, IsMeshCell c
  cellParity :
    ∀ c ∈ cells,
      ((cellIncidenceCount (facetFamily cells) FaceIncidentByFacet c : ZMod 2) =
        cellFullyLabeledIndicatorZ2 (fun p : GridVertex n m => gridLabel f hm p) c)
  interiorPairWitness :
    ∀ face ∈ interiorFaces (facetFamily cells),
      ∃ c₁ c₂,
        c₁ ∈ cells ∧ FaceIncidentByFacet c₁ face ∧
        c₂ ∈ cells ∧ FaceIncidentByFacet c₂ face ∧
        c₁ ≠ c₂ ∧
        (∀ c ∈ cells, FaceIncidentByFacet c face → c = c₁ ∨ c = c₂)
  markedBoundaryMem :
    f0 ∈ boundaryFaces (facetFamily cells)
  markedBoundaryUnique :
    ∃ c₀, c₀ ∈ cells ∧ FaceIncidentByFacet c₀ f0 ∧
      (∀ c ∈ cells, FaceIncidentByFacet c f0 → c = c₀)
  otherBoundaryNone :
    ∀ face ∈ boundaryFaces (facetFamily cells), face ≠ f0 →
      ∀ c ∈ cells, ¬ FaceIncidentByFacet c face

/--
Structured-input wrapper: scale-indexed `KuhnFacetWitnessScaleData` implies a fixed point.
-/
theorem exists_fixedPoint_of_kuhnFacetWitnessScaleData_at_scales
    {n : ℕ} (f : stdSimplex ℝ (Idx n) → stdSimplex ℝ (Idx n))
    (hcont : Continuous f)
    (hdata :
      ∀ (m : ℕ) (hm : 0 < m),
        KuhnFacetWitnessScaleData (n := n) (m := m) f hm) :
    ∃ x : stdSimplex ℝ (Idx n), Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_kuhnFacetWitnessPattern_at_scales (f := f) hcont ?_
  intro m hm
  rcases hdata m hm with
    ⟨cells, f0, hmesh, hcellPar, hinteriorWit, hf0, hmarkedUnique, hboundaryNone⟩
  exact ⟨cells, f0, hmesh, hcellPar, hinteriorWit, hf0, hmarkedUnique, hboundaryNone⟩

end Cell

section KuhnBridge

/--
Boundary-marked witness package extracted from `KuhnSubdivision` data.

This upgrades facet-family membership of the marked face to
`SpernerParity.boundaryFaces` membership using the explicit coordinate-hyperface
condition `∀ v ∈ f0, v_j = 0`.
-/
theorem exists_markedBoundary_uniqueWitness_cellsAtScale_from_kuhn
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ∃ p : Fixpoint.KuhnSubdivision.GridVertex n m,
      ∃ hp : p ∈ Fixpoint.KuhnSubdivision.allGridVertices (n := n) (m := m),
        ∃ j : Fixpoint.KuhnSubdivision.Idx n,
          ∃ hj : 0 < p.1 j, p.1 j = 1 ∧
            ∃ f0 : Finset (Fixpoint.KuhnSubdivision.GridVertex n m),
              ∃ c₀ : Fixpoint.KuhnSubdivision.Cell n m,
                c₀ ∈ Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m) ∧
                Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m) c₀ f0 ∧
                f0 ∈ boundaryFaces
                  (Fixpoint.KuhnSubdivision.facetFamily
                    (n := n) (m := m)
                    (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m))) ∧
                (∀ c ∈ Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m),
                    c ∈ Fixpoint.KuhnSubdivision.starCellsFrom (n := n) (m := m) p →
                    Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m) c f0 →
                    c = c₀) := by
  rcases Fixpoint.KuhnSubdivision.exists_markedFacet_coordZero_uniqueWitness_cellsAtScale
      (n := n) (m := m) hn hm with
    ⟨p, hp, j, hj, hj1, f0, c₀, hc₀, hI₀, hf0Fam, hcoord0, huniq⟩
  refine ⟨p, hp, j, hj, hj1, f0, c₀, hc₀, hI₀, ?_, huniq⟩
  exact (mem_boundaryFaces_iff
    (Fixpoint.KuhnSubdivision.facetFamily
      (n := n) (m := m)
      (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m))) f0).2
      ⟨hf0Fam, ⟨j, hcoord0⟩⟩

/--
Immediate corollary: for `n > 0`, `m > 0`, the Kuhn scale family has a boundary face.
-/
theorem exists_boundaryFace_in_cellsAtScale_from_kuhn
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ∃ f0 : Finset (Fixpoint.KuhnSubdivision.GridVertex n m),
      f0 ∈ boundaryFaces
        (Fixpoint.KuhnSubdivision.facetFamily
          (n := n) (m := m)
          (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m))) := by
  rcases exists_markedBoundary_uniqueWitness_cellsAtScale_from_kuhn
      (n := n) (m := m) hn hm with
    ⟨p, hp, j, hj, hj1, f0, c₀, hc₀, hI₀, hf0Bnd, huniq⟩
  exact ⟨f0, hf0Bnd⟩

/--
From the Kuhn bridge, one boundary face of `cellsAtScale` has positive incidence count.
-/
theorem exists_boundaryFace_posIncidence_in_cellsAtScale_from_kuhn
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ∃ f0 : Finset (Fixpoint.KuhnSubdivision.GridVertex n m),
      f0 ∈ boundaryFaces
        (Fixpoint.KuhnSubdivision.facetFamily
          (n := n) (m := m)
          (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m))) ∧
      0 < faceIncidenceCount
            (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m))
            (Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m))
            f0 := by
  rcases exists_markedBoundary_uniqueWitness_cellsAtScale_from_kuhn
      (n := n) (m := m) hn hm with
    ⟨p, hp, j, hj, hj1, f0, c₀, hc₀, hI₀, hf0Bnd, huniq⟩
  refine ⟨f0, hf0Bnd, ?_⟩
  exact faceIncidenceCount_pos_of_witness
    (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m))
    (Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m))
    f0
    ⟨c₀, hc₀, hI₀⟩

/--
Local rooted count-control:
on `starCellsFrom p`, the source facet of `starCell p j hj` has incidence count `1`.
-/
theorem faceIncidenceCount_eq_one_on_starCellsFrom_sourceFacet
    {n m : ℕ}
    (p : Fixpoint.KuhnSubdivision.GridVertex n m)
    (j : Fixpoint.KuhnSubdivision.Idx n)
    (hj : 0 < p.1 j) :
    faceIncidenceCount
        (Fixpoint.KuhnSubdivision.starCellsFrom (n := n) (m := m) p)
        (Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m))
        (Fixpoint.KuhnSubdivision.cellFacet (n := n) (m := m)
          (Fixpoint.KuhnSubdivision.starCell p j hj) j) = 1 := by
  let c0 : Fixpoint.KuhnSubdivision.Cell n m := Fixpoint.KuhnSubdivision.starCell p j hj
  let f0 : Finset (Fixpoint.KuhnSubdivision.GridVertex n m) :=
    Fixpoint.KuhnSubdivision.cellFacet (n := n) (m := m) c0 j
  have hc0 :
      c0 ∈ Fixpoint.KuhnSubdivision.starCellsFrom (n := n) (m := m) p := by
    exact (Fixpoint.KuhnSubdivision.mem_starCellsFrom_iff (n := n) (m := m) p c0).2
      ⟨j, hj, rfl⟩
  have hI0 :
      Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m) c0 f0 := by
    exact ⟨j, rfl⟩
  have huniq :
      ∀ c ∈ Fixpoint.KuhnSubdivision.starCellsFrom (n := n) (m := m) p,
        Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m) c f0 → c = c0 := by
    intro c hc hinc
    exact Fixpoint.KuhnSubdivision.unique_sourceFacet_faceIncident_in_starCellsFrom
      (n := n) (m := m) p j hj hc (by simpa [c0, f0] using hinc)
  exact faceIncidenceCount_eq_one_of_unique_witness
    (Fixpoint.KuhnSubdivision.starCellsFrom (n := n) (m := m) p)
    f0 c0 hc0 hI0 huniq

/--
Root-slice lift of the rooted count-control lemma:
on `(cellsAtScale).filter (· ∈ starCellsFrom p)`, the same source facet
still has incidence count `1`.
-/
theorem faceIncidenceCount_eq_one_on_cellsAtScale_rootSlice_sourceFacet
    {n m : ℕ}
    (p : Fixpoint.KuhnSubdivision.GridVertex n m)
    (hp : p ∈ Fixpoint.KuhnSubdivision.allGridVertices (n := n) (m := m))
    (j : Fixpoint.KuhnSubdivision.Idx n)
    (hj : 0 < p.1 j) :
    let f0 :=
      Fixpoint.KuhnSubdivision.cellFacet (n := n) (m := m)
        (Fixpoint.KuhnSubdivision.starCell p j hj) j
    let cellsRoot :=
      (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m)).filter
        (fun c => c ∈ Fixpoint.KuhnSubdivision.starCellsFrom (n := n) (m := m) p)
    faceIncidenceCount cellsRoot
      (Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m)) f0 = 1 := by
  let f0 :=
    Fixpoint.KuhnSubdivision.cellFacet (n := n) (m := m)
      (Fixpoint.KuhnSubdivision.starCell p j hj) j
  let cellsRoot :=
    (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m)).filter
      (fun c => c ∈ Fixpoint.KuhnSubdivision.starCellsFrom (n := n) (m := m) p)
  have hEqRoot :
      cellsRoot = Fixpoint.KuhnSubdivision.starCellsFrom (n := n) (m := m) p := by
    ext c
    constructor
    · intro hc
      exact (Finset.mem_filter.1 hc).2
    · intro hc
      have hcScale :
          c ∈ Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m) := by
        rcases (Fixpoint.KuhnSubdivision.mem_starCellsFrom_iff (n := n) (m := m) p c).1 hc with
          ⟨j', hj', hEq⟩
        exact (Fixpoint.KuhnSubdivision.mem_cellsFromRoots_iff (n := n) (m := m)
          (Fixpoint.KuhnSubdivision.allGridVertices (n := n) (m := m)) c).2
          ⟨p, hp, j', hj', hEq⟩
      exact Finset.mem_filter.2 ⟨hcScale, hc⟩
  simpa [f0, cellsRoot, hEqRoot] using
    (faceIncidenceCount_eq_one_on_starCellsFrom_sourceFacet (n := n) (m := m) p j hj)

/--
Hard count-control slice:
for `n > 0`, `m > 0`, one marked source facet has exact incidence count `1`
on the rooted star-cell slice inside `cellsAtScale`.
-/
theorem exists_boundaryFace_countOne_on_rootStarSlice_from_kuhn
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ∃ p : Fixpoint.KuhnSubdivision.GridVertex n m,
      ∃ j : Fixpoint.KuhnSubdivision.Idx n,
        ∃ hj : 0 < p.1 j, p.1 j = 1 ∧
          let f0 :=
            Fixpoint.KuhnSubdivision.cellFacet (n := n) (m := m)
              (Fixpoint.KuhnSubdivision.starCell p j hj) j
          let cellsRoot :=
            (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m)).filter
              (fun c => c ∈ Fixpoint.KuhnSubdivision.starCellsFrom (n := n) (m := m) p)
          f0 ∈ boundaryFaces
                (Fixpoint.KuhnSubdivision.facetFamily
                  (n := n) (m := m)
                  (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m))) ∧
          faceIncidenceCount cellsRoot
            (Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m)) f0 = 1 := by
  rcases Fixpoint.KuhnSubdivision.exists_coord_eq_one (n := n) (m := m) hn hm with
    ⟨p, j, hj1, hj⟩
  let f0 :=
    Fixpoint.KuhnSubdivision.cellFacet (n := n) (m := m)
      (Fixpoint.KuhnSubdivision.starCell p j hj) j
  let cellsRoot :=
    (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m)).filter
      (fun c => c ∈ Fixpoint.KuhnSubdivision.starCellsFrom (n := n) (m := m) p)
  have hp : p ∈ Fixpoint.KuhnSubdivision.allGridVertices (n := n) (m := m) :=
    Fixpoint.KuhnSubdivision.mem_allGridVertices (n := n) (m := m) p
  have hc0Scale :
      Fixpoint.KuhnSubdivision.starCell p j hj ∈
        Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m) := by
    exact (Fixpoint.KuhnSubdivision.mem_cellsFromRoots_iff (n := n) (m := m)
      (Fixpoint.KuhnSubdivision.allGridVertices (n := n) (m := m))
      (Fixpoint.KuhnSubdivision.starCell p j hj)).2 ⟨p, hp, j, hj, rfl⟩
  have hc0Root :
      Fixpoint.KuhnSubdivision.starCell p j hj ∈
        Fixpoint.KuhnSubdivision.starCellsFrom (n := n) (m := m) p := by
    exact (Fixpoint.KuhnSubdivision.mem_starCellsFrom_iff (n := n) (m := m) p
      (Fixpoint.KuhnSubdivision.starCell p j hj)).2 ⟨j, hj, rfl⟩
  have hc0CellsRoot :
      Fixpoint.KuhnSubdivision.starCell p j hj ∈ cellsRoot := by
    exact Finset.mem_filter.2 ⟨hc0Scale, hc0Root⟩
  have hI0 :
      Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m)
        (Fixpoint.KuhnSubdivision.starCell p j hj) f0 := by
    exact Fixpoint.KuhnSubdivision.faceIncident_sourceFacet_starCell
      (n := n) (m := m) p j hj
  have huniq :
      ∀ c ∈ cellsRoot,
        Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m) c f0 →
          c = Fixpoint.KuhnSubdivision.starCell p j hj := by
    intro c hc hinc
    have hcRoot : c ∈ Fixpoint.KuhnSubdivision.starCellsFrom (n := n) (m := m) p :=
      (Finset.mem_filter.1 hc).2
    exact Fixpoint.KuhnSubdivision.unique_sourceFacet_faceIncident_in_starCellsFrom
      (n := n) (m := m) p j hj hcRoot (by simpa [f0] using hinc)
  have hf0Fam :
      f0 ∈ Fixpoint.KuhnSubdivision.facetFamily
        (n := n) (m := m)
        (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m)) := by
    exact (Fixpoint.KuhnSubdivision.mem_facetFamily_iff (n := n) (m := m)
      (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m)) f0).2
      ⟨Fixpoint.KuhnSubdivision.starCell p j hj, hc0Scale, j, rfl⟩
  have hcoord0 :
      ∀ v ∈ f0, v.1 j = 0 := by
    simpa [f0] using
      (Fixpoint.KuhnSubdivision.all_sourceFacet_coords_zero_of_coord_one
        (n := n) (m := m) p j hj hj1)
  have hf0Bnd :
      f0 ∈ boundaryFaces
        (Fixpoint.KuhnSubdivision.facetFamily
          (n := n) (m := m)
          (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m))) := by
    exact (mem_boundaryFaces_iff
      (Fixpoint.KuhnSubdivision.facetFamily
        (n := n) (m := m)
        (Fixpoint.KuhnSubdivision.cellsAtScale (n := n) (m := m))) f0).2
      ⟨hf0Fam, ⟨j, hcoord0⟩⟩
  have hcount1 :
      faceIncidenceCount cellsRoot
        (Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m)) f0 = 1 := by
    classical
    let S := cellsRoot.filter
      (fun c =>
        Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m) c f0)
    have hc0S : Fixpoint.KuhnSubdivision.starCell p j hj ∈ S := by
      exact Finset.mem_filter.2 ⟨hc0CellsRoot, hI0⟩
    have hS :
        S = ({Fixpoint.KuhnSubdivision.starCell p j hj}
          : Finset (Fixpoint.KuhnSubdivision.Cell n m)) := by
      ext c
      constructor
      · intro hc
        have hcEq : c = Fixpoint.KuhnSubdivision.starCell p j hj :=
          huniq c (Finset.mem_filter.1 hc).1 (Finset.mem_filter.1 hc).2
        simp [hcEq]
      · intro hc
        have hcEq : c = Fixpoint.KuhnSubdivision.starCell p j hj := by simpa using hc
        subst hcEq
        exact hc0S
    have hcardS : S.card = 1 := by
      rw [hS]
      simp
    simpa [faceIncidenceCount, S] using hcardS
  refine ⟨p, j, hj, hj1, ?_⟩
  exact ⟨hf0Bnd, hcount1⟩

/--
Hard interior-style count-control slice:
for `n > 1`, one shared facet has exact incidence count `2`
on the concrete two-cell slice formed by the witness pair in
`permCellsAtScale`.
-/
theorem exists_sharedFacet_countTwo_on_pairSlice_from_kuhn
    {n m : ℕ} (h1n : 1 < n) (hm : 0 < m) :
    ∃ p : Fixpoint.KuhnSubdivision.GridVertex n m,
      ∃ σ : Equiv.Perm (Fixpoint.KuhnSubdivision.Idx n),
        ∃ c₁ c₂ : Fixpoint.KuhnSubdivision.Cell n m,
          ∃ face : Finset (Fixpoint.KuhnSubdivision.GridVertex n m),
            c₁ ≠ c₂ ∧
            c₁ ∈ Fixpoint.KuhnSubdivision.permCellsAtScale (n := n) (m := m) ∧
            c₂ ∈ Fixpoint.KuhnSubdivision.permCellsAtScale (n := n) (m := m) ∧
            face ∈ Fixpoint.KuhnSubdivision.facetFamily
              (n := n) (m := m)
              (Fixpoint.KuhnSubdivision.permCellsAtScale (n := n) (m := m)) ∧
            faceIncidenceCount ({c₁, c₂} : Finset (Fixpoint.KuhnSubdivision.Cell n m))
              (Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m))
              face = 2 := by
  have hn : 0 < n := lt_trans Nat.zero_lt_one h1n
  rcases Fixpoint.KuhnSubdivision.exists_coord_eq_one (n := n) (m := m) hn hm with
    ⟨p, j, hj1, hj⟩
  let σ : Equiv.Perm (Fixpoint.KuhnSubdivision.Idx n) := Equiv.swap 0 j
  have h0 : 0 < p.1 (σ 0) := by
    simpa [σ] using hj
  rcases Fixpoint.KuhnSubdivision.exists_twoIncidence_witness_in_permCellsAtScale
      (n := n) (m := m) h1n σ p h0 with
    ⟨c₁, c₂, face, hc₁, hc₂, hneq, hI₁, hI₂, hfaceFam⟩
  have hcover :
      ∀ c ∈ ({c₁, c₂} : Finset (Fixpoint.KuhnSubdivision.Cell n m)),
        Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m) c face →
        c = c₁ ∨ c = c₂ := by
    intro c hc _hinc
    rcases Finset.mem_insert.1 hc with rfl | hc'
    · exact Or.inl rfl
    · have hc2 : c = c₂ := by simpa using hc'
      exact Or.inr hc2
  have hcount2 :
      faceIncidenceCount ({c₁, c₂} : Finset (Fixpoint.KuhnSubdivision.Cell n m))
        (Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m))
        face = 2 := by
    exact faceIncidenceCount_eq_two_of_pair_witness_generic
      ({c₁, c₂} : Finset (Fixpoint.KuhnSubdivision.Cell n m))
      (Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m))
      face c₁ c₂ (by simp) hI₁ (by simp) hI₂ hneq hcover
  refine ⟨p, σ, c₁, c₂, face, hneq, hc₁, hc₂, hfaceFam, hcount2⟩

/--
Global-family interior lower bound:
for `n > 1`, `m > 0`, some shared facet in `permCellsAtScale` has incidence count at least `2`.
-/
theorem exists_sharedFacet_countAtLeastTwo_in_permCellsAtScale_from_kuhn
    {n m : ℕ} (h1n : 1 < n) (hm : 0 < m) :
    ∃ p : Fixpoint.KuhnSubdivision.GridVertex n m,
      ∃ σ : Equiv.Perm (Fixpoint.KuhnSubdivision.Idx n),
        ∃ face : Finset (Fixpoint.KuhnSubdivision.GridVertex n m),
          face ∈ Fixpoint.KuhnSubdivision.facetFamily
            (n := n) (m := m)
            (Fixpoint.KuhnSubdivision.permCellsAtScale (n := n) (m := m)) ∧
          2 ≤ faceIncidenceCount
                (Fixpoint.KuhnSubdivision.permCellsAtScale (n := n) (m := m))
                (Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m))
                face := by
  have hn : 0 < n := lt_trans Nat.zero_lt_one h1n
  rcases Fixpoint.KuhnSubdivision.exists_coord_eq_one (n := n) (m := m) hn hm with
    ⟨p, j, hj1, hj⟩
  let σ : Equiv.Perm (Fixpoint.KuhnSubdivision.Idx n) := Equiv.swap 0 j
  have h0 : 0 < p.1 (σ 0) := by
    simpa [σ] using hj
  rcases Fixpoint.KuhnSubdivision.exists_twoIncidence_witness_in_permCellsAtScale
      (n := n) (m := m) h1n σ p h0 with
    ⟨c₁, c₂, face, hc₁, hc₂, hneq, hI₁, hI₂, hfaceFam⟩
  have htwo :
      2 ≤ faceIncidenceCount
            (Fixpoint.KuhnSubdivision.permCellsAtScale (n := n) (m := m))
            (Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m))
            face := by
    classical
    let S :=
      (Fixpoint.KuhnSubdivision.permCellsAtScale (n := n) (m := m)).filter
        (fun c =>
          Fixpoint.KuhnSubdivision.FaceIncidentByFacet (n := n) (m := m) c face)
    have hc₁S : c₁ ∈ S := Finset.mem_filter.2 ⟨hc₁, hI₁⟩
    have hc₂S : c₂ ∈ S := Finset.mem_filter.2 ⟨hc₂, hI₂⟩
    have hcard2 : 2 ≤ S.card := by
      have hsubset : ({c₁, c₂} : Finset (Fixpoint.KuhnSubdivision.Cell n m)) ⊆ S := by
        intro c hc
        rcases Finset.mem_insert.1 hc with rfl | hc'
        · exact hc₁S
        · have : c = c₂ := by simpa using hc'
          subst this
          exact hc₂S
      have hle := Finset.card_le_card hsubset
      have hpair : ({c₁, c₂} : Finset (Fixpoint.KuhnSubdivision.Cell n m)).card = 2 := by
        simp [hneq]
      simpa [hpair] using hle
    simpa [faceIncidenceCount, S] using hcard2
  exact ⟨p, σ, face, hfaceFam, htwo⟩

/--
Boundary-face existence directly on the permutation-chain family `permCellsAtScale`.
-/
theorem exists_boundaryFace_in_permCellsAtScale_from_kuhn
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ∃ f0 : Finset (Fixpoint.KuhnSubdivision.GridVertex n m),
      f0 ∈ boundaryFaces
        (Fixpoint.KuhnSubdivision.facetFamily
          (n := n) (m := m)
          (Fixpoint.KuhnSubdivision.permCellsAtScale (n := n) (m := m))) := by
  rcases Fixpoint.KuhnSubdivision.exists_coord_eq_one (n := n) (m := m) hn hm with
    ⟨p, j, hj1, hj⟩
  let σ : Equiv.Perm (Fixpoint.KuhnSubdivision.Idx n) := Equiv.swap 0 j
  have hσ : 0 < p.1 (σ 0) := by
    simpa [σ] using hj
  let c0 : Fixpoint.KuhnSubdivision.Cell n m :=
    Fixpoint.KuhnSubdivision.permChainCell (n := n) (m := m) σ p hσ
  let f0 : Finset (Fixpoint.KuhnSubdivision.GridVertex n m) :=
    Fixpoint.KuhnSubdivision.cellFacet (n := n) (m := m) c0 0
  have hp : p ∈ Fixpoint.KuhnSubdivision.allGridVertices (n := n) (m := m) :=
    Fixpoint.KuhnSubdivision.mem_allGridVertices (n := n) (m := m) p
  have hc0 :
      c0 ∈ Fixpoint.KuhnSubdivision.permCellsAtScale (n := n) (m := m) := by
    exact (Fixpoint.KuhnSubdivision.mem_permCellsFromRoots_iff (n := n) (m := m)
      (Fixpoint.KuhnSubdivision.allGridVertices (n := n) (m := m)) c0).2
      ⟨p, hp, σ, hσ, rfl⟩
  have hf0Fam :
      f0 ∈ Fixpoint.KuhnSubdivision.facetFamily
        (n := n) (m := m)
        (Fixpoint.KuhnSubdivision.permCellsAtScale (n := n) (m := m)) := by
    exact (Fixpoint.KuhnSubdivision.mem_facetFamily_iff (n := n) (m := m)
      (Fixpoint.KuhnSubdivision.permCellsAtScale (n := n) (m := m)) f0).2
      ⟨c0, hc0, 0, rfl⟩
  have hσ1 : p.1 (σ 0) = 1 := by
    simpa [σ] using hj1
  have hcoord0 :
      ∀ v ∈ f0, v.1 (σ 0) = 0 := by
    simpa [f0, c0] using
      (Fixpoint.KuhnSubdivision.all_zeroFacet_coords_zero_permChainCell_of_coord_one
        (n := n) (m := m) hn σ p hσ hσ1)
  refine ⟨f0, ?_⟩
  exact (mem_boundaryFaces_iff
    (Fixpoint.KuhnSubdivision.facetFamily
      (n := n) (m := m)
      (Fixpoint.KuhnSubdivision.permCellsAtScale (n := n) (m := m))) f0).2
    ⟨hf0Fam, ⟨σ 0, hcoord0⟩⟩

end KuhnBridge

section Dim1

/-- A simple chain of grid vertices on the 1-simplex (`Fin 2`). -/
def chainVertex1 (m k : ℕ) : GridVertex 1 m := by
  refine ⟨fun i => Fin.cases (m - Nat.min k m) (Nat.min k m) i, ?_⟩
  have hsum : (m - Nat.min k m) + Nat.min k m = m :=
    Nat.sub_add_cancel (Nat.min_le_right k m)
  simpa [Fin.sum_univ_two, hsum]

lemma fin2_eq_zero_of_ne_one {x : Idx 1} (hx : x ≠ (1 : Idx 1)) : x = 0 := by
  fin_cases x <;> simp at hx ⊢

lemma fin2_eq_one_of_ne_zero {x : Idx 1} (hx : x ≠ (0 : Idx 1)) : x = 1 := by
  fin_cases x <;> simp at hx ⊢

@[simp] lemma chainVertex1_coord0 {m k : ℕ} (hk : k ≤ m) :
    (chainVertex1 m k).1 0 = m - k := by
  change m - Nat.min k m = m - k
  simp [Nat.min_eq_left hk]

@[simp] lemma chainVertex1_coord1 {m k : ℕ} (hk : k ≤ m) :
    (chainVertex1 m k).1 1 = k := by
  change Nat.min k m = k
  simp [Nat.min_eq_left hk]

lemma coordDiffLeOne_chainVertex1_pred_succ
    {m k : ℕ} (hkpos : 0 < k) (hkle : k ≤ m) :
    CoordDiffLeOne (chainVertex1 m (k - 1)) (chainVertex1 m k) := by
  intro i
  fin_cases i
  · have hkpredle : k - 1 ≤ m := le_trans (Nat.sub_le _ _) hkle
    have hk' : m - (k - 1) = m - k + 1 := by
      have hkpos' : 1 ≤ k := Nat.succ_le_iff.mpr hkpos
      omega
    calc
      |(((chainVertex1 m (k - 1)).1 0 : ℝ) - ((chainVertex1 m k).1 0 : ℝ))|
          = |((m - (k - 1) : ℕ) : ℝ) - ((m - k : ℕ) : ℝ)| := by
              simp [chainVertex1_coord0 hkpredle, chainVertex1_coord0 hkle]
      _ = |((m - k + 1 : ℕ) : ℝ) - ((m - k : ℕ) : ℝ)| := by simp [hk']
      _ = 1 := by
            have hdiff : (((m - k + 1 : ℕ) : ℝ) - ((m - k : ℕ) : ℝ)) = 1 := by
              norm_num
            rw [hdiff, abs_one]
      _ ≤ 1 := le_rfl
  · have hkpredle : k - 1 ≤ m := le_trans (Nat.sub_le _ _) hkle
    calc
      |(((chainVertex1 m (k - 1)).1 1 : ℝ) - ((chainVertex1 m k).1 1 : ℝ))|
          = |((k - 1 : ℕ) : ℝ) - (k : ℝ)| := by
              simp [chainVertex1_coord1 hkpredle, chainVertex1_coord1 hkle]
      _ = 1 := by
            have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
            have hkcast : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
              exact_mod_cast hkpred.symm
            rw [hkcast]
            norm_num
      _ ≤ 1 := le_rfl

/--
One-dimensional Sperner: a boundary-admissible labeling on a 1-simplex grid
contains a fully-labeled edge.
-/
theorem exists_fullyLabeled_pair_dim1
    {m : ℕ}
    (L : Labeling 1 m) (hbd : BoundaryAdmissible L) :
    ∃ v : Idx 1 → GridVertex 1 m, FullyLabeled L v := by
  have h0ne1 : L (chainVertex1 m 0) ≠ (1 : Idx 1) := by
    apply hbd (chainVertex1 m 0) 1
    change Nat.min 0 m = 0
    simp
  have h0eq0 : L (chainVertex1 m 0) = 0 := fin2_eq_zero_of_ne_one h0ne1
  have hmne0 : L (chainVertex1 m m) ≠ (0 : Idx 1) := by
    apply hbd (chainVertex1 m m) 0
    simp [chainVertex1]
  have hmeq1 : L (chainVertex1 m m) = 1 := fin2_eq_one_of_ne_zero hmne0
  have hex : ∃ k : ℕ, k ≤ m ∧ L (chainVertex1 m k) = (1 : Idx 1) := ⟨m, le_rfl, hmeq1⟩
  let k0 : ℕ := Nat.find hex
  have hk0le : k0 ≤ m := (Nat.find_spec hex).1
  have hk0lab : L (chainVertex1 m k0) = (1 : Idx 1) := (Nat.find_spec hex).2
  have hk0pos : 0 < k0 := by
    by_contra hk0npos
    have hk0eq0 : k0 = 0 := Nat.eq_zero_of_not_pos hk0npos
    exact h0ne1 (by simpa [hk0eq0] using hk0lab)
  have hpred_ne1 : L (chainVertex1 m (k0 - 1)) ≠ (1 : Idx 1) := by
    intro hpred1
    have hpred_witness : k0 - 1 ≤ m ∧ L (chainVertex1 m (k0 - 1)) = (1 : Idx 1) := by
      refine ⟨le_trans (Nat.sub_le _ _) hk0le, hpred1⟩
    have hle : k0 ≤ k0 - 1 := Nat.find_min' hex hpred_witness
    have hlt : k0 - 1 < k0 := Nat.sub_lt hk0pos (by decide)
    exact (not_lt_of_ge hle) hlt
  have hpred_eq0 : L (chainVertex1 m (k0 - 1)) = 0 := fin2_eq_zero_of_ne_one hpred_ne1
  let v : Idx 1 → GridVertex 1 m := ![chainVertex1 m (k0 - 1), chainVertex1 m k0]
  refine ⟨v, ?_⟩
  intro i
  fin_cases i
  · refine ⟨0, ?_⟩
    simp [v, hpred_eq0]
  · refine ⟨1, ?_⟩
    simp [v, hk0lab]

/--
One-dimensional Sperner with mesh control:
a boundary-admissible labeling on a 1-simplex grid contains a fully-labeled mesh edge.
-/
theorem exists_fullyLabeled_mesh_pair_dim1
    {m : ℕ}
    (L : Labeling 1 m) (hbd : BoundaryAdmissible L) :
    ∃ v : Cell 1 m, IsMeshCell v ∧ FullyLabeled L v := by
  have h0ne1 : L (chainVertex1 m 0) ≠ (1 : Idx 1) := by
    apply hbd (chainVertex1 m 0) 1
    change Nat.min 0 m = 0
    simp
  have h0eq0 : L (chainVertex1 m 0) = 0 := fin2_eq_zero_of_ne_one h0ne1
  have hmne0 : L (chainVertex1 m m) ≠ (0 : Idx 1) := by
    apply hbd (chainVertex1 m m) 0
    simp [chainVertex1]
  have hmeq1 : L (chainVertex1 m m) = 1 := fin2_eq_one_of_ne_zero hmne0
  have hex : ∃ k : ℕ, k ≤ m ∧ L (chainVertex1 m k) = (1 : Idx 1) := ⟨m, le_rfl, hmeq1⟩
  let k0 : ℕ := Nat.find hex
  have hk0le : k0 ≤ m := (Nat.find_spec hex).1
  have hk0lab : L (chainVertex1 m k0) = (1 : Idx 1) := (Nat.find_spec hex).2
  have hk0pos : 0 < k0 := by
    by_contra hk0npos
    have hk0eq0 : k0 = 0 := Nat.eq_zero_of_not_pos hk0npos
    exact h0ne1 (by simpa [hk0eq0] using hk0lab)
  have hpred_ne1 : L (chainVertex1 m (k0 - 1)) ≠ (1 : Idx 1) := by
    intro hpred1
    have hpred_witness : k0 - 1 ≤ m ∧ L (chainVertex1 m (k0 - 1)) = (1 : Idx 1) := by
      refine ⟨le_trans (Nat.sub_le _ _) hk0le, hpred1⟩
    have hle : k0 ≤ k0 - 1 := Nat.find_min' hex hpred_witness
    have hlt : k0 - 1 < k0 := Nat.sub_lt hk0pos (by decide)
    exact (not_lt_of_ge hle) hlt
  have hpred_eq0 : L (chainVertex1 m (k0 - 1)) = 0 := fin2_eq_zero_of_ne_one hpred_ne1
  let v : Cell 1 m := ![chainVertex1 m (k0 - 1), chainVertex1 m k0]
  refine ⟨v, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · intro t; simp [v]
    · simpa [v] using coordDiffLeOne_chainVertex1_pred_succ hk0pos hk0le
    · intro t
      have hmesh : CoordDiffLeOne (chainVertex1 m (k0 - 1)) (chainVertex1 m k0) :=
        coordDiffLeOne_chainVertex1_pred_succ hk0pos hk0le
      have := hmesh t
      simpa [abs_sub_comm, v] using this
    · intro t; simp [v]
  · intro i
    fin_cases i
    · refine ⟨0, ?_⟩
      simp [v, hpred_eq0]
    · refine ⟨1, ?_⟩
      simp [v, hk0lab]

/-- One-dimensional fully-labeled edge existence for the canonical `gridLabel`. -/
theorem exists_fullyLabeled_pair_dim1_gridLabel
    {m : ℕ} (f : stdSimplex ℝ (Idx 1) → stdSimplex ℝ (Idx 1))
    (hm : 0 < m) :
    ∃ v : Idx 1 → GridVertex 1 m,
      FullyLabeled (fun p : GridVertex 1 m => gridLabel f hm p) v := by
  refine exists_fullyLabeled_pair_dim1
    (L := fun p : GridVertex 1 m => gridLabel f hm p) ?_
  exact boundaryAdmissible_gridLabel (f := f) hm

/-- One-dimensional fully-labeled mesh edge existence for canonical `gridLabel`. -/
theorem exists_fullyLabeled_mesh_pair_dim1_gridLabel
    {m : ℕ} (f : stdSimplex ℝ (Idx 1) → stdSimplex ℝ (Idx 1))
    (hm : 0 < m) :
    ∃ v : Cell 1 m,
      IsMeshCell v ∧
      FullyLabeled (fun p : GridVertex 1 m => gridLabel f hm p) v := by
  refine exists_fullyLabeled_mesh_pair_dim1
    (L := fun p : GridVertex 1 m => gridLabel f hm p) ?_
  exact boundaryAdmissible_gridLabel (f := f) hm

/--
Dimension-1 odd-cardinality witness at each scale from a singleton fully-labeled mesh edge.
-/
theorem exists_odd_data_dim1_gridLabel
    (f : stdSimplex ℝ (Idx 1) → stdSimplex ℝ (Idx 1)) :
    ∀ (m : ℕ) (hm : 0 < m),
      ∃ cells : Finset (Cell 1 m),
        (∀ c ∈ cells, IsMeshCell c) ∧
        (fullyLabeledCells (fun p : GridVertex 1 m => gridLabel f hm p) cells).card % 2 = 1 := by
  intro m hm
  rcases exists_fullyLabeled_mesh_pair_dim1_gridLabel (f := f) hm with ⟨v, hvMesh, hvFull⟩
  refine ⟨{v}, ?_, ?_⟩
  · intro c hc
    have hc' : c = v := by simpa using Finset.mem_singleton.mp hc
    simpa [hc'] using hvMesh
  · classical
    let L : Labeling 1 m := fun p : GridVertex 1 m => gridLabel f hm p
    have hEq : fullyLabeledCells L ({v} : Finset (Cell 1 m)) = ({v} : Finset (Cell 1 m)) := by
      ext c
      constructor
      · intro hc
        exact (mem_fullyLabeledCells L ({v} : Finset (Cell 1 m)) c).1 hc |>.1
      · intro hc
        have hc' : c = v := by simpa using Finset.mem_singleton.mp hc
        exact (mem_fullyLabeledCells L ({v} : Finset (Cell 1 m)) c).2
          ⟨hc, by simpa [L, hc'] using hvFull⟩
    rw [hEq]
    norm_num

/-- Dimension-1 Brouwer via odd-cardinality cell data pipeline. -/
theorem exists_fixedPoint_dim1_of_continuous
    (f : stdSimplex ℝ (Idx 1) → stdSimplex ℝ (Idx 1))
    (hcont : Continuous f) :
    ∃ x : stdSimplex ℝ (Idx 1), Function.IsFixedPt f x := by
  exact exists_fixedPoint_of_odd_card_fullyLabeledCells_at_scales
    (f := f) hcont (exists_odd_data_dim1_gridLabel (f := f))

end Dim1

end SpernerParity

end Fixpoint
