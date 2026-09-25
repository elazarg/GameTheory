/-
# Sampling finitely many coordinates of a dependent assignment

The selected coordinates have independent PMF laws. A total assignment
supplies deterministic values elsewhere; coordinate carriers may be infinite.
-/

import GameTheory.Math.Probability.Product
import GameTheory.Math.Probability.Support

noncomputable section

namespace GameTheory.Math.Probability.FiniteAssignment

universe uι uA

variable {ι : Type uι} {A : ι → Type uA}

/-- Insert a finite dependent tuple into a total fallback assignment. -/
def resolve [DecidableEq ι] (fallback : ∀ i, A i) (sites : Finset ι)
    (draw : ∀ i : sites, A i) : ∀ i, A i :=
  fun i => if hi : i ∈ sites then draw ⟨i, hi⟩ else fallback i

@[simp]
theorem resolve_of_mem [DecidableEq ι] (fallback : ∀ i, A i)
    (sites : Finset ι) (draw : ∀ i : sites, A i)
    {i : ι} (hi : i ∈ sites) :
    resolve fallback sites draw i = draw ⟨i, hi⟩ := by
  simp [resolve, hi]

@[simp]
theorem resolve_of_not_mem [DecidableEq ι] (fallback : ∀ i, A i)
    (sites : Finset ι) (draw : ∀ i : sites, A i)
    {i : ι} (hi : i ∉ sites) :
    resolve fallback sites draw i = fallback i := by
  simp [resolve, hi]

theorem resolve_restrict_of_mem [DecidableEq ι]
    (fallback assignment : ∀ i, A i) (sites : Finset ι)
    {i : ι} (hi : i ∈ sites) :
    resolve fallback sites (sites.restrict assignment) i = assignment i := by
  rw [resolve_of_mem fallback sites _ hi]
  rfl

/-- Replace one coordinate of a dependent assignment. -/
def setOne [DecidableEq ι] (assignment : ∀ i, A i) (entry : Sigma A) :
    ∀ i, A i :=
  resolve assignment {entry.1} fun index => by
    have hindex : index.1 = entry.1 := Finset.mem_singleton.mp index.2
    cases index with
    | mk value _ =>
      dsimp only at hindex
      subst value
      exact entry.2

@[simp]
theorem setOne_same [DecidableEq ι] (assignment : ∀ i, A i)
    {i : ι} (value : A i) :
    setOne assignment ⟨i, value⟩ i = value := by
  simp [setOne, resolve]

@[simp]
theorem setOne_other [DecidableEq ι] (assignment : ∀ i, A i)
    {i j : ι} (value : A i) (hji : j ≠ i) :
    setOne assignment ⟨i, value⟩ j = assignment j := by
  simp [setOne, resolve, hji]

/-- Draw coordinates in list order and write their values into an assignment. -/
def runOrdered [DecidableEq ι] (laws : ∀ i, PMF (A i)) :
    List ι → (∀ i, A i) → PMF (∀ i, A i)
  | [], assignment => PMF.pure assignment
  | index :: rest, assignment =>
    (laws index).bind fun value =>
      runOrdered laws rest (setOne assignment ⟨index, value⟩)

/-- Independently sample selected coordinates and fill the rest from a total
fallback assignment. -/
def sampleOn [DecidableEq ι] (laws : ∀ i, PMF (A i))
    (sites : Finset ι) (fallback : ∀ i, A i) : PMF (∀ i, A i) :=
  (independentProduct (fun i : sites => laws i)).map
    (resolve fallback sites)

theorem sampleOn_pure [DecidableEq ι] (fallback : ∀ i, A i)
    (sites : Finset ι) :
    sampleOn (fun i => PMF.pure (fallback i)) sites fallback =
      PMF.pure fallback := by
  rw [sampleOn, independentProduct_pure, PMF.pure_map]
  congr 1
  funext i
  by_cases hi : i ∈ sites
  · simp [hi]
  · simp [hi]

theorem sampleOn_map_eval_of_mem [DecidableEq ι]
    (laws : ∀ i, PMF (A i)) (sites : Finset ι)
    (fallback : ∀ i, A i) {i : ι} (hi : i ∈ sites) :
    (sampleOn laws sites fallback).map (fun assignment => assignment i) =
      laws i := by
  rw [sampleOn, PMF.map_comp]
  have heq : (fun draw : ∀ j : sites, A j =>
      resolve fallback sites draw i) =
      (fun draw => draw ⟨i, hi⟩) := by
    funext draw
    exact resolve_of_mem fallback sites draw hi
  simp only [Function.comp_def]
  rw [heq]
  exact independentProduct_map_eval (fun j : sites => laws j) ⟨i, hi⟩

theorem sampleOn_map_eval_of_not_mem [DecidableEq ι]
    (laws : ∀ i, PMF (A i)) (sites : Finset ι)
    (fallback : ∀ i, A i) {i : ι} (hi : i ∉ sites) :
    (sampleOn laws sites fallback).map (fun assignment => assignment i) =
      PMF.pure (fallback i) := by
  rw [sampleOn, PMF.map_comp]
  have heq : (fun draw : ∀ j : sites, A j =>
      resolve fallback sites draw i) = fun _ => fallback i := by
    funext draw
    exact resolve_of_not_mem fallback sites draw hi
  simp only [Function.comp_def]
  rw [heq]
  exact PMF.map_const _ _

/-- Split finite sampling at a selected coordinate while keeping the same site set.
The continuation replaces that coordinate law by the drawn point mass. -/
theorem sampleOn_factor_of_mem [DecidableEq ι]
    (laws : ∀ i, PMF (A i)) (sites : Finset ι)
    (fallback : ∀ i, A i) {j : ι} (hj : j ∈ sites)
    (committed : A j → ∀ i, PMF (A i))
    (hself : ∀ a, committed a j = PMF.pure a)
    (hother : ∀ a i, i ≠ j → committed a i = laws i) :
    sampleOn laws sites fallback =
      (laws j).bind (fun a => sampleOn (committed a) sites fallback) := by
  classical
  let k : sites := ⟨j, hj⟩
  rw [sampleOn, independentProduct_splitAt (fun i : sites => laws i) k,
    PMF.map_bind]
  apply bind_congr_on_support
  intro a _
  rw [sampleOn, independentProduct_splitAt (fun i : sites => committed a i) k]
  have hhead : committed a k = PMF.pure a := hself a
  have htail : (fun i : {i : sites // i ≠ k} => committed a i.1) =
      (fun i : {i : sites // i ≠ k} => laws i.1) := by
    funext i
    apply hother
    intro heq
    apply i.2
    exact Subtype.ext heq
  rw [hhead, htail, PMF.pure_bind, PMF.map_comp]

/-- Sampling every coordinate is the full independent product. -/
theorem sampleOn_univ [Fintype ι] [DecidableEq ι]
    (laws : ∀ i, PMF (A i)) (fallback : ∀ i, A i) :
    sampleOn laws Finset.univ fallback = independentProduct laws := by
  classical
  ext assignment
  rw [sampleOn, PMF.map_apply, independentProduct_apply]
  let draws : ∀ i : (Finset.univ : Finset ι), A i :=
    fun i => assignment i.1
  rw [tsum_eq_single draws]
  · have hresolve : resolve fallback Finset.univ draws = assignment := by
      funext i
      simp [resolve, draws]
    simp [hresolve, independentProduct_apply, Finset.prod_attach_univ, draws]
  · intro other hne
    have hresolved : resolve fallback Finset.univ other ≠ assignment := by
      intro heq
      apply hne
      funext i
      have hi := congrFun heq i.1
      simpa [resolve, draws] using hi
    simp [Ne.symm hresolved]

/-- A duplicate-free ordered draw has the law of simultaneous sampling on
the listed coordinates. The initial assignment is used outside that list. -/
theorem runOrdered_eq_sampleOn [DecidableEq ι] (laws : ∀ i, PMF (A i)) :
    ∀ indices : List ι, indices.Nodup → ∀ fallback : ∀ i, A i,
      runOrdered laws indices fallback =
        sampleOn laws indices.toFinset fallback := by
  intro indices
  induction indices with
  | nil =>
      intro _ fallback
      let emptyDraw : ∀ i : {i : ι // i ∈ ([] : List ι).toFinset}, A i.1 :=
        fun i => False.elim (List.not_mem_nil (List.mem_toFinset.mp i.2))
      have hlaws : (fun i : {i : ι // i ∈ ([] : List ι).toFinset} => laws i.1) =
          fun i => PMF.pure (emptyDraw i) := by
        funext i
        exact False.elim (List.not_mem_nil (List.mem_toFinset.mp i.2))
      rw [runOrdered, sampleOn, hlaws, independentProduct_pure, PMF.pure_map]
      congr 1
  | cons head tail ih =>
      intro hnodup fallback
      have hheadNotMem : head ∉ tail := (List.nodup_cons.mp hnodup).1
      have htailNodup : tail.Nodup := (List.nodup_cons.mp hnodup).2
      have hheadNotFinset : head ∉ tail.toFinset := by simpa using hheadNotMem
      let full := {i : ι // i ∈ (head :: tail).toFinset}
      let headIndex : full := ⟨head, by simp⟩
      let remaining := {i : full // i ≠ headIndex}
      let tailIndex := {i : ι // i ∈ tail.toFinset}
      let remainingEquiv : tailIndex ≃ remaining :=
        { toFun := fun i => ⟨⟨i.1, by simp [i.2]⟩, by
            intro heq
            have hvalue : i.1 = head := by
              simpa [headIndex] using congrArg (fun value : full => value.1) heq
            have htail : head ∈ tail.toFinset := by
              rw [← hvalue]
              exact i.2
            exact hheadNotFinset htail⟩
          invFun := fun i => ⟨i.1.1, by
            have hmem : i.1.1 = head ∨ i.1.1 ∈ tail.toFinset := by
              simpa using i.1.2
            rcases hmem with hhead | htail
            · exfalso
              apply i.2
              apply Subtype.ext
              exact hhead
            · exact htail⟩
          left_inv := fun i => Subtype.ext rfl
          right_inv := fun i => Subtype.ext rfl }
      let remainingValue (i : remaining) := A i.1.1
      let remainingLaws (i : remaining) : PMF (remainingValue i) := laws i.1.1
      have hreindex :
          (independentProduct remainingLaws).map
              (Equiv.piCongrLeft remainingValue remainingEquiv).symm =
            independentProduct (fun i : tailIndex => laws i.1) := by
        simpa [remainingEquiv, remainingValue, remainingLaws, tailIndex] using
          independentProduct_reindex remainingEquiv.symm remainingLaws
      have hresolve (value : A head) :
          (independentProduct remainingLaws).map
              (fun draw =>
                resolve fallback (head :: tail).toFinset
                  ((Equiv.piSplitAt headIndex (fun i : full => A i.1)).symm
                    (value, draw))) =
            sampleOn laws tail.toFinset (setOne fallback ⟨head, value⟩) := by
        rw [sampleOn, ← hreindex, PMF.map_comp]
        apply congrArg (fun f => (independentProduct remainingLaws).map f)
        funext draw i
        by_cases hindexHead : i = head
        · subst i
          simp [resolve, setOne, headIndex, full, remainingEquiv,
            hheadNotFinset]
        · by_cases hindexTail : i ∈ tail.toFinset
          · simp [resolve, setOne, hindexHead, hindexTail,
              headIndex, full, remainingEquiv, remainingValue, tailIndex]
          · simp [resolve, setOne, hindexHead, hindexTail]
      rw [runOrdered]
      simp_rw [ih htailNodup]
      let fullLaws : ∀ i : full, PMF (A i.1) := fun i => laws i.1
      rw [sampleOn,
        show (fun i : {i : ι // i ∈ (head :: tail).toFinset} => laws i.1) =
          fullLaws by rfl,
        independentProduct_splitAt fullLaws headIndex, PMF.map_bind]
      apply bind_congr_on_support
      intro value _
      rw [PMF.map_comp]
      exact (hresolve value).symm

/-- An exhaustive duplicate-free schedule samples the full product law. -/
theorem runOrdered_eq_independentProduct [Fintype ι] [DecidableEq ι]
    (laws : ∀ i, PMF (A i)) (indices : List ι)
    (hnodup : indices.Nodup) (hcomplete : ∀ i, i ∈ indices)
    (fallback : ∀ i, A i) :
    runOrdered laws indices fallback = independentProduct laws := by
  rw [runOrdered_eq_sampleOn laws indices hnodup fallback]
  have hsites : indices.toFinset = Finset.univ := by
    ext i
    simp [hcomplete i]
  rw [hsites, sampleOn_univ]

end GameTheory.Math.Probability.FiniteAssignment
