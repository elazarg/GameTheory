/-
# EXP-104: global Markov with impossible evidence

This hostile consumer runs finite global-Markov soundness through a separated
three-node chain whose middle node is deterministically false.  The theorem is
then instantiated at the unsupported evidence configuration `middle = true`.
The result uses the division-free cylinder cross-product directly and requires
neither evidence positivity nor a conditional-law convention at zero mass.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovZeroEvidenceTest

open GameTheory.Languages.MAID
open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation

inductive ChainNode
  | left
  | middle
  | right
  deriving DecidableEq, Fintype

def parents : ChainNode → Finset ChainNode
  | .left => ∅
  | .middle => {.left}
  | .right => {.middle}

def topological : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.left, .middle, .right]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index
    · simp [parents] at hparent
    · have hleft : parent = .left := by
        simpa [parents] using hparent
      subst parent
      exact ⟨0, by decide, rfl⟩
    · have hmiddle : parent = .middle := by
        simpa [parents] using hparent
      subst parent
      exact ⟨1, by decide, rfl⟩

@[reducible]
def diagram : Structure Unit ChainNode where
  kind _ := .chance
  parents := parents
  observedParents := parents
  Value _ := Bool
  observed_sub _ := Finset.Subset.rfl
  observed_eq_of_chance _ _ := rfl
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder topological

def allFalse : Assignment diagram := fun _ => false

def law : FinDist (Assignment diagram) :=
  FinDist.pi fun _ => FinDist.pure false

def kernels : LocalKernels diagram.Value parents :=
  fun _ _ => FinDist.pure false

def first : Finset ChainNode := {.left}

def second : Finset ChainNode := {.right}

def evidence : Finset ChainNode := {.middle}

def impossibleEvidenceConfiguration : Config diagram evidence :=
  fun _ => true

theorem factorizes : Factorizes diagram.Value law parents kernels := by
  intro assignment
  rw [law, FinDist.prob_pi]
  simp [factorProduct, localFactor, kernels]

theorem separates : Separates parents first second evidence := by
  intro source hsource target htarget
  have hsourceEq : source = .left := by
    simpa [first] using hsource
  have htargetEq : target = .right := by
    simpa [second] using htarget
  subst source
  subst target
  rintro ⟨_, _, connection⟩
  have isolated : ∀ next,
      ¬ MoralAdjacent parents first second evidence .left next := by
    intro next adjacent
    rcases adjacent with
      ⟨hne, _, hnextOpen, _, _, hforward | hbackward | hcoparents⟩
    · cases next with
      | left => exact hne rfl
      | middle => exact hnextOpen (by simp [evidence])
      | right => simp [DirectedEdge, parents] at hforward
    · cases next <;> simp [DirectedEdge, parents] at hbackward
    · obtain ⟨child, _, hleftParent, hnextParent⟩ := hcoparents
      cases child with
      | left => simp [DirectedEdge, parents] at hleftParent
      | middle =>
          have hnextEq : next = .left := by
            cases next <;> simp [DirectedEdge, parents] at hnextParent ⊢
          exact hne hnextEq.symm
      | right => simp [DirectedEdge, parents] at hleftParent
  rcases Relation.ReflTransGen.cases_head connection with
    equality | ⟨next, firstStep, _⟩
  · cases equality
  · exact isolated next firstStep

theorem law_eq_pure : law = FinDist.pure allFalse := by
  exact FinDist.pi_pure allFalse

/-- The evidence value used below is outside the support of the chain law. -/
theorem impossibleEvidenceCylinder_mass_zero :
    law.probOf (cylinder evidence impossibleEvidenceConfiguration) = 0 := by
  classical
  have hnot : allFalse ∉ cylinder evidence impossibleEvidenceConfiguration := by
    intro hevidence
    have hvalue := congrFun hevidence
      (⟨.middle, by simp [evidence]⟩ : {node // node ∈ evidence})
    simp [Assignment.restrict, allFalse, impossibleEvidenceConfiguration] at hvalue
  rw [law_eq_pure, ← FinDist.expect_indicator_eq_probOf, FinDist.expect_pure]
  simp [hnot]

/-- Global Markov soundness applies to the deterministic chain without any
support or positivity assumption. -/
theorem conditionallyIndependent :
    CoordinatesConditionallyIndependent law first second evidence := by
  exact coordinatesConditionallyIndependent_of_factorizes_of_separates
    law parents topological kernels factorizes first second evidence
      (by simp [first, second]) (by simp [first, evidence])
        (by simp [second, evidence]) separates

/-- The arbitrary-configuration global-Markov equation at unsupported
evidence.  Its evidence factor is explicitly known to be zero. -/
theorem cross_product_at_impossible_evidence
    (firstConfiguration : Config diagram first)
    (secondConfiguration : Config diagram second) :
    law.probOf
          (tripleCylinder first second evidence firstConfiguration
            secondConfiguration impossibleEvidenceConfiguration) *
        law.probOf (cylinder evidence impossibleEvidenceConfiguration) =
      law.probOf
          (pairCylinder first evidence firstConfiguration
            impossibleEvidenceConfiguration) *
        law.probOf
          (pairCylinder second evidence secondConfiguration
            impossibleEvidenceConfiguration) := by
  exact conditionallyIndependent firstConfiguration secondConfiguration
    impossibleEvidenceConfiguration

end GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovZeroEvidenceTest
