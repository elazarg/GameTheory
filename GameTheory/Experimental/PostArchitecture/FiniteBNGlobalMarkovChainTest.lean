/-
# EXP-104: hostile heterogeneous chain consumer

This file exercises canonical MAID global-Markov soundness on a nonconstant
Boolean-to-ternary-to-Boolean chain.  Conditioning on the middle coordinate
separates the endpoints; removing that evidence exposes both the graph path
and the induced endpoint dependence.
-/

import GameTheory.Experimental.PostArchitecture.MAIDGlobalMarkovSoundness

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovChainTest

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Strategic
open GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation
open GameTheory.Experimental.PostArchitecture.MAIDGlobalMarkovSoundness
open GameTheory.Experimental.PostArchitecture.MAIDRequisiteObservation

abbrev Node := FiniteBNMoralSeparation.ControlNode

deriving instance Fintype for FiniteBNMoralSeparation.ControlNode

def Value : Node → Type
  | .left => Bool
  | .middle => Fin 3
  | .right => Bool

def topological : GameTheory.Math.DAG.TopologicalOrder Chain.parents where
  order := [.left, .middle, .right]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index
    · simp [Chain.parents] at hparent
    · have hleft : parent = .left := by
        simpa [Chain.parents] using hparent
      subst parent
      exact ⟨0, by decide, rfl⟩
    · have hmiddle : parent = .middle := by
        simpa [Chain.parents] using hparent
      subst parent
      exact ⟨1, by decide, rfl⟩

def model : Structure Unit Node where
  kind _ := .chance
  parents := Chain.parents
  observedParents := Chain.parents
  Value := Value
  observed_sub _ := Finset.Subset.rfl
  observed_eq_of_chance _ _ := rfl
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder topological

instance valueFintype (node : Node) : Fintype (model.Value node) := by
  cases node with
  | left => exact inferInstanceAs (Fintype Bool)
  | middle => exact inferInstanceAs (Fintype (Fin 3))
  | right => exact inferInstanceAs (Fintype Bool)

instance valueDecidableEq (node : Node) : DecidableEq (model.Value node) := by
  cases node with
  | left => exact inferInstanceAs (DecidableEq Bool)
  | middle => exact inferInstanceAs (DecidableEq (Fin 3))
  | right => exact inferInstanceAs (DecidableEq Bool)

def fairBool : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

def encode : Bool → Fin 3
  | false => 0
  | true => 1

def decode (value : Fin 3) : Bool := value = 1

def semantics : Semantics model where
  defaultValue node := by
    cases node with
    | left => exact false
    | middle => exact (0 : Fin 3)
    | right => exact false
  chanceLaw node _ configuration := by
    cases node with
    | left => exact fairBool
    | middle =>
        exact FinDist.pure
          (encode (configuration ⟨.left, by simp [model, Chain.parents]⟩))
    | right =>
        exact FinDist.pure
          (decode (configuration ⟨.middle, by simp [model, Chain.parents]⟩))
  utility _ _ := 0

def policy : Profile (nativeBehavioralSignature model) := by
  intro owner site
  rcases site with ⟨node, hdecision⟩
  cases node <;> simp [model] at hdecision

def law : FinDist (Assignment model) :=
  (nativeBehavioralGameForm semantics).play policy

theorem effectiveParents_eq : effectiveParents model = Chain.parents := by
  funext node
  cases node <;> rfl

theorem separated_by_middle :
    Separates (effectiveParents model) queryFirst querySecond
      Chain.middleEvidence := by
  rw [effectiveParents_eq]
  exact Chain.separated_by_middle

/-- The canonical evaluator, factorization bridge, moral separation, and
global-Markov theorem compose on genuinely dependent value domains. -/
theorem endpoints_independent_given_middle :
    CoordinatesConditionallyIndependent law queryFirst querySecond
      Chain.middleEvidence := by
  exact native_coordinatesConditionallyIndependent_of_moralSeparation
    topological semantics policy queryFirst querySecond Chain.middleEvidence
      (by decide) (by decide) (by decide) separated_by_middle

/-- The preceding result has its full arbitrary-configuration meaning, rather
than only a same-witness specialization. -/
theorem arbitrary_config_cross_product
    (firstConfiguration : Config model queryFirst)
    (secondConfiguration : Config model querySecond)
    (evidenceConfiguration : Config model Chain.middleEvidence) :
    law.probOf
          (tripleCylinder queryFirst querySecond Chain.middleEvidence
            firstConfiguration secondConfiguration evidenceConfiguration) *
        law.probOf (cylinder Chain.middleEvidence evidenceConfiguration) =
      law.probOf
          (pairCylinder queryFirst Chain.middleEvidence
            firstConfiguration evidenceConfiguration) *
        law.probOf
          (pairCylinder querySecond Chain.middleEvidence
            secondConfiguration evidenceConfiguration) := by
  exact (coordinatesConditionallyIndependent_iff_cylinders law
    queryFirst querySecond Chain.middleEvidence).mp
      endpoints_independent_given_middle _ _ _

/-- Without conditioning, the live chain path remains open. -/
theorem not_separated_without_evidence :
    ¬ Separates (effectiveParents model) queryFirst querySecond
      Chain.noEvidence := by
  rw [effectiveParents_eq]
  exact Chain.not_separated_without_evidence

end GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovChainTest
