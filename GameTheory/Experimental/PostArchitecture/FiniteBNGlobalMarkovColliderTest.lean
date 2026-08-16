/-
# EXP-104: hostile collider consumer for finite global-Markov soundness

Two independent fair Boolean roots feed a deterministic equality collider,
whose value is copied to a descendant.  The completed global-Markov theorem
must separate the roots without evidence, while conditioning on either the
collider or its descendant opens the graphical path.

The finite law is written explicitly and accompanied by a proved local-factor
certificate.  This is a test fixture, not another Bayesian-network evaluator.
-/

import GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovColliderTest

open GameTheory.Languages.MAID
open GameTheory.Math.Probability
open GameTheory.Experimental.PostArchitecture.FiniteBNCoordinateIndependence
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov
open GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovSoundness
open GameTheory.Experimental.PostArchitecture.FiniteBNMarginalization
open GameTheory.Experimental.PostArchitecture.FiniteBNMoralSeparation

inductive ColliderNode
  | first
  | second
  | collider
  | descendant
  deriving DecidableEq, Fintype

def parents : ColliderNode → Finset ColliderNode
  | .first => ∅
  | .second => ∅
  | .collider => {.first, .second}
  | .descendant => {.collider}

def topological : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.first, .second, .collider, .descendant]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index
    · simp [parents] at hparent
    · simp [parents] at hparent
    · cases parent with
      | first => exact ⟨0, by decide, rfl⟩
      | second => exact ⟨1, by decide, rfl⟩
      | collider => simp [parents] at hparent
      | descendant => simp [parents] at hparent
    · have hcollider : parent = .collider := by
        simpa [parents] using hparent
      subst parent
      exact ⟨2, by decide, rfl⟩

@[reducible]
def diagram : Structure Unit ColliderNode where
  kind _ := .chance
  parents := parents
  observedParents := parents
  Value _ := Bool
  observed_sub _ := Finset.Subset.rfl
  observed_eq_of_chance _ _ := rfl
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder topological

abbrev BNAssignment :=
  GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkov.Assignment
    diagram.Value

def world (first second : Bool) : BNAssignment
  | .first => first
  | .second => second
  | .collider => first == second
  | .descendant => first == second

def rawWorld (first second collider descendant : Bool) : BNAssignment
  | .first => first
  | .second => second
  | .collider => collider
  | .descendant => descendant

@[simp]
private theorem rawWorld_eq_world_iff (first second collider descendant x y : Bool) :
    rawWorld first second collider descendant = world x y ↔
      first = x ∧ second = y ∧ collider = (x == y) ∧ descendant = (x == y) := by
  constructor
  · intro equality
    exact ⟨congrFun equality .first, congrFun equality .second,
      congrFun equality .collider, congrFun equality .descendant⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

def fairMix {T : Type} (left right : FinDist T) : FinDist T :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) left right

def fairBool : FinDist Bool := fairMix (FinDist.pure false) (FinDist.pure true)

def law : FinDist BNAssignment :=
  fairMix
    (fairMix (FinDist.pure (world false false))
      (FinDist.pure (world false true)))
    (fairMix (FinDist.pure (world true false))
      (FinDist.pure (world true true)))

def kernels : LocalKernels diagram.Value parents
  | .first, _ => fairBool
  | .second, _ => fairBool
  | .collider, configuration =>
      FinDist.pure
        (configuration ⟨.first, by simp [parents]⟩ ==
          configuration ⟨.second, by simp [parents]⟩)
  | .descendant, configuration =>
      FinDist.pure (configuration ⟨.collider, by simp [parents]⟩)

private theorem assignment_eq_worldValues (assignment : BNAssignment) :
    assignment = rawWorld (assignment .first) (assignment .second)
      (assignment .collider) (assignment .descendant) := by
  funext node
  cases node <;> rfl

private theorem allNodes : (Finset.univ : Finset ColliderNode) =
    {.first, .second, .collider, .descendant} := by
  ext node
  cases node <;> simp

theorem factorizes : Factorizes diagram.Value law parents kernels := by
  intro assignment
  rw [assignment_eq_worldValues assignment]
  generalize assignment .first = firstValue
  generalize assignment .second = secondValue
  generalize assignment .collider = colliderValue
  generalize assignment .descendant = descendantValue
  cases firstValue <;> cases secondValue <;>
    cases colliderValue <;> cases descendantValue <;>
      simp_rw [law, fairMix, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
  all_goals
    rw [factorProduct, allNodes]
    simp [rawWorld_eq_world_iff, rawWorld, localFactor, parentConfiguration,
      kernels, fairBool, fairMix, FinDist.prob_pure_eq_ite]

def firstCoordinates : Finset ColliderNode := {.first}

def secondCoordinates : Finset ColliderNode := {.second}

def noEvidence : Finset ColliderNode := ∅

def colliderEvidence : Finset ColliderNode := {.collider}

def descendantEvidence : Finset ColliderNode := {.descendant}

private theorem collider_not_ancestral_without_evidence :
    ¬ InAncestralClosure parents firstCoordinates secondCoordinates noEvidence
      .collider := by
  rintro ⟨root, hroot, path⟩
  have hrootCases : root = .first ∨ root = .second := by
    simpa [queryRoots, firstCoordinates, secondCoordinates, noEvidence] using hroot
  rcases Relation.ReflTransGen.cases_head path with heq | ⟨next, hedge, tail⟩
  · subst root
    simp at hrootCases
  · have hnext : next = .descendant := by
      cases next <;> simp [DirectedEdge, parents] at hedge ⊢
    subst next
    rcases Relation.ReflTransGen.cases_head tail with heq | ⟨next, hedge, _⟩
    · subst root
      simp at hrootCases
    · cases next <;> simp [DirectedEdge, parents] at hedge

private theorem descendant_not_ancestral_without_evidence :
    ¬ InAncestralClosure parents firstCoordinates secondCoordinates noEvidence
      .descendant := by
  rintro ⟨root, hroot, path⟩
  have hrootCases : root = .first ∨ root = .second := by
    simpa [queryRoots, firstCoordinates, secondCoordinates, noEvidence] using hroot
  rcases Relation.ReflTransGen.cases_head path with heq | ⟨next, hedge, _⟩
  · subst root
    simp at hrootCases
  · cases next <;> simp [DirectedEdge, parents] at hedge

theorem separated_without_evidence :
    Separates parents firstCoordinates secondCoordinates noEvidence := by
  intro source hsource target htarget
  have hsourceEq : source = .first := by simpa [firstCoordinates] using hsource
  have htargetEq : target = .second := by simpa [secondCoordinates] using htarget
  subst source
  subst target
  rintro ⟨_, _, connection⟩
  have isolated : ∀ next,
      ¬ MoralAdjacent parents firstCoordinates secondCoordinates noEvidence
        .first next := by
    intro next adjacent
    rcases adjacent with
      ⟨hne, _, _, _, hnextAncestral,
        hforward | hbackward | hcoparents⟩
    · cases next with
      | first => exact hne rfl
      | second => simp [DirectedEdge, parents] at hforward
      | collider => exact collider_not_ancestral_without_evidence hnextAncestral
      | descendant => exact descendant_not_ancestral_without_evidence hnextAncestral
    · cases next <;> simp [DirectedEdge, parents] at hbackward
    · obtain ⟨child, hchildAncestral, hfirstParent, _⟩ := hcoparents
      cases child with
      | first => simp [DirectedEdge, parents] at hfirstParent
      | second => simp [DirectedEdge, parents] at hfirstParent
      | collider => exact collider_not_ancestral_without_evidence hchildAncestral
      | descendant => simp [DirectedEdge, parents] at hfirstParent
  rcases Relation.ReflTransGen.cases_head connection with heq | ⟨next, firstStep, _⟩
  · cases heq
  · exact isolated next firstStep

theorem roots_conditionallyIndependent_without_evidence :
    CoordinatesConditionallyIndependent law firstCoordinates secondCoordinates noEvidence :=
  coordinatesConditionallyIndependent_of_factorizes_of_separates law parents
    topological kernels factorizes firstCoordinates secondCoordinates noEvidence
    (by simp [firstCoordinates, secondCoordinates])
    (by simp [firstCoordinates, noEvidence])
    (by simp [secondCoordinates, noEvidence]) separated_without_evidence

private theorem collider_ancestral_with_collider_evidence :
    InAncestralClosure parents firstCoordinates secondCoordinates colliderEvidence
      .collider :=
  ⟨.collider, by simp [queryRoots, colliderEvidence], Relation.ReflTransGen.refl⟩

private theorem collider_ancestral_with_descendant_evidence :
    InAncestralClosure parents firstCoordinates secondCoordinates descendantEvidence
      .collider := by
  refine ⟨.descendant, by simp [queryRoots, descendantEvidence], ?_⟩
  exact Relation.ReflTransGen.single (by simp [DirectedEdge, parents])

private theorem not_separated_of_collider_ancestral
    (evidence : Finset ColliderNode)
    (hfirstOpen : ColliderNode.first ∉ evidence)
    (hsecondOpen : ColliderNode.second ∉ evidence)
    (hcollider :
      InAncestralClosure parents firstCoordinates secondCoordinates evidence
        .collider) :
    ¬ Separates parents firstCoordinates secondCoordinates evidence := by
  have hfirstParent : DirectedEdge parents .first .collider := by
    simp [DirectedEdge, parents]
  have hsecondParent : DirectedEdge parents .second .collider := by
    simp [DirectedEdge, parents]
  have moralEdge :
      MoralAdjacent parents firstCoordinates secondCoordinates evidence
        .first .second :=
    factorScope_pairwise_moralAdjacent hcollider
      (Finset.mem_insert_of_mem hfirstParent)
      (Finset.mem_insert_of_mem hsecondParent) (by decide)
      hfirstOpen hsecondOpen
  intro separated
  exact separated .first (by simp [firstCoordinates])
    .second (by simp [secondCoordinates])
      ⟨hfirstOpen, hsecondOpen, Relation.ReflTransGen.single moralEdge⟩

theorem not_separated_by_collider :
    ¬ Separates parents firstCoordinates secondCoordinates colliderEvidence :=
  not_separated_of_collider_ancestral colliderEvidence
    (by simp [colliderEvidence]) (by simp [colliderEvidence])
      collider_ancestral_with_collider_evidence

theorem not_separated_by_descendant :
    ¬ Separates parents firstCoordinates secondCoordinates descendantEvidence :=
  not_separated_of_collider_ancestral descendantEvidence
    (by simp [descendantEvidence]) (by simp [descendantEvidence])
      collider_ancestral_with_descendant_evidence

end GameTheory.Experimental.PostArchitecture.FiniteBNGlobalMarkovColliderTest
