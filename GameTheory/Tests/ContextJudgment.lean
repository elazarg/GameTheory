module

/-
# Belief-mediated guarded choice

A possibility preference accepts a fair law that expected utility rejects in
favor of certainty. The same outcome laws transfer optimality to three choices
using coverage, including two choices realizing the same source law. No order
or expectation assumption is imposed on the possibility comparison.
-/

public import GameTheory.Protocol.ContextTransport
public import GameTheory.Tests.Potential
public import GameTheory.Math.Probability.Uniform

@[expose] public section

noncomputable section

namespace GameTheory.Tests.ContextJudgment

open GameTheory.Math GameTheory.Math.Probability

/-- The numerical specialization retains the complete original guarded shape. -/
theorem context_optimality_shape {Choice Outcome : Type*}
    (ctx : Protocol.Context Choice Outcome) (allowed : Set Choice) (chosen : Choice) :
    ctx.IsLocallyOptimal allowed chosen ↔
      ctx.HasValueAt chosen ∧
        (∀ alternative ∈ allowed, ctx.HasValueAt alternative) ∧
          ∀ alternative ∈ allowed, ctx.extendedValue alternative ≤ ctx.extendedValue chosen :=
  Iff.rfl

def beliefPrior : PMF Bool := uniformLaw Bool

def beliefBranch (hidden choice : Bool) : PMF Bool :=
  PMF.pure (if choice then hidden else true)

def beliefOutcome (choice : Bool) : PMF Bool :=
  beliefPrior.bind fun hidden => beliefBranch hidden choice

theorem beliefOutcome_true : beliefOutcome true = beliefPrior := by
  simp [beliefOutcome, beliefBranch]

theorem beliefOutcome_false : beliefOutcome false = PMF.pure true := by
  simp [beliefOutcome, beliefBranch]

theorem beliefOutcome_true_supported : true ∈ (beliefOutcome true).support := by
  rw [beliefOutcome_true]
  exact mem_support_uniformLaw true

                                                                         
                                                           
theorem belief_direct_optimal :
    IsOptimalOn (fun _ : Bool => True)
      (fun preferred alternative => GameTheory.Tests.Potential.supportPreference ()
        (beliefOutcome preferred) (beliefOutcome alternative)) Set.univ true := by
  refine ⟨trivial, fun _ _ => trivial, ?_⟩
  intro alternative _
  exact Or.inl beliefOutcome_true_supported

def numericalBelief : Protocol.Context Bool Bool :=
  Protocol.Context.ofBelief beliefPrior beliefBranch (fun bit => if bit then 1 else 0)

theorem numericalBelief_not_optimal :
    ¬ numericalBelief.IsLocallyOptimal Set.univ true := by
  intro hoptimal
  have hintegrable (choice : Bool) : numericalBelief.IntegrableAt choice :=
    payoffIntegrable_of_finite _ _
  have hvalues :=
    (Protocol.Context.isLocallyOptimal_iff_of_integrable (hintegrable true)
      (fun alternative _ => hintegrable alternative)).1 hoptimal false (Set.mem_univ false)
  change expect (beliefOutcome false) (fun bit => if bit then 1 else 0) ≤
    expect (beliefOutcome true) (fun bit => if bit then 1 else 0) at hvalues
  rw [beliefOutcome_false, beliefOutcome_true] at hvalues
  norm_num [beliefPrior, expect_pure, expect_uniformOfFintype, Fintype.sum_bool] at hvalues

                                                                        
                                                             
def sourceBeliefChoice (choice : Fin 3) : Bool :=
  if choice = 0 then false else true

def targetBeliefOutcome (choice : Fin 3) : PMF Bool :=
  beliefOutcome (sourceBeliefChoice choice)

theorem targetBeliefOutcome_chosen : targetBeliefOutcome 1 = beliefOutcome true := by
  simp [targetBeliefOutcome, sourceBeliefChoice]

theorem belief_law_coverage : ∀ alternative ∈ (Set.univ : Set (Fin 3)),
    ∃ original ∈ (Set.univ : Set Bool), targetBeliefOutcome alternative = beliefOutcome original :=
  fun alternative _ => ⟨sourceBeliefChoice alternative, trivial, rfl⟩

                                                                      
                                        
theorem target_belief_direct_optimal :
    IsOptimalOn (fun _ : Fin 3 => True)
      (fun preferred alternative => GameTheory.Tests.Potential.supportPreference ()
        (targetBeliefOutcome preferred) (targetBeliefOutcome alternative)) Set.univ 1 := by
  refine IsOptimalOn.of_coverage (chosen := true) (compiled := (1 : Fin 3))
    belief_direct_optimal (fun _ => trivial) ?_
  intro alternative allowed
  obtain ⟨original, used, same⟩ := belief_law_coverage alternative allowed
  refine ⟨original, used, fun _ => trivial, ?_⟩
  intro hcomparison
  rw [targetBeliefOutcome_chosen, same]
  exact hcomparison


end GameTheory.Tests.ContextJudgment
