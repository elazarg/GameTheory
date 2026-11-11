module

/-
EXP-176: compare direct guarded choice predicates with a law-valued record.
Both presentations retain the same numerical shape and use the same genuinely
stochastic belief example and nonbijective alternative coverage. This file
preserves the measured alternatives rather than exporting a second context API.
-/

public import GameTheory.Protocol.Context
public import GameTheory.Tests.Potential
public import GameTheory.Math.Probability.Uniform

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.ContextJudgment

open GameTheory.Math.Probability

universe ua us ut uo

/-- Optimality separates the domain of evaluation from the comparison.
The chosen value remains admissible even when the allowed set is empty. -/
def IsOptimalOn {α : Type ua} (admissible : α → Prop) (prefers : α → α → Prop)
    (allowed : Set α) (chosen : α) : Prop :=
  admissible chosen ∧ (∀ alternative ∈ allowed, admissible alternative) ∧
    ∀ alternative ∈ allowed, prefers chosen alternative

/-- Every target alternative is covered by a source alternative whose domain
membership and chosen comparison imply the target obligations. -/
theorem IsOptimalOn.of_coverage
    {Source : Type us} {Target : Type ut}
    {sourceAdmissible : Source → Prop} {targetAdmissible : Target → Prop}
    {sourcePrefers : Source → Source → Prop} {targetPrefers : Target → Target → Prop}
    {sourceAllowed : Set Source} {targetAllowed : Set Target}
    {chosen : Source} {compiled : Target}
    (optimal : IsOptimalOn sourceAdmissible sourcePrefers sourceAllowed chosen)
    (base : sourceAdmissible chosen → targetAdmissible compiled)
    (coverage : ∀ alternative ∈ targetAllowed, ∃ original ∈ sourceAllowed,
      (sourceAdmissible original → targetAdmissible alternative) ∧
        (sourcePrefers chosen original → targetPrefers compiled alternative)) :
    IsOptimalOn targetAdmissible targetPrefers targetAllowed compiled := by
  refine ⟨base optimal.1, ?_, ?_⟩
  · intro alternative allowed
    obtain ⟨original, used, domain, _⟩ := coverage alternative allowed
    exact domain (optimal.2.1 original used)
  · intro alternative allowed
    obtain ⟨original, used, _, comparison⟩ := coverage alternative allowed
    exact comparison (optimal.2.2 original used)

/-- Numerical context optimality has exactly the direct predicate's guarded
shape, including chosen admissibility for an empty set of alternatives. -/
theorem context_optimal_iff_predicate
    {Choice : Type ua} {Outcome : Type uo}
    (ctx : Protocol.Context Choice Outcome) (allowed : Set Choice) (chosen : Choice) :
    ctx.IsLocallyOptimal allowed chosen ↔
      IsOptimalOn ctx.HasValueAt
        (fun preferred alternative => ctx.extendedValue alternative ≤ ctx.extendedValue preferred)
        allowed chosen := Iff.rfl

/-- An alternative presentation stores an outcome map, a law-domain predicate,
and a comparison on laws together. -/
structure ComparisonContext (Choice : Type ua) (Outcome : Type uo) where
  outcome : Choice → PMF Outcome
  admissible : PMF Outcome → Prop
  prefers : PMF Outcome → PMF Outcome → Prop

namespace ComparisonContext

/-- Pull guarded law comparison back along the context's outcome map. -/
def IsOptimal {Choice : Type ua} {Outcome : Type uo}
    (ctx : ComparisonContext Choice Outcome) (allowed : Set Choice) (chosen : Choice) : Prop :=
  IsOptimalOn (fun choice => ctx.admissible (ctx.outcome choice))
    (fun preferred alternative => ctx.prefers (ctx.outcome preferred) (ctx.outcome alternative))
    allowed chosen

/-- Numerical contexts provide both a domain guard and an extended-value
comparison; finite values are not required. -/
def ofContext {Choice : Type ua} {Outcome : Type uo}
    (ctx : Protocol.Context Choice Outcome) : ComparisonContext Choice Outcome where
  outcome := ctx.outcome
  admissible law := HasExpectation law ctx.continuation
  prefers preferred alternative :=
    extendedExpect alternative ctx.continuation ≤ extendedExpect preferred ctx.continuation

theorem ofContext_isOptimal_iff {Choice : Type ua} {Outcome : Type uo}
    (ctx : Protocol.Context Choice Outcome) (allowed : Set Choice) (chosen : Choice) :
    (ofContext ctx).IsOptimal allowed chosen ↔ ctx.IsLocallyOptimal allowed chosen := Iff.rfl

/-- Equality of chosen laws and coverage of alternatives transports a common
law-domain predicate and relation. -/
theorem IsOptimal.of_outcome_coverage
    {Source : Type us} {Target : Type ut} {Outcome : Type uo}
    {source : ComparisonContext Source Outcome} {target : ComparisonContext Target Outcome}
    {sourceAllowed : Set Source} {targetAllowed : Set Target}
    {chosen : Source} {compiled : Target}
    (optimal : source.IsOptimal sourceAllowed chosen)
    (domain : target.admissible = source.admissible)
    (comparison : target.prefers = source.prefers)
    (honest : target.outcome compiled = source.outcome chosen)
    (coverage : ∀ alternative ∈ targetAllowed, ∃ original ∈ sourceAllowed,
      target.outcome alternative = source.outcome original) :
    target.IsOptimal targetAllowed compiled := by
  refine IsOptimalOn.of_coverage optimal ?_ ?_
  · intro hbase
    rw [domain, honest]
    exact hbase
  · intro alternative allowed
    obtain ⟨original, used, same⟩ := coverage alternative allowed
    refine ⟨original, used, ?_, ?_⟩
    · intro hadmissible
      rw [domain, same]
      exact hadmissible
    · intro hcomparison
      rw [comparison, honest, same]
      exact hcomparison

end ComparisonContext

/-- The existing numerical law-coverage client can supply the predicate's
obligations directly without constructing a comparison context. -/
theorem context_transport_via_predicate
    {Source : Type us} {Target : Type ut} {Outcome : Type uo}
    {source : Protocol.Context Source Outcome} {target : Protocol.Context Target Outcome}
    {sourceAllowed : Set Source} {targetAllowed : Set Target}
    {chosen : Source} {compiled : Target}
    (optimal : source.IsLocallyOptimal sourceAllowed chosen)
    (payoff : target.continuation = source.continuation)
    (honest : target.outcome compiled = source.outcome chosen)
    (coverage : ∀ alternative ∈ targetAllowed, ∃ original ∈ sourceAllowed,
      target.outcome alternative = source.outcome original) :
    target.IsLocallyOptimal targetAllowed compiled := by
  apply (context_optimal_iff_predicate target targetAllowed compiled).2
  refine IsOptimalOn.of_coverage
    ((context_optimal_iff_predicate source sourceAllowed chosen).1 optimal) ?_ ?_
  · intro hbase
    change HasExpectation (target.outcome compiled) target.continuation
    rw [payoff, honest]
    exact hbase
  · intro alternative allowed
    obtain ⟨original, used, same⟩ := coverage alternative allowed
    refine ⟨original, used, ?_, ?_⟩
    · intro hadmissible
      change HasExpectation (target.outcome alternative) target.continuation
      rw [payoff, same]
      exact hadmissible
    · intro hcomparison
      change extendedExpect (target.outcome alternative) target.continuation ≤
        extendedExpect (target.outcome compiled) target.continuation
      rw [payoff, honest, same]
      exact hcomparison

/-- The record-based alternative constructs the two numerical comparison
contexts and proves equality of their domain predicates and relations. -/
theorem context_transport_via_record
    {Source : Type us} {Target : Type ut} {Outcome : Type uo}
    {source : Protocol.Context Source Outcome} {target : Protocol.Context Target Outcome}
    {sourceAllowed : Set Source} {targetAllowed : Set Target}
    {chosen : Source} {compiled : Target}
    (optimal : source.IsLocallyOptimal sourceAllowed chosen)
    (payoff : target.continuation = source.continuation)
    (honest : target.outcome compiled = source.outcome chosen)
    (coverage : ∀ alternative ∈ targetAllowed, ∃ original ∈ sourceAllowed,
      target.outcome alternative = source.outcome original) :
    target.IsLocallyOptimal targetAllowed compiled := by
  change (ComparisonContext.ofContext target).IsOptimal targetAllowed compiled
  refine ComparisonContext.IsOptimal.of_outcome_coverage
    (source := ComparisonContext.ofContext source) optimal ?_ ?_ honest coverage
  · dsimp only [ComparisonContext.ofContext]
    rw [payoff]
  · dsimp only [ComparisonContext.ofContext]
    rw [payoff]

/-! ## Belief-mediated possibility preferences -/

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

/-- The chosen law is genuinely stochastic, while the alternative is sure
`true`. Possibility regards the two laws as indifferent. -/
theorem belief_direct_optimal :
    IsOptimalOn (fun _ : Bool => True)
      (fun preferred alternative => GameTheory.Tests.Potential.supportPreference ()
        (beliefOutcome preferred) (beliefOutcome alternative)) Set.univ true := by
  refine ⟨trivial, fun _ _ => trivial, ?_⟩
  intro alternative _
  exact Or.inl beliefOutcome_true_supported

def beliefComparison : ComparisonContext Bool Bool where
  outcome := beliefOutcome
  admissible _ := True
  prefers := GameTheory.Tests.Potential.supportPreference ()

theorem belief_record_optimal : beliefComparison.IsOptimal Set.univ true :=
  belief_direct_optimal

/-- The numerical context uses precisely the same belief, kernel, and two
outcome laws. Its payoff distinguishes probability from mere possibility. -/
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

/-- Two administrative target choices realize the same stochastic source
choice. This map is deliberately not a choice equivalence. -/
def sourceBeliefChoice (choice : Fin 3) : Bool :=
  if choice = 0 then false else true

def targetBeliefOutcome (choice : Fin 3) : PMF Bool :=
  beliefOutcome (sourceBeliefChoice choice)

theorem targetBeliefOutcome_chosen : targetBeliefOutcome 1 = beliefOutcome true := by
  simp [targetBeliefOutcome, sourceBeliefChoice]

theorem belief_law_coverage : ∀ alternative ∈ (Set.univ : Set (Fin 3)),
    ∃ original ∈ (Set.univ : Set Bool), targetBeliefOutcome alternative = beliefOutcome original :=
  fun alternative _ => ⟨sourceBeliefChoice alternative, trivial, rfl⟩

/-- Direct predicates transport through coverage, without a law-valued
context record or a choice bijection. -/
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

def targetBeliefComparison : ComparisonContext (Fin 3) Bool where
  outcome := targetBeliefOutcome
  admissible _ := True
  prefers := GameTheory.Tests.Potential.supportPreference ()

/-- The record alternative supplies the identical chosen-law equality and
coverage theorem, together with common domain and relation fields. -/
theorem target_belief_record_optimal : targetBeliefComparison.IsOptimal Set.univ 1 :=
  ComparisonContext.IsOptimal.of_outcome_coverage
    (source := beliefComparison) belief_record_optimal rfl rfl
    targetBeliefOutcome_chosen belief_law_coverage

end GameTheory.Experimental.ContextJudgment
