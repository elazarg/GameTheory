/-
# The Shapley value

The Shapley value lives directly on `CoalitionalGame`. Its weighted marginal
contributions use explicit finite enumeration, while the game itself continues
to store only its characteristic function and the empty-coalition law.

Primary reference: L. S. Shapley, “A Value for n-Person Games,” in
*Contributions to the Theory of Games II*, Princeton University Press, 1953.
-/

import GameTheory.Core.Coalitional
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace GameTheory

open scoped BigOperators

universe ua

namespace CoalitionalGame

variable {Agent : Type ua} [DecidableEq Agent]

section FiniteAgents

variable [Fintype Agent]

/-- The Shapley value: each marginal contribution is weighted by the fraction
of arrival orders in which exactly that coalition precedes the agent. -/
noncomputable def shapleyValue
    (G : CoalitionalGame Agent) : Allocation Agent :=
  fun agent =>
    ∑ coalition ∈
        (Finset.univ : Finset (Finset Agent)).filter
          (fun coalition => agent ∉ coalition),
      ((coalition.card.factorial *
          (Fintype.card Agent - coalition.card - 1).factorial : ℕ) : ℝ) /
        ((Fintype.card Agent).factorial : ℝ) *
          G.marginalContribution agent coalition

/-- A null agent receives zero. -/
theorem shapleyValue_null
    (G : CoalitionalGame Agent) {agent : Agent}
    (hnull : G.IsNull agent) :
    G.shapleyValue agent = 0 := by
  simp only [shapleyValue]
  apply Finset.sum_eq_zero
  intro coalition hcoalition
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcoalition
  rw [hnull coalition hcoalition, mul_zero]

end FiniteAgents

/-- Two agents are symmetric when exchanging which one joins any coalition
containing neither leaves its worth unchanged. -/
def AreSymmetric
    (G : CoalitionalGame Agent) (first second : Agent) : Prop :=
  ∀ coalition : Finset Agent,
    first ∉ coalition → second ∉ coalition →
      G.value (insert first coalition) =
        G.value (insert second coalition)

theorem marginalContribution_eq_of_symmetric
    (G : CoalitionalGame Agent) {first second : Agent}
    (hsymmetric : G.AreSymmetric first second)
    {coalition : Finset Agent}
    (hfirst : first ∉ coalition)
    (hsecond : second ∉ coalition) :
    G.marginalContribution first coalition =
      G.marginalContribution second coalition := by
  simp only [marginalContribution]
  rw [hsymmetric coalition hfirst hsecond]

theorem smul_isNull
    {scalar : ℝ} {G : CoalitionalGame Agent} {agent : Agent}
    (hnull : G.IsNull agent) :
    (smul scalar G).IsNull agent := by
  intro coalition hnotmem
  have hmc := hnull coalition hnotmem
  simp only [marginalContribution, smul] at hmc ⊢
  have hvalue :
      G.value (insert agent coalition) = G.value coalition := by
    linarith
  rw [hvalue]
  ring

theorem smul_areSymmetric
    {scalar : ℝ} {G : CoalitionalGame Agent} {first second : Agent}
    (hsymmetric : G.AreSymmetric first second) :
    (smul scalar G).AreSymmetric first second := by
  intro coalition hfirst hsecond
  simp only [smul]
  rw [hsymmetric coalition hfirst hsecond]

section FiniteAgents

variable [Fintype Agent]

/-- The Shapley value is additive across games. -/
theorem shapleyValue_add
    (G H : CoalitionalGame Agent) :
    (add G H).shapleyValue =
      fun agent => G.shapleyValue agent + H.shapleyValue agent := by
  funext agent
  simp only [shapleyValue, add, marginalContribution]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coalition _
  ring

/-- The Shapley value commutes with scalar multiplication. -/
theorem shapleyValue_smul
    (scalar : ℝ) (G : CoalitionalGame Agent) :
    (smul scalar G).shapleyValue =
      fun agent => scalar * G.shapleyValue agent := by
  funext agent
  simp only [shapleyValue, smul, marginalContribution]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coalition _
  ring

/-- Symmetric agents receive the same Shapley value. -/
theorem shapleyValue_symmetric
    (G : CoalitionalGame Agent) {first second : Agent}
    (hsymmetric : G.AreSymmetric first second) :
    G.shapleyValue first = G.shapleyValue second := by
  classical
  rcases eq_or_ne first second with rfl | hne
  · rfl
  simp only [shapleyValue]
  set firstCoalitions :=
    (Finset.univ : Finset (Finset Agent)).filter
      (fun coalition => first ∉ coalition)
  set secondCoalitions :=
    (Finset.univ : Finset (Finset Agent)).filter
      (fun coalition => second ∉ coalition)
  let swapMember
      (added removed : Agent) (coalition : Finset Agent) :
      Finset Agent :=
    if removed ∈ coalition then
      insert added (coalition.erase removed)
    else
      coalition
  have swapMember_not_mem
      (added removed : Agent) (hdistinct : added ≠ removed)
      (coalition : Finset Agent) (hadded : added ∉ coalition) :
      removed ∉ swapMember added removed coalition := by
    simp only [swapMember]
    split_ifs with hremoved
    · intro hmem
      rcases Finset.mem_insert.mp hmem with hEq | herased
      · exact hdistinct hEq.symm
      · exact (Finset.notMem_erase removed coalition) herased
    · exact hremoved
  have swapMember_inverse
      (added removed : Agent) (hdistinct : added ≠ removed)
      (coalition : Finset Agent) (hadded : added ∉ coalition) :
      swapMember removed added
          (swapMember added removed coalition) =
        coalition := by
    simp only [swapMember]
    by_cases hremoved : removed ∈ coalition
    · simp only [hremoved, ↓reduceIte, Finset.mem_insert_self]
      have hnotErased : added ∉ coalition.erase removed := by
        intro hmem
        exact hadded (Finset.mem_of_mem_erase hmem)
      rw [Finset.erase_insert hnotErased,
        Finset.insert_erase hremoved]
    · simp only [hremoved, ↓reduceIte, hadded]
  have swapMember_card
      (added removed : Agent) (coalition : Finset Agent)
      (hadded : added ∉ coalition) (hremoved : removed ∈ coalition) :
      (swapMember added removed coalition).card =
        coalition.card := by
    simp only [swapMember, hremoved, ↓reduceIte]
    have hnotErased : added ∉ coalition.erase removed := by
      simp only [Finset.mem_erase]
      exact fun ⟨_, hmem⟩ => hadded hmem
    rw [Finset.card_insert_of_notMem hnotErased,
      Finset.card_erase_of_mem hremoved]
    have hpositive : 0 < coalition.card :=
      Finset.card_pos.mpr ⟨removed, hremoved⟩
    omega
  apply Finset.sum_nbij'
    (swapMember first second) (swapMember second first)
  · intro coalition hcoalition
    simp only [firstCoalitions, Finset.mem_filter,
      Finset.mem_univ, true_and] at hcoalition
    simp only [secondCoalitions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact
      swapMember_not_mem first second hne coalition hcoalition
  · intro coalition hcoalition
    simp only [secondCoalitions, Finset.mem_filter,
      Finset.mem_univ, true_and] at hcoalition
    simp only [firstCoalitions, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact
      swapMember_not_mem second first hne.symm coalition hcoalition
  · intro coalition hcoalition
    simp only [firstCoalitions, Finset.mem_filter,
      Finset.mem_univ, true_and] at hcoalition
    exact
      swapMember_inverse first second hne coalition hcoalition
  · intro coalition hcoalition
    simp only [secondCoalitions, Finset.mem_filter,
      Finset.mem_univ, true_and] at hcoalition
    exact
      swapMember_inverse second first hne.symm coalition hcoalition
  · intro coalition hcoalition
    simp only [firstCoalitions, Finset.mem_filter,
      Finset.mem_univ, true_and] at hcoalition
    simp only [swapMember]
    split_ifs with hsecond
    · have hcard :=
        swapMember_card first second coalition hcoalition hsecond
      simp only [swapMember, hsecond, ↓reduceIte] at hcard
      set rest := coalition.erase second with hrest
      have hfirstRest : first ∉ rest := by
        simp only [Finset.mem_erase, hrest]
        exact fun ⟨_, hmem⟩ => hcoalition hmem
      have hsecondRest : second ∉ rest :=
        Finset.notMem_erase second coalition
      have hsymmetricValue :
          G.value (insert first rest) =
            G.value (insert second rest) :=
        hsymmetric rest hfirstRest hsecondRest
      have hcoalitionValue :
          insert second rest = coalition :=
        Finset.insert_erase hsecond
      have hjoinedValue :
          insert second (insert first rest) =
            insert first coalition := by
        rw [Finset.insert_comm, hcoalitionValue]
      simp only [marginalContribution, hcard, hjoinedValue,
        ← hcoalitionValue, hsymmetricValue]
    · congr 1
      exact
        G.marginalContribution_eq_of_symmetric
          hsymmetric hcoalition hsecond

/-- The Shapley allocation is efficient: all shares sum to the worth of the
grand coalition. -/
theorem shapleyValue_efficient
    (G : CoalitionalGame Agent) :
    ∑ agent, G.shapleyValue agent =
      G.value Finset.univ := by
  classical
  rcases isEmpty_or_nonempty Agent with hempty | hnonempty
  · haveI := hempty
    simp only [Finset.univ_eq_empty, Finset.sum_empty, G.value_empty]
  set agentCount := Fintype.card Agent with hcount
  have hcountPositive : 0 < agentCount := by
    rw [hcount]
    exact Fintype.card_pos
  let weight : ℕ → ℝ :=
    fun size =>
      ((size.factorial *
          (agentCount - size - 1).factorial : ℕ) : ℝ) /
        (agentCount.factorial : ℝ)
  have hindicator :
      ∀ agent : Agent,
        G.shapleyValue agent =
          ∑ coalition : Finset Agent,
            if agent ∉ coalition then
              weight coalition.card *
                (G.value (insert agent coalition) -
                  G.value coalition)
            else
              0 := by
    intro agent
    rw [shapleyValue]
    simp only [marginalContribution, weight]
    rw [← Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun agent _ => hindicator agent)]
  rw [Finset.sum_comm]
  have hinner :
      ∀ coalition : Finset Agent,
        (∑ agent,
          if agent ∉ coalition then
            weight coalition.card *
              (G.value (insert agent coalition) -
                G.value coalition)
          else
            0) =
          (∑ agent ∈ coalitionᶜ,
            weight coalition.card *
              G.value (insert agent coalition)) -
          weight coalition.card * G.value coalition *
            (coalitionᶜ.card : ℝ) := by
    intro coalition
    have hfilter :
        Finset.univ.filter
            (fun agent : Agent => agent ∉ coalition) =
          coalitionᶜ := by
      ext agent
      simp [Finset.mem_compl]
    rw [← Finset.sum_filter, hfilter]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun coalition _ => hinner coalition)]
  rw [Finset.sum_sub_distrib]
  have hpositive :
      (∑ coalition : Finset Agent,
        ∑ agent ∈ coalitionᶜ,
          weight coalition.card *
            G.value (insert agent coalition)) =
        ∑ joined : Finset Agent,
          (joined.card : ℝ) *
            weight (joined.card - 1) *
              G.value joined := by
    let fiber : Finset Agent → Type ua := fun _ => Agent
    let leftTerm : Sigma fiber → ℝ :=
      fun pair =>
        weight pair.1.card *
          G.value (insert pair.2 pair.1)
    let rightTerm : Sigma fiber → ℝ :=
      fun pair =>
        weight (pair.1.card - 1) *
          G.value pair.1
    have hleft :
        (∑ coalition : Finset Agent,
          ∑ agent ∈ coalitionᶜ,
            weight coalition.card *
              G.value (insert agent coalition)) =
          ∑ pair ∈
            (Finset.univ : Finset (Finset Agent)).sigma
              (fun coalition : Finset Agent => coalitionᶜ),
            leftTerm pair :=
      (Finset.sum_sigma (σ := fiber) _ _ leftTerm).symm
    have hrightNested :
        (∑ joined : Finset Agent,
          (joined.card : ℝ) *
            weight (joined.card - 1) *
              G.value joined) =
          ∑ joined : Finset Agent,
            ∑ _ ∈ joined,
              weight (joined.card - 1) *
                G.value joined := by
      refine Finset.sum_congr rfl (fun joined _ => ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    have hright :
        (∑ joined : Finset Agent,
          ∑ _ ∈ joined,
            weight (joined.card - 1) *
              G.value joined) =
          ∑ pair ∈
            (Finset.univ : Finset (Finset Agent)).sigma
              (fun joined : Finset Agent => joined),
            rightTerm pair :=
      (Finset.sum_sigma (σ := fiber) _ _ rightTerm).symm
    rw [hleft, hrightNested, hright]
    refine Finset.sum_nbij'
      (i := fun pair : Sigma fiber =>
        ⟨insert pair.2 pair.1, pair.2⟩)
      (j := fun pair : Sigma fiber =>
        ⟨pair.1.erase pair.2, pair.2⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨coalition, agent⟩ hmem
      simp only [Finset.mem_sigma, Finset.mem_univ,
        Finset.mem_compl, true_and] at hmem
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and]
      exact Finset.mem_insert_self agent coalition
    · rintro ⟨joined, agent⟩ hmem
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hmem
      simp only [Finset.mem_sigma, Finset.mem_univ,
        Finset.mem_compl, true_and]
      exact Finset.notMem_erase agent joined
    · rintro ⟨coalition, agent⟩ hmem
      simp only [Finset.mem_sigma, Finset.mem_univ,
        Finset.mem_compl, true_and] at hmem
      simp [Finset.erase_insert hmem]
    · rintro ⟨joined, agent⟩ hmem
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hmem
      simp [Finset.insert_erase hmem]
    · rintro ⟨coalition, agent⟩ hmem
      simp only [Finset.mem_sigma, Finset.mem_univ,
        Finset.mem_compl, true_and] at hmem
      simp only [leftTerm, rightTerm,
        Finset.card_insert_of_notMem hmem,
        Nat.add_sub_cancel]
  rw [hpositive]
  rw [show
    (∑ joined : Finset Agent,
      (joined.card : ℝ) * weight (joined.card - 1) *
        G.value joined) -
      (∑ joined : Finset Agent,
        weight joined.card * G.value joined *
          (joinedᶜ.card : ℝ)) =
      ∑ joined : Finset Agent,
        ((joined.card : ℝ) * weight (joined.card - 1) -
          weight joined.card * (joinedᶜ.card : ℝ)) *
            G.value joined from by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun joined _ => ?_)
      ring]
  rw [Finset.sum_eq_single Finset.univ]
  · have hunivCard :
        (Finset.univ : Finset Agent).card =
          agentCount :=
      Finset.card_univ.trans hcount.symm
    have hcomplementCard :
        (Finset.univᶜ : Finset Agent).card = 0 := by
      simp [Finset.compl_univ]
    rw [hunivCard, hcomplementCard]
    simp only [Nat.cast_zero, mul_zero, sub_zero, weight]
    obtain ⟨predecessorCount, hsuccessor⟩ :
        ∃ predecessorCount, agentCount = predecessorCount + 1 :=
      Nat.exists_eq_succ_of_ne_zero hcountPositive.ne'
    have hsub :
        agentCount - 1 = predecessorCount := by
      omega
    have hsubAgain :
        agentCount - (agentCount - 1) - 1 = 0 := by
      omega
    rw [hsubAgain, Nat.factorial_zero, mul_one]
    rw [hsub, hsuccessor, Nat.factorial_succ]
    field_simp
    push_cast
    ring
  · intro coalition _ hnotUniv
    rcases Finset.eq_empty_or_nonempty coalition with
      hempty | hnonempty
    · subst coalition
      simp [G.value_empty]
    · have hcardPositive : 0 < coalition.card :=
        Finset.card_pos.mpr hnonempty
      have hcardLess : coalition.card < agentCount := by
        rw [hcount]
        exact
          Finset.card_lt_card
            (Finset.ssubset_univ_iff.mpr hnotUniv)
      suffices hcoefficient :
          (coalition.card : ℝ) *
              weight (coalition.card - 1) =
            weight coalition.card *
              (coalitionᶜ.card : ℝ) by
        rw [hcoefficient, sub_self, zero_mul]
      have hsub :
          agentCount - (coalition.card - 1) - 1 =
            agentCount - coalition.card := by
        omega
      have hfactorial :
          ∀ number, 0 < number →
            number * (number - 1).factorial =
              number.factorial := by
        intro number hpositive
        obtain ⟨predecessor, rfl⟩ :
            ∃ predecessor, number = predecessor + 1 :=
          Nat.exists_eq_succ_of_ne_zero hpositive.ne'
        rw [Nat.add_sub_cancel, Nat.factorial_succ]
      have hleftFactorial :=
        hfactorial coalition.card hcardPositive
      have hrightFactorial :=
        hfactorial (agentCount - coalition.card) (by omega)
      have hkey :
          coalition.card *
              ((coalition.card - 1).factorial *
                (agentCount - coalition.card).factorial) =
            coalition.card.factorial *
              (agentCount - coalition.card - 1).factorial *
                (agentCount - coalition.card) := by
        rw [show
          coalition.card *
              ((coalition.card - 1).factorial *
                (agentCount - coalition.card).factorial) =
            (coalition.card *
              (coalition.card - 1).factorial) *
                (agentCount - coalition.card).factorial from by
              ring,
          hleftFactorial,
          show
            coalition.card.factorial *
                (agentCount - coalition.card - 1).factorial *
                  (agentCount - coalition.card) =
              coalition.card.factorial *
                ((agentCount - coalition.card) *
                  (agentCount - coalition.card - 1).factorial) from by
              ring,
          hrightFactorial]
      simp only [weight]
      rw [Finset.card_compl, ← hcount, hsub]
      rw [mul_div_assoc', div_mul_eq_mul_div]
      congr 1
      exact_mod_cast hkey
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- If every pair of distinct agents is symmetric, each receives an equal
share of the grand coalition's worth. -/
theorem shapleyValue_eq_of_all_symmetric
    (G : CoalitionalGame Agent)
    (hsymmetric :
      ∀ first second : Agent, first ≠ second →
        G.AreSymmetric first second)
    (agent : Agent) :
    G.shapleyValue agent =
      G.value Finset.univ / Fintype.card Agent := by
  classical
  have hconstant :
      ∀ other : Agent,
        G.shapleyValue other = G.shapleyValue agent :=
    fun other => by
      by_cases hEq : other = agent
      · subst other
        rfl
      · exact
          G.shapleyValue_symmetric
            (hsymmetric other agent hEq)
  have hsum := G.shapleyValue_efficient
  rw [Finset.sum_congr rfl (fun other _ => hconstant other),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcard :
      (Fintype.card Agent : ℝ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨agent⟩).ne'
  rw [eq_div_iff hcard, mul_comm]
  exact hsum

end FiniteAgents

/-! ## Unanimity basis -/

/-- The unanimity game on a nonempty coalition pays one exactly when that
coalition is contained in the coalition being evaluated. -/
def unanimityGame
    (coalition : Finset Agent) (hnonempty : coalition.Nonempty) :
    CoalitionalGame Agent where
  value present :=
    if coalition ⊆ present then 1 else 0
  value_empty := by
    rw [if_neg]
    intro hsubset
    obtain ⟨agent, hmem⟩ := hnonempty
    exact Finset.notMem_empty agent (hsubset hmem)

theorem unanimityGame_isNull_of_notMem
    (coalition : Finset Agent) (hnonempty : coalition.Nonempty)
    {agent : Agent} (hnotmem : agent ∉ coalition) :
    (unanimityGame coalition hnonempty).IsNull agent := by
  intro present _
  simp only [marginalContribution, unanimityGame]
  have hequivalent :
      coalition ⊆ insert agent present ↔
        coalition ⊆ present := by
    refine
      ⟨fun h member hmember => ?_,
        fun h => h.trans (Finset.subset_insert agent present)⟩
    rcases Finset.mem_insert.mp (h hmember) with hEq | hpresent
    · subst member
      exact (hnotmem hmember).elim
    · exact hpresent
  by_cases hsubset : coalition ⊆ present
  · simp [hsubset, hequivalent.mpr hsubset]
  · have hnotSubset :
        ¬ coalition ⊆ insert agent present :=
      fun h => hsubset (hequivalent.mp h)
    simp [hsubset, hnotSubset]

theorem unanimityGame_areSymmetric
    (coalition : Finset Agent) (hnonempty : coalition.Nonempty)
    {first second : Agent}
    (hdistinct : first ≠ second)
    (hfirst : first ∈ coalition) (hsecond : second ∈ coalition) :
    (unanimityGame coalition hnonempty).AreSymmetric first second := by
  intro present hfirstAbsent hsecondAbsent
  simp only [unanimityGame]
  have hnotFirst :
      ¬ coalition ⊆ insert first present := fun h =>
    hsecondAbsent <| by
      rcases Finset.mem_insert.mp (h hsecond) with hEq | hpresent
      · exact absurd hEq.symm hdistinct
      · exact hpresent
  have hnotSecond :
      ¬ coalition ⊆ insert second present := fun h =>
    hfirstAbsent <| by
      rcases Finset.mem_insert.mp (h hfirst) with hEq | hpresent
      · exact absurd hEq hdistinct
      · exact hpresent
  simp [hnotFirst, hnotSecond]

section FiniteAgents

variable [Fintype Agent]

theorem unanimityGame_value_univ
    (coalition : Finset Agent) (hnonempty : coalition.Nonempty) :
    (unanimityGame coalition hnonempty).value Finset.univ = 1 := by
  have hsubset : coalition ⊆ Finset.univ :=
    coalition.subset_univ
  simp [unanimityGame, hsubset]

end FiniteAgents

/-- Möbius coefficient of a coalition in the unanimity basis. -/
def unanimityCoeff
    (G : CoalitionalGame Agent) (coalition : Finset Agent) : ℝ :=
  ∑ smaller ∈ coalition.powerset,
    (-1 : ℝ) ^ (coalition.card - smaller.card) *
      G.value smaller

/-- Every coalitional game is the sum of its unanimity-basis coefficients on
the subsets of the coalition being evaluated. -/
theorem unanimity_decomposition
    (G : CoalitionalGame Agent) (coalition : Finset Agent) :
    G.value coalition =
      ∑ basis ∈ coalition.powerset,
        G.unanimityCoeff basis := by
  classical
  simp only [unanimityCoeff]
  have hswap :
      (∑ basis ∈ coalition.powerset,
      ∑ smaller ∈ basis.powerset,
        (-1 : ℝ) ^ (basis.card - smaller.card) *
          G.value smaller) =
      ∑ smaller ∈ coalition.powerset,
        ∑ basis ∈
          coalition.powerset.filter (smaller ⊆ ·),
          (-1 : ℝ) ^ (basis.card - smaller.card) *
            G.value smaller := by
    apply Finset.sum_comm'
    intro basis smaller
    simp only [Finset.mem_powerset, Finset.mem_filter]
    refine
      ⟨fun ⟨hbasis, hsmaller⟩ =>
          ⟨⟨hbasis, hsmaller⟩,
            hsmaller.trans hbasis⟩,
        fun ⟨⟨hbasis, hsmaller⟩, _⟩ =>
          ⟨hbasis, hsmaller⟩⟩
  rw [hswap]
  have hinner :
      ∀ smaller ∈ coalition.powerset,
        (∑ basis ∈
          coalition.powerset.filter (smaller ⊆ ·),
          (-1 : ℝ) ^ (basis.card - smaller.card) *
            G.value smaller) =
          G.value smaller *
            (if smaller = coalition then 1 else 0) := by
    intro smaller hsmaller
    rw [Finset.mem_powerset] at hsmaller
    rw [show
      (∑ basis ∈
        coalition.powerset.filter (smaller ⊆ ·),
        (-1 : ℝ) ^ (basis.card - smaller.card) *
          G.value smaller) =
        G.value smaller *
          ∑ basis ∈
            coalition.powerset.filter (smaller ⊆ ·),
            (-1 : ℝ) ^ (basis.card - smaller.card) by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun basis _ => ?_)
        ring]
    have hreindex :
        coalition.powerset.filter (smaller ⊆ ·) =
          (coalition \ smaller).powerset.image
            (fun rest => smaller ∪ rest) := by
      ext basis
      simp only [Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_image]
      refine
        ⟨fun ⟨hbasis, hsmallerBasis⟩ =>
          ⟨basis \ smaller,
            Finset.subset_sdiff.mpr
              ⟨Finset.sdiff_subset.trans hbasis,
                Finset.sdiff_disjoint⟩,
            Finset.union_sdiff_of_subset hsmallerBasis⟩,
          ?_⟩
      rintro ⟨rest, hrest, rfl⟩
      exact
        ⟨Finset.union_subset hsmaller
            ((Finset.subset_sdiff.mp hrest).1),
          Finset.subset_union_left⟩
    rw [hreindex]
    have hdisjoint :
        ∀ {rest : Finset Agent},
          rest ⊆ coalition \ smaller →
            Disjoint smaller rest :=
      fun hrest =>
        ((Finset.subset_sdiff.mp hrest).2).symm
    have hinjective :
        Set.InjOn (fun rest => smaller ∪ rest)
          ((coalition \ smaller).powerset :
            Set (Finset Agent)) := by
      intro first hfirst second hsecond hequal
      simp only [Finset.coe_powerset, Set.mem_preimage,
        Set.mem_powerset_iff, Finset.coe_subset] at hfirst hsecond
      have herased :=
        congrArg (· \ smaller) hequal
      simp only [Finset.union_sdiff_left,
        Finset.sdiff_eq_self_of_disjoint
          (hdisjoint hfirst).symm,
        Finset.sdiff_eq_self_of_disjoint
          (hdisjoint hsecond).symm] at herased
      exact herased
    rw [Finset.sum_image
      (fun first hfirst second hsecond =>
        hinjective hfirst hsecond)]
    have hcard :
        ∀ rest ∈ (coalition \ smaller).powerset,
          (smaller ∪ rest).card - smaller.card =
            rest.card := by
      intro rest hrest
      rw [Finset.card_union_of_disjoint
          (hdisjoint (Finset.mem_powerset.mp hrest)),
        Nat.add_sub_cancel_left]
    rw [Finset.sum_congr rfl
      (fun rest hrest => by rw [hcard rest hrest])]
    have hinteger :
        (∑ rest ∈ (coalition \ smaller).powerset,
          ((-1 : ℤ) ^ rest.card)) =
          if coalition \ smaller = ∅ then 1 else 0 :=
      Finset.sum_powerset_neg_one_pow_card
    have hreal :
        (∑ rest ∈ (coalition \ smaller).powerset,
          ((-1 : ℝ) ^ rest.card)) =
          if coalition \ smaller = ∅ then
            (1 : ℝ)
          else
            0 := by
      have hcast :
          (∑ rest ∈ (coalition \ smaller).powerset,
            ((-1 : ℝ) ^ rest.card)) =
            (((∑ rest ∈
              (coalition \ smaller).powerset,
              ((-1 : ℤ) ^ rest.card)) : ℤ) : ℝ) := by
        push_cast
        rfl
      rw [hcast, hinteger]
      split_ifs <;> simp
    rw [hreal]
    have hempty :
        coalition \ smaller = ∅ ↔
          smaller = coalition := by
      constructor
      · intro h
        exact
          Finset.Subset.antisymm hsmaller
            (Finset.sdiff_eq_empty_iff_subset.mp h)
      · rintro rfl
        exact Finset.sdiff_self _
    by_cases hequal : smaller = coalition
    · rw [if_pos hequal, if_pos (hempty.mpr hequal)]
    · rw [if_neg hequal,
        if_neg (fun h => hequal (hempty.mp h))]
  rw [Finset.sum_congr rfl hinner]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' coalition.powerset coalition G.value,
    if_pos (Finset.mem_powerset.mpr Finset.Subset.rfl)]

/-! ## Allocation rules and uniqueness -/

/-- A rule assigning an allocation to every game on the same agents. -/
abbrev AllocationRule (Agent : Type ua) :=
  CoalitionalGame Agent → Allocation Agent

namespace AllocationRule

variable [Fintype Agent]

/-- The rule distributes exactly the grand coalition's worth. -/
def IsEfficient (rule : AllocationRule Agent) : Prop :=
  ∀ G : CoalitionalGame Agent,
    ∑ agent, rule G agent = G.value Finset.univ

/-- The rule pays symmetric agents equally. -/
def IsSymmetric (rule : AllocationRule Agent) : Prop :=
  ∀ (G : CoalitionalGame Agent) {first second : Agent},
    G.AreSymmetric first second →
      rule G first = rule G second

/-- The rule pays every null agent zero. -/
def RespectsNull (rule : AllocationRule Agent) : Prop :=
  ∀ (G : CoalitionalGame Agent) {agent : Agent},
    G.IsNull agent → rule G agent = 0

/-- The rule is pointwise additive across games. -/
def IsAdditive (rule : AllocationRule Agent) : Prop :=
  ∀ (G H : CoalitionalGame Agent) (agent : Agent),
    rule (G.add H) agent =
      rule G agent + rule H agent

end AllocationRule

section FiniteAgents

variable [Fintype Agent]

theorem shapleyValue_isEfficient :
    AllocationRule.IsEfficient
      (fun G : CoalitionalGame Agent => G.shapleyValue) :=
  shapleyValue_efficient

theorem shapleyValue_isSymmetric :
    AllocationRule.IsSymmetric
      (fun G : CoalitionalGame Agent => G.shapleyValue) :=
  fun G _ _ hsymmetric =>
    G.shapleyValue_symmetric hsymmetric

theorem shapleyValue_respectsNull :
    AllocationRule.RespectsNull
      (fun G : CoalitionalGame Agent => G.shapleyValue) :=
  shapleyValue_null

theorem shapleyValue_isAdditive :
    AllocationRule.IsAdditive
      (fun G : CoalitionalGame Agent => G.shapleyValue) := by
  intro G H agent
  simpa only using
    congrFun (shapleyValue_add G H) agent

private theorem allocation_on_unanimityGame
    (rule : AllocationRule Agent)
    (hefficient : rule.IsEfficient)
    (hsymmetric : rule.IsSymmetric)
    (hnull : rule.RespectsNull)
    (coalition : Finset Agent) (hnonempty : coalition.Nonempty)
    (agent : Agent) :
    rule (unanimityGame coalition hnonempty) agent =
      if agent ∈ coalition then
        (1 : ℝ) / coalition.card
      else
        0 := by
  classical
  set G := unanimityGame coalition hnonempty
  by_cases hmember : agent ∈ coalition
  · have houtside :
        ∀ other ∉ coalition, rule G other = 0 :=
      fun other hnotmem =>
        hnull G
          (unanimityGame_isNull_of_notMem
            coalition hnonempty hnotmem)
    obtain ⟨share, hshare⟩ :
        ∃ share : ℝ,
          ∀ other ∈ coalition, rule G other = share := by
      refine
        ⟨rule G agent, fun other hother => ?_⟩
      by_cases hEq : other = agent
      · subst other
        rfl
      · exact
          hsymmetric G
            (unanimityGame_areSymmetric coalition hnonempty
              hEq hother hmember)
    have hsum :
        ∑ other, rule G other =
          ∑ other ∈ coalition, rule G other := by
      rw [← Finset.sum_filter_add_sum_filter_not
        Finset.univ (· ∈ coalition) (rule G)]
      have hin :
          Finset.univ.filter (· ∈ coalition) =
            coalition := by
        ext other
        simp
      have hout :
          ∑ other ∈
            Finset.univ.filter (¬ · ∈ coalition),
            rule G other = 0 := by
        apply Finset.sum_eq_zero
        intro other hother
        simp only [Finset.mem_filter, Finset.mem_univ,
          true_and] at hother
        exact houtside other hother
      rw [hin, hout, add_zero]
    have hsumConstant :
        ∑ other ∈ coalition, rule G other =
          coalition.card * share := by
      rw [Finset.sum_congr rfl
          (fun other hother => hshare other hother),
        Finset.sum_const, nsmul_eq_mul]
    have heff := hefficient G
    rw [hsum, hsumConstant,
      unanimityGame_value_univ] at heff
    have hpositive : 0 < (coalition.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hnonempty
    have hshareValue :
        share = 1 / coalition.card := by
      field_simp at heff ⊢
      linarith
    rw [if_pos hmember, hshare agent hmember, hshareValue]
  · rw [if_neg hmember]
    exact
      hnull G
        (unanimityGame_isNull_of_notMem
          coalition hnonempty hmember)

private theorem allocation_on_smul_unanimityGame
    (rule : AllocationRule Agent)
    (hefficient : rule.IsEfficient)
    (hsymmetric : rule.IsSymmetric)
    (hnull : rule.RespectsNull)
    (coalition : Finset Agent) (hnonempty : coalition.Nonempty)
    (scalar : ℝ) (agent : Agent) :
    rule (smul scalar (unanimityGame coalition hnonempty)) agent =
      if agent ∈ coalition then
        scalar / coalition.card
      else
        0 := by
  classical
  set G := smul scalar (unanimityGame coalition hnonempty) with hG
  by_cases hmember : agent ∈ coalition
  · have houtside :
        ∀ other ∉ coalition, rule G other = 0 :=
      fun other hnotmem =>
        hnull G
          (smul_isNull
            (unanimityGame_isNull_of_notMem
              coalition hnonempty hnotmem))
    obtain ⟨share, hshare⟩ :
        ∃ share : ℝ,
          ∀ other ∈ coalition, rule G other = share := by
      refine
        ⟨rule G agent, fun other hother => ?_⟩
      by_cases hEq : other = agent
      · subst other
        rfl
      · exact
          hsymmetric G
            (smul_areSymmetric
              (unanimityGame_areSymmetric coalition hnonempty
                hEq hother hmember))
    have hsum :
        ∑ other, rule G other =
          ∑ other ∈ coalition, rule G other := by
      rw [← Finset.sum_filter_add_sum_filter_not
        Finset.univ (· ∈ coalition) (rule G)]
      have hin :
          Finset.univ.filter (· ∈ coalition) =
            coalition := by
        ext other
        simp
      have hout :
          ∑ other ∈
            Finset.univ.filter (¬ · ∈ coalition),
            rule G other = 0 := by
        apply Finset.sum_eq_zero
        intro other hother
        simp only [Finset.mem_filter, Finset.mem_univ,
          true_and] at hother
        exact houtside other hother
      rw [hin, hout, add_zero]
    have hsumConstant :
        ∑ other ∈ coalition, rule G other =
          coalition.card * share := by
      rw [Finset.sum_congr rfl
          (fun other hother => hshare other hother),
        Finset.sum_const, nsmul_eq_mul]
    have hvalue : G.value Finset.univ = scalar := by
      rw [hG]
      simp only [smul]
      rw [unanimityGame_value_univ]
      ring
    have heff := hefficient G
    rw [hsum, hsumConstant, hvalue] at heff
    have hpositive : 0 < (coalition.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hnonempty
    have hshareValue :
        share = scalar / coalition.card := by
      field_simp at heff ⊢
      linarith
    rw [if_pos hmember, hshare agent hmember, hshareValue]
  · rw [if_neg hmember]
    exact
      hnull G
        (smul_isNull
          (unanimityGame_isNull_of_notMem
            coalition hnonempty hmember))

private def sumGames
    {Index : Type*} (indices : Finset Index)
    (games : Index → CoalitionalGame Agent) :
    CoalitionalGame Agent where
  value coalition :=
    ∑ index ∈ indices, (games index).value coalition
  value_empty := by
    apply Finset.sum_eq_zero
    intro index _
    exact (games index).value_empty

omit [DecidableEq Agent] [Fintype Agent] in
private theorem sumGames_value
    {Index : Type*} (indices : Finset Index)
    (games : Index → CoalitionalGame Agent)
    (coalition : Finset Agent) :
    (sumGames indices games).value coalition =
      ∑ index ∈ indices,
        (games index).value coalition :=
  rfl

omit [DecidableEq Agent] [Fintype Agent] in
private theorem allocation_sumGames
    (rule : AllocationRule Agent)
    (hadditive : rule.IsAdditive)
    {Index : Type*} (indices : Finset Index)
    (games : Index → CoalitionalGame Agent)
    (agent : Agent) :
    rule (sumGames indices games) agent =
      ∑ index ∈ indices, rule (games index) agent := by
  classical
  induction indices using Finset.induction with
  | empty =>
      rw [Finset.sum_empty]
      have hself :
          (sumGames (∅ : Finset Index) games).add
              (sumGames (∅ : Finset Index) games) =
            sumGames (∅ : Finset Index) games := by
        ext coalition
        simp [add, sumGames]
      have h :=
        hadditive
          (sumGames (∅ : Finset Index) games)
          (sumGames (∅ : Finset Index) games)
          agent
      rw [hself] at h
      linarith
  | insert index indices hnotmem ih =>
      have hequal :
          sumGames (insert index indices) games =
            (games index).add (sumGames indices games) := by
        ext coalition
        simp [add, sumGames, Finset.sum_insert hnotmem]
      rw [hequal, hadditive, ih,
        Finset.sum_insert hnotmem]

private def zeroGame : CoalitionalGame Agent where
  value _ := 0
  value_empty := rfl

private noncomputable def decompositionTerm
    (G : CoalitionalGame Agent) (coalition : Finset Agent) :
    CoalitionalGame Agent :=
  if hnonempty : coalition.Nonempty then
    smul (G.unanimityCoeff coalition)
      (unanimityGame coalition hnonempty)
  else
    zeroGame

private theorem eq_sumGames_decomposition
    (G : CoalitionalGame Agent) :
    G =
      sumGames
        (Finset.univ : Finset (Finset Agent))
        G.decompositionTerm := by
  classical
  ext coalition
  simp only [sumGames_value]
  have hterm :
      ∀ basis : Finset Agent,
        (G.decompositionTerm basis).value coalition =
          G.unanimityCoeff basis *
            (if basis ⊆ coalition then 1 else 0) := by
    intro basis
    simp only [decompositionTerm]
    by_cases hnonempty : basis.Nonempty
    · simp only [hnonempty, dif_pos, smul, unanimityGame]
    · simp only [hnonempty, dif_neg, zeroGame, not_false_iff]
      have hempty : basis = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      have hcoefficient :
          G.unanimityCoeff basis = 0 := by
        subst basis
        simp [unanimityCoeff, G.value_empty]
      rw [hcoefficient, zero_mul]
  rw [Finset.sum_congr rfl (fun basis _ => hterm basis)]
  have hmul :
      ∀ basis : Finset Agent,
        G.unanimityCoeff basis *
            (if basis ⊆ coalition then (1 : ℝ) else 0) =
          if basis ⊆ coalition then
            G.unanimityCoeff basis
          else
            0 := by
    intro basis
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun basis _ => hmul basis)]
  rw [← Finset.sum_filter]
  rw [show
    Finset.univ.filter
        (fun basis : Finset Agent => basis ⊆ coalition) =
      coalition.powerset by
        ext basis
        simp [Finset.mem_powerset]]
  exact G.unanimity_decomposition coalition

/-- **Shapley's uniqueness theorem.** Every allocation rule satisfying
efficiency, symmetry, the null-player axiom, and additivity is the Shapley
value on every coalitional game. -/
theorem shapleyValue_unique
    (rule : AllocationRule Agent)
    (hefficient : rule.IsEfficient)
    (hsymmetric : rule.IsSymmetric)
    (hnull : rule.RespectsNull)
    (hadditive : rule.IsAdditive)
    (G : CoalitionalGame Agent) :
    rule G = G.shapleyValue := by
  classical
  funext agent
  have hrule :
      rule G agent =
        ∑ basis : Finset Agent,
          rule (G.decompositionTerm basis) agent := by
    nth_rewrite 1 [G.eq_sumGames_decomposition]
    exact
      allocation_sumGames rule hadditive _ _
        agent
  have hshapley :
      G.shapleyValue agent =
        ∑ basis : Finset Agent,
          (G.decompositionTerm basis).shapleyValue agent := by
    nth_rewrite 1 [G.eq_sumGames_decomposition]
    exact
      allocation_sumGames
        (fun H : CoalitionalGame Agent => H.shapleyValue)
        shapleyValue_isAdditive _ _ agent
  rw [hrule, hshapley]
  refine Finset.sum_congr rfl (fun basis _ => ?_)
  simp only [decompositionTerm]
  by_cases hnonempty : basis.Nonempty
  · simp only [hnonempty, dif_pos]
    rw [allocation_on_smul_unanimityGame
        rule hefficient hsymmetric hnull
        basis hnonempty _ agent,
      allocation_on_smul_unanimityGame
        (fun H : CoalitionalGame Agent => H.shapleyValue)
        shapleyValue_isEfficient
        shapleyValue_isSymmetric
        shapleyValue_respectsNull
        basis hnonempty _ agent]
  · simp only [hnonempty, dif_neg, not_false_iff]
    have hnullAgent : zeroGame.IsNull agent := by
      intro coalition _
      simp [marginalContribution, zeroGame]
    rw [hnull zeroGame hnullAgent,
      shapleyValue_null zeroGame hnullAgent]

/-- The four axioms characterize exactly one allocation rule. -/
theorem shapleyValue_characterization :
    ∃! rule : AllocationRule Agent,
      rule.IsEfficient ∧
      rule.IsSymmetric ∧
      rule.RespectsNull ∧
      rule.IsAdditive := by
  refine
    ⟨(fun G : CoalitionalGame Agent => G.shapleyValue),
      ⟨shapleyValue_isEfficient,
        shapleyValue_isSymmetric,
        shapleyValue_respectsNull,
        shapleyValue_isAdditive⟩,
      ?_⟩
  intro rule hproperties
  funext G
  exact
    shapleyValue_unique rule
      hproperties.1 hproperties.2.1
      hproperties.2.2.1 hproperties.2.2.2 G

end FiniteAgents

end CoalitionalGame

end GameTheory
