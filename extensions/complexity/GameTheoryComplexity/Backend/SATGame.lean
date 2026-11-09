module

public import GameTheoryComplexity.Backend.SATTableScannerCorrectness
public import GameTheory.Core.SatisfiabilityGame

@[expose] public section

/-! Semantic interpretation of encoded SAT inputs as finite literal/clause games.
Variables and clauses are padded to the bit length plus one. Clause indices run
backwards through the decoded formula, matching a scan from the input tail.
Unused clause slots are tautologies; malformed inputs have only empty clauses.
-/

namespace GameTheory.Complexity.Backend

open Cslib.Logic.PL

/-- Satisfiable native CNF formulas in the public unary byte format. -/
def satWordLanguage : Set (List Bool) :=
  {input | ∃ formula : CNF ℕ,
    SATWords.decodeFormula? input = some formula ∧ formula.Satisfiable}

@[simp] theorem mem_satWordLanguage_encodeFormula (formula : CNF ℕ) :
    SATWords.encodeFormula formula ∈ satWordLanguage ↔ formula.Satisfiable := by
  simp [satWordLanguage, SATWords.decodeFormula_encodeFormula]

/-- Incidence of a padded CNF with clauses indexed from the final clause. -/
def paddedSATIncidence (formula : CNF ℕ) (n m : ℕ) : SatisfiabilityGame.Clauses n m :=
  fun clause var sign => match formula.reverse[clause.val]? with
    | some literals => literals.any fun literal => literal.1 == var.val && literal.2 == sign
    | none => true

/-- Decode a SAT instance into a polynomial-sized literal/clause game incidence. -/
def satIncidence (input : List Bool) :
    SatisfiabilityGame.Clauses (input.length + 1) (input.length + 1) :=
  match SATWords.decodeFormula? input with
  | some formula => paddedSATIncidence formula _ _
  | none => fun _ _ _ => false

/-- A satisfying assignment satisfies the padded incidence table. -/
theorem paddedSATIncidence_satisfies_of_satisfiable
    (formula : CNF ℕ) {n m : ℕ} (hn : 0 < n)
    (hvars : ∀ clause ∈ formula, ∀ literal ∈ clause, literal.1 < n)
    (hformula : formula.Satisfiable) :
    ∃ assignment, SatisfiabilityGame.Satisfies (paddedSATIncidence formula n m) assignment := by
  rcases hformula with ⟨assignment, hsat⟩
  refine ⟨fun var => assignment var.val, ?_⟩
  intro clause
  cases hc : formula.reverse[clause.val]? with
  | none =>
      refine ⟨⟨0, hn⟩, ?_⟩
      simp [paddedSATIncidence, hc]
  | some literals =>
      have hclause : literals ∈ formula :=
        List.mem_reverse.mp (List.mem_of_getElem? hc)
      have heval : literals.eval assignment = true :=
        (CNF.eval_eq_true_iff assignment formula).mp hsat literals hclause
      obtain ⟨literal, hliteral, htrue⟩ := (Clause.eval_eq_true_iff assignment literals).mp heval
      refine ⟨⟨literal.1, hvars literals hclause literal hliteral⟩, ?_⟩
      simp only [paddedSATIncidence, hc]
      apply List.any_eq_true.mpr
      refine ⟨literal, hliteral, ?_⟩
      simp [htrue]

/-- Satisfaction of the padded incidence table yields a satisfying native assignment. -/
theorem satisfiable_of_paddedSATIncidence_satisfies
    (formula : CNF ℕ) {n m : ℕ} (hm : formula.length ≤ m)
    (assignment : Fin n → Bool)
    (hsat : SatisfiabilityGame.Satisfies (paddedSATIncidence formula n m) assignment) :
    formula.Satisfiable := by
  let extension (var : ℕ) : Bool :=
    if h : var < n then assignment ⟨var, h⟩ else false
  refine ⟨extension, (CNF.eval_eq_true_iff extension formula).mpr ?_⟩
  intro clause hclause
  have hrev : clause ∈ formula.reverse := List.mem_reverse.mpr hclause
  obtain ⟨index, hi, heq⟩ := List.mem_iff_getElem.mp hrev
  have him : index < m := by
    simp only [List.length_reverse] at hi
    exact hi.trans_le hm
  have hget : formula.reverse[index]? = some clause := by
    rw [List.getElem?_eq_getElem hi, heq]
  obtain ⟨var, hv⟩ := hsat ⟨index, him⟩
  simp only [paddedSATIncidence, hget, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at hv
  obtain ⟨literal, hliteral, hvar, hsign⟩ := hv
  apply (Clause.eval_eq_true_iff extension clause).mpr
  refine ⟨literal, hliteral, ?_⟩
  simp [extension, hvar, hsign]

/-- Literal bounds alone do not make tautological padding satisfiable when no
variable action is available. -/
private theorem empty_formula_zero_variables :
    CNF.Satisfiable ([] : CNF ℕ) ∧
      (∀ clause ∈ ([] : CNF ℕ), ∀ literal ∈ clause, literal.1 < 0) ∧
      ¬∃ assignment : Fin 0 → Bool,
        SatisfiabilityGame.Satisfies (paddedSATIncidence [] 0 1) assignment := by
  refine ⟨⟨fun _ => false, rfl⟩, by simp, ?_⟩
  rintro ⟨assignment, hsat⟩
  obtain ⟨var, _⟩ := hsat ⟨0, by omega⟩
  exact Fin.elim0 var

/-- Padding native CNF variables and clauses preserves satisfiability. -/
theorem paddedSATIncidence_satisfiable_iff
    (formula : CNF ℕ) {n m : ℕ} (hn : 0 < n)
    (hvars : ∀ clause ∈ formula, ∀ literal ∈ clause, literal.1 < n)
    (hm : formula.length ≤ m) :
    formula.Satisfiable ↔
      ∃ assignment, SatisfiabilityGame.Satisfies (paddedSATIncidence formula n m) assignment :=
  ⟨paddedSATIncidence_satisfies_of_satisfiable formula hn hvars,
    fun ⟨assignment, hsat⟩ => satisfiable_of_paddedSATIncidence_satisfies formula hm assignment hsat⟩

/-- Unary SAT-word membership is precisely satisfaction of the decoded game incidence. -/
theorem satWordLanguage_iff_satisfies (input : List Bool) :
    input ∈ satWordLanguage ↔
      ∃ assignment, SatisfiabilityGame.Satisfies (satIncidence input) assignment := by
  cases hdecode : SATWords.decodeFormula? input with
  | none =>
      constructor
      · rintro ⟨formula, hformula, _⟩
        rw [hdecode] at hformula
        contradiction
      · rintro ⟨assignment, hsat⟩
        obtain ⟨var, hv⟩ := hsat ⟨0, by omega⟩
        simp [satIncidence, hdecode] at hv
  | some formula =>
      have hinput := SATWords.decodeFormula_sound hdecode
      have hvars : ∀ clause ∈ formula, ∀ literal ∈ clause,
          literal.1 < input.length + 1 := by
        intro clause hclause literal hliteral
        have h := SATWords.variable_le_encodeFormula_length literal clause formula hliteral hclause
        rw [← hinput] at h
        omega
      have hm : formula.length ≤ input.length + 1 := by
        have h := SATWords.clauseCount_le_encodeFormula_length formula
        rw [← hinput] at h
        omega
      have hlanguage : input ∈ satWordLanguage ↔ formula.Satisfiable := by
        simp [satWordLanguage, hdecode]
      simpa only [satIncidence, hdecode] using hlanguage.trans
        (paddedSATIncidence_satisfiable_iff formula (by omega) hvars hm)

/-- On decoded words the reverse scanner agrees with the canonical game incidence. -/
theorem scanIncidence_eq_satIncidence (input : List Bool) (formula : CNF ℕ)
    (hdecode : SATWords.decodeFormula? input = some formula)
    (clause var : Fin (input.length + 1)) (sign : Bool) :
    scanIncidence var.val sign clause.val input = satIncidence input clause var sign := by
  simp only [satIncidence, hdecode, paddedSATIncidence]
  exact scanIncidence_decode input formula hdecode var.val clause.val sign

/-- The reduction has a linear number of actions per player. -/
theorem sat_action_card (input : List Bool) :
    Fintype.card (SatisfiabilityGame.Action (input.length + 1) (input.length + 1)) =
      4 * input.length + 5 := by
  simp [SatisfiabilityGame.Action, Fintype.card_sum, Fintype.card_prod]
  omega

/-- An explicit payoff matrix has a quadratic number of cells. -/
theorem sat_matrix_cell_card (input : List Bool) :
    Fintype.card
      (SatisfiabilityGame.Action (input.length + 1) (input.length + 1) ×
       SatisfiabilityGame.Action (input.length + 1) (input.length + 1)) =
      (4 * input.length + 5) ^ 2 := by
  rw [Fintype.card_prod, sat_action_card]
  simp only [pow_two]

/-- Every payoff has magnitude bounded linearly in the source bit length. -/
theorem sat_payoffInt_bounds (input : List Bool)
    (a b : SatisfiabilityGame.Action (input.length + 1) (input.length + 1)) :
    -((input.length : ℤ) + 3) ≤ SatisfiabilityGame.payoffInt (satIncidence input) a b ∧
      SatisfiabilityGame.payoffInt (satIncidence input) a b ≤ (input.length : ℤ) + 3 := by
  rcases a with ⟨va, ba⟩ | va | ca | ua <;>
    rcases b with ⟨vb, bb⟩ | vb | cb | ub <;>
    simp only [SatisfiabilityGame.payoffInt] <;> (try split_ifs) <;> omega

end GameTheory.Complexity.Backend
