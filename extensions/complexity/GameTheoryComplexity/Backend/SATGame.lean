import Complexitylib.SAT.Verifier
import GameTheory.Core.SatisfiabilityGame

/-! Semantic interpretation of encoded SAT inputs as finite literal/clause games.
Variables and clauses are padded to the bit length plus one. Clause indices run
backwards through the decoded formula, matching a scan from the input tail.
Unused clause slots are tautologies; malformed inputs have only empty clauses.
-/

namespace GameTheory.Complexity.Backend

open _root_.Complexity.SAT

/-- Incidence of a padded CNF with clauses indexed from the final clause. -/
def paddedSATIncidence (φ : CNF) (n m : ℕ) : SatisfiabilityGame.Clauses n m :=
  fun c v b => match φ.reverse[c.val]? with
    | some clause => clause.any fun lit => lit.var == v.val && lit.sign == b
    | none => true

/-- Decode a SAT instance into a polynomial-sized literal/clause game incidence. -/
def satIncidence (input : List Bool) :
    SatisfiabilityGame.Clauses (input.length + 1) (input.length + 1) :=
  match CNF.decode? input with
  | some φ => paddedSATIncidence φ _ _
  | none => fun _ _ _ => false

/-- The concrete encoding contains at least one bit per clause. -/
theorem cnf_length_le_encode_length (φ : CNF) : φ.length ≤ φ.encode.length := by
  induction φ with
  | nil => simp [CNF.encode]
  | cons c cs ih =>
      simp only [List.length_cons, CNF.encode_cons, List.length_append,
        List.length_cons, List.length_nil]
      omega

/-- A satisfying assignment satisfies the padded incidence table. -/
theorem paddedSATIncidence_satisfies_of_satisfiable
    (φ : CNF) {n m : ℕ} (hn : φ.maxVar < n) (hφ : φ.Satisfiable) :
    ∃ τ, SatisfiabilityGame.Satisfies (paddedSATIncidence φ n m) τ := by
  rcases hφ with ⟨α, hα⟩
  refine ⟨fun v => α.get v.val, ?_⟩
  intro c
  cases hc : φ.reverse[c.val]? with
  | none =>
      refine ⟨⟨0, by omega⟩, ?_⟩
      simp [paddedSATIncidence, hc]
  | some clause =>
      have hclause : clause ∈ φ := by
        exact List.mem_reverse.mp (List.mem_of_getElem? hc)
      have heval : Clause.eval α clause = true :=
        List.all_eq_true.mp hα clause hclause
      obtain ⟨lit, hlit, htrue⟩ := List.any_eq_true.mp heval
      have hv : lit.var < n :=
        lt_of_le_of_lt ((Clause.var_le_maxVar hlit).trans
          (CNF.clause_maxVar_le_maxVar hclause)) hn
      refine ⟨⟨lit.var, hv⟩, ?_⟩
      simp only [paddedSATIncidence, hc]
      apply List.any_eq_true.mpr
      refine ⟨lit, hlit, ?_⟩
      simp [Lit.eval] at htrue
      simp [htrue]

/-- Satisfaction of the padded incidence table yields a satisfying bit assignment. -/
theorem satisfiable_of_paddedSATIncidence_satisfies
    (φ : CNF) {n m : ℕ} (hm : φ.length ≤ m)
    (τ : Fin n → Bool) (hτ : SatisfiabilityGame.Satisfies (paddedSATIncidence φ n m) τ) :
    φ.Satisfiable := by
  refine ⟨List.ofFn τ, List.all_eq_true.mpr ?_⟩
  intro clause hclause
  have hrev : clause ∈ φ.reverse := List.mem_reverse.mpr hclause
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hrev
  have him : i < m := by
    simp only [List.length_reverse] at hi
    exact hi.trans_le hm
  have hget : φ.reverse[i]? = some clause := by
    rw [List.getElem?_eq_getElem hi, heq]
  obtain ⟨v, hv⟩ := hτ ⟨i, him⟩
  simp only [paddedSATIncidence, hget, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at hv
  obtain ⟨lit, hlit, hvar, hsign⟩ := hv
  apply List.any_eq_true.mpr
  refine ⟨lit, hlit, ?_⟩
  simp [Lit.eval, Assignment.get, hvar, hsign]

/-- Padding variables and clauses preserves satisfiability. -/
theorem paddedSATIncidence_satisfiable_iff
    (φ : CNF) {n m : ℕ} (hn : φ.maxVar < n) (hm : φ.length ≤ m) :
    φ.Satisfiable ↔ ∃ τ, SatisfiabilityGame.Satisfies (paddedSATIncidence φ n m) τ :=
  ⟨paddedSATIncidence_satisfies_of_satisfiable φ hn,
    fun ⟨τ, hτ⟩ => satisfiable_of_paddedSATIncidence_satisfies φ hm τ hτ⟩

/-- Encoded SAT membership is precisely satisfaction of the decoded game incidence. -/
theorem sat_language_iff_satisfies (input : List Bool) :
    input ∈ _root_.Complexity.SAT.language ↔
      ∃ τ, SatisfiabilityGame.Satisfies (satIncidence input) τ := by
  cases hdecode : CNF.decode? input with
  | none =>
      constructor
      · rintro ⟨φ, hinput, _⟩
        rw [hinput, CNF.decode?_encode] at hdecode
        contradiction
      · rintro ⟨τ, hτ⟩
        obtain ⟨v, hv⟩ := hτ ⟨0, by omega⟩
        simp [satIncidence, hdecode] at hv
  | some φ =>
      have hinput : input = φ.encode := CNF.decode?_sound hdecode
      have hn : φ.maxVar < input.length + 1 := by
        have h := CNF.maxVar_le_encode_length φ
        rw [← hinput] at h
        omega
      have hm : φ.length ≤ input.length + 1 := by
        have h := cnf_length_le_encode_length φ
        rw [← hinput] at h
        omega
      simp only [satIncidence, hdecode]
      rw [← paddedSATIncidence_satisfiable_iff φ hn hm]
      constructor
      · rintro ⟨ψ, hψ, hsat⟩
        have hsame : φ = ψ := by
          rw [hψ, CNF.decode?_encode] at hdecode
          exact Option.some.inj hdecode.symm
        exact hsame.symm ▸ hsat
      · exact fun hsat => ⟨φ, hinput, hsat⟩

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
