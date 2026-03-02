import GameTheory.SolutionConcepts

/-!
# Rationalizability

Iterated elimination of strictly dominated strategies and rationalizability.

A strategy is **rationalizable** if it survives all rounds of iterated
elimination of strictly dominated strategies. This is a fundamental solution
concept weaker than Nash equilibrium: every Nash equilibrium strategy is
rationalizable, but not conversely.

## Main definitions

* `KernelGame.Survives` — a strategy survives round `n` of elimination
* `KernelGame.IsRationalizable` — survives all rounds (the fixed point)

## Main results

* `KernelGame.Survives.mono` — survival is monotone decreasing in rounds
* `KernelGame.IsNash.survives` — Nash equilibrium strategies survive all rounds
* `KernelGame.IsNash.isRationalizable` — Nash equilibrium strategies are rationalizable
* `KernelGame.IsDominant.isRationalizable` — dominant strategies are rationalizable
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type}

open Classical in
/-- A strategy survives round `n` of iterated strict dominance elimination.

    - Round 0: all strategies survive.
    - Round n+1: `s` survives if it survived round `n` and is not strictly
      dominated by any round-`n` survivor, when opponents are restricted to
      round-`n` survivors. -/
def Survives (G : KernelGame ι) : ℕ → (who : ι) → G.Strategy who → Prop
  | 0 => fun _ _ => True
  | n + 1 => fun who s =>
      G.Survives n who s ∧
      ¬∃ t : G.Strategy who, G.Survives n who t ∧
        ∀ (σ : Profile G), (∀ j, G.Survives n j (σ j)) →
          G.eu (Function.update σ who t) who > G.eu (Function.update σ who s) who

/-- Survival is monotone: surviving round `n+1` implies surviving round `n`. -/
theorem Survives.prev {G : KernelGame ι} {n : ℕ} {who : ι} {s : G.Strategy who}
    (h : G.Survives (n + 1) who s) : G.Survives n who s :=
  h.1

/-- Survival is monotone in the number of rounds. -/
theorem Survives.mono {G : KernelGame ι} {m n : ℕ} (hmn : m ≤ n)
    {who : ι} {s : G.Strategy who} (h : G.Survives n who s) :
    G.Survives m who s := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih h.prev

/-- A strategy is **rationalizable** if it survives all rounds of iterated
    strict dominance elimination. -/
def IsRationalizable (G : KernelGame ι) (who : ι) (s : G.Strategy who) : Prop :=
  ∀ n, G.Survives n who s

/-- Nash equilibrium strategies survive all rounds of elimination. -/
theorem IsNash.survives {G : KernelGame ι} {σ : Profile G}
    (hN : G.IsNash σ) : ∀ (n : ℕ) (who : ι), G.Survives n who (σ who) := by
  intro n
  induction n with
  | zero => intro _; trivial
  | succ n ih =>
    intro who
    refine ⟨ih who, ?_⟩
    intro ⟨_t, _ht_surv, ht_dom⟩
    have h_dom := ht_dom σ ih
    classical
    have h_nash := hN who _t
    simp only [Function.update_eq_self] at h_dom
    linarith

/-- Nash equilibrium strategies are rationalizable. -/
theorem IsNash.isRationalizable {G : KernelGame ι} {σ : Profile G}
    (hN : G.IsNash σ) (who : ι) : G.IsRationalizable who (σ who) :=
  fun n => hN.survives n who

/-- A dominant strategy survives all rounds of elimination.

    Requires that every player has at least one strategy (so that
    round-`n` surviving profiles exist for applying dominance). -/
theorem IsDominant.survives {G : KernelGame ι} {who : ι} {s : G.Strategy who}
    (_hdom : G.IsDominant who s)
    (σ₀ : Profile G) (hσ₀ : σ₀ who = s)
    (hdom_all : ∀ j, G.IsDominant j (σ₀ j)) :
    ∀ n, G.Survives n who s := by
  have hN : G.IsNash σ₀ := dominant_is_nash G σ₀ hdom_all
  intro n
  rw [← hσ₀]
  exact hN.survives n who

open Classical in
/-- A rationalizable strategy survives the first round: it is not strictly
    dominated by any strategy against all profiles. -/
theorem IsRationalizable.not_globally_dominated {G : KernelGame ι}
    {who : ι} {s : G.Strategy who} (hs : G.IsRationalizable who s) :
    ¬∃ t : G.Strategy who,
      ∀ (σ : Profile G),
        G.eu (Function.update σ who t) who >
        G.eu (Function.update σ who s) who := by
  intro ⟨t, hdom⟩
  have hs1 := hs 1
  exact hs1.2 ⟨t, hs1.1 |> fun _ => trivial, fun σ _ => hdom σ⟩

end KernelGame

end GameTheory
