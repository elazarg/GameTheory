import GameTheory.Core.KernelGame
import GameTheory.Languages.FOSG.Execution

/-!
# GameTheory.Languages.FOSG.Compile

Compilation of FOSGs into `KernelGame`.

The induced `KernelGame` uses legal behavioral strategies as the strategy sets
and terminal realized histories as outcomes. Since `KernelGame` expects a PMF
on outcomes, this bridge is available under an explicit normalization
assumption on the terminal-history mass function.
-/

namespace GameTheory

open Math.Probability
open scoped BigOperators

namespace FOSG

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

namespace History

variable {G : FOSG ι W Act PrivObs PubObs}

/-- Total history extension by a legal action and candidate destination. If the
transition mass is zero, the history is left unchanged; this branch contributes
zero mass inside the induced PMF kernels. -/
noncomputable def extendByOutcome
    (h : G.History) (a : G.LegalAction h.lastState) (dst : W) : G.History :=
  if hsupp : G.transition h.lastState a dst ≠ 0 then h.snoc a dst hsupp else h

theorem extendByOutcome_of_support
    (h : G.History) (a : G.LegalAction h.lastState) (dst : W)
    (hsupp : G.transition h.lastState a dst ≠ 0) :
    h.extendByOutcome a dst = h.snoc a dst hsupp := by
  simp [extendByOutcome, hsupp]

theorem extendByOutcome_of_no_support
    (h : G.History) (a : G.LegalAction h.lastState) (dst : W)
    (hsupp : G.transition h.lastState a dst = 0) :
    h.extendByOutcome a dst = h := by
  simp [extendByOutcome, hsupp]

/-- Horizon-bounded run distribution on realized histories induced by a legal
behavioral profile. Terminal histories absorb. -/
noncomputable def runDistFrom
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) : Nat → G.History → PMF G.History
  | 0, h => PMF.pure h
  | n + 1, h =>
      if hterm : G.terminal h.lastState then
        PMF.pure h
      else
        (G.legalActionLaw σ h hterm).bind fun a =>
          (G.transition h.lastState a).bind fun dst =>
            runDistFrom G σ n (h.extendByOutcome a dst)

@[simp] theorem runDistFrom_zero
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) (h : G.History) :
    runDistFrom G σ 0 h = PMF.pure h := rfl

@[simp] theorem runDistFrom_succ_terminal
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) (n : Nat) (h : G.History)
    (hterm : G.terminal h.lastState) :
    runDistFrom G σ (n + 1) h = PMF.pure h := by
  simp [runDistFrom, hterm]

@[simp] theorem runDistFrom_succ_nonterminal
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) (n : Nat) (h : G.History)
    (hterm : ¬ G.terminal h.lastState) :
    runDistFrom G σ (n + 1) h =
      (G.legalActionLaw σ h hterm).bind fun a =>
        (G.transition h.lastState a).bind fun dst =>
          runDistFrom G σ n (h.extendByOutcome a dst) := by
  simp [runDistFrom, hterm]

end History

/-- Exact-horizon predicate for FOSGs: terminal histories are exactly those of
length `k`. -/
def ExactHorizon
    (G : FOSG ι W Act PrivObs PubObs) (k : Nat) : Prop :=
  ∀ h : G.History, h.IsTerminal ↔ h.steps.length = k

/-- Horizon-bounded run distribution on realized histories from the initial
history. -/
noncomputable def runDist
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (k : Nat) (σ : G.LegalBehavioralProfile) : PMF G.History :=
  History.runDistFrom G σ k (History.nil G)

@[simp] theorem runDist_zero
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) :
    G.runDist 0 σ = PMF.pure (History.nil G) := rfl

/-- The terminal-history mass function normalizes to a probability law on
legal behavioral profiles. -/
def HasNormalizedTerminalLaw
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal] : Prop := by
  classical
  exact ∀ σ : G.LegalBehavioralProfile,
    ∑ h : G.History, History.terminalWeight (G := G) σ.toProfile h = 1

/-- The terminal-history law induced by a legal behavioral profile, assuming
normalization. -/
noncomputable def terminalLawPMF
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw)
    (σ : G.LegalBehavioralProfile) : PMF G.History := by
  classical
  exact PMF.ofFintype
    (fun h => History.terminalWeight (G := G) σ.toProfile h)
    (hNorm σ)

@[simp] theorem terminalLawPMF_apply
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw)
    (σ : G.LegalBehavioralProfile) (h : G.History) :
    G.terminalLawPMF hNorm σ h = History.terminalWeight (G := G) σ.toProfile h := by
  simp [terminalLawPMF, PMF.ofFintype_apply]

/-- The `KernelGame` induced by a FOSG whose terminal-history law normalizes on
legal behavioral profiles. -/
noncomputable def toKernelGame
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw) : KernelGame ι where
  Strategy := fun i => G.LegalBehavioralStrategy i
  Outcome := G.History
  utility := fun h i => History.utility h i
  outcomeKernel := fun σ => G.terminalLawPMF hNorm σ

@[simp] theorem toKernelGame_outcomeKernel
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw)
    (σ : G.LegalBehavioralProfile) :
    (G.toKernelGame hNorm).outcomeKernel σ = G.terminalLawPMF hNorm σ := rfl

/-- Expected utility in the induced `KernelGame` is exactly the terminal-history
sum computed from the native FOSG execution semantics. -/
theorem toKernelGame_eu_eq
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw)
    (σ : G.LegalBehavioralProfile) (i : ι) :
    (G.toKernelGame hNorm).eu σ i =
      ∑ h : G.History,
        (History.terminalWeight (G := G) σ.toProfile h).toReal * History.utility h i := by
  rw [KernelGame.eu]
  simp [toKernelGame, terminalLawPMF, expect_eq_sum]

/-- Canonical finite-horizon compilation of a FOSG to `KernelGame`, using the
native history run distribution after exactly `k` steps. This does not require
any terminal-law normalization assumption. -/
noncomputable def toKernelGameAtHorizon
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (k : Nat) : KernelGame ι where
  Strategy := fun i => G.LegalBehavioralStrategy i
  Outcome := G.History
  utility := fun h i => History.utility h i
  outcomeKernel := fun σ => G.runDist k σ

@[simp] theorem toKernelGameAtHorizon_outcomeKernel
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (k : Nat) (σ : G.LegalBehavioralProfile) :
    (G.toKernelGameAtHorizon k).outcomeKernel σ = G.runDist k σ := rfl

theorem toKernelGameAtHorizon_eu_eq
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal] [Fintype G.History]
    (k : Nat) (σ : G.LegalBehavioralProfile) (i : ι) :
    (G.toKernelGameAtHorizon k).eu σ i =
      ∑ h : G.History, (G.runDist k σ h).toReal * History.utility h i := by
  rw [KernelGame.eu]
  simp [toKernelGameAtHorizon, expect_eq_sum]

end FOSG

end GameTheory
