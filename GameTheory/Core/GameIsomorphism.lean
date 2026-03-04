import GameTheory.Core.GameForm
import Math.Probability

/-!
# GameTheory.Core.GameIsomorphism

Structural isomorphisms for finite stochastic games.

This file separates two notions:

- `GameForm.ProtocolIsomorphism`: same protocol dynamics, i.e. same outcome
  distributions up to relabeling of strategies/outcomes.
- `KernelGame.GameIsomorphism`: same utility distributions up to relabeling of
  strategies.

Protocol isomorphism plus utility compatibility implies game isomorphism.
-/

namespace GameTheory

open Math.Probability

variable {ι : Type}

namespace GameForm

/-- Protocol-level isomorphism: relabel strategies/outcomes while preserving the
    induced outcome distribution for every profile. -/
structure ProtocolIsomorphism (F F' : GameForm ι) where
  stratEquiv : ∀ i, F.Strategy i ≃ F'.Strategy i
  outcomeEquiv : F.Outcome ≃ F'.Outcome
  outcomeKernel_preserved : ∀ σ : F.Profile,
    F'.outcomeKernel (fun i => stratEquiv i (σ i)) =
      (F.outcomeKernel σ).bind (fun ω => PMF.pure (outcomeEquiv ω))

end GameForm

namespace KernelGame

/-- Game-level isomorphism: relabel strategies while preserving joint utility
    distributions at every profile. -/
structure GameIsomorphism (G H : KernelGame ι) where
  stratEquiv : ∀ i, G.Strategy i ≃ H.Strategy i
  udist_preserved : ∀ σ : Profile G,
    H.udist (fun i => stratEquiv i (σ i)) = G.udist σ

/-- Utility-distribution preservation implies per-player utility-distribution
    preservation. -/
theorem GameIsomorphism.udistPlayer_preserved {G H : KernelGame ι}
    (e : GameIsomorphism G H) (σ : Profile G) (who : ι) :
    H.udistPlayer (fun i => e.stratEquiv i (σ i)) who = G.udistPlayer σ who := by
  have h :=
    congrArg (fun d : PMF (Payoff ι) => d.bind (fun u => PMF.pure (u who))) (e.udist_preserved σ)
  simpa [KernelGame.udistPlayer_eq_udist_bind] using h

/-- Protocol isomorphism between underlying game forms. -/
abbrev ProtocolIsomorphism (G H : KernelGame ι) : Type :=
  GameForm.ProtocolIsomorphism G.toGameForm H.toGameForm

/-- Protocol isomorphism plus utility compatibility implies game isomorphism. -/
def ProtocolIsomorphism.toGameIsomorphism {G H : KernelGame ι}
    (e : ProtocolIsomorphism G H)
    (hutil : ∀ ω : G.Outcome, H.utility (e.outcomeEquiv ω) = G.utility ω) :
    GameIsomorphism G H where
  stratEquiv := e.stratEquiv
  udist_preserved := by
    intro σ
    have hk := e.outcomeKernel_preserved σ
    have hk' : H.outcomeKernel (fun i => e.stratEquiv i (σ i)) =
        (G.outcomeKernel σ).bind (fun ω => PMF.pure (e.outcomeEquiv ω)) := by
      simpa using hk
    calc
      H.udist (fun i => e.stratEquiv i (σ i))
          = (H.outcomeKernel (fun i => e.stratEquiv i (σ i))).bind
              (fun ω => PMF.pure (H.utility ω)) := rfl
      _ = (G.outcomeKernel σ).bind (fun ω => PMF.pure (H.utility (e.outcomeEquiv ω))) := by
            rw [hk']
            rw [PMF.bind_bind]
            simp
      _ = (G.outcomeKernel σ).bind (fun ω => PMF.pure (G.utility ω)) := by
            congr
            funext ω
            exact congrArg PMF.pure (hutil ω)
      _ = G.udist σ := rfl

end KernelGame

end GameTheory
