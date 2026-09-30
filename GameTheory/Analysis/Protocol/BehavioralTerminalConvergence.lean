/-
# Convergence of well-founded behavioral terminal laws

Convergence passes through the randomized terminal recursion one realized
successor at a time. A global fuel or uniform termination tail is unnecessary.
-/

import GameTheory.Protocol.BehavioralTerminal
import GameTheory.Math.Probability.Convergence

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

/-- Pointwise convergence of randomized choices passes through the
well-founded terminal-history law, even with unbounded finite play lengths. -/
theorem randomizedBackwardLaw_convergesPointwise
    (certificate : E.WellFoundedHistories)
    {sequence : ℕ → E.RandomizedChooser} {target : E.RandomizedChooser}
    (hchooser : ∀ history hterm,
      PMFConvergesPointwise (fun n => sequence n history hterm)
        (target history hterm)) (history : E.History) :
    PMFConvergesPointwise
      (fun n => E.randomizedBackwardLaw certificate (sequence n) history)
      (E.randomizedBackwardLaw certificate target history) := by
  classical
  induction history using
      certificate.induction with
  | _ current ih =>
      by_cases hterm : E.terminal current.state
      · simpa only [E.randomizedBackwardLaw_of_terminal hterm] using
          pmfConvergesPointwise_const (PMF.pure current)
      · let jointLaw (n : ℕ) := sequence n current hterm
        let jointTarget := target current hterm
        have hjoint : PMFConvergesPointwise jointLaw jointTarget :=
          hchooser current hterm
        let continuation (n : ℕ) (draw :
            {action : ∀ i, Option (E.Action i) // E.Legal current.state action}) :=
          (E.step current.state draw).bindOnSupport fun state realized =>
            E.randomizedBackwardLaw certificate (sequence n)
              (current.extend draw.2 realized)
        let targetContinuation (draw :
            {action : ∀ i, Option (E.Action i) // E.Legal current.state action}) :=
          (E.step current.state draw).bindOnSupport fun state realized =>
            E.randomizedBackwardLaw certificate target
              (current.extend draw.2 realized)
        have hcontinuation (draw :
            {action : ∀ i, Option (E.Action i) // E.Legal current.state action}) :
            PMFConvergesPointwise (fun n => continuation n draw)
              (targetContinuation draw) := by
          let kernel (n : ℕ) (state : E.State) : PMF E.History :=
            if realized : state ∈ (E.step current.state draw).support then
              E.randomizedBackwardLaw certificate (sequence n)
                (current.extend draw.2 realized)
            else PMF.pure current
          let targetKernel (state : E.State) : PMF E.History :=
            if realized : state ∈ (E.step current.state draw).support then
              E.randomizedBackwardLaw certificate target
                (current.extend draw.2 realized)
            else PMF.pure current
          have hkernel (state : E.State) :
              PMFConvergesPointwise (fun n => kernel n state)
                (targetKernel state) := by
            by_cases realized : state ∈ (E.step current.state draw).support
            · simpa only [kernel, targetKernel, dite_eq_left realized] using
                ih (current.extend draw.2 realized)
                  ⟨draw.1, draw.2, realized⟩
            · simpa only [kernel, targetKernel, dite_eq_right realized] using
                pmfConvergesPointwise_const (PMF.pure current)
          have hstep :=
            (pmfConvergesPointwise_const (E.step current.state draw)).bind
              (kernel := kernel) (targetKernel := targetKernel) hkernel
          have hbind (n : ℕ) :
              continuation n draw = (E.step current.state draw).bind (kernel n) := by
            unfold continuation kernel
            apply bindOnSupport_eq_bind_of_eq_on_support
            intro state realized
            simp only [dite_eq_left realized]
          have htarget :
              targetContinuation draw =
                (E.step current.state draw).bind targetKernel := by
            unfold targetContinuation targetKernel
            apply bindOnSupport_eq_bind_of_eq_on_support
            intro state realized
            simp only [dite_eq_left realized]
          simpa only [hbind, htarget] using hstep
        simpa only [E.randomizedBackwardLaw_of_not_terminal hterm,
          jointLaw, jointTarget, continuation, targetContinuation] using
          hjoint.bind hcontinuation

end ExecutionProtocol

namespace InformationModel

variable [Fintype ι] (M : InformationModel E)

/-- Local laws need converge only at decision sites. At a nonterminal history,
inactive players have a unique legal choice and hence a fixed law. -/
theorem behavioralJoint_convergesPointwise_of_sites
    {sequence : ℕ → (i : ι) → M.BehavioralPolicy i}
    {target : (i : ι) → M.BehavioralPolicy i}
    (hlimit : ∀ i (site : M.InformationSite i),
      PMFConvergesPointwise (fun n => sequence n i site.1)
        (target i site.1))
    (history : E.History) (hterm : ¬ E.terminal history.state) :
    PMFConvergesPointwise
      (fun n => M.behavioralJoint (sequence n) history.trace hterm)
      (M.behavioralJoint target history.trace hterm) := by
  classical
  have hcoordinate (i : ι) :
      PMFConvergesPointwise
        (fun n => sequence n i (M.infoOf i history.trace))
        (target i (M.infoOf i history.trace)) := by
    by_cases hactive : E.active history.state i
    · obtain ⟨joint, hlegal⟩ := E.exists_legal hterm
      obtain ⟨action, hchoice⟩ :=
        LegalOption.exists_eq_some_of_active (joint i)
          (E.legalOption_of_legal hlegal i) hactive
      let site : M.InformationSite i :=
        ⟨M.infoOf i history.trace,
          ⟨⟨history, rfl⟩, hterm, action, by
            rw [← hchoice]
            exact (M.menu_adequate i history.trace (joint i)).mpr
              (E.legalOption_of_legal hlegal i)⟩⟩
      simpa only [site] using hlimit i site
    · have heq (n : ℕ) :
          sequence n i (M.infoOf i history.trace) =
            target i (M.infoOf i history.trace) :=
        M.behavioral_eq_of_not_active (sequence n i) (target i)
          history.trace hactive
      simpa only [heq] using
        pmfConvergesPointwise_const (target i (M.infoOf i history.trace))
  simp only [InformationModel.behavioralJoint_eq_independentProduct]
  exact (PMFConvergesPointwise.independentProduct hcoordinate).map _

/-- Coordinate convergence of behavioral laws passes through every
well-founded terminal continuation without finite history or action carriers. -/
theorem runBehavioralTerminalFrom_convergesPointwise
    (certificate : E.WellFoundedHistories)
    {sequence : ℕ → (i : ι) → M.BehavioralPolicy i}
    {target : (i : ι) → M.BehavioralPolicy i}
    (hlimit : ∀ i (site : M.InformationSite i),
      PMFConvergesPointwise (fun n => sequence n i site.1)
        (target i site.1)) (history : E.History) :
    PMFConvergesPointwise
      (fun n => M.runBehavioralTerminalFrom certificate (sequence n) history)
      (M.runBehavioralTerminalFrom certificate target history) := by
  apply E.randomizedBackwardLaw_convergesPointwise certificate
  intro current hterm
  exact M.behavioralJoint_convergesPointwise_of_sites hlimit current hterm

omit [Fintype ι] in
/-- Whole-profile update preserves convergence at decision sites. -/
theorem update_convergesPointwise_on_sites [DecidableEq ι]
    {sequence : ℕ → (i : ι) → M.BehavioralPolicy i}
    {target : (i : ι) → M.BehavioralPolicy i}
    (hlimit : ∀ i (site : M.InformationSite i),
      PMFConvergesPointwise (fun n => sequence n i site.1)
        (target i site.1))
    (who : ι) {alternative : ℕ → M.BehavioralPolicy who}
    {replacement : M.BehavioralPolicy who}
    (halternative : ∀ site : M.InformationSite who,
      PMFConvergesPointwise (fun n => alternative n site.1)
        (replacement site.1))
    (i : ι) (site : M.InformationSite i) :
    PMFConvergesPointwise
      (fun n => (Profile.update (sig := M.behavioralSignature)
        (sequence n) who (alternative n)) i site.1)
      ((Profile.update (sig := M.behavioralSignature) target who replacement)
        i site.1) := by
  by_cases hi : i = who
  · subst i
    simpa only [Profile.update_same] using halternative site
  · simpa only [Profile.update_of_ne _ _ hi] using hlimit i site

end InformationModel

end GameTheory.Protocol
