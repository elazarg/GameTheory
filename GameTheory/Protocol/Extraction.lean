/-
# Reachable decision sites and strategy extraction

`Tree.PureStrategy` is defined by recursion on the tree, so a finite-first plan
is indexed by the tree's *own* decision sites. The general-state `Chooser`, by
contrast, is a function on *every* non-terminal state — all syntactically
possible states, including ones no play ever reaches.

This module closes that gap for the general-state presentation. It carves out the
reachable decision sites and proves the extraction is faithful: two choosers
that agree on reachable sites induce the same run law, so behaviour off the
reachable set is genuinely irrelevant rather than merely ignored by convention.

Note the difference from `IsTreeShaped`. There, history *uniqueness* had to be
stated over `Type`-valued traces, because a `Prop`-valued version is vacuous
under proof irrelevance. Here we only ask whether a history *exists*, which is
honestly a `Prop`.
-/

import GameTheory.Protocol.Execution

noncomputable section

namespace GameTheory.Protocol

open Probability

universe uι us ua

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

variable (E) in
/-- Some history ends at this state. Existence of a history is a genuine
proposition; only uniqueness needed traces to be data. -/
def Reachable (state : E.State) : Prop := Nonempty (Trace E state)

theorem reachable_init : E.Reachable E.init := ⟨.start⟩

/-- Reachability is preserved by a realized legal step. -/
theorem Reachable.extend {source target : E.State} (hsource : E.Reachable source)
    {joint : ∀ i, Option (E.Action i)} (isLegal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) :
    E.Reachable target :=
  hsource.elim fun prior => ⟨.extend prior joint isLegal realized⟩

/-- Everything the runner can produce from a reachable state is reachable. -/
theorem reachable_of_mem_runFor (chooser : E.Chooser) :
    ∀ (fuel : ℕ) {source reached : E.State}, E.Reachable source →
      reached ∈ (E.runFor chooser fuel source).support → E.Reachable reached := by
  intro fuel
  induction fuel with
  | zero =>
    intro source reached hsource hreached
    rw [runFor_zero, FinDist.mem_support_pure] at hreached
    subst hreached
    exact hsource
  | succ fuel ih =>
    intro source reached hsource hreached
    by_cases hterm : E.terminal source
    · rw [runFor_of_terminal chooser _ hterm, FinDist.mem_support_pure] at hreached
      subst hreached
      exact hsource
    · rw [runFor_succ_of_not_terminal chooser fuel hterm, FinDist.support_bind] at hreached
      simp only [Set.mem_iUnion] at hreached
      obtain ⟨mid, hmid, hrest⟩ := hreached
      exact ih (hsource.extend (chooser source hterm).2 hmid) hrest

variable (E) in
/-- A place where the protocol actually asks somebody to act: reachable, and
not stopped. -/
def DecisionSite : Type _ :=
  { state : E.State // E.Reachable state ∧ ¬ E.terminal state }

variable (E) in
/-- A strategy indexed by the protocol's own decision sites, rather than by
every syntactically possible state. -/
def SiteStrategy : Type _ :=
  (site : E.DecisionSite) → { joint : ∀ i, Option (E.Action i) // E.Legal site.1 joint }

/-- Every chooser restricts to the decision sites. -/
def Chooser.restrict (chooser : E.Chooser) : E.SiteStrategy :=
  fun site => chooser site.1 site.2.2

/-- **Faithfulness.** Choosers agreeing on the reachable decision sites induce
the same run law from any reachable state. Behaviour elsewhere cannot be
observed, so the site-indexed strategy is the honest object. -/
theorem runFor_congr_of_restrict_eq {first second : E.Chooser}
    (hagree : first.restrict = second.restrict) :
    ∀ (fuel : ℕ) {source : E.State}, E.Reachable source →
      E.runFor first fuel source = E.runFor second fuel source := by
  intro fuel
  induction fuel with
  | zero => intro source _; rfl
  | succ fuel ih =>
    intro source hsource
    by_cases hterm : E.terminal source
    · rw [runFor_of_terminal first _ hterm, runFor_of_terminal second _ hterm]
    · have hhere : first source hterm = second source hterm :=
        congrFun hagree ⟨source, hsource, hterm⟩
      rw [runFor_succ_of_not_terminal first fuel hterm,
        runFor_succ_of_not_terminal second fuel hterm, hhere]
      exact FinDist.bind_congr fun mid hmid =>
        ih (hsource.extend (second source hterm).2 hmid)

end ExecutionProtocol

end GameTheory.Protocol
