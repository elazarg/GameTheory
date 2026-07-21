/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.Contracts.Basic
import GameTheory.Mechanism.SocialChoice.GibbardSatterthwaite

/-!
# GameTheory.Mechanism.Tests

Compilation validation entrypoint for mechanism-design modules.
-/

namespace GameTheory.Mechanism.Tests

noncomputable section

open GameTheory

example (I : PrincipalAgent Bool Bool) (a : Bool) :
    I.agentUtility (I.linearPayment 1) a = I.socialSurplus a :=
  I.agentUtility_linearPayment_one a

example (I : PrincipalAgent Bool Bool) (a : Bool) :
    I.principalUtility (I.linearPayment 1) a = 0 :=
  I.principalUtility_linearPayment_one a

example : HasAtLeastThree (Fin 3) :=
  hasAtLeastThree_of_natCard (by norm_num [Nat.card_eq_fintype_card])

example : HasAtLeastThree ℕ := by
  refine ⟨inferInstance, fun a b => ⟨max a b + 1, ?_, ?_⟩⟩ <;> omega

universe u v

example {ι : Type u} {A : Type v} [Nonempty ι] [Finite ι] {f : SWF ι A}
    (hswo : f.IsSWO) (hp : f.IsParetoOnRankings) (hiia : f.IsIIAOnRankings)
    (hA : HasAtLeastThree A) : ∃ d, f.IsDictatorOnRankings d :=
  arrow_impossibility hswo hp hiia hA

example {ι : Type u} [Nonempty ι] [Finite ι] [DecidableEq ι] {g : SCF ι ℕ}
    (hsp : g.IsStrategyProof) (honto : g.IsOnto) : ∃ d, g.IsDictator d :=
  SCF.gibbard_satterthwaite hsp honto (by
    refine ⟨inferInstance, fun a b => ⟨max a b + 1, ?_, ?_⟩⟩ <;> omega)

end

end GameTheory.Mechanism.Tests
