/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Babbling
import GameTheory.Languages.NFG.Examples

/-!
# Cheap-Talk Examples for Normal-Form Games

Small examples showing how normal-form games use the observable cheap-talk
extension. Cheap talk can add non-babbling equilibria; the theorem used here is
only the standard one-way babbling result.
-/

namespace NFG

open GameTheory

namespace BattleOfTheSexesCheapTalk

/-- A two-message cheap-talk channel for Battle of the Sexes. Messages reuse the
two activity labels; the default babbling message is `opera`. -/
noncomputable def extension : battleOfTheSexes.toKernelGame.CheapTalkExtension where
  Msg := fun _ => BoSAction
  default := fun _ => BoSAction.opera

/-- The Battle-of-the-Sexes kernel game with observable pre-play cheap talk. -/
noncomputable abbrev game : KernelGame Bool :=
  extension.game

/-- The `(Opera, Opera)` base Nash equilibrium embeds as a babbling equilibrium
of the observable cheap-talk extension. -/
theorem opera_babbling_nash :
    game.IsNash (extension.embedProfile bos_opera_opera) := by
  exact extension.babbling_nash
    ((IsNashPure_iff_kernelGame _ _).mp bos_opera_is_nash)

/-- The `(Football, Football)` base Nash equilibrium also embeds as a babbling
equilibrium, with the same default-message channel behavior. -/
theorem football_babbling_nash :
    game.IsNash (extension.embedProfile bos_football_football) := by
  exact extension.babbling_nash
    ((IsNashPure_iff_kernelGame _ _).mp bos_football_is_nash)

end BattleOfTheSexesCheapTalk

end NFG
