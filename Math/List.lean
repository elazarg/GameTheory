/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.List.OfFn

/-!
# List Utilities

Small generic identities relating finite functions and lists.
-/

namespace Math
namespace List

/-- Converting a function extended by `Fin.snoc` to a list appends its last
value. -/
@[simp] theorem ofFn_snoc {α : Type*} {n : ℕ}
    (f : Fin n → α) (a : α) :
    _root_.List.ofFn (Fin.snoc f a) = _root_.List.ofFn f ++ [a] := by
  simpa using _root_.List.ofFn_succ' (Fin.snoc f a)

end List
end Math
