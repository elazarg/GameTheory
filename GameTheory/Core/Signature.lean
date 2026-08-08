/-
# Game signatures and profile operations

A `GameSignature` owns the strategy and outcome carriers. Profiles are bound to
the signature, never to a play law or a payoff package, so one profile theorem
serves every game built over the same signature.

`Profile.update`, `Profile.override`, and `Profile.restrict` are the *only*
public profile operations. `Function.update` is used here, in the profile
implementation, and nowhere else in the library. `Subprofile` and
`Profile.restrict` deliberately carry no `DecidableEq` instance: only the
operations that branch on membership need one.

This module deliberately imports no probability: signatures and profiles are
the lowest sufficient semantic layer, so the executable rational frontend can
share these operations without pulling real-valued semantics in.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic

namespace GameTheory

universe uι us uo

set_option linter.checkUnivs false in
/-- Strategy and outcome carriers. Strategy and outcome universes stay
independent by design, so a signature may pair small strategies with large
outcomes; the universe linter would otherwise suggest collapsing them. -/
structure GameSignature (ι : Type uι) where
  /-- Each player's strategy carrier. -/
  Strategy : ι → Type us
  /-- The shared outcome carrier. -/
  Outcome : Type uo

variable {ι : Type uι} {sig : GameSignature ι}

/-- A strategy profile over a signature. -/
abbrev Profile (sig : GameSignature ι) := ∀ i, sig.Strategy i

/-- The strategies of a designated group of players, and nothing else. A value
of this type cannot mention a nonmember's strategy. -/
abbrev Subprofile (sig : GameSignature ι) (members : Finset ι) :=
  (i : { i // i ∈ members }) → sig.Strategy i.1

/-- The one-player subprofile playing `s`. This is the only declaration in the
library that transports a strategy along a coordinate equality; the equality is
`j = i` for a member `j` of `{i}`, and the profile module is the designated
transport site. -/
def Subprofile.single (i : ι) (s : sig.Strategy i) : Subprofile sig {i} :=
  fun j => (Finset.mem_singleton.mp j.2).symm ▸ s

@[simp]
theorem Subprofile.single_self (i : ι) (s : sig.Strategy i) :
    Subprofile.single i s ⟨i, Finset.mem_singleton_self i⟩ = s := rfl

/-- A one-player subprofile carries exactly one strategy and nothing else. This
is the machine-checked form of the recommendation-locality invariant: a
unilateral deviation's input type is *equivalent* to the deviator's own
strategy, so it cannot mention another player's recommendation. -/
def Subprofile.singletonEquiv (i : ι) : Subprofile sig {i} ≃ sig.Strategy i where
  toFun own := own ⟨i, Finset.mem_singleton_self i⟩
  invFun := Subprofile.single i
  left_inv own := by
    funext j
    obtain ⟨j, hj⟩ := j
    obtain rfl := Finset.mem_singleton.mp hj
    rfl
  right_inv _ := rfl

namespace Profile

/-- Project a profile onto a group's coordinates. This is the only public
subprofile projection. -/
def restrict (members : Finset ι) (profile : Profile sig) : Subprofile sig members :=
  fun i => profile i.1

@[simp]
theorem restrict_apply (members : Finset ι) (profile : Profile sig)
    (i : { i // i ∈ members }) : restrict members profile i = profile i.1 := rfl

/-- Replace one player's strategy. -/
def update [DecidableEq ι] (profile : Profile sig) (i : ι) (s : sig.Strategy i) :
    Profile sig :=
  Function.update profile i s

/-- Replace a whole group's strategies, leaving every nonmember coordinate
untouched. -/
def override [DecidableEq ι] (members : Finset ι) (members' : Subprofile sig members)
    (profile : Profile sig) : Profile sig :=
  fun i => if h : i ∈ members then members' ⟨i, h⟩ else profile i

@[simp]
theorem update_same [DecidableEq ι] (profile : Profile sig) (i : ι) (s : sig.Strategy i) :
    update profile i s i = s :=
  Function.update_self ..

@[simp]
theorem update_of_ne [DecidableEq ι] (profile : Profile sig) {i j : ι}
    (s : sig.Strategy i) (h : j ≠ i) : update profile i s j = profile j :=
  Function.update_of_ne h ..

@[simp]
theorem update_eq_self [DecidableEq ι] (profile : Profile sig) (i : ι) :
    update profile i (profile i) = profile :=
  Function.update_eq_self ..

theorem update_idem [DecidableEq ι] (profile : Profile sig) (i : ι)
    (s t : sig.Strategy i) : update (update profile i s) i t = update profile i t :=
  Function.update_idem ..

theorem update_comm [DecidableEq ι] (profile : Profile sig) {i j : ι}
    (h : i ≠ j) (s : sig.Strategy i) (t : sig.Strategy j) :
    update (update profile i s) j t = update (update profile j t) i s :=
  Function.update_comm h s t profile

@[simp]
theorem override_mem [DecidableEq ι] (members : Finset ι) (members' : Subprofile sig members)
    (profile : Profile sig) (i : { i // i ∈ members }) :
    override members members' profile i.1 = members' i := by
  simp [override, i.2]

/-- Every nonmember coordinate survives an override. This is proved once here so
that no deviation concept has to restate it. -/
@[simp]
theorem override_of_not_mem [DecidableEq ι] (members : Finset ι)
    (members' : Subprofile sig members) (profile : Profile sig) {j : ι} (h : j ∉ members) :
    override members members' profile j = profile j := by
  simp [override, h]

@[simp]
theorem restrict_override [DecidableEq ι] (members : Finset ι)
    (members' : Subprofile sig members) (profile : Profile sig) :
    restrict members (override members members' profile) = members' := by
  funext i
  simp

@[simp]
theorem override_restrict [DecidableEq ι] (members : Finset ι) (profile : Profile sig) :
    override members (restrict members profile) profile = profile := by
  funext j
  by_cases h : j ∈ members <;> simp [override, h]

/-- A singleton override is exactly a unilateral update. -/
theorem override_singleton [DecidableEq ι] (i : ι) (members' : Subprofile sig {i})
    (profile : Profile sig) :
    override {i} members' profile =
      update profile i (members' ⟨i, Finset.mem_singleton_self i⟩) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [override]
  · simp [override, update, h, Finset.mem_singleton]

/-- A unilateral update is a singleton override. -/
@[simp]
theorem override_single [DecidableEq ι] (profile : Profile sig) (i : ι)
    (s : sig.Strategy i) :
    override {i} (Subprofile.single i s) profile = update profile i s :=
  override_singleton i (Subprofile.single i s) profile

end Profile

end GameTheory
