import GameTheory.Languages.EFG.SOS
import GameTheory.Theorems.Kuhn

/-!
# GameTheory.Languages.EFG.CompileObs

Compilation of EFG tree semantics into the `ObsModel` layer.

The compiled `ObsModel` treats each tree node as a stochastic transition:
chance nodes sample from their distribution, decision nodes read the acting
player's action deterministically. Terminal nodes are absorbing.

## Main definitions

- `compileObsModel G` : the observation model for an EFG game tree

## TODO

This compilation currently uses the canonical list-backed
`InfoStateSpec.list` representation in `ObsModel`. For EFGs, the semantically
relevant local information states are the finite set of observation summaries
reachable in the given tree, not all list-backed states over
`Option (Infoset i)`. Any future full-strength
Kuhn reduction through the generic `ObsModel` layer should therefore either:

- compile to an information-state-indexed model whose carrier is the finite
  reachable summary space for the tree, or
- use a restricted/covered-history Kuhn theorem rather than the unrestricted
  list-backed one.

The bridge bundle below (`ObsCompilation`) isolates the profile lift/descent
maps needed for that future reduction, but it does not by itself supply the
finite reachable information-state carrier or the run-distribution-to-`evalDist`
compatibility theorem.
-/

namespace GameTheory.EFG

open _root_.EFG

variable {S : InfoStructure} {Outcome : Type}

/-- Compiled action family for the `ObsModel` view of an EFG.

Inactive observations carry only the trivial action, while an active infoset
uses its native action type. -/
def CompiledAct (S : InfoStructure) (i : S.Player) :
    Option (S.Infoset i) → Type
  | none => PUnit
  | some I => S.Act I

theorem compiledAct_eq_of_some (S : InfoStructure) (i : S.Player)
    {o : Option (S.Infoset i)} {I : S.Infoset i} (h : o = some I) :
    CompiledAct S i o = S.Act I := by
  cases h
  rfl

instance compiledActFintype (S : InfoStructure) (i : S.Player)
    (o : Option (S.Infoset i)) : Fintype (CompiledAct S i o) := by
  cases o <;> dsimp [CompiledAct] <;> infer_instance

instance compiledActNonempty (S : InfoStructure) (i : S.Player)
    (o : Option (S.Infoset i)) : Nonempty (CompiledAct S i o) := by
  cases o with
  | none =>
      exact ⟨PUnit.unit⟩
  | some I =>
      dsimp [CompiledAct]
      exact ⟨⟨0, S.arity_pos i I⟩⟩

/-- Stochastic tree step: given a game tree node and joint player actions,
produce a distribution over successor tree nodes.

- **Chance**: sample from μ, ignore all actions
- **Decision** at infoset I of player p: read p's unique active action
- **Terminal**: absorbing (identity) -/
noncomputable def treeStepPMF
    (t : GameTree S Outcome)
    (acts : ∀ p : S.Player,
      CompiledAct S p (obsOfState (S := S) (Outcome := Outcome) p t)) :
    PMF (GameTree S Outcome) :=
  match t with
  | .terminal z => PMF.pure (.terminal z)
  | .chance _k μ _hk next => μ.map next
  | .decision (p := p) I next =>
      PMF.pure (next (by
        simpa [CompiledAct, obsOfState] using acts p))

/-- Compile an EFG game tree into the observation model layer.

- **States**: game tree nodes (`GameTree S Outcome`)
- **Players**: `Fin S.n`
- **Observations**: `Option (S.Infoset i)` (current infoset if acting, else none)
- **Actions**: `CompiledAct S i` (`PUnit` when inactive, `S.Act I` when active)
- **Step**: stochastic resolution via `treeStepPMF`
-/
noncomputable def compileObsModel (t : GameTree S Outcome) :
    ObsModel S.Player (GameTree S Outcome)
      (fun i => Option (S.Infoset i))
      (CompiledAct S) where
  infoState := fun _ => InfoStateSpec.list _
  observe := fun i s => obsOfState (S := S) (Outcome := Outcome) i s
  machine := {
    init := t
    step := fun s acts => treeStepPMF s acts
  }

/-- Core EFG compilation with the honest strategic state:
the current active infoset (or `none` when inactive). -/
noncomputable def compileObsCoreModel (t : GameTree S Outcome) :
    ObsModelCore S.Player (GameTree S Outcome)
      (fun i => Option (S.Infoset i))
      (CompiledAct S) where
  infoState := fun _ => {
    Carrier := Option _
    start := id
    push := fun _ o => o
    current := id
    current_start := by intro o; rfl
    current_push := by intro _ o; rfl
  }
  observe := fun i s => obsOfState (S := S) (Outcome := Outcome) i s
  machine := {
    init := t
    step := fun s acts => treeStepPMF s acts
  }

/-- Canonical core information state for observation `o`. -/
def canonicalCoreInfoState (i : S.Player) (o : Option (S.Infoset i)) :
    (compileObsCoreModel (S := S) (Outcome := Outcome) t).InfoState i :=
  o

@[simp] theorem currentObs_canonicalCoreInfoState (t : GameTree S Outcome)
    (i : S.Player) (o : Option (S.Infoset i)) :
    (compileObsCoreModel (S := S) (Outcome := Outcome) t).currentObs i
      (canonicalCoreInfoState (S := S) (Outcome := Outcome) (t := t) i o) = o := by
  rfl

/-- Lift a native EFG pure profile to the honest core compilation. -/
noncomputable def liftPureProfileCore (t : GameTree S Outcome) :
    PureProfile S → ObsModelCore.PureProfile (compileObsCoreModel (S := S) (Outcome := Outcome) t)
  | π => fun i v =>
      match v with
      | none => PUnit.unit
      | some I => π i I

/-- Player-local pure strategies for the core compilation are equivalent to native
pure strategies: the `none` observation carries only the trivial action. -/
noncomputable def pureStrategyEquivCoreLocalStrategy
    (t : GameTree S Outcome) (i : S.Player) :
    PureStrategy S i ≃ (compileObsCoreModel (S := S) (Outcome := Outcome) t).LocalStrategy i where
  toFun := fun π v =>
    match v with
    | none => PUnit.unit
    | some I => π I
  invFun := fun π I => π (some I)
  left_inv := by
    intro π
    funext I
    rfl
  right_inv := by
    intro π
    funext v
    cases v <;> rfl

/-- Descend a compiled core pure profile back to a native EFG pure profile. -/
noncomputable def descendPureProfileCore (t : GameTree S Outcome) :
    ObsModelCore.PureProfile (compileObsCoreModel (S := S) (Outcome := Outcome) t) → PureProfile S
  | π => fun i I => π i (some I)

/-- Lift a native mixed profile to the core compilation playerwise. -/
noncomputable def liftMixedProfileCore (t : GameTree S Outcome) (μ : MixedProfile S) :
    ∀ i, PMF ((compileObsCoreModel (S := S) (Outcome := Outcome) t).LocalStrategy i) :=
  fun i => (μ i).map (pureStrategyEquivCoreLocalStrategy (S := S) (Outcome := Outcome) t i).toFun

/-- Lift a native EFG behavioral profile to the honest core compilation. -/
noncomputable def liftBehavioralProfileCore (t : GameTree S Outcome) :
    BehavioralProfile S →
      ObsModelCore.BehavioralProfile (compileObsCoreModel (S := S) (Outcome := Outcome) t)
  | σ => fun i v =>
      match v with
      | none => PMF.pure PUnit.unit
      | some I => σ i I

/-- Descend a compiled core behavioral profile back to a native EFG behavioral profile. -/
noncomputable def descendBehavioralProfileCore (t : GameTree S Outcome) :
    ObsModelCore.BehavioralProfile (compileObsCoreModel (S := S) (Outcome := Outcome) t) →
      BehavioralProfile S
  | β => fun i I => β i (some I)

@[simp] theorem descendPureProfileCore_liftPureProfileCore
    (t : GameTree S Outcome) (π : PureProfile S) :
    descendPureProfileCore (S := S) (Outcome := Outcome) t
      (liftPureProfileCore (S := S) (Outcome := Outcome) t π) = π := by
  funext i I
  simp [descendPureProfileCore, liftPureProfileCore]

@[simp] theorem pureStrategyEquivCoreLocalStrategy_apply_some
    (t : GameTree S Outcome) (i : S.Player) (π : PureStrategy S i) (I : S.Infoset i) :
    pureStrategyEquivCoreLocalStrategy (S := S) (Outcome := Outcome) t i π (some I) = π I := by
  rfl

@[simp] theorem pureStrategyEquivCoreLocalStrategy_apply_none
    (t : GameTree S Outcome) (i : S.Player) (π : PureStrategy S i) :
    pureStrategyEquivCoreLocalStrategy (S := S) (Outcome := Outcome) t i π none = PUnit.unit := by
  rfl

@[simp] theorem descendBehavioralProfileCore_liftBehavioralProfileCore
    (t : GameTree S Outcome) (σ : BehavioralProfile S) :
    descendBehavioralProfileCore (S := S) (Outcome := Outcome) t
      (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ) = σ := by
  funext i I
  simp [descendBehavioralProfileCore, liftBehavioralProfileCore]

@[simp] theorem liftBehavioralProfileCore_descendBehavioralProfileCore
    (t : GameTree S Outcome)
    (β : ObsModelCore.BehavioralProfile (compileObsCoreModel (S := S) (Outcome := Outcome) t)) :
    liftBehavioralProfileCore (S := S) (Outcome := Outcome) t
      (descendBehavioralProfileCore (S := S) (Outcome := Outcome) t β) = β := by
  funext i v
  cases v with
  | none =>
      have hne : β i none PUnit.unit ≠ 0 := by
        rcases (β i none).support_nonempty with ⟨x, hx⟩
        cases x
        simpa using hx
      have hunit : β i none PUnit.unit = 1 := by
        exact ((β i none).apply_eq_one_iff PUnit.unit).2 (by
          ext y
          cases y
          simp [hne])
      ext x
      cases x
      simpa [liftBehavioralProfileCore, descendBehavioralProfileCore] using hunit.symm
  | some I =>
      rfl

/-- A bundled interface for the EFG-to-ObsModel compilation, including the
canonical lift/descent maps between native EFG profiles and compiled profiles. -/
structure ObsCompilation (t : GameTree S Outcome) where
  O : ObsModel S.Player (GameTree S Outcome)
    (fun i => Option (S.Infoset i))
    (CompiledAct S)
  liftPure : PureProfile S → ObsModel.PureProfile O
  descendPure : ObsModel.PureProfile O → PureProfile S
  liftBehavioral : BehavioralProfile S → ObsModel.BehavioralProfile O
  descendBehavioral : ObsModel.BehavioralProfile O → BehavioralProfile S

/-- Canonical information state ending at observation `o` in the compiled model. -/
noncomputable def canonicalInfoState (t : GameTree S Outcome)
    (i : S.Player) (o : Option (S.Infoset i)) :
    (compileObsModel t).InfoState i :=
  ((compileObsModel t).infoState i).start o

@[simp] theorem currentObs_canonicalInfoState (t : GameTree S Outcome)
    (i : S.Player) (o : Option (S.Infoset i)) :
    (compileObsModel t).currentObs i (canonicalInfoState t i o) = o := by
  simpa [canonicalInfoState, ObsModel.currentObs] using
    (((compileObsModel t).infoState i).current_start o)

/-- Native EFG pure actions viewed as compiled actions at a fixed observation. -/
noncomputable def compiledPureAtObs (π : PureProfile S) (i : S.Player)
    (o : Option (S.Infoset i)) : CompiledAct S i o :=
  match o with
  | none => PUnit.unit
  | some I => π i I

/-- Native EFG behavioral actions viewed as compiled action distributions at a
fixed observation. -/
noncomputable def compiledBehavioralAtObs (σ : BehavioralProfile S) (i : S.Player)
    (o : Option (S.Infoset i)) : PMF (CompiledAct S i o) :=
  match o with
  | none => PMF.pure PUnit.unit
  | some I => σ i I

/-- Lift an EFG pure profile to the compiled ObsModel by ignoring extra summary
and using only the current infoset observation. -/
noncomputable def liftPureProfile (t : GameTree S Outcome) :
    PureProfile S → ObsModel.PureProfile (compileObsModel t)
  | π => fun i v =>
      compiledPureAtObs π i ((compileObsModel t).currentObs i v)

@[simp] theorem liftPureProfile_canonicalInfoState_some
    (t : GameTree S Outcome) (π : PureProfile S)
    (i : S.Player) (I : S.Infoset i) :
    liftPureProfile t π i (canonicalInfoState t i (some I)) = π i I := by
  unfold liftPureProfile compiledPureAtObs
  have hlast :
      (compileObsModel t).currentObs i (canonicalInfoState t i (some I)) = some I :=
    currentObs_canonicalInfoState t i (some I)
  cases hlast
  rfl

/-- Descend a compiled pure profile to an EFG pure profile by evaluating it at
the canonical singleton information state for each infoset. -/
noncomputable def descendPureProfile (t : GameTree S Outcome) :
    ObsModel.PureProfile (compileObsModel t) → PureProfile S
  | π => fun i I =>
      let v := canonicalInfoState t i (some I)
      let h : (compileObsModel t).currentObs i v = some I :=
        currentObs_canonicalInfoState t i (some I)
      cast (compiledAct_eq_of_some S i h) (π i v)

/-- Lift an EFG behavioral profile to the compiled ObsModel by ignoring extra
summary and using only the current infoset observation. -/
noncomputable def liftBehavioralProfile (t : GameTree S Outcome) :
    BehavioralProfile S → ObsModel.BehavioralProfile (compileObsModel t)
  | σ => fun i v =>
      compiledBehavioralAtObs σ i ((compileObsModel t).currentObs i v)

@[simp] theorem liftBehavioralProfile_canonicalInfoState_some
    (t : GameTree S Outcome) (σ : BehavioralProfile S)
    (i : S.Player) (I : S.Infoset i) :
    liftBehavioralProfile t σ i (canonicalInfoState t i (some I)) = σ i I := by
  unfold liftBehavioralProfile compiledBehavioralAtObs
  have hlast :
      (compileObsModel t).currentObs i (canonicalInfoState t i (some I)) = some I :=
    currentObs_canonicalInfoState t i (some I)
  cases hlast
  rfl

/-- Descend a compiled behavioral profile to an EFG behavioral profile by
evaluating it at the canonical singleton information state for each infoset. -/
noncomputable def descendBehavioralProfile (t : GameTree S Outcome) :
    ObsModel.BehavioralProfile (compileObsModel t) → BehavioralProfile S
  | β => fun i I =>
      let v := canonicalInfoState t i (some I)
      let h : (compileObsModel t).currentObs i v = some I :=
        currentObs_canonicalInfoState t i (some I)
      cast (congrArg PMF (compiledAct_eq_of_some S i h)) (β i v)

@[simp] theorem descendPureProfile_liftPureProfile (t : GameTree S Outcome)
    (π : PureProfile S) :
    descendPureProfile t (liftPureProfile t π) = π := by
  funext i I
  unfold descendPureProfile
  simp

@[simp] theorem descendBehavioralProfile_liftBehavioralProfile
    (t : GameTree S Outcome) (σ : BehavioralProfile S) :
    descendBehavioralProfile t (liftBehavioralProfile t σ) = σ := by
  funext i I
  unfold descendBehavioralProfile
  simp

/-- The canonical bundled EFG compilation to ObsModel together with the
lift/descent maps used for bridge constructions. -/
noncomputable def obsCompilation (t : GameTree S Outcome) : ObsCompilation t where
  O := compileObsModel t
  liftPure := liftPureProfile t
  descendPure := descendPureProfile t
  liftBehavioral := liftBehavioralProfile t
  descendBehavioral := descendBehavioralProfile t

end GameTheory.EFG
