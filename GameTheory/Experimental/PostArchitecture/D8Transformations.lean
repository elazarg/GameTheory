/-
# EXP-045: the smallest transformation surface

This file tests concrete player and strategy equivalences against the accepted
`GameForm`, mixed-extension, Nash, and correlated-equilibrium APIs. It is
experiment evidence until D8 is decided; stable code must not import it.
-/

import GameTheory.Core.Mixed

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.D8Transformations

open GameTheory.Math.Probability

universe uι uκ us us' uo

namespace Candidate

/-! ## Player reindexing -/

/-- Reindex the players of a signature along an equivalence. -/
abbrev GameSignature.reindexPlayers {ι : Type uι} {κ : Type uκ}
    (sig : GameTheory.GameSignature ι) (equiv : ι ≃ κ) :
    GameTheory.GameSignature κ where
  Strategy player := sig.Strategy (equiv.symm player)
  Outcome := sig.Outcome

namespace Profile

/-- Send a profile forward along a player equivalence. -/
def reindexPlayers {ι : Type uι} {κ : Type uκ}
    {sig : GameTheory.GameSignature ι} (equiv : ι ≃ κ)
    (profile : GameTheory.Profile sig) :
    GameTheory.Profile (GameSignature.reindexPlayers sig equiv) :=
  Equiv.piCongrLeft' sig.Strategy equiv profile

/-- Read a reindexed profile back in the source coordinates. -/
def unreindexPlayers {ι : Type uι} {κ : Type uκ}
    {sig : GameTheory.GameSignature ι} (equiv : ι ≃ κ)
    (profile : GameTheory.Profile (GameSignature.reindexPlayers sig equiv)) :
    GameTheory.Profile sig :=
  (Equiv.piCongrLeft' sig.Strategy equiv).symm profile

@[simp]
theorem unreindex_reindex {ι : Type uι} {κ : Type uκ}
    {sig : GameTheory.GameSignature ι} (equiv : ι ≃ κ)
    (profile : GameTheory.Profile sig) :
    unreindexPlayers equiv (reindexPlayers equiv profile) = profile := by
  exact (Equiv.piCongrLeft' sig.Strategy equiv).symm_apply_apply profile

@[simp]
theorem reindex_unreindex {ι : Type uι} {κ : Type uκ}
    {sig : GameTheory.GameSignature ι} (equiv : ι ≃ κ)
    (profile : GameTheory.Profile (GameSignature.reindexPlayers sig equiv)) :
    reindexPlayers equiv (unreindexPlayers equiv profile) = profile := by
  exact (Equiv.piCongrLeft' sig.Strategy equiv).apply_symm_apply profile

@[simp]
theorem unreindex_update {ι : Type uι} {κ : Type uκ}
    [DecidableEq ι] [DecidableEq κ]
    {sig : GameTheory.GameSignature ι} (equiv : ι ≃ κ)
    (profile : GameTheory.Profile (GameSignature.reindexPlayers sig equiv))
    (who : κ) (replacement : sig.Strategy (equiv.symm who)) :
    unreindexPlayers equiv
        (GameTheory.Profile.update profile who replacement) =
      GameTheory.Profile.update (unreindexPlayers equiv profile)
        (equiv.symm who) replacement := by
  funext player
  obtain ⟨target, rfl⟩ := equiv.symm.surjective player
  by_cases h : target = who
  · subst target
    simp [unreindexPlayers]
  · simp [unreindexPlayers, h, equiv.symm.injective.ne h]

@[simp]
theorem update_reindex {ι : Type uι} {κ : Type uκ}
    [DecidableEq ι] [DecidableEq κ]
    {sig : GameTheory.GameSignature ι} (equiv : ι ≃ κ)
    (profile : GameTheory.Profile sig) (who : ι)
    (replacement : sig.Strategy who) :
    GameTheory.Profile.update (reindexPlayers equiv profile) (equiv who)
        (reindexPlayers equiv
          (GameTheory.Profile.update profile who replacement) (equiv who)) =
      reindexPlayers equiv
        (GameTheory.Profile.update profile who replacement) := by
  funext target
  by_cases h : target = equiv who
  · subst target
    simp
  · have hsource : equiv.symm target ≠ who := by
      exact fun heq => h (by simpa using congrArg equiv heq)
    simp [reindexPlayers, h, hsource]

end Profile

/-- Reindex a form by reading target profiles in source coordinates. -/
abbrev GameForm.reindexPlayers {ι : Type uι} {κ : Type uκ}
    (F : GameTheory.GameForm ι) (equiv : ι ≃ κ) :
    GameTheory.GameForm κ where
  sig := GameSignature.reindexPlayers F.sig equiv
  play profile := F.play (Profile.unreindexPlayers equiv profile)

@[simp]
theorem GameForm.reindexPlayers_play {ι : Type uι} {κ : Type uκ}
    (F : GameTheory.GameForm ι) (equiv : ι ≃ κ)
    (profile : GameTheory.Profile (GameSignature.reindexPlayers F.sig equiv)) :
    (GameForm.reindexPlayers F equiv).play profile =
      F.play (Profile.unreindexPlayers equiv profile) :=
  rfl

/-- Reindex the owners of a preference family. -/
def Preference.reindexPlayers {ι : Type uι} {κ : Type uκ} {Outcome : Type uo}
    (equiv : ι ≃ κ) (weaklyPrefers : GameTheory.WeakPreference ι Outcome) :
    GameTheory.WeakPreference κ Outcome :=
  fun player => weaklyPrefers (equiv.symm player)

/-- Nash equilibrium is invariant under an invertible player reindexing. -/
theorem isNash_reindexPlayers {ι : Type uι} {κ : Type uκ}
    [DecidableEq ι] [DecidableEq κ]
    (F : GameTheory.GameForm ι)
    (weaklyPrefers : GameTheory.WeakPreference ι F.sig.Outcome)
    (equiv : ι ≃ κ) (profile : GameTheory.Profile F.sig) :
    GameTheory.IsNash (GameForm.reindexPlayers F equiv)
        (Preference.reindexPlayers equiv weaklyPrefers)
        (Profile.reindexPlayers equiv profile) ↔
      GameTheory.IsNash F weaklyPrefers profile := by
  rw [GameTheory.isNash_iff, GameTheory.isNash_iff]
  constructor
  · intro h who replacement
    let targetProfile :=
      Profile.reindexPlayers equiv
        (GameTheory.Profile.update profile who replacement)
    have htarget := h (equiv who) (targetProfile (equiv who))
    rw [Profile.update_reindex] at htarget
    simpa [targetProfile, Preference.reindexPlayers] using htarget
  · intro h who replacement
    let sourceReplacement :=
      (Profile.unreindexPlayers equiv
        (GameTheory.Profile.update
          (Profile.reindexPlayers equiv profile) who replacement))
        (equiv.symm who)
    have hsource := h (equiv.symm who) sourceReplacement
    simpa [sourceReplacement, Preference.reindexPlayers] using hsource

/-! ## Strategy relabeling -/

/-- Replace every strategy carrier, keeping players and outcomes fixed. -/
abbrev GameSignature.relabelStrategies {ι : Type uι}
    (sig : GameTheory.GameSignature.{uι, us, uo} ι)
    (Strategy : ι → Type us') : GameTheory.GameSignature ι where
  Strategy := Strategy
  Outcome := sig.Outcome

namespace Profile

/-- Relabel every coordinate of a profile. -/
def relabelStrategies {ι : Type uι}
    {sig : GameTheory.GameSignature.{uι, us, uo} ι}
    {Strategy : ι → Type us'}
    (equiv : ∀ player, sig.Strategy player ≃ Strategy player)
    (profile : GameTheory.Profile sig) :
    GameTheory.Profile (GameSignature.relabelStrategies sig Strategy) :=
  fun player => equiv player (profile player)

/-- Read a relabeled profile in the source strategy carriers. -/
def unrelabelStrategies {ι : Type uι}
    {sig : GameTheory.GameSignature.{uι, us, uo} ι}
    {Strategy : ι → Type us'}
    (equiv : ∀ player, sig.Strategy player ≃ Strategy player)
    (profile : GameTheory.Profile (GameSignature.relabelStrategies sig Strategy)) :
    GameTheory.Profile sig :=
  fun player => (equiv player).symm (profile player)

@[simp]
theorem unrelabel_relabel {ι : Type uι}
    {sig : GameTheory.GameSignature.{uι, us, uo} ι}
    {Strategy : ι → Type us'}
    (equiv : ∀ player, sig.Strategy player ≃ Strategy player)
    (profile : GameTheory.Profile sig) :
    unrelabelStrategies equiv (relabelStrategies equiv profile) = profile := by
  funext player
  simp [unrelabelStrategies, relabelStrategies]

@[simp]
theorem relabel_unrelabel {ι : Type uι}
    {sig : GameTheory.GameSignature.{uι, us, uo} ι}
    {Strategy : ι → Type us'}
    (equiv : ∀ player, sig.Strategy player ≃ Strategy player)
    (profile : GameTheory.Profile (GameSignature.relabelStrategies sig Strategy)) :
    relabelStrategies equiv (unrelabelStrategies equiv profile) = profile := by
  funext player
  simp [unrelabelStrategies, relabelStrategies]

@[simp]
theorem unrelabel_update {ι : Type uι} [DecidableEq ι]
    {sig : GameTheory.GameSignature.{uι, us, uo} ι}
    {Strategy : ι → Type us'}
    (equiv : ∀ player, sig.Strategy player ≃ Strategy player)
    (profile : GameTheory.Profile (GameSignature.relabelStrategies sig Strategy))
    (who : ι) (replacement : Strategy who) :
    unrelabelStrategies equiv
        (GameTheory.Profile.update profile who replacement) =
      GameTheory.Profile.update (unrelabelStrategies equiv profile) who
        ((equiv who).symm replacement) := by
  funext player
  by_cases h : player = who
  · subst player
    simp [unrelabelStrategies]
  · simp [unrelabelStrategies, h]

end Profile

/-- Relabel a form's strategies by evaluating through inverse relabeling. -/
abbrev GameForm.relabelStrategies {ι : Type uι}
    (F : GameTheory.GameForm ι) {Strategy : ι → Type us'}
    (equiv : ∀ player, F.sig.Strategy player ≃ Strategy player) :
    GameTheory.GameForm ι where
  sig := GameSignature.relabelStrategies F.sig Strategy
  play profile := F.play (Profile.unrelabelStrategies equiv profile)

@[simp]
theorem GameForm.relabelStrategies_play {ι : Type uι}
    (F : GameTheory.GameForm ι) {Strategy : ι → Type us'}
    (equiv : ∀ player, F.sig.Strategy player ≃ Strategy player)
    (profile : GameTheory.Profile
      (GameSignature.relabelStrategies F.sig Strategy)) :
    (GameForm.relabelStrategies F equiv).play profile =
      F.play (Profile.unrelabelStrategies equiv profile) :=
  rfl

/-- Nash equilibrium is invariant under invertible strategy relabeling. -/
theorem isNash_relabelStrategies {ι : Type uι} [DecidableEq ι]
    (F : GameTheory.GameForm ι)
    (weaklyPrefers : GameTheory.WeakPreference ι F.sig.Outcome)
    {Strategy : ι → Type us'}
    (equiv : ∀ player, F.sig.Strategy player ≃ Strategy player)
    (profile : GameTheory.Profile F.sig) :
    GameTheory.IsNash (GameForm.relabelStrategies F equiv) weaklyPrefers
        (Profile.relabelStrategies equiv profile) ↔
      GameTheory.IsNash F weaklyPrefers profile := by
  rw [GameTheory.isNash_iff, GameTheory.isNash_iff]
  constructor
  · intro h who replacement
    simpa using h who (equiv who replacement)
  · intro h who replacement
    simpa using h who ((equiv who).symm replacement)

/-! ## Correlated-equilibrium transport -/

/-- Correlated equilibrium is invariant under invertible strategy relabeling.
The response map is conjugated by the coordinate equivalence, so every target
deviation is reflected to a source deviation and conversely. -/
theorem isCorrelatedEq_relabelStrategies {ι : Type uι} [DecidableEq ι]
    (F : GameTheory.GameForm ι)
    (weaklyPrefers : GameTheory.WeakPreference ι F.sig.Outcome)
    {Strategy : ι → Type us'}
    (equiv : ∀ player, F.sig.Strategy player ≃ Strategy player)
    (statusQuo : FinDist (GameTheory.Profile F.sig)) :
    GameTheory.IsCorrelatedEq (GameForm.relabelStrategies F equiv)
        weaklyPrefers
        (statusQuo.map (Profile.relabelStrategies equiv)) ↔
      GameTheory.IsCorrelatedEq F weaklyPrefers statusQuo := by
  rw [GameTheory.isCorrelatedEq_iff, GameTheory.isCorrelatedEq_iff]
  constructor
  · intro h who respond
    let targetRespond : Strategy who → Strategy who :=
      fun recommendation =>
        equiv who (respond ((equiv who).symm recommendation))
    have htarget := h who targetRespond
    simpa [targetRespond, GameTheory.GameForm.outcomeLaw,
      Profile.relabelStrategies] using htarget
  · intro h who respond
    let sourceRespond : F.sig.Strategy who → F.sig.Strategy who :=
      fun recommendation =>
        (equiv who).symm (respond (equiv who recommendation))
    have hsource := h who sourceRespond
    simpa [sourceRespond, GameTheory.GameForm.outcomeLaw,
      Profile.relabelStrategies] using hsource

/-! ## Mixed lifting -/

private theorem finDist_pi_unreindex {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] (A : ι → Type us) (equiv : ι ≃ κ)
    (laws : (target : κ) → FinDist (A (equiv.symm target))) :
    FinDist.map (Equiv.piCongrLeft' A equiv).symm (FinDist.pi laws) =
      FinDist.pi
        ((Equiv.piCongrLeft' (fun player => FinDist (A player)) equiv).symm laws) := by
  classical
  let profileEquiv := Equiv.piCongrLeft' A equiv
  let lawEquiv :=
    Equiv.piCongrLeft' (fun player => FinDist (A player)) equiv
  apply FinDist.ext_of_prob
  intro source
  have htarget :
      source = profileEquiv.symm (profileEquiv source) :=
    (profileEquiv.symm_apply_apply source).symm
  conv_lhs => rw [htarget]
  rw [FinDist.prob_map_of_injective profileEquiv.symm
      profileEquiv.symm.injective,
    FinDist.prob_pi, FinDist.prob_pi,
    ← equiv.prod_comp
      (g := fun target => (laws target).prob (profileEquiv source target))]
  apply Finset.prod_congr rfl
  intro player _
  obtain ⟨target, rfl⟩ := equiv.symm.surjective player
  simp [profileEquiv]
  rw [equiv.apply_symm_apply target]

/-- The forward orientation needed by the existing MAID serialization
consumer follows from the inverse orientation without another probability
argument. -/
private theorem finDist_pi_reindex {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] (A : ι → Type us) (equiv : ι ≃ κ)
    (laws : (source : ι) → FinDist (A source)) :
    FinDist.map (Equiv.piCongrLeft' A equiv) (FinDist.pi laws) =
      FinDist.pi
        (Equiv.piCongrLeft' (fun player => FinDist (A player)) equiv laws) := by
  let profileEquiv := Equiv.piCongrLeft' A equiv
  let lawEquiv :=
    Equiv.piCongrLeft' (fun player => FinDist (A player)) equiv
  have hinverse :
      FinDist.map profileEquiv.symm (FinDist.pi (lawEquiv laws)) =
        FinDist.pi laws := by
    simpa [profileEquiv, lawEquiv] using
      finDist_pi_unreindex A equiv (lawEquiv laws)
  rw [← hinverse, FinDist.map_comp]
  convert FinDist.map_id (FinDist.pi (lawEquiv laws)) using 1
  apply congrArg (fun relabel =>
    FinDist.map relabel (FinDist.pi (lawEquiv laws)))
  funext target
  exact profileEquiv.apply_symm_apply target

set_option maxHeartbeats 800000 in
/-- Player reindexing commutes with the independent mixed extension at the
actual play law. -/
theorem mixed_reindexPlayers_play {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ]
    (F : GameTheory.GameForm ι) (equiv : ι ≃ κ)
    (profile : GameTheory.Profile
      (GameSignature.reindexPlayers F.sig equiv).mixed) :
    (GameForm.reindexPlayers F.mixed equiv).play profile =
      (GameForm.reindexPlayers F equiv).mixed.play profile := by
  show
    (FinDist.pi
      (Profile.unreindexPlayers (sig := F.sig.mixed) equiv profile)).bind F.play =
      (FinDist.pi profile).bind
        (fun source =>
          F.play (Profile.unreindexPlayers (sig := F.sig) equiv source))
  have hunreindexLaws :
      Profile.unreindexPlayers (sig := F.sig.mixed) equiv profile =
        (Equiv.piCongrLeft'
          (fun player => FinDist (F.sig.Strategy player)) equiv).symm profile :=
    rfl
  have hunreindexProfiles :
      Profile.unreindexPlayers (sig := F.sig) equiv =
        (Equiv.piCongrLeft' F.sig.Strategy equiv).symm :=
    rfl
  rw [hunreindexLaws, hunreindexProfiles]
  rw [← finDist_pi_unreindex F.sig.Strategy equiv profile, FinDist.bind_map]

/-! ## Hostile instantiations

The player swap is deliberately heterogeneous: one coordinate uses `Bool` and
the other `Fin 3`. A constant-family toy would not exercise the dependent
transport hidden by `Equiv.piCongrLeft'`.
-/

namespace Hostile

abbrev HeterogeneousStrategy : Bool → Type
  | false => Bool
  | true => Fin 3

abbrev heterogeneousSignature : GameTheory.GameSignature Bool where
  Strategy := HeterogeneousStrategy
  Outcome := Unit

def heterogeneousForm : GameTheory.GameForm Bool where
  sig := heterogeneousSignature
  play _ := FinDist.pure ()

def playerSwap : Bool ≃ Bool :=
  Equiv.swap false true

def heterogeneousProfile : GameTheory.Profile heterogeneousSignature
  | false => false
  | true => 0

def heterogeneousMixedProfile :
    GameTheory.Profile
      (GameSignature.reindexPlayers heterogeneousSignature playerSwap).mixed :=
  Profile.reindexPlayers playerSwap
    (heterogeneousForm.purify heterogeneousProfile)

/-- The mixed lifting theorem survives an actual swap of unequal strategy
carriers. -/
theorem heterogeneous_mixed_lifting :
    (GameForm.reindexPlayers heterogeneousForm.mixed playerSwap).play
        heterogeneousMixedProfile =
      (GameForm.reindexPlayers heterogeneousForm playerSwap).mixed.play
        heterogeneousMixedProfile :=
  mixed_reindexPlayers_play heterogeneousForm playerSwap
    heterogeneousMixedProfile

/-- Nash transport also survives the heterogeneous player swap. -/
theorem heterogeneous_nash_transport
    (weaklyPrefers :
      GameTheory.WeakPreference Bool heterogeneousSignature.Outcome) :
    GameTheory.IsNash
        (GameForm.reindexPlayers heterogeneousForm playerSwap)
        (Preference.reindexPlayers playerSwap weaklyPrefers)
        (Profile.reindexPlayers playerSwap heterogeneousProfile) ↔
      GameTheory.IsNash heterogeneousForm weaklyPrefers
        heterogeneousProfile :=
  isNash_reindexPlayers heterogeneousForm weaklyPrefers playerSwap
    heterogeneousProfile

abbrev boolSignature : GameTheory.GameSignature Bool where
  Strategy _ := Bool
  Outcome := Unit

def boolForm : GameTheory.GameForm Bool where
  sig := boolSignature
  play _ := FinDist.pure ()

def strategyFlip (_ : Bool) : Bool ≃ Bool :=
  Equiv.swap false true

/-- The strategy equivalence is genuinely nonidentity at both coordinates. -/
theorem strategyFlip_false (player : Bool) :
    strategyFlip player false = true := by
  simp [strategyFlip]

/-- Correlated-equilibrium transport conjugates a nonidentity response space;
it is not merely a carrier-renaming statement. -/
theorem flipped_correlated_transport
    (weaklyPrefers : GameTheory.WeakPreference Bool Unit)
    (statusQuo : FinDist (GameTheory.Profile boolSignature)) :
    GameTheory.IsCorrelatedEq
        (GameForm.relabelStrategies boolForm strategyFlip)
        weaklyPrefers
        (statusQuo.map (Profile.relabelStrategies strategyFlip)) ↔
      GameTheory.IsCorrelatedEq boolForm weaklyPrefers statusQuo :=
  isCorrelatedEq_relabelStrategies boolForm weaklyPrefers strategyFlip
    statusQuo

end Hostile

end Candidate

end GameTheory.Experimental.PostArchitecture.D8Transformations
