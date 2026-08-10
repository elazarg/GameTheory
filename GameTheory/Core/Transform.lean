/-
# Concrete game-form transformations

The public transformation surface is intentionally concrete. Outcome
relabeling has an explicit Nash/CCE/CE pullback square. Player
reindexing and per-player strategy equivalence are invertible profile
operations.  The current laws cover Nash for both, correlated equilibrium for
strategy relabeling, and mixed-play commutation for player reindexing; the
remaining product-law squares are not inferred.
No generic morphism or certificate hierarchy is introduced.
-/

import GameTheory.Core.Mixed

noncomputable section

namespace GameTheory

open Probability

universe uι uκ us us' uo

/-! ## Outcome relabeling -/

/-- Relabeling outcomes and pulling the preference back along the same map
preserves Nash equilibrium for an arbitrary weak preference. -/
theorem isNash_mapOutcome_comap {ι : Type uι} [DecidableEq ι]
    (F : GameForm ι) {Outcome' : Type*}
    (relabel : F.sig.Outcome → Outcome')
    (weaklyPrefers : WeakPreference ι Outcome')
    (profile : Profile F.sig) :
    IsNash (F.mapOutcome relabel) weaklyPrefers profile ↔
      IsNash F (Preference.comapOutcome relabel weaklyPrefers) profile := by
  rw [isNash_iff, isNash_iff]
  rfl

/-- The same outcome/preference pullback preserves coarse correlated
equilibrium without changing the profile law. -/
theorem isCoarseCorrelatedEq_mapOutcome_comap
    {ι : Type uι} [DecidableEq ι]
    (F : GameForm ι) {Outcome' : Type*}
    (relabel : F.sig.Outcome → Outcome')
    (weaklyPrefers : WeakPreference ι Outcome')
    (statusQuo : FinDist (Profile F.sig)) :
    IsCoarseCorrelatedEq (F.mapOutcome relabel) weaklyPrefers statusQuo ↔
      IsCoarseCorrelatedEq F
        (Preference.comapOutcome relabel weaklyPrefers) statusQuo := by
  rw [isCoarseCorrelatedEq_iff, isCoarseCorrelatedEq_iff]
  simp only [Preference.comapOutcome_apply,
    GameForm.outcomeLaw_mapOutcome, FinDist.map_bind]
  rfl

/-- The same outcome/preference pullback preserves correlated equilibrium. -/
theorem isCorrelatedEq_mapOutcome_comap
    {ι : Type uι} [DecidableEq ι]
    (F : GameForm ι) {Outcome' : Type*}
    (relabel : F.sig.Outcome → Outcome')
    (weaklyPrefers : WeakPreference ι Outcome')
    (statusQuo : FinDist (Profile F.sig)) :
    IsCorrelatedEq (F.mapOutcome relabel) weaklyPrefers statusQuo ↔
      IsCorrelatedEq F
        (Preference.comapOutcome relabel weaklyPrefers) statusQuo := by
  rw [isCorrelatedEq_iff, isCorrelatedEq_iff]
  simp only [Preference.comapOutcome_apply,
    GameForm.outcomeLaw_mapOutcome, FinDist.map_bind]
  rfl

/-! ## Player reindexing -/

/-- Reindex the players of a signature along an equivalence. -/
abbrev GameSignature.reindexPlayers {ι : Type uι} {κ : Type uκ}
    (sig : GameSignature ι) (equiv : ι ≃ κ) : GameSignature κ where
  Strategy player := sig.Strategy (equiv.symm player)
  Outcome := sig.Outcome

namespace Profile

/-- Send a profile forward along a player equivalence. -/
def reindexPlayers {ι : Type uι} {κ : Type uκ}
    {sig : GameSignature ι} (equiv : ι ≃ κ)
    (profile : Profile sig) : Profile (sig.reindexPlayers equiv) :=
  Equiv.piCongrLeft' sig.Strategy equiv profile

/-- Read a reindexed profile back in the source coordinates. -/
def unreindexPlayers {ι : Type uι} {κ : Type uκ}
    {sig : GameSignature ι} (equiv : ι ≃ κ)
    (profile : Profile (sig.reindexPlayers equiv)) : Profile sig :=
  (Equiv.piCongrLeft' sig.Strategy equiv).symm profile

@[simp]
theorem unreindex_reindex {ι : Type uι} {κ : Type uκ}
    {sig : GameSignature ι} (equiv : ι ≃ κ) (profile : Profile sig) :
    unreindexPlayers equiv (reindexPlayers equiv profile) = profile :=
  (Equiv.piCongrLeft' sig.Strategy equiv).symm_apply_apply profile

@[simp]
theorem reindex_unreindex {ι : Type uι} {κ : Type uκ}
    {sig : GameSignature ι} (equiv : ι ≃ κ)
    (profile : Profile (sig.reindexPlayers equiv)) :
    reindexPlayers equiv (unreindexPlayers equiv profile) = profile :=
  (Equiv.piCongrLeft' sig.Strategy equiv).apply_symm_apply profile

@[simp]
theorem unreindex_update {ι : Type uι} {κ : Type uκ}
    [DecidableEq ι] [DecidableEq κ]
    {sig : GameSignature ι} (equiv : ι ≃ κ)
    (profile : Profile (sig.reindexPlayers equiv))
    (who : κ) (replacement : sig.Strategy (equiv.symm who)) :
    unreindexPlayers equiv (Profile.update profile who replacement) =
      Profile.update (unreindexPlayers equiv profile)
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
    {sig : GameSignature ι} (equiv : ι ≃ κ)
    (profile : Profile sig) (who : ι) (replacement : sig.Strategy who) :
    Profile.update (reindexPlayers equiv profile) (equiv who)
        (reindexPlayers equiv
          (Profile.update profile who replacement) (equiv who)) =
      reindexPlayers equiv (Profile.update profile who replacement) := by
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
    (F : GameForm ι) (equiv : ι ≃ κ) : GameForm κ where
  sig := F.sig.reindexPlayers equiv
  play profile := F.play (Profile.unreindexPlayers equiv profile)

@[simp]
theorem GameForm.reindexPlayers_play {ι : Type uι} {κ : Type uκ}
    (F : GameForm ι) (equiv : ι ≃ κ)
    (profile : Profile (F.sig.reindexPlayers equiv)) :
    (F.reindexPlayers equiv).play profile =
      F.play (Profile.unreindexPlayers equiv profile) :=
  rfl

/-- Reindex the owners of a preference family. -/
def Preference.reindexPlayers {ι : Type uι} {κ : Type uκ}
    {Outcome : Type uo} (equiv : ι ≃ κ)
    (weaklyPrefers : WeakPreference ι Outcome) : WeakPreference κ Outcome :=
  fun player => weaklyPrefers (equiv.symm player)

/-- Nash equilibrium is invariant under an invertible player reindexing. -/
theorem isNash_reindexPlayers {ι : Type uι} {κ : Type uκ}
    [DecidableEq ι] [DecidableEq κ]
    (F : GameForm ι) (weaklyPrefers : WeakPreference ι F.sig.Outcome)
    (equiv : ι ≃ κ) (profile : Profile F.sig) :
    IsNash (F.reindexPlayers equiv)
        (Preference.reindexPlayers equiv weaklyPrefers)
        (Profile.reindexPlayers equiv profile) ↔
      IsNash F weaklyPrefers profile := by
  rw [isNash_iff, isNash_iff]
  constructor
  · intro h who replacement
    let targetProfile :=
      Profile.reindexPlayers equiv (Profile.update profile who replacement)
    have htarget := h (equiv who) (targetProfile (equiv who))
    rw [Profile.update_reindex] at htarget
    simpa [targetProfile, Preference.reindexPlayers] using htarget
  · intro h who replacement
    let sourceReplacement :=
      (Profile.unreindexPlayers equiv
        (Profile.update (Profile.reindexPlayers equiv profile) who replacement))
        (equiv.symm who)
    have hsource := h (equiv.symm who) sourceReplacement
    simpa [sourceReplacement, Preference.reindexPlayers] using hsource

/-! ## Strategy relabeling -/

/-- Replace every strategy carrier, keeping players and outcomes fixed. -/
abbrev GameSignature.relabelStrategies {ι : Type uι}
    (sig : GameSignature.{uι, us, uo} ι)
    (Strategy : ι → Type us') : GameSignature ι where
  Strategy := Strategy
  Outcome := sig.Outcome

namespace Profile

/-- Relabel every coordinate of a profile. -/
def relabelStrategies {ι : Type uι}
    {sig : GameSignature.{uι, us, uo} ι} {Strategy : ι → Type us'}
    (equiv : ∀ player, sig.Strategy player ≃ Strategy player)
    (profile : Profile sig) : Profile (sig.relabelStrategies Strategy) :=
  fun player => equiv player (profile player)

/-- Read a relabeled profile in the source strategy carriers. -/
def unrelabelStrategies {ι : Type uι}
    {sig : GameSignature.{uι, us, uo} ι} {Strategy : ι → Type us'}
    (equiv : ∀ player, sig.Strategy player ≃ Strategy player)
    (profile : Profile (sig.relabelStrategies Strategy)) : Profile sig :=
  fun player => (equiv player).symm (profile player)

@[simp]
theorem unrelabel_relabel {ι : Type uι}
    {sig : GameSignature.{uι, us, uo} ι} {Strategy : ι → Type us'}
    (equiv : ∀ player, sig.Strategy player ≃ Strategy player)
    (profile : Profile sig) :
    unrelabelStrategies equiv (relabelStrategies equiv profile) = profile := by
  funext player
  simp [unrelabelStrategies, relabelStrategies]

@[simp]
theorem relabel_unrelabel {ι : Type uι}
    {sig : GameSignature.{uι, us, uo} ι} {Strategy : ι → Type us'}
    (equiv : ∀ player, sig.Strategy player ≃ Strategy player)
    (profile : Profile (sig.relabelStrategies Strategy)) :
    relabelStrategies equiv (unrelabelStrategies equiv profile) = profile := by
  funext player
  simp [unrelabelStrategies, relabelStrategies]

@[simp]
theorem unrelabel_update {ι : Type uι} [DecidableEq ι]
    {sig : GameSignature.{uι, us, uo} ι} {Strategy : ι → Type us'}
    (equiv : ∀ player, sig.Strategy player ≃ Strategy player)
    (profile : Profile (sig.relabelStrategies Strategy))
    (who : ι) (replacement : Strategy who) :
    unrelabelStrategies equiv (Profile.update profile who replacement) =
      Profile.update (unrelabelStrategies equiv profile) who
        ((equiv who).symm replacement) := by
  funext player
  by_cases h : player = who
  · subst player
    simp [unrelabelStrategies]
  · simp [unrelabelStrategies, h]

end Profile

/-- Relabel a form's strategies by evaluating through inverse relabeling. -/
abbrev GameForm.relabelStrategies {ι : Type uι}
    (F : GameForm ι) {Strategy : ι → Type us'}
    (equiv : ∀ player, F.sig.Strategy player ≃ Strategy player) : GameForm ι where
  sig := F.sig.relabelStrategies Strategy
  play profile := F.play (Profile.unrelabelStrategies equiv profile)

@[simp]
theorem GameForm.relabelStrategies_play {ι : Type uι}
    (F : GameForm ι) {Strategy : ι → Type us'}
    (equiv : ∀ player, F.sig.Strategy player ≃ Strategy player)
    (profile : Profile (F.sig.relabelStrategies Strategy)) :
    (F.relabelStrategies equiv).play profile =
      F.play (Profile.unrelabelStrategies equiv profile) :=
  rfl

/-- Nash equilibrium is invariant under invertible strategy relabeling. -/
theorem isNash_relabelStrategies {ι : Type uι} [DecidableEq ι]
    (F : GameForm ι) (weaklyPrefers : WeakPreference ι F.sig.Outcome)
    {Strategy : ι → Type us'}
    (equiv : ∀ player, F.sig.Strategy player ≃ Strategy player)
    (profile : Profile F.sig) :
    IsNash (F.relabelStrategies equiv) weaklyPrefers
        (Profile.relabelStrategies equiv profile) ↔
      IsNash F weaklyPrefers profile := by
  rw [isNash_iff, isNash_iff]
  constructor
  · intro h who replacement
    simpa using h who (equiv who replacement)
  · intro h who replacement
    simpa using h who ((equiv who).symm replacement)

/-- Correlated equilibrium is invariant under invertible strategy relabeling.
The response map is conjugated by the coordinate equivalence, so every target
deviation is reflected to a source deviation and conversely. -/
theorem isCorrelatedEq_relabelStrategies {ι : Type uι} [DecidableEq ι]
    (F : GameForm ι) (weaklyPrefers : WeakPreference ι F.sig.Outcome)
    {Strategy : ι → Type us'}
    (equiv : ∀ player, F.sig.Strategy player ≃ Strategy player)
    (statusQuo : FinDist (Profile F.sig)) :
    IsCorrelatedEq (F.relabelStrategies equiv) weaklyPrefers
        (statusQuo.map (Profile.relabelStrategies equiv)) ↔
      IsCorrelatedEq F weaklyPrefers statusQuo := by
  rw [isCorrelatedEq_iff, isCorrelatedEq_iff]
  constructor
  · intro h who respond
    let targetRespond : Strategy who → Strategy who :=
      fun recommendation =>
        equiv who (respond ((equiv who).symm recommendation))
    have htarget := h who targetRespond
    simpa [targetRespond, GameForm.outcomeLaw,
      Profile.relabelStrategies] using htarget
  · intro h who respond
    let sourceRespond : F.sig.Strategy who → F.sig.Strategy who :=
      fun recommendation =>
        (equiv who).symm (respond (equiv who recommendation))
    have hsource := h who sourceRespond
    simpa [sourceRespond, GameForm.outcomeLaw,
      Profile.relabelStrategies] using hsource

set_option maxHeartbeats 800000 in
/-- Player reindexing commutes with the independent mixed extension at the
actual play law. -/
theorem mixed_reindexPlayers_play {ι : Type uι} {κ : Type uκ}
    [Fintype ι] [Fintype κ] (F : GameForm ι) (equiv : ι ≃ κ)
    (profile : Profile (F.sig.reindexPlayers equiv).mixed) :
    (F.mixed.reindexPlayers equiv).play profile =
      (F.reindexPlayers equiv).mixed.play profile := by
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
  rw [← FinDist.pi_unreindex F.sig.Strategy equiv profile, FinDist.bind_map]

end GameTheory
