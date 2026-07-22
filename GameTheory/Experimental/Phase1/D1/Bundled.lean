/- # EXP-002 bundled-signature candidate. -/

import GameTheory.Experimental.Phase1.D1.Indexed

noncomputable section

namespace GameTheory.Experimental.Phase1.D1.Bundled

open D2.FiniteSupportPMF

set_option linter.checkUnivs false

universe uι uκ us uo up

structure Signature (ι : Type uι) where
  Strategy : ι → Type us
  Outcome : Type uo

abbrev Profile {ι : Type uι} (sig : Signature ι) := ∀ i, sig.Strategy i

namespace Profile

def update {ι : Type uι} {sig : Signature ι} [DecidableEq ι]
    (p : Profile sig) (i : ι) (s : sig.Strategy i) : Profile sig :=
  fun j => if h : j = i then h ▸ s else p j

@[simp]
theorem update_same {ι : Type uι} {sig : Signature ι} [DecidableEq ι]
    (p : Profile sig) (i : ι) (s : sig.Strategy i) : update p i s i = s := by
  simp [update]

@[simp]
theorem update_of_ne {ι : Type uι} {sig : Signature ι} [DecidableEq ι]
    (p : Profile sig) {i j : ι} (s : sig.Strategy i) (h : j ≠ i) :
    update p i s j = p j := by
  simp [update, h]

end Profile

/-- Candidate B stores the signature as a form field. -/
structure Form (ι : Type uι) where
  sig : Signature.{uι, us, uo} ι
  play : Profile sig → Law sig.Outcome

def Signature.reindex {ι : Type uι} {κ : Type uκ} (sig : Signature ι) (e : ι ≃ κ) :
    Signature κ where
  Strategy k := sig.Strategy (e.symm k)
  Outcome := sig.Outcome

def Form.reindex {ι : Type uι} {κ : Type uκ} (F : Form ι) (e : ι ≃ κ) : Form κ where
  sig := F.sig.reindex e
  play p := F.play (Equiv.piCongrLeft F.sig.Strategy e.symm p)

def Signature.mapOutcome {ι : Type uι} (sig : Signature ι) (O : Type up) : Signature ι where
  Strategy := sig.Strategy
  Outcome := O

def Form.mapOutcome {ι : Type uι} (F : Form ι) {O : Type up}
    (f : F.sig.Outcome → O) : Form ι where
  sig := F.sig.mapOutcome O
  play p := Law.map f (F.play p)

def Signature.product {ι : Type uι} (sig τ : Signature ι) : Signature ι where
  Strategy i := sig.Strategy i × τ.Strategy i
  Outcome := sig.Outcome × τ.Outcome

def Form.product {ι : Type uι} (F G : Form ι) : Form ι where
  sig := F.sig.product G.sig
  play p := Law.product (F.play fun i => (p i).1) (G.play fun i => (p i).2)

def Signature.mixed {ι : Type uι} (sig : Signature ι) : Signature ι where
  Strategy i := Law (sig.Strategy i)
  Outcome := sig.Outcome

def Form.mixed {ι : Type uι} [Fintype ι] (F : Form ι) : Form ι where
  sig := F.sig.mixed
  play μ := Law.bind (Law.pi μ) F.play

structure Hom {ι : Type uι} (F G : Form ι) where
  strategy : ∀ i, F.sig.Strategy i → G.sig.Strategy i
  outcome : F.sig.Outcome → G.sig.Outcome
  commutes : ∀ p, Law.map outcome (F.play p) = G.play fun i => strategy i (p i)

def Hom.id {ι : Type uι} (F : Form ι) : Hom F F where
  strategy _ := _root_.id
  outcome := _root_.id
  commutes p := by simp

def Hom.comp {ι : Type uι} {F G H : Form ι} (g : Hom G H) (f : Hom F G) : Hom F H where
  strategy i := g.strategy i ∘ f.strategy i
  outcome := g.outcome ∘ f.outcome
  commutes p := by
    change Law.map (g.outcome ∘ f.outcome) (F.play p) =
      H.play fun i => g.strategy i (f.strategy i (p i))
    rw [← g.commutes (fun i => f.strategy i (p i)), ← f.commutes]
    symm
    exact Law.map_comp _ _ _

@[ext]
theorem Hom.ext {ι : Type uι} {F G : Form ι} {f g : Hom F G}
    (hs : f.strategy = g.strategy) (ho : f.outcome = g.outcome) : f = g := by
  cases f
  cases g
  cases hs
  cases ho
  rfl

@[simp]
theorem Hom.id_comp {ι : Type uι} {F G : Form ι} (f : Hom F G) :
    (Hom.id G).comp f = f := by
  apply Hom.ext <;> rfl

@[simp]
theorem Hom.comp_id {ι : Type uι} {F G : Form ι} (f : Hom F G) :
    f.comp (Hom.id F) = f := by
  apply Hom.ext <;> rfl

theorem Hom.comp_assoc {ι : Type uι} {F G H K : Form ι}
    (h : Hom H K) (g : Hom G H) (f : Hom F G) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply Hom.ext <;> rfl

end GameTheory.Experimental.Phase1.D1.Bundled
