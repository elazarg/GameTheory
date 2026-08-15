/- # EXP-002 indexed-signature candidate. -/

import GameTheory.Experimental.Phase1.D2.FiniteSupportPMF

noncomputable section

namespace GameTheory.Experimental.Phase1.D1.Indexed

open D2.FiniteSupportPMF

universe uι uκ us ut uo up

/-- Strategy and outcome universes stay independent intentionally; the universe
linter otherwise suggests collapsing them because both occur under one `max`. -/
structure Signature (ι : Type uι) where
  Strategy : ι → Type us
  Outcome : Type uo

-- EXP-002 deliberately tests independent strategy and outcome universes; the
-- declaration docstring records why the linter's proposed collapse is invalid.

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

structure Form {ι : Type uι} (sig : Signature ι) where
  play : Profile sig → Law sig.Outcome

def Signature.reindex {ι : Type uι} {κ : Type uκ} (sig : Signature ι) (e : ι ≃ κ) :
    Signature κ where
  Strategy k := sig.Strategy (e.symm k)
  Outcome := sig.Outcome

def Form.reindex {ι : Type uι} {κ : Type uκ} {sig : Signature ι}
    (F : Form sig) (e : ι ≃ κ) : Form (sig.reindex e) where
  play p := F.play (Equiv.piCongrLeft sig.Strategy e.symm p)

def Signature.mapOutcome {ι : Type uι} (sig : Signature ι) (O : Type up) : Signature ι where
  Strategy := sig.Strategy
  Outcome := O

def Form.mapOutcome {ι : Type uι} {sig : Signature ι} (F : Form sig)
    {O : Type up} (f : sig.Outcome → O) : Form (sig.mapOutcome O) where
  play p := Law.map f (F.play p)

def Signature.product {ι : Type uι} (sig : Signature ι) (τ : Signature ι) : Signature ι where
  Strategy i := sig.Strategy i × τ.Strategy i
  Outcome := sig.Outcome × τ.Outcome

def Form.product {ι : Type uι} {sig τ : Signature ι} (F : Form sig) (G : Form τ) :
    Form (sig.product τ) where
  play p := Law.product (F.play fun i => (p i).1) (G.play fun i => (p i).2)

def Signature.mixed {ι : Type uι} (sig : Signature ι) : Signature ι where
  Strategy i := Law (sig.Strategy i)
  Outcome := sig.Outcome

def Form.mixed {ι : Type uι} [Fintype ι] {sig : Signature ι} (F : Form sig) :
    Form sig.mixed where
  play μ := Law.bind (Law.pi μ) F.play

/-- A heterogeneous signature map whose law square commutes for a form pair. -/
structure Hom {ι : Type uι} {sig τ : Signature ι} (F : Form sig) (G : Form τ) where
  strategy : ∀ i, sig.Strategy i → τ.Strategy i
  outcome : sig.Outcome → τ.Outcome
  commutes : ∀ p, Law.map outcome (F.play p) = G.play fun i => strategy i (p i)

def Hom.id {ι : Type uι} {sig : Signature ι} (F : Form sig) : Hom F F where
  strategy _ := _root_.id
  outcome := _root_.id
  commutes p := by simp

def Hom.comp {ι : Type uι} {σ τ υ : Signature ι}
    {F : Form σ} {G : Form τ} {H : Form υ} (g : Hom G H) (f : Hom F G) : Hom F H where
  strategy i := g.strategy i ∘ f.strategy i
  outcome := g.outcome ∘ f.outcome
  commutes p := by
    change Law.map (g.outcome ∘ f.outcome) (F.play p) =
      H.play fun i => g.strategy i (f.strategy i (p i))
    rw [← g.commutes (fun i => f.strategy i (p i)), ← f.commutes]
    symm
    exact Law.map_comp _ _ _

@[ext]
theorem Hom.ext {ι : Type uι} {σ τ : Signature ι} {F : Form σ} {G : Form τ}
    {f g : Hom F G} (hs : f.strategy = g.strategy) (ho : f.outcome = g.outcome) : f = g := by
  cases f
  cases g
  cases hs
  cases ho
  rfl

@[simp]
theorem Hom.id_comp {ι : Type uι} {σ τ : Signature ι} {F : Form σ} {G : Form τ}
    (f : Hom F G) : (Hom.id G).comp f = f := by
  apply Hom.ext <;> rfl

@[simp]
theorem Hom.comp_id {ι : Type uι} {σ τ : Signature ι} {F : Form σ} {G : Form τ}
    (f : Hom F G) : f.comp (Hom.id F) = f := by
  apply Hom.ext <;> rfl

theorem Hom.comp_assoc {ι : Type uι} {σ τ υ φ : Signature ι}
    {F : Form σ} {G : Form τ} {H : Form υ} {K : Form φ}
    (h : Hom H K) (g : Hom G H) (f : Hom F G) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply Hom.ext <;> rfl

end GameTheory.Experimental.Phase1.D1.Indexed
