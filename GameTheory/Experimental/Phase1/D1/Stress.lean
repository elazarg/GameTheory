/- # EXP-002 downstream signature and composition stress. -/

import GameTheory.Experimental.Phase1.D1.Bundled

noncomputable section

namespace GameTheory.Experimental.Phase1.D1.Stress

namespace I

open Indexed
open D2.FiniteSupportPMF

/-- Two distinct laws reuse one signature, profile, update operation, and result type. -/
def pairedPlay {ι : Type*} {sig : Signature ι} (F G : Form sig) (p : Profile sig) :
    Law sig.Outcome × Law sig.Outcome := (F.play p, G.play p)

structure ToyLanguage {ι : Type*} (sig : Signature ι) where
  eval : Profile sig → sig.Outcome

def ToyLanguage.compile {ι : Type*} {sig : Signature ι} (L : ToyLanguage sig) : Form sig where
  play p := Law.pure (L.eval p)

def ToyLanguage.reindex {ι κ : Type*} {sig : Signature ι}
    (L : ToyLanguage sig) (e : ι ≃ κ) : ToyLanguage (sig.reindex e) where
  eval p := L.eval (Equiv.piCongrLeft sig.Strategy e.symm p)

theorem compile_reindex {ι κ : Type*} {sig : Signature ι}
    (L : ToyLanguage sig) (e : ι ≃ κ) :
    (L.reindex e).compile = L.compile.reindex e := by
  rfl

theorem six_comp {ι : Type*} {s₀ s₁ s₂ s₃ s₄ s₅ s₆ : Signature ι}
    {F₀ : Form s₀} {F₁ : Form s₁} {F₂ : Form s₂} {F₃ : Form s₃}
    {F₄ : Form s₄} {F₅ : Form s₅} {F₆ : Form s₆}
    (f₀₁ : Hom F₀ F₁) (f₁₂ : Hom F₁ F₂) (f₂₃ : Hom F₂ F₃)
    (f₃₄ : Hom F₃ F₄) (f₄₅ : Hom F₄ F₅) (f₅₆ : Hom F₅ F₆) :
    (((((f₅₆.comp f₄₅).comp f₃₄).comp f₂₃).comp f₁₂).comp f₀₁) =
      f₅₆.comp (f₄₅.comp (f₃₄.comp (f₂₃.comp (f₁₂.comp f₀₁)))) := by
  apply Hom.ext <;> rfl

end I

namespace B

open Bundled
open D2.FiniteSupportPMF

/-- Bundling requires both forms' projected signatures to be propositionally identified. -/
def pairedPlay {ι : Type*} (F G : Form ι) (h : F.sig = G.sig) (p : Profile F.sig) :
    Law F.sig.Outcome × Law F.sig.Outcome :=
  (F.play p, h ▸ G.play (h ▸ p))

structure ToyLanguage {ι : Type*} (sig : Signature ι) where
  eval : Profile sig → sig.Outcome

def ToyLanguage.compile {ι : Type*} {sig : Signature ι} (L : ToyLanguage sig) : Form ι where
  sig := sig
  play p := Law.pure (L.eval p)

def ToyLanguage.reindex {ι κ : Type*} {sig : Signature ι}
    (L : ToyLanguage sig) (e : ι ≃ κ) : ToyLanguage (sig.reindex e) where
  eval p := L.eval (Equiv.piCongrLeft sig.Strategy e.symm p)

theorem compile_reindex {ι κ : Type*} {sig : Signature ι}
    (L : ToyLanguage sig) (e : ι ≃ κ) :
    (L.reindex e).compile = L.compile.reindex e := by
  rfl

theorem six_comp {ι : Type*} {F₀ F₁ F₂ F₃ F₄ F₅ F₆ : Form ι}
    (f₀₁ : Hom F₀ F₁) (f₁₂ : Hom F₁ F₂) (f₂₃ : Hom F₂ F₃)
    (f₃₄ : Hom F₃ F₄) (f₄₅ : Hom F₄ F₅) (f₅₆ : Hom F₅ F₆) :
    (((((f₅₆.comp f₄₅).comp f₃₄).comp f₂₃).comp f₁₂).comp f₀₁) =
      f₅₆.comp (f₄₅.comp (f₃₄.comp (f₂₃.comp (f₁₂.comp f₀₁)))) := by
  apply Hom.ext <;> rfl

end B

end GameTheory.Experimental.Phase1.D1.Stress
