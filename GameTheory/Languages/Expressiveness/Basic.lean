import GameTheory.Core.KernelGame

/-!
# GameTheory.Languages.Expressiveness.Basic

Generic definitions for comparing concrete game languages by the
`KernelGame`s they compile to.

The definitions are deliberately parameterized by a semantic relation
`R : KernelGame ι → KernelGame ι → Prop`.  Different expressiveness projects can
then choose whether `R` means equality of expected utility, equality of utility
distributions, protocol isomorphism, observation-preserving bisimulation, or
some stricter structural relation.
-/

namespace GameTheory
namespace Languages
namespace Expressiveness

universe u v w

/-- Reindex the player type of a kernel game along an equivalence.

This is presentation bookkeeping: some syntactic bridges choose a canonical
finite player type, such as `Fin (Fintype.card ι)`, while the source game is
indexed by `ι`. -/
noncomputable def KernelGame.reindex {ι κ : Type} (e : ι ≃ κ)
    (G : KernelGame κ) : KernelGame ι where
  Strategy := fun i => G.Strategy (e i)
  Outcome := G.Outcome
  utility := fun ω i => G.utility ω (e i)
  outcomeKernel := fun σ =>
    G.outcomeKernel (fun k => by
      simpa using σ (e.symm k))

/-- A game language for a fixed player type `ι`: syntax plus compilation into
the common kernel-game semantics. -/
structure Language (ι : Type) where
  /-- Concrete syntax/presentation objects of the language. -/
  Syntax : Type u
  /-- Semantic compilation target. -/
  compile : Syntax → KernelGame ι

namespace Language

variable {ι : Type}

/-- A language realizes a semantic game up to relation `R`. -/
def Realizes (L : Language.{u} ι) (R : KernelGame ι → KernelGame ι → Prop)
    (G : KernelGame ι) : Prop :=
  ∃ x : L.Syntax, R (L.compile x) G

/-- Restrict a language to a syntactic sublanguage. -/
def restrict (L : Language.{u} ι) (P : L.Syntax → Prop) : Language ι where
  Syntax := { x : L.Syntax // P x }
  compile := fun x => L.compile x.1

@[simp] theorem restrict_compile (L : Language.{u} ι) (P : L.Syntax → Prop)
    (x : { x : L.Syntax // P x }) :
    (L.restrict P).compile x = L.compile x.1 := rfl

end Language

/-- A semantic-preserving translation from language `L` to language `M`.

The relation is oriented from the source compiled game to the target compiled
game.  For equivalence relations this is an ordinary reduction.  For directed
relations, such as simulations/refinements, the orientation is part of the
meaning of the theorem using the reduction. -/
structure Reduction {ι : Type} (L : Language.{u} ι) (M : Language.{v} ι)
    (R : KernelGame ι → KernelGame ι → Prop) where
  /-- Translation on syntax. -/
  translate : L.Syntax → M.Syntax
  /-- Semantic preservation theorem for every source program. -/
  sound : ∀ x : L.Syntax, R (L.compile x) (M.compile (translate x))

namespace Reduction

variable {ι : Type}
variable {L : Language.{u} ι} {M : Language.{v} ι} {N : Language.{w} ι}
variable {R : KernelGame ι → KernelGame ι → Prop}

/-- Identity reduction for a reflexive semantic relation. -/
def id (L : Language.{u} ι)
    (hrefl : ∀ G : KernelGame ι, R G G) :
    Reduction L L R where
  translate := _root_.id
  sound := fun x => hrefl (L.compile x)

/-- Compose reductions for a transitive semantic relation. -/
def comp
    (g : Reduction M N R) (f : Reduction L M R)
    (htrans : ∀ {G H K : KernelGame ι}, R G H → R H K → R G K) :
    Reduction L N R where
  translate := fun x => g.translate (f.translate x)
  sound := fun x => htrans (f.sound x) (g.sound (f.translate x))

end Reduction

/-- A reduction defined only on a syntactic sublanguage of `L`. -/
structure SubReduction {ι : Type} (L : Language.{u} ι) (M : Language.{v} ι)
    (P : L.Syntax → Prop)
    (R : KernelGame ι → KernelGame ι → Prop) where
  /-- Translation for source programs satisfying `P`. -/
  translate : (x : L.Syntax) → P x → M.Syntax
  /-- Semantic preservation for the restricted source programs. -/
  sound : ∀ (x : L.Syntax) (hx : P x),
    R (L.compile x) (M.compile (translate x hx))

namespace SubReduction

variable {ι : Type} {L : Language.{u} ι} {M : Language.{v} ι}
variable {P : L.Syntax → Prop}
variable {R : KernelGame ι → KernelGame ι → Prop}

/-- View a sublanguage reduction as an ordinary reduction from `L.restrict P`. -/
def toReduction (r : SubReduction L M P R) :
    Reduction (L.restrict P) M R where
  translate := fun x => r.translate x.1 x.2
  sound := fun x => r.sound x.1 x.2

end SubReduction

/-- An equivalence-style semantic lens for absolute expressiveness claims. -/
structure EquivalenceLens (ι : Type) where
  /-- The semantic equivalence relation used to compare compiled games. -/
  Rel : KernelGame ι → KernelGame ι → Prop
  refl : ∀ G : KernelGame ι, Rel G G
  symm : ∀ {G H : KernelGame ι}, Rel G H → Rel H G
  trans : ∀ {G H K : KernelGame ι}, Rel G H → Rel H K → Rel G K

namespace EquivalenceLens

variable {ι : Type}

/-- Absolute expressiveness class: the semantic games realized by `L` under
the equivalence lens `E`. -/
def ExpressiveClass (E : EquivalenceLens ι) (L : Language.{u} ι) :
    Set (KernelGame ι) :=
  { G | L.Realizes E.Rel G }

/-- `L` is no more expressive than `M` under lens `E`, extensionally. -/
def ExpressiveLe (E : EquivalenceLens ι) (L : Language.{u} ι)
    (M : Language.{v} ι) : Prop :=
  ∀ G : KernelGame ι, G ∈ E.ExpressiveClass L → G ∈ E.ExpressiveClass M

/-- `L` and `M` realize exactly the same semantic games under lens `E`. -/
def ExpressiveEq (E : EquivalenceLens ι) (L : Language.{u} ι)
    (M : Language.{v} ι) : Prop :=
  E.ExpressiveLe L M ∧ E.ExpressiveLe M L

/-- A syntactic reduction gives extensional expressiveness inclusion whenever
the comparison relation is an equivalence. -/
theorem expressiveLe_of_reduction
    (E : EquivalenceLens ι) {L : Language.{u} ι} {M : Language.{v} ι}
    (r : Reduction L M E.Rel) :
    E.ExpressiveLe L M := by
  intro G hG
  rcases hG with ⟨x, hx⟩
  exact ⟨r.translate x, E.trans (E.symm (r.sound x)) hx⟩

/-- Reductions in both directions give exact relative expressiveness. -/
theorem expressiveEq_of_reductions
    (E : EquivalenceLens ι) {L : Language.{u} ι} {M : Language.{v} ι}
    (rLM : Reduction L M E.Rel) (rML : Reduction M L E.Rel) :
    E.ExpressiveEq L M :=
  ⟨E.expressiveLe_of_reduction rLM, E.expressiveLe_of_reduction rML⟩

/-- A language exactly characterizes a class of kernel games under lens `E`. -/
def Characterizes (E : EquivalenceLens ι) (L : Language.{u} ι)
    (C : Set (KernelGame ι)) : Prop :=
  ∀ G : KernelGame ι, G ∈ C ↔ G ∈ E.ExpressiveClass L

end EquivalenceLens

end Expressiveness
end Languages
end GameTheory
