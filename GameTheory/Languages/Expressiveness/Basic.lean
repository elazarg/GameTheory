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

/-! ## Directed / simulation-style expressiveness -/

/-- A preorder-style semantic lens for directed expressiveness claims.

The orientation is representation-oriented: `Rel G H` should be read as
"`H` can simulate/represent `G`."  Thus a language realizes `G` when some
compiled game appears on the right of the relation.  This is the directed
analogue of `EquivalenceLens`; use `EquivalenceLens` when the relation is
symmetric and exact. -/
structure PreorderLens (ι : Type) where
  /-- Directed semantic relation.  `Rel G H` means `H` represents `G`. -/
  Rel : KernelGame ι → KernelGame ι → Prop
  refl : ∀ G : KernelGame ι, Rel G G
  trans : ∀ {G H K : KernelGame ι}, Rel G H → Rel H K → Rel G K

namespace PreorderLens

variable {ι : Type}

/-- Directed absolute expressiveness class.  `G` belongs when some compiled
program simulates/represents `G` according to the preorder lens. -/
def ExpressiveClass (P : PreorderLens ι) (L : Language.{u} ι) :
    Set (KernelGame ι) :=
  { G | ∃ x : L.Syntax, P.Rel G (L.compile x) }

/-- `L` is no more expressive than `M` under a directed preorder lens. -/
def ExpressiveLe (P : PreorderLens ι) (L : Language.{u} ι)
    (M : Language.{v} ι) : Prop :=
  ∀ G : KernelGame ι, G ∈ P.ExpressiveClass L → G ∈ P.ExpressiveClass M

/-- Directed expressiveness equality as inclusion both ways. -/
def ExpressiveEq (P : PreorderLens ι) (L : Language.{u} ι)
    (M : Language.{v} ι) : Prop :=
  P.ExpressiveLe L M ∧ P.ExpressiveLe M L

/-- A syntactic reduction gives directed expressiveness inclusion for a
transitive simulation/refinement relation. -/
theorem expressiveLe_of_reduction
    (P : PreorderLens ι) {L : Language.{u} ι} {M : Language.{v} ι}
    (r : Reduction L M P.Rel) :
    P.ExpressiveLe L M := by
  intro G hG
  rcases hG with ⟨x, hx⟩
  exact ⟨r.translate x, P.trans hx (r.sound x)⟩

/-- Reductions in both directions give directed exact relative expressiveness. -/
theorem expressiveEq_of_reductions
    (P : PreorderLens ι) {L : Language.{u} ι} {M : Language.{v} ι}
    (rLM : Reduction L M P.Rel) (rML : Reduction M L P.Rel) :
    P.ExpressiveEq L M :=
  ⟨P.expressiveLe_of_reduction rLM, P.expressiveLe_of_reduction rML⟩

/-- Directed language characterization under a preorder lens. -/
def Characterizes (P : PreorderLens ι) (L : Language.{u} ι)
    (C : Set (KernelGame ι)) : Prop :=
  ∀ G : KernelGame ι, G ∈ C ↔ G ∈ P.ExpressiveClass L

end PreorderLens

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
the comparison relation is an equivalence.

For non-symmetric simulation/refinement relations, use `PreorderLens`: this
equivalence proof relies on symmetry to turn the reduction's preservation
statement around. -/
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
