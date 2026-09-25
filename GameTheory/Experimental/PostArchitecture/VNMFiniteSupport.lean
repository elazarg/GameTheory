/-
# EXP-074: finite-support compound-indifference boundary

The support-induction proof belongs to canonical VNM theory. This consumer
checks its operation-local finite-support premise with an infinite outer
carrier and arbitrary PMF branches. No second preference axiom or lottery
carrier is defined here.
-/

import GameTheory.Core.VNM

namespace GameTheory.Experimental.PostArchitecture.VNMFiniteSupport

open GameTheory

universe u

/-- Finite compound substitution permits infinitely supported branch laws;
only the outer lottery's support is finite. -/
example {Outcome : Type u} (pref : PMF Outcome → PMF Outcome → Prop)
    (htrans : Rank.Transitive pref)
    (hindependent : Preference.MixtureIndependent (fun (_ : Unit) => pref))
    (outer : PMF ℕ) (hfinite : outer.support.Finite)
    (first second : ℕ → PMF Outcome)
    (hlocal : ∀ index ∈ outer.support,
      Rank.Indifferent pref (first index) (second index)) :
    Rank.Indifferent pref (outer.bind first) (outer.bind second) :=
  hindependent.indifferent_bind_of_finite_support () htrans
    outer hfinite first second hlocal

end GameTheory.Experimental.PostArchitecture.VNMFiniteSupport
