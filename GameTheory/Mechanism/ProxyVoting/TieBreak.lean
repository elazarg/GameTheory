/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.ProxyVoting
import GameTheory.Mechanism.ProxyVoting.Bounded

/-!
# Tie-break genericity for follower and proxy strategyproofness

The base development fixes one deterministic delegation tie-break: `delegate`
selects a nearest proxy by the proxy order (`Finset.min'`).  The paper, however,
states its strategyproofness results "for every deterministic tie-breaking
scheme that only depends on the state of voters".  This file shows that
Theorems 1 and 2 do not depend on the choice of tie-break: they hold for an
arbitrary *nearest selector* — any function that, at each population median,
selects some proxy whose report is closest to it.  The concrete `delegate` is
one such selector (`isNearestSelector_delegate`), so the base theorems are the
`sel := delegate` instances (`follower_strategyproof_of_delegate`,
`proxy_manipulation_iff_of_delegate`).

The proofs reuse the population-median lemmas verbatim — those never mention the
tie-break — and re-derive only the nearest-proxy geometry from the abstract
distance-optimality property `IsNearestSelector`.
-/

namespace GameTheory

namespace ProxyVoting

open Finset

/-! ## Nearest selectors and their geometry (no finiteness needed) -/

variable {P : Type*}

/-- A deterministic delegation tie-break, abstractly: `sel s x` selects a proxy
whose reported position is nearest to `x`.  Every deterministic tie-breaking
scheme that depends only on the state is such a nearest selector. -/
def IsNearestSelector (sel : (P → ℝ) → ℝ → P) : Prop :=
  ∀ (s : P → ℝ) (x : ℝ) (k : P), |s (sel s x) - x| ≤ |s k - x|

variable {sel : (P → ℝ) → ℝ → P} {s : P → ℝ}

private theorem two_mul_le_add_of_abs_le {a b x : ℝ} (hab : a < b)
    (h : |a - x| ≤ |b - x|) : 2 * x ≤ a + b := by
  rcases abs_cases (a - x) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
    rcases abs_cases (b - x) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
      rw [ha, hb] at h <;> linarith

private theorem add_le_two_mul_of_abs_le {a b y : ℝ} (hab : a < b)
    (h : |b - y| ≤ |a - y|) : a + b ≤ 2 * y := by
  rcases abs_cases (a - y) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
    rcases abs_cases (b - y) with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
      rw [ha, hb] at h <;> linarith

theorem lt_of_selPos_lt (hsel : IsNearestSelector sel) {x y : ℝ}
    (h : s (sel s x) < s (sel s y)) : x < y := by
  have h1 : |s (sel s x) - x| ≤ |s (sel s y) - x| := hsel s x _
  have h2 : |s (sel s y) - y| ≤ |s (sel s x) - y| := hsel s y _
  have hx2 : 2 * x ≤ s (sel s x) + s (sel s y) := two_mul_le_add_of_abs_le h h1
  have hy2 : s (sel s x) + s (sel s y) ≤ 2 * y := add_le_two_mul_of_abs_le h h2
  rcases eq_or_lt_of_le (by linarith : x ≤ y) with heq | hlt
  · subst heq; exact absurd h (lt_irrefl _)
  · exact hlt

theorem selPos_mono (hsel : IsNearestSelector sel) {x y : ℝ} (h : x ≤ y) :
    s (sel s x) ≤ s (sel s y) := by
  by_contra hc
  rw [not_le] at hc
  exact absurd (lt_of_selPos_lt hsel hc) (not_lt.mpr h)

theorem selPos_gap (hsel : IsNearestSelector sel) {μ : ℝ} {k : P}
    (h : s (sel s μ) < s k) : 2 * μ - s (sel s μ) ≤ s k := by
  have hd := hsel s μ k
  rcases abs_cases (s (sel s μ) - μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (s k - μ) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] at hd <;> linarith

theorem selPos_gap' (hsel : IsNearestSelector sel) {μ : ℝ} {k : P}
    (h : s k < s (sel s μ)) : s k ≤ 2 * μ - s (sel s μ) := by
  have hd := hsel s μ k
  rcases abs_cases (s (sel s μ) - μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (s k - μ) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] at hd <;> linarith

theorem pos_lt_of_lt_selPos (hsel : IsNearestSelector sel) {μ : ℝ} {k : P}
    (h : s k < s (sel s μ)) : s k < μ := by
  by_contra hc
  rw [not_lt] at hc
  have hd := hsel s μ k
  rcases abs_cases (s (sel s μ) - μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (s k - μ) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] at hd <;> linarith

theorem pos_gt_of_gt_selPos (hsel : IsNearestSelector sel) {μ : ℝ} {k : P}
    (h : s (sel s μ) < s k) : μ < s k := by
  by_contra hc
  rw [not_lt] at hc
  have hd := hsel s μ k
  rcases abs_cases (s (sel s μ) - μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (s k - μ) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] at hd <;> linarith

theorem abs_selPos_sub_le_of_le (hsel : IsNearestSelector sel) {μ μ' t : ℝ}
    (ht : t < μ) (hm : μ ≤ μ') :
    |s (sel s μ) - t| ≤ |s (sel s μ') - t| := by
  have hν : s (sel s μ) ≤ s (sel s μ') := selPos_mono hsel hm
  rcases le_or_gt t (s (sel s μ)) with hcase | hcase
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rcases eq_or_lt_of_le hν with heq | hlt
    · rw [heq]
    · have hgap : 2 * μ - s (sel s μ) ≤ s (sel s μ') := selPos_gap hsel hlt
      rw [abs_of_neg (by linarith), abs_of_nonneg (by linarith)]; linarith

theorem abs_selPos_sub_le_of_ge (hsel : IsNearestSelector sel) {μ μ' t : ℝ}
    (ht : μ < t) (hm : μ' ≤ μ) :
    |s (sel s μ) - t| ≤ |s (sel s μ') - t| := by
  have hν : s (sel s μ') ≤ s (sel s μ) := selPos_mono hsel hm
  rcases le_or_gt (s (sel s μ)) t with hcase | hcase
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · rcases eq_or_lt_of_le hν with heq | hlt
    · rw [← heq]
    · have hgap : s (sel s μ') ≤ 2 * μ - s (sel s μ) := selPos_gap' hsel hlt
      rw [abs_of_pos (by linarith), abs_of_nonpos (by linarith)]; linarith

/-! ## Outcomes under a nearest selector, and Theorem 1 -/

variable [Fintype P] [Nonempty P] [LinearOrder P] {F : Type*} [Fintype F]

/-- The concrete order-based `delegate` is a nearest selector. -/
theorem isNearestSelector_delegate :
    IsNearestSelector (P := P) (fun s x => delegate s x) :=
  fun s x k => delegate_dist_le s x k

/-- The winning position under a nearest selector `sel`. -/
noncomputable def outcomeWith (sel : (P → ℝ) → ℝ → P) (s : P → ℝ) (q : F → ℝ) : ℝ :=
  s (sel s (socialMedian s q))

/-- `outcomeWith` for the order-based selector is the concrete `outcome`. -/
theorem outcomeWith_delegate (s : P → ℝ) (q : F → ℝ) :
    outcomeWith (fun s x => delegate s x) s q = outcome s q := rfl

/-- **Theorem 1, tie-break generic.**  For *any* nearest-selector tie-break, the
weighted-median rule is strategyproof with respect to follower positions: no
follower misreport brings the winning position strictly closer to the
follower's own position.  The proof reuses the tie-break-free population-median
lemmas and the abstract nearest-proxy geometry. -/
theorem follower_strategyproof_of_nearestSelector (hsel : IsNearestSelector sel)
    [DecidableEq F] (s : P → ℝ) (q : F → ℝ) (i : F) (x : ℝ) :
    |outcomeWith sel s q - q i| ≤ |outcomeWith sel s (Function.update q i x) - q i| := by
  simp only [outcomeWith]
  rcases lt_trichotomy (q i) (socialMedian s q) with hqi | hqi | hqi
  · rcases le_or_gt x (socialMedian s q) with hx | hx
    · rw [socialMedian_update_eq_of_lt_of_le hqi hx]
    · exact abs_selPos_sub_le_of_le hsel hqi
        (socialMedian_le_update (le_of_lt (lt_trans hqi hx)))
  · rw [← hqi]; exact hsel s (q i) _
  · rcases le_or_gt (socialMedian s q) x with hx | hx
    · rw [socialMedian_update_eq_of_gt_of_ge hqi hx]
    · exact abs_selPos_sub_le_of_ge hsel hqi
        (socialMedian_update_le (le_of_lt (lt_trans hx hqi)))

/-- Theorem 1 for the concrete order-based tie-break, recovered as the
`sel := delegate` instance. -/
theorem follower_strategyproof_of_delegate [DecidableEq F]
    (s : P → ℝ) (q : F → ℝ) (i : F) (x : ℝ) :
    |outcome s q - q i| ≤ |outcome s (Function.update q i x) - q i| :=
  follower_strategyproof_of_nearestSelector isNearestSelector_delegate s q i x

/-! ## Theorem 2 under a nearest selector -/

variable {pp : P → ℝ} {q : F → ℝ}

omit [LinearOrder P] in
/-- With a proxy at the median, the outcome under a nearest selector is the
median. -/
private theorem outcomeWith_eq_median_of_proxy_at (hsel : IsNearestSelector sel)
    {k : P} (hk : pp k = socialMedian pp q) :
    outcomeWith sel pp q = socialMedian pp q := by
  have hd := hsel pp (socialMedian pp q) k
  rw [hk, sub_self, abs_zero] at hd
  have h0 := abs_eq_zero.mp (le_antisymm hd (abs_nonneg _))
  have := sub_eq_zero.mp h0
  simpa [outcomeWith] using this

/-- No proxy can manipulate when some proxy sits at the population median: no
report brings the outcome strictly closer to the manipulator's peak. -/
private theorem no_manipulation_of_proxy_at_median_sel (hsel : IsNearestSelector sel)
    {k : P} (hk : pp k = socialMedian pp q) (j : P) (r : ℝ) :
    ¬ Prefers pp j (outcomeWith sel (Function.update pp j r) q) (outcomeWith sel pp q) := by
  intro hpref
  rw [outcomeWith_eq_median_of_proxy_at hsel hk] at hpref
  rcases lt_trichotomy (pp j) (socialMedian pp q) with hj | hj | hj
  · -- peak strictly left of the median: the new outcome stays weakly right of
    -- the median, so it cannot land strictly between the peak and the median
    have hout : socialMedian pp q ≤ outcomeWith sel (Function.update pp j r) q := by
      have hkj : k ≠ j := fun h => by rw [h] at hk; exact absurd (hk ▸ hj) (lt_irrefl _)
      have hs'k : Function.update pp j r k = socialMedian pp q := by
        rw [Function.update_apply, if_neg hkj, hk]
      rcases le_or_gt r (socialMedian pp q) with hr | hr
      · -- median unchanged; the proxy at the median still wins it exactly
        have hμ := socialMedian_update_eq_of_proxy_lt hj hr
        have hd := hsel (Function.update pp j r)
          (socialMedian (Function.update pp j r) q) k
        rw [hμ, hs'k, sub_self, abs_zero] at hd
        have h0 := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd (abs_nonneg _)))
        simp only [outcomeWith, hμ, h0, le_refl]
      · -- median weakly rises; the proxy at the old median caps the distance
        have hμ : socialMedian pp q ≤ socialMedian (Function.update pp j r) q :=
          socialMedian_le_update_proxy (le_of_lt (lt_trans hj hr))
        have hd := hsel (Function.update pp j r)
          (socialMedian (Function.update pp j r) q) k
        rw [hs'k] at hd
        have habs : |socialMedian pp q - socialMedian (Function.update pp j r) q|
            = socialMedian (Function.update pp j r) q - socialMedian pp q := by
          rw [abs_of_nonpos (by linarith)]
          ring
        rw [habs] at hd
        have := neg_le_of_abs_le hd
        simp only [outcomeWith]
        linarith
    simp only [Prefers] at hpref
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hpref
    linarith
  · -- peak at the median: the truthful outcome is already the peak
    simp only [Prefers] at hpref
    rw [← hj, sub_self, abs_zero] at hpref
    linarith [abs_nonneg (outcomeWith sel (Function.update pp j r) q - pp j)]
  · -- peak strictly right of the median: mirror of the first case
    have hout : outcomeWith sel (Function.update pp j r) q ≤ socialMedian pp q := by
      have hkj : k ≠ j := fun h => by rw [h] at hk; exact absurd (hk ▸ hj) (lt_irrefl _)
      have hs'k : Function.update pp j r k = socialMedian pp q := by
        rw [Function.update_apply, if_neg hkj, hk]
      rcases le_or_gt (socialMedian pp q) r with hr | hr
      · have hμ := socialMedian_update_eq_of_proxy_gt hj hr
        have hd := hsel (Function.update pp j r)
          (socialMedian (Function.update pp j r) q) k
        rw [hμ, hs'k, sub_self, abs_zero] at hd
        have h0 := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd (abs_nonneg _)))
        simp only [outcomeWith, hμ, h0, le_refl]
      · have hμ : socialMedian (Function.update pp j r) q ≤ socialMedian pp q :=
          socialMedian_update_proxy_le (le_of_lt (lt_trans hr hj))
        have hd := hsel (Function.update pp j r)
          (socialMedian (Function.update pp j r) q) k
        rw [hs'k] at hd
        have habs : |socialMedian pp q - socialMedian (Function.update pp j r) q|
            = socialMedian pp q - socialMedian (Function.update pp j r) q :=
          abs_of_nonneg (by linarith)
        rw [habs] at hd
        have := le_of_abs_le hd
        simp only [outcomeWith]
        linarith
    simp only [Prefers] at hpref
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hpref
    linarith

/-- No proxy can manipulate when every proxy reports weakly left of the
median: no report brings the outcome strictly closer to any peak. -/
private theorem no_manipulation_of_proxies_le_sel (hsel : IsNearestSelector sel)
    (hall : ∀ k, pp k ≤ socialMedian pp q) (j : P) (r : ℝ) :
    ¬ Prefers pp j (outcomeWith sel (Function.update pp j r) q) (outcomeWith sel pp q) := by
  intro hpref
  -- The truthful outcome is the greatest proxy position.
  have hcle : outcomeWith sel pp q ≤ socialMedian pp q := by
    simp only [outcomeWith]
    exact hall _
  have hmax : ∀ k, pp k ≤ outcomeWith sel pp q := by
    intro k
    have hd := hsel pp (socialMedian pp q) k
    have h1 : pp (sel pp (socialMedian pp q)) - socialMedian pp q ≤ 0 := by
      have := hall (sel pp (socialMedian pp q))
      linarith
    have h2 : pp k - socialMedian pp q ≤ 0 := by
      have := hall k
      linarith
    rw [abs_of_nonpos h1, abs_of_nonpos h2] at hd
    change pp k ≤ pp (sel pp (socialMedian pp q))
    linarith
  rcases eq_or_lt_of_le (hmax j) with hj | hj
  · -- the manipulator already holds the winning position: its peak is the
    -- truthful outcome
    simp only [Prefers] at hpref
    rw [← hj, sub_self, abs_zero] at hpref
    linarith [abs_nonneg (outcomeWith sel (Function.update pp j r) q - pp j)]
  · -- the manipulator's peak is strictly below the winning position: the new
    -- outcome never falls strictly below the old one
    have hout : outcomeWith sel pp q ≤ outcomeWith sel (Function.update pp j r) q := by
      have hj₀ : sel pp (socialMedian pp q) ≠ j := by
        intro h
        rw [← h] at hj
        simp only [outcomeWith] at hj
        exact absurd hj (lt_irrefl _)
      have hs'j₀ : Function.update pp j r (sel pp (socialMedian pp q)) = outcomeWith sel pp q := by
        rw [Function.update_apply, if_neg hj₀]
        rfl
      have hcμ' : outcomeWith sel pp q ≤ socialMedian (Function.update pp j r) q := by
        rcases le_or_gt r (socialMedian pp q) with hr | hr
        · rw [socialMedian_update_eq_of_proxy_lt
            (lt_of_lt_of_le hj hcle) hr]
          exact hcle
        · exact le_trans hcle
            (socialMedian_le_update_proxy (le_of_lt (lt_of_le_of_lt (le_trans (hmax j) hcle) hr)))
      have hd := hsel (Function.update pp j r)
        (socialMedian (Function.update pp j r) q) (sel pp (socialMedian pp q))
      rw [hs'j₀, abs_of_nonpos (sub_nonpos.mpr hcμ')] at hd
      have := neg_le_of_abs_le hd
      simp only [outcomeWith] at *
      linarith
    simp only [Prefers] at hpref
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hpref
    linarith

/-- No proxy can manipulate when every proxy reports weakly right of the
median: no report brings the outcome strictly closer to any peak. -/
private theorem no_manipulation_of_proxies_ge_sel (hsel : IsNearestSelector sel)
    (hall : ∀ k, socialMedian pp q ≤ pp k) (j : P) (r : ℝ) :
    ¬ Prefers pp j (outcomeWith sel (Function.update pp j r) q) (outcomeWith sel pp q) := by
  intro hpref
  have hcge : socialMedian pp q ≤ outcomeWith sel pp q := by
    simp only [outcomeWith]
    exact hall _
  have hmin : ∀ k, outcomeWith sel pp q ≤ pp k := by
    intro k
    have hd := hsel pp (socialMedian pp q) k
    have h1 : 0 ≤ pp (sel pp (socialMedian pp q)) - socialMedian pp q := by
      have := hall (sel pp (socialMedian pp q))
      linarith
    have h2 : 0 ≤ pp k - socialMedian pp q := by
      have := hall k
      linarith
    rw [abs_of_nonneg h1, abs_of_nonneg h2] at hd
    change pp (sel pp (socialMedian pp q)) ≤ pp k
    linarith
  rcases eq_or_lt_of_le (hmin j) with hj | hj
  · simp only [Prefers] at hpref
    rw [hj, sub_self, abs_zero] at hpref
    linarith [abs_nonneg (outcomeWith sel (Function.update pp j r) q - pp j)]
  · have hout : outcomeWith sel (Function.update pp j r) q ≤ outcomeWith sel pp q := by
      have hj₀ : sel pp (socialMedian pp q) ≠ j := by
        intro h
        rw [← h] at hj
        simp only [outcomeWith] at hj
        exact absurd hj (lt_irrefl _)
      have hs'j₀ : Function.update pp j r (sel pp (socialMedian pp q)) = outcomeWith sel pp q := by
        rw [Function.update_apply, if_neg hj₀]
        rfl
      have hcμ' : socialMedian (Function.update pp j r) q ≤ outcomeWith sel pp q := by
        rcases le_or_gt (socialMedian pp q) r with hr | hr
        · rw [socialMedian_update_eq_of_proxy_gt
            (lt_of_le_of_lt hcge hj) hr]
          exact hcge
        · exact le_trans
            (socialMedian_update_proxy_le (le_of_lt (lt_of_lt_of_le hr (le_trans hcge (hmin j)))))
            hcge
      have hd := hsel (Function.update pp j r)
        (socialMedian (Function.update pp j r) q) (sel pp (socialMedian pp q))
      rw [hs'j₀, abs_of_nonneg (sub_nonneg.mpr hcμ')] at hd
      have := le_of_abs_le hd
      simp only [outcomeWith] at *
      linarith
    simp only [Prefers] at hpref
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hpref
    linarith

/-- **Theorem 2** (Bielous–Meir), tie-break generic.  For *any* nearest-selector
tie-break, some proxy has a manipulation in the truthful state — a report whose
outcome every single-peaked preference at the proxy's peak strictly prefers —
iff no proxy sits at the population median and proxies are present strictly on
both sides of it. -/
theorem proxy_manipulation_iff_of_nearestSelector (hsel : IsNearestSelector sel)
    (pp : P → ℝ) (q : F → ℝ) :
    (∃ (j : P) (r : ℝ),
        SPPrefers (pp j) (outcomeWith sel (Function.update pp j r) q) (outcomeWith sel pp q))
      ↔ (∀ j, pp j ≠ socialMedian pp q)
        ∧ (∃ j, pp j < socialMedian pp q)
        ∧ (∃ j, socialMedian pp q < pp j) := by
  constructor
  · rintro ⟨j, r, hpref⟩
    refine ⟨fun k hk => no_manipulation_of_proxy_at_median_sel hsel hk j r hpref.abs_lt, ?_, ?_⟩
    · by_contra hno
      rw [not_exists] at hno
      exact no_manipulation_of_proxies_ge_sel hsel
        (fun k => not_lt.mp (hno k)) j r hpref.abs_lt
    · by_contra hno
      rw [not_exists] at hno
      exact no_manipulation_of_proxies_le_sel hsel
        (fun k => not_lt.mp (hno k)) j r hpref.abs_lt
  · rintro ⟨hne, ⟨jl, hjl⟩, ⟨jr, hjr⟩⟩
    have hcne : outcomeWith sel pp q ≠ socialMedian pp q := hne (sel pp (socialMedian pp q))
    rcases lt_or_gt_of_ne hcne with hc | hc
    · -- outcome left of the median: the right-side proxy moves to the median
      refine ⟨jr, socialMedian pp q, ?_⟩
      have hμ := socialMedian_update_eq_of_proxy_gt hjr (le_refl _)
      have hs'jr : Function.update pp jr (socialMedian pp q) jr
          = socialMedian pp q := Function.update_self ..
      have hd := hsel
        (Function.update pp jr (socialMedian pp q))
        (socialMedian (Function.update pp jr (socialMedian pp q)) q) jr
      rw [hμ, hs'jr, sub_self, abs_zero] at hd
      have hout : outcomeWith sel (Function.update pp jr (socialMedian pp q)) q
          = socialMedian pp q := by
        have h0 := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd (abs_nonneg _)))
        simpa [outcomeWith, hμ] using h0
      rw [hout]
      exact Or.inr ⟨hc, le_of_lt hjr⟩
    · -- outcome right of the median: the left-side proxy moves to the median
      refine ⟨jl, socialMedian pp q, ?_⟩
      have hμ := socialMedian_update_eq_of_proxy_lt hjl (le_refl _)
      have hs'jl : Function.update pp jl (socialMedian pp q) jl
          = socialMedian pp q := Function.update_self ..
      have hd := hsel
        (Function.update pp jl (socialMedian pp q))
        (socialMedian (Function.update pp jl (socialMedian pp q)) q) jl
      rw [hμ, hs'jl, sub_self, abs_zero] at hd
      have hout : outcomeWith sel (Function.update pp jl (socialMedian pp q)) q
          = socialMedian pp q := by
        have h0 := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hd (abs_nonneg _)))
        simpa [outcomeWith, hμ] using h0
      rw [hout]
      exact Or.inl ⟨le_of_lt hjl, hc⟩

/-- **Theorem 2** for the concrete order-based tie-break, recovered as the
`sel := delegate` instance. -/
theorem proxy_manipulation_iff_of_delegate (pp : P → ℝ) (q : F → ℝ) :
    (∃ (j : P) (r : ℝ),
        SPPrefers (pp j) (outcome (Function.update pp j r) q) (outcome pp q))
      ↔ (∀ j, pp j ≠ socialMedian pp q)
        ∧ (∃ j, pp j < socialMedian pp q)
        ∧ (∃ j, socialMedian pp q < pp j) :=
  proxy_manipulation_iff_of_nearestSelector isNearestSelector_delegate pp q

/-! ## The follower reduction, made precise

After Theorem 1 the paper "considers followers non-strategic" and fixes the
follower profile.  Theorem 1 (`follower_strategyproof_of_nearestSelector`) is
mechanized in a form uniform over *every* proxy report profile, so a
dominance-respecting follower reports truthfully whatever the proxies do.  This
section records exactly what that buys, and is explicit about the one thing it
does not.  Everything here is tie-break generic; the median statements are even
tie-break independent. -/

/-- **(a) Per-state follower reduction.**  For any nearest-selector tie-break and
any sequence `σ` of proxy report profiles — an arbitrary "proxy dynamics", valid
or not — no follower has a manipulation *at any step's proxy profile*: holding
the proxies' reports fixed at `σ t`, truthful reporting is optimal for every
follower.  This is the precise per-state content of the paper's move to fixed
truthful followers.  It compares the truthful and misreported follower profiles
*at the same proxy profile*; it does **not** assert that a follower cannot gain
by misreporting so as to change the whole trajectory (see
`socialMedian_follower_strategyproof` for the converging regime, and
`bandFarDist_follower_strategyproof` / `FollowerPNE` for the non-converging
case). -/
theorem follower_no_perState_manipulation_of_nearestSelector
    (hsel : IsNearestSelector sel) [DecidableEq F]
    (σ : ℕ → P → ℝ) (q : F → ℝ) (t : ℕ) (i : F) (x : ℝ) :
    ¬ Prefers q i (outcomeWith sel (σ t) (Function.update q i x))
        (outcomeWith sel (σ t) q) :=
  not_lt.mpr (follower_strategyproof_of_nearestSelector hsel (σ t) q i x)

/-- (a) for the concrete order-based tie-break. -/
theorem follower_no_perState_manipulation_of_delegate [DecidableEq F]
    (σ : ℕ → P → ℝ) (q : F → ℝ) (t : ℕ) (i : F) (x : ℝ) :
    ¬ Prefers q i (outcome (σ t) (Function.update q i x)) (outcome (σ t) q) :=
  not_lt.mpr (follower_strategyproof_of_delegate (σ t) q i x)

/-- **(b) Follower strategyproofness of the true median.**  The population median
is itself strategyproof for followers: no follower brings the median strictly
closer to their own position by misreporting it.  This is Moulin median
strategyproofness for the full proxy-plus-follower population; it is tie-break
independent (the median does not depend on the delegation tie-break).

In the converging regime this is exactly follower-strategyproofness of the
*limit*.  A monotone better-response dynamics from truth keeps the median at
`socialMedian s q` (`socialMedian_eq_of_isMonotoneDynamics`) and its outcome
converges to that value (`tendsto_outcome_of_windowed_contraction`).  So the
limit a follower faces is `socialMedian s q` under truthful reporting and
`socialMedian s (Function.update q i x)` under a misreport, and this lemma says
the truthful limit is at least as close to the follower's true position. -/
theorem socialMedian_follower_strategyproof [DecidableEq F]
    (s : P → ℝ) (q : F → ℝ) (i : F) (x : ℝ) :
    |socialMedian s q - q i| ≤ |socialMedian s (Function.update q i x) - q i| := by
  rcases lt_trichotomy (q i) (socialMedian s q) with hqi | hqi | hqi
  · rcases le_or_gt x (socialMedian s q) with hx | hx
    · rw [socialMedian_update_eq_of_lt_of_le hqi hx]
    · have hmono : socialMedian s q ≤ socialMedian s (Function.update q i x) :=
        socialMedian_le_update (le_of_lt (lt_trans hqi hx))
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
  · rw [← hqi, sub_self, abs_zero]
    exact abs_nonneg _
  · rcases le_or_gt (socialMedian s q) x with hx | hx
    · rw [socialMedian_update_eq_of_gt_of_ge hqi hx]
    · have hmono : socialMedian s (Function.update q i x) ≤ socialMedian s q :=
        socialMedian_update_le (le_of_lt (lt_trans hx hqi))
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      linarith

/-- (b) in preference form: no follower strictly prefers the true median under a
misreported position to the true median under truthful reporting. -/
theorem socialMedian_follower_no_manipulation [DecidableEq F]
    (s : P → ℝ) (q : F → ℝ) (i : F) (x : ℝ) :
    ¬ Prefers q i (socialMedian s (Function.update q i x)) (socialMedian s q) :=
  not_lt.mpr (socialMedian_follower_strategyproof s q i x)

/-! ## Band worst-case follower strategyproofness

Truthful reporting minimizes the worst reachable band outcome.
When the proxy dynamics need not converge, a follower's outcome is only pinned
to the band `[med − Δ, med + Δ]`.  Under the worst-case reading — the follower
evaluates against the least favourable outcome the band permits — truthful
reporting minimizes that worst-case distance.  Both the band centre `med` and
its radius `Δ` move with the follower's report, but the radius is `1`-Lipschitz
in the centre while the centre only ever moves *away* from the follower (median
monotonicity), so the far edge of the band cannot come closer.  This is the
worst-case objective; the reachable-equilibrium (non-median PNE) steering
objective is framed separately in `FollowerPNE`. -/

/-- Distance from `m` to the nearest proxy report.  This is the radius of the
band `[med − Δ, med + Δ]` when `m` is the population median (`Δ = initialDelta`),
and it is independent of the delegation tie-break. -/
noncomputable def nearestProxyDist (pp : P → ℝ) (m : ℝ) : ℝ := |pp (delegate pp m) - m|

theorem nearestProxyDist_le (pp : P → ℝ) (m : ℝ) (k : P) :
    nearestProxyDist pp m ≤ |pp k - m| := delegate_dist_le pp m k

/-- `nearestProxyDist` is `1`-Lipschitz in the evaluation point: moving the
median by `d` changes the band radius by at most `d`. -/
theorem nearestProxyDist_sub_le (pp : P → ℝ) (m m' : ℝ) :
    nearestProxyDist pp m - nearestProxyDist pp m' ≤ |m - m'| := by
  have h1 : nearestProxyDist pp m ≤ |pp (delegate pp m') - m| :=
    nearestProxyDist_le pp m (delegate pp m')
  have h2 : |pp (delegate pp m') - m| ≤ |pp (delegate pp m') - m'| + |m - m'| := by
    have ht := abs_sub_le (pp (delegate pp m')) m' m
    rwa [abs_sub_comm m' m] at ht
  have h3 : nearestProxyDist pp m' = |pp (delegate pp m') - m'| := rfl
  linarith

theorem initialDelta_eq_nearestProxyDist (pp : P → ℝ) (q : F → ℝ) :
    initialDelta pp q = nearestProxyDist pp (socialMedian pp q) := rfl

/-- The worst-case distance from a fixed reference point `peak` to an outcome in
the `Δ`-band `[med − Δ, med + Δ]` of profile `q`: the distance to the far edge.
The reference `peak` is kept explicit (and held fixed across a follower's
misreport) precisely because the follower evaluates outcomes by their *true*
position, not the position they report. -/
noncomputable def bandFarDist (pp : P → ℝ) (q : F → ℝ) (peak : ℝ) : ℝ :=
  |socialMedian pp q - peak| + initialDelta pp q

/-- The farthest point of a ball `[c − Δ, c + Δ]` from `t` is at distance
`|c − t| + Δ`, and it is attained (at a band edge). -/
theorem isGreatest_dist_Icc (c t : ℝ) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    IsGreatest ((fun o => |o - t|) '' Set.Icc (c - Δ) (c + Δ)) (|c - t| + Δ) := by
  constructor
  · rcases le_total t c with h | h
    · refine ⟨c + Δ, ⟨by linarith, le_refl _⟩, ?_⟩
      change |c + Δ - t| = |c - t| + Δ
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c + Δ - t),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ c - t)]; ring
    · refine ⟨c - Δ, ⟨le_refl _, by linarith⟩, ?_⟩
      change |c - Δ - t| = |c - t| + Δ
      rw [abs_of_nonpos (by linarith : c - Δ - t ≤ 0),
        abs_of_nonpos (by linarith : c - t ≤ 0)]; ring
  · rintro d ⟨o, ⟨hlo, hhi⟩, rfl⟩
    have htri : |o - t| ≤ |o - c| + |c - t| := abs_sub_le o c t
    have hoc : |o - c| ≤ Δ := by rw [abs_le]; constructor <;> linarith
    linarith

/-- `bandFarDist` really is the worst-case outcome distance over the
`Δ`-band, attained at a band edge. -/
theorem isGreatest_bandFarDist (pp : P → ℝ) (q : F → ℝ) (peak : ℝ) :
    IsGreatest ((fun o => |o - peak|) ''
        Set.Icc (socialMedian pp q - initialDelta pp q)
          (socialMedian pp q + initialDelta pp q))
      (bandFarDist pp q peak) := by
  unfold bandFarDist
  exact isGreatest_dist_Icc (socialMedian pp q) peak (initialDelta_nonneg pp q)

/-- The worst band outcome is never closer to the reference position than its
nearest proxy: no report beats "support your nearest proxy". -/
theorem nearestProxyDist_le_bandFarDist (pp : P → ℝ) (q : F → ℝ) (peak : ℝ) :
    nearestProxyDist pp peak ≤ bandFarDist pp q peak := by
  have h1 : nearestProxyDist pp peak
      ≤ |pp (delegate pp (socialMedian pp q)) - peak| :=
    nearestProxyDist_le pp peak (delegate pp (socialMedian pp q))
  have h2 : |pp (delegate pp (socialMedian pp q)) - peak|
      ≤ |pp (delegate pp (socialMedian pp q)) - socialMedian pp q|
        + |socialMedian pp q - peak| := abs_sub_le _ _ _
  have h3 : initialDelta pp q
      = |pp (delegate pp (socialMedian pp q)) - socialMedian pp q| := rfl
  rw [bandFarDist, h3]
  linarith

/-- **Band worst-case follower strategyproofness.**  Truthful follower reporting
minimizes the worst reachable band outcome, measured against the follower's
*true* position `q i` (held fixed on both sides): for every misreport `x`, the far
edge of the band under the misreported profile is at least as far from `q i` as
the far edge under truthful reporting.  So even against an adversarial choice of
bounded outcome, no follower gains by misreporting to reshape the band.  Tie-break
independent: the band radius `initialDelta` is the minimum distance to a proxy,
unchanged by the tie-break. -/
theorem bandFarDist_follower_strategyproof [DecidableEq F]
    (pp : P → ℝ) (q : F → ℝ) (i : F) (x : ℝ) :
    bandFarDist pp q (q i) ≤ bandFarDist pp (Function.update q i x) (q i) := by
  have hlip := nearestProxyDist_sub_le pp (socialMedian pp q)
    (socialMedian pp (Function.update q i x))
  unfold bandFarDist
  rw [initialDelta_eq_nearestProxyDist pp q,
    initialDelta_eq_nearestProxyDist pp (Function.update q i x)]
  rcases lt_trichotomy (q i) (socialMedian pp q) with hqi | hqi | hqi
  · rcases le_or_gt x (socialMedian pp q) with hx | hx
    · rw [socialMedian_update_eq_of_lt_of_le hqi hx]
    · have hmono : socialMedian pp q ≤ socialMedian pp (Function.update q i x) :=
        socialMedian_le_update (le_of_lt (lt_trans hqi hx))
      rw [abs_of_pos (by linarith : (0:ℝ) < socialMedian pp q - q i),
        abs_of_pos (by linarith :
          (0:ℝ) < socialMedian pp (Function.update q i x) - q i)]
      rw [abs_of_nonpos (by linarith :
          socialMedian pp q - socialMedian pp (Function.update q i x) ≤ 0)] at hlip
      linarith
  · rw [hqi, sub_self, abs_zero, zero_add]
    rw [abs_sub_comm (socialMedian pp q)
      (socialMedian pp (Function.update q i x))] at hlip
    linarith
  · rcases le_or_gt (socialMedian pp q) x with hx | hx
    · rw [socialMedian_update_eq_of_gt_of_ge hqi hx]
    · have hmono : socialMedian pp (Function.update q i x) ≤ socialMedian pp q :=
        socialMedian_update_le (le_of_lt (lt_trans hx hqi))
      rw [abs_of_neg (by linarith : socialMedian pp q - q i < 0),
        abs_of_neg (by linarith :
          socialMedian pp (Function.update q i x) - q i < 0)]
      rw [abs_of_nonneg (by linarith :
          (0:ℝ) ≤ socialMedian pp q - socialMedian pp (Function.update q i x))] at hlip
      linarith

/-- Worst-case follower reduction in preference form: no follower strictly
prefers the worst reachable band outcome under a misreport to the worst reachable
band outcome under truthful reporting. -/
theorem bandFarDist_follower_no_manipulation [DecidableEq F]
    (pp : P → ℝ) (q : F → ℝ) (i : F) (x : ℝ) :
    ¬ bandFarDist pp (Function.update q i x) (q i) < bandFarDist pp q (q i) :=
  not_lt.mpr (bandFarDist_follower_strategyproof pp q i x)

open Filter in
/-- **Converging-regime follower reduction, at the limit.**  Suppose the outcome
of a proxy dynamics under the truthful follower profile converges to a limit `L`,
and also converges to the true median (as any convergent monotone dynamics does,
by `tendsto_outcome_of_windowed_contraction`); and likewise the outcome under a
misreported follower position converges to `L'` and to the corresponding true
median.  Then the follower does not strictly prefer the misreported limit: the
limits are the two true medians, and the true median is follower-strategyproof.

Together with `bandFarDist_follower_strategyproof` (worst-case bounded regime),
this covers the converging and bounded regimes; the selection of a *non-median*
pure equilibrium under a non-monotone dynamics is framed in `FollowerPNE`. -/
theorem follower_no_manipulation_at_median_limit [DecidableEq F]
    (pp : P → ℝ) (q : F → ℝ) (i : F) (x : ℝ)
    {σ σ' : ℕ → P → ℝ} {L L' : ℝ}
    (hL : Tendsto (fun t => outcome (σ t) q) atTop (nhds L))
    (hLmed : Tendsto (fun t => outcome (σ t) q) atTop (nhds (socialMedian pp q)))
    (hL' : Tendsto (fun t => outcome (σ' t) (Function.update q i x)) atTop (nhds L'))
    (hL'med : Tendsto (fun t => outcome (σ' t) (Function.update q i x)) atTop
      (nhds (socialMedian pp (Function.update q i x)))) :
    |L - q i| ≤ |L' - q i| := by
  rw [tendsto_nhds_unique hL hLmed, tendsto_nhds_unique hL' hL'med]
  exact socialMedian_follower_strategyproof pp q i x

end ProxyVoting

end GameTheory
