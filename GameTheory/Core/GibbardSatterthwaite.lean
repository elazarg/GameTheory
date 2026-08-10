/-
# Gibbard--Satterthwaite

The public semantics are the canonical weak `Ranking` profile and the
`SocialChoiceFunction` laws from `Core.SocialChoice`.  The proof reduces a
strategyproof onto choice function to the existing Arrow theorem.  Raised
rankings, staged voter replacement, and the induced aggregator are private
proof machinery rather than a second social-choice language.

Primary references: A. Gibbard, “Manipulation of Voting Schemes,”
*Econometrica* 41 (1973); M. A. Satterthwaite, “Strategy-proofness and
Arrow's Conditions,” *Journal of Economic Theory* 10 (1975).
-/

import GameTheory.Core.Arrow

namespace GameTheory

universe uv ua

namespace SocialChoiceFunction

variable {Voter : Type uv} {Alternative : Type ua}

/-! ## Positive dictatorship witness -/

/-- Select the dictator's best alternative on linear inputs, with an arbitrary
fallback on malformed rankings.  The fallback is invisible to all public
social-choice laws, whose domain premise is `Preference.Linear`. -/
noncomputable def dictatorialChoice [Fintype Alternative]
    [Nonempty Alternative] (dictator : Voter) :
    SocialChoiceFunction Voter Alternative := by
  classical
  exact fun ranks =>
    if hlinear : Rank.Linear (ranks dictator) then
      Classical.choose <| Rank.exists_best_finset hlinear.2.1 hlinear.2.2.1
        (Finset.univ_nonempty : (Finset.univ : Finset Alternative).Nonempty)
    else Classical.choice inferInstance

/-- The canonical dictatorial choice function really selects a top alternative
of the dictator's reported linear ranking. -/
theorem dictatorialChoice_isDictator [Fintype Alternative]
    [Nonempty Alternative] (dictator : Voter) :
    (dictatorialChoice dictator : SocialChoiceFunction Voter Alternative).IsDictator
      dictator := by
  intro ranks hlinear alternative
  rw [dictatorialChoice, dif_pos (hlinear dictator)]
  exact (Classical.choose_spec <| Rank.exists_best_finset
    (hlinear dictator).2.1 (hlinear dictator).2.2.1
      (Finset.univ_nonempty : (Finset.univ : Finset Alternative).Nonempty)).2
        alternative (Finset.mem_univ _)

/-- Every exact dictator is strategyproof on the unrestricted linear-ranking
domain. -/
theorem IsDictator.isStrategyProof
    {choice : SocialChoiceFunction Voter Alternative} {dictator : Voter}
    (hdictator : choice.IsDictator dictator) : choice.IsStrategyProof := by
  intro ranks hlinear voter report hreport himproves
  by_cases hvoter : voter = dictator
  · subst voter
    exact himproves.2
      (hdictator ranks hlinear
        (choice (replaceRanking ranks dictator report)))
  · have hreplacement :
        Preference.Linear (replaceRanking ranks voter report) := by
      intro current
      by_cases hcurrent : current = voter
      · subst current
        simpa using hreport
      · rw [replaceRanking_of_ne _ hcurrent]
        exact hlinear current
    have hold := hdictator ranks hlinear
      (choice (replaceRanking ranks voter report))
    have hnew := hdictator (replaceRanking ranks voter report) hreplacement
      (choice ranks)
    rw [replaceRanking_of_ne _ (fun h => hvoter h.symm)] at hnew
    have heq : choice ranks = choice (replaceRanking ranks voter report) :=
      (hlinear dictator).2.2.2 _ _ hold hnew
    rw [← heq] at himproves
    exact Rank.strict_irrefl (ranks voter) _ himproves

/-- On a finite nonempty alternative set, the canonical dictatorial choice
function is onto the admissible linear-ranking domain. -/
theorem dictatorialChoice_isOnto [Fintype Alternative]
    [Nonempty Alternative] (dictator : Voter) :
    (dictatorialChoice dictator : SocialChoiceFunction Voter Alternative).IsOnto := by
  intro target
  classical
  letI : LinearOrder Alternative := WellOrderingRel.isWellOrder.linearOrder
  let maximum : Alternative :=
    (Finset.univ : Finset Alternative).max' Finset.univ_nonempty
  let relabel : Alternative ≃ Alternative := Equiv.swap target maximum
  let rank : Alternative → Alternative → Prop := fun preferred alternative =>
    relabel alternative ≤ relabel preferred
  let ranks : Ranking Voter Alternative := fun _ => rank
  have hrank : Rank.Linear rank := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro item
      exact le_rfl
    · intro preferred middle alternative hfirst hsecond
      exact le_trans hsecond hfirst
    · intro first second
      exact le_total (relabel second) (relabel first)
    · intro first second hfirst hsecond
      exact relabel.injective (le_antisymm hsecond hfirst)
  have hranks : Preference.Linear ranks := fun _ => hrank
  refine ⟨ranks, hranks, ?_⟩
  have hchosenTop := dictatorialChoice_isDictator dictator ranks hranks target
  have htargetTop :
      ranks dictator target (dictatorialChoice dictator ranks) := by
    show relabel (dictatorialChoice dictator ranks) ≤ relabel target
    rw [show relabel target = maximum by
      simp [relabel, Equiv.swap_apply_left]]
    exact Finset.le_max' (Finset.univ : Finset Alternative)
      (relabel (dictatorialChoice dictator ranks)) (Finset.mem_univ _)
  exact hrank.2.2.2 _ _ hchosenTop htargetTop

/-- The canonical dictatorship simultaneously witnesses the consistency of
the strategyproofness and onto premises. -/
theorem dictatorialChoice_isStrategyProof_and_isOnto
    [Fintype Alternative] [Nonempty Alternative] (dictator : Voter) :
    (dictatorialChoice dictator : SocialChoiceFunction Voter Alternative).IsStrategyProof ∧
      (dictatorialChoice dictator : SocialChoiceFunction Voter Alternative).IsOnto :=
  ⟨(dictatorialChoice_isDictator dictator).isStrategyProof,
    dictatorialChoice_isOnto dictator⟩

/-- **Single-voter monotonicity.** A strategyproof choice does not change when
one voter replaces their report by a linear ranking that weakly raises the
chosen alternative. -/
theorem IsStrategyProof.monotone_step
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof)
    {ranks : Ranking Voter Alternative} (hlinear : Preference.Linear ranks)
    {voter : Voter} {report : Alternative → Alternative → Prop}
    (hreport : Rank.Linear report)
    (hraised : ∀ alternative,
      ranks voter (choice ranks) alternative →
        report (choice ranks) alternative) :
    choice (replaceRanking ranks voter report) = choice ranks := by
  have hreplacement :
      Preference.Linear (replaceRanking ranks voter report) := by
    intro current
    by_cases hcurrent : current = voter
    · subst current
      simpa using hreport
    · rw [replaceRanking_of_ne _ hcurrent]
      exact hlinear current
  have hnotNew :
      ¬ Rank.strict report (choice ranks)
        (choice (replaceRanking ranks voter report)) := by
    have h := hstrategy (replaceRanking ranks voter report) hreplacement
      voter (ranks voter) (hlinear voter)
    simpa using h
  have hnotOld :
      ¬ Rank.strict (ranks voter)
        (choice (replaceRanking ranks voter report)) (choice ranks) :=
    hstrategy ranks hlinear voter report hreport
  by_contra hchanged
  have hne : choice (replaceRanking ranks voter report) ≠ choice ranks := hchanged
  have hnewReverse :
      Rank.strict report (choice (replaceRanking ranks voter report))
        (choice ranks) :=
    (Rank.strict_total_of_linear hreport hne.symm).resolve_left hnotNew
  have holdForward :
      Rank.strict (ranks voter) (choice ranks)
        (choice (replaceRanking ranks voter report)) :=
    (Rank.strict_total_of_linear (hlinear voter) hne).resolve_left hnotOld
  exact hnewReverse.2
    (hraised (choice (replaceRanking ranks voter report)) holdForward.1)

private def mixedRankings [DecidableEq Voter]
    (ranks ranks' : Ranking Voter Alternative) (switched : Finset Voter) :
    Ranking Voter Alternative :=
  fun voter => if voter ∈ switched then ranks' voter else ranks voter

private theorem mixedRankings_mem [DecidableEq Voter]
    {ranks ranks' : Ranking Voter Alternative} {switched : Finset Voter}
    {voter : Voter} (hmem : voter ∈ switched) :
    mixedRankings ranks ranks' switched voter = ranks' voter :=
  if_pos hmem

private theorem mixedRankings_not_mem [DecidableEq Voter]
    {ranks ranks' : Ranking Voter Alternative} {switched : Finset Voter}
    {voter : Voter} (hnot : voter ∉ switched) :
    mixedRankings ranks ranks' switched voter = ranks voter :=
  if_neg hnot

private theorem mixedRankings_empty [DecidableEq Voter]
    (ranks ranks' : Ranking Voter Alternative) :
    mixedRankings ranks ranks' ∅ = ranks := by
  funext voter
  simp [mixedRankings]

private theorem mixedRankings_univ [Fintype Voter] [DecidableEq Voter]
    (ranks ranks' : Ranking Voter Alternative) :
    mixedRankings ranks ranks' Finset.univ = ranks' := by
  funext voter
  simp [mixedRankings]

private theorem mixedRankings_insert [DecidableEq Voter]
    {ranks ranks' : Ranking Voter Alternative} {switched : Finset Voter}
    {voter : Voter} :
    mixedRankings ranks ranks' (insert voter switched) =
      replaceRanking (mixedRankings ranks ranks' switched) voter (ranks' voter) := by
  classical
  funext current
  by_cases hcurrent : current = voter
  · subst current
    simp [mixedRankings]
  · rw [replaceRanking_of_ne _ hcurrent]
    by_cases hmem : current ∈ switched
    · rw [mixedRankings_mem (Finset.mem_insert_of_mem hmem), mixedRankings_mem hmem]
    · rw [mixedRankings_not_mem (fun h => (Finset.mem_insert.mp h).elim hcurrent hmem),
        mixedRankings_not_mem hmem]

/-- **Monotonicity.** A strategyproof choice stays fixed when every voter
weakly raises the chosen alternative. -/
theorem IsStrategyProof.monotone [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof)
    {ranks ranks' : Ranking Voter Alternative}
    (hlinear : Preference.Linear ranks)
    (hlinear' : Preference.Linear ranks')
    (hraised : ∀ voter alternative,
      ranks voter (choice ranks) alternative →
        ranks' voter (choice ranks) alternative) :
    choice ranks' = choice ranks := by
  classical
  have hmixed : ∀ switched : Finset Voter,
      Preference.Linear (mixedRankings ranks ranks' switched) := by
    intro switched voter
    by_cases hmem : voter ∈ switched
    · rw [mixedRankings_mem hmem]
      exact hlinear' voter
    · rw [mixedRankings_not_mem hmem]
      exact hlinear voter
  have hfixed : ∀ switched : Finset Voter,
      choice (mixedRankings ranks ranks' switched) = choice ranks := by
    intro switched
    induction switched using Finset.induction_on with
    | empty => rw [mixedRankings_empty]
    | @insert voter switched hnot ih =>
        rw [mixedRankings_insert]
        have hstep : ∀ alternative,
            mixedRankings ranks ranks' switched voter
                (choice (mixedRankings ranks ranks' switched)) alternative →
              ranks' voter
                (choice (mixedRankings ranks ranks' switched)) alternative := by
          rw [ih, mixedRankings_not_mem hnot]
          exact hraised voter
        rw [hstrategy.monotone_step (hmixed switched) (hlinear' voter) hstep, ih]
  rw [← mixedRankings_univ ranks ranks']
  exact hfixed Finset.univ

/-! ## Private raised-ranking reduction -/

private def raiseTop (selected : Alternative → Prop)
    (ranks : Alternative → Alternative → Prop) :
    Alternative → Alternative → Prop :=
  fun first second =>
    (selected first ∧ ¬ selected second) ∨
      ((selected first ↔ selected second) ∧ ranks first second)

private theorem raiseTop_above {selected : Alternative → Prop}
    {ranks : Alternative → Alternative → Prop} {first second : Alternative}
    (hfirst : selected first) (hsecond : ¬ selected second) :
    raiseTop selected ranks first second :=
  Or.inl ⟨hfirst, hsecond⟩

private theorem raiseTop_same {selected : Alternative → Prop}
    {ranks : Alternative → Alternative → Prop} {first second : Alternative}
    (hsame : selected first ↔ selected second) :
    raiseTop selected ranks first second ↔ ranks first second := by
  constructor
  · rintro (⟨hfirst, hsecond⟩ | ⟨_, hranks⟩)
    · exact absurd (hsame.mp hfirst) hsecond
    · exact hranks
  · exact fun hranks => Or.inr ⟨hsame, hranks⟩

private theorem raiseTop_linear {selected : Alternative → Prop}
    {ranks : Alternative → Alternative → Prop} (hlinear : Rank.Linear ranks) :
    Rank.Linear (raiseTop selected ranks) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro alternative
    exact Or.inr ⟨Iff.rfl, hlinear.1 alternative⟩
  · intro first middle last hfirst hsecond
    rcases hfirst with ⟨hfirst, hnotMiddle⟩ | ⟨hfirstMiddle, hfm⟩
    · rcases hsecond with ⟨hmiddle, _⟩ | ⟨hmiddleLast, _⟩
      · exact absurd hmiddle hnotMiddle
      · exact Or.inl ⟨hfirst, fun hlast => hnotMiddle (hmiddleLast.mpr hlast)⟩
    · rcases hsecond with ⟨hmiddle, hnotLast⟩ | ⟨hmiddleLast, hml⟩
      · exact Or.inl ⟨hfirstMiddle.mpr hmiddle, hnotLast⟩
      · exact Or.inr ⟨hfirstMiddle.trans hmiddleLast,
          hlinear.2.1 first middle last hfm hml⟩
  · intro first second
    by_cases hfirst : selected first <;> by_cases hsecond : selected second
    · rcases hlinear.2.2.1 first second with h | h
      · exact Or.inl (Or.inr ⟨iff_of_true hfirst hsecond, h⟩)
      · exact Or.inr (Or.inr ⟨iff_of_true hsecond hfirst, h⟩)
    · exact Or.inl (Or.inl ⟨hfirst, hsecond⟩)
    · exact Or.inr (Or.inl ⟨hsecond, hfirst⟩)
    · rcases hlinear.2.2.1 first second with h | h
      · exact Or.inl (Or.inr ⟨iff_of_false hfirst hsecond, h⟩)
      · exact Or.inr (Or.inr ⟨iff_of_false hsecond hfirst, h⟩)
  · intro first second hfirst hsecond
    rcases hfirst with ⟨hselected, hnotSecond⟩ | ⟨hsame, hfirst⟩
    · rcases hsecond with ⟨hselectedSecond, _⟩ | ⟨hsame', _⟩
      · exact absurd hselectedSecond hnotSecond
      · exact absurd (hsame'.mpr hselected) hnotSecond
    · rcases hsecond with ⟨hselectedSecond, hnotFirst⟩ | ⟨_, hsecond⟩
      · exact absurd (hsame.mpr hselectedSecond) hnotFirst
      · exact hlinear.2.2.2 first second hfirst hsecond

private theorem raiseTop_congr {selected selected' : Alternative → Prop}
    (heq : ∀ alternative, selected alternative ↔ selected' alternative)
    (ranks : Alternative → Alternative → Prop) :
    raiseTop selected ranks = raiseTop selected' ranks := by
  funext first second
  simp only [raiseTop, heq first, heq second]

private def IsTop (ranks : Alternative → Alternative → Prop)
    (alternative : Alternative) : Prop :=
  ∀ other, ranks alternative other

private theorem IsTop.unique {ranks : Alternative → Alternative → Prop}
    (hlinear : Rank.Linear ranks) {first second : Alternative}
    (hfirst : IsTop ranks first) (hsecond : IsTop ranks second) :
    first = second :=
  hlinear.2.2.2 first second (hfirst second) (hsecond first)

/-- Strategyproofness plus full range implies unanimity. -/
theorem IsStrategyProof.unanimous [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto)
    {ranks : Ranking Voter Alternative} (hlinear : Preference.Linear ranks)
    {alternative : Alternative}
    (htop : ∀ voter other, ranks voter alternative other) :
    choice ranks = alternative := by
  obtain ⟨source, hsourceLinear, hsourceChoice⟩ := honto alternative
  have hraised : ∀ voter other,
      source voter (choice source) other → ranks voter (choice source) other := by
    intro voter other _
    rw [hsourceChoice]
    exact htop voter other
  rw [hstrategy.monotone hsourceLinear hlinear hraised, hsourceChoice]

/-- Strategyproofness and full range imply weak Pareto: an alternative that
everyone ranks strictly below another cannot be selected. -/
theorem IsStrategyProof.pareto [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto)
    {ranks : Ranking Voter Alternative} (hlinear : Preference.Linear ranks)
    {preferred dominated : Alternative}
    (hne : preferred ≠ dominated)
    (hdom : ∀ voter, Rank.strict (ranks voter) preferred dominated) :
    choice ranks ≠ dominated := by
  intro hchoice
  let raised : Ranking Voter Alternative :=
    fun voter => raiseTop (fun alternative => alternative = preferred) (ranks voter)
  have hraisedLinear : Preference.Linear raised :=
    fun voter => raiseTop_linear (hlinear voter)
  have htop : ∀ voter, IsTop (raised voter) preferred := by
    intro voter alternative
    by_cases heq : alternative = preferred
    · subst alternative
      exact (hraisedLinear voter).1 preferred
    · exact raiseTop_above rfl heq
  have hpreferred : choice raised = preferred :=
    hstrategy.unanimous honto hraisedLinear htop
  have hmono : ∀ voter alternative,
      ranks voter (choice ranks) alternative →
        raised voter (choice ranks) alternative := by
    intro voter alternative hranks
    rw [hchoice] at hranks ⊢
    by_cases heq : alternative = preferred
    · subst alternative
      exact absurd hranks (hdom voter).2
    · exact (raiseTop_same (selected := fun candidate => candidate = preferred)
        (iff_of_false hne.symm heq)).mpr hranks
  have hsame := hstrategy.monotone hlinear hraisedLinear hmono
  rw [hpreferred, hchoice] at hsame
  exact hne hsame

private def pairLift (ranks : Ranking Voter Alternative)
    (first second : Alternative) : Ranking Voter Alternative :=
  fun voter =>
    raiseTop (fun alternative => alternative = first ∨ alternative = second)
      (ranks voter)

private theorem pairLift_linear {ranks : Ranking Voter Alternative}
    (hlinear : Preference.Linear ranks) (first second : Alternative) :
    Preference.Linear (pairLift ranks first second) :=
  fun voter => raiseTop_linear (hlinear voter)

private theorem pairLift_swap (choice : SocialChoiceFunction Voter Alternative)
    (ranks : Ranking Voter Alternative) (first second : Alternative) :
    choice (pairLift ranks first second) = choice (pairLift ranks second first) := by
  congr 1
  funext voter
  exact raiseTop_congr (fun alternative => or_comm) (ranks voter)

private theorem pairLift_choice [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto)
    {ranks : Ranking Voter Alternative} (hlinear : Preference.Linear ranks)
    (first second : Alternative) :
    choice (pairLift ranks first second) = first ∨
      choice (pairLift ranks first second) = second := by
  by_contra hneither
  push Not at hneither
  obtain ⟨hfirst, hsecond⟩ := hneither
  have hliftLinear := pairLift_linear hlinear first second
  have hdom : ∀ voter,
      Rank.strict ((pairLift ranks first second) voter) first
        (choice (pairLift ranks first second)) := by
    intro voter
    apply Rank.strict_of_le_of_ne (hliftLinear voter).2.2.2
    · exact raiseTop_above (Or.inl rfl) (fun h => h.elim hfirst hsecond)
    · exact Ne.symm hfirst
  exact hstrategy.pareto honto hliftLinear (Ne.symm hfirst) hdom rfl

private def tripleLift (ranks : Ranking Voter Alternative)
    (first second third : Alternative) : Ranking Voter Alternative :=
  fun voter => raiseTop
    (fun alternative =>
      alternative = first ∨ alternative = second ∨ alternative = third)
    (ranks voter)

private theorem tripleLift_linear {ranks : Ranking Voter Alternative}
    (hlinear : Preference.Linear ranks) (first second third : Alternative) :
    Preference.Linear (tripleLift ranks first second third) :=
  fun voter => raiseTop_linear (hlinear voter)

private theorem tripleLift_choice [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto)
    {ranks : Ranking Voter Alternative} (hlinear : Preference.Linear ranks)
    (first second third : Alternative) :
    choice (tripleLift ranks first second third) = first ∨
      choice (tripleLift ranks first second third) = second ∨
      choice (tripleLift ranks first second third) = third := by
  by_contra hnone
  push Not at hnone
  obtain ⟨hfirst, hsecond, hthird⟩ := hnone
  have hliftLinear := tripleLift_linear hlinear first second third
  have hdom : ∀ voter,
      Rank.strict ((tripleLift ranks first second third) voter) first
        (choice (tripleLift ranks first second third)) := by
    intro voter
    apply Rank.strict_of_le_of_ne (hliftLinear voter).2.2.2
    · exact raiseTop_above (Or.inl rfl) (fun h => by
        rcases h with h | h | h
        · exact hfirst h
        · exact hsecond h
        · exact hthird h)
    · exact Ne.symm hfirst
  exact hstrategy.pareto honto hliftLinear (Ne.symm hfirst) hdom rfl

private theorem lift_winner_beats [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof)
    {ranks : Ranking Voter Alternative} (hlinear : Preference.Linear ranks)
    {selected : Alternative → Prop} {winner other : Alternative}
    (hwinner : selected winner) (hother : selected other)
    (hchoice : choice (fun voter => raiseTop selected (ranks voter)) = winner) :
    choice (pairLift ranks winner other) = winner := by
  let lifted : Ranking Voter Alternative :=
    fun voter => raiseTop selected (ranks voter)
  have hliftedLinear : Preference.Linear lifted :=
    fun voter => raiseTop_linear (hlinear voter)
  have hpairLinear := pairLift_linear hlinear winner other
  have hraised : ∀ voter alternative,
      lifted voter (choice lifted) alternative →
        (pairLift ranks winner other) voter (choice lifted) alternative := by
    intro voter alternative hranks
    rw [hchoice] at hranks ⊢
    by_cases hw : alternative = winner
    · subst alternative
      exact (hpairLinear voter).1 winner
    · by_cases ho : alternative = other
      · subst alternative
        exact (raiseTop_same
          (selected := fun candidate => candidate = winner ∨ candidate = other)
          (iff_of_true (Or.inl rfl) (Or.inr rfl))).mpr
            ((raiseTop_same (iff_of_true hwinner hother)).mp hranks)
      · exact raiseTop_above (Or.inl rfl) (fun h => h.elim hw ho)
  rw [hstrategy.monotone hliftedLinear hpairLinear hraised, hchoice]

private def strictInduced (choice : SocialChoiceFunction Voter Alternative)
    (ranks : Ranking Voter Alternative) : Alternative → Alternative → Prop :=
  fun first second =>
    first ≠ second ∧ choice (pairLift ranks first second) = first

private structure StrictLinear (relation : Alternative → Alternative → Prop) : Prop where
  irrefl : ∀ alternative, ¬ relation alternative alternative
  trans : ∀ {first second third},
    relation first second → relation second third → relation first third
  total : ∀ first second, first ≠ second →
    relation first second ∨ relation second first

private theorem StrictLinear.asymm {relation : Alternative → Alternative → Prop}
    (hlinear : StrictLinear relation) {first second : Alternative}
    (hfirst : relation first second) : ¬ relation second first :=
  fun hsecond => hlinear.irrefl first (hlinear.trans hfirst hsecond)

private def weakOfStrict (relation : Alternative → Alternative → Prop) :
    Alternative → Alternative → Prop :=
  fun first second => first = second ∨ relation first second

private theorem weakOfStrict_linear {relation : Alternative → Alternative → Prop}
    (hlinear : StrictLinear relation) : Rank.Linear (weakOfStrict relation) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro alternative
    exact Or.inl rfl
  · intro first second third hfirst hsecond
    rcases hfirst with rfl | hfirst
    · exact hsecond
    · rcases hsecond with rfl | hsecond
      · exact Or.inr hfirst
      · exact Or.inr (hlinear.trans hfirst hsecond)
  · intro first second
    by_cases heq : first = second
    · exact Or.inl (Or.inl heq)
    · rcases hlinear.total first second heq with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
  · intro first second hfirst hsecond
    rcases hfirst with heq | hfirst
    · exact heq
    · rcases hsecond with heq | hsecond
      · exact heq.symm
      · exact absurd hsecond (hlinear.asymm hfirst)

private theorem strict_weakOfStrict {relation : Alternative → Alternative → Prop}
    (hlinear : StrictLinear relation) (first second : Alternative) :
    Rank.strict (weakOfStrict relation) first second ↔ relation first second := by
  constructor
  · rintro ⟨hforward, hnotReverse⟩
    rcases hforward with heq | hrelation
    · subst second
      exact (hnotReverse (Or.inl rfl)).elim
    · exact hrelation
  · intro hrelation
    refine ⟨Or.inr hrelation, ?_⟩
    rintro (heq | hreverse)
    · subst second
      exact hlinear.irrefl first hrelation
    · exact hlinear.asymm hrelation hreverse

private theorem strictInduced_linear [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto)
    {ranks : Ranking Voter Alternative} (hlinear : Preference.Linear ranks) :
    StrictLinear (strictInduced choice ranks) := by
  refine ⟨?_, ?_, ?_⟩
  · intro alternative h
    exact h.1 rfl
  · intro first second third hfirst hsecond
    obtain ⟨hfirstNe, hfirstChoice⟩ := hfirst
    obtain ⟨hsecondNe, hsecondChoice⟩ := hsecond
    have hthirdNe : first ≠ third := by
      intro heq
      have hswap := pairLift_swap choice ranks first second
      rw [heq] at hfirstChoice hswap
      exact hsecondNe (hfirstChoice.symm.trans (hswap.trans hsecondChoice)).symm
    have htriple : choice (tripleLift ranks first second third) = first := by
      rcases tripleLift_choice hstrategy honto hlinear first second third with h | h | h
      · exact h
      · exfalso
        have hbeat := lift_winner_beats hstrategy hlinear
          (selected := fun candidate =>
            candidate = first ∨ candidate = second ∨ candidate = third)
          (winner := second) (other := first)
          (Or.inr (Or.inl rfl)) (Or.inl rfl) h
        exact hfirstNe (hfirstChoice.symm.trans
          ((pairLift_swap choice ranks first second).trans hbeat))
      · exfalso
        have hbeat := lift_winner_beats hstrategy hlinear
          (selected := fun candidate =>
            candidate = first ∨ candidate = second ∨ candidate = third)
          (winner := third) (other := second)
          (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) h
        exact hsecondNe (hsecondChoice.symm.trans
          ((pairLift_swap choice ranks second third).trans hbeat))
    exact ⟨hthirdNe, lift_winner_beats hstrategy hlinear
      (selected := fun candidate =>
        candidate = first ∨ candidate = second ∨ candidate = third)
      (winner := first) (other := third)
      (Or.inl rfl) (Or.inr (Or.inr rfl)) htriple⟩
  · intro first second hne
    rcases pairLift_choice hstrategy honto hlinear first second with h | h
    · exact Or.inl ⟨hne, h⟩
    · exact Or.inr ⟨hne.symm,
        (pairLift_swap choice ranks first second).symm.trans h⟩

private def inducedAggregator (choice : SocialChoiceFunction Voter Alternative) :
    Aggregator Voter Alternative :=
  fun ranks => weakOfStrict (strictInduced choice ranks)

private theorem induced_collectivelyRational [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto) :
    (inducedAggregator choice).IsCollectivelyRational := by
  intro ranks hlinear
  exact weakOfStrict_linear (strictInduced_linear hstrategy honto hlinear)

private theorem induced_pareto [Nonempty Voter] [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto) :
    (inducedAggregator choice).IsPareto := by
  intro ranks hlinear preferred dominated hdom
  have hne : preferred ≠ dominated := by
    let voter : Voter := Classical.choice inferInstance
    exact fun heq => by
      subst dominated
      exact (hdom voter).2 ((hlinear voter).1 preferred)
  have hstrictLinear := strictInduced_linear hstrategy honto hlinear
  simp only [inducedAggregator]
  rw [strict_weakOfStrict hstrictLinear]
  refine ⟨hne, ?_⟩
  have hliftLinear := pairLift_linear hlinear preferred dominated
  have htop : ∀ voter, IsTop ((pairLift ranks preferred dominated) voter) preferred := by
    intro voter alternative
    by_cases hp : alternative = preferred
    · subst alternative
      exact (hliftLinear voter).1 preferred
    · by_cases hd : alternative = dominated
      · subst alternative
        exact (raiseTop_same
          (selected := fun candidate => candidate = preferred ∨ candidate = dominated)
          (iff_of_true (Or.inl rfl) (Or.inr rfl))).mpr (hdom voter).1
      · exact raiseTop_above (Or.inl rfl) (fun h => h.elim hp hd)
  exact hstrategy.unanimous honto hliftLinear htop

private theorem pairLift_choice_eq_of_agree [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto)
    {ranks ranks' : Ranking Voter Alternative}
    (hlinear : Preference.Linear ranks)
    (hlinear' : Preference.Linear ranks')
    {first second : Alternative}
    (hagree : ∀ voter,
      (ranks voter first second ↔ ranks' voter first second) ∧
      (ranks voter second first ↔ ranks' voter second first)) :
    choice (pairLift ranks first second) =
      choice (pairLift ranks' first second) := by
  have hliftLinear := pairLift_linear hlinear first second
  have hliftLinear' := pairLift_linear hlinear' first second
  rcases pairLift_choice hstrategy honto hlinear first second with hchoice | hchoice
  · symm
    refine hstrategy.monotone hliftLinear hliftLinear' ?_
    intro voter alternative hranks
    rw [hchoice] at hranks ⊢
    by_cases hfirst : alternative = first
    · subst alternative
      exact (hliftLinear' voter).1 first
    · by_cases hsecond : alternative = second
      · subst alternative
        exact (raiseTop_same
          (selected := fun candidate => candidate = first ∨ candidate = second)
          (iff_of_true (Or.inl rfl) (Or.inr rfl))).mpr
            ((hagree voter).1.mp ((raiseTop_same
              (selected := fun candidate => candidate = first ∨ candidate = second)
              (iff_of_true (Or.inl rfl) (Or.inr rfl))).mp hranks))
      · exact raiseTop_above (Or.inl rfl) (fun h => h.elim hfirst hsecond)
  · symm
    refine hstrategy.monotone hliftLinear hliftLinear' ?_
    intro voter alternative hranks
    rw [hchoice] at hranks ⊢
    by_cases hsecond : alternative = second
    · subst alternative
      exact (hliftLinear' voter).1 second
    · by_cases hfirst : alternative = first
      · subst alternative
        exact (raiseTop_same
          (selected := fun candidate => candidate = first ∨ candidate = second)
          (iff_of_true (Or.inr rfl) (Or.inl rfl))).mpr
            ((hagree voter).2.mp ((raiseTop_same
              (selected := fun candidate => candidate = first ∨ candidate = second)
              (iff_of_true (Or.inr rfl) (Or.inl rfl))).mp hranks))
      · exact raiseTop_above (Or.inr rfl) (fun h => h.elim hfirst hsecond)

private theorem induced_iia [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto) :
    (inducedAggregator choice).IsIIA := by
  intro ranks ranks' hlinear hlinear' first second hagree
  have hweakAgree : ∀ voter,
      (ranks voter first second ↔ ranks' voter first second) ∧
      (ranks voter second first ↔ ranks' voter second first) := by
    intro voter
    constructor
    · constructor
      · intro h
        by_cases heq : first = second
        · subst second
          exact (hlinear' voter).1 first
        · exact ((hagree voter).1.mp
            (Rank.strict_of_le_of_ne (hlinear voter).2.2.2 h heq)).1
      · intro h
        by_cases heq : first = second
        · subst second
          exact (hlinear voter).1 first
        · exact ((hagree voter).1.mpr
            (Rank.strict_of_le_of_ne (hlinear' voter).2.2.2 h heq)).1
    · constructor
      · intro h
        by_cases heq : second = first
        · subst second
          exact (hlinear' voter).1 first
        · exact ((hagree voter).2.mp
            (Rank.strict_of_le_of_ne (hlinear voter).2.2.2 h heq)).1
      · intro h
        by_cases heq : second = first
        · subst second
          exact (hlinear voter).1 first
        · exact ((hagree voter).2.mpr
            (Rank.strict_of_le_of_ne (hlinear' voter).2.2.2 h heq)).1
  have hforward := pairLift_choice_eq_of_agree hstrategy honto
    hlinear hlinear' hweakAgree
  have hreverse := pairLift_choice_eq_of_agree hstrategy honto
    hlinear hlinear' (first := second) (second := first)
    (fun voter => ⟨(hweakAgree voter).2, (hweakAgree voter).1⟩)
  have hstrict := strictInduced_linear hstrategy honto hlinear
  have hstrict' := strictInduced_linear hstrategy honto hlinear'
  constructor
  · simp only [inducedAggregator, strict_weakOfStrict hstrict,
      strict_weakOfStrict hstrict', strictInduced]
    rw [hforward]
  · simp only [inducedAggregator, strict_weakOfStrict hstrict,
      strict_weakOfStrict hstrict', strictInduced]
    rw [hreverse]

private theorem dictator_transfer [Nonempty Voter] [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto)
    {dictator : Voter}
    (hdictator : (inducedAggregator choice).IsDictator dictator) :
    choice.IsDictator dictator := by
  intro ranks hlinear alternative
  by_cases heq : alternative = choice ranks
  · subst alternative
    exact (hlinear dictator).1 (choice ranks)
  rcases (hlinear dictator).2.2.1 (choice ranks) alternative with hchosen | halternative
  · exact hchosen
  · have hindividual :
        Rank.strict (ranks dictator) alternative (choice ranks) :=
      Rank.strict_of_le_of_ne (hlinear dictator).2.2.2 halternative heq
    have hsocial :
        Rank.strict (inducedAggregator choice ranks) alternative (choice ranks) :=
      (hdictator ranks hlinear alternative (choice ranks)).2 hindividual
    have hstrict := strictInduced_linear hstrategy honto hlinear
    have hinduced : strictInduced choice ranks alternative (choice ranks) := by
      exact (strict_weakOfStrict hstrict alternative (choice ranks)).mp
        (by simpa only [inducedAggregator] using hsocial)
    have hliftLinear := pairLift_linear hlinear alternative (choice ranks)
    have hraised : ∀ voter other,
        ranks voter (choice ranks) other →
          (pairLift ranks alternative (choice ranks)) voter
            (choice ranks) other := by
      intro voter other hranks
      by_cases halt : other = alternative
      · subst other
        exact (raiseTop_same
          (selected := fun candidate =>
            candidate = alternative ∨ candidate = choice ranks)
          (iff_of_true (Or.inr rfl) (Or.inl rfl))).mpr hranks
      · by_cases hchoice : other = choice ranks
        · subst other
          exact (hliftLinear voter).1 (choice ranks)
        · exact raiseTop_above (Or.inr rfl) (fun h => h.elim halt hchoice)
    have hsame := hstrategy.monotone hlinear hliftLinear hraised
    exact (heq (hinduced.2.symm.trans hsame)).elim

end SocialChoiceFunction

namespace GibbardSatterthwaite

variable {Voter : Type uv} {Alternative : Type ua}

/-- **Gibbard--Satterthwaite.** An onto strategyproof social choice function
on the unrestricted domain of linear rankings is dictatorial when the finite
nonempty electorate faces at least three alternatives.  The alternative
carrier itself need not be finite. -/
theorem impossibility [Nonempty Voter] [Fintype Voter]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto)
    (hatLeastThree : Arrow.HasAtLeastThree Alternative) :
    ∃ dictator, choice.IsDictator dictator := by
  have hcollective :=
    SocialChoiceFunction.induced_collectivelyRational hstrategy honto
  have hpareto := SocialChoiceFunction.induced_pareto hstrategy honto
  have hiia := SocialChoiceFunction.induced_iia hstrategy honto
  obtain ⟨dictator, hdictator⟩ :=
    Arrow.impossibility hcollective hpareto hiia hatLeastThree
  exact ⟨dictator,
    SocialChoiceFunction.dictator_transfer hstrategy honto hdictator⟩

/-- Finite-cardinality convenience form of Gibbard--Satterthwaite. -/
theorem impossibility_of_card [Nonempty Voter] [Fintype Voter]
    [Fintype Alternative]
    {choice : SocialChoiceFunction Voter Alternative}
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto)
    (hcard : 2 < Fintype.card Alternative) :
    ∃ dictator, choice.IsDictator dictator :=
  impossibility hstrategy honto (Arrow.hasAtLeastThree_of_card hcard)

end GibbardSatterthwaite

end GameTheory
