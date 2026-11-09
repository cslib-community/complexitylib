/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Randomized
public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.SOA
import CslibFrontier.Foundations.Data.Nat.Choose.Sum

/-!
# Agnostic online learning

In the agnostic setting the labels are arbitrary: no concept of `C` need be consistent with them.
The learner competes with the best concept of `C` in hindsight. Its *regret* on a labelled sequence
`S` is the excess of its mistakes over `#{(x, y) ∈ S | c x ≠ y}`, the mistakes of the best concept
`c ∈ C`. Ben-David, Pál and Shalev-Shwartz showed that the Littlestone dimension controls the
regret [BenDavidPalShalevShwartz2009, §1.1, Theorem 1]. This file proves the upper half of their
Theorem 1, in its Littlestone-dimension form (`expectedMistakes_agnosticSOA_le`): if
`littlestoneDim C ≤ d`, a randomized learner has expected regret at most `2 √(T d log (T + 1))` on
every sequence of at most `T` rounds. The source's bound is `√(½ L̃dim(C) T)` with
`L̃dim(C) = min {ln |C|, Ldim(C) ln T}` [BenDavidPalShalevShwartz2009, eq. (1)], so its
Littlestone branch is `√(½ Ldim(C) T ln T)`. The constant here comes from the library's Hedge bound
and the expert count `(T + 1) ^ d`, and is weaker by a factor of about `2 √2`. The `ln |C|` branch
for finite classes is not stated here. Following the source, the environment is oblivious: the
labelled sequence is fixed in advance [BenDavidPalShalevShwartz2009, §6].

**The experts.** For a set `I` of rounds, `flipExpert A I` runs the deterministic learner `A` on a
self-labelled history. It labels each earlier instance by `A`'s prediction, negated at the rounds
in `I`, and predicts in the same way. For `A = soa C` this is the source's `Expert(i₁, …, i_L)`
[BenDavidPalShalevShwartz2009, §3.2, Algorithm 3]. Fix a concept `c` and a sequence of instances,
and let `I` be the rounds on which `A` errs on the `c`-labelled sequence (`mistakeRounds`). Then the
self-labelled history is exactly the `c`-labelled one, and `flipExpert A I` predicts `c` in every
round (`flipExpert_mistakeRounds`). It therefore makes exactly the mistakes of `c` on any labelling
of these instances (`mistakes_flipExpert_mistakeRounds`). For `A = soa C` and `c ∈ C`, the
`c`-labelled sequence is realizable, so `I` has at most `littlestoneDim C` elements
(`mistakesFrom_soa_le`). Together these are the source's Lemma 12 and Corollary 13, stated here
for any deterministic `A`.

**The learner.** `agnosticSOA C T d` runs Hedge (`hedgeLearner`) over the experts
`flipExpert (soa C) I` for the sets `I` of at most `d` rounds below `T` (`flipSets T d`), as in the
source's Algorithm 4. There are at most `∑_{j ≤ d} (T choose j) ≤ (T + 1) ^ d` of them
(`card_flipSets_le`; the source's eq. (7) bounds the same sum by `T ^ Ldim(C)`), so the Hedge regret
`2 √(T log N)` is at most `2 √(T d log (T + 1))`. The learner needs the horizon `T` and the
dimension bound `d`; it is a noncomputable specification, like `soa`.

**Randomization is necessary.** Against Cover's adversary (`Adversary.cover`), which labels each
round by the negation of the learner's prediction, a deterministic learner errs in every round. If
`C` contains both constant classifiers, one of them errs at most half the time, so the
deterministic regret is at least `T / 2` (`exists_mistakes_eq_length_of_const_mem`), although this
class has Littlestone dimension at most `1`. The source attributes this observation to Cover
(1965) [BenDavidPalShalevShwartz2009, §1].

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.flipExpert`: the learner `A`, negated at the
  rounds of a set `I` of its own self-labelled run.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakeRounds`: the rounds on which a learner
  errs.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.agnosticSOA`: the agnostic learner.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.Adversary.cover`: Cover's adversary.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakes_flipExpert_mistakeRounds`: the
  expert that flips `A` at its mistakes on the `c`-labelling makes exactly the mistakes of `c`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.expectedMistakes_agnosticSOA_le`: expected
  regret at most `2 √(T d log (T + 1))` against every concept of a class of Littlestone dimension
  at most `d` [BenDavidPalShalevShwartz2009].
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.exists_mistakes_eq_length_of_const_mem`:
  deterministic learners have linear regret.

## References

* [S. Ben-David, D. Pál, S. Shalev-Shwartz, *Agnostic online
  learning*][BenDavidPalShalevShwartz2009]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

open PACLearning (ConceptClass)
open Finset

variable {α : Type*}

/-! ### Experts that flip a learner -/

/-- The self-labelled history of `flipExpert A I` on the instances `xs`: each instance is labelled
by `A`'s prediction from the history so far, negated at the rounds in `I`. -/
def flipHistory (A : OnlineLearner α) (I : Finset ℕ) (xs : List α) : List (α × Bool) :=
  xs.foldl (fun h x => h ++ [(x, if h.length ∈ I then !A h x else A h x)]) []

/-- The expert that runs `A` on its self-labelled history and negates `A`'s prediction at the
rounds in `I`. It reads only the instances of its history, not their labels. For `A = soa C` this
is `Expert(i₁, …, i_L)` [BenDavidPalShalevShwartz2009, §3.2, Algorithm 3]. -/
def flipExpert (A : OnlineLearner α) (I : Finset ℕ) : OnlineLearner α := fun h x =>
  let h' := flipHistory A I (h.map Prod.fst)
  if h'.length ∈ I then !A h' x else A h' x

@[simp] theorem flipHistory_nil (A : OnlineLearner α) (I : Finset ℕ) :
    flipHistory A I [] = [] := by
  simp [flipHistory]

theorem flipHistory_append_singleton (A : OnlineLearner α) (I : Finset ℕ) (xs : List α) (x : α) :
    flipHistory A I (xs ++ [x]) = flipHistory A I xs ++
      [(x, if (flipHistory A I xs).length ∈ I then !A (flipHistory A I xs) x
        else A (flipHistory A I xs) x)] := by
  rw [flipHistory, flipHistory, List.foldl_append]
  rfl

theorem length_flipHistory (A : OnlineLearner α) (I : Finset ℕ) (xs : List α) :
    (flipHistory A I xs).length = xs.length := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih => simp [flipHistory_append_singleton, ih]

/-- The rounds on which the learner `A` errs on `S`. -/
def mistakeRounds (A : OnlineLearner α) (S : List (α × Bool)) : Finset ℕ :=
  (Finset.univ.filter fun t : Fin S.length => A (S.take t) S[t].1 ≠ S[t].2).map Fin.valEmbedding

theorem card_mistakeRounds (A : OnlineLearner α) (S : List (α × Bool)) :
    (mistakeRounds A S).card = mistakes A S := by
  rw [mistakeRounds, Finset.card_map, mistakes_eq_card]

theorem mem_mistakeRounds {A : OnlineLearner α} {S : List (α × Bool)} {t : ℕ} :
    t ∈ mistakeRounds A S ↔ ∃ ht : t < S.length, A (S.take t) S[t].1 ≠ S[t].2 := by
  simp only [mistakeRounds, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨ht, h⟩
    exact ⟨⟨t, ht⟩, h, rfl⟩

/-- Negating `A` at its mistakes on `S` recovers the labels of `S`: the self-labelled history of
the first `n` instances is the first `n` examples. -/
theorem flipHistory_mistakeRounds (A : OnlineLearner α) (S : List (α × Bool)) (n : ℕ)
    (hn : n ≤ S.length) :
    flipHistory A (mistakeRounds A S) ((S.take n).map Prod.fst) = S.take n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : n < S.length := hn
    rw [List.take_succ_eq_append_getElem hn', List.map_append, List.map_singleton,
      flipHistory_append_singleton, ih hn'.le]
    congr 2
    rw [List.length_take, min_eq_left hn'.le]
    refine Prod.ext rfl ?_
    by_cases hm : n ∈ mistakeRounds A S
    · rw [ite_eq_left hm]
      obtain ⟨_, hne⟩ := mem_mistakeRounds.mp hm
      revert hne
      cases A (S.take n) S[n].1 <;> cases S[n].2 <;> simp
    · rw [ite_eq_right hm]
      by_contra hne
      exact hm (mem_mistakeRounds.mpr ⟨hn', hne⟩)

/-- The expert that negates `A` at its mistakes on `S` predicts the labels of `S`, after any
history with the instances of `S` [BenDavidPalShalevShwartz2009, §3.2, Lemma 12]. -/
theorem flipExpert_mistakeRounds (A : OnlineLearner α) (S : List (α × Bool)) {t : ℕ}
    (ht : t < S.length) {h : List (α × Bool)} (hh : h.map Prod.fst = (S.take t).map Prod.fst) :
    flipExpert A (mistakeRounds A S) h S[t].1 = S[t].2 := by
  simp only [flipExpert]
  rw [hh, flipHistory_mistakeRounds A S t ht.le, List.length_take, min_eq_left ht.le]
  by_cases hm : t ∈ mistakeRounds A S
  · rw [ite_eq_left hm]
    obtain ⟨_, hne⟩ := mem_mistakeRounds.mp hm
    revert hne
    cases A (S.take t) S[t].1 <;> cases S[t].2 <;> simp
  · rw [ite_eq_right hm]
    by_contra hne
    exact hm (mem_mistakeRounds.mpr ⟨ht, hne⟩)

/-- The expert that negates `A` at its mistakes on the `c`-labelling of the instances of `S` makes
exactly the mistakes of `c` on `S` [BenDavidPalShalevShwartz2009, §3.2, Corollary 13]. -/
theorem mistakes_flipExpert_mistakeRounds (A : OnlineLearner α) (c : α → Bool)
    (S : List (α × Bool)) :
    mistakes (flipExpert A (mistakeRounds A (S.map fun p => (p.1, c p.1)))) S =
      S.countP fun p => c p.1 ≠ p.2 := by
  rw [← mistakesFrom_classifier c [] S, ← mistakes, mistakes_eq_card, mistakes_eq_card]
  congr 1
  refine Finset.filter_congr fun t _ => ?_
  have hlen : (t : ℕ) < (S.map fun p => (p.1, c p.1)).length := by simp
  have hh : (S.take t).map Prod.fst = ((S.map fun p => (p.1, c p.1)).take t).map Prod.fst := by
    simp [← List.map_take, List.map_map, Function.comp_def]
  have := flipExpert_mistakeRounds A _ hlen hh
  simp only [List.getElem_map] at this
  exact Iff.of_eq (congrArg (· ≠ S[t].2) this)

/-! ### The agnostic learner -/

/-- The sets of at most `d` rounds below `T`, which index the experts of `agnosticSOA`. -/
def flipSets (T d : ℕ) : Finset (Finset ℕ) :=
  (range (d + 1)).biUnion fun j => powersetCard j (range T)

theorem mem_flipSets {T d : ℕ} {I : Finset ℕ} : I ∈ flipSets T d ↔ I ⊆ range T ∧ I.card ≤ d := by
  simp only [flipSets, mem_biUnion, mem_range, mem_powersetCard]
  constructor
  · rintro ⟨j, hj, hI, rfl⟩
    exact ⟨hI, by omega⟩
  · rintro ⟨hI, hd⟩
    exact ⟨I.card, by omega, hI, rfl⟩

/-- There are at most `∑_{j ≤ d} (T choose j) ≤ (T + 1) ^ d` sets of at most `d` rounds below
`T`. Compare [BenDavidPalShalevShwartz2009, §3.2, eq. (7)]: for `d = Ldim(C)` it bounds the sum
by `T ^ d`. -/
theorem card_flipSets_le (T d : ℕ) : (flipSets T d).card ≤ (T + 1) ^ d :=
  card_biUnion_le.trans (by
    simpa only [card_powersetCard, card_range] using sum_range_choose_le_add_one_pow T d)

theorem card_flipSets_le_two_pow (T d : ℕ) : (flipSets T d).card ≤ 2 ^ T :=
  calc (flipSets T d).card ≤ (range T).powerset.card :=
        card_le_card fun I hI => mem_powerset.mpr (mem_flipSets.mp hI).1
    _ = 2 ^ T := by rw [card_powerset, card_range]

instance (T d : ℕ) : Nonempty (flipSets T d) :=
  ⟨⟨∅, mem_flipSets.mpr ⟨empty_subset _, by simp⟩⟩⟩

/-- The agnostic learner [BenDavidPalShalevShwartz2009, §3.2, Algorithm 4] for the horizon `T` and
the dimension bound `d`: Hedge, with learning rate `√(log N / T)` for its `N` experts, over the
experts `flipExpert (soa C) I` for the sets `I` of at most `d` rounds below `T`. -/
noncomputable def agnosticSOA (C : ConceptClass α Bool) (T d : ℕ) : RandomizedLearner α :=
  hedgeLearner (√(Real.log (Fintype.card (flipSets T d)) / T))
    fun I : flipSets T d => flipExpert (soa C) I

/-- **Agnostic online learning**, the upper half of [BenDavidPalShalevShwartz2009, §1.1,
Theorem 1] in its Littlestone-dimension form: if `littlestoneDim C ≤ d`, then on every labelled
sequence `S` of at most `T` rounds, with arbitrary labels, the agnostic learner makes at most
`2 √(T d log (T + 1))` more expected mistakes than any concept `c ∈ C`. The source's constant is
`√(½ d T ln T)`; the one here comes from the library's Hedge bound. -/
theorem expectedMistakes_agnosticSOA_le {C : ConceptClass α Bool} {d : ℕ}
    (hC : littlestoneDim C ≤ d) {T : ℕ} (S : List (α × Bool)) (hS : S.length ≤ T)
    {c : α → Bool} (hc : c ∈ C) :
    expectedMistakes (agnosticSOA C T d) S ≤
      (S.countP fun p => c p.1 ≠ p.2) + 2 * √(T * d * Real.log (T + 1)) := by
  set Sc := S.map fun p => (p.1, c p.1) with hSc
  have hI : mistakeRounds (soa C) Sc ∈ flipSets T d := by
    refine mem_flipSets.mpr ⟨fun t ht => ?_, ?_⟩
    · obtain ⟨ht, _⟩ := mem_mistakeRounds.mp ht
      rw [hSc, List.length_map] at ht
      exact mem_range.mpr (by omega)
    · rw [card_mistakeRounds]
      have hr : Realizable C ([] ++ Sc) := by
        simpa [hSc, List.map_map, Function.comp_def] using realizable_map hc (S.map Prod.fst)
      have h1 := mistakesFrom_soa_le C [] Sc hr
      rw [versionSpace_nil] at h1
      exact ENat.natCast_le_natCast.mp (h1.trans hC)
  have hNpos : (0 : ℝ) < Fintype.card (flipSets T d) := by exact_mod_cast Fintype.card_pos
  have hN : Real.log (Fintype.card (flipSets T d)) ≤ T :=
    calc Real.log (Fintype.card (flipSets T d)) ≤ Real.log ((2 : ℝ) ^ T) :=
          Real.log_le_log hNpos (by
            rw [Fintype.card_coe]
            exact_mod_cast card_flipSets_le_two_pow T d)
      _ = T * Real.log 2 := Real.log_pow _ _
      _ ≤ T * 1 := by
          gcongr
          linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ = T := mul_one _
  have hNd : Real.log (Fintype.card (flipSets T d)) ≤ d * Real.log (T + 1) :=
    calc Real.log (Fintype.card (flipSets T d)) ≤ Real.log (((T : ℝ) + 1) ^ d) :=
          Real.log_le_log hNpos (by
            rw [Fintype.card_coe]
            exact_mod_cast card_flipSets_le T d)
      _ = d * Real.log (T + 1) := Real.log_pow _ _
  have h := expectedMistakes_hedgeLearner_le (fun I : flipSets T d => flipExpert (soa C) I) hN
    S hS ⟨_, hI⟩
  have hm : (mistakes (flipExpert (soa C) (mistakeRounds (soa C) Sc)) S : ℝ) =
      (S.countP fun p => c p.1 ≠ p.2 : ℕ) := by
    rw [hSc, mistakes_flipExpert_mistakeRounds]
  rw [hm] at h
  refine h.trans (add_le_add_right ?_ _)
  rw [mul_assoc (T : ℝ)]
  gcongr

/-! ### Deterministic learners have linear regret -/

/-- Cover's adversary: it presents the instance `x` in every round and labels it by the negation of
the learner's prediction. -/
def Adversary.cover (x : α) : Adversary α where
  next _ := x
  label _ b := !b

/-- A deterministic learner errs in every round against Cover's adversary. -/
theorem mistakes_transcript_cover (A : OnlineLearner α) (x : α) (n : ℕ) :
    mistakes A ((Adversary.cover x).transcript A n) = n := by
  induction n with
  | zero => rw [Adversary.transcript_zero]; rfl
  | succ n ih =>
    rw [Adversary.transcript_succ, mistakes, mistakesFrom_append, ← mistakes, ih, List.nil_append,
      mistakesFrom_cons, mistakesFrom_nil]
    simp only [Adversary.cover]
    cases A ((Adversary.cover x).transcript A n) x <;> simp

/-- **Deterministic learners have linear regret**, an observation of Cover (1965) as cited in
[BenDavidPalShalevShwartz2009, §1]: if `C` contains both constant classifiers, then for every
deterministic learner `A` and every `n` there is a labelled sequence of `n` rounds, the transcript
of `Adversary.cover`, on which `A` errs in every round, while some concept of `C` errs in at most
`n / 2` rounds. So `expectedMistakes_agnosticSOA_le` needs a randomized learner. -/
theorem exists_mistakes_eq_length_of_const_mem {C : ConceptClass α Bool}
    (htrue : (fun _ => true) ∈ C) (hfalse : (fun _ => false) ∈ C) (A : OnlineLearner α) (x : α)
    (n : ℕ) :
    ∃ S : List (α × Bool), S.length = n ∧ mistakes A S = n ∧
      ∃ c ∈ C, 2 * S.countP (fun p => c p.1 ≠ p.2) ≤ n := by
  set S := (Adversary.cover x).transcript A n
  refine ⟨S, Adversary.length_transcript _ A n, mistakes_transcript_cover A x n, ?_⟩
  have hsum : ∀ S : List (α × Bool),
      S.countP (fun p => true ≠ p.2) + S.countP (fun p => false ≠ p.2) = S.length := by
    intro S
    rw [List.length_eq_countP_add_countP (fun p => true ≠ p.2)]
    congr 1
    refine List.countP_congr fun p _ => ?_
    cases p.2 <;> simp
  have h := hsum S
  rw [Adversary.length_transcript] at h
  by_cases ht : 2 * S.countP (fun p => true ≠ p.2) ≤ n
  · exact ⟨_, htrue, ht⟩
  · exact ⟨_, hfalse, by omega⟩

end Cslib.MachineLearning.OnlineLearning.MistakeBound
