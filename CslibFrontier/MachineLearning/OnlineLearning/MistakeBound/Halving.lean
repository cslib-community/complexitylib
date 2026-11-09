/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Littlestone
public import Mathlib.Data.Nat.Log

/-!
# The halving algorithm

The **halving algorithm** [Littlestone1988, §3, Algorithm 1] learns a finite class
`C : Finset (α → Bool)`. It keeps the concepts of `C` consistent with the history
(`consistent C h`) and predicts the label given by the majority of them, with ties broken towards
`false`. After a mistake at least half of the consistent concepts are eliminated. On a realizable
sequence some concept always survives, so the halving algorithm makes at most `⌊log₂ |C|⌋`
mistakes (`mistakeBound_halving_le`, [Littlestone1988, §3, Theorem 1]). Consequently
`optimalMistakeBound C ≤ ⌊log₂ |C|⌋` [Littlestone1988, §3, Theorem 2], and by the lower bound of
`CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Littlestone`,
`littlestoneDim C ≤ ⌊log₂ |C|⌋`. The bounds are stated with `Nat.log 2`, the floor of `log₂`, which
is equivalent to the real bound `log₂ |C|` for integer counts of mistakes.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.consistent`: the concepts of a finite class
  that are consistent with a history.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.halving`: the halving algorithm.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakeBound_halving_le`:
  [Littlestone1988, §3, Theorem 1], the halving algorithm makes at most `⌊log₂ |C|⌋` mistakes.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.optimalMistakeBound_le_log_card`:
  [Littlestone1988, §3, Theorem 2].
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_le_log_card`: the Littlestone
  dimension is at most `⌊log₂ |C|⌋`.

## References

* [N. Littlestone, *Learning quickly when irrelevant attributes abound: a new linear-threshold
  algorithm*][Littlestone1988]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

variable {α : Type*}

/-- The concepts of the finite class `C` that agree with every example of the history `h`
(Littlestone's `CONSIST`). -/
@[expose] def consistent (C : Finset (α → Bool)) (h : List (α × Bool)) : Finset (α → Bool) :=
  C.filter fun c => ∀ p ∈ h, c p.1 = p.2

/-- The halving algorithm [Littlestone1988, §3, Algorithm 1]: predict `true` iff more consistent
concepts label the instance `true` than `false`. -/
@[expose] def halving (C : Finset (α → Bool)) : OnlineLearner α := fun h x =>
  decide (((consistent C h).filter (fun c => c x = false)).card <
    ((consistent C h).filter (fun c => c x = true)).card)

@[simp] theorem consistent_nil (C : Finset (α → Bool)) : consistent C [] = C := by
  ext; simp [consistent]

theorem consistent_append_singleton (C : Finset (α → Bool)) (h : List (α × Bool)) (x : α)
    (y : Bool) :
    consistent C (h ++ [(x, y)]) = (consistent C h).filter (fun c => c x = y) := by
  ext c
  simp only [consistent, Finset.mem_filter, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hc, hp⟩
    exact ⟨⟨hc, fun p hp' => hp p (Or.inl hp')⟩, hp (x, y) (Or.inr rfl)⟩
  · rintro ⟨⟨hc, hp⟩, hxy⟩
    refine ⟨hc, fun p hp' => ?_⟩
    rcases hp' with hp' | rfl
    · exact hp p hp'
    · exact hxy

theorem coe_consistent (C : Finset (α → Bool)) (h : List (α × Bool)) :
    (consistent C h : Set (α → Bool)) = versionSpace (C : Set (α → Bool)) h := by
  ext c
  simp [consistent, versionSpace]

/-- After the history `h`, each mistake of the halving algorithm at least halves the consistent
concepts, so `2 ^ (mistakes) ≤ |consistent C h|` on rounds that some consistent concept labels. -/
theorem two_pow_mistakesFrom_halving_le (C : Finset (α → Bool)) (h S : List (α × Bool))
    (hS : ∃ c ∈ consistent C h, ∀ p ∈ S, c p.1 = p.2) :
    2 ^ mistakesFrom (halving C) h S ≤ (consistent C h).card := by
  induction S generalizing h with
  | nil =>
    obtain ⟨c, hc, -⟩ := hS
    simpa using Finset.card_pos.mpr ⟨c, hc⟩
  | cons p S ih =>
    obtain ⟨x, y⟩ := p
    obtain ⟨c, hc, hcS⟩ := hS
    have hS' : ∃ c ∈ consistent C (h ++ [(x, y)]), ∀ p ∈ S, c p.1 = p.2 := by
      refine ⟨c, ?_, fun p hp => hcS p (List.mem_cons_of_mem _ hp)⟩
      rw [consistent_append_singleton, Finset.mem_filter]
      exact ⟨hc, hcS (x, y) List.mem_cons_self⟩
    have ih' := ih _ hS'
    rw [consistent_append_singleton] at ih'
    rw [mistakesFrom_cons]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := consistent C h) (fun c => c x = y)
    have hneg : (consistent C h).filter (fun c => ¬ c x = y) =
        (consistent C h).filter (fun c => c x = !y) := by
      congr 1; ext c; cases c x <;> cases y <;> simp
    rw [hneg] at hsplit
    split
    · rw [zero_add]
      exact ih'.trans (Finset.card_filter_le _ _)
    · rename_i hne
      have hmaj : ((consistent C h).filter (fun c => c x = y)).card ≤
          ((consistent C h).filter (fun c => c x = !y)).card := by
        cases y <;> simp only [halving, decide_eq_true_eq, decide_eq_false_iff_not,
          not_lt, Bool.not_true, Bool.not_false] at hne ⊢ <;> omega
      rw [pow_add, pow_one]
      omega

theorem mistakes_halving_le_log (C : Finset (α → Bool)) (S : List (α × Bool))
    (hS : Realizable (C : Set (α → Bool)) S) : mistakes (halving C) S ≤ Nat.log 2 C.card := by
  have hS' : ∃ c ∈ consistent C [], ∀ p ∈ S, c p.1 = p.2 := by
    obtain ⟨c, hc, hcS⟩ := realizable_iff.mp hS
    exact ⟨c, by simpa using hc, hcS⟩
  have h2 := two_pow_mistakesFrom_halving_le C [] S hS'
  rw [consistent_nil] at h2
  exact Nat.le_log_of_pow_le (by norm_num) h2

/-- **The halving bound** [Littlestone1988, §3, Theorem 1]: on a finite class `C`, the halving
algorithm makes at most `⌊log₂ |C|⌋` mistakes. -/
theorem mistakeBound_halving_le (C : Finset (α → Bool)) :
    mistakeBound (halving C) (C : Set (α → Bool)) ≤ Nat.log 2 C.card :=
  mistakeBound_le_iff.mpr fun S hS => by exact_mod_cast mistakes_halving_le_log C S hS

/-- [Littlestone1988, §3, Theorem 2]: the optimal mistake bound of a finite class `C` is at most
`⌊log₂ |C|⌋`. -/
theorem optimalMistakeBound_le_log_card (C : Finset (α → Bool)) :
    optimalMistakeBound (C : Set (α → Bool)) ≤ Nat.log 2 C.card :=
  (optimalMistakeBound_le (halving C) _).trans (mistakeBound_halving_le C)

/-- The Littlestone dimension of a finite class `C` is at most `⌊log₂ |C|⌋`. -/
theorem littlestoneDim_le_log_card (C : Finset (α → Bool)) :
    littlestoneDim (C : Set (α → Bool)) ≤ Nat.log 2 C.card :=
  (littlestoneDim_le_mistakeBound (halving C) _).trans (mistakeBound_halving_le C)

end Cslib.MachineLearning.OnlineLearning.MistakeBound
