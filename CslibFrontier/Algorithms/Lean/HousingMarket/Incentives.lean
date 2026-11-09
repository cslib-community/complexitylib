/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.HousingMarket.TopTradingCycles
import CslibFrontier.Foundations.Combinatorics.FunctionalGraph.PeriodicPts

/-!
# Strategy-proofness of top trading cycles

A housing mechanism maps reported preference profiles to allocations. It is strategy-proof when
no agent obtains, by reporting a list other than its true one, a house it truly prefers to the
house it receives when reporting truthfully, whatever the other agents report. The top trading
cycles mechanism is strategy-proof ([Roth1982Indivisible]; [SchummerVohra2007], Theorem 10.7;
[Roughgarden2013CS364A], Lecture 9, Theorem 3.1).

The proof compares truthful TTC with TTC after agent `i` misreports, round by round. The
misreport changes only `i`'s pointer. While neither run has removed `i`, the two runs remove the
same cycles, because a cycle avoiding `i` uses only unchanged pointers. In the first round in
which one run removes `i`:

* if the truthful run removes `i`, agent `i` receives its favourite remaining house, which is at
  least as good as anything still present in either run;
* otherwise the misreporting run removes `i` along a cycle whose part from `i`'s new house back
  to `i` uses only unchanged pointers, so in the truthful run `i` is reached from that house along
  pointers, and `rank_ttcRounds_le_of_iterate` shows that truthful `i` receives a house at least
  as good.

## Main definitions

* `Instance.updatePref`: agent `i` reports the list `π` and the others report truthfully.
* `Cslib.Algorithms.Lean.HousingMarket.HousingMechanism`, `HousingMechanism.IsStrategyProof`.
* `HousingMechanism.topTradingCycles`: the TTC mechanism.

## Main results

* `HousingMechanism.isStrategyProof_topTradingCycles`: TTC is strategy-proof.
* `Instance.rank_ttc_le_updatePref`: the same statement for the allocation `Instance.ttc`.

## References

* [Roth1982Indivisible]
* [SchummerVohra2007]
* [Roughgarden2013CS364A]
-/

public section

namespace Cslib.Algorithms.Lean.HousingMarket

open Function

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- The market in which agent `i` reports the list `π` and everyone else reports truthfully. -/
@[expose] def updatePref (i : Fin n) (π : Equiv.Perm (Fin n)) : Instance n :=
  ⟨Function.update I.pref i π⟩

variable {I}

theorem updatePref_pref_of_ne {i j : Fin n} (π : Equiv.Perm (Fin n)) (hji : j ≠ i) :
    (I.updatePref i π).pref j = I.pref j :=
  Function.update_of_ne hji _ _

theorem updatePref_rank_of_ne {i j : Fin n} (π : Equiv.Perm (Fin n)) (hji : j ≠ i) :
    (I.updatePref i π).rank j = I.rank j := by
  funext h
  rw [rank, rank, updatePref_pref_of_ne π hji]

/-- A misreport by `i` does not change any other agent's pointer. -/
theorem updatePref_topChoice_of_ne {i j : Fin n} (π : Equiv.Perm (Fin n)) (hji : j ≠ i)
    (R : Finset (Fin n)) : (I.updatePref i π).topChoice R j = I.topChoice R j := by
  simp only [topChoice, updatePref_rank_of_ne π hji, updatePref_pref_of_ne π hji]

/-- On every submarket, agent `i` weakly prefers its truthful TTC house to its TTC house after
reporting `π`. -/
private theorem rank_ttcRounds_le_updatePref {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k)
    (i : Fin n) (π : Equiv.Perm (Fin n)) :
    I.rank i (I.ttcRounds k R i) ≤ I.rank i ((I.updatePref i π).ttcRounds k R i) := by
  induction k generalizing R with
  | zero => exact le_rfl
  | succ k ih =>
    by_cases hiR : i ∉ R
    · rw [ttcRounds_of_notMem hiR, ttcRounds_of_notMem hiR]
    rw [not_not] at hiR
    have hR : R.Nonempty := ⟨i, hiR⟩
    have hk' : (R \ I.cycleAgents R).card ≤ k := by
      have := card_sdiff_cycleAgents_lt (I := I) hR
      omega
    set J := I.updatePref i π
    have hfg : ∀ x, x ≠ i → J.topChoice R x = I.topChoice R x :=
      fun x hx => updatePref_topChoice_of_ne π hx R
    -- truthful `i` leaves now with its favourite remaining house
    by_cases hiC : i ∈ I.cycleAgents R
    · rw [ttcRounds_succ_of_mem hiC]
      exact rank_topChoice_le (ttcRounds_mem hk hiR) i
    by_cases hiC' : i ∈ J.cycleAgents R
    · -- misreporting `i` leaves now along a cycle; the rest of the cycle is a truthful path
      rw [ttcRounds_succ_of_mem (I := J) hiC']
      rw [mem_cycleAgents hR] at hiC'
      set p := minimalPeriod (J.topChoice R) i
      have hp := minimalPeriod_pos_of_mem_periodicPts hiC'
      have hne : ∀ j < p - 1, (J.topChoice R)^[j] (J.topChoice R i) ≠ i := by
        intro j hj heq
        rw [← iterate_succ_apply] at heq
        exact not_isPeriodicPt_of_pos_of_lt_minimalPeriod (Nat.succ_ne_zero j) (by omega) heq
      have hpath : (I.topChoice R)^[p - 1] (J.topChoice R i) = i := by
        rw [← Cslib.FunctionalGraph.iterate_eq_of_forall_lt fun j hj => hfg _ (hne j hj),
          ← iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
        exact iterate_minimalPeriod
      exact rank_ttcRounds_le_of_iterate hk (topChoice_mem hR i) hpath
    · -- neither run removes `i` now, so both remove the same cycles
      have hCC : I.cycleAgents R = J.cycleAgents R := by
        rw [mem_cycleAgents hR] at hiC hiC'
        ext x
        rw [mem_cycleAgents hR, mem_cycleAgents hR]
        exact ⟨fun hx => Cslib.FunctionalGraph.periodicPts_subset_of_eqOn
            (fun y hy => (hfg y fun h => hiC (h ▸ hy)).symm) hx,
          fun hx => Cslib.FunctionalGraph.periodicPts_subset_of_eqOn
            (fun y hy => hfg y fun h => hiC' (h ▸ hy)) hx⟩
      rw [ttcRounds_succ_of_notMem hiC, ttcRounds_succ_of_notMem (I := J) hiC', ← hCC]
      exact ih hk'

/-- No agent obtains a house it truly prefers to its TTC house by reporting another list. -/
theorem rank_ttc_le_updatePref (i : Fin n) (π : Equiv.Perm (Fin n)) :
    I.rank i (I.ttc i) ≤ I.rank i ((I.updatePref i π).ttc i) :=
  rank_ttcRounds_le_updatePref (by simp) i π

end Instance

/-- A direct housing mechanism maps a reported preference profile to an allocation. There are no
payments. -/
abbrev HousingMechanism (n : ℕ) := Instance n → Allocation n

namespace HousingMechanism

variable {n : ℕ}

/-- A mechanism is strategy-proof when, whatever the profile `I`, no agent `i` obtains, by
reporting a list `π` instead of its list in `I`, a house that it strictly prefers according to its
list in `I`. -/
@[expose] def IsStrategyProof (M : HousingMechanism n) : Prop :=
  ∀ (I : Instance n) (i : Fin n) (π : Equiv.Perm (Fin n)),
    I.rank i (M I i) ≤ I.rank i (M (I.updatePref i π) i)

/-- The top trading cycles mechanism. -/
@[expose] def topTradingCycles : HousingMechanism n := fun I => I.ttc

/-- The top trading cycles mechanism is strategy-proof ([Roth1982Indivisible];
[SchummerVohra2007], Theorem 10.7; [Roughgarden2013CS364A], Lecture 9, Theorem 3.1). -/
theorem isStrategyProof_topTradingCycles : (topTradingCycles (n := n)).IsStrategyProof :=
  fun I i π => I.rank_ttc_le_updatePref i π

end HousingMechanism

end Cslib.Algorithms.Lean.HousingMarket
