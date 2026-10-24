/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.MassProduction.Scheduler.Cost
import Mathlib.Tactic.Ring

/-!
# A near-linear nonuniform scheduler circuit

For `2 ^ D` requests, a fixed De Morgan circuit maps the bits of arbitrary target points of
`K ^ ℓ`, which may repeat, to listed punctured lines through them with nonzero directions and
pairwise disjoint lines, in the original request order (`IsScheduler`). Universal menus of
direction tuples are a hypothesis: for every `0 < k ≤ 2 ^ D` pending requests some menu of `r`
entries with `k * r ≤ 2 ^ D * (2 + 3 ℓ b) + 2 k` serves every state with `2 ^ D` occupied lines.

The circuit labels every request with its position, then runs `D + 1` phases with `2 ^ D`,
`2 ^ (D - 1)`, …, `1` pending requests. Each phase tests its menu and accepts the clean half of
the pending requests (`Scheduler.next`), keeping the state good (`Scheduler.good_next`). Finally
the records are sorted by label, which returns every request's line to its original position
(`Scheduler.finalOutput_eq_lineBits`).

The size counts every gate, including constants, and is at most
`524288 * 2 ^ D * (s + 1) * (D + ℓ * b + 2) ^ 5` (`schedulerBound`). The circuit is obtained
existentially from synthesis bounds; its size does not certify the running time of any
constructor.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.schedulerBound`: the gate bound.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.exists_isScheduler`: a scheduler circuit within
  `schedulerBound` gates.

## References

* Adapted from MassProduction/Nonuniform/SchedulerCircuit.lean,
  MassProduction/Nonuniform/BufferIteration.lean and
  MassProduction/Nonuniform/BufferIterationCost.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction],
  using the sorting network of
  [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction

open BitString LineCode BitonicSort Scheduler

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ b s D : ℕ}

namespace Scheduler

/-- Some circuit computes `finalOutput` exactly, by sorting the records by label and reading every
request's line from the rank of its label, within the displayed number of gates. -/
private theorem exists_finalOutput_circuit (D L s : ℕ) :
    ∃ c : Circuit signature (2 ^ D * width D L s) (2 ^ D * (s * L)),
      c.Computes interpretation finalOutput ∧
        c.size ≤ (D + 1) ^ 2 * 2 ^ D * (2 * D + 2 * width D L s + 1) := by
  have h2 := arity_eq_two_pow D
  let g : Fin (arity D * width D L s) → BooleanFunction (2 ^ D * width D L s) := fun w x =>
    x (finProdFinEquiv (Fin.cast h2 (finProdFinEquiv.symm w).1, (finProdFinEquiv.symm w).2))
  have hsyn := Synthesis.circuit (I := interpretation) (s := inputs (2 ^ D * width D L s))
    (bitonicSortCircuit labelBit D true) g fun w => ⟨_, rfl⟩
  have hsub : (Set.range fun q x => finalOutput (D := D) (L := L) (s := s) x q) ⊆
      Set.range fun j x => (bitonicSortCircuit labelBit D true).eval interpretation
        (fun i => g i x) j := by
    rintro _ ⟨q, rfl⟩
    let ip := finProdFinEquiv.symm q
    let cb := finProdFinEquiv.symm ip.2
    refine ⟨finProdFinEquiv (Fin.cast h2.symm (rank ip.1), lineBit cb.1 cb.2),
      funext fun x => ?_⟩
    have h := congrFun (congrFun (eval_bitonicSortCircuit labelBit D true (fun i => g i x))
      (Fin.cast h2.symm (rank ip.1))) (lineBit cb.1 cb.2)
    have hin : directProductInput (fun i => g i x) =
        fun j f => x (finProdFinEquiv (Fin.cast h2 j, f)) := by
      funext j f
      simp only [directProductInput, g, Equiv.symm_apply_apply]
    rw [hin] at h
    exact h
  obtain ⟨c, hc, hsize⟩ := Synthesis.exists_circuit_outputs
    (hsyn.mono Set.Subset.rfl hsub le_rfl)
  refine ⟨c, hc, hsize.trans ?_⟩
  exact size_bitonicSortCircuit_le (labelBit (D := D) (L := L) (s := s)) D true

/-- The phases with `2 ^ p, 2 ^ (p - 1), …, 1` pending requests accept every remaining request:
some circuit maps every good state with `2 ^ D - 2 ^ p` accepted records to a good state with all
records accepted, within `p + 1` phase budgets. -/
private theorem exists_phases_circuit (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (hmenu : ∀ k, 0 < k → k ≤ 2 ^ D → ∃ r, k * r ≤ 2 ^ D * (2 + 3 * (ℓ * b)) + 2 * k ∧
      ∃ menu : Fin r → Fin k → Fin ℓ → K, IsUniversalMenu (2 ^ D) menu)
    (hs : s < 2 ^ b) (p : ℕ) (hp : p ≤ D) :
    ∃ c : Circuit signature (2 ^ D * width D (ℓ * b) s) (2 ^ D * width D (ℓ * b) s),
      (∀ targets x, Good bits scalar targets (2 ^ D - arity p) x →
        Good bits scalar targets (2 ^ D) (c.eval interpretation x)) ∧
      c.size ≤ (p + 1) * (16384 * 2 ^ D * (s + 1) * (D + ℓ * b + b + 2) ^ 4) := by
  have hkD (q : ℕ) (hq : q ≤ D) : arity q ≤ 2 ^ D := by
    rw [arity_eq_two_pow]
    exact Nat.pow_le_pow_right (by decide) hq
  have hk1 (q : ℕ) : 0 < arity q := by
    rw [arity_eq_two_pow]
    exact Nat.two_pow_pos q
  -- One phase with `2 ^ q` pending requests.
  have phase (q : ℕ) (hq : q ≤ D) :
      ∃ c : Circuit signature (2 ^ D * width D (ℓ * b) s) (2 ^ D * width D (ℓ * b) s),
        (∀ targets x, Good bits scalar targets (2 ^ D - arity q) x →
          Good bits scalar targets (2 ^ D - arity q + (arity q + 1) / 2)
            (c.eval interpretation x)) ∧
        c.size ≤ 16384 * 2 ^ D * (s + 1) * (D + ℓ * b + b + 2) ^ 4 := by
    obtain ⟨r, hr, menu, hU⟩ := hmenu (arity q) (hk1 q) (hkD q hq)
    have hk : 2 ^ D - arity q + arity q = 2 ^ D := Nat.sub_add_cancel (hkD q hq)
    obtain ⟨c, hc, hsize⟩ := exists_next_circuit hk bits scalar menu
    refine ⟨c, fun targets x hx => ?_, hsize.trans (phaseCost_le hk hr hs)⟩
    rw [hc x]
    exact good_next bits scalar menu hU hx
  induction p with
  | zero =>
    obtain ⟨c, hc, hsize⟩ := phase 0 (Nat.zero_le D)
    refine ⟨c, fun targets x hx => ?_, by lia⟩
    have h := hc targets x hx
    have e : 2 ^ D - arity 0 + (arity 0 + 1) / 2 = 2 ^ D := by
      have := hkD 0 (Nat.zero_le D)
      simp only [arity] at this ⊢
      lia
    rwa [e] at h
  | succ p ih =>
    obtain ⟨c', hc', hsize'⟩ := ih (by lia)
    obtain ⟨c, hc, hsize⟩ := phase (p + 1) hp
    refine ⟨c'.comp c, fun targets x hx => ?_, ?_⟩
    · rw [Circuit.eval_comp]
      refine hc' targets _ ?_
      have h := hc targets x hx
      have e : 2 ^ D - arity (p + 1) + (arity (p + 1) + 1) / 2 = 2 ^ D - arity p := by
        have h1 := hkD (p + 1) hp
        have h2 : arity (p + 1) = arity p + arity p := rfl
        lia
      rwa [e] at h
    · rw [Circuit.size_comp]
      lia

end Scheduler

/-- The gate bound of the scheduler: `524288 * 2 ^ D * (s + 1) * (D + ℓ * b + 2) ^ 5`. -/
def schedulerBound (D ℓ b s : ℕ) : ℕ := 524288 * 2 ^ D * (s + 1) * (D + ℓ * b + 2) ^ 5

private theorem total_le {D L b s P F : ℕ} (hb : b ≤ L)
    (hP : P ≤ (D + 1) * (16384 * 2 ^ D * (s + 1) * (D + L + b + 2) ^ 4))
    (hF : F ≤ (D + 1) ^ 2 * 2 ^ D * (2 * D + 2 * Scheduler.width D L s + 1)) :
    2 + P + F ≤ 524288 * 2 ^ D * (s + 1) * (D + L + 2) ^ 5 := by
  set V := D + L + 2 with hV
  set n := 2 ^ D with hn
  have hV1 : 1 ≤ V := by lia
  have hn1 : 1 ≤ n := Nat.one_le_two_pow
  have hW : D + L + b + 2 ≤ 2 * V := by lia
  have hD : D + 1 ≤ V := by lia
  have hP' : P ≤ 262144 * n * (s + 1) * V ^ 5 :=
    calc P ≤ (D + 1) * (16384 * n * (s + 1) * (D + L + b + 2) ^ 4) := hP
      _ ≤ V * (16384 * n * (s + 1) * (2 * V) ^ 4) :=
          Nat.mul_le_mul hD (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW 4))
      _ = 262144 * n * (s + 1) * V ^ 5 := by ring
  have hwidth : 2 * D + 2 * Scheduler.width D L s + 1 ≤ 6 * ((s + 1) * V) := by
    have : s * L ≤ s * V := Nat.mul_le_mul_left _ (by lia)
    have : (s + 1) * V = s * V + V := by ring
    simp only [Scheduler.width]
    lia
  have hF' : F ≤ 6 * n * (s + 1) * V ^ 5 :=
    calc F ≤ (D + 1) ^ 2 * n * (2 * D + 2 * Scheduler.width D L s + 1) := hF
      _ ≤ V ^ 2 * n * (6 * ((s + 1) * V)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hD 2)) hwidth
      _ = 6 * n * (s + 1) * V ^ 3 := by ring
      _ ≤ 6 * n * (s + 1) * V ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hV1 (by decide))
  have h2 : 2 ≤ 2 * n * (s + 1) * V ^ 5 := by
    have : 0 < n * (s + 1) * V ^ 5 :=
      Nat.mul_pos (Nat.mul_pos hn1 (Nat.succ_pos s)) (Nat.pow_pos hV1)
    have e : 2 * n * (s + 1) * V ^ 5 = 2 * (n * (s + 1) * V ^ 5) := by ring
    lia
  have e1 : 524288 * n * (s + 1) * V ^ 5 = 262144 * n * (s + 1) * V ^ 5 +
      6 * n * (s + 1) * V ^ 5 + 2 * n * (s + 1) * V ^ 5 + 262136 * (n * (s + 1) * V ^ 5) := by
    ring
  lia

/-- **A near-linear scheduler circuit.** Given universal menus for every number `0 < k ≤ 2 ^ D`
of pending requests, of `r` entries with `k * r ≤ 2 ^ D * (2 + 3 ℓ b) + 2 k`, some De Morgan
circuit schedules `2 ^ D` requests: for all targets, repeated or not, it outputs in the
original order listed punctured lines through them with nonzero directions and pairwise disjoint
lines. Its size, counting every gate including constants, is at most `schedulerBound D ℓ b s`. -/
theorem exists_isScheduler (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (hmenu : ∀ k, 0 < k → k ≤ 2 ^ D → ∃ r, k * r ≤ 2 ^ D * (2 + 3 * (ℓ * b)) + 2 * k ∧
      ∃ menu : Fin r → Fin k → Fin ℓ → K, IsUniversalMenu (2 ^ D) menu) :
    ∃ c : Circuit signature (2 ^ D * (ℓ * b)) (2 ^ D * (s * (ℓ * b))),
      IsScheduler bits scalar c ∧ c.size ≤ schedulerBound D ℓ b s := by
  -- The scalars are the nonzero field elements, and the field has `2 ^ b` elements.
  have hs : s < 2 ^ b := by
    have h1 : s = Fintype.card {c : K // c ≠ 0} := by
      simpa using Fintype.card_congr scalar
    have h2 : Fintype.card K = 2 ^ b := by
      rw [Fintype.card_congr bits.toEquiv]
      simp
    rw [h1, ← h2]
    exact Fintype.card_subtype_lt (x := (0 : K)) (by simp)
  -- A universal menu has nonzero directions, so the points have a coordinate.
  have hℓ : 0 < ℓ := by
    obtain ⟨r, -, menu, hU⟩ := hmenu 1 one_pos Nat.one_le_two_pow
    obtain ⟨e, -⟩ := hU.2 (fun _ => none) (fun _ => 0)
    by_contra h
    obtain rfl : ℓ = 0 := by lia
    exact hU.1 e 0 (funext fun i => i.elim0)
  obtain ⟨cP, hP, hPsize⟩ := exists_phases_circuit bits scalar hmenu hs D le_rfl
  obtain ⟨cF, hF, hFsize⟩ := exists_finalOutput_circuit D (ℓ * b) s
  let cI := substituteCircuit (initialSubstitution D (ℓ * b) s)
  refine ⟨cF.comp (cP.comp cI), fun targets => ?_, ?_⟩
  · have h0 : Good bits scalar targets (2 ^ D - arity D)
        (cI.eval interpretation (targetBits bits targets)) := by
      rw [eval_substituteCircuit, arity_eq_two_pow, Nat.sub_self]
      exact good_initial bits scalar targets
    obtain ⟨dirs, hne, hdisj, heq⟩ := finalOutput_eq_lineBits bits scalar (hP targets _ h0)
    refine ⟨dirs, hne, hdisj, ?_⟩
    rw [Circuit.eval_comp, Circuit.eval_comp, hF]
    exact heq
  · rw [Circuit.size_comp, Circuit.size_comp, size_substituteCircuit, schedulerBound]
    exact total_le (Nat.le_mul_of_pos_left b hℓ) hPsize hFsize

end Cslib.Circuits.Boolean.MassProduction
