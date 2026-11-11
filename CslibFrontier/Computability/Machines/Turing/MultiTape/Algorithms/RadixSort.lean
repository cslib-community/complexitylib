/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists

/-!
# Uniform bounded-width radix sorting

A runtime width controls a fixed machine performing stable streaming bit
partitions. The loop preserves every key/payload occurrence and sorts all keys
fitting the supplied width. Resource bounds charge the binary loop control,
materialized lists and the peak per-record partition workspace.
-/

public section
namespace Turing.MultiTapeTM.RadixSort
open RadixPartition

/-- Increment the unary bit position after one real streaming partition. -/
def step (state : ℕ × List (ℕ × ℕ)) : ℕ × List (ℕ × ℕ) :=
  let (position, _) := state
  (position + 1, pass state)

/-- The loop is uniform in the runtime width; no width-dependent executable is advice. -/
def sort (input : ℕ × List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  let (width, rows) := input
  (step^[width] (0, rows)).2

/-- Every prefix has the actual round number and preserves all original occurrences. -/
theorem prefix_invariants (rows : List (ℕ × ℕ)) (j : ℕ) :
    (step^[j] (0, rows)).1 = j ∧ (step^[j] (0, rows)).2.Perm rows := by
  induction j with
  | zero => exact ⟨rfl, .refl _⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨by simp only [step, ih.1], (pass_perm _).trans ih.2⟩

private theorem remainder_next (n j : ℕ) :
    n % 2 ^ (j + 1) = n % 2 ^ j + if n.testBit j then 2 ^ j else 0 := by
  rw [Nat.pow_succ, Nat.mod_mul]
  have h := Nat.mod_lt (n / 2 ^ j) (by decide : 0 < 2)
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  split_ifs <;> simp_all

/-- A pass stably extends sortedness by one low-order bit. -/
theorem pass_sorted {rows : List (ℕ × ℕ)} {j : ℕ}
    (h : rows.Pairwise (fun a b => a.1 % 2 ^ j ≤ b.1 % 2 ^ j)) :
    (pass (j, rows)).Pairwise (fun a b => a.1 % 2 ^ (j + 1) ≤ b.1 % 2 ^ (j + 1)) := by
  rw [pass, List.pairwise_append]
  have same (bit : Bool) :
      (select bit (j, rows)).Pairwise
        (fun a b => a.1 % 2 ^ (j + 1) ≤ b.1 % 2 ^ (j + 1)) := by
    have hf := (h.filter (fun row => row.1.testBit j == bit))
    apply List.Pairwise.imp_of_mem _ hf
    intro a b ha hb hab
    have ha' : a.1.testBit j = bit := by simpa [select] using (List.mem_filter.mp ha).2
    have hb' : b.1.testBit j = bit := by simpa [select] using (List.mem_filter.mp hb).2
    simp only [remainder_next, ha', hb']
    omega
  refine ⟨same false, same true, ?_⟩
  intro a ha b hb
  have ha' : a.1.testBit j = false := by simpa [select] using (List.mem_filter.mp ha).2
  have hb' : b.1.testBit j = true := by simpa [select] using (List.mem_filter.mp hb).2
  have hm := Nat.mod_lt a.1 (Nat.two_pow_pos j)
  simp only [remainder_next, ha', hb', Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
  omega

/-- The actual loop is sorted by all bits it has visited, including width zero. -/
theorem prefix_sorted (rows : List (ℕ × ℕ)) (j : ℕ) :
    (step^[j] (0, rows)).2.Pairwise (fun a b => a.1 % 2 ^ j ≤ b.1 % 2 ^ j) := by
  induction j with
  | zero =>
    exact List.pairwise_of_forall (fun _ _ => by simp only [Nat.pow_zero, Nat.mod_one]; omega)
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change (pass (step^[j] (0, rows))).Pairwise _
    have hp := (prefix_invariants rows j).1
    have heq : (j, (step^[j] (0, rows)).2) = step^[j] (0, rows) :=
      Prod.ext hp.symm rfl
    rw [← heq]
    exact pass_sorted ih

/-- Sorting is exhaustive, with no traversal or ordering conclusion assumed. -/
theorem correct (input : ℕ × List (ℕ × ℕ))
    (fits : ∀ row ∈ input.2, row.1 < 2 ^ input.1) :
    (sort input).Perm input.2 ∧ (sort input).Pairwise (fun a b => a.1 ≤ b.1) := by
  refine ⟨(prefix_invariants input.2 input.1).2, ?_⟩
  apply List.Pairwise.imp_of_mem _ (prefix_sorted input.2 input.1)
  intro a b ha hb hab
  have ha' := fits a ((prefix_invariants input.2 input.1).2.mem_iff.mp ha)
  have hb' := fits b ((prefix_invariants input.2 input.1).2.mem_iff.mp hb)
  simpa only [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] using hab

/-- Physical binary key/payload widths bound the actual per-record workspace parameter. The
payload width is independent of the key width, so packed indices are explicitly charged. -/
theorem wire_bounds (input : ℕ × List (ℕ × ℕ)) (payloadWidth : ℕ)
    (fits : ∀ row ∈ input.2, row.1 < 2 ^ input.1 ∧ row.2 < 2 ^ payloadWidth) :
    streamFilterWidth encUnary recordEncoding input ≤ 3 * input.1 + payloadWidth + 2 ∧
      (inputEncoding input).length ≤ 2 * input.1 + 1 +
        input.2.length * (4 * input.1 + 2 * payloadWidth + 3) := by
  have record (row : ℕ × ℕ) (hr : row ∈ input.2) :
      (recordEncoding row).length ≤ 2 * input.1 + 1 + payloadWidth := by
    obtain ⟨hk, hv⟩ := fits row hr
    have hk' : (encNat row.1).length ≤ input.1 := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr hk
    have hv' : (encNat row.2).length ≤ payloadWidth := by
      simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr hv
    simp only [recordEncoding, length_encPair]
    omega
  have hmax : streamRecordLength recordEncoding input.2 ≤
      2 * input.1 + 1 + payloadWidth := listMax_le record
  have listwire : (encList recordEncoding input.2).length ≤
      input.2.length * (4 * input.1 + 2 * payloadWidth + 3) := by
    have bound (rows : List (ℕ × ℕ)) (sub : ∀ row ∈ rows, row ∈ input.2) :
        (encList recordEncoding rows).length ≤
          rows.length * (4 * input.1 + 2 * payloadWidth + 3) := by
      induction rows with
      | nil => simp
      | cons row rows ih =>
        have hr := record row (sub row (by simp))
        have ht := ih (fun r h => sub r (by simp [h]))
        simp only [encList_cons, List.length_append, length_frame, List.length_cons]
        nlinarith
    exact bound input.2 (fun _ h => h)
  constructor
  · simp only [streamFilterWidth, encUnary_apply, List.length_replicate]
    omega
  · simp only [inputEncoding, length_encPair, encUnary_apply, List.length_replicate]
    omega

/-- One uniform multitape sorter, with a polynomial width budget and linear record-count factor.
The peak-space bound charges input/output, all loop buffers, counter conversion and every
partition's internal workspace. No sortedness, traversal, time or space conclusion is a premise. -/
theorem computable :
    ∃ Q : ℕ → ℕ, Cslib.PolynomiallyBounded Q ∧ Monotone Q ∧
      ComputableInO sort inputEncoding (encList recordEncoding)
        (fun input => (input.1 + 1) * ((inputEncoding input).length +
          (input.2.length + 1) * Q (streamFilterWidth encUnary recordEncoding input)))
        (fun input => (inputEncoding input).length +
          Q (streamFilterWidth encUnary recordEncoding input)) := by
  obtain ⟨P, hP, hmP, hpass⟩ := pass_computable
  let convertClock := Cslib.GenericRAM.NativeCertificate.ofPolyTime
    ComputableInPolyTime.unary_to_binary
  obtain ⟨R, hR, hmR, hr⟩ := Cslib.GenericRAM.exists_mono_poly_cert
    ComputableInPolyTime.unary_to_binary
  let Q : ℕ → ℕ := fun B => P B + R B + (B + 1) ^ 2 + 10
  have hQ : Cslib.PolynomiallyBounded Q := by dsimp only [Q]; fun_prop
  have hmQ : Monotone Q := fun a b hab => by
    have := hmP hab
    have := hmR hab
    have := Nat.pow_le_pow_left (Nat.add_le_add_right hab 1) 2
    dsimp only [Q]
    omega
  let hid : Cslib.GenericRAM.NativeCertificate
      (id : ℕ × List (ℕ × ℕ) → _) inputEncoding inputEncoding :=
    .linear (.of_eq (fun _ => rfl))
  let initial := Cslib.GenericRAM.NativeCertificate.prod
    (Cslib.GenericRAM.NativeCertificate.const (em := encUnary) 0)
    (Cslib.GenericRAM.NativeCertificate.snd hid)
  let clock := convertClock.comp (Cslib.GenericRAM.NativeCertificate.fst hid)
  have hstep := ((ComputableInO.unarySucc').comp_linear
    (ComputableInO.fst encUnary (encList recordEncoding))).prod hpass
  let round : Cslib.GenericRAM.NativeCertificate step inputEncoding inputEncoding :=
    ⟨fun input => 3 * (inputEncoding input).length + (input.2.length + 1) *
        P (streamFilterWidth encUnary recordEncoding input),
      fun input => 3 * (inputEncoding input).length +
        P (streamFilterWidth encUnary recordEncoding input), by
      convert hstep using 1 <;> first | rfl | (funext input; dsimp only [inputEncoding]; ring)⟩
  let loop := Cslib.GenericRAM.NativeCertificate.iterate clock initial round
  have output := (Cslib.GenericRAM.NativeCertificate.snd loop).computes
  refine ⟨Q, hQ, hmQ, ?_⟩
  refine output.mono 16 ?_ ?_
  all_goals intro input
  all_goals
    let I := (inputEncoding input).length
    let B := streamFilterWidth encUnary recordEncoding input
    have hwidth : input.1 ≤ B := by
      dsimp only [B, streamFilterWidth]
      simp only [encUnary_apply, List.length_replicate]
      omega
    have hclock : (encNat input.1).length ≤ input.1 := by
      rw [encNat_apply, Nat.size_eq_bits_len]
      exact Nat.size_le.mpr Nat.lt_two_pow_self
    have hct := (hr input.1).1.trans (hmR (show (encUnary input.1).length ≤ B by
      simpa only [encUnary_apply, List.length_replicate] using hwidth))
    have hcs := (hr input.1).2.trans (hmR (show (encUnary input.1).length ≤ B by
      simpa only [encUnary_apply, List.length_replicate] using hwidth))
    change convertClock.time input.1 ≤ R B at hct
    change convertClock.space input.1 ≤ R B at hcs
    have state_bounds (j : ℕ) (hj : j ≤ input.1) :
        (inputEncoding (step^[j] (0, input.2))).length ≤ I ∧
        streamFilterWidth encUnary recordEncoding (step^[j] (0, input.2)) ≤ B ∧
        (step^[j] (0, input.2)).2.length = input.2.length := by
      have hp := prefix_invariants input.2 j
      have wire := (List.Perm.flatMap_right (fun row => frame (recordEncoding row))
        hp.2).length_eq
      have maxwire : streamRecordLength recordEncoding (step^[j] (0, input.2)).2 ≤
          streamRecordLength recordEncoding input.2 := by
        apply listMax_le
        intro row hrow
        exact le_listMax (f := fun row => (recordEncoding row).length)
          (hp.2.mem_iff.mp hrow)
      have hw : (encList recordEncoding (step^[j] (0, input.2)).2).length =
          (encList recordEncoding input.2).length := wire
      refine ⟨?_, ?_, hp.2.length_eq⟩
      · dsimp only [I, inputEncoding]
        simp only [length_encPair, encUnary_apply, List.length_replicate, hp.1, hw]
        omega
      · dsimp only [B, streamFilterWidth]
        simp only [encUnary_apply, List.length_replicate, hp.1]
        omega
    have hrt : Cslib.GenericRAM.NativeCertificate.maxRoundTime round input.1
        (0, input.2) ≤ 3 * I + (input.2.length + 1) * P B := by
      apply Cslib.GenericRAM.NativeCertificate.maxRoundTime_le
      intro j hj
      obtain ⟨hi, hb, hn⟩ := state_bounds j hj
      have hm := Nat.mul_le_mul_left (input.2.length + 1) (hmP hb)
      dsimp only [round]
      rw [hn]
      omega
    have hrs : Cslib.GenericRAM.NativeCertificate.maxRoundSpace round input.1
        (0, input.2) ≤ 3 * I + P B := by
      apply Cslib.GenericRAM.NativeCertificate.maxRoundSpace_le
      intro j hj
      obtain ⟨hi, hb, _⟩ := state_bounds j hj
      have hm := hmP hb
      dsimp only [round]
      omega
    have hlen : Cslib.GenericRAM.NativeCertificate.maxStateLength inputEncoding step input.1
        (0, input.2) ≤ I :=
      Cslib.GenericRAM.NativeCertificate.maxStateLength_le _ _ _ _
        (fun j hj => (state_bounds j hj).1)
    have hpq : P B ≤ Q B := by dsimp only [Q]; omega
    have hrq : R B ≤ Q B := by dsimp only [Q]; omega
    have hcq : ((encNat input.1).length + 1) ^ 2 ≤ Q B := by
      have := Nat.pow_le_pow_left (by omega : (encNat input.1).length + 1 ≤ B + 1) 2
      dsimp only [Q]
      omega
    have hbq : B ≤ Q B := by dsimp only [Q]; nlinarith
  · change clock.time input + initial.time input +
      (input.1 + 1) * (_ + _ + _) ≤ _
    have hinner : Cslib.GenericRAM.NativeCertificate.maxRoundTime round input.1
        (0, input.2) +
        Cslib.GenericRAM.NativeCertificate.maxStateLength inputEncoding step input.1
          (0, input.2) + ((encNat input.1).length + 1) ^ 2 ≤
        4 * I + (input.2.length + 1) * Q B + Q B := by
      have := Nat.mul_le_mul_left (input.2.length + 1) hpq
      omega
    have hmul := Nat.mul_le_mul_left (input.1 + 1) hinner
    have hsmall := Nat.mul_le_mul_left (input.1 + 1)
      (show Q B ≤ (input.2.length + 1) * Q B by nlinarith)
    simp only [clock, initial, Cslib.GenericRAM.NativeCertificate.comp_time,
      Cslib.GenericRAM.NativeCertificate.prod_time,
      Cslib.GenericRAM.NativeCertificate.const_time,
      hid]
    change I + convertClock.time input.1 + (I + I) +
      (input.1 + 1) * (Cslib.GenericRAM.NativeCertificate.maxRoundTime round input.1
        (0, input.2) + Cslib.GenericRAM.NativeCertificate.maxStateLength inputEncoding step
          input.1 (0, input.2) + ((encNat input.1).length + 1) ^ 2) ≤
      16 * ((input.1 + 1) * (I + (input.2.length + 1) * Q B) + 1)
    nlinarith
  · change clock.space input + initial.space input + _ + _ + _ ≤ _
    simp only [clock, initial, Cslib.GenericRAM.NativeCertificate.comp_space,
      Cslib.GenericRAM.NativeCertificate.prod_space,
      Cslib.GenericRAM.NativeCertificate.const_space,
      hid]
    change I + convertClock.space input.1 + (I + I) +
      Cslib.GenericRAM.NativeCertificate.maxRoundSpace round input.1 (0, input.2) +
      Cslib.GenericRAM.NativeCertificate.maxStateLength inputEncoding step input.1 (0, input.2) +
      (encNat input.1).length ≤ 16 * (I + Q B + 1)
    omega

end Turing.MultiTapeTM.RadixSort
