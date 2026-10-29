/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Tactic.PolyTime.Init
public import Mathlib.Data.Nat.Sqrt
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-time integer square roots on binary naturals

`Nat.sqrt m` (`⌊√m⌋`) is computable in polynomial time over `Turing.MultiTapeTM.encNat` by a
most-significant-bit-first fold over `m.size` bit positions: at position `i`, the candidate bit
`2 ^ i` is added to the running root `acc` whenever `(acc + 2 ^ i) ^ 2 ≤ m`. Every intermediate
accumulator satisfies `acc ^ 2 ≤ m`, hence `acc ≤ m` and `(encNat acc).length ≤ (encNat m).length`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.binary_sqrt`, `.binary_sqrt'`: plain polynomial-time
  floor square root `Nat.sqrt` over `encNat`.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_ceilSqrt`, `.binary_ceilSqrt'`: plain
  polynomial-time integer ceiling square root `if m = 0 then 0 else (m - 1).sqrt + 1` over `encNat`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

section Internal

open ComputableTidilyInPolyTime

private abbrev isqrtStep (m acc i : ℕ) : ℕ :=
  let cand := acc + 2 ^ i
  if decide (cand * cand ≤ m) then cand else acc

private theorem isqrtStep_sq_le {m acc i : ℕ} (h : acc * acc ≤ m) :
    isqrtStep m acc i * isqrtStep m acc i ≤ m := by
  unfold isqrtStep; dsimp only
  split_ifs with hcand
  · simpa only [decide_eq_true_eq] using hcand
  · exact h

private theorem foldl_isqrtStep_sq_le (m : ℕ) :
    ∀ (l : List ℕ) {acc : ℕ}, acc * acc ≤ m →
      l.foldl (isqrtStep m) acc * l.foldl (isqrtStep m) acc ≤ m
  | [], _, h => h
  | _ :: l, _, h => foldl_isqrtStep_sq_le m l (isqrtStep_sq_le h)

private theorem foldl_isqrtStep_bounds (m : ℕ) :
    ∀ (k acc : ℕ), acc * acc ≤ m → m < (acc + 2 ^ k) * (acc + 2 ^ k) →
      let r := (List.range k).reverse.foldl (isqrtStep m) acc
      r * r ≤ m ∧ m < (r + 1) * (r + 1)
  | 0, acc, hle, hlt => by
    simpa only [List.range_zero, List.reverse_nil, List.foldl_nil, pow_zero] using ⟨hle, hlt⟩
  | k + 1, acc, hle, hlt => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    unfold isqrtStep; dsimp only
    split_ifs with hcand
    · refine foldl_isqrtStep_bounds m k (acc + 2 ^ k)
        (by simpa only [decide_eq_true_eq] using hcand) ?_
      rw [Nat.add_assoc, ← hpow]; exact hlt
    · exact foldl_isqrtStep_bounds m k acc hle
        (Nat.lt_of_not_ge (by simpa only [decide_eq_true_eq] using hcand))

private theorem foldl_isqrtStep_eq_sqrt (m : ℕ) :
    (List.range m.size).reverse.foldl (isqrtStep m) 0 = m.sqrt := by
  have hlt_pow : m < 2 ^ m.size := Nat.lt_size_self m
  have hpow_pos : 1 ≤ 2 ^ m.size := Nat.one_le_two_pow
  obtain ⟨hle, hlt⟩ := foldl_isqrtStep_bounds m m.size 0 (Nat.zero_le m) (by nlinarith)
  exact le_antisymm (Nat.le_sqrt.mpr hle)
    (Nat.lt_succ_iff.mp (Nat.sqrt_lt'.mpr (by simpa only [sq] using hlt)))

private theorem tidy_binary_sqrt : ComputableTidilyInPolyTime Nat.sqrt encNat encNat := by
  have hlist : ComputableTidilyInPolyTime (fun m : ℕ => (List.range m.size).reverse)
      encNat (encList encUnary) :=
    (listReverse encUnary).comp (range.comp ComputableInPolyTime.binary_size.tidy)
  have hstep : ComputableTidilyInPolyTime
      (fun p : (ℕ × ℕ) × ℕ => isqrtStep p.1.1 p.1.2 p.2)
      (encPair (encPair encNat encNat) encUnary) encNat := by
    unfold isqrtStep; fun_prop
  have hfold := foldlWith (encP := encNat) (encA := encUnary) (encL := encList encUnary)
    (encB := encNat) (par := id) (list := fun m => (List.range m.size).reverse)
    (init := fun _ => 0) (step := isqrtStep) id' hlist (const 0) hstep
    (B := fun m => (encNat m).length) .self fun m j _ => by
      set acc := ((List.range m.size).reverse.take j).foldl (isqrtStep m) 0
      have hsq : acc * acc ≤ m := foldl_isqrtStep_sq_le m _ (Nat.zero_le m)
      have hacc_le : acc ≤ m := by
        rcases Nat.eq_zero_or_pos acc with h0 | hpos
        · omega
        · nlinarith
      change acc.bits.length ≤ m.bits.length
      rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
      exact Nat.size_le_size hacc_le
  exact hfold.of_enc_eq fun m => congrArg encNat (foldl_isqrtStep_eq_sqrt m).symm

private theorem tidy_binary_ceilSqrt :
    ComputableTidilyInPolyTime (fun m : ℕ => if m = 0 then 0 else (m - 1).sqrt + 1)
      encNat encNat := by
  have hcond : ComputableTidilyInPolyTime
      (fun m : ℕ => if decide (m ≤ 0) then 0 else (m - 1).sqrt + 1) encNat encNat :=
    (binary_le' id' (const 0)).ite' (const 0)
      (binary_add' (tidy_binary_sqrt.comp (binary_sub' id' (const 1))) (const 1))
  refine hcond.of_enc_eq fun m => congrArg encNat ?_
  simp only [Nat.le_zero, decide_eq_true_eq]

end Internal

namespace ComputableInPolyTime

/-- Integer floor square root `Nat.sqrt` is polynomial-time on binary naturals. -/
@[fun_prop, program_certificate]
theorem binary_sqrt : ComputableInPolyTime Nat.sqrt encNat encNat :=
  .of_tidy tidy_binary_sqrt

/-- Integer floor square root of a computed binary natural. -/
theorem binary_sqrt' {α : Type} {input : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f input encNat) :
    ComputableInPolyTime (fun a => (f a).sqrt) input encNat :=
  binary_sqrt.comp hf

/-- Integer ceiling square root `if m = 0 then 0 else (m - 1).sqrt + 1` is polynomial-time on
binary naturals. -/
theorem binary_ceilSqrt :
    ComputableInPolyTime (fun m : ℕ => if m = 0 then 0 else (m - 1).sqrt + 1) encNat encNat :=
  .of_tidy tidy_binary_ceilSqrt

/-- Integer ceiling square root of a computed binary natural. -/
theorem binary_ceilSqrt' {α : Type} {input : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f input encNat) :
    ComputableInPolyTime (fun a => if f a = 0 then 0 else (f a - 1).sqrt + 1) input encNat :=
  binary_ceilSqrt.comp hf

end ComputableInPolyTime

end Turing.MultiTapeTM
