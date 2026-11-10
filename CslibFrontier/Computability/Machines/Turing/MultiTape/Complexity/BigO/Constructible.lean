/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bound
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Foundations.Data.Nat.Bits.Halving
import CslibFrontier.Foundations.Data.Nat.Doubling
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Foundations.Data.Nat.RecursionTree
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.Tactic.EncLen

/-!
# Lengths, comparisons and unary conversion within given bounds

Routines that compute resource bounds from an input, with computability up to constants
(`Turing.MultiTapeTM.ComputableInO`): the length of a bit word in binary, the comparison of two
unary numbers, and conversions between unary and binary. They are the building blocks of
constructible resource bounds, of padding arguments and of the diagonal machines of the hierarchy
theorems.

The conversions are linear. From unary to binary, a counter is halved once per round and the parity
of each nonzero value is emitted; the rounds cost `n + n / 2 + ⋯ = O(n)`. From binary to unary, the
digits are read least significant first while a unary place value doubles, and the place value is
emitted at each digit one; round `i` costs `O(2 ^ i)`. The number of binary digits of `m` is
logarithmic in `m`, so every power of it is `O(m + 1)`; this absorbs binary counters into bounds
linear in the counted value.

## Main results

* `Turing.MultiTapeTM.two_pow_length_encNat_le`: the binary digits of `m` are logarithmic.
* `Turing.MultiTapeTM.exists_pow_length_encNat_le`: every power of the number of binary digits of
  `m` is `O(m + 1)`.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.unary_div_two`: halving a unary number, in
  linear time and zero work space.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.unary_nil`: reading a unary number and emitting
  nothing, in linear time and zero work space.
* `Turing.MultiTapeTM.ComputableInO.unaryToNat`: from unary to binary, within linear time and space.
* `Turing.MultiTapeTM.ComputableInO.lengthNat`: the length of a bit word in binary, within linear
  time and space.
* `Turing.MultiTapeTM.ComputableInO.unaryLe`: the comparison of unary numbers, within
  quadratic time and linear space.
* `Turing.MultiTapeTM.ComputableInO.natToUnary`: from binary to unary, within linear time and space.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- The binary digits of `m` are logarithmic: `2 ^ (encNat m).length ≤ 2 * (m + 1)`. -/
theorem two_pow_length_encNat_le (m : ℕ) : 2 ^ (encNat m).length ≤ 2 * (m + 1) := by
  rw [encNat_apply, Nat.size_eq_bits_len]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h₁ : 2 ^ (m.size - 1) ≤ m := Nat.lt_size.mp (by
      have := Nat.size_pos.mpr hm
      omega)
    have h₂ : 1 ≤ m.size := Nat.size_pos.mpr hm
    rw [show m.size = (m.size - 1) + 1 by omega, pow_succ]
    omega

/-- Every power of the number of binary digits of `m` is `O(m + 1)`. -/
theorem exists_pow_length_encNat_le (d : ℕ) :
    ∃ C, ∀ m, ((encNat m).length + 1) ^ d ≤ C * (m + 1) := by
  obtain ⟨C, hC⟩ := Cslib.PolynomiallyBounded.exists_le_mul_two_pow (p := fun L => (L + 1) ^ d)
    (by fun_prop)
  refine ⟨2 * C, fun m => (hC _).trans ?_⟩
  calc C * 2 ^ (encNat m).length ≤ C * (2 * (m + 1)) :=
        Nat.mul_le_mul_left _ (two_pow_length_encNat_le m)
    _ = 2 * C * (m + 1) := by ring

/-! ### Conversions between unary and binary, in linear time -/

/-- The transducer halving a unary number: it keeps every second bit. -/
private def halveT : Transducer Bool Bool where
  q₀ := false
  step q _ := (!q, if q then [true] else [])
  final _ := []
  length_step_le q _ := by cases q <;> simp
  length_final_le _ := by simp

private lemma run_halveT (q : Bool) (k : ℕ) :
    halveT.run q (List.replicate k true) = List.replicate ((k + q.toNat) / 2) true := by
  induction k generalizing q with
  | zero => cases q <;> rfl
  | succ k ih =>
    rw [List.replicate_succ, Transducer.run_cons, ih]
    cases q
    · simp only [halveT, Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.nil_append,
        Bool.toNat_true, Bool.toNat_false]
    · have e : (k + 1 + Bool.toNat true) / 2 = (k + Bool.toNat false) / 2 + 1 := by grind
      rw [e, List.replicate_succ]
      rfl

/-- The transducer emitting `Nat.halfBit` of a unary number: its parity, if it is positive. The
state records whether a bit was read and the parity so far. -/
private def halfBitT : Transducer Bool (Bool × Bool) where
  q₀ := (false, false)
  step q _ := ((true, !q.2), [])
  final q := if q.1 then [q.2] else []
  length_step_le _ _ := by simp
  length_final_le q := by cases q.1 <;> simp

private lemma run_halfBitT (p : Bool) (k : ℕ) :
    halfBitT.run (true, p) (List.replicate k true) = [p ^^ decide (k % 2 = 1)] := by
  induction k generalizing p with
  | zero => simp [halfBitT]
  | succ k ih =>
    rw [List.replicate_succ, Transducer.run_cons]
    change [] ++ halfBitT.run (true, !p) (List.replicate k true) = _
    rw [ih, List.nil_append]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> cases p <;>
      simp [Nat.succ_mod_two_eq_one_iff, h]

/-- The transducer emitting nothing. -/
private def silentT : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private lemma run_silentT (w : List Bool) : silentT.run () w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih => exact ih

/-- Halving a unary number, by a finite-state transducer, in linear time and zero work space. -/
theorem ComputableTidilyInTimeAndSpace.unary_div_two :
    ComputableTidilyInTimeAndSpace (· / 2) encUnary encUnary
      (fun k => 4 * (encUnary k).length + 8) fun _ => 0 :=
  halveT.computableTidilyInTimeAndSpace fun k => by
    rw [encUnary_apply, encUnary_apply, run_halveT]
    rfl

/-- Reading a unary number and emitting nothing, in linear time and zero work space. -/
theorem ComputableTidilyInTimeAndSpace.unary_nil :
    ComputableTidilyInTimeAndSpace (fun _ : ℕ => ([] : List Bool)) encUnary encBits
      (fun k => 4 * (encUnary k).length + 8) fun _ => 0 :=
  silentT.computableTidilyInTimeAndSpace fun _ => (run_silentT _).symm

/-- Emitting `Nat.halfBit` of a unary number, in linear time and zero work space. -/
private theorem computableTidilyInTimeAndSpace_halfBit :
    ComputableTidilyInTimeAndSpace Nat.halfBit encUnary encBits
      (fun k => 4 * (encUnary k).length + 8) fun _ => 0 :=
  halfBitT.computableTidilyInTimeAndSpace fun k => by
    rw [encUnary_apply, encBits_apply]
    rcases k with _ | k
    · rfl
    · rw [List.replicate_succ, Transducer.run_cons]
      change Nat.halfBit (k + 1) = [] ++ halfBitT.run (true, true) (List.replicate k true)
      rw [run_halfBitT, List.nil_append]
      rcases Nat.mod_two_eq_zero_or_one k with h | h <;>
        simp [Nat.halfBit, Nat.succ_mod_two_eq_one_iff, h]

/-- Repeated halving with emission: from `(n, m)` in unary, `m` rounds halve `n` and emit
`Nat.halfBit` of each value, in time `O(n + m)` and zero work space beyond the counter. -/
private theorem computableTidilyInO_halfBits :
    ComputableTidilyInO
      (fun x : ℕ × ℕ => ((List.range x.2).map fun i => Nat.halfBit ((· / 2)^[i] x.1)).flatten ++
        ([] : List Bool))
      (encPair encUnary encUnary) encBits (fun x => x.1 + x.2) fun x => x.1 + x.2 := by
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.iterate_unary_stream_sum
    ComputableTidilyInTimeAndSpace.unary_div_two computableTidilyInTimeAndSpace_halfBit
    ComputableTidilyInTimeAndSpace.unary_nil
    (R := fun x i => 17 * (x.1 / 2 ^ i) + 17) (Q := fun _ => 0) (B := fun x => x.1)
    (fun x i _ => by
      simp only [encUnary_apply, List.length_replicate, Nat.iterate_div_two]
      have : x.1 / 2 ^ (i + 1) ≤ x.1 / 2 ^ i :=
        Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ i)) (by positivity)
      omega)
    (fun _ _ _ => le_rfl)
    (fun x i _ => by
      simp only [encUnary_apply, List.length_replicate, Nat.iterate_div_two]
      exact Nat.div_le_self _ _)
  have ht (x : ℕ × ℕ) :
      4 * (encUnary ((· / 2)^[x.2] x.1)).length + 8 +
        (∑ i ∈ Finset.range x.2, (17 * (x.1 / 2 ^ i) + 17)) + x.1 + 1 ≤
        50 * (x.1 + x.2 + 1) := by
    have hs := Nat.sum_div_two_pow_le x.1 x.2
    have hq : x.1 / 2 ^ x.2 ≤ x.1 := Nat.div_le_self _ _
    simp only [encUnary_apply, List.length_replicate, Nat.iterate_div_two, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  refine ComputableTidilyInO.of_bounds h (50 * c + 50) (fun x => ?_) (fun x => ?_) fun x => ?_
  · calc c * (4 * (encUnary ((· / 2)^[x.2] x.1)).length + 8 +
          (∑ i ∈ Finset.range x.2, (17 * (x.1 / 2 ^ i) + 17)) + x.1 + 1)
        ≤ c * (50 * (x.1 + x.2 + 1)) := Nat.mul_le_mul_left c (ht x)
      _ ≤ (50 * c + 50) * (x.1 + x.2 + 1) := by nlinarith
  · nlinarith
  · calc _ ≤ c * (4 * (encUnary ((· / 2)^[x.2] x.1)).length + 8 +
          (∑ i ∈ Finset.range x.2, (17 * (x.1 / 2 ^ i) + 17)) + x.1 + 1) := h.length_le x
      _ ≤ c * (50 * (x.1 + x.2 + 1)) := Nat.mul_le_mul_left c (ht x)
      _ ≤ (50 * c + 50) * (x.1 + x.2 + 1) := by nlinarith

namespace ComputableInO

/-- **From unary to binary**, by repeated halving, within linear time and space. Round `i` halves
the counter `n / 2 ^ i` and emits its parity while it is positive (`Nat.flatten_map_range_halfBit`),
so the rounds cost `O(n)` in total. -/
theorem unaryToNat : ComputableInO (fun n : ℕ => n) encUnary encNat (fun n => n) fun n => n := by
  have hd : ComputableTidilyInO (fun n : ℕ => (n, n)) encUnary (encPair encUnary encUnary)
      (fun n => n + n) fun n => n + n := by
    have hid : ComputableTidilyInO (fun n : ℕ => n) encUnary encUnary (fun n => n) fun n => n :=
      (ComputableTidilyInO.of_linear (.of_eq fun _ => rfl)).mono 1
        (fun n => by simp only [encUnary_apply, List.length_replicate]; omega)
        fun n => by simp only [encUnary_apply, List.length_replicate]; omega
    exact hid.prod hid
  refine ((computableTidilyInO_halfBits.comp hd).of_enc_eq (g := fun n : ℕ => n)
    (encOut := encNat) fun n => ?_).mono 4 (fun n => ?_) (fun n => ?_) |>.computableInO
  · simp only [encNat_apply, encBits_apply, Function.comp_apply, List.append_nil]
    exact (Nat.flatten_map_range_halfBit le_rfl).symm
  all_goals dsimp only; omega

/-- The length of a bit word in binary, within linear time and space: the word is measured in
unary and converted by `Turing.MultiTapeTM.ComputableInO.unaryToNat`. -/
theorem lengthNat : ComputableInO (fun l : List Bool => l.length) encBits encNat
    (fun l => l.length) fun l => l.length :=
  (unaryToNat.comp lengthUnary).mono 2 (fun l => by omega) fun l => by omega

/-- The comparison of unary numbers, by counting down, within quadratic time and linear space. -/
theorem unaryLe : ComputableInO (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encUnary encUnary) encBool (fun p => ((encPair encUnary encUnary p).length + 1) ^ 2)
    fun p => (encPair encUnary encUnary p).length + 1 := by
  have hstep :=
    ComputableTidilyInDegree.unary_pred.inO_one.computableInO.comp (fst encUnary encBool)
  have hrep (a b : ℕ) : (List.replicate b true).foldl (fun n _ => n - 1) a = a - b := by
    induction b generalizing a with
    | zero => rfl
    | succ b ih => rw [List.replicate_succ, List.foldl_cons, ih]; omega
  have h := foldl (encA := encBool) (encL := encBits) (encB := encUnary)
    (list := fun p : ℕ × ℕ => List.replicate p.2 true) (init := fun p => p.1)
    (step := fun n _ => n - 1)
    ((of_linear (.of_eq (f := fun n => List.replicate n true) (encIn := encUnary)
      (encMid := encBits) fun _ => rfl)).comp (snd encUnary encUnary))
    (fst encUnary encUnary) hstep
    (R := fun p => 3 * ((encPair encUnary encUnary p).length + 1))
    (Q := fun p => 3 * ((encPair encUnary encUnary p).length + 1))
    (B := fun p => (encPair encUnary encUnary p).length)
    (fun p i hi => by
      rw [List.take_replicate, hrep]
      simp only [length_encPair, encUnary_apply, List.length_replicate,
        encBool_apply, List.length_singleton]
      omega)
    (fun p i hi => by
      rw [List.take_replicate, hrep]
      simp only [length_encPair, encUnary_apply, List.length_replicate,
        encBool_apply, List.length_singleton]
      omega)
    (fun p i hi => by
      rw [List.take_replicate, hrep]
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega)
  have hz := ComputableTidilyInDegree.unary_isZero.inO_one.computableInO.comp_linear h
  refine (hz.mono 16 (fun p => ?_) fun p => ?_).of_enc_eq fun p => ?_
  · simp only [length_encPair, encUnary_apply, List.length_replicate,
      encBits_apply]
    nlinarith
  · enc_len
  · simp only [Function.comp_apply, hrep, Nat.sub_eq_zero_iff_le]

end ComputableInO

/-- Doubling a unary place value on every digit and emitting it at every digit one writes the
number with those little-endian digits, scaled by the initial place value. -/
private theorem streamEmit_double (s : ℕ) (l : List Bool) :
    streamEmit (fun p : ℕ × Bool => p.1 + p.1)
      (fun p => List.replicate (if p.2 then p.1 else 0) true) s l =
      List.replicate (s * l.foldr Nat.bit 0) true := by
  induction l generalizing s with
  | nil => simp [streamEmit]
  | cons b l ih =>
    rw [streamEmit, ih, ← List.replicate_add, List.foldr_cons]
    congr 1
    cases b <;> simp only [Nat.bit_true, Nat.bit_false, ↓reduceIte, Bool.false_eq_true] <;> ring

/-- **From binary to unary**, within linear time and space. The digits are read least
significant first while a unary place value `2 ^ i` doubles, and the place value is emitted at
every digit one. Round `i` costs `O(2 ^ i)`, so the rounds cost `O(n + 1)` in total. -/
theorem ComputableInO.natToUnary : ComputableInO (fun n : ℕ => n) encNat encUnary
    (fun n => n) fun n => n := by
  obtain ⟨ci, hi⟩ := computableInTimeAndSpace_of_const (encIn := encNat) (encOut := encUnary) 1
  obtain ⟨ce, he⟩ := computableInTimeAndSpace_of_const
    (encIn := encUnary) (encOut := encBits) ([] : List Bool)
  obtain ⟨c₀, hstep, -⟩ := ((ComputableInDegree.unaryAdd (ComputableInDegree.fst encUnary encBool)
    (ComputableInDegree.fst encUnary encBool) le_rfl le_rfl).inO_one).tidy
  have hemit : ComputableTidilyInO (fun p : ℕ × Bool => if p.2 then p.1 else 0)
      (encPair encUnary encBool) encUnary (fun p => (encPair encUnary encBool p).length)
      fun p => (encPair encUnary encBool p).length :=
    ((ComputableTidilyInO.snd encUnary encBool).ite (ComputableTidilyInO.fst encUnary encBool)
      (ComputableTidilyInO.const 0)).mono 2 (fun p => by split_ifs <;> omega)
      fun p => by split_ifs <;> omega
  obtain ⟨c₁, hemit, -⟩ := hemit
  have hstate (n j : ℕ) (hj : j ≤ (encNat n).length) :
      streamState 1 (fun p : ℕ × Bool => p.1 + p.1) (encNat n) j = 2 ^ j := by
    rw [streamState, List.foldl_add_self_eq_mul_two_pow, List.length_take, Nat.min_eq_left hj,
      one_mul]
  obtain ⟨D, hD⟩ : ∃ D, D = 3 * c₀ + 3 * c₁ + 8 := ⟨_, rfl⟩
  let reader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩
  obtain ⟨K, hK⟩ := ComputableTidilyInTimeAndSpace.streamFold_sum (g := fun n : ℕ => n)
    (encOut := encUnary) (encS := encUnary) (encA := encBool) (encE := encUnary) (encF := encBits)
    reader (fun b => [b]) (fun _ => List.cons_ne_nil _ _)
    (fun a rest => by simp [reader, InputReader.read])
    (fun n => encNat n) (fun n => by simp)
    (init := fun _ => 1) (next := fun p => p.1 + p.1) (emit := fun p => if p.2 then p.1 else 0)
    (finish := fun _ => ([] : List Bool))
    hi.computableTidilyInTimeAndSpace hstep hemit he.computableTidilyInTimeAndSpace
    (fun n => by
      simp only [encUnary_apply, encBits_apply, List.append_nil]
      rw [streamEmit_double, one_mul, encNat_apply, Nat.foldr_bit_bits])
    (roundCost := fun _ j => D * (2 ^ j + 1)) (sMax := fun n => D * (2 ^ (encNat n).length + 1))
    (lMax := fun n => 2 ^ (encNat n).length + 1)
    (fun n j hj => by
      have h₁ := hstate n j hj.le
      have h₂ := hstate n (j + 1) hj
      simp only [length_encPair, encUnary_apply, encBool_apply, List.length_singleton,
        List.length_replicate, h₁, h₂, pow_succ, hD]
      nlinarith [Nat.zero_le (c₀ * 2 ^ j), Nat.zero_le (c₁ * 2 ^ j)])
    (fun n j hj => by
      have h₁ := hstate n j hj.le
      have hpow : 2 ^ j ≤ 2 ^ (encNat n).length := Nat.pow_le_pow_right (by norm_num) hj.le
      simp only [length_encPair, encUnary_apply, encBool_apply, List.length_singleton,
        List.length_replicate, h₁, hD]
      nlinarith [Nat.mul_le_mul_left c₀ hpow, Nat.mul_le_mul_left c₁ hpow])
    (fun n j hj => by
      rw [hstate n j hj, encUnary_apply, List.length_replicate]
      exact (Nat.pow_le_pow_right (by norm_num) hj).trans (Nat.le_succ _))
    (fun n j hj => by simp)
  have hgeom (L : ℕ) : ∑ j ∈ Finset.range L, D * (2 ^ j + 1) ≤ D * (2 ^ L + L) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
    exact Nat.mul_le_mul_left D (Nat.add_le_add_right
      (Nat.geomSum_lt le_rfl fun _ => Finset.mem_range.1).le _)
  have hbound (n : ℕ) : 2 * ci + 2 + (2 * ce + 2) + (encNat n).length +
      (∑ j ∈ Finset.range (encNat n).length, D * (2 ^ j + 1)) +
        (2 ^ (encNat n).length + 1) + 1 ≤ (2 * ci + 2 * ce + 5 * D + 20) * (n + 1) := by
    have h₁ := two_pow_length_encNat_le n
    have h₂ := Universal.length_encNat_le n
    have h₃ := hgeom (encNat n).length
    nlinarith
  refine (ComputableTidilyInO.of_bounds hK (K * (2 * ci + 2 * ce + 5 * D + 20) + 1)
    (fun n => ?_) (fun n => ?_) fun n => ?_).computableInO
  · calc K * (2 * ci + 2 + (2 * ce + 2) + (encNat n).length +
          (∑ j ∈ Finset.range (encNat n).length, D * (2 ^ j + 1)) +
            (2 ^ (encNat n).length + 1) + 1)
        ≤ K * ((2 * ci + 2 * ce + 5 * D + 20) * (n + 1)) := Nat.mul_le_mul_left K (hbound n)
      _ ≤ _ := by nlinarith
  · have h₁ := two_pow_length_encNat_le n
    calc K * (0 + 0 + D * (2 ^ (encNat n).length + 1) + (2 ^ (encNat n).length + 1) + 1)
        ≤ K * ((2 * ci + 2 * ce + 5 * D + 20) * (n + 1)) := Nat.mul_le_mul_left K (by nlinarith)
      _ ≤ _ := by nlinarith
  · simp only [encUnary_apply, List.length_replicate]
    exact (Nat.le_succ n).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))

end Turing.MultiTapeTM
