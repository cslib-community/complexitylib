/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.LempelZiv.LZ78Count
public import CslibFrontier.Foundations.Data.BitString.Counter
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

import CslibFrontier.Foundations.Data.BitString.Binary
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The LZ78 bit code and its length

`encodeBits e x` writes the LZ78 (pointer, symbol) pairs of `x` as bits ([ZivLempel1978];
[CoverThomas2006], Ch. 13). The `i`-th pair (counting from `1`) has a pointer in
`{0, …, i - 1}`, written in `⌈log₂ i⌉` bits, and a symbol, written in `⌈log₂ k⌉` bits through a
fixed numbering `e : α ≃ Fin k` of the alphabet; numbers are written least significant bit first
(`Cslib.BitString.lowBits`). The widths depend only on the position, so the decoder needs no
separators. For `k ≥ 2` every pair has at least one bit and `decodeBits` recovers the input.

The length of the code of an input of length `n` with `c` phrases is exactly
`∑_{i=1}^{c} (⌈log₂ i⌉ + ⌈log₂ k⌉) ≤ c (⌈log₂ c⌉ + ⌈log₂ k⌉)`. With the distinct-parsing bound
`c log_k c ≤ n + 2c` this gives `⌈log₂ k⌉ (n + 4c)`, and with `c ≤ n / ((1 - ε_n) log_k n)`
the worst-case length `⌈log₂ k⌉ n (1 + 4 / ((1 - ε_n) log_k n)) = ⌈log₂ k⌉ n (1 + o(1))`: LZ78
never expands its input by more than a vanishing fraction over the fixed-length code of
`⌈log₂ k⌉ n` bits.

## Main definitions

* `Cslib.Algorithms.Lean.LempelZiv.LZ78.pairsToBits`,
  `Cslib.Algorithms.Lean.LempelZiv.LZ78.bitsToPairs`: the bit code of (pointer, symbol) pairs.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.encodeBits`,
  `Cslib.Algorithms.Lean.LempelZiv.LZ78.decodeBits`: the LZ78 bit code.

## Main results

* `Cslib.Algorithms.Lean.LempelZiv.LZ78.decodeBits_encodeBits`: the bit code is lossless.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.length_encodeBits`: the exact length.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.length_encodeBits_le`: at most
  `c (⌈log₂ c⌉ + ⌈log₂ k⌉)`.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.length_encodeBits_le_mul_add`: at most
  `⌈log₂ k⌉ (n + 4c)`.
* `Cslib.Algorithms.Lean.LempelZiv.LZ78.length_encodeBits_le_mul_one_add`,
  `Cslib.Algorithms.Lean.LempelZiv.LZ78.tendsto_four_div_one_sub_epsilon_mul_logb`,
  `Cslib.Algorithms.Lean.LempelZiv.LZ78.exists_length_encodeBits_le`: the worst-case length is
  `⌈log₂ k⌉ n (1 + o(1))`.

## References

* [ZivLempel1978] J. Ziv and A. Lempel, *Compression of individual sequences via variable-rate
  coding*, IEEE Trans. Inf. Theory 24(5), 1978.
* [CoverThomas2006] T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed.,
  2006, Ch. 13.
-/

public section

namespace Cslib.Algorithms.Lean.LempelZiv.LZ78

open Cslib.BitString
open Cslib.Algorithms.Lean.LempelZiv.DistinctParsing (epsilon tendsto_epsilon)

variable {α : Type*} {k : ℕ}

/-- Write (pointer, symbol) pairs as bits, the pair at position `i` (counting from `0`) with a
pointer of `⌈log₂ (i + 1)⌉` bits and a symbol of `⌈log₂ k⌉` bits. -/
@[expose] def pairsToBits (e : α ≃ Fin k) : ℕ → List (ℕ × α) → List Bool
  | _, [] => []
  | i, (j, a) :: ps =>
    lowBits (Nat.clog 2 (i + 1)) j ++ lowBits (Nat.clog 2 k) (e a) ++ pairsToBits e (i + 1) ps

/-- Read (pointer, symbol) pairs written by `pairsToBits`, starting at position `i`, with `fuel`
steps. Fails on a truncated pair or a symbol number `≥ k`. -/
@[expose] def bitsToPairs (e : α ≃ Fin k) : ℕ → ℕ → List Bool → Option (List (ℕ × α))
  | 0, _, _ => none
  | fuel + 1, i, bs =>
    if bs = [] then some []
    else
      let w := Nat.clog 2 (i + 1)
      let b := Nat.clog 2 k
      if w + b ≤ bs.length then
        let v := lsbValue ((bs.drop w).take b)
        if hv : v < k then
          (bitsToPairs e fuel (i + 1) (bs.drop (w + b))).map
            fun ps => (lsbValue (bs.take w), e.symm ⟨v, hv⟩) :: ps
        else none
      else none

/-- **LZ78 bit encoder.** -/
@[expose] def encodeBits [DecidableEq α] (e : α ≃ Fin k) (x : List α) : List Bool :=
  pairsToBits e 0 (encode x)

/-- **LZ78 bit decoder.** -/
@[expose] def decodeBits (e : α ≃ Fin k) (bs : List Bool) : Option (List α) :=
  (bitsToPairs e (bs.length + 1) 0 bs).map decode

/-- The exact length of `pairsToBits`. -/
theorem length_pairsToBits (e : α ≃ Fin k) (i : ℕ) (ps : List (ℕ × α)) :
    (pairsToBits e i ps).length =
      ∑ j ∈ Finset.range ps.length, (Nat.clog 2 (i + j + 1) + Nat.clog 2 k) := by
  induction ps generalizing i with
  | nil => simp [pairsToBits]
  | cons p ps ih =>
    obtain ⟨j, a⟩ := p
    simp only [pairsToBits, List.length_append, length_lowBits, ih, List.length_cons,
      Finset.sum_range_succ', Nat.add_zero]
    have : ∀ x ∈ Finset.range ps.length, Nat.clog 2 (i + 1 + x + 1) + Nat.clog 2 k =
        Nat.clog 2 (i + (x + 1) + 1) + Nat.clog 2 k := fun x _ => by
      rw [show i + 1 + x + 1 = i + (x + 1) + 1 by omega]
    rw [Finset.sum_congr rfl this]
    omega

/-- The pointers are in range: the pair at position `i` points below `i + 1`. -/
private def PointersLt : ℕ → List (ℕ × α) → Prop
  | _, [] => True
  | i, (j, _) :: ps => j < i + 1 ∧ PointersLt (i + 1) ps

private theorem pointersLt_encodePhrases [DecidableEq α] (dict ws : List (List α))
    (ht : IsTreeStructured dict ws) : PointersLt dict.length (encodePhrases dict ws) := by
  induction ws generalizing dict with
  | nil => simp [encodePhrases, PointersLt]
  | cons w ws ih =>
    obtain ⟨⟨q, hq, a, rfl⟩, ht⟩ := (isTreeStructured_cons _ _ _).1 ht
    simp only [encodePhrases, List.getLast?_concat, List.dropLast_concat, PointersLt]
    refine ⟨?_, ?_⟩
    · have := List.idxOf_lt_length_of_mem hq
      simpa using this
    · have := ih _ ht
      simpa using this

private theorem length_lt_length_pairsToBits (e : α ≃ Fin k) (hk : 2 ≤ k) (i : ℕ)
    (ps : List (ℕ × α)) : ps.length ≤ (pairsToBits e i ps).length := by
  have hb : 1 ≤ Nat.clog 2 k := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) hk)
  rw [length_pairsToBits]
  calc ps.length = ∑ _j ∈ Finset.range ps.length, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ => by omega

private theorem bitsToPairs_pairsToBits (e : α ≃ Fin k) (hk : 2 ≤ k) (ps : List (ℕ × α))
    (i fuel : ℕ) (hp : PointersLt i ps) (hfuel : ps.length < fuel) :
    bitsToPairs e fuel i (pairsToBits e i ps) = some ps := by
  induction ps generalizing i fuel with
  | nil =>
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by rw [List.length_nil] at hfuel; omega⟩
    simp [pairsToBits, bitsToPairs]
  | cons p ps ih =>
    obtain ⟨j, a⟩ := p
    obtain ⟨hj, hp⟩ := hp
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 :=
      ⟨fuel - 1, by rw [List.length_cons] at hfuel; omega⟩
    have hb : 1 ≤ Nat.clog 2 k := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) hk)
    have hjw : j < 2 ^ Nat.clog 2 (i + 1) :=
      lt_of_lt_of_le hj (Nat.le_pow_clog (by norm_num) _)
    have haw : ((e a : Fin k) : ℕ) < 2 ^ Nat.clog 2 k :=
      lt_of_lt_of_le (e a).isLt (Nat.le_pow_clog (by norm_num) _)
    set w := Nat.clog 2 (i + 1)
    set b := Nat.clog 2 k
    set rest := pairsToBits e (i + 1) ps
    have hbits : pairsToBits e i ((j, a) :: ps) = lowBits w j ++ lowBits b (e a) ++ rest := rfl
    have hne : lowBits w j ++ lowBits b (e a) ++ rest ≠ [] := by
      grind [List.length_append, length_lowBits, List.length_nil]
    have hlen : w + b ≤ (lowBits w j ++ lowBits b (e a) ++ rest).length := by
      simp only [List.length_append, length_lowBits]; omega
    have hdrop1 : (lowBits w j ++ lowBits b (e a) ++ rest).drop w = lowBits b (e a) ++ rest := by
      rw [List.append_assoc, List.drop_left' (length_lowBits w j)]
    have htake1 : (lowBits w j ++ lowBits b (e a) ++ rest).take w = lowBits w j := by
      rw [List.append_assoc, List.take_left' (length_lowBits w j)]
    have hsym : (lowBits b (e a) ++ rest).take b = lowBits b (e a) :=
      List.take_left' (length_lowBits b _)
    have hdrop2 : (lowBits w j ++ lowBits b (e a) ++ rest).drop (w + b) = rest := by
      rw [← List.drop_drop, hdrop1, List.drop_left' (length_lowBits b _)]
    have hv : lsbValue (((lowBits w j ++ lowBits b (e a) ++ rest).drop w).take b) = e a := by
      rw [hdrop1, hsym, lsbValue_lowBits haw]
    have hvk : lsbValue (((lowBits w j ++ lowBits b (e a) ++ rest).drop w).take b) < k := by
      rw [hv]; exact (e a).isLt
    have hsa : e.symm ⟨_, hvk⟩ = a := by
      rw [Equiv.symm_apply_eq]
      exact Fin.ext hv
    rw [hbits, bitsToPairs, ite_eq_right hne, ite_eq_left hlen, dite_eq_left hvk, hdrop2,
      ih (i + 1) fuel hp (by rw [List.length_cons] at hfuel; omega), Option.map_some, htake1,
      lsbValue_lowBits hjw, hsa]

/-- **The LZ78 bit code is lossless** for an alphabet of size `k ≥ 2`. -/
theorem decodeBits_encodeBits [DecidableEq α] (e : α ≃ Fin k) (hk : 2 ≤ k) (x : List α) :
    decodeBits e (encodeBits e x) = some x := by
  have hp : PointersLt 0 (encode x) :=
    pointersLt_encodePhrases [] (parse x) (isTreeStructured_parse x)
  rw [decodeBits, encodeBits, bitsToPairs_pairsToBits e hk _ 0 _ hp
    (Nat.lt_succ_of_le (length_lt_length_pairsToBits e hk 0 _)), Option.map_some, decode_encode]

/-- **The exact length of the LZ78 bit code**: `∑_{i=1}^{c} (⌈log₂ i⌉ + ⌈log₂ k⌉)`, where `c` is
the number of phrases. -/
theorem length_encodeBits [DecidableEq α] (e : α ≃ Fin k) (x : List α) :
    (encodeBits e x).length =
      ∑ i ∈ Finset.range (parse x).length, (Nat.clog 2 (i + 1) + Nat.clog 2 k) := by
  rw [encodeBits, length_pairsToBits, length_encode]
  simp only [Nat.zero_add]

/-- The LZ78 bit code of an input with `c` phrases has at most `c (⌈log₂ c⌉ + ⌈log₂ k⌉)` bits. -/
theorem length_encodeBits_le [DecidableEq α] (e : α ≃ Fin k) (x : List α) :
    (encodeBits e x).length ≤
      (parse x).length * (Nat.clog 2 (parse x).length + Nat.clog 2 k) := by
  rw [length_encodeBits]
  calc ∑ i ∈ Finset.range (parse x).length, (Nat.clog 2 (i + 1) + Nat.clog 2 k)
      ≤ ∑ _i ∈ Finset.range (parse x).length,
          (Nat.clog 2 (parse x).length + Nat.clog 2 k) :=
        Finset.sum_le_sum fun i hi => Nat.add_le_add_right
          (Nat.clog_mono_right 2 (Finset.mem_range.1 hi)) _
    _ = _ := by simp

/-- **Finite length bound.** For an alphabet of size `k ≥ 2`, the LZ78 bit code of an input of
length `n` with `c` phrases has at most `⌈log₂ k⌉ (n + 4c)` bits. -/
theorem length_encodeBits_le_mul_add [DecidableEq α] (e : α ≃ Fin k) (hk : 2 ≤ k)
    (x : List α) :
    (encodeBits e x).length ≤ Nat.clog 2 k * (x.length + 4 * (parse x).length) := by
  let _ : Fintype α := Fintype.ofEquiv (Fin k) e.symm
  have hcard : Fintype.card α = k := by rw [Fintype.card_congr e, Fintype.card_fin]
  set c := (parse x).length
  set b := Nat.clog 2 k
  set L := Nat.log k c
  have hlog : c * L ≤ x.length + 2 * c := by
    have := length_parse_mul_log_le x
    rwa [hcard] at this
  -- `⌈log₂ c⌉ ≤ b (L + 1)`, since `c < k ^ (L + 1) ≤ 2 ^ (b (L + 1))`.
  have hclog : Nat.clog 2 c ≤ b * (L + 1) := by
    refine Nat.clog_le_of_le_pow ?_
    calc c ≤ k ^ (L + 1) := (Nat.lt_pow_succ_log_self (by omega) c).le
      _ ≤ (2 ^ b) ^ (L + 1) := Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) k) _
      _ = 2 ^ (b * (L + 1)) := by rw [← pow_mul]
  calc (encodeBits e x).length ≤ c * (Nat.clog 2 c + b) := length_encodeBits_le e x
    _ ≤ c * (b * (L + 1) + b) := Nat.mul_le_mul_left _ (Nat.add_le_add_right hclog _)
    _ = b * (c * L) + 2 * b * c := by ring
    _ ≤ b * (x.length + 2 * c) + 2 * b * c := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hlog) _
    _ = b * (x.length + 4 * c) := by ring

/-- **Worst-case length `n (1 + o(1))`.** For an alphabet of size `k ≥ 2` and an input of length
`n ≥ 2` with `ε_n < 1`, the LZ78 bit code has at most
`⌈log₂ k⌉ n (1 + 4 / ((1 - ε_n) log_k n))` bits; the overhead factor tends to `0`
(`tendsto_four_div_one_sub_epsilon_mul_logb`). -/
theorem length_encodeBits_le_mul_one_add [DecidableEq α] (e : α ≃ Fin k) (hk : 2 ≤ k)
    (x : List α) (hn : 2 ≤ x.length) (hε : epsilon k x.length < 1) :
    ((encodeBits e x).length : ℝ) ≤
      Nat.clog 2 k * x.length * (1 + 4 / ((1 - epsilon k x.length) * Real.logb k x.length)) := by
  let _ : Fintype α := Fintype.ofEquiv (Fin k) e.symm
  have hcard : Fintype.card α = k := by rw [Fintype.card_congr e, Fintype.card_fin]
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have hLpos : 0 < Real.logb k x.length := Real.logb_pos hk1 (by exact_mod_cast hn)
  have hD : 0 < (1 - epsilon k x.length) * Real.logb k x.length :=
    mul_pos (by linarith) hLpos
  have hc : ((parse x).length : ℝ) ≤
      x.length / ((1 - epsilon k x.length) * Real.logb k x.length) := by
    have := length_parse_le_div (hcard ▸ hk) x hn (by rwa [hcard])
    rwa [hcard] at this
  have hbits : ((encodeBits e x).length : ℝ) ≤
      Nat.clog 2 k * (x.length + 4 * (parse x).length) := by
    exact_mod_cast length_encodeBits_le_mul_add e hk x
  have hb : (0 : ℝ) ≤ Nat.clog 2 k := Nat.cast_nonneg _
  calc ((encodeBits e x).length : ℝ) ≤ Nat.clog 2 k * (x.length + 4 * (parse x).length) := hbits
    _ ≤ Nat.clog 2 k * (x.length + 4 * (x.length /
          ((1 - epsilon k x.length) * Real.logb k x.length))) := by gcongr
    _ = Nat.clog 2 k * x.length *
          (1 + 4 / ((1 - epsilon k x.length) * Real.logb k x.length)) := by
        field_simp

/-- The overhead factor `4 / ((1 - ε_n) log_k n)` of the worst-case LZ78 length tends to `0`. -/
theorem tendsto_four_div_one_sub_epsilon_mul_logb (hk : 2 ≤ k) :
    Filter.Tendsto (fun n : ℕ => 4 / ((1 - epsilon k n) * Real.logb k n))
      Filter.atTop (nhds 0) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  have h1 : Filter.Tendsto (fun n : ℕ => 1 - epsilon k n) Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_epsilon hk)
  have hL : Filter.Tendsto (fun n : ℕ => Real.logb k n) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop hk1).comp tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop (h1.pos_mul_atTop one_pos hL)

/-- **The LZ78 code length is `⌈log₂ k⌉ n (1 + o(1))` in the worst case**: there is a sequence
`δ n → 0` such that every input of length `n` over an alphabet of size `k ≥ 2` has a bit code of
at most `⌈log₂ k⌉ n (1 + δ n)` bits. -/
theorem exists_length_encodeBits_le [DecidableEq α] (e : α ≃ Fin k) (hk : 2 ≤ k) :
    ∃ δ : ℕ → ℝ, Filter.Tendsto δ Filter.atTop (nhds 0) ∧
      ∀ x : List α, ((encodeBits e x).length : ℝ) ≤
        Nat.clog 2 k * x.length * (1 + δ x.length) := by
  classical
  refine ⟨fun n => if 2 ≤ n ∧ epsilon k n < 1 then
    4 / ((1 - epsilon k n) * Real.logb k n) else 4, ?_, fun x => ?_⟩
  · refine (tendsto_four_div_one_sub_epsilon_mul_logb hk).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 2,
      (tendsto_epsilon hk).eventually (gt_mem_nhds one_pos)] with n hn hε
    simp only [hn, hε, and_self, ↓reduceIte]
  · by_cases h : 2 ≤ x.length ∧ epsilon k x.length < 1
    · simp only [h, and_self, ↓reduceIte]
      exact length_encodeBits_le_mul_one_add e hk x h.1 h.2
    · simp only [h, ↓reduceIte]
      have hbits : ((encodeBits e x).length : ℝ) ≤
          Nat.clog 2 k * (x.length + 4 * (parse x).length) := by
        exact_mod_cast length_encodeBits_le_mul_add e hk x
      have hc : ((parse x).length : ℝ) ≤ x.length := by exact_mod_cast length_parse_le x
      have hb : (0 : ℝ) ≤ Nat.clog 2 k := Nat.cast_nonneg _
      nlinarith

end Cslib.Algorithms.Lean.LempelZiv.LZ78
