/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Header
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Meaning
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Copy
import Mathlib.Tactic.Ring

/-!
# Alternating buffers for the shared native encoder

## Main definitions

* `Encoding.destination`, `Encoding.source`: the alternating buffer addresses.
* `Encoding.Progress`: the mixed-radix array and frame invariant after a stage.

## References

The shared encodings are from [AlmanWilliams2026, Section 2.4.1]; see `Encoding` for provenance.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open CoordinateTransform

/-- Destination of the next coordinate transform; always one of the two fixed buffers. -/
def destination (L : ℕ) : ℕ → ℕ
  | 0 => outputBase L
  | j + 1 => if destination L j = outputBase L then scratchBase L else outputBase L

/-- Source of the next coordinate transform; initially the preserved input segment. -/
def source (L : ℕ) : ℕ → ℕ
  | 0 => 2
  | j + 1 => destination L j

/-- A destination is either the fixed output block or the scratch block. -/
theorem destination_cases (L j : ℕ) :
    destination L j = outputBase L ∨ destination L j = scratchBase L := by
  cases j with
  | zero => exact Or.inl rfl
  | succ j => unfold destination; split <;> simp

/-- After the initial transform, the source is also one of the two buffers. -/
theorem source_cases {L j : ℕ} (hj : 0 < j) :
    source L j = outputBase L ∨ source L j = scratchBase L := by
  cases j with
  | zero => omega
  | succ j => exact destination_cases L j

/-- The two alternating buffer addresses differ at every stage. -/
theorem source_ne_destination (L j : ℕ) : source L j ≠ destination L j := by
  have hpos : 0 < 10 ^ L := by positivity
  have h7pos : 0 < 7 ^ L := by positivity
  cases j with
  | zero => simp only [source, destination, outputBase]; omega
  | succ j =>
    rcases destination_cases L j with h | h
    · simp only [source, destination, h, ↓reduceIte]
      unfold scratchBase
      omega
    · have hne : scratchBase L ≠ outputBase L := by unfold scratchBase; omega
      simp only [source, destination, h, hne, ↓reduceIte]
      exact hne

/-- Both current addresses are bounded by the end of the second buffer. -/
theorem buffer_address_le (L j : ℕ) :
    source L j ≤ 2 + 2 * 10 ^ L ∧ destination L j ≤ 2 + 2 * 10 ^ L := by
  have h7 := Nat.pow_le_pow_left (by decide : 7 ≤ 10) L
  have hd := destination_cases L j
  have hs : source L j = 2 ∨ source L j = outputBase L ∨ source L j = scratchBase L := by
    cases j with
    | zero => exact Or.inl rfl
    | succ j => exact Or.inr (destination_cases L j)
  simp only [scratchBase, outputBase] at hs hd
  constructor <;> omega

/-- Arrays stored at consecutive buffers are disjoint, in either order. The initial input
ends exactly at the first output address. -/
theorem buffers_separated {L j k N : ℕ} (hjk : j + k = L)
    (hN : N ≤ 10 ^ L) :
    source L j + 10 ^ j * 7 ^ k ≤ destination L j ∨
      destination L j + N ≤ source L j := by
  have hsize : 10 ^ j * 7 ^ k ≤ 10 ^ L := by simpa only [hjk] using stageSize_le j k
  cases j with
  | zero =>
    left
    simp only [Nat.zero_add] at hjk
    simp [source, destination, outputBase, hjk]
  | succ j =>
    have hs := source_cases (L := L) (j := j + 1) (by omega)
    have hd := destination_cases L (j + 1)
    have hne := source_ne_destination L (j + 1)
    unfold scratchBase at hs hd
    omega

/-- The shared-array invariant at depth `j`. All fields describe ordinary registers or
mathematical memory values. Execution, timing and width are proved separately. -/
structure Progress (side : Bool) (L j : ℕ) (arr : ℕ → ℤ) (initial : ℕ → ℕ)
    (y : Data 32) : Prop where
  /-- Fixed parameters retained across coordinate stages. -/
  fixed : y.regs depth = L ∧ y.regs capacity = 10 ^ L ∧
    y.regs output = outputBase L ∧ y.regs scratch = scratchBase L ∧
    y.regs one = 1 ∧ y.regs seven = 7 ∧ y.regs ten = 10
  /-- Number of transformed coordinates. -/
  stage : y.regs Encoding.stage = j
  /-- Number of transformed prefixes. -/
  prefixes : y.regs Encoding.prefixes = 10 ^ j
  /-- Original suffix length in the current source. -/
  stride : y.regs Encoding.stride = 7 ^ (L - j)
  /-- Current source address. -/
  src : y.regs Encoding.src = source L j
  /-- Current destination address. -/
  dst : y.regs Encoding.dst = destination L j
  /-- The source holds exactly the shared prefix sums. -/
  values : ∀ p < 10 ^ j, ∀ r < 7 ^ (L - j),
    y.mem (source L j + p * 7 ^ (L - j) + r) =
      encode (value (table (coefficients side)) j (L - j) arr p r)
  /-- Input, headers and all cells outside both work buffers are preserved. -/
  frame : ∀ a, ¬(outputBase L ≤ a ∧ a < scratchBase L + 10 ^ L) → y.mem a = initial a

/-- The actual header initialization establishes the zero-stage invariant from the original
flat input segment. No scratch values or preinitialized coefficient tables are required. -/
theorem progress_zero (side : Bool) (L : ℕ) (arr : ℕ → ℤ) (x y : Data 32)
    (hy : SetupPost L x y) (hinput : ∀ i < 7 ^ L, x.mem (2 + i) = encode (arr i)) :
    Progress side L 0 arr x.mem y := by
  refine ⟨⟨hy.depth, hy.capacity, hy.output, hy.scratch, hy.one, hy.seven, hy.ten⟩,
    hy.stage, hy.prefixes, ?_, hy.src, hy.dst, ?_, ?_⟩
  · simpa only [Nat.sub_zero] using hy.stride
  · intro p hp r hr
    have hp0 : p = 0 := by simpa only [pow_zero] using Nat.eq_zero_of_le_zero (by omega : p ≤ 0)
    subst p
    rw [hy.mem, value_zero]
    simpa only [source, Nat.sub_zero, Nat.zero_mul, Nat.add_zero] using hinput r hr
  · intro a _
    rw [hy.mem]

/-- One proved native stage advances the mixed-radix invariant. The signed magnitude bound
comes from the original input and the number of coordinates already transformed. -/
theorem progress_step {w L j : ℕ} (hw : 0 < w) (hj : j < L) (side : Bool)
    (arr : ℕ → ℤ) (initial : ℕ → ℕ) (x : Data 32) (hx : Progress side L j arr initial x)
    (A : ℤ) (hA : 0 ≤ A) (ha : ∀ i < 7 ^ L, |arr i| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L)) :
    ∃ y, ExecWithin (w + 2) (stageBody side) x y (207 * 10 ^ L + 12) ∧
      Progress side L (j + 1) arr initial y := by
  let k := L - (j + 1)
  let n := 7 ^ k
  let P := 10 ^ j
  have hn : 0 < n := by dsimp only [n]; positivity
  have hP : 0 < P := by dsimp only [P]; positivity
  have hk : L - j = k + 1 := by omega
  have hjk : j + (k + 1) = L := by omega
  have hjk' : j + 1 + k = L := by omega
  have hstride : 7 ^ (L - j) = 7 * n := by rw [hk, pow_succ']
  have hN : 10 * P * n ≤ 10 ^ L := by
    have h := stageSize_le (j + 1) k
    simpa only [hjk', pow_succ', P, n] using h
  have hcoeff : ∀ t < 10, ∀ s < 7, |table (coefficients side) t s| ≤ 1 := by
    intro t _ s _
    unfold table coefficients
    cases side
    · exact abs_phi_le_one _ _
    · exact abs_psi_le_one _ _
  let v (i : ℕ) (a : Fin 7) : ℤ := value (table (coefficients side)) j (k + 1) arr
    (i / (10 * n)) (a.val * n + i % n)
  let B : ℤ := (7 ^ j : ℕ) * A
  have hB : 0 ≤ B := mul_nonneg (by positivity) hA
  have hsuffix (i : ℕ) (a : Fin 7) : a.val * n + i % n < 7 ^ (k + 1) := by
    have hm := Nat.mul_le_mul_right n (Nat.succ_le_of_lt a.isLt)
    have hr := Nat.mod_lt i hn
    rw [pow_succ']
    change a.val * n + i % n < 7 * n
    nlinarith only [hm, hr]
  have hv : ∀ i < 10 * P * n, ∀ a, |v i a| ≤ B := by
    intro i _ a
    exact abs_value_le_of_input hcoeff hjk _ _ (hsuffix i a) ha
  have hload : ∀ i < 10 * P * n, ∀ a,
      x.mem (source L j + (i / (10 * n) * 7 + a.val) * n + i % n) = encode (v i a) := by
    intro i hi a
    have hp : i / (10 * n) < 10 ^ j := by
      apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 10 * n)).mpr
      dsimp only [P] at hi
      nlinarith only [hi]
    have hidx : source L j + (i / (10 * n) * 7 + a.val) * n + i % n =
        source L j + i / (10 * n) * 7 ^ (L - j) + (a.val * n + i % n) := by
      rw [hstride]
      ring
    rw [hidx, hx.values _ hp _ (by rw [hk]; exact hsuffix i a)]
    rw [hk]
  have hvalue : 7 * B < (2 : ℤ) ^ (w - 1) := by
    have hpow : 7 ^ (j + 1) ≤ 7 ^ L := Nat.pow_le_pow_right (by decide) (by omega)
    have hpowZ : ((7 ^ (j + 1) : ℕ) : ℤ) ≤ (7 ^ L : ℕ) := by exact_mod_cast hpow
    have hprod := mul_le_mul_of_nonneg_right hpowZ hA
    simpa only [Nat.pow_succ', Nat.cast_mul, Nat.cast_ofNat, mul_assoc, B] using
      hprod.trans_lt hmag
  have hbound := buffer_address_le L j
  have hcap : 1 ≤ 10 ^ L := Nat.one_le_pow L 10 (by decide)
  have hnative : Fits (w + 2) (source L j + destination L j + 64 + 64 * P * n) :=
    haddr.of_le (by unfold addressBound; nlinarith only [hbound.1, hbound.2, hN, hcap])
  have hseparate : source L j + 7 * P * n ≤ destination L j ∨
      destination L j + 10 * P * n ≤ source L j := by
    have h := buffers_separated (k := L - j) (by omega : j + (L - j) = L) hN
    simpa only [hstride, P, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  obtain ⟨y, he, hm, hf, hsrc, hdst, hstr, hp, hstage, hreg⟩ := exec_stageBody hw side x
    P n (source L j) (destination L j) j (outputBase L) (scratchBase L) hP hn hx.src hx.dst
    hx.stage (by simpa only [hstride] using hx.stride) hx.prefixes hx.fixed.2.2.2.2.2.1
    hx.fixed.2.2.2.2.2.2 hx.fixed.2.2.2.2.1 hx.fixed.2.2.1 hx.fixed.2.2.2.1 v B hB hv hload
    hvalue hnative (haddr.of_le (by unfold addressBound; omega)) hseparate
  refine ⟨y, he.mono (by omega), ?_⟩
  have hr (a : Fin 32) (ha : 9 ≤ a.val) (hl : ¬StageLocal a) : y.regs a = x.regs a := hreg a ha hl
  refine ⟨?_, hstage, ?_, ?_, hsrc, hdst, ?_, ?_⟩
  · rcases hx.fixed with ⟨hd, hc, ho, hs, h1, h7, h10⟩
    exact ⟨(hr depth (by decide) (by decide)).trans hd,
      (hr capacity (by decide) (by decide)).trans hc,
      (hr output (by decide) (by decide)).trans ho,
      (hr scratch (by decide) (by decide)).trans hs,
      (hr one (by decide) (by decide)).trans h1,
      (hr seven (by decide) (by decide)).trans h7,
      (hr ten (by decide) (by decide)).trans h10⟩
  · simpa only [P, pow_succ'] using hp
  · exact hstr
  · intro p hpp r hrr
    have hrr' : r < n := hrr
    have hpp' : p < 10 * P := by simpa only [pow_succ', P] using hpp
    have hprod := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hpp')
    have hi : p * n + r < 10 * P * n := by nlinarith only [hprod, hrr']
    have hdiv : (p * n + r) / n = p := by
      rw [Nat.mul_comm p n, Nat.mul_add_div hn, Nat.div_eq_of_lt hrr', Nat.add_zero]
    have hmod : (p * n + r) % n = r := Nat.mul_add_mod_of_lt hrr'
    have hvout := hm (p * n + r) hi
    rw [show stageResult side n v (p * n + r) = value (table (coefficients side))
      (j + 1) k arr ((p * n + r) / n) ((p * n + r) % n) from stageResult_value side j k _ arr,
      hdiv, hmod] at hvout
    simpa only [source, n, k, Nat.add_assoc] using hvout
  · intro a haout
    rw [hf a ?_]
    · exact hx.frame a haout
    · rcases destination_cases L j with hd | hd <;> rw [hd] <;> unfold scratchBase at * <;> omega

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
