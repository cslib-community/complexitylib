/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Dictionary
public import Complexity.Algorithms.Lean.UniformProbing
public import Complexity.Algorithms.WordRAM.Hashing.MultiplyShift
public import Complexity.Algorithms.WordRAM.Hashing.Tabulation
public import Complexity.Computability.WordRAM.ExactNotation
public import Complexity.Computability.WordRAM.Randomized.Subroutine
import Complexity.Probability.PMF.Expect

/-!
# Self-Contained Open-Addressed Permutation-Probing Dictionary on the Word-RAM

This file implements a self-contained open-addressed permutation-probing dictionary realizing
`Cslib.Algorithms.Lean.Dictionary.spec U V n_max` (`get` and `insert` up to `n_max` distinct keys)
on the Word-RAM (`Cslib.WordRAM.Basis.exact` and `Cslib.WordRAM.Basis.standard`), following the
double-hashing construction of
[Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms*, third edition (MIT Press,
2009), Section 11.4, "Double hashing", pp. 272–274][CLRS2009] with simple tabulation due to
Zobrist (1970) and Pătraşcu and Thorup (2012).

## Design and reuse of `Cslib.Algorithms.Lean.UniformProbing`

In the ideal uniform-probing model (`Complexity/Algorithms/Lean/UniformProbing.lean`), each key
`u : Fin U` is assigned an independent random permutation `π u : Equiv.Perm (Fin m)`. Storing an
explicit table of `U` permutations requires `Ω(U)` words when `U = poly(n_max) ≫ n_max`.

To achieve a self-contained `O(n_max)`-word data structure (when `U = poly(n_max)`), we construct
for each key `u : Fin U` a full-cycle affine permutation of `m = 2 ^ M` slots
(`M = Nat.clog 2 (max (4 * n_max) 4)`):
`probePerm θ u i = (h₁(u) + i * h₂(u)) mod 2 ^ M`, where:
* `h₁(u) ∈ Fin (2 ^ M)` is a 2-universal multiply-shift hash
  (`Cslib.Algorithms.WordRAM.Hashing.MultiplyShift`);
* `h₂(u) ∈ Fin (2 ^ M)` is an odd stride computed by `d`-character simple tabulation
  (`Cslib.Algorithms.WordRAM.Hashing.Tabulation.TabulatedOddStride`, with character bit-width
  `b = max 1 (⌊log₂ (max n_max 2)⌋ / 2)` and `d = numChars U n_max`), following Zobrist (1970)
  and Pătraşcu and Thorup (2012).

Because `h₂(u)` is always odd and therefore coprime to `2 ^ M`, `probePerm θ u` is a bijection on
`Fin (2 ^ M)` for **every** seed `θ` and key `u` (`TabulatedOddStride.bijective_probeSeq`). We
therefore instantiate `Cslib.Algorithms.Lean.UniformProbing.TableRep (probePerm θ)` directly on the
concrete Word-RAM slot arrays. Note that `TabulatedOddStride` proves full-cycle permutation
bijectivity (`bijective_probeSeq`) rather than full uniform-permutation independence: accordingly,
`subroutineDS` certifies the concrete deterministic full-cycle body bound
`charge = opSteps U n_max = 13 * numBuckets n_max + 8 * numChars U n_max + 49`
(`O(n_max + log U / log n_max)`), while `expect_opPathSteps_le_of_probeBound` and
`expect_idealProbeSteps_le` connect the exact probe-path body cost
`13 * probeCount + 8 * numChars U n_max + 49` to `≤ 8 * numChars U n_max + 75` expected
instructions under an ideal uniform permutation law
(`Complexity/Algorithms/Lean/UniformProbing.lean`, Theorem 11.6, Corollary 11.7, and the per-key
bound from the proof of Theorem 11.8 of [CLRS2009], third edition, pp. 274–276).

## Model, specialization, and cost scope

* For fixed universe `U` and capacity bound `n_max` and an admissible external machine word width
  `w` (`2 * hashBits U n_max ≤ w`, `Fits w (base + space U n_max)`, `Fits w V`),
  `subroutineCode U n_max` uses precomputed configuration literals (`bucketBits`, `hashBits`,
  `charBits`, `numChars`, masks, and layout offsets baked as instruction literals, with
  `initParams = Fin.elim0`).
* Expected and amortized bounds in `seq_expected_amortized` charge initialization (`initFresh`) and
  subroutine operation bodies (`C.ExecSteps`) across an operation history `ops` fixed independently
  of the sampled seed (oblivious adversary), excluding caller argument delivery, caller
  control/dispatch loops, and code/configuration construction.
* `Dictionary.spec U V n_max` is insert-only (`get` and `insert` up to `n_max` distinct keys), so
  open-addressed slots require no tombstones.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.bucketBits`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.numBuckets`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.hashBits`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.charBits`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.numChars`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.space`: table dimension parameters and memory
  footprint.
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.Seed`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.seedLaw`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.primaryHash`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.strideHash`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.probePerm`: seed space, uniform seed law,
  multiply-shift primary hash, tabulated odd stride, and full-cycle probe permutation.
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.extractSlots`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.Rep`: slot-array extractor and Word-RAM
  representation invariant.
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.allocSpan`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.initSetup`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.opCode`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.subroutineCode`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.subroutineDS`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.subroutineDSStandard`: structured Word-RAM
  programs and `Randomized.SubroutineDS` certificates over `Basis.exact` and `Basis.standard`.

## Main results

* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.setup_exec_spec`: randomized seed and table
  initialization in `setupSteps U n_max = 5 * (numChars U n_max * 2 ^ charBits n_max) + 25`
  expected instructions.
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.opCode_execWithin`: every `get` or `insert`
  operation on key `u` executes in at most
  `opPathSteps U n_max θ T u = 13 * probeCount T u (probePerm θ u) + 8 * numChars U n_max + 49 ≤
  opSteps U n_max` instructions for every seed `θ`.
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.seq_expected_amortized`: end-to-end expected
  instruction bound across any admissible sequence `ops : List (Dictionary.Op U)`.
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.isUniversalHash_primaryHash`:
  `(2 / numBuckets n_max)`-universality of `primaryHash` under `seedLaw U n_max`.
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.expect_opPathSteps_le_of_probeBound`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.expect_idealProbeSteps_le`: parametric
  expected-step transfer (`13 * B + 8 * numChars U n_max + 49`) from any expected-probe bound `B`,
  yielding `≤ 8 * numChars U n_max + 75` under the ideal uniform permutation law (`B = 2`).

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*, third edition (MIT Press, 2009), Section 11.4,
  pp. 269–277][CLRS2009]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dictionary.UniformProbing

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.UniformProbing
open Cslib.Algorithms.WordRAM.Hashing
open Cslib.Algorithms.WordRAM.Hashing.Tabulation
open Cslib.Probability
open Cslib.WordRAM
open Cslib.WordRAM.Randomized
open scoped BigOperators ENNReal

/-! ## Section 1: Table Parameters, Seed Space, and Full-Cycle Probe Permutations -/

/-- Log₂ of the power-of-2 table size: `M = ⌈log₂ (max (4 * n_max) 4)⌉ ≥ 2`. -/
def bucketBits (n_max : ℕ) : ℕ :=
  Nat.clog 2 (max (4 * n_max) 4)

/-- Power-of-2 number of open-addressed table slots `m = 2 ^ bucketBits n_max ≥ max (4 * n_max) 4`.
-/
def numBuckets (n_max : ℕ) : ℕ :=
  2 ^ bucketBits n_max

/-- Bit-width `w₀ = max (bucketBits n_max) ⌈log₂ (max U 2)⌉` for the multiply-shift primary hash.
-/
def hashBits (U n_max : ℕ) : ℕ :=
  max (bucketBits n_max) (Nat.clog 2 (max U 2))

/-- Character bit-width `b = max 1 (⌊log₂ (max n_max 2)⌋ / 2)` for the tabulated odd stride. -/
def charBits (n_max : ℕ) : ℕ :=
  TabulatedOddStride.charBits n_max

/-- Number of base-`2 ^ b` characters `d = max 1 ⌈⌈log₂ (max U 2)⌉ / b⌉` used by the tabulated odd
stride. When `U = poly(n_max)`, `numChars U n_max = O(1)`. -/
def numChars (U n_max : ℕ) : ℕ :=
  max 1 ((Nat.clog 2 (max U 2) + charBits n_max - 1) / charBits n_max)

/-- Memory footprint `4 + d * 2 ^ b` words of the `TabulatedOddStride` table at `[base, ...)`. -/
def tabSpace (U n_max : ℕ) : ℕ :=
  TabulatedOddStride.space n_max (numChars U n_max)

/-- Offset `tabSpace U n_max + 1` of the open-addressed slot arrays relative to `base` (after the
`TabulatedOddStride` table at `[base, base + tabSpace U n_max)` and the 1-word multiply-shift seed
at `base + tabSpace U n_max`). -/
def slotOffset (U n_max : ℕ) : ℕ :=
  tabSpace U n_max + 1

/-- Total memory footprint `slotOffset U n_max + 3 * numBuckets n_max` words in
`[base, base + space U n_max)`. -/
def space (U n_max : ℕ) : ℕ :=
  slotOffset U n_max + 3 * numBuckets n_max

theorem two_le_bucketBits (n_max : ℕ) : 2 ≤ bucketBits n_max := by
  dsimp only [bucketBits]
  calc
    2 = Nat.clog 2 (2 ^ 2) := (Nat.clog_pow 2 2 (by decide)).symm
    _ ≤ Nat.clog 2 (max (4 * n_max) 4) := Nat.clog_mono_right 2 (by omega)

theorem bucketBits_pos (n_max : ℕ) : 0 < bucketBits n_max :=
  lt_of_lt_of_le (by decide : 0 < 2) (two_le_bucketBits n_max)

theorem max_four_mul_le_numBuckets (n_max : ℕ) :
    max (4 * n_max) 4 ≤ numBuckets n_max :=
  Nat.le_pow_clog (by decide) (max (4 * n_max) 4)

theorem four_le_numBuckets (n_max : ℕ) : 4 ≤ numBuckets n_max :=
  le_trans (Nat.le_max_right (4 * n_max) 4) (max_four_mul_le_numBuckets n_max)

theorem four_mul_le_numBuckets (n_max : ℕ) : 4 * n_max ≤ numBuckets n_max :=
  le_trans (Nat.le_max_left (4 * n_max) 4) (max_four_mul_le_numBuckets n_max)

theorem two_mul_le_numBuckets (n_max : ℕ) : 2 * n_max ≤ numBuckets n_max := by
  have := four_mul_le_numBuckets n_max
  omega

theorem lt_numBuckets (n_max : ℕ) : n_max < numBuckets n_max := by
  have h4 := four_le_numBuckets n_max
  have h4n := four_mul_le_numBuckets n_max
  omega

theorem numBuckets_pos (n_max : ℕ) : 0 < numBuckets n_max :=
  lt_of_lt_of_le (by decide : 0 < 4) (four_le_numBuckets n_max)

instance instNonemptyFinNumBuckets (n_max : ℕ) : Nonempty (Fin (numBuckets n_max)) :=
  ⟨⟨0, numBuckets_pos n_max⟩⟩

theorem bucketBits_le_hashBits (U n_max : ℕ) : bucketBits n_max ≤ hashBits U n_max :=
  Nat.le_max_left _ _

theorem hashBits_pos (U n_max : ℕ) : 0 < hashBits U n_max :=
  lt_of_lt_of_le (bucketBits_pos n_max) (bucketBits_le_hashBits U n_max)

theorem one_le_numChars (U n_max : ℕ) : 1 ≤ numChars U n_max :=
  Nat.le_max_left 1 _

theorem lt_two_pow_hashBits {U : ℕ} (n_max : ℕ) (u : Fin U) :
    u.val < 2 ^ hashBits U n_max := by
  have h1 : u.val < max U 2 := lt_of_lt_of_le u.isLt (Nat.le_max_left U 2)
  have h2 : max U 2 ≤ 2 ^ Nat.clog 2 (max U 2) := Nat.le_pow_clog (by decide) (max U 2)
  have h3 : 2 ^ Nat.clog 2 (max U 2) ≤ 2 ^ hashBits U n_max :=
    Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)
  exact lt_of_lt_of_le h1 (le_trans h2 h3)

/-- Embed key `u : Fin U` into `Fin (2 ^ hashBits U n_max)`. -/
def encodeKey {U : ℕ} (n_max : ℕ) (u : Fin U) : Fin (2 ^ hashBits U n_max) :=
  ⟨u.val, lt_two_pow_hashBits n_max u⟩

@[simp]
theorem val_encodeKey {U : ℕ} (n_max : ℕ) (u : Fin U) :
    (encodeKey n_max u).val = u.val := rfl

theorem encodeKey_injective {U : ℕ} (n_max : ℕ) :
    Function.Injective (encodeKey (U := U) n_max) := by
  intro u₁ u₂ h
  exact Fin.ext (congrArg (fun x : Fin (2 ^ hashBits U n_max) => x.val) h)

/-- Combined random seed `(b_ms, T)` consisting of the multiply-shift seed
`b_ms : Fin (2 ^ (hashBits U n_max - 1))` and the character table
`T : Fin (numChars U n_max * 2 ^ charBits n_max) → Fin (numBuckets n_max)`. -/
abbrev Seed (U n_max : ℕ) : Type :=
  Fin (2 ^ (hashBits U n_max - 1)) ×
    (Fin (numChars U n_max * 2 ^ charBits n_max) → Fin (numBuckets n_max))

instance instNonemptySeed (U n_max : ℕ) : Nonempty (Seed U n_max) :=
  ⟨(⟨0, Nat.two_pow_pos _⟩, fun _ => ⟨0, numBuckets_pos n_max⟩)⟩

/-- Uniform reference distribution over `Seed U n_max`. -/
noncomputable def seedLaw (U n_max : ℕ) : PMF (Seed U n_max) :=
  PMF.uniformOfFintype (Seed U n_max)

theorem multiplyShift_lt_numBuckets {U n_max : ℕ}
    (b : Fin (2 ^ (hashBits U n_max - 1))) (x : Fin (2 ^ hashBits U n_max)) :
    multiplyShift (hashBits U n_max) (bucketBits n_max) b x < numBuckets n_max := by
  dsimp only [multiplyShift, numBuckets]
  refine Nat.div_lt_of_lt_mul ?_
  rw [← pow_add, Nat.sub_add_cancel (bucketBits_le_hashBits U n_max)]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Multiply-shift primary slot `h₁(u) ∈ Fin (numBuckets n_max)`. -/
def primaryHash {U n_max : ℕ} (θ : Seed U n_max) (u : Fin U) : Fin (numBuckets n_max) :=
  ⟨multiplyShift (hashBits U n_max) (bucketBits n_max) θ.1 (encodeKey n_max u),
    multiplyShift_lt_numBuckets θ.1 (encodeKey n_max u)⟩

@[simp]
theorem val_primaryHash {U n_max : ℕ} (θ : Seed U n_max) (u : Fin U) :
    (primaryHash θ u).val =
      multiplyShift (hashBits U n_max) (bucketBits n_max) θ.1 (encodeKey n_max u) :=
  rfl

/-- Raw simple-tabulation character XOR sum `simpleTab b d M θ.2 u.val : Fin (numBuckets n_max)`. -/
def rawTabHash {U n_max : ℕ} (θ : Seed U n_max) (u : Fin U) : Fin (numBuckets n_max) :=
  TabulatedOddStride.simpleTab (charBits n_max) (numChars U n_max) (bucketBits n_max) θ.2 u.val

/-- Tabulated odd stride `h₂(u) = (2 * rawTabHash θ u + 1) mod 2 ^ M ∈ Fin (numBuckets n_max)`. -/
def strideHash {U n_max : ℕ} (θ : Seed U n_max) (u : Fin U) : Fin (numBuckets n_max) :=
  TabulatedOddStride.tabulatedOddStride (charBits n_max) (numChars U n_max) (bucketBits n_max)
    θ.2 u.val

/-- Full-cycle double-hashing probe permutation
`probePerm θ u : Equiv.Perm (Fin (numBuckets n_max))` sending probe index `i` to
`(h₁(u) + i * h₂(u)) mod 2 ^ M`, certified bijective by `TabulatedOddStride.bijective_probeSeq`. -/
noncomputable def probePerm {U n_max : ℕ} (θ : Seed U n_max) (u : Fin U) :
    Equiv.Perm (Fin (numBuckets n_max)) :=
  Equiv.ofBijective
    (TabulatedOddStride.probeSeq (bucketBits n_max) (primaryHash θ u).val (rawTabHash θ u).val)
    (TabulatedOddStride.bijective_probeSeq (bucketBits n_max)
      (primaryHash θ u).val (rawTabHash θ u).val)

theorem probePerm_apply {U n_max : ℕ} (θ : Seed U n_max) (u : Fin U)
    (i : Fin (numBuckets n_max)) :
    probePerm θ u i =
      TabulatedOddStride.probeSeq (bucketBits n_max) (primaryHash θ u).val (rawTabHash θ u).val i :=
  rfl

@[simp]
theorem val_probePerm {U n_max : ℕ} (θ : Seed U n_max) (u : Fin U)
    (i : Fin (numBuckets n_max)) :
    (probePerm θ u i).val =
      ((primaryHash θ u).val + i.val * (strideHash θ u).val) % numBuckets n_max :=
  rfl

@[simp]
theorem probePerm_zero {U n_max : ℕ} (θ : Seed U n_max) (u : Fin U) :
    probePerm θ u ⟨0, numBuckets_pos n_max⟩ = primaryHash θ u := by
  apply Fin.ext
  rw [val_probePerm]
  simpa using Nat.mod_eq_of_lt (primaryHash θ u).isLt

/-- One step of the Word-RAM probe loop `(slot + stride) &&& (2 ^ M - 1)` advances from
`probePerm θ u ⟨i, _⟩` to `probePerm θ u ⟨i + 1, _⟩`. -/
theorem val_probePerm_succ {U n_max : ℕ} (θ : Seed U n_max) (u : Fin U)
    {i : ℕ} (hi : i + 1 < numBuckets n_max) :
    (probePerm θ u ⟨i + 1, hi⟩).val =
      ((probePerm θ u ⟨i, by omega⟩).val + (strideHash θ u).val) &&&
        (numBuckets n_max - 1) := by
  change (probePerm θ u ⟨i + 1, hi⟩).val =
    ((probePerm θ u ⟨i, by omega⟩).val + (strideHash θ u).val) &&&
      (2 ^ bucketBits n_max - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod, val_probePerm, val_probePerm]
  simp [numBuckets, Nat.add_mul, one_mul, Nat.add_assoc]

/-! ## Section 2: Concrete Slot Extraction and Representation Invariant -/

/-- Well-formedness of the flat open-addressed slot arrays at
`[base + slotOffset U n_max, base + slotOffset U n_max + 3 * numBuckets n_max)`:
each `used[j]` word is `0` or `1`, and whenever `used[j] = 1`, `key[j] < U`. -/
def SlotArrayWF (base U n_max : ℕ) (mem : ℕ → ℕ) : Prop :=
  let sBase := base + slotOffset U n_max
  let m := numBuckets n_max
  ∀ j : Fin m,
    (mem (sBase + j.val) = 0 ∨ mem (sBase + j.val) = 1) ∧
    (mem (sBase + j.val) = 1 → mem (sBase + m + j.val) < U)

/-- Extract the abstract open-addressed table `UniformProbing.Table U (numBuckets n_max)` from
Word-RAM memory `mem`. -/
def extractSlots (base U n_max : ℕ) (mem : ℕ → ℕ) :
    UniformProbing.Table U (numBuckets n_max) :=
  let sBase := base + slotOffset U n_max
  let m := numBuckets n_max
  fun j =>
    if mem (sBase + j.val) = 0 then none
    else if h : mem (sBase + m + j.val) < U then
      some (⟨mem (sBase + m + j.val), h⟩, mem (sBase + 2 * m + j.val))
    else none

theorem extractSlots_eq_none_iff {base U n_max : ℕ} {mem : ℕ → ℕ}
    (hwf : SlotArrayWF base U n_max mem) (j : Fin (numBuckets n_max)) :
    extractSlots base U n_max mem j = none ↔
      mem (base + slotOffset U n_max + j.val) = 0 := by
  rcases hwf j with ⟨h0 | h1, hkey⟩
  · simp [extractSlots, h0]
  · have hlt : mem (base + slotOffset U n_max + numBuckets n_max + j.val) < U := hkey h1
    simp [extractSlots, h1, hlt]

theorem extractSlots_eq_some_iff {base U n_max : ℕ} {mem : ℕ → ℕ}
    (hwf : SlotArrayWF base U n_max mem) (j : Fin (numBuckets n_max))
    (u : Fin U) (v : ℕ) :
    extractSlots base U n_max mem j = some (u, v) ↔
      mem (base + slotOffset U n_max + j.val) = 1 ∧
      mem (base + slotOffset U n_max + numBuckets n_max + j.val) = u.val ∧
      mem (base + slotOffset U n_max + 2 * numBuckets n_max + j.val) = v := by
  rcases hwf j with ⟨h0 | h1, hkey⟩
  · simp [extractSlots, h0]
  · have hlt : mem (base + slotOffset U n_max + numBuckets n_max + j.val) < U := hkey h1
    simp [extractSlots, h1, hlt, Fin.ext_iff]

theorem mem_otherOccupiedSlots_extractSlots_iff {base U n_max : ℕ} {mem : ℕ → ℕ}
    (hwf : SlotArrayWF base U n_max mem) (u : Fin U) (j : Fin (numBuckets n_max)) :
    j ∈ otherOccupiedSlots (extractSlots base U n_max mem) u ↔
      mem (base + slotOffset U n_max + j.val) = 1 ∧
      mem (base + slotOffset U n_max + numBuckets n_max + j.val) ≠ u.val := by
  rw [mem_otherOccupiedSlots_iff]
  constructor
  · rintro ⟨u', v', hsome, hne⟩
    rw [extractSlots_eq_some_iff hwf] at hsome
    refine ⟨hsome.1, ?_⟩
    rw [hsome.2.1]
    exact fun h => hne (Fin.ext h)
  · rintro ⟨h1, hne⟩
    have hlt : mem (base + slotOffset U n_max + numBuckets n_max + j.val) < U :=
      (hwf j).2 h1
    refine ⟨⟨mem (base + slotOffset U n_max + numBuckets n_max + j.val), hlt⟩,
      mem (base + slotOffset U n_max + 2 * numBuckets n_max + j.val), ?_, ?_⟩
    · rw [extractSlots_eq_some_iff hwf]
      exact ⟨h1, rfl, rfl⟩
    · intro heq
      exact hne (congrArg Fin.val heq)

/-- Coupled representation invariant `Rep w base U V n_max θ s x` on `Data 12`:
* `x.Bounded w`;
* `x.regs 0 = base`;
* `TabulatedOddStride.Rep` holds for `θ.2` at `[base, base + tabSpace U n_max)`;
* `x.mem (base + tabSpace U n_max) = θ.1.val` holds the multiply-shift seed;
* `SlotArrayWF base U n_max x.mem` and `UniformProbing.TableRep (probePerm θ) s (extractSlots ...)`
  hold on the slot arrays;
* `(Dictionary.dom s).card ≤ n_max` and `Dictionary.ValuesBounded V s`. -/
structure Rep (w base U V n_max : ℕ) (θ : Seed U n_max) (s : Dictionary.State U)
    (x : Data 12) : Prop where
  bounded : x.Bounded w
  regs_base : x.regs 0 = base
  tab_rep : TabulatedOddStride.Rep base (charBits n_max) (numChars U n_max)
    (bucketBits n_max) θ.2 x.mem
  ms_seed : x.mem (base + tabSpace U n_max) = θ.1.val
  slot_wf : SlotArrayWF base U n_max x.mem
  table_rep : UniformProbing.TableRep (probePerm θ) s (extractSlots base U n_max x.mem)
  dom_le : (Dictionary.dom s).card ≤ n_max
  vals_bounded : Dictionary.ValuesBounded V s

theorem Rep.unique {w base U V n_max : ℕ} {θ : Seed U n_max}
    {s₁ s₂ : Dictionary.State U} {x : Data 12}
    (h₁ : Rep w base U V n_max θ s₁ x) (h₂ : Rep w base U V n_max θ s₂ x) :
    s₁ = s₂ := by
  funext u
  cases hs₁ : s₁ u with
  | none =>
    cases hs₂ : s₂ u with
    | none => rfl
    | some v₂ =>
      obtain ⟨hlt, hT⟩ := h₂.table_rep.key_spec u v₂ hs₂
      have hs₁' := (h₁.table_rep.slot_spec _ u v₂ hT).1
      rw [hs₁] at hs₁'
      cases hs₁'
  | some v₁ =>
    obtain ⟨hlt, hT⟩ := h₁.table_rep.key_spec u v₁ hs₁
    exact (h₂.table_rep.slot_spec _ u v₁ hT).1.symm

theorem mem_footprint_of_lt_space {base U n_max a : ℕ}
    (hlo : base ≤ a) (hhi : a < base + space U n_max) :
    a ∈ (Block.mk base (space U n_max)).footprint := by
  rw [Block.mem_footprint]
  exact ⟨hlo, hhi⟩

theorem SlotArrayWF.congr_mem {base U n_max : ℕ} {mem mem' : ℕ → ℕ}
    (hmem : ∀ a ∈ (Block.mk base (space U n_max)).footprint, mem' a = mem a)
    (hwf : SlotArrayWF base U n_max mem) :
    SlotArrayWF base U n_max mem' := by
  intro j
  have hj := j.isLt
  have hsp : space U n_max = slotOffset U n_max + 3 * numBuckets n_max := rfl
  have h0 : mem' (base + slotOffset U n_max + j.val) =
      mem (base + slotOffset U n_max + j.val) :=
    hmem _ (mem_footprint_of_lt_space (by omega) (by omega))
  have h1 : mem' (base + slotOffset U n_max + numBuckets n_max + j.val) =
      mem (base + slotOffset U n_max + numBuckets n_max + j.val) :=
    hmem _ (mem_footprint_of_lt_space (by omega) (by omega))
  dsimp only [SlotArrayWF] at hwf ⊢
  rw [h0, h1]
  exact hwf j

theorem extractSlots_congr_mem {base U n_max : ℕ} {mem mem' : ℕ → ℕ}
    (hmem : ∀ a ∈ (Block.mk base (space U n_max)).footprint, mem' a = mem a) :
    extractSlots base U n_max mem' = extractSlots base U n_max mem := by
  funext j
  have hj := j.isLt
  have hsp : space U n_max = slotOffset U n_max + 3 * numBuckets n_max := rfl
  have h0 : mem' (base + slotOffset U n_max + j.val) =
      mem (base + slotOffset U n_max + j.val) :=
    hmem _ (mem_footprint_of_lt_space (by omega) (by omega))
  have h1 : mem' (base + slotOffset U n_max + numBuckets n_max + j.val) =
      mem (base + slotOffset U n_max + numBuckets n_max + j.val) :=
    hmem _ (mem_footprint_of_lt_space (by omega) (by omega))
  have h2 : mem' (base + slotOffset U n_max + 2 * numBuckets n_max + j.val) =
      mem (base + slotOffset U n_max + 2 * numBuckets n_max + j.val) :=
    hmem _ (mem_footprint_of_lt_space (by omega) (by omega))
  dsimp only [extractSlots]
  rw [h0, h1, h2]

theorem Rep.congr {w base U V n_max : ℕ} {θ : Seed U n_max} {s : Dictionary.State U}
    {x x' : Data 12}
    (hbdd : x'.Bounded w) (hbase : x'.regs 0 = x.regs 0)
    (hmem : ∀ a ∈ (Block.mk base (space U n_max)).footprint, x'.mem a = x.mem a)
    (hrep : Rep w base U V n_max θ s x) :
    Rep w base U V n_max θ s x' := by
  have hsp : space U n_max =
      (4 + numChars U n_max * 2 ^ charBits n_max) + 1 + 3 * numBuckets n_max := rfl
  have htab_eq : tabSpace U n_max = 4 + numChars U n_max * 2 ^ charBits n_max := rfl
  have htab : TabulatedOddStride.Rep base (charBits n_max) (numChars U n_max)
      (bucketBits n_max) θ.2 x'.mem := by
    rcases hrep.tab_rep with ⟨hm0, hm1, hm2, hm3, hmt⟩
    refine ⟨?_, ?_, ?_, ?_, fun i => ?_⟩
    · rw [hmem base (mem_footprint_of_lt_space (by omega) (by omega)), hm0]
    · rw [hmem (base + 1) (mem_footprint_of_lt_space (by omega) (by omega)), hm1]
    · rw [hmem (base + 2) (mem_footprint_of_lt_space (by omega) (by omega)), hm2]
    · rw [hmem (base + 3) (mem_footprint_of_lt_space (by omega) (by omega)), hm3]
    · have hi := i.isLt
      rw [hmem (base + 4 + i.val) (mem_footprint_of_lt_space (by omega) (by omega)), hmt i]
  have hms : x'.mem (base + tabSpace U n_max) = θ.1.val := by
    rw [hmem (base + tabSpace U n_max) (mem_footprint_of_lt_space (by omega) (by omega)),
      hrep.ms_seed]
  refine ⟨hbdd, hbase.trans hrep.regs_base, htab, hms,
    hrep.slot_wf.congr_mem hmem, ?_, hrep.dom_le, hrep.vals_bounded⟩
  rw [extractSlots_congr_mem hmem]
  exact hrep.table_rep

theorem slotArrayWF_of_zero {base U n_max : ℕ} {mem : ℕ → ℕ}
    (hz : ∀ j : Fin (numBuckets n_max), mem (base + slotOffset U n_max + j.val) = 0) :
    SlotArrayWF base U n_max mem := by
  intro j
  refine ⟨Or.inl (hz j), ?_⟩
  rw [hz j]
  intro h
  omega

theorem extractSlots_eq_emptyTable_of_zero {base U n_max : ℕ} {mem : ℕ → ℕ}
    (hz : ∀ j : Fin (numBuckets n_max), mem (base + slotOffset U n_max + j.val) = 0) :
    extractSlots base U n_max mem = emptyTable U (numBuckets n_max) := by
  funext j
  simp [extractSlots, emptyTable, hz j]

/-! ## Section 3: Register Layout, Allocation, and Randomized Initialization -/

/-- Register `0` (`baseReg`, persistent): holds the base memory address `base`. -/
abbrev regBase : Fin 12 := 0

/-- Register `1` (`curReg`): loop condition / multiply-shift seed / tabulation key scratch. -/
abbrev regCond : Fin 12 := 1

/-- Register `2` (`zeroReg`): memory address / multiply-shift key / tabulation output scratch. -/
abbrev regAddr : Fin 12 := 2

/-- Register `3` (`oneReg`): current probe slot `slot ∈ Fin (numBuckets n_max)`. -/
abbrev regSlot : Fin 12 := 3

/-- Register `4`: slot array base address `base + slotOffset U n_max`. -/
abbrev regSlotBase : Fin 12 := 4

/-- Register `5`: bucket mask `numBuckets n_max - 1`. -/
abbrev regMaskM : Fin 12 := 5

/-- Register `6`: odd probe stride `strideHash θ u`. -/
abbrev regStride : Fin 12 := 6

/-- Register `7`: table size `numBuckets n_max`. -/
abbrev regM : Fin 12 := 7

/-- Register `8`: constant `0` during probing / general scratch. -/
abbrev regZero : Fin 12 := 8

/-- Register `9` (`output`): operation tag (`0` for `get`, `1` for `insert`) on input; decoded
return value (`0` for `none`/`()`, `v + 1` for `some v`) on output. -/
abbrev regOp : Fin 12 := 9

/-- Register `10`: input key `u.val < U`. -/
abbrev regU : Fin 12 := 10

/-- Register `11` (`frontierReg`): input value `v < V` for `insert` / allocation frontier. -/
abbrev regV : Fin 12 := 11

/-- Register injection `Fin 5 → Fin 12` embedding `MultiplyShift` into registers `1..5`
(preserving `regBase = 0` and `6..11`). -/
def msMap : Fin 5 → Fin 12 :=
  fun i => ⟨i.val + 1, by omega⟩

theorem injective_msMap : Function.Injective msMap := by
  intro i j h
  ext
  simpa [msMap] using congrArg Fin.val h

theorem notMem_range_msMap {j : Fin 12} (hj : j.val = 0 ∨ 6 ≤ j.val) :
    j ∉ Set.range msMap := by
  rintro ⟨i, rfl⟩
  have := i.isLt
  simp only [msMap] at hj
  omega

/-- Register injection `Fin 9 → Fin 12` embedding `TabulatedOddStride` into registers `0..8`
(with `tabMap 0 = regBase` and preserving `regOp = 9`, `regU = 10`, `regV = 11`). -/
def tabMap : Fin 9 → Fin 12 :=
  fun i => ⟨i.val, by omega⟩

theorem injective_tabMap : Function.Injective tabMap := by
  intro i j h
  ext
  simpa [tabMap] using congrArg Fin.val h

theorem notMem_range_tabMap {j : Fin 12} (hj : 9 ≤ j.val) :
    j ∉ Set.range tabMap := by
  rintro ⟨i, rfl⟩
  have := i.isLt
  simp only [tabMap] at hj
  omega

/-- Allocation program `allocSpan U n_max` (3 instructions): copies `frontierReg` (`regV`) to
`baseReg` (`regBase`) and advances `frontierReg` by `space U n_max`. -/
def allocSpan (U n_max : ℕ) : Code .exact 12 :=
  .seq (.op (.copy regBase regV))
  (.seq (.op (.const regCond (space U n_max)))
        (.op (.exactBin .add regV regBase regCond)))

theorem allocSpan_execWithin {w base U n_max : ℕ} {x : Data 12}
    (hS : Fits w (base + space U n_max)) (hfr : x.regs regV = base) :
    ∃ x₁ : Data 12,
      ExecWithin w (allocSpan U n_max) x x₁ 3 ∧
      x₁.mem = x.mem ∧
      x₁.regs regBase = base ∧
      x₁.regs regV = base + space U n_max := by
  have hfit_sp : Fits w (space U n_max) := hS.of_le (by omega)
  set s1 := x.set regBase base
  have e1 : Exec w (.op (.copy regBase regV) : Code .exact 12) x s1 1 := by
    simpa [s1, hfr] using (Exec.copy (B := .exact) (w := w) (d := regBase) (s := regV) (x := x))
  set s2 := s1.set regCond (space U n_max)
  have e2 : Exec w (.op (.const regCond (space U n_max)) : Code .exact 12) s1 s2 1 :=
    Exec.const hfit_sp
  set s3 := s2.set regV (base + space U n_max)
  have e3 : Exec w (.op (.exactBin .add regV regBase regCond) : Code .exact 12) s2 s3 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s2, s1]) hS
  exact ⟨s3, (e1.seq (e2.seq e3)).within, rfl,
    by simp +decide [s3, s2, s1], by simp +decide [s3]⟩

/-- Deterministic 5-instruction glue between `MultiplyShift.initCode` and
`TabulatedOddStride.initFromBCode`: stores the multiply-shift seed `regCond` at
`base + tabSpace U n_max` and loads `charBits n_max` into `regMaskM` and `bucketBits n_max` into
`regAddr`. -/
def initMidCode (U n_max : ℕ) : Code .exact 12 :=
  .seq (.op (.const regAddr (tabSpace U n_max)))
  (.seq (.op (.exactBin .add regAddr regBase regAddr))
  (.seq (.op (.store regAddr regCond))
  (.seq (.op (.const regMaskM (charBits n_max)))
        (.op (.const regAddr (bucketBits n_max))))))

/-- Closed-form machine state after `initMidCode U n_max`. -/
def initMidData (base U n_max : ℕ) (d : Data 12) : Data 12 :=
  ((((d.set regAddr (tabSpace U n_max)).set regAddr (base + tabSpace U n_max)).write
    (base + tabSpace U n_max) (d.regs regCond)).set regMaskM (charBits n_max)).set
    regAddr (bucketBits n_max)

theorem fits_of_space {w base U n_max : ℕ} (hS : Fits w (base + space U n_max)) :
    Fits w (base + tabSpace U n_max) ∧
    Fits w (2 ^ charBits n_max) ∧
    Fits w (2 ^ bucketBits n_max) ∧
    Fits w (numChars U n_max) ∧
    Fits w (charBits n_max) ∧
    Fits w (bucketBits n_max) := by
  have hd : 1 ≤ numChars U n_max := one_le_numChars U n_max
  have hpowB_pos : 1 ≤ 2 ^ charBits n_max := Nat.one_le_two_pow
  have hpowB_le : 2 ^ charBits n_max ≤ numChars U n_max * 2 ^ charBits n_max :=
    Nat.le_mul_of_pos_left _ hd
  have hd_le : numChars U n_max ≤ numChars U n_max * 2 ^ charBits n_max :=
    Nat.le_mul_of_pos_right _ hpowB_pos
  have htab : tabSpace U n_max = 4 + numChars U n_max * 2 ^ charBits n_max := rfl
  have hsp : space U n_max = tabSpace U n_max + 1 + 3 * numBuckets n_max := rfl
  have hcb_lt : charBits n_max < 2 ^ charBits n_max := Nat.lt_two_pow_self
  have hbb_lt : bucketBits n_max < 2 ^ bucketBits n_max := Nat.lt_two_pow_self
  have hM : 2 ^ bucketBits n_max = numBuckets n_max := rfl
  refine ⟨hS.of_le (by omega), hS.of_le (by omega), hS.of_le (by omega),
    hS.of_le (by omega), hS.of_le (by omega), hS.of_le (by omega)⟩

theorem initMidCode_exec {w base U n_max : ℕ} {d : Data 12}
    (hbase : d.regs regBase = base) (hS : Fits w (base + space U n_max)) :
    Exec w (initMidCode U n_max) d (initMidData base U n_max d) 5 := by
  obtain ⟨hfit_btab, _, _, _, hfit_cb, hfit_bb⟩ := fits_of_space hS
  have hfit_tab : Fits w (tabSpace U n_max) := hfit_btab.of_le (by omega)
  set s1 := d.set regAddr (tabSpace U n_max)
  have e1 : Exec w (.op (.const regAddr (tabSpace U n_max)) : Code .exact 12) d s1 1 :=
    Exec.const hfit_tab
  set s2 := s1.set regAddr (base + tabSpace U n_max)
  have e2 : Exec w (.op (.exactBin .add regAddr regBase regAddr) : Code .exact 12) s1 s2 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s1, hbase]) hfit_btab
  set s3 := s2.write (base + tabSpace U n_max) (d.regs regCond)
  have e3 : Exec w (.op (.store regAddr regCond) : Code .exact 12) s2 s3 1 := by
    simpa +decide [s3, s2, s1] using
      (Exec.store (B := .exact) (w := w) (a := regAddr) (s := regCond) (x := s2))
  set s4 := s3.set regMaskM (charBits n_max)
  have e4 : Exec w (.op (.const regMaskM (charBits n_max)) : Code .exact 12) s3 s4 1 :=
    Exec.const hfit_cb
  set s5 := s4.set regAddr (bucketBits n_max)
  have e5 : Exec w (.op (.const regAddr (bucketBits n_max)) : Code .exact 12) s4 s5 1 :=
    Exec.const hfit_bb
  exact e1.seq (e2.seq (e3.seq (e4.seq e5)))

/-- Complete randomized setup program `initSetup U n_max`: samples the multiply-shift seed,
stores it at `base + tabSpace U n_max`, and initializes the `TabulatedOddStride` table at
`[base, base + tabSpace U n_max)`. -/
def initSetup (U n_max : ℕ) : Code .exact 12 :=
  .seq ((MultiplyShift.initCode (hashBits U n_max)).rename msMap)
  (.seq (initMidCode U n_max)
        ((TabulatedOddStride.initFromBCode (numChars U n_max)).rename tabMap))

/-- Total instruction count `5 * (numChars U n_max * 2 ^ charBits n_max) + 25` of `initSetup`. -/
def setupSteps (U n_max : ℕ) : ℕ :=
  5 * (numChars U n_max * 2 ^ charBits n_max) + 25

/-- Extract the multiply-shift seed from `mem (base + tabSpace U n_max)`. -/
def extractMSSeedFromMem (base U n_max : ℕ) (mem : ℕ → ℕ) : Fin (2 ^ (hashBits U n_max - 1)) :=
  if h : mem (base + tabSpace U n_max) < 2 ^ (hashBits U n_max - 1) then
    ⟨mem (base + tabSpace U n_max), h⟩
  else
    ⟨0, Nat.two_pow_pos _⟩

/-- Extract the combined seed `Seed U n_max` from machine state `y`. -/
def extractSeedPair (base U n_max : ℕ) (y : Data 12) : Seed U n_max :=
  (extractMSSeedFromMem base U n_max y.mem,
    TabulatedOddStride.extractTable base (charBits n_max) (numChars U n_max) (bucketBits n_max)
      y.mem)

/-- Stage-1 state distribution produced by
`(MultiplyShift.initCode (hashBits U n_max)).rename msMap`. -/
noncomputable def msInitPMF (U n_max : ℕ) (x₁ : Data 12) : PMF (Data 12) :=
  (Prod.fst <$>
    ((fun z => (z.1.extend msMap x₁, z.2)) <$>
      MultiplyShift.initComp (hashBits U n_max) (x₁.comap msMap))).eval

/-- Stage-3 state distribution produced by
`(TabulatedOddStride.initFromBCode (numChars U n_max)).rename tabMap`. -/
noncomputable def tabInitPMF (base U n_max : ℕ) (y₂ : Data 12) : PMF (Data 12) :=
  (Prod.fst <$>
    ((fun z => (z.1.extend tabMap y₂, z.2)) <$>
      TabulatedOddStride.initFromBComp base (charBits n_max) (numChars U n_max) (bucketBits n_max)
        (y₂.comap tabMap))).eval

/-- Output state distribution of `initSetup U n_max`. -/
noncomputable def initSetupPMF (base U n_max : ℕ) (x₁ : Data 12) : PMF (Data 12) :=
  (msInitPMF U n_max x₁).bind (fun y₁ => tabInitPMF base U n_max (initMidData base U n_max y₁))

/-- Coupled `(Seed × Data 12)` distribution produced by `initSetup U n_max`. -/
noncomputable def initSeedStatePMF (base U n_max : ℕ) (x₁ : Data 12) :
    PMF (Seed U n_max × Data 12) :=
  (initSetupPMF base U n_max x₁).map (fun y => (extractSeedPair base U n_max y, y))

theorem mem_support_msInitPMF {U n_max : ℕ} {x₁ y₁ : Data 12}
    (hy₁ : y₁ ∈ (msInitPMF U n_max x₁).support) :
    y₁.regs regBase = x₁.regs regBase ∧
    y₁.regs regV = x₁.regs regV ∧
    y₁.regs regCond < 2 ^ (hashBits U n_max - 1) ∧
    (y₁.comap msMap).regs MultiplyShift.regB = y₁.regs regCond ∧
    y₁.mem = x₁.mem := by
  dsimp only [msInitPMF] at hy₁
  rw [Functor.map_map, ProbComp.eval_map, PMF.mem_support_map_iff] at hy₁
  obtain ⟨z, hz, rfl⟩ := hy₁
  rw [ProbComp.support_eval] at hz
  dsimp only [MultiplyShift.initComp] at hz
  obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
  cases OracleComp.eq_of_mem_supportWith_pure hk
  have hlt : k.val < 2 ^ (hashBits U n_max - 1) := by
    have hpos : 1 ≤ 2 ^ (hashBits U n_max - 1) := Nat.one_le_two_pow
    have hk_lt := k.isLt
    omega
  refine ⟨Data.extend_regs_of_notMem _ _ (notMem_range_msMap (by decide)),
    Data.extend_regs_of_notMem _ _ (notMem_range_msMap (by decide)), ?_, rfl, rfl⟩
  change ((MultiplyShift.initData (hashBits U n_max) (x₁.comap msMap) k.val).extend msMap
    x₁ |>.comap msMap).regs MultiplyShift.regB < 2 ^ (hashBits U n_max - 1)
  rw [Data.comap_extend injective_msMap]
  simpa [MultiplyShift.initData] using hlt

theorem map_extractSeed_msInitPMF (U n_max : ℕ) (x₁ : Data 12) :
    (msInitPMF U n_max x₁).map
        (fun y₁ => MultiplyShift.extractSeed (hashBits U n_max) (y₁.comap msMap)) =
      PMF.uniformOfFintype (Fin (2 ^ (hashBits U n_max - 1))) := by
  dsimp only [msInitPMF]
  rw [Functor.map_map, ProbComp.eval_map, PMF.map_comp]
  have hcomp :
      ((fun y₁ : Data 12 => MultiplyShift.extractSeed (hashBits U n_max) (y₁.comap msMap)) ∘
        fun x : Data 5 × ℕ => x.1.extend msMap x₁) =
      fun x : Data 5 × ℕ => MultiplyShift.extractSeed (hashBits U n_max) x.1 := by
    funext z
    simp [Data.comap_extend injective_msMap]
  rw [hcomp]
  exact MultiplyShift.map_extractSeed_eval_initComp (hashBits U n_max) (x₁.comap msMap)

theorem mem_support_tabInitPMF {base U n_max : ℕ} {y₂ y : Data 12}
    (hbase : y₂.regs regBase = base)
    (hy : y ∈ (tabInitPMF base U n_max y₂).support) :
    TabulatedOddStride.Rep base (charBits n_max) (numChars U n_max) (bucketBits n_max)
      (TabulatedOddStride.extractTable base (charBits n_max) (numChars U n_max) (bucketBits n_max)
        y.mem) y.mem ∧
    y.regs regBase = base ∧
    y.regs regV = y₂.regs regV ∧
    (∀ a, (a < base ∨ base + tabSpace U n_max ≤ a) → y.mem a = y₂.mem a) := by
  dsimp only [tabInitPMF] at hy
  rw [Functor.map_map, ProbComp.eval_map, PMF.mem_support_map_iff] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [ProbComp.support_eval] at hz
  have hbase_comap : (y₂.comap tabMap).regs TabulatedOddStride.regBase = base := hbase
  obtain ⟨-, hrep, hbase', hframe⟩ :=
    TabulatedOddStride.mem_support_initFromBComp hbase_comap hz
  have hbase_ext : (z.1.extend tabMap y₂).regs regBase = base := by
    change ((z.1.extend tabMap y₂).comap tabMap).regs TabulatedOddStride.regBase = base
    rw [Data.comap_extend injective_tabMap]
    exact hbase'
  have hv_ext : (z.1.extend tabMap y₂).regs regV = y₂.regs regV :=
    Data.extend_regs_of_notMem _ _ (notMem_range_tabMap (by decide))
  exact ⟨hrep, hbase_ext, hv_ext, hframe⟩

theorem map_extractSeedPair_tabInitPMF {base U n_max : ℕ} {y₁ : Data 12}
    (hbase : y₁.regs regBase = base)
    (hcond : y₁.regs regCond < 2 ^ (hashBits U n_max - 1)) :
    (tabInitPMF base U n_max (initMidData base U n_max y₁)).map (extractSeedPair base U n_max) =
      (PMF.uniformOfFintype
        (Fin (numChars U n_max * 2 ^ charBits n_max) → Fin (numBuckets n_max))).map
        (fun T => (MultiplyShift.extractSeed (hashBits U n_max) (y₁.comap msMap), T)) := by
  set y₂ := initMidData base U n_max y₁
  have hy₂_base : y₂.regs regBase = base := by
    simpa [y₂, initMidData, regBase, regAddr, regMaskM] using hbase
  have hcongr :
      (tabInitPMF base U n_max y₂).map (extractSeedPair base U n_max) =
      (tabInitPMF base U n_max y₂).map
        (fun y =>
          (MultiplyShift.extractSeed (hashBits U n_max) (y₁.comap msMap),
            TabulatedOddStride.extractTable base (charBits n_max) (numChars U n_max)
              (bucketBits n_max) y.mem)) := by
    apply PMF.map_congr_on_support
    intro y hy
    obtain ⟨-, -, -, hframe⟩ := mem_support_tabInitPMF hy₂_base hy
    have hms_mem : y.mem (base + tabSpace U n_max) = y₁.regs regCond := by
      rw [hframe (base + tabSpace U n_max) (Or.inr le_rfl)]
      simp [y₂, initMidData, Data.write]
    have hms_eq : extractMSSeedFromMem base U n_max y.mem =
        MultiplyShift.extractSeed (hashBits U n_max) (y₁.comap msMap) := by
      have hregB : y₁.regs (msMap MultiplyShift.regB) = y₁.regs regCond := rfl
      apply Fin.ext
      dsimp only [extractMSSeedFromMem, MultiplyShift.extractSeed, Data.comap]
      simp [hms_mem, hregB, hcond]
    exact Prod.ext hms_eq rfl
  rw [hcongr]
  dsimp only [tabInitPMF]
  rw [Functor.map_map, ProbComp.eval_map, PMF.map_comp]
  have hcomp :
      ((fun y : Data 12 =>
          (MultiplyShift.extractSeed (hashBits U n_max) (y₁.comap msMap),
            TabulatedOddStride.extractTable base (charBits n_max) (numChars U n_max)
              (bucketBits n_max) y.mem)) ∘
        fun z : Data 9 × ℕ => z.1.extend tabMap y₂) =
      ((fun T => (MultiplyShift.extractSeed (hashBits U n_max) (y₁.comap msMap), T)) ∘
        fun z : Data 9 × ℕ =>
          TabulatedOddStride.extractTable base (charBits n_max) (numChars U n_max)
            (bucketBits n_max) z.1.mem) := rfl
  rw [hcomp, ← PMF.map_comp]
  change (((TabulatedOddStride.initFromBComp base (charBits n_max) (numChars U n_max)
      (bucketBits n_max) (y₂.comap tabMap)).eval).map
      (fun z => TabulatedOddStride.extractTable base (charBits n_max) (numChars U n_max)
        (bucketBits n_max) z.1.mem)).map
      (fun T => (MultiplyShift.extractSeed (hashBits U n_max) (y₁.comap msMap), T)) =
    (PMF.uniformOfFintype
      (Fin (numChars U n_max * 2 ^ charBits n_max) → Fin (2 ^ bucketBits n_max))).map
      (fun T => (MultiplyShift.extractSeed (hashBits U n_max) (y₁.comap msMap), T))
  rw [TabulatedOddStride.map_extractTable_eval_initFromBComp]

/-- **Exact uniformity of the sampled seed pair**: the seed marginal of `initSeedStatePMF` is the
exact product uniform distribution `seedLaw U n_max`. -/
theorem map_fst_initSeedStatePMF {base U n_max : ℕ} {x₁ : Data 12}
    (hbase : x₁.regs regBase = base) :
    (initSeedStatePMF base U n_max x₁).map Prod.fst = seedLaw U n_max := by
  dsimp only [initSeedStatePMF, initSetupPMF]
  rw [PMF.map_comp]
  have hfst : Prod.fst ∘ (fun y : Data 12 => (extractSeedPair base U n_max y, y)) =
      extractSeedPair base U n_max := rfl
  rw [hfst, PMF.map_bind]
  let μ_tab : PMF (Fin (numChars U n_max * 2 ^ charBits n_max) → Fin (numBuckets n_max)) :=
    PMF.uniformOfFintype
      (Fin (numChars U n_max * 2 ^ charBits n_max) → Fin (numBuckets n_max))
  have hbind :
      (msInitPMF U n_max x₁).bind
        (fun y₁ => (tabInitPMF base U n_max (initMidData base U n_max y₁)).map
          (extractSeedPair base U n_max)) =
      (msInitPMF U n_max x₁).bind
        (fun y₁ => μ_tab.map
          (fun T => (MultiplyShift.extractSeed (hashBits U n_max) (y₁.comap msMap), T))) := by
    ext θ
    rw [PMF.bind_apply, PMF.bind_apply]
    refine tsum_congr fun y₁ => ?_
    by_cases hy₁ : y₁ ∈ (msInitPMF U n_max x₁).support
    · obtain ⟨hb₁, -, hcond₁, -, -⟩ := mem_support_msInitPMF hy₁
      rw [map_extractSeedPair_tabInitPMF (hb₁.trans hbase) hcond₁]
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hy₁, zero_mul, zero_mul]
  rw [hbind]
  have hmap_bind :
      (msInitPMF U n_max x₁).bind
        (fun y₁ => μ_tab.map
          (fun T => (MultiplyShift.extractSeed (hashBits U n_max) (y₁.comap msMap), T))) =
      ((msInitPMF U n_max x₁).map
        (fun y₁ => MultiplyShift.extractSeed (hashBits U n_max) (y₁.comap msMap))).bind
        (fun b => μ_tab.map (fun T => (b, T))) := by
    rw [PMF.bind_map]
    rfl
  rw [hmap_bind, map_extractSeed_msInitPMF]
  exact Cslib.Probability.PMF.uniformOfFintype_prod _ _

theorem initSetup_execCodeDist {w base U n_max : ℕ} {x₁ : Data 12}
    (hbase : x₁.regs regBase = base) (hS : Fits w (base + space U n_max))
    (hw : 2 * hashBits U n_max ≤ w) :
    ExecCodeDist w (initSetup U n_max) x₁ (initSetupPMF base U n_max x₁) (setupSteps U n_max) := by
  have hw₀ : hashBits U n_max ≤ w := by omega
  obtain ⟨hfit_btab, hfit_powB, hfit_powM, hfit_d, -, -⟩ := fits_of_space hS
  have hms_rand :=
    (MultiplyShift.initCode_execRand (w := w) hw₀ (x₁.comap msMap)).rename injective_msMap
  have hms_dist : ExecCodeDist w
      ((MultiplyShift.initCode (hashBits U n_max)).rename msMap) x₁
      (msInitPMF U n_max x₁) 2 := by
    refine (ExecCodeDist.of_execRand hms_rand).congr_dist rfl ?_
    rw [ProbComp.expect_map]
    refine (ProbComp.expect_mono_on_support fun z hz => ?_).trans
      (le_of_eq (ProbComp.expect_const _ 2))
    dsimp only [MultiplyShift.initComp] at hz
    obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hk
    exact le_rfl
  have hrest : ∀ y₁ ∈ (msInitPMF U n_max x₁).support,
      ExecCodeDist w
        (.seq (initMidCode U n_max)
          ((TabulatedOddStride.initFromBCode (numChars U n_max)).rename tabMap))
        y₁ (tabInitPMF base U n_max (initMidData base U n_max y₁))
        (5 + (5 * (numChars U n_max * 2 ^ charBits n_max) + 18 : ℕ)) := by
    intro y₁ hy₁
    obtain ⟨hb₁, -, -, -, -⟩ := mem_support_msInitPMF hy₁
    have hmid := ExecCodeDist.of_exec (initMidCode_exec (hb₁.trans hbase) hS)
    set y₂ := initMidData base U n_max y₁
    have hy₂_base : (y₂.comap tabMap).regs TabulatedOddStride.regBase = base := by
      simpa +decide [y₂, initMidData, tabMap, Data.comap] using hb₁.trans hbase
    have hy₂_b : (y₂.comap tabMap).regs TabulatedOddStride.regB = charBits n_max := by
      simp +decide [y₂, initMidData, tabMap, Data.comap]
    have hy₂_M : (y₂.comap tabMap).regs TabulatedOddStride.regOut = bucketBits n_max := by
      simp +decide [y₂, initMidData, tabMap, Data.comap]
    have htab_rand :=
      (TabulatedOddStride.initFromBCode_execRand (w := w)
        hy₂_base hy₂_b hy₂_M hfit_btab hfit_powB hfit_powM hfit_d).rename injective_tabMap
    have htab_dist : ExecCodeDist w
        ((TabulatedOddStride.initFromBCode (numChars U n_max)).rename tabMap) y₂
        (tabInitPMF base U n_max y₂)
        (5 * (numChars U n_max * 2 ^ charBits n_max) + 18 : ℕ) := by
      refine (ExecCodeDist.of_execRand htab_rand).congr_dist rfl ?_
      rw [ProbComp.expect_map]
      refine (ProbComp.expect_mono_on_support fun z hz => ?_).trans
        (le_of_eq (ProbComp.expect_const _ _))
      obtain ⟨hsteps, -, -, -⟩ := TabulatedOddStride.mem_support_initFromBComp hy₂_base hz
      exact_mod_cast hsteps.le
    exact hmid.seq_pure htab_dist
  have hseq := hms_dist.seq_const hrest (fun _ _ => le_rfl)
  refine hseq.congr_dist rfl ?_
  dsimp only [setupSteps]
  norm_cast
  omega

/-- Full `SubroutineDS.setup_exec` certificate for `initSetup U n_max`. -/
theorem setup_exec_spec {w base U V n_max : ℕ} {x₁ : Data 12}
    (hS : Fits w (base + space U n_max)) (hw : 2 * hashBits U n_max ≤ w)
    (hx₁ : x₁.Bounded w) (hbase : x₁.regs regBase = base)
    (hfr : x₁.regs regV = base + space U n_max)
    (hz : ∀ a ∈ (Block.mk base (space U n_max)).footprint, x₁.mem a = 0) :
    ∃ ν₀ : PMF (Seed U n_max × Data 12),
      ExecCodeDist w (initSetup U n_max) x₁ (ν₀.map Prod.snd) (setupSteps U n_max) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ 1 * seedLaw U n_max θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs regV = base + space U n_max ∧
        Rep w base U V n_max p.1 (Dictionary.empty U) p.2 ∧
        (0 : ℕ) ≤ 0 ∧
        Modifies (Block.mk base (space U n_max)).footprint x₁.mem p.2.mem := by
  refine ⟨initSeedStatePMF base U n_max x₁, ?_, ?_, ?_⟩
  · have hsnd : (initSeedStatePMF base U n_max x₁).map Prod.snd =
        initSetupPMF base U n_max x₁ := by
      dsimp only [initSeedStatePMF]
      rw [PMF.map_comp]
      exact PMF.map_id _
    rw [hsnd]
    exact initSetup_execCodeDist hbase hS hw
  · intro θ
    rw [map_fst_initSeedStatePMF hbase, one_mul]
  · intro p hp
    dsimp only [initSeedStatePMF] at hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨y, hy, rfl⟩ := hp
    have hbdd_y : y.Bounded w :=
      (initSetup_execCodeDist hbase hS hw).bounded hx₁ y hy
    dsimp only [initSetupPMF] at hy
    rw [PMF.mem_support_bind_iff] at hy
    obtain ⟨y₁, hy₁, hy₃⟩ := hy
    obtain ⟨hb₁, hv₁, hcond₁, -, hmem₁⟩ := mem_support_msInitPMF hy₁
    set y₂ := initMidData base U n_max y₁
    have hy₂_base : y₂.regs regBase = base := by
      simpa +decide [y₂, initMidData] using hb₁.trans hbase
    obtain ⟨htab_rep, hy_base, hy_v, hframe₃⟩ := mem_support_tabInitPMF hy₂_base hy₃
    have hy_v_eq : y.regs regV = base + space U n_max := by
      rw [hy_v]
      simpa +decide [y₂, initMidData, hv₁] using hfr
    have hms_mem : y.mem (base + tabSpace U n_max) = y₁.regs regCond := by
      rw [hframe₃ (base + tabSpace U n_max) (Or.inr le_rfl)]
      simp [y₂, initMidData, Data.write]
    have hms_seed : y.mem (base + tabSpace U n_max) = (extractSeedPair base U n_max y).1.val := by
      dsimp only [extractSeedPair, extractMSSeedFromMem]
      have hlt_mem : y.mem (base + tabSpace U n_max) < 2 ^ (hashBits U n_max - 1) := by
        rwa [hms_mem]
      simp [hlt_mem]
    have hz_slots : ∀ j : Fin (numBuckets n_max),
        y.mem (base + slotOffset U n_max + j.val) = 0 := by
      intro j
      have hj := j.isLt
      have hsp : space U n_max = slotOffset U n_max + 3 * numBuckets n_max := rfl
      have hso : slotOffset U n_max = tabSpace U n_max + 1 := rfl
      rw [hframe₃ (base + slotOffset U n_max + j.val) (Or.inr (by omega))]
      have hne : base + slotOffset U n_max + j.val ≠ base + tabSpace U n_max := by omega
      simpa [y₂, initMidData, Data.write, Function.update_of_ne hne, hmem₁] using
        hz _ (mem_footprint_of_lt_space (by omega) (by omega))
    have hwf : SlotArrayWF base U n_max y.mem := slotArrayWF_of_zero hz_slots
    have hempty : extractSlots base U n_max y.mem = emptyTable U (numBuckets n_max) :=
      extractSlots_eq_emptyTable_of_zero hz_slots
    have htrep : TableRep (probePerm (extractSeedPair base U n_max y))
        (Dictionary.empty U) (extractSlots base U n_max y.mem) := by
      rw [hempty]
      exact tableRep_empty _
    have hmod : Modifies (Block.mk base (space U n_max)).footprint x₁.mem y.mem := by
      intro a ha
      have ha_out : a < base ∨ base + space U n_max ≤ a := by
        by_contra h
        rw [not_or, not_lt, not_le] at h
        exact ha (mem_footprint_of_lt_space h.1 h.2)
      have hsp : space U n_max = tabSpace U n_max + 1 + 3 * numBuckets n_max := rfl
      have ha₃ : a < base ∨ base + tabSpace U n_max ≤ a := by omega
      have hne : a ≠ base + tabSpace U n_max := by omega
      rw [hframe₃ a ha₃]
      simp [y₂, initMidData, Data.write, Function.update_of_ne hne, hmem₁]
    refine ⟨hy_v_eq, ⟨hbdd_y, hy_base, htab_rep, hms_seed, hwf, htrep, ?_, ?_⟩, le_rfl, hmod⟩
    · simp
    · exact Dictionary.valuesBounded_empty U V

/-! ## Section 4: Lookup and Insertion Operations (`opCode`) -/

/-- Probe inspection snippet `probeCheckCode` (`≤ 9` instructions): checks whether the slot in
`regSlot` belongs to `otherOccupiedSlots (extractSlots base U n_max d.mem) u` (i.e.,
`used[slot] = 1` and `key[slot] ≠ u.val`), storing `1` in `regCond` if so and `0` otherwise. -/
def probeCheckCode : Code .exact 12 :=
  .seq (.op (.exactBin .add regAddr regSlotBase regSlot))
  (.seq (.op (.load regCond regAddr))
        (.branch (.eq regCond regZero)
          (.op (.const regCond 0))
          (.seq (.op (.exactBin .add regAddr regAddr regM))
          (.seq (.op (.load regCond regAddr))
                (.branch (.eq regCond regU)
                  (.op (.const regCond 0))
                  (.op (.const regCond 1)))))))

theorem probeCheckCode_execWithin {w base U n_max : ℕ} {d : Data 12}
    (hS : Fits w (base + space U n_max))
    (hwf : SlotArrayWF base U n_max d.mem)
    (u : Fin U) (slot : Fin (numBuckets n_max))
    (hsbase : d.regs regSlotBase = base + slotOffset U n_max)
    (hslot : d.regs regSlot = slot.val)
    (hm : d.regs regM = numBuckets n_max)
    (hzero : d.regs regZero = 0)
    (hu : d.regs regU = u.val) :
    ∃ d' : Data 12,
      ExecWithin w probeCheckCode d d' 9 ∧
      d'.mem = d.mem ∧
      d'.regs regCond =
        (if slot ∈ otherOccupiedSlots (extractSlots base U n_max d.mem) u then 1 else 0) ∧
      ∀ r : Fin 12, r ≠ regAddr → r ≠ regCond → d'.regs r = d.regs r := by
  have hslot_lt := slot.isLt
  have hsp : space U n_max = slotOffset U n_max + 3 * numBuckets n_max := rfl
  have hfit_0 : Fits w 0 := hS.of_le (by omega)
  have hfit_1 : Fits w 1 := hS.of_le (by omega)
  let sBase := base + slotOffset U n_max
  let m := numBuckets n_max
  have hfit_a0 : Fits w (sBase + slot.val) := hS.of_le (by omega)
  have hfit_a1 : Fits w (sBase + slot.val + m) := hS.of_le (by omega)
  set s1 := d.set regAddr (sBase + slot.val)
  have e1 : Exec w (.op (.exactBin .add regAddr regSlotBase regSlot) : Code .exact 12) d s1 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, hsbase, hslot, sBase]) hfit_a0
  let usedVal := d.mem (sBase + slot.val)
  set s2 := s1.set regCond usedVal
  have e2 : Exec w (.op (.load regCond regAddr) : Code .exact 12) s1 s2 1 := by
    simpa +decide [s2, s1, usedVal] using
      (Exec.load (B := .exact) (w := w) (d := regCond) (a := regAddr) (x := s1))
  rcases (hwf slot).1 with hused0 | hused1
  · have hc : (Cond.eq regCond regZero).Holds s2 := by
      simp +decide [Cond.Holds, s2, s1, usedVal, sBase, hused0, hzero]
    set s3 := s2.set regCond 0
    have e3 : Exec w (.op (.const regCond 0) : Code .exact 12) s2 s3 1 := Exec.const hfit_0
    have hnot_mem : slot ∉ otherOccupiedSlots (extractSlots base U n_max d.mem) u := by
      rw [mem_otherOccupiedSlots_extractSlots_iff hwf]
      omega
    refine ⟨s3,
      (e1.within.seq (e2.within.seq (ExecWithin.branch_pos hc e3.within))).mono (by omega),
      rfl, ?_, ?_⟩
    · simp +decide [s3, hnot_mem]
    · intro r hr1 hr2
      simp [s3, s2, s1, Data.set, Function.update_of_ne hr2, Function.update_of_ne hr1]
  · have hc : ¬(Cond.eq regCond regZero).Holds s2 := by
      simp +decide [Cond.Holds, s2, s1, usedVal, sBase, hused1, hzero]
    set s3 := s2.set regAddr (sBase + slot.val + m)
    have e3 : Exec w (.op (.exactBin .add regAddr regAddr regM) : Code .exact 12) s2 s3 1 :=
      Exec.alu (by simp +decide [StandardOp.evalExact, s2, s1, hm, m]) hfit_a1
    have haddr_eq : sBase + slot.val + m = sBase + m + slot.val := by omega
    let keyVal := d.mem (sBase + m + slot.val)
    set s4 := s3.set regCond keyVal
    have e4 : Exec w (.op (.load regCond regAddr) : Code .exact 12) s3 s4 1 := by
      simpa +decide [s4, s3, s2, s1, haddr_eq, keyVal] using
        (Exec.load (B := .exact) (w := w) (d := regCond) (a := regAddr) (x := s3))
    by_cases hkey : keyVal = u.val
    · have hc2 : (Cond.eq regCond regU).Holds s4 := by
        simp +decide [Cond.Holds, s4, s3, s2, s1, hkey, hu]
      set s5 := s4.set regCond 0
      have e5 : Exec w (.op (.const regCond 0) : Code .exact 12) s4 s5 1 := Exec.const hfit_0
      have hnot_mem : slot ∉ otherOccupiedSlots (extractSlots base U n_max d.mem) u := by
        rw [mem_otherOccupiedSlots_extractSlots_iff hwf]
        exact fun h => h.2 hkey
      refine ⟨s5,
        (e1.within.seq (e2.within.seq
          (ExecWithin.branch_neg hc
            (e3.within.seq (e4.within.seq (ExecWithin.branch_pos hc2 e5.within)))))).mono
          (by omega),
        rfl, ?_, ?_⟩
      · simp +decide [s5, hnot_mem]
      · intro r hr1 hr2
        simp [s5, s4, s3, s2, s1, Data.set, Function.update_of_ne hr2, Function.update_of_ne hr1]
    · have hc2 : ¬(Cond.eq regCond regU).Holds s4 := by
        simp +decide [Cond.Holds, s4, s3, s2, s1, hkey, hu]
      set s5 := s4.set regCond 1
      have e5 : Exec w (.op (.const regCond 1) : Code .exact 12) s4 s5 1 := Exec.const hfit_1
      have hmem : slot ∈ otherOccupiedSlots (extractSlots base U n_max d.mem) u := by
        rw [mem_otherOccupiedSlots_extractSlots_iff hwf]
        exact ⟨hused1, hkey⟩
      refine ⟨s5,
        (e1.within.seq (e2.within.seq
          (ExecWithin.branch_neg hc
            (e3.within.seq (e4.within.seq (ExecWithin.branch_neg hc2 e5.within)))))).mono
          (by omega),
        rfl, ?_, ?_⟩
      · simp +decide [s5, hmem]
      · intro r hr1 hr2
        simp [s5, s4, s3, s2, s1, Data.set, Function.update_of_ne hr2, Function.update_of_ne hr1]

/-- One iteration of the probe loop (`≤ 11` instructions): advances `regSlot` by `regStride` modulo
`numBuckets n_max` (`regMaskM`) and runs `probeCheckCode`. -/
def probeStepCode : Code .exact 12 :=
  .seq (.op (.exactBin .add regSlot regSlot regStride))
  (.seq (.op (.exactBin .and regSlot regSlot regMaskM))
        probeCheckCode)

/-- Probe loop: continues advancing `regSlot` while `0 < regCond` (i.e., while `regSlot` is occupied
by a key other than `u`). -/
def probeLoop : Code .exact 12 :=
  .loop (.lt regZero regCond) probeStepCode

theorem probeLoop_execWithin_aux {w base U n_max : ℕ} (θ : Seed U n_max)
    (hS : Fits w (base + space U n_max))
    {mem : ℕ → ℕ} (hwf : SlotArrayWF base U n_max mem)
    (u : Fin U)
    (hO : (otherOccupiedSlots (extractSlots base U n_max mem) u).card < numBuckets n_max) :
    let T := extractSlots base U n_max mem
    let O := otherOccupiedSlots T u
    let k := missedProbes O (probePerm θ u)
    ∀ (rem i : ℕ) (hi_lt : i < numBuckets n_max) (d : Data 12),
      i + rem = k →
      d.mem = mem →
      d.regs regSlotBase = base + slotOffset U n_max →
      d.regs regMaskM = numBuckets n_max - 1 →
      d.regs regStride = (strideHash θ u).val →
      d.regs regM = numBuckets n_max →
      d.regs regZero = 0 →
      d.regs regU = u.val →
      d.regs regSlot = (probePerm θ u ⟨i, hi_lt⟩).val →
      d.regs regCond = (if probePerm θ u ⟨i, hi_lt⟩ ∈ O then 1 else 0) →
      ∃ d' : Data 12,
        ExecWithin w probeLoop d d' (13 * rem + 2) ∧
        d'.mem = mem ∧
        d'.regs regSlot = (targetSlot (probePerm θ) T u hO).val ∧
        ∀ r : Fin 12, r ≠ regSlot → r ≠ regAddr → r ≠ regCond → d'.regs r = d.regs r := by
  intro T O k rem
  have hk_lt : k < numBuckets n_max := missedProbes_lt_of_card_lt hO (probePerm θ u)
  induction rem with
  | zero =>
    intro i hi_lt d hik hmem hsbase hmask hstride hm hzero hu hslot hcond
    have hi_eq : i = k := by omega
    have hnot_mem : probePerm θ u ⟨i, hi_lt⟩ ∉ O := by
      have heq_idx : (⟨i, hi_lt⟩ : Fin (numBuckets n_max)) =
          probeSlotIndex O (probePerm θ u) hO := Fin.ext hi_eq
      rw [heq_idx]
      exact notMem_apply_probeSlotIndex hO
    have hcond0 : d.regs regCond = 0 := by
      rw [hcond]
      exact ite_eq_right_iff.mpr (fun h => False.elim (hnot_mem h))
    have hc : ¬(Cond.lt regZero regCond).Holds d := by
      simp [Cond.Holds, hzero, hcond0]
    refine ⟨d, (Exec.loop_exit hc).within, hmem, ?_, fun _ _ _ _ => rfl⟩
    rw [hslot]
    dsimp only [targetSlot, probeSlotIndex]
    congr 2
    ext
    exact hi_eq
  | succ rem ih =>
    intro i hi_lt d hik hmem hsbase hmask hstride hm hzero hu hslot hcond
    have hi_lt_k : i < k := by omega
    have hi1_lt : i + 1 < numBuckets n_max := by omega
    have hmem_i : probePerm θ u ⟨i, hi_lt⟩ ∈ O :=
      mem_of_lt_probeSlotIndex hO (i := ⟨i, hi_lt⟩) hi_lt_k
    have hcond1 : d.regs regCond = 1 := by
      rw [hcond]
      exact ite_eq_left_iff.mpr (fun h => False.elim (h hmem_i))
    have hc : (Cond.lt regZero regCond).Holds d := by
      simp [Cond.Holds, hzero, hcond1]
    let slot_i := probePerm θ u ⟨i, hi_lt⟩
    let slot_next := probePerm θ u ⟨i + 1, hi1_lt⟩
    have hsp : space U n_max = slotOffset U n_max + 3 * numBuckets n_max := rfl
    have hfit_add : Fits w (slot_i.val + (strideHash θ u).val) := by
      have := slot_i.isLt
      have := (strideHash θ u).isLt
      exact hS.of_le (by omega)
    have hfit_next : Fits w slot_next.val := by
      have := slot_next.isLt
      exact hS.of_le (by omega)
    set s1 := d.set regSlot (slot_i.val + (strideHash θ u).val)
    have e1 : Exec w (.op (.exactBin .add regSlot regSlot regStride) : Code .exact 12) d s1 1 :=
      Exec.alu (by simp +decide [StandardOp.evalExact, hslot, hstride, slot_i]) hfit_add
    set s2 := s1.set regSlot slot_next.val
    have e2 : Exec w (.op (.exactBin .and regSlot regSlot regMaskM) : Code .exact 12) s1 s2 1 := by
      refine Exec.alu ?_ hfit_next
      have hs1_slot : s1.regs regSlot = slot_i.val + (strideHash θ u).val := by
        simp +decide [s1]
      have hs1_mask : s1.regs regMaskM = numBuckets n_max - 1 := by
        simp +decide [s1, hmask]
      change some (s1.regs regSlot &&& s1.regs regMaskM) = some slot_next.val
      rw [hs1_slot, hs1_mask]
      exact congrArg some (val_probePerm_succ θ u hi1_lt).symm
    have hwf_s2 : SlotArrayWF base U n_max s2.mem := by simpa [s2, s1, hmem] using hwf
    obtain ⟨s3, e3, hs3_mem, hs3_cond, hs3_regs⟩ :=
      probeCheckCode_execWithin hS hwf_s2 u slot_next
        (by simp +decide [s2, s1, hsbase])
        (by simp +decide [s2])
        (by simp +decide [s2, s1, hm])
        (by simp +decide [s2, s1, hzero])
        (by simp +decide [s2, s1, hu])
    have eStep : ExecWithin w probeStepCode d s3 11 :=
      (e1.within.seq (e2.within.seq e3)).mono (by omega)
    have hs2_mem_eq : s2.mem = mem := hmem
    have hs3_mem_eq : s3.mem = mem := hs3_mem.trans hs2_mem_eq
    have hs3_slot : s3.regs regSlot = slot_next.val := by
      rw [hs3_regs regSlot (by decide) (by decide)]
      simp +decide [s2]
    have hs3_cond' : s3.regs regCond = (if slot_next ∈ O then 1 else 0) := by
      rw [hs2_mem_eq] at hs3_cond
      exact hs3_cond
    obtain ⟨d', eRec, hd'_mem, hd'_slot, hd'_regs⟩ :=
      ih (i + 1) hi1_lt s3 (by omega) hs3_mem_eq
        (by rw [hs3_regs regSlotBase (by decide) (by decide)]; simp +decide [s2, s1, hsbase])
        (by rw [hs3_regs regMaskM (by decide) (by decide)]; simp +decide [s2, s1, hmask])
        (by rw [hs3_regs regStride (by decide) (by decide)]; simp +decide [s2, s1, hstride])
        (by rw [hs3_regs regM (by decide) (by decide)]; simp +decide [s2, s1, hm])
        (by rw [hs3_regs regZero (by decide) (by decide)]; simp +decide [s2, s1, hzero])
        (by rw [hs3_regs regU (by decide) (by decide)]; simp +decide [s2, s1, hu])
        hs3_slot
        hs3_cond'
    refine ⟨d', (ExecWithin.loop_iter hc eStep eRec).mono (by omega), hd'_mem, hd'_slot, ?_⟩
    intro r hr_slot hr_addr hr_cond
    rw [hd'_regs r hr_slot hr_addr hr_cond, hs3_regs r hr_addr hr_cond]
    simp [s2, s1, Data.set, Function.update_of_ne hr_slot]

/-- Deterministic 5-instruction glue before `MultiplyShift.evalCode`: saves the stride from
`regAddr` into `regStride`, loads the multiply-shift seed from `base + tabSpace U n_max` into
`regCond` (`msMap regB`), and copies `regU` into `regAddr` (`msMap regX`). -/
def opPreMSCode (U n_max : ℕ) : Code .exact 12 :=
  .seq (.op (.copy regStride regAddr))
  (.seq (.op (.const regAddr (tabSpace U n_max)))
  (.seq (.op (.exactBin .add regAddr regBase regAddr))
  (.seq (.op (.load regCond regAddr))
        (.op (.copy regAddr regU)))))

/-- Deterministic 5-instruction glue after `MultiplyShift.evalCode`: initializes `regSlotBase`,
`regMaskM`, `regM`, and `regZero`. -/
def opPostMSCode (U n_max : ℕ) : Code .exact 12 :=
  .seq (.op (.const regSlotBase (slotOffset U n_max)))
  (.seq (.op (.exactBin .add regSlotBase regBase regSlotBase))
  (.seq (.op (.const regMaskM (numBuckets n_max - 1)))
  (.seq (.op (.const regM (numBuckets n_max)))
        (.op (.const regZero 0)))))

/-- Hash evaluation and probe-register setup `opEvalHashesCode U n_max`
(`8 * numChars U n_max + 41` instructions): evaluates `strideHash θ u` into `regStride`,
`primaryHash θ u` into `regSlot`, and initializes `regSlotBase`, `regMaskM`, `regM`,
and `regZero`. -/
def opEvalHashesCode (U n_max : ℕ) : Code .exact 12 :=
  .seq (.op (.copy regCond regU))
  (.seq ((TabulatedOddStride.evalCode (numChars U n_max)).rename tabMap)
  (.seq (opPreMSCode U n_max)
  (.seq ((MultiplyShift.evalCode (hashBits U n_max) (bucketBits n_max)).rename msMap)
        (opPostMSCode U n_max))))

theorem opEvalHashesCode_execWithin {w base U V n_max : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {x : Data 12}
    (hS : Fits w (base + space U n_max)) (hw : 2 * hashBits U n_max ≤ w)
    (hrep : Rep w base U V n_max θ s x) (u : Fin U) (hu : x.regs regU = u.val) :
    ∃ d : Data 12,
      ExecWithin w (opEvalHashesCode U n_max) x d (8 * numChars U n_max + 41) ∧
      d.mem = x.mem ∧
      d.regs regBase = base ∧
      d.regs regSlot = (probePerm θ u ⟨0, numBuckets_pos n_max⟩).val ∧
      d.regs regSlotBase = base + slotOffset U n_max ∧
      d.regs regMaskM = numBuckets n_max - 1 ∧
      d.regs regStride = (strideHash θ u).val ∧
      d.regs regM = numBuckets n_max ∧
      d.regs regZero = 0 ∧
      d.regs regOp = x.regs regOp ∧
      d.regs regU = u.val ∧
      d.regs regV = x.regs regV := by
  obtain ⟨hfit_btab, _, hfit_powM, hfit_d, _, _⟩ := fits_of_space hS
  have hsp : space U n_max = tabSpace U n_max + 1 + 3 * numBuckets n_max := rfl
  have hso : slotOffset U n_max = tabSpace U n_max + 1 := rfl
  have hM : 2 ^ bucketBits n_max = numBuckets n_max := rfl
  have hfit_2powM : Fits w (2 * 2 ^ bucketBits n_max) := hS.of_le (by omega)
  have hfit_u : Fits w u.val := by
    rw [fits_iff]
    have hu_lt : u.val < 2 ^ hashBits U n_max := (encodeKey n_max u).isLt
    have hpow : 2 ^ hashBits U n_max ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
    exact hu_lt.trans_le hpow
  set s1 := x.set regCond u.val
  have e1 : Exec w (.op (.copy regCond regU) : Code .exact 12) x s1 1 := by
    simpa [s1, hu] using (Exec.copy (B := .exact) (w := w) (d := regCond) (s := regU) (x := x))
  have hs1_base : (s1.comap tabMap).regs TabulatedOddStride.regBase = base := by
    simpa +decide [s1, tabMap, Data.comap] using hrep.regs_base
  have hs1_key : (s1.comap tabMap).regs TabulatedOddStride.regKey = u.val := by
    simp +decide [s1, tabMap, Data.comap]
  obtain ⟨yTab, htab_exec, hyTab_out, hyTab_base, hyTab_mem⟩ :=
    TabulatedOddStride.evalCode_execWithin hrep.tab_rep hs1_base hs1_key
      hfit_btab hfit_2powM hfit_d hfit_u
  set s2 := yTab.extend tabMap s1
  have e2 : ExecWithin w ((TabulatedOddStride.evalCode (numChars U n_max)).rename tabMap)
      s1 s2 (8 * numChars U n_max + 21) :=
    htab_exec.rename injective_tabMap
  have hs2_mem : s2.mem = x.mem := by
    change yTab.mem = x.mem
    exact hyTab_mem
  have hs2_base : s2.regs regBase = base := by
    change (s2.comap tabMap).regs TabulatedOddStride.regBase = base
    rw [Data.comap_extend injective_tabMap]
    exact hyTab_base
  have hs2_addr : s2.regs regAddr = (strideHash θ u).val := by
    change (s2.comap tabMap).regs TabulatedOddStride.regOut = (strideHash θ u).val
    rw [Data.comap_extend injective_tabMap]
    exact hyTab_out
  have hs2_op : s2.regs regOp = x.regs regOp := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_tabMap (by decide))]
    simp +decide [s1]
  have hs2_u : s2.regs regU = u.val := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_tabMap (by decide))]
    simp +decide [s1, hu]
  have hs2_v : s2.regs regV = x.regs regV := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_tabMap (by decide))]
    simp +decide [s1]
  -- Execute opPreMSCode
  have hfit_tab : Fits w (tabSpace U n_max) := hfit_btab.of_le (by omega)
  set s3 := s2.set regStride (strideHash θ u).val
  have e3 : Exec w (.op (.copy regStride regAddr) : Code .exact 12) s2 s3 1 := by
    simpa [s3, hs2_addr] using
      (Exec.copy (B := .exact) (w := w) (d := regStride) (s := regAddr) (x := s2))
  set s4 := s3.set regAddr (tabSpace U n_max)
  have e4 : Exec w (.op (.const regAddr (tabSpace U n_max)) : Code .exact 12) s3 s4 1 :=
    Exec.const hfit_tab
  set s5 := s4.set regAddr (base + tabSpace U n_max)
  have e5 : Exec w (.op (.exactBin .add regAddr regBase regAddr) : Code .exact 12) s4 s5 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s4, s3, hs2_base]) hfit_btab
  set s6 := s5.set regCond θ.1.val
  have e6 : Exec w (.op (.load regCond regAddr) : Code .exact 12) s5 s6 1 := by
    simpa +decide [s6, s5, s4, s3, hs2_mem, hrep.ms_seed] using
      (Exec.load (B := .exact) (w := w) (d := regCond) (a := regAddr) (x := s5))
  set s7 := s6.set regAddr u.val
  have e7 : Exec w (.op (.copy regAddr regU) : Code .exact 12) s6 s7 1 := by
    simpa +decide [s7, s6, s5, s4, s3, hs2_u] using
      (Exec.copy (B := .exact) (w := w) (d := regAddr) (s := regU) (x := s6))
  have ePre : Exec w (opPreMSCode U n_max) s2 s7 5 :=
    e3.seq (e4.seq (e5.seq (e6.seq e7)))
  -- Execute MultiplyShift.evalCode
  have hs7_b : (s7.comap msMap).regs MultiplyShift.regB = θ.1.val := by
    simp +decide [s7, s6, msMap, Data.comap]
  have hs7_x : (s7.comap msMap).regs MultiplyShift.regX = (encodeKey n_max u).val := by
    simp +decide [s7, msMap, Data.comap, encodeKey]
  have hms_eval :=
    MultiplyShift.evalCode_exec (w₀ := hashBits U n_max) (M := bucketBits n_max) (w := w)
      (hashBits_pos U n_max) hw
      (by rw [hs7_b]; exact θ.1.isLt)
      (by rw [hs7_x]; exact (encodeKey n_max u).isLt)
  set yMS := MultiplyShift.evalData (hashBits U n_max) (bucketBits n_max) (s7.comap msMap)
  set s8 := yMS.extend msMap s7
  have e8 : Exec w ((MultiplyShift.evalCode (hashBits U n_max) (bucketBits n_max)).rename msMap)
      s7 s8 9 :=
    hms_eval.rename injective_msMap
  have hs8_mem : s8.mem = x.mem := by
    change (s7.comap msMap).mem = x.mem
    exact hs2_mem
  have hs8_slot : s8.regs regSlot = (primaryHash θ u).val := by
    change (s8.comap msMap).regs MultiplyShift.regOut = (primaryHash θ u).val
    rw [Data.comap_extend injective_msMap]
    exact MultiplyShift.evalData_regs_out_eq_multiplyShift
      (hashBits U n_max) (bucketBits n_max) (s7.comap msMap) θ.1 (encodeKey n_max u) hs7_b hs7_x
  have hs8_base : s8.regs regBase = base := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_msMap (by decide))]
    simp +decide [s7, s6, s5, s4, s3, hs2_base]
  have hs8_stride : s8.regs regStride = (strideHash θ u).val := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_msMap (by decide))]
    simp +decide [s7, s6, s5, s4, s3]
  have hs8_op : s8.regs regOp = x.regs regOp := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_msMap (by decide))]
    simp +decide [s7, s6, s5, s4, s3, hs2_op]
  have hs8_u : s8.regs regU = u.val := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_msMap (by decide))]
    simp +decide [s7, s6, s5, s4, s3, hs2_u]
  have hs8_v : s8.regs regV = x.regs regV := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_msMap (by decide))]
    simp +decide [s7, s6, s5, s4, s3, hs2_v]
  -- Execute opPostMSCode
  have hfit_so : Fits w (slotOffset U n_max) := hS.of_le (by omega)
  have hfit_bso : Fits w (base + slotOffset U n_max) := hS.of_le (by omega)
  have hfit_mask : Fits w (numBuckets n_max - 1) := hS.of_le (by omega)
  have hfit_m : Fits w (numBuckets n_max) := hS.of_le (by omega)
  have hfit_0 : Fits w 0 := hS.of_le (by omega)
  set s9 := s8.set regSlotBase (slotOffset U n_max)
  have e9 : Exec w (.op (.const regSlotBase (slotOffset U n_max)) : Code .exact 12) s8 s9 1 :=
    Exec.const hfit_so
  set s10 := s9.set regSlotBase (base + slotOffset U n_max)
  have e10 : Exec w (.op (.exactBin .add regSlotBase regBase regSlotBase) : Code .exact 12)
      s9 s10 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s9, hs8_base]) hfit_bso
  set s11 := s10.set regMaskM (numBuckets n_max - 1)
  have e11 : Exec w (.op (.const regMaskM (numBuckets n_max - 1)) : Code .exact 12) s10 s11 1 :=
    Exec.const hfit_mask
  set s12 := s11.set regM (numBuckets n_max)
  have e12 : Exec w (.op (.const regM (numBuckets n_max)) : Code .exact 12) s11 s12 1 :=
    Exec.const hfit_m
  set s13 := s12.set regZero 0
  have e13 : Exec w (.op (.const regZero 0) : Code .exact 12) s12 s13 1 :=
    Exec.const hfit_0
  have ePost : Exec w (opPostMSCode U n_max) s8 s13 5 :=
    e9.seq (e10.seq (e11.seq (e12.seq e13)))
  have eAll : ExecWithin w (opEvalHashesCode U n_max) x s13 (8 * numChars U n_max + 41) :=
    (e1.within.seq (e2.seq (ePre.within.seq (e8.within.seq ePost.within)))).mono (by omega)
  refine ⟨s13, eAll, hs8_mem,
    by simp +decide [s13, s12, s11, s10, s9, hs8_base],
    by rw [probePerm_zero]; simp +decide [s13, s12, s11, s10, s9, hs8_slot],
    by simp +decide [s13, s12, s11, s10],
    by simp +decide [s13, s12, s11],
    by simp +decide [s13, s12, s11, s10, s9, hs8_stride],
    by simp +decide [s13, s12],
    by simp +decide [s13],
    by simp +decide [s13, s12, s11, s10, s9, hs8_op],
    by simp +decide [s13, s12, s11, s10, s9, hs8_u],
    by simp +decide [s13, s12, s11, s10, s9, hs8_v]⟩

/-- Lookup completion program `finishGetCode` (`≤ 9` instructions): inspects `used[regSlot]`;
if `0`, writes `0` (`none`) into `regOp`, and if `1`, loads `val[regSlot]` and writes
`val[regSlot] + 1` (`some v`) into `regOp`. -/
def finishGetCode : Code .exact 12 :=
  .seq (.op (.exactBin .add regAddr regSlotBase regSlot))
  (.seq (.op (.load regCond regAddr))
        (.branch (.eq regCond regZero)
          (.op (.const regOp 0))
          (.seq (.op (.exactBin .add regAddr regAddr regM))
          (.seq (.op (.exactBin .add regAddr regAddr regM))
          (.seq (.op (.load regOp regAddr))
          (.seq (.op (.const regCond 1))
                (.op (.exactBin .add regOp regOp regCond))))))))

theorem finishGetCode_execWithin {w base U V n_max : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {x d : Data 12}
    (hS : Fits w (base + space U n_max)) (hV : Fits w V)
    (hrep : Rep w base U V n_max θ s x)
    (u : Fin U)
    (hO : (otherOccupiedSlots (extractSlots base U n_max x.mem) u).card < numBuckets n_max)
    (hmem : d.mem = x.mem)
    (hbase : d.regs regBase = base)
    (hsbase : d.regs regSlotBase = base + slotOffset U n_max)
    (hslot : d.regs regSlot = (targetSlot (probePerm θ) (extractSlots base U n_max x.mem) u hO).val)
    (hm : d.regs regM = numBuckets n_max)
    (hzero : d.regs regZero = 0) :
    ∃ y : Data 12,
      ExecWithin w finishGetCode d y 9 ∧
      y.mem = x.mem ∧
      y.regs regBase = base ∧
      y.regs regOp = (match s u with | none => 0 | some v => v + 1) := by
  let T := extractSlots base U n_max x.mem
  let slot := targetSlot (probePerm θ) T u hO
  have hslot_lt := slot.isLt
  have hsp : space U n_max = slotOffset U n_max + 3 * numBuckets n_max := rfl
  have hfit_0 : Fits w 0 := hS.of_le (by omega)
  have hfit_1 : Fits w 1 := hS.of_le (by omega)
  let sBase := base + slotOffset U n_max
  let m := numBuckets n_max
  have hfit_a0 : Fits w (sBase + slot.val) := hS.of_le (by omega)
  have hfit_a1 : Fits w (sBase + slot.val + m) := hS.of_le (by omega)
  have hfit_a2 : Fits w (sBase + slot.val + m + m) := hS.of_le (by omega)
  set s1 := d.set regAddr (sBase + slot.val)
  have e1 : Exec w (.op (.exactBin .add regAddr regSlotBase regSlot) : Code .exact 12) d s1 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, hsbase, hslot, sBase, slot, T]) hfit_a0
  let usedVal := x.mem (sBase + slot.val)
  set s2 := s1.set regCond usedVal
  have e2 : Exec w (.op (.load regCond regAddr) : Code .exact 12) s1 s2 1 := by
    simpa +decide [s2, s1, hmem, usedVal] using
      (Exec.load (B := .exact) (w := w) (d := regCond) (a := regAddr) (x := s1))
  have htarget := hrep.table_rep.apply_targetSlot u hO
  cases hsu : s u with
  | none =>
    have hT_none : extractSlots base U n_max x.mem slot = none := by
      simpa [slot, T, hsu] using htarget
    have hused0 : usedVal = 0 := (extractSlots_eq_none_iff hrep.slot_wf slot).mp hT_none
    have hc : (Cond.eq regCond regZero).Holds s2 := by
      simp +decide [Cond.Holds, s2, s1, hused0, hzero]
    set s3 := s2.set regOp 0
    have e3 : Exec w (.op (.const regOp 0) : Code .exact 12) s2 s3 1 := Exec.const hfit_0
    refine ⟨s3,
      (e1.within.seq (e2.within.seq (ExecWithin.branch_pos hc e3.within))).mono (by omega),
      hmem, by simp +decide [s3, s2, s1, hbase], by simp +decide [s3]⟩
  | some v =>
    have hT_some : extractSlots base U n_max x.mem slot = some (u, v) := by
      simpa [slot, T, hsu] using htarget
    obtain ⟨hused1, _, hval_eq⟩ := (extractSlots_eq_some_iff hrep.slot_wf slot u v).mp hT_some
    have hv_lt : v < V := hrep.vals_bounded u v hsu
    have hfit_v1 : Fits w (v + 1) := hV.of_le (by omega)
    have hc : ¬(Cond.eq regCond regZero).Holds s2 := by
      simp +decide [Cond.Holds, s2, s1, usedVal, sBase, hused1, hzero]
    set s3 := s2.set regAddr (sBase + slot.val + m)
    have e3 : Exec w (.op (.exactBin .add regAddr regAddr regM) : Code .exact 12) s2 s3 1 :=
      Exec.alu (by simp +decide [StandardOp.evalExact, s2, s1, hm, m]) hfit_a1
    set s4 := s3.set regAddr (sBase + slot.val + m + m)
    have e4 : Exec w (.op (.exactBin .add regAddr regAddr regM) : Code .exact 12) s3 s4 1 :=
      Exec.alu (by simp +decide [StandardOp.evalExact, s3, s2, s1, hm, m]) hfit_a2
    have haddr2_eq :
        sBase + slot.val + m + m = base + slotOffset U n_max + 2 * numBuckets n_max + slot.val := by
      dsimp only [sBase, m]
      omega
    set s5 := s4.set regOp v
    have e5 : Exec w (.op (.load regOp regAddr) : Code .exact 12) s4 s5 1 := by
      simpa +decide [s5, s4, s3, s2, s1, hmem, haddr2_eq, hval_eq] using
        (Exec.load (B := .exact) (w := w) (d := regOp) (a := regAddr) (x := s4))
    set s6 := s5.set regCond 1
    have e6 : Exec w (.op (.const regCond 1) : Code .exact 12) s5 s6 1 := Exec.const hfit_1
    set s7 := s6.set regOp (v + 1)
    have e7 : Exec w (.op (.exactBin .add regOp regOp regCond) : Code .exact 12) s6 s7 1 :=
      Exec.alu (by simp +decide [StandardOp.evalExact, s6, s5]) hfit_v1
    refine ⟨s7,
      (e1.within.seq (e2.within.seq
        (ExecWithin.branch_neg hc
          (e3.within.seq (e4.within.seq (e5.within.seq (e6.within.seq e7.within))))))).mono
        (by omega),
      hmem, by simp +decide [s7, s6, s5, s4, s3, s2, s1, hbase], by simp +decide [s7]⟩

/-- Insertion completion program `finishInsertCode` (`8` instructions): writes `used[regSlot] := 1`,
`key[regSlot] := regU`, `val[regSlot] := regV`, and sets `regOp := 0`. -/
def finishInsertCode : Code .exact 12 :=
  .seq (.op (.exactBin .add regAddr regSlotBase regSlot))
  (.seq (.op (.const regCond 1))
  (.seq (.op (.store regAddr regCond))
  (.seq (.op (.exactBin .add regAddr regAddr regM))
  (.seq (.op (.store regAddr regU))
  (.seq (.op (.exactBin .add regAddr regAddr regM))
  (.seq (.op (.store regAddr regV))
        (.op (.const regOp 0))))))))

theorem finishInsertCode_execWithin {w base U V n_max : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {x d : Data 12}
    (hS : Fits w (base + space U n_max))
    (hrep : Rep w base U V n_max θ s x)
    (u : Fin U) (v : ℕ)
    (hvalid : ((Dictionary.spec U V n_max).valid s (.insert u v)))
    (hO : (otherOccupiedSlots (extractSlots base U n_max x.mem) u).card < numBuckets n_max)
    (hmem : d.mem = x.mem)
    (hbase : d.regs regBase = base)
    (hsbase : d.regs regSlotBase = base + slotOffset U n_max)
    (hslot : d.regs regSlot = (targetSlot (probePerm θ) (extractSlots base U n_max x.mem) u hO).val)
    (hm : d.regs regM = numBuckets n_max)
    (hu : d.regs regU = u.val)
    (hv : d.regs regV = v) :
    ∃ y : Data 12,
      ExecWithin w finishInsertCode d y 8 ∧
      y.regs regBase = base ∧
      y.regs regOp = 0 ∧
      TabulatedOddStride.Rep base (charBits n_max) (numChars U n_max)
        (bucketBits n_max) θ.2 y.mem ∧
      y.mem (base + tabSpace U n_max) = θ.1.val ∧
      SlotArrayWF base U n_max y.mem ∧
      TableRep (probePerm θ) (Function.update s u (some v)) (extractSlots base U n_max y.mem) ∧
      (Dictionary.dom (Function.update s u (some v))).card ≤ n_max ∧
      Dictionary.ValuesBounded V (Function.update s u (some v)) ∧
      Modifies (Block.mk base (space U n_max)).footprint x.mem y.mem := by
  let T := extractSlots base U n_max x.mem
  let slot := targetSlot (probePerm θ) T u hO
  have hslot_lt := slot.isLt
  have hsp : space U n_max = slotOffset U n_max + 3 * numBuckets n_max := rfl
  have hso : slotOffset U n_max = tabSpace U n_max + 1 := rfl
  have htab_eq : tabSpace U n_max = 4 + numChars U n_max * 2 ^ charBits n_max := rfl
  have hfit_0 : Fits w 0 := hS.of_le (by omega)
  have hfit_1 : Fits w 1 := hS.of_le (by omega)
  let sBase := base + slotOffset U n_max
  let m := numBuckets n_max
  have hfit_a0 : Fits w (sBase + slot.val) := hS.of_le (by omega)
  have hfit_a1 : Fits w (sBase + slot.val + m) := hS.of_le (by omega)
  have hfit_a2 : Fits w (sBase + slot.val + m + m) := hS.of_le (by omega)
  have ha1_eq : sBase + slot.val + m = sBase + m + slot.val := by omega
  have ha2_eq : sBase + slot.val + m + m = sBase + 2 * m + slot.val := by omega
  set s1 := d.set regAddr (sBase + slot.val)
  have e1 : Exec w (.op (.exactBin .add regAddr regSlotBase regSlot) : Code .exact 12) d s1 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, hsbase, hslot, sBase, slot, T]) hfit_a0
  set s2 := s1.set regCond 1
  have e2 : Exec w (.op (.const regCond 1) : Code .exact 12) s1 s2 1 := Exec.const hfit_1
  set s3 := s2.write (sBase + slot.val) 1
  have e3 : Exec w (.op (.store regAddr regCond) : Code .exact 12) s2 s3 1 := by
    simpa +decide [s3, s2, s1] using
      (Exec.store (B := .exact) (w := w) (a := regAddr) (s := regCond) (x := s2))
  set s4 := s3.set regAddr (sBase + slot.val + m)
  have e4 : Exec w (.op (.exactBin .add regAddr regAddr regM) : Code .exact 12) s3 s4 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s3, s2, s1, hm, m]) hfit_a1
  set s5 := s4.write (sBase + m + slot.val) u.val
  have e5 : Exec w (.op (.store regAddr regU) : Code .exact 12) s4 s5 1 := by
    simpa +decide [s5, s4, s3, s2, s1, ha1_eq, hu] using
      (Exec.store (B := .exact) (w := w) (a := regAddr) (s := regU) (x := s4))
  set s6 := s5.set regAddr (sBase + slot.val + m + m)
  have e6 : Exec w (.op (.exactBin .add regAddr regAddr regM) : Code .exact 12) s5 s6 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s5, s4, s3, s2, s1, hm, m]) hfit_a2
  set s7 := s6.write (sBase + 2 * m + slot.val) v
  have e7 : Exec w (.op (.store regAddr regV) : Code .exact 12) s6 s7 1 := by
    simpa +decide [s7, s6, s5, s4, s3, s2, s1, ha2_eq, hv] using
      (Exec.store (B := .exact) (w := w) (a := regAddr) (s := regV) (x := s6))
  set s8 := s7.set regOp 0
  have e8 : Exec w (.op (.const regOp 0) : Code .exact 12) s7 s8 1 := Exec.const hfit_0
  have eAll := (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))).within
  have hs8_mem_below : ∀ a < sBase, s8.mem a = x.mem a := by
    intro a ha
    have hne0 : a ≠ sBase + slot.val := by omega
    have hne1 : a ≠ sBase + m + slot.val := by omega
    have hne2 : a ≠ sBase + 2 * m + slot.val := by omega
    simp [s8, s7, s6, s5, s4, s3, s2, s1, Data.write,
      Function.update_of_ne hne0, Function.update_of_ne hne1, Function.update_of_ne hne2, hmem]
  have htab : TabulatedOddStride.Rep base (charBits n_max) (numChars U n_max)
      (bucketBits n_max) θ.2 s8.mem := by
    rcases hrep.tab_rep with ⟨hm0, hm1, hm2, hm3, hmt⟩
    refine ⟨?_, ?_, ?_, ?_, fun i => ?_⟩
    · rw [hs8_mem_below base (by omega), hm0]
    · rw [hs8_mem_below (base + 1) (by omega), hm1]
    · rw [hs8_mem_below (base + 2) (by omega), hm2]
    · rw [hs8_mem_below (base + 3) (by omega), hm3]
    · have hi := i.isLt
      rw [hs8_mem_below (base + 4 + i.val) (by omega), hmt i]
  have hms : s8.mem (base + tabSpace U n_max) = θ.1.val := by
    rw [hs8_mem_below (base + tabSpace U n_max) (by omega), hrep.ms_seed]
  have hs8_slot0 : s8.mem (sBase + slot.val) = 1 := by
    have hne2 : sBase + slot.val ≠ sBase + 2 * m + slot.val := by omega
    have hne1 : sBase + slot.val ≠ sBase + m + slot.val := by omega
    simp [s8, s7, s6, s5, s4, s3, Data.write,
      Function.update_of_ne hne2, Function.update_of_ne hne1]
  have hs8_slot1 : s8.mem (sBase + m + slot.val) = u.val := by
    have hne2 : sBase + m + slot.val ≠ sBase + 2 * m + slot.val := by omega
    simp [s8, s7, s6, s5, Data.write, Function.update_of_ne hne2]
  have hs8_slot2 : s8.mem (sBase + 2 * m + slot.val) = v := by
    simp [s8, s7, Data.write]
  have hwf : SlotArrayWF base U n_max s8.mem := by
    intro j
    have hj := j.isLt
    by_cases hjs : j = slot
    · subst hjs
      exact ⟨Or.inr hs8_slot0, fun _ => hs8_slot1 ▸ u.isLt⟩
    · have hne_val : j.val ≠ slot.val := fun h => hjs (Fin.ext h)
      have h0 : s8.mem (sBase + j.val) = x.mem (sBase + j.val) := by
        simp [s8, s7, s6, s5, s4, s3, s2, s1, Data.write,
          Function.update_of_ne (show sBase + j.val ≠ sBase + 2 * m + slot.val by omega),
          Function.update_of_ne (show sBase + j.val ≠ sBase + m + slot.val by omega),
          Function.update_of_ne (show sBase + j.val ≠ sBase + slot.val by omega), hmem]
      have h1 : s8.mem (sBase + m + j.val) = x.mem (sBase + m + j.val) := by
        simp [s8, s7, s6, s5, s4, s3, s2, s1, Data.write,
          Function.update_of_ne (show sBase + m + j.val ≠ sBase + 2 * m + slot.val by omega),
          Function.update_of_ne (show sBase + m + j.val ≠ sBase + m + slot.val by omega),
          Function.update_of_ne (show sBase + m + j.val ≠ sBase + slot.val by omega), hmem]
      have hwf_j := hrep.slot_wf j
      change (s8.mem (sBase + j.val) = 0 ∨ s8.mem (sBase + j.val) = 1) ∧
        (s8.mem (sBase + j.val) = 1 → s8.mem (sBase + m + j.val) < U)
      rw [h0, h1]
      exact hwf_j
  have hext : extractSlots base U n_max s8.mem =
      tableInsert (numBuckets_pos n_max) (probePerm θ) T u v := by
    rw [tableInsert_eq_update_targetSlot (numBuckets_pos n_max) (probePerm θ) T u v hO]
    funext j
    have hj := j.isLt
    by_cases hjs : j = slot
    · subst hjs
      simp only [slot, Function.update_self]
      rw [extractSlots_eq_some_iff hwf]
      exact ⟨hs8_slot0, hs8_slot1, hs8_slot2⟩
    · have hne_val : j.val ≠ slot.val := fun h => hjs (Fin.ext h)
      simp only [slot, Function.update_of_ne hjs]
      have h0 : s8.mem (sBase + j.val) = x.mem (sBase + j.val) := by
        simp [s8, s7, s6, s5, s4, s3, s2, s1, Data.write,
          Function.update_of_ne (show sBase + j.val ≠ sBase + 2 * m + slot.val by omega),
          Function.update_of_ne (show sBase + j.val ≠ sBase + m + slot.val by omega),
          Function.update_of_ne (show sBase + j.val ≠ sBase + slot.val by omega), hmem]
      have h1 : s8.mem (sBase + m + j.val) = x.mem (sBase + m + j.val) := by
        simp [s8, s7, s6, s5, s4, s3, s2, s1, Data.write,
          Function.update_of_ne (show sBase + m + j.val ≠ sBase + 2 * m + slot.val by omega),
          Function.update_of_ne (show sBase + m + j.val ≠ sBase + m + slot.val by omega),
          Function.update_of_ne (show sBase + m + j.val ≠ sBase + slot.val by omega), hmem]
      have h2 : s8.mem (sBase + 2 * m + j.val) = x.mem (sBase + 2 * m + j.val) := by
        simp [s8, s7, s6, s5, s4, s3, s2, s1, Data.write,
          Function.update_of_ne (show sBase + 2 * m + j.val ≠ sBase + 2 * m + slot.val by omega),
          Function.update_of_ne (show sBase + 2 * m + j.val ≠ sBase + m + slot.val by omega),
          Function.update_of_ne (show sBase + 2 * m + j.val ≠ sBase + slot.val by omega), hmem]
      change extractSlots base U n_max s8.mem j = extractSlots base U n_max x.mem j
      dsimp only [extractSlots]
      rw [show base + slotOffset U n_max + j.val = sBase + j.val from rfl,
        show base + slotOffset U n_max + numBuckets n_max + j.val = sBase + m + j.val from rfl,
        show base + slotOffset U n_max + 2 * numBuckets n_max + j.val =
          sBase + 2 * m + j.val from rfl,
        h0, h1, h2]
  have htrep : TableRep (probePerm θ) (Function.update s u (some v))
      (extractSlots base U n_max s8.mem) := by
    rw [hext]
    exact hrep.table_rep.tableInsert (numBuckets_pos n_max) u v hO
  have hdom_le : (Dictionary.dom (Function.update s u (some v))).card ≤ n_max :=
    Dictionary.card_dom_step_le_of_valid (V := V) hrep.dom_le (o := .insert u v) hvalid
  have hvals : Dictionary.ValuesBounded V (Function.update s u (some v)) :=
    Dictionary.valuesBounded_step_of_valid (n_max := n_max) hrep.vals_bounded
      (o := .insert u v) hvalid
  have hmod : Modifies (Block.mk base (space U n_max)).footprint x.mem s8.mem := by
    intro a ha
    have ha_out : a < base ∨ base + space U n_max ≤ a := by
      by_contra h
      rw [not_or, not_lt, not_le] at h
      exact ha (mem_footprint_of_lt_space h.1 h.2)
    have hne0 : a ≠ sBase + slot.val := by omega
    have hne1 : a ≠ sBase + m + slot.val := by omega
    have hne2 : a ≠ sBase + 2 * m + slot.val := by omega
    simp [s8, s7, s6, s5, s4, s3, s2, s1, Data.write,
      Function.update_of_ne hne0, Function.update_of_ne hne1, Function.update_of_ne hne2, hmem]
  exact ⟨s8, eAll,
    by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, hbase],
    by simp +decide [s8],
    htab, hms, hwf, htrep, hdom_le, hvals, hmod⟩

/-- Complete operation body `opCode U n_max` for both `get` and `insert`. -/
def opCode (U n_max : ℕ) : Code .exact 12 :=
  .seq (opEvalHashesCode U n_max)
  (.seq probeCheckCode
  (.seq probeLoop
        (.branch (.eq regOp regZero) finishGetCode finishInsertCode)))

/-- Exact pathwise instruction budget
`13 * probeCount T u (probePerm θ u) + 8 * numChars U n_max + 49` for `opCode U n_max` on table `T`
and key `u`. -/
noncomputable def opPathSteps (U n_max : ℕ) (θ : Seed U n_max)
    (T : UniformProbing.Table U (numBuckets n_max)) (u : Fin U) : ℕ :=
  13 * probeCount T u (probePerm θ u) + 8 * numChars U n_max + 49

/-- Worst-case instruction bound `13 * numBuckets n_max + 8 * numChars U n_max + 49` for
`opCode`. -/
def opSteps (U n_max : ℕ) : ℕ :=
  13 * numBuckets n_max + 8 * numChars U n_max + 49

theorem opPathSteps_le_opSteps {U n_max : ℕ} (θ : Seed U n_max)
    (T : UniformProbing.Table U (numBuckets n_max)) (u : Fin U)
    (hO : (otherOccupiedSlots T u).card < numBuckets n_max) :
    opPathSteps U n_max θ T u ≤ opSteps U n_max := by
  dsimp only [opPathSteps, opSteps, probeCount, unsuccessfulProbes]
  have hlt := missedProbes_lt_of_card_lt hO (probePerm θ u)
  omega

/-- Key extracted from a `Dictionary.Op U`. -/
def opKey {U : ℕ} : Dictionary.Op U → Fin U
  | .get u => u
  | .insert u _ => u

/-- Operation tag (`0` for `get`, `1` for `insert`). -/
def opTag {U : ℕ} : Dictionary.Op U → ℕ
  | .get _ => 0
  | .insert _ _ => 1

/-- Encoded output word in `regOp` after executing `op` from state `s`. -/
def opOutWord {U : ℕ} (s : Dictionary.State U) : Dictionary.Op U → ℕ
  | .get u => match s u with | none => 0 | some v => v + 1
  | .insert _ _ => 0

/-- **Pathwise correctness and complexity of `opCode U n_max`**: for any seed `θ`, dictionary
state `s`, machine state `x` satisfying `Rep w base U V n_max θ s x`, and admissible operation
`op`, `opCode U n_max` halts deterministically in at most
`opPathSteps U n_max θ (extractSlots base U n_max x.mem) (opKey op) ≤ opSteps U n_max` instructions,
preserving `Rep` for `((Dictionary.spec U V n_max).step s op).1`, writing `opOutWord s op` into
`regOp`, and modifying memory only within `[base, base + space U n_max)`. -/
theorem opCode_execWithin {w base U V n_max : ℕ} {θ : Seed U n_max}
    {s : Dictionary.State U} {x : Data 12}
    (hS : Fits w (base + space U n_max)) (hw : 2 * hashBits U n_max ≤ w) (hV : Fits w V)
    (hrep : Rep w base U V n_max θ s x) (op : Dictionary.Op U)
    (hvalid : (Dictionary.spec U V n_max).valid s op)
    (hop : x.regs regOp = opTag op)
    (hu : x.regs regU = (opKey op).val)
    (hv : ∀ u v, op = .insert u v → x.regs regV = v) :
    ∃ y : Data 12,
      ExecWithin w (opCode U n_max) x y
        (opPathSteps U n_max θ (extractSlots base U n_max x.mem) (opKey op)) ∧
      Rep w base U V n_max θ ((Dictionary.spec U V n_max).step s op).1 y ∧
      y.regs regOp = opOutWord s op ∧
      Modifies (Block.mk base (space U n_max)).footprint x.mem y.mem := by
  have hO :
      (otherOccupiedSlots (extractSlots base U n_max x.mem) (opKey op)).card < numBuckets n_max :=
    lt_of_le_of_lt (hrep.table_rep.card_otherOccupiedSlots_le (opKey op))
      (lt_of_le_of_lt hrep.dom_le (lt_numBuckets n_max))
  obtain ⟨d1, e1, hd1_mem, hd1_base, hd1_slot, hd1_sbase, hd1_mask, hd1_stride, hd1_m,
      hd1_zero, hd1_op, hd1_u, hd1_v⟩ :=
    opEvalHashesCode_execWithin hS hw hrep (opKey op) hu
  have hwf_d1 : SlotArrayWF base U n_max d1.mem := by simpa [hd1_mem] using hrep.slot_wf
  obtain ⟨d2, e2, hd2_mem, hd2_cond, hd2_regs⟩ :=
    probeCheckCode_execWithin hS hwf_d1 (opKey op)
      (probePerm θ (opKey op) ⟨0, numBuckets_pos n_max⟩)
      hd1_sbase hd1_slot hd1_m hd1_zero hd1_u
  have hd2_mem_eq : d2.mem = x.mem := hd2_mem.trans hd1_mem
  have hd2_cond' : d2.regs regCond =
      (if probePerm θ (opKey op) ⟨0, numBuckets_pos n_max⟩ ∈
          otherOccupiedSlots (extractSlots base U n_max x.mem) (opKey op) then 1 else 0) := by
    rw [hd1_mem] at hd2_cond
    exact hd2_cond
  obtain ⟨d3, e3, hd3_mem, hd3_slot, hd3_regs⟩ :=
    probeLoop_execWithin_aux θ hS hrep.slot_wf (opKey op) hO
      (missedProbes (otherOccupiedSlots (extractSlots base U n_max x.mem) (opKey op))
        (probePerm θ (opKey op))) 0 (numBuckets_pos n_max) d2
      (zero_add _) hd2_mem_eq
      (by rw [hd2_regs regSlotBase (by decide) (by decide), hd1_sbase])
      (by rw [hd2_regs regMaskM (by decide) (by decide), hd1_mask])
      (by rw [hd2_regs regStride (by decide) (by decide), hd1_stride])
      (by rw [hd2_regs regM (by decide) (by decide), hd1_m])
      (by rw [hd2_regs regZero (by decide) (by decide), hd1_zero])
      (by rw [hd2_regs regU (by decide) (by decide), hd1_u])
      (by rw [hd2_regs regSlot (by decide) (by decide), hd1_slot])
      hd2_cond'
  have hd3_base : d3.regs regBase = base := by
    rw [hd3_regs regBase (by decide) (by decide) (by decide),
      hd2_regs regBase (by decide) (by decide), hd1_base]
  have hd3_sbase : d3.regs regSlotBase = base + slotOffset U n_max := by
    rw [hd3_regs regSlotBase (by decide) (by decide) (by decide),
      hd2_regs regSlotBase (by decide) (by decide), hd1_sbase]
  have hd3_m : d3.regs regM = numBuckets n_max := by
    rw [hd3_regs regM (by decide) (by decide) (by decide),
      hd2_regs regM (by decide) (by decide), hd1_m]
  have hd3_zero : d3.regs regZero = 0 := by
    rw [hd3_regs regZero (by decide) (by decide) (by decide),
      hd2_regs regZero (by decide) (by decide), hd1_zero]
  have hd3_op : d3.regs regOp = opTag op := by
    rw [hd3_regs regOp (by decide) (by decide) (by decide),
      hd2_regs regOp (by decide) (by decide), hd1_op, hop]
  have hd3_u : d3.regs regU = (opKey op).val := by
    rw [hd3_regs regU (by decide) (by decide) (by decide),
      hd2_regs regU (by decide) (by decide), hd1_u]
  have hd3_v : d3.regs regV = x.regs regV := by
    rw [hd3_regs regV (by decide) (by decide) (by decide),
      hd2_regs regV (by decide) (by decide), hd1_v]
  cases op with
  | get u₀ =>
    have hc : (Cond.eq regOp regZero).Holds d3 := by
      simp [Cond.Holds, hd3_op, hd3_zero, opTag]
    obtain ⟨y, eFin, hy_mem, hy_base, hy_op⟩ :=
      finishGetCode_execWithin hS hV hrep u₀ hO hd3_mem hd3_base hd3_sbase hd3_slot hd3_m hd3_zero
    have eBr : ExecWithin w (.branch (.eq regOp regZero) finishGetCode finishInsertCode) d3 y 10 :=
      ExecWithin.branch_pos hc eFin
    have eTot : ExecWithin w (opCode U n_max) x y
        (opPathSteps U n_max θ (extractSlots base U n_max x.mem) u₀) := by
      refine (e1.seq (e2.seq (e3.seq eBr))).mono ?_
      dsimp only [opPathSteps, probeCount, unsuccessfulProbes, opKey] at *
      omega
    have hbdd_y : y.Bounded w := eTot.bounded hrep.bounded
    have hrep_y : Rep w base U V n_max θ s y :=
      hrep.congr hbdd_y (hy_base.trans hrep.regs_base.symm) (fun a _ => by rw [hy_mem])
    have hmod : Modifies (Block.mk base (space U n_max)).footprint x.mem y.mem := by
      intro a _
      rw [hy_mem]
    exact ⟨y, eTot, hrep_y, hy_op, hmod⟩
  | insert u₀ v₀ =>
    have hc : ¬(Cond.eq regOp regZero).Holds d3 := by
      simp [Cond.Holds, hd3_op, hd3_zero, opTag]
    have hd3_v₀ : d3.regs regV = v₀ := hd3_v.trans (hv u₀ v₀ rfl)
    obtain ⟨y, eFin, hy_base, hy_op, hy_tab, hy_ms, hy_wf, hy_trep, hy_dom, hy_vals, hy_mod⟩ :=
      finishInsertCode_execWithin hS hrep u₀ v₀ hvalid hO
        hd3_mem hd3_base hd3_sbase hd3_slot hd3_m hd3_u hd3_v₀
    have eBr : ExecWithin w (.branch (.eq regOp regZero) finishGetCode finishInsertCode) d3 y 10 :=
      ExecWithin.branch_neg hc eFin
    have eTot : ExecWithin w (opCode U n_max) x y
        (opPathSteps U n_max θ (extractSlots base U n_max x.mem) u₀) := by
      refine (e1.seq (e2.seq (e3.seq eBr))).mono ?_
      dsimp only [opPathSteps, probeCount, unsuccessfulProbes, opKey] at *
      omega
    have hbdd_y : y.Bounded w := eTot.bounded hrep.bounded
    exact ⟨y, eTot,
      ⟨hbdd_y, hy_base, hy_tab, hy_ms, hy_wf, hy_trep, hy_dom, hy_vals⟩,
      hy_op, hy_mod⟩

/-! ## Section 5: `SubroutineCode`, `SubroutineDS`, and Expected Probe / Collision Bounds -/

/-- Relocatable `SubroutineCode` over `Basis.exact` (`12` registers, `0` runtime init parameters)
for the open-addressed permutation-probing dictionary. -/
def subroutineCode (U n_max : ℕ) : SubroutineCode .exact 12 0 where
  allocSpan := allocSpan U n_max
  initSetup := initSetup U n_max
  code := opCode U n_max
  frontierReg := regV
  baseReg := regBase
  initParams := Fin.elim0
  curReg := regCond
  zeroReg := regAddr
  oneReg := regSlot
  incCur := .exactBin .add regCond regCond regSlot
  input := fun i => decide (i ≠ regBase)
  output := regOp

/-- Standalone argument encoder for `Dictionary.Op U` on `12` registers. -/
def encodeOp {U : ℕ} : Dictionary.Op U → Fin 12 → ℕ
  | .get u, i =>
      if i = regOp then 0
      else if i = regU then u.val
      else 0
  | .insert u v, i =>
      if i = regOp then 1
      else if i = regU then u.val
      else if i = regV then v
      else 0

/-- Partial argument-matching predicate for inline and standalone callers. -/
def argMatch {U : ℕ} (op : Dictionary.Op U) (regs : Fin 12 → ℕ) : Prop :=
  regs regOp = opTag op ∧
  regs regU = (opKey op).val ∧
  ∀ u v, op = .insert u v → regs regV = v

/-- Output decoder reading typed operation observations from final registers. -/
def decodeOp {U V n_max : ℕ} : (op : Dictionary.Op U) → (Fin 12 → ℕ) →
    Option ((Dictionary.spec U V n_max).Result op)
  | .get _, regs => some (if regs regOp = 0 then none else some (regs regOp - 1))
  | .insert _ _, _ => some ()

theorem encode_matches {U n_max : ℕ} (op : Dictionary.Op U) (regs : Fin 12 → ℕ) :
    argMatch op (fun i => if (subroutineCode U n_max).input i then encodeOp op i else regs i) := by
  cases op with
  | get u =>
    refine ⟨rfl, ?_, fun _ _ h => by nomatch h⟩
    simp +decide [subroutineCode, encodeOp, opKey]
  | insert u v =>
    refine ⟨rfl, ?_, fun u' v' h => ?_⟩
    · simp +decide [subroutineCode, encodeOp, opKey]
    · cases h
      simp +decide [subroutineCode, encodeOp]

theorem arguments_fit {w U V n_max : ℕ}
    (hw : 2 * hashBits U n_max ≤ w) (hV : Fits w V)
    {s : Dictionary.State U} (op : Dictionary.Op U)
    (hv : (Dictionary.spec U V n_max).valid s op)
    (i : Fin 12) :
    Fits w (encodeOp op i) := by
  have hpos_hb := hashBits_pos U n_max
  have hfit0 : Fits w 0 := fits_zero w
  have hfit1 : Fits w 1 := fits_one (by omega)
  have hfitU : ∀ u : Fin U, Fits w u.val := by
    intro u
    rw [fits_iff]
    have hu_lt : u.val < 2 ^ hashBits U n_max := lt_two_pow_hashBits n_max u
    have hpow : 2 ^ hashBits U n_max ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
    exact hu_lt.trans_le hpow
  cases op with
  | get u =>
    dsimp only [encodeOp]
    split_ifs
    · exact hfit0
    · exact hfitU u
    · exact hfit0
  | insert u v =>
    dsimp only [encodeOp]
    split_ifs
    · exact hfit1
    · exact hfitU u
    · exact hV.of_le (by have := hv.2; omega)
    · exact hfit0

theorem decodeOp_eq_step {U V n_max : ℕ} {s : Dictionary.State U}
    (op : Dictionary.Op U) (regs : Fin 12 → ℕ)
    (h : regs regOp = opOutWord s op) :
    decodeOp (V := V) (n_max := n_max) op regs =
      some ((Dictionary.spec U V n_max).step s op).2 := by
  cases op with
  | get u =>
    dsimp only [decodeOp, Dictionary.spec, opOutWord] at h ⊢
    rw [h]
    cases s u with
    | none => simp
    | some v => simp
  | insert u v =>
    rfl

theorem step_exec_spec {w base U V n_max : ℕ}
    (hS : Fits w (base + space U n_max)) (hw : 2 * hashBits U n_max ≤ w) (hV : Fits w V)
    {s : Dictionary.State U} (o : Dictionary.Op U)
    (ν : PMF (Seed U n_max × Data 12))
    (hv : (Dictionary.spec U V n_max).valid s o)
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ 1 * seedLaw U n_max θ)
    (hsupp : ∀ p ∈ ν.support, Rep w base U V n_max p.1 s p.2 ∧ argMatch o p.2.regs) :
    ∃ (μ_step : Seed U n_max × Data 12 → PMF (Seed U n_max × Data 12))
      (T_step : Seed U n_max × Data 12 → ℝ≥0∞),
      (∀ p ∈ ν.support,
        ExecCodeDist w (opCode U n_max) p.2 ((μ_step p).map Prod.snd) (T_step p) ∧
        ∀ q ∈ (μ_step p).support,
          decodeOp (V := V) (n_max := n_max) o q.2.regs =
            some ((Dictionary.spec U V n_max).step s o).2 ∧
          Rep w base U V n_max q.1 ((Dictionary.spec U V n_max).step s o).1 q.2 ∧
          Modifies (Block.mk base (space U n_max)).footprint p.2.mem q.2.mem) ∧
      (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ 1 * seedLaw U n_max θ') ∧
      (∑' p, ν p * (T_step p + ∑' q, μ_step p q * ((0 : ℕ) : ℝ≥0∞))) ≤
        (opSteps U n_max : ℝ≥0∞) + ∑' p, ν p * ((0 : ℕ) : ℝ≥0∞) := by
  classical
  have hEx : ∀ p : Seed U n_max × Data 12, ∃ y : Data 12,
      p ∈ ν.support →
        ExecWithin w (opCode U n_max) p.2 y (opSteps U n_max) ∧
        Rep w base U V n_max p.1 ((Dictionary.spec U V n_max).step s o).1 y ∧
        y.regs regOp = opOutWord s o ∧
        Modifies (Block.mk base (space U n_max)).footprint p.2.mem y.mem := by
    intro p
    by_cases hp : p ∈ ν.support
    · obtain ⟨hrep, harg1, harg2, harg3⟩ := hsupp p hp
      have hO :
          (otherOccupiedSlots (extractSlots base U n_max p.2.mem) (opKey o)).card <
            numBuckets n_max :=
        lt_of_le_of_lt (hrep.table_rep.card_otherOccupiedSlots_le (opKey o))
          (lt_of_le_of_lt hrep.dom_le (lt_numBuckets n_max))
      obtain ⟨y, e, hrep_y, hout, hmod⟩ :=
        opCode_execWithin hS hw hV hrep o hv harg1 harg2 harg3
      exact ⟨y, fun _ => ⟨e.mono (opPathSteps_le_opSteps p.1 _ _ hO), hrep_y, hout, hmod⟩⟩
    · exact ⟨p.2, fun h => False.elim (hp h)⟩
  let yOf : Seed U n_max × Data 12 → Data 12 := fun p => Classical.choose (hEx p)
  refine ⟨fun p => PMF.pure (p.1, yOf p), fun _ => (opSteps U n_max : ℝ≥0∞), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨e, hrep_y, hout, hmod⟩ := Classical.choose_spec (hEx p) hp
    refine ⟨?_, ?_⟩
    · simpa [yOf] using ExecCodeDist.of_execWithin e
    · intro q hq
      rw [PMF.support_pure, Set.mem_singleton_iff] at hq
      subst hq
      exact ⟨decodeOp_eq_step o (yOf p).regs hout, hrep_y, hmod⟩
  · intro θ'
    have hmap : ((ν.bind fun p => PMF.pure (p.1, yOf p)).map Prod.fst) = ν.map Prod.fst := by
      rw [PMF.map_bind]
      simp only [PMF.map, PMF.pure_bind]
      rfl
    rw [hmap]
    exact hseed θ'
  · simp [ENNReal.tsum_mul_right, ν.tsum_coe]

/-- **Composable randomized Word-RAM `SubroutineDS` certificate over `Basis.exact`** for the
open-addressed permutation-probing dictionary realizing `Dictionary.spec U V n_max`. -/
noncomputable def subroutineDS {w base U V n_max : ℕ}
    (hS : Fits w (base + space U n_max)) (hw : 2 * hashBits U n_max ≤ w) (hV : Fits w V) :
    Randomized.SubroutineDS (subroutineCode U n_max)
      (Dictionary.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) where
  Seed := Seed U n_max
  seedLaw := seedLaw U n_max
  seedSlack := 1
  space := space U n_max
  spanTime := 3
  setupTime := (setupSteps U n_max : ℝ≥0∞)
  initPotential := 0
  charge _ _ := opSteps U n_max
  rep := Rep w base U V n_max
  potential _ _ := 0
  encode := encodeOp
  argMatch := argMatch
  decode := decodeOp
  bounded hrep := hrep.bounded
  rep_unique h1 h2 := h1.unique h2
  arguments_fit o hv i _ := arguments_fit hw hV o hv i
  encode_matches := encode_matches
  rep_supported {θ s x x'} hregs hmem hbdd hrep := by
    have hbase : x'.regs regBase = x.regs regBase := hregs regBase rfl
    exact hrep.congr hbdd hbase hmem
  potential_supported _ _ _ := rfl
  clear_nodup := by
    dsimp only [subroutineCode]
    decide
  params_not_clear j := Fin.elim0 j
  incCur_eval {x} h1 hfit := by
    dsimp only [subroutineCode] at h1 hfit ⊢
    simp [Op.exactBin, Op.eval, StandardOp.evalExact, Data.put, h1, hfit]
  span_exec {x} _ hfr _ := by
    obtain ⟨x₁, he, hm, hb, hfr'⟩ := allocSpan_execWithin hS hfr
    exact ⟨x₁, he, hm, hb, hfr', fun j => Fin.elim0 j⟩
  setup_exec {x₁} hx₁ hb hfr _ hz :=
    setup_exec_spec hS hw hx₁ hb hfr hz
  step_exec {s} o ν hv hseed hsupp :=
    step_exec_spec hS hw hV o ν hv hseed hsupp

/-- Standard-basis (`Basis.standard`) randomized `SubroutineDS` certificate for the open-addressed
permutation-probing dictionary. -/
noncomputable abbrev subroutineDSStandard {w base U V n_max : ℕ}
    (hS : Fits w (base + space U n_max)) (hw : 2 * hashBits U n_max ≤ w) (hV : Fits w V) :
    Randomized.SubroutineDS (subroutineCode U n_max).toStandard
      (Dictionary.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  (subroutineDS hS hw hV).toStandard

/-- **End-to-end multi-operation expected-time theorem (`seq_expected_amortized`)**:
from fresh zeroed memory `[base, base + space U n_max)`, initializing the permutation-probing
dictionary (`initFresh`) and executing the subroutine operation bodies (`ExecSteps`) across any
admissible operation history `ops : List (Dictionary.Op U)` fixed independently of the sampled seed
(oblivious adversary) takes at most `3 + setupSteps U n_max + ops.length * opSteps U n_max` expected
Word-RAM instructions (charging the deterministic full-cycle body bound `opSteps U n_max` per
operation and excluding caller argument delivery, caller control/dispatch loops, and
code/configuration construction). -/
theorem seq_expected_amortized {w base U V n_max : ℕ}
    (hS : Fits w (base + space U n_max)) (hw : 2 * hashBits U n_max ≤ w) (hV : Fits w V)
    {x : Data 12} (ops : List (Dictionary.Op U))
    (hx : x.Bounded w) (hfr : x.regs regV = base)
    (hz : ∀ a ∈ (Block.mk base (space U n_max)).footprint, x.mem a = 0)
    (hv : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    ∃ (ν₀ ν_final : PMF (Seed U n_max × Data 12)) (T_ops : ℝ≥0∞),
      ExecCodeDist w (subroutineCode U n_max).initFresh x (ν₀.map Prod.snd)
        (subroutineDS (V := V) hS hw hV).initTime ∧
      (subroutineDS (V := V) hS hw hV).ExecSteps (Dictionary.empty U) ops ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ seedLaw U n_max θ) ∧
      (∀ p ∈ ν_final.support,
        Rep w base U V n_max p.1
          ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1 p.2) ∧
      (subroutineDS (V := V) hS hw hV).initTime + T_ops ≤
        (3 + setupSteps U n_max : ℝ≥0∞) +
          ((Dictionary.spec U V n_max).totalCost (fun _ _ => opSteps U n_max)
            (Dictionary.empty U) ops : ℝ≥0∞) := by
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hrep_final, hbound⟩ :=
    (subroutineDS (V := V) hS hw hV).seq_expected_amortized ops hx hfr (fun j => Fin.elim0 j) hz hv
  refine ⟨ν₀, ν_final, T_ops, he_init, hex_steps, ?_, hrep_final, ?_⟩
  · intro θ
    have h1 : (ν_final.map Prod.fst) θ ≤ 1 * seedLaw U n_max θ := hseed_final θ
    rwa [one_mul] at h1
  · have hinit : (subroutineDS (V := V) hS hw hV).initTime = (3 + setupSteps U n_max : ℝ≥0∞) := rfl
    rw [hinit]
    have h2 : (3 + (setupSteps U n_max : ℝ≥0∞)) + T_ops +
        ∑' q : Seed U n_max × Data 12, ν_final q * ((0 : ℕ) : ℝ≥0∞) ≤
        (3 + (setupSteps U n_max : ℝ≥0∞)) + ((0 : ℕ) : ℝ≥0∞) +
          ((Dictionary.spec U V n_max).totalCost (fun _ _ => opSteps U n_max)
            (Dictionary.empty U) ops : ℝ≥0∞) := hbound
    simpa only [Nat.cast_zero, mul_zero, tsum_zero, add_zero, Nat.cast_add, Nat.cast_ofNat] using h2

/-- The first projection of `seedLaw U n_max` is the uniform distribution on multiply-shift
seeds `Fin (2 ^ (hashBits U n_max - 1))`. -/
theorem map_fst_seedLaw (U n_max : ℕ) :
    (seedLaw U n_max).map Prod.fst = PMF.uniformOfFintype (Fin (2 ^ (hashBits U n_max - 1))) :=
  Cslib.Probability.PMF.uniformOfFintype_prod_map_fst

/-- **Primary-slot `2 / numBuckets n_max`-universality (`isUniversalHash_primaryHash`)**:
the primary hash `primaryHash θ : Fin U → Fin (numBuckets n_max)` under `seedLaw U n_max` is
`(2 / numBuckets n_max)`-universal. -/
theorem isUniversalHash_primaryHash (U n_max : ℕ) :
    Cslib.Probability.IsUniversalHash (seedLaw U n_max) (primaryHash (U := U) (n_max := n_max))
      (2 / (numBuckets n_max : ℝ≥0∞)) := by
  intro u₁ u₂ hne
  have h1 := Cslib.Probability.isUniversalHash_multiplyShift
    (hashBits_pos U n_max) (bucketBits_le_hashBits U n_max)
    (encodeKey n_max u₁) (encodeKey n_max u₂)
    (fun h => hne (encodeKey_injective n_max h))
  rw [← map_fst_seedLaw U n_max, PMF.toOuterMeasure_map_apply] at h1
  have heq : (Prod.fst ⁻¹' {σ : Fin (2 ^ (hashBits U n_max - 1)) |
      Cslib.Probability.multiplyShift (hashBits U n_max) (bucketBits n_max) σ
        (encodeKey n_max u₁) =
      Cslib.Probability.multiplyShift (hashBits U n_max) (bucketBits n_max) σ
        (encodeKey n_max u₂)}) =
      {θ : Seed U n_max | primaryHash θ u₁ = primaryHash θ u₂} := by
    ext θ
    simp [primaryHash, Fin.ext_iff]
  rw [heq] at h1
  have hnum : (2 / (numBuckets n_max : ℝ≥0∞)) = 2 / 2 ^ bucketBits n_max := by
    simp [numBuckets]
  rw [hnum]
  exact h1

/-- **Parametric expected-step bound from any expected-probe bound**:
for any permutation distribution `μ : PMF α` and family
`π : α → Equiv.Perm (Fin (numBuckets n_max))` whose expected probe count on table `T` and key `u`
is at most `B`, the expected Word-RAM instruction count of the probe path is at most
`13 * B + (8 * numChars U n_max + 49)`. -/
theorem expect_opPathSteps_le_of_probeBound {α : Type*} {U n_max : ℕ}
    (μ : PMF α) (π : α → Equiv.Perm (Fin (numBuckets n_max)))
    (T : Fin (numBuckets n_max) → Option (Fin U × ℕ)) (u : Fin U) (B : ℝ≥0∞)
    (hB : (∑' a, μ a * (UniformProbing.probeCount T u (π a) : ℝ≥0∞)) ≤ B) :
    (∑' a, μ a *
      ((13 * UniformProbing.probeCount T u (π a) + 8 * numChars U n_max + 49 : ℕ) : ℝ≥0∞)) ≤
      13 * B + (8 * numChars U n_max + 49 : ℝ≥0∞) := by
  have hterm : ∀ a : α,
      μ a * ((13 * UniformProbing.probeCount T u (π a) + 8 * numChars U n_max + 49 : ℕ) : ℝ≥0∞) =
        13 * (μ a * (UniformProbing.probeCount T u (π a) : ℝ≥0∞)) +
          μ a * (8 * numChars U n_max + 49 : ℝ≥0∞) := by
    intro a
    push_cast
    ring
  simp_rw [hterm]
  rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
  gcongr

/-- **Ideal uniform-probing expected-step corollary (`≤ 8 * numChars U n_max + 75`)**:
when the probe permutation `π` is drawn uniformly from `Equiv.Perm (Fin (numBuckets n_max))` on a
table `T` with at most `n_max` other occupied slots (`(otherOccupiedSlots T u).card ≤ n_max`), the
expected Word-RAM step count `13 * probeCount T u π + 8 * numChars U n_max + 49` is at most
`8 * numChars U n_max + 75` (combining `expect_opPathSteps_le_of_probeBound` with `B = 2` from
`UniformProbing.expect_unsuccessfulProbes_le_two`). -/
theorem expect_idealProbeSteps_le {U n_max : ℕ}
    (T : Fin (numBuckets n_max) → Option (Fin U × ℕ)) (u : Fin U)
    (hcard : (UniformProbing.otherOccupiedSlots T u).card ≤ n_max) :
    (∑' π : Equiv.Perm (Fin (numBuckets n_max)),
      (PMF.uniformOfFintype (Equiv.Perm (Fin (numBuckets n_max)))) π *
        ((13 * UniformProbing.probeCount T u π + 8 * numChars U n_max + 49 : ℕ) : ℝ≥0∞)) ≤
      (8 * numChars U n_max + 75 : ℝ≥0∞) := by
  have h2m : 2 * (UniformProbing.otherOccupiedSlots T u).card ≤ numBuckets n_max := by
    have h4 := four_mul_le_numBuckets n_max
    omega
  have hB : (∑' π : Equiv.Perm (Fin (numBuckets n_max)),
      (PMF.uniformOfFintype (Equiv.Perm (Fin (numBuckets n_max)))) π *
        (UniformProbing.probeCount T u π : ℝ≥0∞)) ≤ 2 :=
    UniformProbing.expect_unsuccessfulProbes_le_two (numBuckets_pos n_max) h2m
  have hstep := expect_opPathSteps_le_of_probeBound (U := U) (n_max := n_max)
    (PMF.uniformOfFintype (Equiv.Perm (Fin (numBuckets n_max)))) id T u 2 hB
  refine hstep.trans ?_
  have heq : (13 : ℝ≥0∞) * 2 + (8 * numChars U n_max + 49 : ℝ≥0∞) =
      (8 * numChars U n_max + 75 : ℝ≥0∞) := by
    ring
  exact le_of_eq heq

end Cslib.Algorithms.WordRAM.Dictionary.UniformProbing
