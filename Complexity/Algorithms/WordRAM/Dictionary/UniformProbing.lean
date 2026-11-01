/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Dictionary
public import Complexity.Algorithms.Lean.DoubleHashing
public import Complexity.Algorithms.Lean.UniformProbing
public import Complexity.DataStructure.HashFamily.WordRAM.DoubleTabulation
public import Complexity.Computability.WordRAM.ExactNotation
public import Complexity.Computability.WordRAM.Randomized.Subroutine
import all Complexity.Algorithms.Lean.DoubleHashing
import Complexity.Probability.PMF.Expect

/-!
# Self-Contained Open-Addressed Permutation-Probing Dictionary on the Word-RAM

This file implements a self-contained open-addressed permutation-probing dictionary realizing
`Cslib.Algorithms.Lean.Dictionary.spec U V n_max` (`get` and `insert` up to `n_max` distinct keys)
on the Word-RAM (`Cslib.WordRAM.Basis.exact` and `Cslib.WordRAM.Basis.standard`), combining the
power-of-two odd-stride double-hashing construction of
[Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms*, third edition (MIT Press,
2009), Section 11.4, "Double hashing", pp. 269–277][CLRS2009], the `k`-wise independence double
hashing analysis of [J. P. Schmidt and A. Siegel, *The Analysis of Closed Hashing under Limited
Randomness*, STOC 1990, pp. 224–234; extended NYU Courant Technical Report `TR1995-687`, May 1995,
pp. 1–2, 4–7, 37–39][SchmidtSiegel1990], and Mikkel Thorup's Double Tabulation
([M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence*, FOCS
2013, pp. 90–99; `arXiv:1311.3121v2`, pp. 4–5, 11–13][Thorup2013], Theorem 1(a) and Lemma 2).

## Design and reuse of `Cslib.Algorithms.Lean.UniformProbing` and `DoubleHashing`

In the ideal uniform-probing model (`Complexity/Algorithms/Lean/UniformProbing.lean`), each key
`u : Fin U` is assigned an independent random permutation `π u : Equiv.Perm (Fin m)`. Storing an
explicit table of `U` permutations requires `Ω(U)` words when `U = poly(n_max) ≫ n_max`.

To achieve a self-contained `O_{c_exp}(n_max + 1)`-word data structure with assumption-free
`O_{c_exp}(1)` expected operation time whenever `U ≤ max n_max 4 ^ c_exp`, we construct for each key
`u : Fin U` a full-cycle affine permutation of `m = 2 ^ M` slots
(`M = bucketBits n_max = Nat.clog 2 (32 * max n_max 4)`):
`probePerm θ u i = (h₁(u) + i * (2 * h₂(u) + 1)) mod 2 ^ M`, where `h₁(u) ∈ Fin (2 ^ M)` and
`h₂(u) ∈ Fin (2 ^ (M - 1))` are independent instances of Mikkel Thorup's Double Tabulation
(`Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation`, with `c = 2 * max c_exp 1`, `d = 8 * c`,
and `b = (1 + Nat.clog 2 (max n_max 4)) / 2`).

Because `2 * h₂(u) + 1` is always odd and therefore coprime to `2 ^ M`, `probePerm θ u` is a
bijection on `Fin (2 ^ M)` for **every** seed `θ` and key `u`
(`DoubleHashing.bijective_oddStrideSeq`).
We maintain `DoubleHashing.OrderedTableRep (probePerm θ)` on the concrete Word-RAM slot arrays and
discharge the expected probe count unconditionally across **all** capacities `n_max : ℕ` via
`DoubleHashing.expect_probeCount_oddStride_unconditional_le` (at most `3` probes above
`doubleTabThreshold c_exp` and at most `doubleTabThreshold c_exp` across all `n_max : ℕ`), yielding
an assumption-free `O_{c_exp}(1)` expected operation charge `expectedOpCharge c_exp` independent of
`n_max` and `U`, and `space c_exp n_max ≤ spaceFactor c_exp * (n_max + 1) = O_{c_exp}(n_max + 1)`
words of memory.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.bucketBits`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.numBuckets`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.numChars`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.tupleLen`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.charBits`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.singleTabSpace`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.slotOffset`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.space`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.spaceFactor`: table dimension parameters and
  memory footprint.
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.Seed`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.seedLaw`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.primaryHash`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.rawStrideHash`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.strideHash`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.probePerm`: Double Tabulation seed space,
  uniform seed law, primary and odd-stride hashes, and full-cycle probe permutation.
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.extractSlots`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.Rep`: slot-array extractor and Word-RAM
  representation invariant (`DoubleHashing.OrderedTableRep`).
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.allocSpan`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.initSetup`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.opCode`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.subroutineCode`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.expectedOpCharge`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.subroutineDS`,
  `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.subroutineDSStandard`: structured Word-RAM
  programs and assumption-free `Randomized.SubroutineDS` certificates over `Basis.exact` and
  `Basis.standard`.

## Main results

* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.space_le`:
  `space c_exp n_max ≤ spaceFactor c_exp * (n_max + 1) = O_{c_exp}(n_max + 1)` across all `n_max`.
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.setup_exec_spec`: randomized seed and table
  initialization in `setupSteps c_exp n_max = O_{c_exp}(n_max + 1)` instructions.
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.opCode_execWithin`: every `get` or `insert`
  operation on key `u` executes in at most
  `opPathSteps c_exp θ T u = 13 * probeCount T u (probePerm θ u) + hashEvalSteps c_exp + 8`
  instructions.
* `Cslib.Algorithms.WordRAM.Dictionary.UniformProbing.seq_expected_amortized`: assumption-free
  `O_{c_exp}(1)` expected operation time (`expectedOpCharge c_exp`) across any admissible sequence
  `ops : List (Dictionary.Op U)` whenever `U ≤ max n_max 4 ^ c_exp`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*, third edition (MIT Press, 2009), Section 11.4,
  pp. 269–277][CLRS2009]
* [J. P. Schmidt and A. Siegel, *The Analysis of Closed Hashing under Limited
  Randomness*][SchmidtSiegel1990] (STOC 1990, pp. 224–234; NYU Courant Technical Report
  `TR1995-687`, May 1995, pp. 1–2, 4–7, 37–39)
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence*][Thorup2013] (FOCS 2013, pp. 90–99; `arXiv:1311.3121v2`, pp. 4–5, 11–13)
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dictionary.UniformProbing

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.DoubleHashing
open Cslib.Algorithms.Lean.UniformProbing
open Cslib.Algorithms.WordRAM.Hashing
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation
open Cslib.Probability
open Cslib.WordRAM
open Cslib.WordRAM.Randomized
open scoped BigOperators ENNReal

/-! ## Section 1: Table Parameters, Seed Space, and Full-Cycle Probe Permutations -/

/-- Log₂ of the power-of-2 table size: `M = ⌈log₂ (32 * max n_max 4)⌉ ≥ 7`. -/
def bucketBits (n_max : ℕ) : ℕ :=
  Nat.clog 2 (32 * max n_max 4)

/-- Power-of-2 number of open-addressed table slots `m = 2 ^ bucketBits n_max ≥ 32 * max n_max 4`.
-/
def numBuckets (n_max : ℕ) : ℕ :=
  2 ^ bucketBits n_max

/-- Number of base-`2 ^ b` characters `c = 2 * max c_exp 1` for Double Tabulation under
`U ≤ max n_max 4 ^ c_exp`. -/
abbrev numChars (c_exp : ℕ) : ℕ :=
  DoubleTabulation.provableC c_exp

/-- Intermediate tuple length `d = 8 * numChars c_exp = 16 * max c_exp 1` for Double Tabulation. -/
abbrev tupleLen (c_exp : ℕ) : ℕ :=
  DoubleTabulation.provableD c_exp

/-- Character bit-width `b = (1 + Nat.clog 2 (max n_max 4)) / 2` for Double Tabulation. -/
abbrev charBits (n_max : ℕ) : ℕ :=
  DoubleTabulation.provableB n_max

/-- Memory footprint `(numChars c_exp + 1) * tupleLen c_exp * 2 ^ charBits n_max` words of a single
Double Tabulation table (`T₁` and `T₂`). -/
def singleTabSpace (c_exp n_max : ℕ) : ℕ :=
  DoubleTabulation.space (numChars c_exp) (tupleLen c_exp) (charBits n_max)

/-- Offset `2 * singleTabSpace c_exp n_max` of the open-addressed slot arrays relative to `base`
(after the primary hash table at `[base, base + singleTabSpace c_exp n_max)` and the stride hash
table at `[base + singleTabSpace c_exp n_max, base + 2 * singleTabSpace c_exp n_max)`). -/
def slotOffset (c_exp n_max : ℕ) : ℕ :=
  2 * singleTabSpace c_exp n_max

/-- Total memory footprint `slotOffset c_exp n_max + 3 * numBuckets n_max` words in
`[base, base + space c_exp n_max)`. -/
def space (c_exp n_max : ℕ) : ℕ :=
  slotOffset c_exp n_max + 3 * numBuckets n_max

/-- Explicit `O_{c_exp}(1)` linear-space factor bounding `space c_exp n_max` by
`spaceFactor c_exp * (n_max + 1)` across every `n_max : ℕ`. -/
def spaceFactor (c_exp : ℕ) : ℕ :=
  32 * (numChars c_exp + 1) * tupleLen c_exp + 768

theorem seven_le_bucketBits (n_max : ℕ) : 7 ≤ bucketBits n_max := by
  dsimp only [bucketBits]
  calc
    7 = Nat.clog 2 (2 ^ 7) := (Nat.clog_pow 2 7 (by decide)).symm
    _ ≤ Nat.clog 2 (32 * max n_max 4) := Nat.clog_mono_right 2 (by omega)

theorem two_le_bucketBits (n_max : ℕ) : 2 ≤ bucketBits n_max :=
  le_trans (by decide : 2 ≤ 7) (seven_le_bucketBits n_max)

theorem bucketBits_pos (n_max : ℕ) : 0 < bucketBits n_max :=
  lt_of_lt_of_le (by decide : 0 < 7) (seven_le_bucketBits n_max)

theorem thirtyTwo_mul_max_le_numBuckets (n_max : ℕ) :
    32 * max n_max 4 ≤ numBuckets n_max :=
  Nat.le_pow_clog (by decide) (32 * max n_max 4)

theorem four_le_numBuckets (n_max : ℕ) : 4 ≤ numBuckets n_max := by
  have := thirtyTwo_mul_max_le_numBuckets n_max
  omega

theorem four_mul_le_numBuckets (n_max : ℕ) : 4 * n_max ≤ numBuckets n_max := by
  have := thirtyTwo_mul_max_le_numBuckets n_max
  omega

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

theorem numBuckets_le_mul_add_one (n_max : ℕ) :
    numBuckets n_max ≤ 256 * (n_max + 1) := by
  have hlt := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (32 * max n_max 4)
  have hclog_le : bucketBits n_max ≤ Nat.log 2 (32 * max n_max 4) + 1 :=
    Nat.clog_le_of_le_pow (le_of_lt hlt)
  have hpow : numBuckets n_max ≤ 2 * 2 ^ Nat.log 2 (32 * max n_max 4) := by
    calc numBuckets n_max
        ≤ 2 ^ (Nat.log 2 (32 * max n_max 4) + 1) :=
          Nat.pow_le_pow_right (by decide) hclog_le
      _ = 2 * 2 ^ Nat.log 2 (32 * max n_max 4) := by ring
  have hlog_le : 2 ^ Nat.log 2 (32 * max n_max 4) ≤ 32 * max n_max 4 :=
    Nat.pow_log_le_self 2 (by omega)
  omega

/-- **All-`n_max` linear space bound (`O_{c_exp}(n_max + 1)`)**:
for every `c_exp, n_max : ℕ`, `space c_exp n_max ≤ spaceFactor c_exp * (n_max + 1)`. -/
theorem space_le (c_exp n_max : ℕ) :
    space c_exp n_max ≤ spaceFactor c_exp * (n_max + 1) := by
  have hpow : 2 ^ charBits n_max ≤ 16 * (n_max + 1) := by
    have h4 := DoubleTabulation.two_pow_provableB_le n_max
    dsimp only [charBits, DoubleTabulation.provableB] at h4 ⊢
    omega
  have htab : singleTabSpace c_exp n_max ≤
      16 * (numChars c_exp + 1) * tupleLen c_exp * (n_max + 1) := by
    dsimp only [singleTabSpace, DoubleTabulation.space]
    calc (numChars c_exp + 1) * tupleLen c_exp * 2 ^ charBits n_max
        ≤ (numChars c_exp + 1) * tupleLen c_exp * (16 * (n_max + 1)) :=
          Nat.mul_le_mul_left _ hpow
      _ = 16 * (numChars c_exp + 1) * tupleLen c_exp * (n_max + 1) := by ring
  have hbuck := numBuckets_le_mul_add_one n_max
  dsimp only [space, slotOffset, spaceFactor]
  calc 2 * singleTabSpace c_exp n_max + 3 * numBuckets n_max
      ≤ 2 * (16 * (numChars c_exp + 1) * tupleLen c_exp * (n_max + 1)) +
          3 * (256 * (n_max + 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 htab) (Nat.mul_le_mul_left 3 hbuck)
    _ = (32 * (numChars c_exp + 1) * tupleLen c_exp + 768) * (n_max + 1) := by ring

/-- Combined Double Tabulation seed `DoubleHashSeed c_exp n_max (bucketBits n_max)` consisting of
the primary hash seed `(T₁, T₂)` and the half-range stride hash seed `(S₁, S₂)`. -/
abbrev Seed (c_exp n_max : ℕ) : Type :=
  DoubleHashing.DoubleHashSeed c_exp n_max (bucketBits n_max)

/-- Uniform reference distribution over `Seed c_exp n_max`. -/
noncomputable def seedLaw (c_exp n_max : ℕ) : PMF (Seed c_exp n_max) :=
  PMF.uniformOfFintype (Seed c_exp n_max)

/-- Double Tabulation primary slot `h₁(u) ∈ Fin (numBuckets n_max)`. -/
def primaryHash {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    Fin (numBuckets n_max) :=
  match θ with
  | ((T₁, T₂), _) =>
    doubleTabHash (numChars c_exp) (tupleLen c_exp) (charBits n_max) U (bucketBits n_max)
      T₁ T₂ u

/-- Double Tabulation half-range stride index `h₂(u) ∈ Fin (2 ^ (bucketBits n_max - 1))`. -/
def rawStrideHash {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    Fin (2 ^ (bucketBits n_max - 1)) :=
  match θ with
  | (_, (S₁, S₂)) =>
    doubleTabHash (numChars c_exp) (tupleLen c_exp) (charBits n_max) U
      (bucketBits n_max - 1) S₁ S₂ u

theorem two_mul_rawStrideHash_add_one_lt {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    2 * (rawStrideHash θ u).val + 1 < numBuckets n_max := by
  have hlt := (rawStrideHash θ u).isLt
  have hpos := bucketBits_pos n_max
  have hpow : 2 * 2 ^ (bucketBits n_max - 1) = numBuckets n_max := by
    dsimp only [numBuckets]
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  omega

/-- Odd probe stride `2 * (rawStrideHash θ u).val + 1 ∈ Fin (numBuckets n_max)`. -/
def strideHash {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    Fin (numBuckets n_max) :=
  ⟨2 * (rawStrideHash θ u).val + 1, two_mul_rawStrideHash_add_one_lt θ u⟩

@[simp]
theorem val_strideHash {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    (strideHash θ u).val = 2 * (rawStrideHash θ u).val + 1 :=
  rfl

/-- Full-cycle double-hashing probe permutation
`probePerm θ u : Equiv.Perm (Fin (numBuckets n_max))` sending probe index `i` to
`(h₁(u) + i * (2 * h₂(u) + 1)) mod 2 ^ M`. -/
noncomputable def probePerm {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    Equiv.Perm (Fin (numBuckets n_max)) :=
  DoubleHashing.doubleHashOddStridePerm c_exp n_max U (bucketBits n_max) θ u

@[simp]
theorem val_probePerm {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U)
    (i : Fin (numBuckets n_max)) :
    (probePerm θ u i).val =
      ((primaryHash θ u).val + i.val * (strideHash θ u).val) % numBuckets n_max := by
  rcases θ with ⟨⟨T₁, T₂⟩, ⟨S₁, S₂⟩⟩
  exact DoubleHashing.val_oddStridePerm _ _ u i

@[simp]
theorem probePerm_zero {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U) :
    probePerm θ u ⟨0, numBuckets_pos n_max⟩ = primaryHash θ u := by
  apply Fin.ext
  rw [val_probePerm]
  simpa using Nat.mod_eq_of_lt (primaryHash θ u).isLt

/-- One step of the Word-RAM probe loop `(slot + stride) &&& (2 ^ M - 1)` advances from
`probePerm θ u ⟨i, _⟩` to `probePerm θ u ⟨i + 1, _⟩`. -/
theorem val_probePerm_succ {c_exp U n_max : ℕ} (θ : Seed c_exp n_max) (u : Fin U)
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
`[base + slotOffset c_exp n_max, base + slotOffset c_exp n_max + 3 * numBuckets n_max)`:
each `used[j]` word is `0` or `1`, and whenever `used[j] = 1`, `key[j] < U`. -/
def SlotArrayWF (base c_exp U n_max : ℕ) (mem : ℕ → ℕ) : Prop :=
  let sBase := base + slotOffset c_exp n_max
  let m := numBuckets n_max
  ∀ j : Fin m,
    (mem (sBase + j.val) = 0 ∨ mem (sBase + j.val) = 1) ∧
    (mem (sBase + j.val) = 1 → mem (sBase + m + j.val) < U)

/-- Extract the abstract open-addressed table `UniformProbing.Table U (numBuckets n_max)` from
Word-RAM memory `mem`. -/
def extractSlots (base c_exp U n_max : ℕ) (mem : ℕ → ℕ) :
    UniformProbing.Table U (numBuckets n_max) :=
  let sBase := base + slotOffset c_exp n_max
  let m := numBuckets n_max
  fun j =>
    if mem (sBase + j.val) = 0 then none
    else if h : mem (sBase + m + j.val) < U then
      some (⟨mem (sBase + m + j.val), h⟩, mem (sBase + 2 * m + j.val))
    else none

theorem extractSlots_eq_none_iff {base c_exp U n_max : ℕ} {mem : ℕ → ℕ}
    (hwf : SlotArrayWF base c_exp U n_max mem) (j : Fin (numBuckets n_max)) :
    extractSlots base c_exp U n_max mem j = none ↔
      mem (base + slotOffset c_exp n_max + j.val) = 0 := by
  rcases hwf j with ⟨h0 | h1, hkey⟩
  · simp [extractSlots, h0]
  · have hlt : mem (base + slotOffset c_exp n_max + numBuckets n_max + j.val) < U := hkey h1
    simp [extractSlots, h1, hlt]

theorem extractSlots_eq_some_iff {base c_exp U n_max : ℕ} {mem : ℕ → ℕ}
    (hwf : SlotArrayWF base c_exp U n_max mem) (j : Fin (numBuckets n_max))
    (u : Fin U) (v : ℕ) :
    extractSlots base c_exp U n_max mem j = some (u, v) ↔
      mem (base + slotOffset c_exp n_max + j.val) = 1 ∧
      mem (base + slotOffset c_exp n_max + numBuckets n_max + j.val) = u.val ∧
      mem (base + slotOffset c_exp n_max + 2 * numBuckets n_max + j.val) = v := by
  rcases hwf j with ⟨h0 | h1, hkey⟩
  · simp [extractSlots, h0]
  · have hlt : mem (base + slotOffset c_exp n_max + numBuckets n_max + j.val) < U := hkey h1
    simp [extractSlots, h1, hlt, Fin.ext_iff]

theorem mem_otherOccupiedSlots_extractSlots_iff {base c_exp U n_max : ℕ} {mem : ℕ → ℕ}
    (hwf : SlotArrayWF base c_exp U n_max mem) (u : Fin U) (j : Fin (numBuckets n_max)) :
    j ∈ otherOccupiedSlots (extractSlots base c_exp U n_max mem) u ↔
      mem (base + slotOffset c_exp n_max + j.val) = 1 ∧
      mem (base + slotOffset c_exp n_max + numBuckets n_max + j.val) ≠ u.val := by
  rw [mem_otherOccupiedSlots_iff]
  constructor
  · rintro ⟨u', v', hsome, hne⟩
    rw [extractSlots_eq_some_iff hwf] at hsome
    refine ⟨hsome.1, ?_⟩
    rw [hsome.2.1]
    exact fun h => hne (Fin.ext h)
  · rintro ⟨h1, hne⟩
    have hlt : mem (base + slotOffset c_exp n_max + numBuckets n_max + j.val) < U :=
      (hwf j).2 h1
    refine ⟨⟨mem (base + slotOffset c_exp n_max + numBuckets n_max + j.val), hlt⟩,
      mem (base + slotOffset c_exp n_max + 2 * numBuckets n_max + j.val), ?_, ?_⟩
    · rw [extractSlots_eq_some_iff hwf]
      exact ⟨h1, rfl, rfl⟩
    · intro heq
      exact hne (congrArg Fin.val heq)

/-- Coupled representation invariant `Rep w base c_exp U V n_max θ s x` on `Data 16`:
* `x.Bounded w`;
* `x.regs 0 = base`;
* `DoubleTabulation.SeedRep` holds for `θ.1` at `[base, base + singleTabSpace c_exp n_max)` and
  for `θ.2` at `[base + singleTabSpace c_exp n_max, base + 2 * singleTabSpace c_exp n_max)`;
* `SlotArrayWF base c_exp U n_max x.mem` and
  `DoubleHashing.OrderedTableRep (probePerm θ) s (extractSlots base c_exp U n_max x.mem)` hold on
  the slot arrays;
* `(Dictionary.dom s).card ≤ n_max` and `Dictionary.ValuesBounded V s`. -/
structure Rep (w base c_exp U V n_max : ℕ) (θ : Seed c_exp n_max) (s : Dictionary.State U)
    (x : Data 16) : Prop where
  bounded : x.Bounded w
  regs_base : x.regs 0 = base
  primary_rep : DoubleTabulation.SeedRep base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
    (bucketBits n_max) θ.1 x.mem
  stride_rep : DoubleTabulation.SeedRep (base + singleTabSpace c_exp n_max) (numChars c_exp)
    (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) θ.2 x.mem
  slot_wf : SlotArrayWF base c_exp U n_max x.mem
  table_rep : DoubleHashing.OrderedTableRep (probePerm θ) s
    (extractSlots base c_exp U n_max x.mem)
  dom_le : (Dictionary.dom s).card ≤ n_max
  vals_bounded : Dictionary.ValuesBounded V s

theorem Rep.unique {w base c_exp U V n_max : ℕ} {θ : Seed c_exp n_max}
    {s₁ s₂ : Dictionary.State U} {x : Data 16}
    (h₁ : Rep w base c_exp U V n_max θ s₁ x) (h₂ : Rep w base c_exp U V n_max θ s₂ x) :
    s₁ = s₂ := by
  funext u
  cases hs₁ : s₁ u with
  | none =>
    cases hs₂ : s₂ u with
    | none => rfl
    | some v₂ =>
      obtain ⟨hlt, hT⟩ := h₂.table_rep.toTableRep.key_spec u v₂ hs₂
      have hs₁' := (h₁.table_rep.toTableRep.slot_spec _ u v₂ hT).1
      rw [hs₁] at hs₁'
      cases hs₁'
  | some v₁ =>
    obtain ⟨hlt, hT⟩ := h₁.table_rep.toTableRep.key_spec u v₁ hs₁
    exact (h₂.table_rep.toTableRep.slot_spec _ u v₁ hT).1.symm

theorem mem_footprint_of_lt_space {base c_exp n_max a : ℕ}
    (hlo : base ≤ a) (hhi : a < base + space c_exp n_max) :
    a ∈ (Block.mk base (space c_exp n_max)).footprint := by
  rw [Block.mem_footprint]
  exact ⟨hlo, hhi⟩

theorem SlotArrayWF.congr_mem {base c_exp U n_max : ℕ} {mem mem' : ℕ → ℕ}
    (hmem : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, mem' a = mem a)
    (hwf : SlotArrayWF base c_exp U n_max mem) :
    SlotArrayWF base c_exp U n_max mem' := by
  intro j
  have hj := j.isLt
  have hsp : space c_exp n_max = slotOffset c_exp n_max + 3 * numBuckets n_max := rfl
  have h0 : mem' (base + slotOffset c_exp n_max + j.val) =
      mem (base + slotOffset c_exp n_max + j.val) :=
    hmem _ (mem_footprint_of_lt_space (by omega) (by omega))
  have h1 : mem' (base + slotOffset c_exp n_max + numBuckets n_max + j.val) =
      mem (base + slotOffset c_exp n_max + numBuckets n_max + j.val) :=
    hmem _ (mem_footprint_of_lt_space (by omega) (by omega))
  dsimp only [SlotArrayWF] at hwf ⊢
  rw [h0, h1]
  exact hwf j

theorem extractSlots_congr_mem {base c_exp U n_max : ℕ} {mem mem' : ℕ → ℕ}
    (hmem : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, mem' a = mem a) :
    extractSlots base c_exp U n_max mem' = extractSlots base c_exp U n_max mem := by
  funext j
  have hj := j.isLt
  have hsp : space c_exp n_max = slotOffset c_exp n_max + 3 * numBuckets n_max := rfl
  have h0 : mem' (base + slotOffset c_exp n_max + j.val) =
      mem (base + slotOffset c_exp n_max + j.val) :=
    hmem _ (mem_footprint_of_lt_space (by omega) (by omega))
  have h1 : mem' (base + slotOffset c_exp n_max + numBuckets n_max + j.val) =
      mem (base + slotOffset c_exp n_max + numBuckets n_max + j.val) :=
    hmem _ (mem_footprint_of_lt_space (by omega) (by omega))
  have h2 : mem' (base + slotOffset c_exp n_max + 2 * numBuckets n_max + j.val) =
      mem (base + slotOffset c_exp n_max + 2 * numBuckets n_max + j.val) :=
    hmem _ (mem_footprint_of_lt_space (by omega) (by omega))
  dsimp only [extractSlots]
  rw [h0, h1, h2]

theorem Rep.congr {w base c_exp U V n_max : ℕ} {θ : Seed c_exp n_max} {s : Dictionary.State U}
    {x x' : Data 16}
    (hbdd : x'.Bounded w) (hbase : x'.regs 0 = x.regs 0)
    (hmem : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, x'.mem a = x.mem a)
    (hrep : Rep w base c_exp U V n_max θ s x) :
    Rep w base c_exp U V n_max θ s x' := by
  have hsp : space c_exp n_max = 2 * singleTabSpace c_exp n_max + 3 * numBuckets n_max := rfl
  have hst : singleTabSpace c_exp n_max =
      DoubleTabulation.space (numChars c_exp) (tupleLen c_exp) (charBits n_max) := rfl
  have hprim : DoubleTabulation.SeedRep base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
      (bucketBits n_max) θ.1 x'.mem :=
    hrep.primary_rep.congr_mem fun a hlo hhi =>
      hmem a (mem_footprint_of_lt_space hlo (by omega))
  have hstr : DoubleTabulation.SeedRep (base + singleTabSpace c_exp n_max) (numChars c_exp)
      (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) θ.2 x'.mem :=
    hrep.stride_rep.congr_mem fun a hlo hhi =>
      hmem a (mem_footprint_of_lt_space (by omega) (by omega))
  refine ⟨hbdd, hbase.trans hrep.regs_base, hprim, hstr,
    hrep.slot_wf.congr_mem hmem, ?_, hrep.dom_le, hrep.vals_bounded⟩
  rw [extractSlots_congr_mem hmem]
  exact hrep.table_rep

theorem slotArrayWF_of_zero {base c_exp U n_max : ℕ} {mem : ℕ → ℕ}
    (hz : ∀ j : Fin (numBuckets n_max), mem (base + slotOffset c_exp n_max + j.val) = 0) :
    SlotArrayWF base c_exp U n_max mem := by
  intro j
  refine ⟨Or.inl (hz j), ?_⟩
  rw [hz j]
  intro h
  omega

theorem extractSlots_eq_emptyTable_of_zero {base c_exp U n_max : ℕ} {mem : ℕ → ℕ}
    (hz : ∀ j : Fin (numBuckets n_max), mem (base + slotOffset c_exp n_max + j.val) = 0) :
    extractSlots base c_exp U n_max mem = emptyTable U (numBuckets n_max) := by
  funext j
  simp [extractSlots, emptyTable, hz j]

/-! ## Section 3: Register Layout, Allocation, and Randomized Initialization -/

/-- Register `0` (`baseReg`, persistent): holds the base memory address `base`. -/
abbrev regBase : Fin 16 := 0

/-- Register `1` (`curReg`): loop condition / Double Tabulation key input. -/
abbrev regCond : Fin 16 := 1

/-- Register `2` (`zeroReg`): memory address / Double Tabulation output. -/
abbrev regAddr : Fin 16 := 2

/-- Register `3` (`oneReg`): current probe slot `slot ∈ Fin (numBuckets n_max)`. -/
abbrev regSlot : Fin 16 := 3

/-- Register `4`: slot array base address `base + slotOffset c_exp n_max`. -/
abbrev regSlotBase : Fin 16 := 4

/-- Register `5`: bucket mask `numBuckets n_max - 1`. -/
abbrev regMaskM : Fin 16 := 5

/-- Register `6`: odd probe stride `strideHash θ u`. -/
abbrev regStride : Fin 16 := 6

/-- Register `7`: table size `numBuckets n_max`. -/
abbrev regM : Fin 16 := 7

/-- Register `8`: constant `0` during probing / general scratch. -/
abbrev regZero : Fin 16 := 8

/-- Register `12` (`output`): operation tag (`0` for `get`, `1` for `insert`) on input; decoded
return value (`0` for `none`/`()`, `v + 1` for `some v`) on output. -/
abbrev regOp : Fin 16 := 12

/-- Register `13`: input key `u.val < U`. -/
abbrev regU : Fin 16 := 13

/-- Register `14` (`frontierReg`): input value `v < V` for `insert` / allocation frontier. -/
abbrev regV : Fin 16 := 14

/-- Register `15`: temporary register saving `primaryHash θ u` across the second hash evaluation. -/
abbrev regSave : Fin 16 := 15

/-- Register injection `Fin 12 → Fin 16` embedding `DoubleTabulation` into registers `0..11`
(preserving `regOp = 12`, `regU = 13`, `regV = 14`, `regSave = 15`). -/
def dtMap : Fin 12 → Fin 16 :=
  Fin.castLE (by decide)

theorem injective_dtMap : Function.Injective dtMap :=
  Fin.castLE_injective _

theorem notMem_range_dtMap {j : Fin 16} (hj : 12 ≤ j.val) :
    j ∉ Set.range dtMap := by
  rintro ⟨i, rfl⟩
  have := i.isLt
  simp only [dtMap, Fin.val_castLE] at hj
  omega

/-- Allocation program `allocSpan c_exp n_max` (`3` instructions): copies `frontierReg` (`regV`) to
`baseReg` (`regBase`) and advances `frontierReg` by `space c_exp n_max`. -/
def allocSpan (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (.op (.copy regBase regV))
  (.seq (.op (.const regCond (space c_exp n_max)))
        (.op (.exactBin .add regV regBase regCond)))

theorem allocSpan_execWithin {w base c_exp n_max : ℕ} {x : Data 16}
    (hS : Fits w (base + space c_exp n_max)) (hfr : x.regs regV = base) :
    ∃ x₁ : Data 16,
      ExecWithin w (allocSpan c_exp n_max) x x₁ 3 ∧
      x₁.mem = x.mem ∧
      x₁.regs regBase = base ∧
      x₁.regs regV = base + space c_exp n_max := by
  have hfit_sp : Fits w (space c_exp n_max) := hS.of_le (by omega)
  set s1 := x.set regBase base
  have e1 : Exec w (.op (.copy regBase regV) : Code .exact 16) x s1 1 := by
    simpa [s1, hfr] using (Exec.copy (B := .exact) (w := w) (d := regBase) (s := regV) (x := x))
  set s2 := s1.set regCond (space c_exp n_max)
  have e2 : Exec w (.op (.const regCond (space c_exp n_max)) : Code .exact 16) s1 s2 1 :=
    Exec.const hfit_sp
  set s3 := s2.set regV (base + space c_exp n_max)
  have e3 : Exec w (.op (.exactBin .add regV regBase regCond) : Code .exact 16) s2 s3 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s2, s1]) hS
  exact ⟨s3, (e1.seq (e2.seq e3)).within, rfl,
    by simp +decide [s3, s2, s1], by simp +decide [s3]⟩

theorem fits_of_space {w base c_exp n_max : ℕ} (hS : Fits w (base + space c_exp n_max)) :
    Fits w (base + singleTabSpace c_exp n_max) ∧
    Fits w (base + singleTabSpace c_exp n_max + singleTabSpace c_exp n_max) ∧
    Fits w (2 ^ charBits n_max) ∧
    Fits w (2 ^ charBits n_max - 1) ∧
    Fits w (2 ^ bucketBits n_max) ∧
    Fits w (2 ^ bucketBits n_max - 1) ∧
    Fits w (2 ^ (bucketBits n_max - 1)) ∧
    Fits w (2 ^ (bucketBits n_max - 1) - 1) ∧
    Fits w 1 := by
  have hc : 1 ≤ numChars c_exp := DoubleTabulation.one_le_provableC c_exp
  have hd : 1 ≤ tupleLen c_exp := by
    dsimp only [tupleLen, DoubleTabulation.provableD, DoubleTabulation.provableC]
    omega
  have hpowB_pos : 1 ≤ 2 ^ charBits n_max := Nat.one_le_two_pow
  have hcd_pos : 1 ≤ (numChars c_exp + 1) * tupleLen c_exp := by
    have : 1 * 1 ≤ (numChars c_exp + 1) * tupleLen c_exp := Nat.mul_le_mul (by omega) hd
    omega
  have hpowB_le : 2 ^ charBits n_max ≤ singleTabSpace c_exp n_max := by
    dsimp only [singleTabSpace, DoubleTabulation.space]
    calc 2 ^ charBits n_max = 1 * 2 ^ charBits n_max := (one_mul _).symm
      _ ≤ (numChars c_exp + 1) * tupleLen c_exp * 2 ^ charBits n_max :=
          Nat.mul_le_mul_right _ hcd_pos
  have hsp : space c_exp n_max = 2 * singleTabSpace c_exp n_max + 3 * numBuckets n_max := rfl
  have hM : 2 ^ bucketBits n_max = numBuckets n_max := rfl
  have hM1_le : 2 ^ (bucketBits n_max - 1) ≤ numBuckets n_max :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ 1)
  have h4 := four_le_numBuckets n_max
  refine ⟨hS.of_le (by omega), hS.of_le (by omega), hS.of_le (by omega), hS.of_le (by omega),
    hS.of_le (by omega), hS.of_le (by omega), hS.of_le (by omega), hS.of_le (by omega),
    hS.of_le (by omega)⟩

/-- Deterministic 2-instruction glue advancing `regBase` by `singleTabSpace c_exp n_max`. -/
def initMidCode (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (.op (.const regCond (singleTabSpace c_exp n_max)))
        (.op (.exactBin .add regBase regBase regCond))

/-- Closed-form machine state after `initMidCode c_exp n_max`. -/
def initMidData (base c_exp n_max : ℕ) (d : Data 16) : Data 16 :=
  (d.set regCond (singleTabSpace c_exp n_max)).set regBase (base + singleTabSpace c_exp n_max)

theorem initMidCode_exec {w base c_exp n_max : ℕ} {d : Data 16}
    (hbase : d.regs regBase = base) (hS : Fits w (base + space c_exp n_max)) :
    Exec w (initMidCode c_exp n_max) d (initMidData base c_exp n_max d) 2 := by
  obtain ⟨hfit_btab, _, _, _, _, _, _, _, _⟩ := fits_of_space hS
  have hfit_tab : Fits w (singleTabSpace c_exp n_max) := hfit_btab.of_le (by omega)
  set s1 := d.set regCond (singleTabSpace c_exp n_max)
  have e1 : Exec w (.op (.const regCond (singleTabSpace c_exp n_max)) : Code .exact 16) d s1 1 :=
    Exec.const hfit_tab
  set s2 := s1.set regBase (base + singleTabSpace c_exp n_max)
  have e2 : Exec w (.op (.exactBin .add regBase regBase regCond) : Code .exact 16) s1 s2 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s1, hbase]) hfit_btab
  exact e1.seq e2

/-- Deterministic 2-instruction glue restoring `regBase` from `base + singleTabSpace c_exp n_max`
back to `base`. -/
def initPostCode (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (.op (.const regCond (singleTabSpace c_exp n_max)))
        (.op (.exactBin .sub regBase regBase regCond))

/-- Closed-form machine state after `initPostCode c_exp n_max`. -/
def initPostData (base c_exp n_max : ℕ) (d : Data 16) : Data 16 :=
  (d.set regCond (singleTabSpace c_exp n_max)).set regBase base

theorem initPostCode_exec {w base c_exp n_max : ℕ} {d : Data 16}
    (hbase : d.regs regBase = base + singleTabSpace c_exp n_max)
    (hS : Fits w (base + space c_exp n_max)) :
    Exec w (initPostCode c_exp n_max) d (initPostData base c_exp n_max d) 2 := by
  obtain ⟨hfit_btab, _, _, _, _, _, _, _, _⟩ := fits_of_space hS
  have hfit_tab : Fits w (singleTabSpace c_exp n_max) := hfit_btab.of_le (by omega)
  have hfit_base : Fits w base := hfit_btab.of_le (by omega)
  set s1 := d.set regCond (singleTabSpace c_exp n_max)
  have e1 : Exec w (.op (.const regCond (singleTabSpace c_exp n_max)) : Code .exact 16) d s1 1 :=
    Exec.const hfit_tab
  set s2 := s1.set regBase base
  have e2 : Exec w (.op (.exactBin .sub regBase regBase regCond) : Code .exact 16) s1 s2 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s1, hbase]) hfit_base
  exact e1.seq e2

/-- Complete randomized setup program `initSetup c_exp n_max`: resamples the primary Double
Tabulation seed at `[base, base + singleTabSpace c_exp n_max)` and the stride Double Tabulation
seed at `[base + singleTabSpace c_exp n_max, base + 2 * singleTabSpace c_exp n_max)`. -/
def initSetup (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq ((DoubleTabulation.resampleCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)
          (bucketBits n_max)).rename dtMap)
  (.seq (initMidCode c_exp n_max)
  (.seq ((DoubleTabulation.resampleCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)
          (bucketBits n_max - 1)).rename dtMap)
        (initPostCode c_exp n_max)))

/-- Total instruction count
`2 * resampleSteps (numChars c_exp) (tupleLen c_exp) (charBits n_max) + 4` of
`initSetup c_exp n_max`. -/
def setupSteps (c_exp n_max : ℕ) : ℕ :=
  2 * DoubleTabulation.resampleSteps (numChars c_exp) (tupleLen c_exp) (charBits n_max) + 4

/-- Extract the combined seed `Seed c_exp n_max` from machine state `y`. -/
def extractSeedPair (base c_exp n_max : ℕ) (y : Data 16) : Seed c_exp n_max :=
  (DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
      (bucketBits n_max) y.mem,
    DoubleTabulation.extractSeed (base + singleTabSpace c_exp n_max) (numChars c_exp)
      (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) y.mem)

/-- Stage-1 state distribution produced by the primary `DoubleTabulation.resampleCode`. -/
noncomputable def primaryInitPMF (base c_exp n_max : ℕ) (x₁ : Data 16) : PMF (Data 16) :=
  (Prod.fst <$>
    ((fun z => (z.1.extend dtMap x₁, z.2)) <$>
      DoubleTabulation.resampleComp base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
        (bucketBits n_max) (x₁.comap dtMap))).eval

/-- Stage-3 state distribution produced by the stride `DoubleTabulation.resampleCode` followed by
`initPostCode`. -/
noncomputable def strideInitPMF (base c_exp n_max : ℕ) (y₂ : Data 16) : PMF (Data 16) :=
  ((Prod.fst <$>
    ((fun z => (z.1.extend dtMap y₂, z.2)) <$>
      DoubleTabulation.resampleComp (base + singleTabSpace c_exp n_max) (numChars c_exp)
        (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) (y₂.comap dtMap))).eval).map
    (initPostData base c_exp n_max)

/-- Output state distribution of `initSetup c_exp n_max`. -/
noncomputable def initSetupPMF (base c_exp n_max : ℕ) (x₁ : Data 16) : PMF (Data 16) :=
  (primaryInitPMF base c_exp n_max x₁).bind
    (fun y₁ => strideInitPMF base c_exp n_max (initMidData base c_exp n_max y₁))

/-- Coupled `(Seed × Data 16)` distribution produced by `initSetup c_exp n_max`. -/
noncomputable def initSeedStatePMF (base c_exp n_max : ℕ) (x₁ : Data 16) :
    PMF (Seed c_exp n_max × Data 16) :=
  (initSetupPMF base c_exp n_max x₁).map (fun y => (extractSeedPair base c_exp n_max y, y))

theorem mem_support_primaryInitPMF {base c_exp n_max : ℕ} {x₁ y₁ : Data 16}
    (hbase : x₁.regs regBase = base)
    (hy₁ : y₁ ∈ (primaryInitPMF base c_exp n_max x₁).support) :
    DoubleTabulation.SeedRep base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
      (bucketBits n_max)
      (DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
        (bucketBits n_max) y₁.mem) y₁.mem ∧
    y₁.regs regBase = base ∧
    y₁.regs regV = x₁.regs regV ∧
    (∀ a, (a < base ∨ base + singleTabSpace c_exp n_max ≤ a) → y₁.mem a = x₁.mem a) := by
  dsimp only [primaryInitPMF] at hy₁
  rw [Functor.map_map, ProbComp.eval_map, PMF.mem_support_map_iff] at hy₁
  obtain ⟨z, hz, rfl⟩ := hy₁
  rw [ProbComp.support_eval] at hz
  have hbase_comap : (x₁.comap dtMap).regs 0 = base := hbase
  obtain ⟨hbase', hrep, hframe, -⟩ :=
    DoubleTabulation.mem_support_resampleComp hbase_comap hz
  have hbase_ext : (z.1.extend dtMap x₁).regs regBase = base := by
    change ((z.1.extend dtMap x₁).comap dtMap).regs 0 = base
    rw [Data.comap_extend injective_dtMap]
    exact hbase'
  have hv_ext : (z.1.extend dtMap x₁).regs regV = x₁.regs regV :=
    Data.extend_regs_of_notMem _ _ (notMem_range_dtMap (by decide))
  exact ⟨hrep, hbase_ext, hv_ext, hframe⟩

theorem map_extractSeed_primaryInitPMF (base c_exp n_max : ℕ) (x₁ : Data 16) :
    (primaryInitPMF base c_exp n_max x₁).map
        (fun y₁ =>
          DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
            (bucketBits n_max) y₁.mem) =
      PMF.uniformOfFintype
        (DoubleTabTopSeed (numChars c_exp) (tupleLen c_exp) (charBits n_max) ×
          DoubleTabBotSeed (tupleLen c_exp) (charBits n_max) (bucketBits n_max)) := by
  dsimp only [primaryInitPMF]
  rw [Functor.map_map, ProbComp.eval_map, PMF.map_comp]
  exact DoubleTabulation.map_extractSeed_eval_resampleComp base (numChars c_exp) (tupleLen c_exp)
    (charBits n_max) (bucketBits n_max) (x₁.comap dtMap)

theorem mem_support_strideInitPMF {base c_exp n_max : ℕ} {y₂ y : Data 16}
    (hbase : y₂.regs regBase = base + singleTabSpace c_exp n_max)
    (hy : y ∈ (strideInitPMF base c_exp n_max y₂).support) :
    DoubleTabulation.SeedRep (base + singleTabSpace c_exp n_max) (numChars c_exp) (tupleLen c_exp)
      (charBits n_max) (bucketBits n_max - 1)
      (DoubleTabulation.extractSeed (base + singleTabSpace c_exp n_max) (numChars c_exp)
        (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) y.mem) y.mem ∧
    y.regs regBase = base ∧
    y.regs regV = y₂.regs regV ∧
    (∀ a, (a < base + singleTabSpace c_exp n_max ∨
        base + singleTabSpace c_exp n_max + singleTabSpace c_exp n_max ≤ a) →
      y.mem a = y₂.mem a) := by
  dsimp only [strideInitPMF] at hy
  rw [PMF.mem_support_map_iff] at hy
  obtain ⟨y₃, hy₃, rfl⟩ := hy
  rw [Functor.map_map, ProbComp.eval_map, PMF.mem_support_map_iff] at hy₃
  obtain ⟨z, hz, rfl⟩ := hy₃
  rw [ProbComp.support_eval] at hz
  have hbase_comap : (y₂.comap dtMap).regs 0 = base + singleTabSpace c_exp n_max := hbase
  obtain ⟨-, hrep, hframe, -⟩ :=
    DoubleTabulation.mem_support_resampleComp hbase_comap hz
  have hv_ext : (initPostData base c_exp n_max (z.1.extend dtMap y₂)).regs regV = y₂.regs regV := by
    change (z.1.extend dtMap y₂).regs regV = y₂.regs regV
    exact Data.extend_regs_of_notMem _ _ (notMem_range_dtMap (by decide))
  exact ⟨hrep, by simp +decide [initPostData], hv_ext, hframe⟩

theorem map_extractSeedPair_strideInitPMF {base c_exp n_max : ℕ} (y₁ : Data 16) :
    (strideInitPMF base c_exp n_max (initMidData base c_exp n_max y₁)).map
        (extractSeedPair base c_exp n_max) =
      (PMF.uniformOfFintype
        (DoubleTabTopSeed (numChars c_exp) (tupleLen c_exp) (charBits n_max) ×
          DoubleTabBotSeed (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1))).map
        (fun S =>
          (DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
            (bucketBits n_max) y₁.mem, S)) := by
  set y₂ := initMidData base c_exp n_max y₁
  have hy₂_base : y₂.regs regBase = base + singleTabSpace c_exp n_max := by
    simp +decide [y₂, initMidData]
  have hcongr :
      (strideInitPMF base c_exp n_max y₂).map (extractSeedPair base c_exp n_max) =
      (strideInitPMF base c_exp n_max y₂).map
        (fun y =>
          (DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
            (bucketBits n_max) y₁.mem,
           DoubleTabulation.extractSeed (base + singleTabSpace c_exp n_max) (numChars c_exp)
            (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) y.mem)) := by
    apply PMF.map_congr_on_support
    intro y hy
    obtain ⟨-, -, -, hframe⟩ := mem_support_strideInitPMF hy₂_base hy
    have heq_prim :
        DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
          (bucketBits n_max) y.mem =
        DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
          (bucketBits n_max) y₁.mem :=
      DoubleTabulation.extractSeed_congr_mem fun a _ hhi => hframe a (Or.inl hhi)
    exact Prod.ext heq_prim rfl
  rw [hcongr]
  dsimp only [strideInitPMF]
  rw [PMF.map_comp, Functor.map_map, ProbComp.eval_map, PMF.map_comp]
  have hcomp :
      (((fun y : Data 16 =>
          (DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
            (bucketBits n_max) y₁.mem,
           DoubleTabulation.extractSeed (base + singleTabSpace c_exp n_max) (numChars c_exp)
            (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) y.mem)) ∘
        initPostData base c_exp n_max) ∘
        fun z : Data 12 × ℕ => z.1.extend dtMap y₂) =
      ((fun S =>
          (DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
            (bucketBits n_max) y₁.mem, S)) ∘
        fun z : Data 12 × ℕ =>
          DoubleTabulation.extractSeed (base + singleTabSpace c_exp n_max) (numChars c_exp)
            (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) z.1.mem) := rfl
  rw [hcomp, ← PMF.map_comp, DoubleTabulation.map_extractSeed_eval_resampleComp]

/-- **Exact uniformity of the sampled seed pair**: the seed marginal of `initSeedStatePMF` is the
exact product uniform distribution `seedLaw c_exp n_max`. -/
theorem map_fst_initSeedStatePMF (base c_exp n_max : ℕ) (x₁ : Data 16) :
    (initSeedStatePMF base c_exp n_max x₁).map Prod.fst = seedLaw c_exp n_max := by
  dsimp only [initSeedStatePMF, initSetupPMF]
  rw [PMF.map_comp]
  have hfst : Prod.fst ∘ (fun y : Data 16 => (extractSeedPair base c_exp n_max y, y)) =
      extractSeedPair base c_exp n_max := rfl
  rw [hfst, PMF.map_bind]
  simp_rw [map_extractSeedPair_strideInitPMF]
  let μ_stride : PMF
      (DoubleTabTopSeed (numChars c_exp) (tupleLen c_exp) (charBits n_max) ×
        DoubleTabBotSeed (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1)) :=
    PMF.uniformOfFintype
      (DoubleTabTopSeed (numChars c_exp) (tupleLen c_exp) (charBits n_max) ×
        DoubleTabBotSeed (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1))
  have hmap_bind :
      (primaryInitPMF base c_exp n_max x₁).bind
        (fun y₁ => μ_stride.map
          (fun S =>
            (DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
              (bucketBits n_max) y₁.mem, S))) =
      ((primaryInitPMF base c_exp n_max x₁).map
        (fun y₁ =>
          DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
            (bucketBits n_max) y₁.mem)).bind
        (fun P => μ_stride.map (fun S => (P, S))) := by
    rw [PMF.bind_map]
    rfl
  rw [hmap_bind, map_extractSeed_primaryInitPMF]
  exact PMF.uniformOfFintype_prod _ _

theorem initSetup_execCodeDist {w base c_exp n_max : ℕ} {x₁ : Data 16}
    (hbase : x₁.regs regBase = base) (hS : Fits w (base + space c_exp n_max)) :
    ExecCodeDist w (initSetup c_exp n_max) x₁ (initSetupPMF base c_exp n_max x₁)
      (setupSteps c_exp n_max) := by
  obtain ⟨hfit_btab, hfit_b2tab, _, hfit_mask_b, _, hfit_mask_M, _, hfit_mask_M1, hfit_1⟩ :=
    fits_of_space hS
  have hbase_comap : (x₁.comap dtMap).regs 0 = base := hbase
  have hprim_rand :=
    (DoubleTabulation.resampleCode_execRand (w := w) hbase_comap hfit_btab
      hfit_mask_b hfit_mask_M hfit_1).rename injective_dtMap
  have hprim_dist : ExecCodeDist w
      ((DoubleTabulation.resampleCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)
        (bucketBits n_max)).rename dtMap) x₁
      (primaryInitPMF base c_exp n_max x₁)
      (DoubleTabulation.resampleSteps (numChars c_exp) (tupleLen c_exp) (charBits n_max)) := by
    refine (ExecCodeDist.of_execRand hprim_rand).congr_dist rfl ?_
    rw [ProbComp.expect_map]
    refine (ProbComp.expect_mono_on_support fun z hz => ?_).trans
      (le_of_eq (ProbComp.expect_const _ _))
    obtain ⟨-, -, -, hsteps⟩ := DoubleTabulation.mem_support_resampleComp hbase_comap hz
    exact_mod_cast hsteps.le
  have hrest : ∀ y₁ ∈ (primaryInitPMF base c_exp n_max x₁).support,
      ExecCodeDist w
        (.seq (initMidCode c_exp n_max)
        (.seq ((DoubleTabulation.resampleCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)
                (bucketBits n_max - 1)).rename dtMap)
              (initPostCode c_exp n_max)))
        y₁ (strideInitPMF base c_exp n_max (initMidData base c_exp n_max y₁))
        (2 + (DoubleTabulation.resampleSteps (numChars c_exp) (tupleLen c_exp) (charBits n_max) +
          2 : ℕ)) := by
    intro y₁ hy₁
    obtain ⟨-, hb₁, -, -⟩ := mem_support_primaryInitPMF hbase hy₁
    have hmid := ExecCodeDist.of_exec (initMidCode_exec hb₁ hS)
    set y₂ := initMidData base c_exp n_max y₁
    have hy₂_base : y₂.regs regBase = base + singleTabSpace c_exp n_max := by
      simp +decide [y₂, initMidData]
    have hy₂_comap : (y₂.comap dtMap).regs 0 = base + singleTabSpace c_exp n_max := hy₂_base
    have hstr_rand :=
      (DoubleTabulation.resampleCode_execRand (w := w) hy₂_comap hfit_b2tab
        hfit_mask_b hfit_mask_M1 hfit_1).rename injective_dtMap
    let rawStridePMF : PMF (Data 16) :=
      (Prod.fst <$>
        ((fun z => (z.1.extend dtMap y₂, z.2)) <$>
          DoubleTabulation.resampleComp (base + singleTabSpace c_exp n_max) (numChars c_exp)
            (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) (y₂.comap dtMap))).eval
    have hstr_dist : ExecCodeDist w
        ((DoubleTabulation.resampleCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)
          (bucketBits n_max - 1)).rename dtMap) y₂
        rawStridePMF
        (DoubleTabulation.resampleSteps (numChars c_exp) (tupleLen c_exp) (charBits n_max)) := by
      refine (ExecCodeDist.of_execRand hstr_rand).congr_dist rfl ?_
      rw [ProbComp.expect_map]
      refine (ProbComp.expect_mono_on_support fun z hz => ?_).trans
        (le_of_eq (ProbComp.expect_const _ _))
      obtain ⟨-, -, -, hsteps⟩ := DoubleTabulation.mem_support_resampleComp hy₂_comap hz
      exact_mod_cast hsteps.le
    have hpost : ∀ y₃ ∈ rawStridePMF.support,
        ExecCodeDist w (initPostCode c_exp n_max) y₃
          (PMF.pure (initPostData base c_exp n_max y₃)) 2 := by
      intro y₃ hy₃
      dsimp only [rawStridePMF] at hy₃
      rw [Functor.map_map, ProbComp.eval_map, PMF.mem_support_map_iff] at hy₃
      obtain ⟨z, hz, rfl⟩ := hy₃
      rw [ProbComp.support_eval] at hz
      obtain ⟨hb₃, -, -, -⟩ := DoubleTabulation.mem_support_resampleComp hy₂_comap hz
      have hb₃_ext : (z.1.extend dtMap y₂).regs regBase = base + singleTabSpace c_exp n_max := by
        change ((z.1.extend dtMap y₂).comap dtMap).regs 0 = base + singleTabSpace c_exp n_max
        rw [Data.comap_extend injective_dtMap]
        exact hb₃
      exact ExecCodeDist.of_exec (initPostCode_exec hb₃_ext hS)
    have hstr_post : ExecCodeDist w
        (.seq ((DoubleTabulation.resampleCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)
                (bucketBits n_max - 1)).rename dtMap)
              (initPostCode c_exp n_max))
        y₂ (strideInitPMF base c_exp n_max y₂)
        (DoubleTabulation.resampleSteps (numChars c_exp) (tupleLen c_exp) (charBits n_max) +
          2 : ℕ) := by
      have hseq_post := hstr_dist.seq_const hpost (fun _ _ => le_rfl)
      have hdist_eq :
          rawStridePMF.bind (fun y₃ => PMF.pure (initPostData base c_exp n_max y₃)) =
            strideInitPMF base c_exp n_max y₂ :=
        (PMF.bind_pure_comp (initPostData base c_exp n_max) rawStridePMF).symm
      exact hseq_post.congr_dist hdist_eq (by norm_cast)
    exact hmid.seq_pure hstr_post
  have hseq := hprim_dist.seq_const hrest (fun _ _ => le_rfl)
  refine hseq.congr_dist rfl ?_
  dsimp only [setupSteps]
  norm_cast
  omega

/-- Full `SubroutineDS.setup_exec` certificate for `initSetup c_exp n_max`. -/
theorem setup_exec_spec {w base c_exp U V n_max : ℕ} {x₁ : Data 16}
    (hS : Fits w (base + space c_exp n_max))
    (hx₁ : x₁.Bounded w) (hbase : x₁.regs regBase = base)
    (hfr : x₁.regs regV = base + space c_exp n_max)
    (hz : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, x₁.mem a = 0) :
    ∃ ν₀ : PMF (Seed c_exp n_max × Data 16),
      ExecCodeDist w (initSetup c_exp n_max) x₁ (ν₀.map Prod.snd) (setupSteps c_exp n_max) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ 1 * seedLaw c_exp n_max θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs regV = base + space c_exp n_max ∧
        Rep w base c_exp U V n_max p.1 (Dictionary.empty U) p.2 ∧
        (0 : ℕ) ≤ 0 ∧
        Modifies (Block.mk base (space c_exp n_max)).footprint x₁.mem p.2.mem := by
  refine ⟨initSeedStatePMF base c_exp n_max x₁, ?_, ?_, ?_⟩
  · have hsnd : (initSeedStatePMF base c_exp n_max x₁).map Prod.snd =
        initSetupPMF base c_exp n_max x₁ := by
      dsimp only [initSeedStatePMF]
      rw [PMF.map_comp]
      exact PMF.map_id _
    rw [hsnd]
    exact initSetup_execCodeDist hbase hS
  · intro θ
    rw [map_fst_initSeedStatePMF, one_mul]
  · intro p hp
    dsimp only [initSeedStatePMF] at hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨y, hy, rfl⟩ := hp
    have hbdd_y : y.Bounded w :=
      (initSetup_execCodeDist hbase hS).bounded hx₁ y hy
    dsimp only [initSetupPMF] at hy
    rw [PMF.mem_support_bind_iff] at hy
    obtain ⟨y₁, hy₁, hy₃⟩ := hy
    obtain ⟨hprim_rep₁, hb₁, hv₁, hframe₁⟩ := mem_support_primaryInitPMF hbase hy₁
    set y₂ := initMidData base c_exp n_max y₁
    have hy₂_base : y₂.regs regBase = base + singleTabSpace c_exp n_max := by
      simp +decide [y₂, initMidData]
    obtain ⟨hstr_rep, hy_base, hy_v, hframe₃⟩ := mem_support_strideInitPMF hy₂_base hy₃
    have hy_v_eq : y.regs regV = base + space c_exp n_max := by
      rw [hy_v]
      simpa +decide [y₂, initMidData, hv₁] using hfr
    have hprim_eq :
        DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
          (bucketBits n_max) y.mem =
        DoubleTabulation.extractSeed base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
          (bucketBits n_max) y₁.mem :=
      DoubleTabulation.extractSeed_congr_mem fun a _ hhi => hframe₃ a (Or.inl hhi)
    have hprim_rep :
        DoubleTabulation.SeedRep base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
          (bucketBits n_max) (extractSeedPair base c_exp n_max y).1 y.mem := by
      dsimp only [extractSeedPair]
      rw [hprim_eq]
      exact hprim_rep₁.congr_mem fun a _ hhi => hframe₃ a (Or.inl hhi)
    have hz_slots : ∀ j : Fin (numBuckets n_max),
        y.mem (base + slotOffset c_exp n_max + j.val) = 0 := by
      intro j
      have hj := j.isLt
      have hsp : space c_exp n_max = slotOffset c_exp n_max + 3 * numBuckets n_max := rfl
      have hso : slotOffset c_exp n_max = 2 * singleTabSpace c_exp n_max := rfl
      rw [hframe₃ (base + slotOffset c_exp n_max + j.val) (Or.inr (by omega))]
      change y₁.mem (base + slotOffset c_exp n_max + j.val) = 0
      rw [hframe₁ (base + slotOffset c_exp n_max + j.val) (Or.inr (by omega))]
      exact hz _ (mem_footprint_of_lt_space (by omega) (by omega))
    have hwf : SlotArrayWF base c_exp U n_max y.mem := slotArrayWF_of_zero hz_slots
    have hempty : extractSlots base c_exp U n_max y.mem = emptyTable U (numBuckets n_max) :=
      extractSlots_eq_emptyTable_of_zero hz_slots
    have htrep : DoubleHashing.OrderedTableRep (probePerm (extractSeedPair base c_exp n_max y))
        (Dictionary.empty U) (extractSlots base c_exp U n_max y.mem) := by
      rw [hempty]
      exact DoubleHashing.OrderedTableRep.empty _
    have hmod : Modifies (Block.mk base (space c_exp n_max)).footprint x₁.mem y.mem := by
      intro a ha
      have ha_out : a < base ∨ base + space c_exp n_max ≤ a := by
        by_contra h
        rw [not_or, not_lt, not_le] at h
        exact ha (mem_footprint_of_lt_space h.1 h.2)
      have hsp : space c_exp n_max = 2 * singleTabSpace c_exp n_max + 3 * numBuckets n_max := rfl
      have ha₃ : a < base + singleTabSpace c_exp n_max ∨
          base + singleTabSpace c_exp n_max + singleTabSpace c_exp n_max ≤ a := by omega
      have ha₁ : a < base ∨ base + singleTabSpace c_exp n_max ≤ a := by omega
      rw [hframe₃ a ha₃]
      change y₁.mem a = x₁.mem a
      exact hframe₁ a ha₁
    refine ⟨hy_v_eq, ⟨hbdd_y, hy_base, hprim_rep, hstr_rep, hwf, htrep, ?_, ?_⟩, le_rfl, hmod⟩
    · simp
    · exact Dictionary.valuesBounded_empty U V

/-! ## Section 4: Lookup and Insertion Operations (`opCode`) -/

/-- Probe inspection snippet `probeCheckCode` (`≤ 9` instructions): checks whether the slot in
`regSlot` belongs to `otherOccupiedSlots (extractSlots base c_exp U n_max d.mem) u` (i.e.,
`used[slot] = 1` and `key[slot] ≠ u.val`), storing `1` in `regCond` if so and `0` otherwise. -/
def probeCheckCode : Code .exact 16 :=
  .seq (.op (.exactBin .add regAddr regSlotBase regSlot))
  (.seq (.op (.load regCond regAddr))
        (.branch (.eq regCond regZero)
          (.op (.const regCond 0))
          (.seq (.op (.exactBin .add regAddr regAddr regM))
          (.seq (.op (.load regCond regAddr))
                (.branch (.eq regCond regU)
                  (.op (.const regCond 0))
                  (.op (.const regCond 1)))))))

theorem probeCheckCode_execWithin {w base c_exp U n_max : ℕ} {d : Data 16}
    (hS : Fits w (base + space c_exp n_max))
    (hwf : SlotArrayWF base c_exp U n_max d.mem)
    (u : Fin U) (slot : Fin (numBuckets n_max))
    (hsbase : d.regs regSlotBase = base + slotOffset c_exp n_max)
    (hslot : d.regs regSlot = slot.val)
    (hm : d.regs regM = numBuckets n_max)
    (hzero : d.regs regZero = 0)
    (hu : d.regs regU = u.val) :
    ∃ d' : Data 16,
      ExecWithin w probeCheckCode d d' 9 ∧
      d'.mem = d.mem ∧
      d'.regs regCond =
        (if slot ∈ otherOccupiedSlots (extractSlots base c_exp U n_max d.mem) u then 1 else 0) ∧
      ∀ r : Fin 16, r ≠ regAddr → r ≠ regCond → d'.regs r = d.regs r := by
  have hslot_lt := slot.isLt
  have hsp : space c_exp n_max = slotOffset c_exp n_max + 3 * numBuckets n_max := rfl
  have hfit_0 : Fits w 0 := hS.of_le (by omega)
  have hfit_1 : Fits w 1 := hS.of_le (by omega)
  let sBase := base + slotOffset c_exp n_max
  let m := numBuckets n_max
  have hfit_a0 : Fits w (sBase + slot.val) := hS.of_le (by omega)
  have hfit_a1 : Fits w (sBase + slot.val + m) := hS.of_le (by omega)
  set s1 := d.set regAddr (sBase + slot.val)
  have e1 : Exec w (.op (.exactBin .add regAddr regSlotBase regSlot) : Code .exact 16) d s1 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, hsbase, hslot, sBase]) hfit_a0
  let usedVal := d.mem (sBase + slot.val)
  set s2 := s1.set regCond usedVal
  have e2 : Exec w (.op (.load regCond regAddr) : Code .exact 16) s1 s2 1 := by
    simpa +decide [s2, s1, usedVal] using
      (Exec.load (B := .exact) (w := w) (d := regCond) (a := regAddr) (x := s1))
  rcases (hwf slot).1 with hused0 | hused1
  · have hc : (Cond.eq regCond regZero).Holds s2 := by
      simp +decide [Cond.Holds, s2, s1, usedVal, sBase, hused0, hzero]
    set s3 := s2.set regCond 0
    have e3 : Exec w (.op (.const regCond 0) : Code .exact 16) s2 s3 1 := Exec.const hfit_0
    have hnot_mem : slot ∉ otherOccupiedSlots (extractSlots base c_exp U n_max d.mem) u := by
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
    have e3 : Exec w (.op (.exactBin .add regAddr regAddr regM) : Code .exact 16) s2 s3 1 :=
      Exec.alu (by simp +decide [StandardOp.evalExact, s2, s1, hm, m]) hfit_a1
    have haddr_eq : sBase + slot.val + m = sBase + m + slot.val := by omega
    let keyVal := d.mem (sBase + m + slot.val)
    set s4 := s3.set regCond keyVal
    have e4 : Exec w (.op (.load regCond regAddr) : Code .exact 16) s3 s4 1 := by
      simpa +decide [s4, s3, s2, s1, haddr_eq, keyVal] using
        (Exec.load (B := .exact) (w := w) (d := regCond) (a := regAddr) (x := s3))
    by_cases hkey : keyVal = u.val
    · have hc2 : (Cond.eq regCond regU).Holds s4 := by
        simp +decide [Cond.Holds, s4, s3, s2, s1, hkey, hu]
      set s5 := s4.set regCond 0
      have e5 : Exec w (.op (.const regCond 0) : Code .exact 16) s4 s5 1 := Exec.const hfit_0
      have hnot_mem : slot ∉ otherOccupiedSlots (extractSlots base c_exp U n_max d.mem) u := by
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
      have e5 : Exec w (.op (.const regCond 1) : Code .exact 16) s4 s5 1 := Exec.const hfit_1
      have hmem : slot ∈ otherOccupiedSlots (extractSlots base c_exp U n_max d.mem) u := by
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
def probeStepCode : Code .exact 16 :=
  .seq (.op (.exactBin .add regSlot regSlot regStride))
  (.seq (.op (.exactBin .and regSlot regSlot regMaskM))
        probeCheckCode)

/-- Probe loop: continues advancing `regSlot` while `0 < regCond` (i.e., while `regSlot` is occupied
by a key other than `u`). -/
def probeLoop : Code .exact 16 :=
  .loop (.lt regZero regCond) probeStepCode

theorem probeLoop_execWithin_aux {w base c_exp U n_max : ℕ} (θ : Seed c_exp n_max)
    (hS : Fits w (base + space c_exp n_max))
    {mem : ℕ → ℕ} (hwf : SlotArrayWF base c_exp U n_max mem)
    (u : Fin U)
    (hO : (otherOccupiedSlots (extractSlots base c_exp U n_max mem) u).card < numBuckets n_max) :
    let T := extractSlots base c_exp U n_max mem
    let O := otherOccupiedSlots T u
    let k := missedProbes O (probePerm θ u)
    ∀ (rem i : ℕ) (hi_lt : i < numBuckets n_max) (d : Data 16),
      i + rem = k →
      d.mem = mem →
      d.regs regSlotBase = base + slotOffset c_exp n_max →
      d.regs regMaskM = numBuckets n_max - 1 →
      d.regs regStride = (strideHash θ u).val →
      d.regs regM = numBuckets n_max →
      d.regs regZero = 0 →
      d.regs regU = u.val →
      d.regs regSlot = (probePerm θ u ⟨i, hi_lt⟩).val →
      d.regs regCond = (if probePerm θ u ⟨i, hi_lt⟩ ∈ O then 1 else 0) →
      ∃ d' : Data 16,
        ExecWithin w probeLoop d d' (13 * rem + 2) ∧
        d'.mem = mem ∧
        d'.regs regSlot = (targetSlot (probePerm θ) T u hO).val ∧
        ∀ r : Fin 16, r ≠ regSlot → r ≠ regAddr → r ≠ regCond → d'.regs r = d.regs r := by
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
    have hsp : space c_exp n_max = slotOffset c_exp n_max + 3 * numBuckets n_max := rfl
    have hfit_add : Fits w (slot_i.val + (strideHash θ u).val) := by
      have := slot_i.isLt
      have := (strideHash θ u).isLt
      exact hS.of_le (by omega)
    have hfit_next : Fits w slot_next.val := by
      have := slot_next.isLt
      exact hS.of_le (by omega)
    set s1 := d.set regSlot (slot_i.val + (strideHash θ u).val)
    have e1 : Exec w (.op (.exactBin .add regSlot regSlot regStride) : Code .exact 16) d s1 1 :=
      Exec.alu (by simp +decide [StandardOp.evalExact, hslot, hstride, slot_i]) hfit_add
    set s2 := s1.set regSlot slot_next.val
    have e2 : Exec w (.op (.exactBin .and regSlot regSlot regMaskM) : Code .exact 16) s1 s2 1 := by
      refine Exec.alu ?_ hfit_next
      have hs1_slot : s1.regs regSlot = slot_i.val + (strideHash θ u).val := by
        simp +decide [s1]
      have hs1_mask : s1.regs regMaskM = numBuckets n_max - 1 := by
        simp +decide [s1, hmask]
      change some (s1.regs regSlot &&& s1.regs regMaskM) = some slot_next.val
      rw [hs1_slot, hs1_mask]
      exact congrArg some (val_probePerm_succ θ u hi1_lt).symm
    have hwf_s2 : SlotArrayWF base c_exp U n_max s2.mem := by simpa [s2, s1, hmem] using hwf
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

/-- Deterministic 3-instruction glue between the primary and stride `DoubleTabulation.evalCode`
calls: saves `(primaryHash θ u).val` from `regAddr` into `regSave` and advances `regBase` by
`singleTabSpace c_exp n_max`. -/
def opMidEvalCode (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (.op (.copy regSave regAddr))
  (.seq (.op (.const regAddr (singleTabSpace c_exp n_max)))
        (.op (.exactBin .add regBase regBase regAddr)))

/-- Deterministic 11-instruction glue after the stride `DoubleTabulation.evalCode` call:
restores `regBase = base`, forms `regStride = 2 * regAddr + 1`, restores `regSlot = regSave`,
and initializes `regSlotBase`, `regMaskM`, `regM`, and `regZero`. -/
def opPostEvalCode (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (.op (.const regCond (singleTabSpace c_exp n_max)))
  (.seq (.op (.exactBin .sub regBase regBase regCond))
  (.seq (.op (.const regCond 1))
  (.seq (.op (.exactBin .add regStride regAddr regAddr))
  (.seq (.op (.exactBin .add regStride regStride regCond))
  (.seq (.op (.copy regSlot regSave))
  (.seq (.op (.const regSlotBase (slotOffset c_exp n_max)))
  (.seq (.op (.exactBin .add regSlotBase regBase regSlotBase))
  (.seq (.op (.const regMaskM (numBuckets n_max - 1)))
  (.seq (.op (.const regM (numBuckets n_max)))
        (.op (.const regZero 0)))))))))))

/-- Hash evaluation and probe-register setup `opEvalHashesCode c_exp n_max`: evaluates
`primaryHash θ u` into `regSlot`, `strideHash θ u` into `regStride`, and initializes
`regSlotBase`, `regMaskM`, `regM`, and `regZero`. -/
def opEvalHashesCode (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (.op (.copy regCond regU))
  (.seq ((DoubleTabulation.evalCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)).rename
          dtMap)
  (.seq (opMidEvalCode c_exp n_max)
  (.seq ((DoubleTabulation.evalCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)).rename
          dtMap)
        (opPostEvalCode c_exp n_max))))

/-- Exact deterministic instruction count
`2 * DoubleTabulation.evalSteps (numChars c_exp) (tupleLen c_exp) + 15 = O_{c_exp}(1)` of
`opEvalHashesCode c_exp n_max` (independent of `n_max` and `U`). -/
def hashEvalSteps (c_exp : ℕ) : ℕ :=
  2 * DoubleTabulation.evalSteps (numChars c_exp) (tupleLen c_exp) + 15

theorem opEvalHashesCode_execWithin {w base c_exp U V n_max : ℕ} {θ : Seed c_exp n_max}
    {s : Dictionary.State U} {x : Data 16}
    (hS : Fits w (base + space c_exp n_max))
    (hrep : Rep w base c_exp U V n_max θ s x) (u : Fin U)
    (hu_fit : Fits w u.val) (hu : x.regs regU = u.val) :
    ∃ d : Data 16,
      ExecWithin w (opEvalHashesCode c_exp n_max) x d (hashEvalSteps c_exp) ∧
      d.mem = x.mem ∧
      d.regs regBase = base ∧
      d.regs regSlot = (probePerm θ u ⟨0, numBuckets_pos n_max⟩).val ∧
      d.regs regSlotBase = base + slotOffset c_exp n_max ∧
      d.regs regMaskM = numBuckets n_max - 1 ∧
      d.regs regStride = (strideHash θ u).val ∧
      d.regs regM = numBuckets n_max ∧
      d.regs regZero = 0 ∧
      d.regs regOp = x.regs regOp ∧
      d.regs regU = u.val ∧
      d.regs regV = x.regs regV := by
  obtain ⟨hfit_btab, hfit_b2tab, hfit_powB, _, hfit_powM, hfit_mask_M, hfit_powM1, _, hfit_1⟩ :=
    fits_of_space hS
  have hsp : space c_exp n_max = slotOffset c_exp n_max + 3 * numBuckets n_max := rfl
  have hfit_tab : Fits w (singleTabSpace c_exp n_max) := hfit_btab.of_le (by omega)
  have hfit_base : Fits w base := hfit_btab.of_le (by omega)
  set s1 := x.set regCond u.val
  have e1 : Exec w (.op (.copy regCond regU) : Code .exact 16) x s1 1 := by
    simpa [s1, hu] using (Exec.copy (B := .exact) (w := w) (d := regCond) (s := regU) (x := x))
  have hs1_base : (s1.comap dtMap).regs 0 = base := by
    simpa +decide [s1, dtMap, Data.comap] using hrep.regs_base
  have hs1_key : (s1.comap dtMap).regs 1 = u.val := by
    simp +decide [s1, dtMap, Data.comap]
  obtain ⟨yPrim, hprim_exec, hyPrim_mem, hyPrim_base, hyPrim_key, hyPrim_out⟩ :=
    DoubleTabulation.evalCode_exec u hs1_base hs1_key hrep.primary_rep
      hfit_btab hfit_powB hfit_powM hu_fit
  set s2 := yPrim.extend dtMap s1
  have e2 : Exec w
      ((DoubleTabulation.evalCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)).rename dtMap)
      s1 s2 (DoubleTabulation.evalSteps (numChars c_exp) (tupleLen c_exp)) :=
    hprim_exec.rename injective_dtMap
  have hs2_mem : s2.mem = x.mem := hyPrim_mem
  have hs2_base : s2.regs regBase = base := by
    change (s2.comap dtMap).regs 0 = base
    rw [Data.comap_extend injective_dtMap]
    exact hyPrim_base
  have hs2_cond : s2.regs regCond = u.val := by
    change (s2.comap dtMap).regs 1 = u.val
    rw [Data.comap_extend injective_dtMap]
    exact hyPrim_key
  have hs2_addr : s2.regs regAddr = (primaryHash θ u).val := by
    change (s2.comap dtMap).regs 2 = (primaryHash θ u).val
    rw [Data.comap_extend injective_dtMap]
    rcases θ with ⟨⟨T₁, T₂⟩, _⟩
    exact hyPrim_out
  have hs2_op : s2.regs regOp = x.regs regOp := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_dtMap (by decide))]
    simp +decide [s1]
  have hs2_u : s2.regs regU = u.val := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_dtMap (by decide))]
    simp +decide [s1, hu]
  have hs2_v : s2.regs regV = x.regs regV := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_dtMap (by decide))]
    simp +decide [s1]
  -- Execute opMidEvalCode
  set s3 := s2.set regSave (primaryHash θ u).val
  have e3 : Exec w (.op (.copy regSave regAddr) : Code .exact 16) s2 s3 1 := by
    simpa [s3, hs2_addr] using
      (Exec.copy (B := .exact) (w := w) (d := regSave) (s := regAddr) (x := s2))
  set s4 := s3.set regAddr (singleTabSpace c_exp n_max)
  have e4 : Exec w (.op (.const regAddr (singleTabSpace c_exp n_max)) : Code .exact 16) s3 s4 1 :=
    Exec.const hfit_tab
  set s5 := s4.set regBase (base + singleTabSpace c_exp n_max)
  have e5 : Exec w (.op (.exactBin .add regBase regBase regAddr) : Code .exact 16) s4 s5 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s4, s3, hs2_base]) hfit_btab
  have eMid : Exec w (opMidEvalCode c_exp n_max) s2 s5 3 := e3.seq (e4.seq e5)
  -- Execute stride DoubleTabulation.evalCode
  have hs5_base : (s5.comap dtMap).regs 0 = base + singleTabSpace c_exp n_max := by
    simp +decide [s5, dtMap, Data.comap]
  have hs5_key : (s5.comap dtMap).regs 1 = u.val := by
    simp +decide [s5, s4, s3, dtMap, Data.comap, hs2_cond]
  have hs5_mem : (s5.comap dtMap).mem = x.mem := hs2_mem
  obtain ⟨yStr, hstr_exec, hyStr_mem, hyStr_base, _, hyStr_out⟩ :=
    DoubleTabulation.evalCode_exec u hs5_base hs5_key (hs5_mem ▸ hrep.stride_rep)
      hfit_b2tab hfit_powB hfit_powM1 hu_fit
  set s6 := yStr.extend dtMap s5
  have e6 : Exec w
      ((DoubleTabulation.evalCode (numChars c_exp) (tupleLen c_exp) (charBits n_max)).rename dtMap)
      s5 s6 (DoubleTabulation.evalSteps (numChars c_exp) (tupleLen c_exp)) :=
    hstr_exec.rename injective_dtMap
  have hs6_mem : s6.mem = x.mem := hyStr_mem.trans hs5_mem
  have hs6_base : s6.regs regBase = base + singleTabSpace c_exp n_max := by
    change (s6.comap dtMap).regs 0 = base + singleTabSpace c_exp n_max
    rw [Data.comap_extend injective_dtMap]
    exact hyStr_base
  have hs6_addr : s6.regs regAddr = (rawStrideHash θ u).val := by
    change (s6.comap dtMap).regs 2 = (rawStrideHash θ u).val
    rw [Data.comap_extend injective_dtMap]
    rcases θ with ⟨_, ⟨S₁, S₂⟩⟩
    exact hyStr_out
  have hs6_save : s6.regs regSave = (primaryHash θ u).val := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_dtMap (by decide))]
    simp +decide [s5, s4, s3]
  have hs6_op : s6.regs regOp = x.regs regOp := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_dtMap (by decide))]
    simp +decide [s5, s4, s3, hs2_op]
  have hs6_u : s6.regs regU = u.val := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_dtMap (by decide))]
    simp +decide [s5, s4, s3, hs2_u]
  have hs6_v : s6.regs regV = x.regs regV := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_dtMap (by decide))]
    simp +decide [s5, s4, s3, hs2_v]
  -- Execute opPostEvalCode
  have hraw_lt := two_mul_rawStrideHash_add_one_lt θ u
  have hM_eq : 2 ^ bucketBits n_max = numBuckets n_max := rfl
  have hfit_2raw : Fits w ((rawStrideHash θ u).val + (rawStrideHash θ u).val) :=
    hfit_powM.of_le (by omega)
  have hfit_stride : Fits w ((strideHash θ u).val) :=
    hfit_powM.of_le (by have := (strideHash θ u).isLt; omega)
  have hfit_so : Fits w (slotOffset c_exp n_max) := hS.of_le (by omega)
  have hfit_bso : Fits w (base + slotOffset c_exp n_max) := hS.of_le (by omega)
  have hfit_m : Fits w (numBuckets n_max) := hS.of_le (by omega)
  have hfit_0 : Fits w 0 := hS.of_le (by omega)
  set s7 := s6.set regCond (singleTabSpace c_exp n_max)
  have e7 : Exec w (.op (.const regCond (singleTabSpace c_exp n_max)) : Code .exact 16) s6 s7 1 :=
    Exec.const hfit_tab
  set s8 := s7.set regBase base
  have e8 : Exec w (.op (.exactBin .sub regBase regBase regCond) : Code .exact 16) s7 s8 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s7, hs6_base]) hfit_base
  set s9 := s8.set regCond 1
  have e9 : Exec w (.op (.const regCond 1) : Code .exact 16) s8 s9 1 :=
    Exec.const hfit_1
  set s10 := s9.set regStride ((rawStrideHash θ u).val + (rawStrideHash θ u).val)
  have e10 : Exec w (.op (.exactBin .add regStride regAddr regAddr) : Code .exact 16) s9 s10 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s9, s8, s7, hs6_addr]) hfit_2raw
  set s11 := s10.set regStride (strideHash θ u).val
  have e11 : Exec w (.op (.exactBin .add regStride regStride regCond) : Code .exact 16)
      s10 s11 1 := by
    refine Exec.alu ?_ hfit_stride
    have hval : (rawStrideHash θ u).val + (rawStrideHash θ u).val + 1 = (strideHash θ u).val := by
      rw [val_strideHash]
      omega
    simp +decide [StandardOp.evalExact, s10, s9, hval]
  set s12 := s11.set regSlot (primaryHash θ u).val
  have e12 : Exec w (.op (.copy regSlot regSave) : Code .exact 16) s11 s12 1 := by
    simpa +decide [s12, s11, s10, s9, s8, s7, hs6_save] using
      (Exec.copy (B := .exact) (w := w) (d := regSlot) (s := regSave) (x := s11))
  set s13 := s12.set regSlotBase (slotOffset c_exp n_max)
  have e13 : Exec w (.op (.const regSlotBase (slotOffset c_exp n_max)) : Code .exact 16)
      s12 s13 1 :=
    Exec.const hfit_so
  set s14 := s13.set regSlotBase (base + slotOffset c_exp n_max)
  have e14 : Exec w (.op (.exactBin .add regSlotBase regBase regSlotBase) : Code .exact 16)
      s13 s14 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s13, s12, s11, s10, s9, s8]) hfit_bso
  set s15 := s14.set regMaskM (numBuckets n_max - 1)
  have e15 : Exec w (.op (.const regMaskM (numBuckets n_max - 1)) : Code .exact 16) s14 s15 1 :=
    Exec.const hfit_mask_M
  set s16 := s15.set regM (numBuckets n_max)
  have e16 : Exec w (.op (.const regM (numBuckets n_max)) : Code .exact 16) s15 s16 1 :=
    Exec.const hfit_m
  set s17 := s16.set regZero 0
  have e17 : Exec w (.op (.const regZero 0) : Code .exact 16) s16 s17 1 :=
    Exec.const hfit_0
  have ePost : Exec w (opPostEvalCode c_exp n_max) s6 s17 11 :=
    e7.seq (e8.seq (e9.seq (e10.seq (e11.seq
      (e12.seq (e13.seq (e14.seq (e15.seq (e16.seq e17)))))))))
  have eAll : ExecWithin w (opEvalHashesCode c_exp n_max) x s17 (hashEvalSteps c_exp) := by
    refine (e1.within.seq (e2.within.seq (eMid.within.seq (e6.within.seq ePost.within)))).mono ?_
    dsimp only [hashEvalSteps]
    omega
  refine ⟨s17, eAll, hs6_mem,
    by simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8],
    by rw [probePerm_zero]; simp +decide [s17, s16, s15, s14, s13, s12],
    by simp +decide [s17, s16, s15, s14],
    by simp +decide [s17, s16, s15],
    by simp +decide [s17, s16, s15, s14, s13, s12, s11],
    by simp +decide [s17, s16],
    by simp +decide [s17],
    by simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, hs6_op],
    by simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, hs6_u],
    by simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, hs6_v]⟩

/-- Lookup completion program `finishGetCode` (`≤ 9` instructions): inspects `used[regSlot]`;
if `0`, writes `0` (`none`) into `regOp`, and if `1`, loads `val[regSlot]` and writes
`val[regSlot] + 1` (`some v`) into `regOp`. -/
def finishGetCode : Code .exact 16 :=
  .seq (.op (.exactBin .add regAddr regSlotBase regSlot))
  (.seq (.op (.load regCond regAddr))
        (.branch (.eq regCond regZero)
          (.op (.const regOp 0))
          (.seq (.op (.exactBin .add regAddr regAddr regM))
          (.seq (.op (.exactBin .add regAddr regAddr regM))
          (.seq (.op (.load regOp regAddr))
          (.seq (.op (.const regCond 1))
                (.op (.exactBin .add regOp regOp regCond))))))))

theorem finishGetCode_execWithin {w base c_exp U V n_max : ℕ} {θ : Seed c_exp n_max}
    {s : Dictionary.State U} {x d : Data 16}
    (hS : Fits w (base + space c_exp n_max)) (hV : Fits w V)
    (hrep : Rep w base c_exp U V n_max θ s x)
    (u : Fin U)
    (hO : (otherOccupiedSlots (extractSlots base c_exp U n_max x.mem) u).card < numBuckets n_max)
    (hmem : d.mem = x.mem)
    (hbase : d.regs regBase = base)
    (hsbase : d.regs regSlotBase = base + slotOffset c_exp n_max)
    (hslot : d.regs regSlot =
      (targetSlot (probePerm θ) (extractSlots base c_exp U n_max x.mem) u hO).val)
    (hm : d.regs regM = numBuckets n_max)
    (hzero : d.regs regZero = 0) :
    ∃ y : Data 16,
      ExecWithin w finishGetCode d y 9 ∧
      y.mem = x.mem ∧
      y.regs regBase = base ∧
      y.regs regOp = (match s u with | none => 0 | some v => v + 1) := by
  let T := extractSlots base c_exp U n_max x.mem
  let slot := targetSlot (probePerm θ) T u hO
  have hslot_lt := slot.isLt
  have hsp : space c_exp n_max = slotOffset c_exp n_max + 3 * numBuckets n_max := rfl
  have hfit_0 : Fits w 0 := hS.of_le (by omega)
  have hfit_1 : Fits w 1 := hS.of_le (by omega)
  let sBase := base + slotOffset c_exp n_max
  let m := numBuckets n_max
  have hfit_a0 : Fits w (sBase + slot.val) := hS.of_le (by omega)
  have hfit_a1 : Fits w (sBase + slot.val + m) := hS.of_le (by omega)
  have hfit_a2 : Fits w (sBase + slot.val + m + m) := hS.of_le (by omega)
  set s1 := d.set regAddr (sBase + slot.val)
  have e1 : Exec w (.op (.exactBin .add regAddr regSlotBase regSlot) : Code .exact 16) d s1 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, hsbase, hslot, sBase, slot, T]) hfit_a0
  let usedVal := x.mem (sBase + slot.val)
  set s2 := s1.set regCond usedVal
  have e2 : Exec w (.op (.load regCond regAddr) : Code .exact 16) s1 s2 1 := by
    simpa +decide [s2, s1, hmem, usedVal] using
      (Exec.load (B := .exact) (w := w) (d := regCond) (a := regAddr) (x := s1))
  have htarget := hrep.table_rep.toTableRep.apply_targetSlot u hO
  cases hsu : s u with
  | none =>
    have hT_none : extractSlots base c_exp U n_max x.mem slot = none := by
      simpa [slot, T, hsu] using htarget
    have hused0 : usedVal = 0 := (extractSlots_eq_none_iff hrep.slot_wf slot).mp hT_none
    have hc : (Cond.eq regCond regZero).Holds s2 := by
      simp +decide [Cond.Holds, s2, s1, hused0, hzero]
    set s3 := s2.set regOp 0
    have e3 : Exec w (.op (.const regOp 0) : Code .exact 16) s2 s3 1 := Exec.const hfit_0
    refine ⟨s3,
      (e1.within.seq (e2.within.seq (ExecWithin.branch_pos hc e3.within))).mono (by omega),
      hmem, by simp +decide [s3, s2, s1, hbase], by simp +decide [s3]⟩
  | some v =>
    have hT_some : extractSlots base c_exp U n_max x.mem slot = some (u, v) := by
      simpa [slot, T, hsu] using htarget
    obtain ⟨hused1, _, hval_eq⟩ := (extractSlots_eq_some_iff hrep.slot_wf slot u v).mp hT_some
    have hv_lt : v < V := hrep.vals_bounded u v hsu
    have hfit_v1 : Fits w (v + 1) := hV.of_le (by omega)
    have hc : ¬(Cond.eq regCond regZero).Holds s2 := by
      simp +decide [Cond.Holds, s2, s1, usedVal, sBase, hused1, hzero]
    set s3 := s2.set regAddr (sBase + slot.val + m)
    have e3 : Exec w (.op (.exactBin .add regAddr regAddr regM) : Code .exact 16) s2 s3 1 :=
      Exec.alu (by simp +decide [StandardOp.evalExact, s2, s1, hm, m]) hfit_a1
    set s4 := s3.set regAddr (sBase + slot.val + m + m)
    have e4 : Exec w (.op (.exactBin .add regAddr regAddr regM) : Code .exact 16) s3 s4 1 :=
      Exec.alu (by simp +decide [StandardOp.evalExact, s3, s2, s1, hm, m]) hfit_a2
    have haddr2_eq :
        sBase + slot.val + m + m =
          base + slotOffset c_exp n_max + 2 * numBuckets n_max + slot.val := by
      dsimp only [sBase, m]
      omega
    set s5 := s4.set regOp v
    have e5 : Exec w (.op (.load regOp regAddr) : Code .exact 16) s4 s5 1 := by
      simpa +decide [s5, s4, s3, s2, s1, hmem, haddr2_eq, hval_eq] using
        (Exec.load (B := .exact) (w := w) (d := regOp) (a := regAddr) (x := s4))
    set s6 := s5.set regCond 1
    have e6 : Exec w (.op (.const regCond 1) : Code .exact 16) s5 s6 1 := Exec.const hfit_1
    set s7 := s6.set regOp (v + 1)
    have e7 : Exec w (.op (.exactBin .add regOp regOp regCond) : Code .exact 16) s6 s7 1 :=
      Exec.alu (by simp +decide [StandardOp.evalExact, s6, s5]) hfit_v1
    refine ⟨s7,
      (e1.within.seq (e2.within.seq
        (ExecWithin.branch_neg hc
          (e3.within.seq (e4.within.seq (e5.within.seq (e6.within.seq e7.within))))))).mono
        (by omega),
      hmem, by simp +decide [s7, s6, s5, s4, s3, s2, s1, hbase], by simp +decide [s7]⟩

/-- Insertion completion program `finishInsertCode` (`8` instructions): writes `used[regSlot] := 1`,
`key[regSlot] := regU`, `val[regSlot] := regV`, and sets `regOp := 0`. -/
def finishInsertCode : Code .exact 16 :=
  .seq (.op (.exactBin .add regAddr regSlotBase regSlot))
  (.seq (.op (.const regCond 1))
  (.seq (.op (.store regAddr regCond))
  (.seq (.op (.exactBin .add regAddr regAddr regM))
  (.seq (.op (.store regAddr regU))
  (.seq (.op (.exactBin .add regAddr regAddr regM))
  (.seq (.op (.store regAddr regV))
        (.op (.const regOp 0))))))))

theorem finishInsertCode_execWithin {w base c_exp U V n_max : ℕ} {θ : Seed c_exp n_max}
    {s : Dictionary.State U} {x d : Data 16}
    (hS : Fits w (base + space c_exp n_max))
    (hrep : Rep w base c_exp U V n_max θ s x)
    (u : Fin U) (v : ℕ)
    (hvalid : ((Dictionary.spec U V n_max).valid s (.insert u v)))
    (hO : (otherOccupiedSlots (extractSlots base c_exp U n_max x.mem) u).card < numBuckets n_max)
    (hmem : d.mem = x.mem)
    (hbase : d.regs regBase = base)
    (hsbase : d.regs regSlotBase = base + slotOffset c_exp n_max)
    (hslot : d.regs regSlot =
      (targetSlot (probePerm θ) (extractSlots base c_exp U n_max x.mem) u hO).val)
    (hm : d.regs regM = numBuckets n_max)
    (hu : d.regs regU = u.val)
    (hv : d.regs regV = v) :
    ∃ y : Data 16,
      ExecWithin w finishInsertCode d y 8 ∧
      y.regs regBase = base ∧
      y.regs regOp = 0 ∧
      DoubleTabulation.SeedRep base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
        (bucketBits n_max) θ.1 y.mem ∧
      DoubleTabulation.SeedRep (base + singleTabSpace c_exp n_max) (numChars c_exp) (tupleLen c_exp)
        (charBits n_max) (bucketBits n_max - 1) θ.2 y.mem ∧
      SlotArrayWF base c_exp U n_max y.mem ∧
      DoubleHashing.OrderedTableRep (probePerm θ) (Function.update s u (some v))
        (extractSlots base c_exp U n_max y.mem) ∧
      (Dictionary.dom (Function.update s u (some v))).card ≤ n_max ∧
      Dictionary.ValuesBounded V (Function.update s u (some v)) ∧
      Modifies (Block.mk base (space c_exp n_max)).footprint x.mem y.mem := by
  let T := extractSlots base c_exp U n_max x.mem
  let slot := targetSlot (probePerm θ) T u hO
  have hslot_lt := slot.isLt
  have hsp : space c_exp n_max = slotOffset c_exp n_max + 3 * numBuckets n_max := rfl
  have hso : slotOffset c_exp n_max = 2 * singleTabSpace c_exp n_max := rfl
  have hfit_0 : Fits w 0 := hS.of_le (by omega)
  have hfit_1 : Fits w 1 := hS.of_le (by omega)
  let sBase := base + slotOffset c_exp n_max
  let m := numBuckets n_max
  have hfit_a0 : Fits w (sBase + slot.val) := hS.of_le (by omega)
  have hfit_a1 : Fits w (sBase + slot.val + m) := hS.of_le (by omega)
  have hfit_a2 : Fits w (sBase + slot.val + m + m) := hS.of_le (by omega)
  have ha1_eq : sBase + slot.val + m = sBase + m + slot.val := by omega
  have ha2_eq : sBase + slot.val + m + m = sBase + 2 * m + slot.val := by omega
  set s1 := d.set regAddr (sBase + slot.val)
  have e1 : Exec w (.op (.exactBin .add regAddr regSlotBase regSlot) : Code .exact 16) d s1 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, hsbase, hslot, sBase, slot, T]) hfit_a0
  set s2 := s1.set regCond 1
  have e2 : Exec w (.op (.const regCond 1) : Code .exact 16) s1 s2 1 := Exec.const hfit_1
  set s3 := s2.write (sBase + slot.val) 1
  have e3 : Exec w (.op (.store regAddr regCond) : Code .exact 16) s2 s3 1 := by
    simpa +decide [s3, s2, s1] using
      (Exec.store (B := .exact) (w := w) (a := regAddr) (s := regCond) (x := s2))
  set s4 := s3.set regAddr (sBase + slot.val + m)
  have e4 : Exec w (.op (.exactBin .add regAddr regAddr regM) : Code .exact 16) s3 s4 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s3, s2, s1, hm, m]) hfit_a1
  set s5 := s4.write (sBase + m + slot.val) u.val
  have e5 : Exec w (.op (.store regAddr regU) : Code .exact 16) s4 s5 1 := by
    simpa +decide [s5, s4, s3, s2, s1, ha1_eq, hu] using
      (Exec.store (B := .exact) (w := w) (a := regAddr) (s := regU) (x := s4))
  set s6 := s5.set regAddr (sBase + slot.val + m + m)
  have e6 : Exec w (.op (.exactBin .add regAddr regAddr regM) : Code .exact 16) s5 s6 1 :=
    Exec.alu (by simp +decide [StandardOp.evalExact, s5, s4, s3, s2, s1, hm, m]) hfit_a2
  set s7 := s6.write (sBase + 2 * m + slot.val) v
  have e7 : Exec w (.op (.store regAddr regV) : Code .exact 16) s6 s7 1 := by
    simpa +decide [s7, s6, s5, s4, s3, s2, s1, ha2_eq, hv] using
      (Exec.store (B := .exact) (w := w) (a := regAddr) (s := regV) (x := s6))
  set s8 := s7.set regOp 0
  have e8 : Exec w (.op (.const regOp 0) : Code .exact 16) s7 s8 1 := Exec.const hfit_0
  have eAll := (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))).within
  have hs8_mem_below : ∀ a < sBase, s8.mem a = x.mem a := by
    intro a ha
    have hne0 : a ≠ sBase + slot.val := by omega
    have hne1 : a ≠ sBase + m + slot.val := by omega
    have hne2 : a ≠ sBase + 2 * m + slot.val := by omega
    simp [s8, s7, s6, s5, s4, s3, s2, s1, Data.write,
      Function.update_of_ne hne0, Function.update_of_ne hne1, Function.update_of_ne hne2, hmem]
  have hprim : DoubleTabulation.SeedRep base (numChars c_exp) (tupleLen c_exp) (charBits n_max)
      (bucketBits n_max) θ.1 s8.mem :=
    hrep.primary_rep.congr_mem fun a _ hhi => hs8_mem_below a (by
      change a < base + 2 * singleTabSpace c_exp n_max
      change a < base + singleTabSpace c_exp n_max at hhi
      omega)
  have hstr : DoubleTabulation.SeedRep (base + singleTabSpace c_exp n_max) (numChars c_exp)
      (tupleLen c_exp) (charBits n_max) (bucketBits n_max - 1) θ.2 s8.mem :=
    hrep.stride_rep.congr_mem fun a _ hhi => hs8_mem_below a (by
      change a < base + 2 * singleTabSpace c_exp n_max
      change a < base + singleTabSpace c_exp n_max + singleTabSpace c_exp n_max at hhi
      omega)
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
  have hwf : SlotArrayWF base c_exp U n_max s8.mem := by
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
  have hext : extractSlots base c_exp U n_max s8.mem =
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
      change extractSlots base c_exp U n_max s8.mem j = extractSlots base c_exp U n_max x.mem j
      dsimp only [extractSlots]
      rw [show base + slotOffset c_exp n_max + j.val = sBase + j.val from rfl,
        show base + slotOffset c_exp n_max + numBuckets n_max + j.val = sBase + m + j.val from rfl,
        show base + slotOffset c_exp n_max + 2 * numBuckets n_max + j.val =
          sBase + 2 * m + j.val from rfl,
        h0, h1, h2]
  have htrep : DoubleHashing.OrderedTableRep (probePerm θ) (Function.update s u (some v))
      (extractSlots base c_exp U n_max s8.mem) := by
    rw [hext]
    exact hrep.table_rep.tableInsert (numBuckets_pos n_max) u v hO
  have hdom_le : (Dictionary.dom (Function.update s u (some v))).card ≤ n_max :=
    Dictionary.card_dom_step_le_of_valid (V := V) hrep.dom_le (o := .insert u v) hvalid
  have hvals : Dictionary.ValuesBounded V (Function.update s u (some v)) :=
    Dictionary.valuesBounded_step_of_valid (n_max := n_max) hrep.vals_bounded
      (o := .insert u v) hvalid
  have hmod : Modifies (Block.mk base (space c_exp n_max)).footprint x.mem s8.mem := by
    intro a ha
    have ha_out : a < base ∨ base + space c_exp n_max ≤ a := by
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
    hprim, hstr, hwf, htrep, hdom_le, hvals, hmod⟩

/-- Complete operation body `opCode c_exp n_max` for both `get` and `insert`. -/
def opCode (c_exp n_max : ℕ) : Code .exact 16 :=
  .seq (opEvalHashesCode c_exp n_max)
  (.seq probeCheckCode
  (.seq probeLoop
        (.branch (.eq regOp regZero) finishGetCode finishInsertCode)))

/-- Exact pathwise instruction budget
`13 * probeCount T u (probePerm θ u) + hashEvalSteps c_exp + 8` for `opCode c_exp n_max` on table
`T` and key `u`. -/
noncomputable def opPathSteps (c_exp U n_max : ℕ) (θ : Seed c_exp n_max)
    (T : UniformProbing.Table U (numBuckets n_max)) (u : Fin U) : ℕ :=
  13 * probeCount T u (probePerm θ u) + hashEvalSteps c_exp + 8

/-- Worst-case instruction bound `13 * numBuckets n_max + hashEvalSteps c_exp + 8` for
`opCode`. -/
def opSteps (c_exp n_max : ℕ) : ℕ :=
  13 * numBuckets n_max + hashEvalSteps c_exp + 8

theorem opPathSteps_le_opSteps {c_exp U n_max : ℕ} (θ : Seed c_exp n_max)
    (T : UniformProbing.Table U (numBuckets n_max)) (u : Fin U)
    (hO : (otherOccupiedSlots T u).card < numBuckets n_max) :
    opPathSteps c_exp U n_max θ T u ≤ opSteps c_exp n_max := by
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

/-- **Pathwise correctness and complexity of `opCode c_exp n_max`**: for any seed `θ`, dictionary
state `s`, machine state `x` satisfying `Rep w base c_exp U V n_max θ s x`, and admissible operation
`op`, `opCode c_exp n_max` halts deterministically in at most
`opPathSteps c_exp U n_max θ (extractSlots base c_exp U n_max x.mem) (opKey op)`
`≤ opSteps c_exp n_max` instructions, preserving `Rep` for
`((Dictionary.spec U V n_max).stepFn s op).1`, writing `opOutWord s op` into `regOp`, and modifying
memory only within `[base, base + space c_exp n_max)`. -/
theorem opCode_execWithin {w base c_exp U V n_max : ℕ} {θ : Seed c_exp n_max}
    {s : Dictionary.State U} {x : Data 16}
    (hS : Fits w (base + space c_exp n_max)) (hV : Fits w V)
    (hrep : Rep w base c_exp U V n_max θ s x) (op : Dictionary.Op U)
    (hvalid : (Dictionary.spec U V n_max).valid s op)
    (hu_fit : Fits w (opKey op).val)
    (hop : x.regs regOp = opTag op)
    (hu : x.regs regU = (opKey op).val)
    (hv : ∀ u v, op = .insert u v → x.regs regV = v) :
    ∃ y : Data 16,
      ExecWithin w (opCode c_exp n_max) x y
        (opPathSteps c_exp U n_max θ (extractSlots base c_exp U n_max x.mem) (opKey op)) ∧
      Rep w base c_exp U V n_max θ ((Dictionary.spec U V n_max).stepFn s op).1 y ∧
      y.regs regOp = opOutWord s op ∧
      Modifies (Block.mk base (space c_exp n_max)).footprint x.mem y.mem := by
  have hO :
      (otherOccupiedSlots (extractSlots base c_exp U n_max x.mem) (opKey op)).card <
        numBuckets n_max :=
    lt_of_le_of_lt (hrep.table_rep.toTableRep.card_otherOccupiedSlots_le (opKey op))
      (lt_of_le_of_lt hrep.dom_le (lt_numBuckets n_max))
  obtain ⟨d1, e1, hd1_mem, hd1_base, hd1_slot, hd1_sbase, hd1_mask, hd1_stride, hd1_m,
      hd1_zero, hd1_op, hd1_u, hd1_v⟩ :=
    opEvalHashesCode_execWithin hS hrep (opKey op) hu_fit hu
  have hwf_d1 : SlotArrayWF base c_exp U n_max d1.mem := by simpa [hd1_mem] using hrep.slot_wf
  obtain ⟨d2, e2, hd2_mem, hd2_cond, hd2_regs⟩ :=
    probeCheckCode_execWithin hS hwf_d1 (opKey op)
      (probePerm θ (opKey op) ⟨0, numBuckets_pos n_max⟩)
      hd1_sbase hd1_slot hd1_m hd1_zero hd1_u
  have hd2_mem_eq : d2.mem = x.mem := hd2_mem.trans hd1_mem
  have hd2_cond' : d2.regs regCond =
      (if probePerm θ (opKey op) ⟨0, numBuckets_pos n_max⟩ ∈
          otherOccupiedSlots (extractSlots base c_exp U n_max x.mem) (opKey op) then 1 else 0) := by
    rw [hd1_mem] at hd2_cond
    exact hd2_cond
  obtain ⟨d3, e3, hd3_mem, hd3_slot, hd3_regs⟩ :=
    probeLoop_execWithin_aux θ hS hrep.slot_wf (opKey op) hO
      (missedProbes (otherOccupiedSlots (extractSlots base c_exp U n_max x.mem) (opKey op))
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
  have hd3_sbase : d3.regs regSlotBase = base + slotOffset c_exp n_max := by
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
    have eTot : ExecWithin w (opCode c_exp n_max) x y
        (opPathSteps c_exp U n_max θ (extractSlots base c_exp U n_max x.mem) u₀) := by
      refine (e1.seq (e2.seq (e3.seq eBr))).mono ?_
      dsimp only [opPathSteps, probeCount, unsuccessfulProbes, opKey] at *
      omega
    have hbdd_y : y.Bounded w := eTot.bounded hrep.bounded
    have hrep_y : Rep w base c_exp U V n_max θ s y :=
      hrep.congr hbdd_y (hy_base.trans hrep.regs_base.symm) (fun a _ => by rw [hy_mem])
    have hmod : Modifies (Block.mk base (space c_exp n_max)).footprint x.mem y.mem := by
      intro a _
      rw [hy_mem]
    exact ⟨y, eTot, hrep_y, hy_op, hmod⟩
  | insert u₀ v₀ =>
    have hc : ¬(Cond.eq regOp regZero).Holds d3 := by
      simp [Cond.Holds, hd3_op, hd3_zero, opTag]
    have hd3_v₀ : d3.regs regV = v₀ := hd3_v.trans (hv u₀ v₀ rfl)
    obtain ⟨y, eFin, hy_base, hy_op, hy_prim, hy_str, hy_wf, hy_trep, hy_dom, hy_vals, hy_mod⟩ :=
      finishInsertCode_execWithin hS hrep u₀ v₀ hvalid hO
        hd3_mem hd3_base hd3_sbase hd3_slot hd3_m hd3_u hd3_v₀
    have eBr : ExecWithin w (.branch (.eq regOp regZero) finishGetCode finishInsertCode) d3 y 10 :=
      ExecWithin.branch_neg hc eFin
    have eTot : ExecWithin w (opCode c_exp n_max) x y
        (opPathSteps c_exp U n_max θ (extractSlots base c_exp U n_max x.mem) u₀) := by
      refine (e1.seq (e2.seq (e3.seq eBr))).mono ?_
      dsimp only [opPathSteps, probeCount, unsuccessfulProbes, opKey] at *
      omega
    have hbdd_y : y.Bounded w := eTot.bounded hrep.bounded
    exact ⟨y, eTot,
      ⟨hbdd_y, hy_base, hy_prim, hy_str, hy_wf, hy_trep, hy_dom, hy_vals⟩,
      hy_op, hy_mod⟩

/-! ## Section 5: `SubroutineCode`, `SubroutineDS`, and Expected Probe / Collision Bounds -/

/-- Relocatable `SubroutineCode` over `Basis.exact` (`16` registers, `0` runtime init parameters)
for the open-addressed permutation-probing dictionary. -/
def subroutineCode (c_exp n_max : ℕ) : SubroutineCode .exact 16 0 where
  allocSpan := allocSpan c_exp n_max
  initSetup := initSetup c_exp n_max
  code := opCode c_exp n_max
  frontierReg := regV
  baseReg := regBase
  initParams := Fin.elim0
  curReg := regCond
  zeroReg := regAddr
  oneReg := regSlot
  incCur := .exactBin .add regCond regCond regSlot
  input := fun i => decide (i ≠ regBase)
  output := regOp

/-- Standalone argument encoder for `Dictionary.Op U` on `16` registers. -/
def encodeOp {U : ℕ} : Dictionary.Op U → Fin 16 → ℕ
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
def argMatch {U : ℕ} (op : Dictionary.Op U) (regs : Fin 16 → ℕ) : Prop :=
  regs regOp = opTag op ∧
  regs regU = (opKey op).val ∧
  ∀ u v, op = .insert u v → regs regV = v

/-- Output decoder reading typed operation observations from final registers. -/
def decodeOp {U V n_max : ℕ} : (op : Dictionary.Op U) → (Fin 16 → ℕ) →
    Option ((Dictionary.spec U V n_max).Result op)
  | .get _, regs => some (if regs regOp = 0 then none else some (regs regOp - 1))
  | .insert _ _, _ => some ()

theorem encode_matches {c_exp U n_max : ℕ} (op : Dictionary.Op U) (regs : Fin 16 → ℕ) :
    argMatch op
      (fun i => if (subroutineCode c_exp n_max).input i then encodeOp op i else regs i) := by
  cases op with
  | get u =>
    refine ⟨rfl, ?_, fun _ _ h => by nomatch h⟩
    simp +decide [subroutineCode, encodeOp, opKey]
  | insert u v =>
    refine ⟨rfl, ?_, fun u' v' h => ?_⟩
    · simp +decide [subroutineCode, encodeOp, opKey]
    · cases h
      simp +decide [subroutineCode, encodeOp]

theorem arguments_fit {w base c_exp U V n_max : ℕ}
    (hS : Fits w (base + space c_exp n_max))
    (hU_fit : ∀ u : Fin U, Fits w u.val)
    (hV : Fits w V)
    {s : Dictionary.State U} (op : Dictionary.Op U)
    (hv : (Dictionary.spec U V n_max).valid s op)
    (i : Fin 16) :
    Fits w (encodeOp op i) := by
  have hfit0 : Fits w 0 := fits_zero w
  have hfit1 : Fits w 1 := (fits_of_space hS).2.2.2.2.2.2.2.2
  cases op with
  | get u =>
    dsimp only [encodeOp]
    split_ifs
    · exact hfit0
    · exact hU_fit u
    · exact hfit0
  | insert u v =>
    dsimp only [encodeOp]
    split_ifs
    · exact hfit1
    · exact hU_fit u
    · exact hV.of_le (by have := hv.2; omega)
    · exact hfit0

theorem decodeOp_eq_step {U V n_max : ℕ} {s : Dictionary.State U}
    (op : Dictionary.Op U) (regs : Fin 16 → ℕ)
    (h : regs regOp = opOutWord s op) :
    decodeOp (V := V) (n_max := n_max) op regs =
      some ((Dictionary.spec U V n_max).stepFn s op).2 := by
  cases op with
  | get u =>
    dsimp only [decodeOp, Dictionary.spec, Dictionary.step, Stateful.Spec.stepFn, opOutWord] at h ⊢
    rw [h]
    cases s u with
    | none => simp
    | some v => simp
  | insert u v =>
    rfl

/-- Expected per-operation instruction charge
`13 * doubleTabThreshold c_exp + hashEvalSteps c_exp + 8 = O_{c_exp}(1)` for both `get` and `insert`
(independent of `n_max` and `U`). -/
def expectedOpCharge (c_exp : ℕ) : ℕ :=
  13 * doubleTabThreshold c_exp + hashEvalSteps c_exp + 8

private noncomputable instance instDecidableExistsOrderedTableProbe {U n_max : ℕ}
    (π : Fin U → Equiv.Perm (Fin (numBuckets n_max)))
    (s : Dictionary.State U) (u : Fin U) :
    DecidablePred (fun k : ℕ =>
      ∃ T : UniformProbing.Table U (numBuckets n_max),
        DoubleHashing.OrderedTableRep π s T ∧ probeCount T u (π u) = k) :=
  Classical.decPred _

private theorem maxOrderedProbe_nonempty {U n_max : ℕ}
    (π : Fin U → Equiv.Perm (Fin (numBuckets n_max)))
    (s : Dictionary.State U) (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    ((Finset.range (n_max + 2)).filter (fun k : ℕ =>
      ∃ T : UniformProbing.Table U (numBuckets n_max),
        DoubleHashing.OrderedTableRep π s T ∧ probeCount T u (π u) = k)).Nonempty := by
  obtain ⟨T₀, hrep₀⟩ := DoubleHashing.exists_orderedTableRep π s
    (le_of_lt (lt_of_le_of_lt hdom (lt_numBuckets n_max)))
  have hle : probeCount T₀ u (π u) ≤ n_max + 1 :=
    probeCount_le_add_one hrep₀.toTableRep hdom u
  exact ⟨probeCount T₀ u (π u),
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), T₀, hrep₀, rfl⟩⟩

private noncomputable def maxOrderedTable {U n_max : ℕ}
    (π : Fin U → Equiv.Perm (Fin (numBuckets n_max)))
    (s : Dictionary.State U) (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    UniformProbing.Table U (numBuckets n_max) :=
  let S := (Finset.range (n_max + 2)).filter (fun k : ℕ =>
    ∃ T : UniformProbing.Table U (numBuckets n_max),
      DoubleHashing.OrderedTableRep π s T ∧ probeCount T u (π u) = k)
  have hmax := (Finset.mem_filter.mp (Finset.max'_mem S (maxOrderedProbe_nonempty π s hdom u))).2
  Classical.choose hmax

private theorem orderedTableRep_maxOrderedTable {U n_max : ℕ}
    (π : Fin U → Equiv.Perm (Fin (numBuckets n_max)))
    (s : Dictionary.State U) (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    DoubleHashing.OrderedTableRep π s (maxOrderedTable π s hdom u) := by
  let S := (Finset.range (n_max + 2)).filter (fun k : ℕ =>
    ∃ T : UniformProbing.Table U (numBuckets n_max),
      DoubleHashing.OrderedTableRep π s T ∧ probeCount T u (π u) = k)
  have hmax := (Finset.mem_filter.mp (Finset.max'_mem S (maxOrderedProbe_nonempty π s hdom u))).2
  exact (Classical.choose_spec hmax).1

private theorem probeCount_le_maxOrderedTable {U n_max : ℕ}
    (π : Fin U → Equiv.Perm (Fin (numBuckets n_max)))
    {s : Dictionary.State U} (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U)
    {T : UniformProbing.Table U (numBuckets n_max)}
    (hrep : DoubleHashing.OrderedTableRep π s T) :
    probeCount T u (π u) ≤ probeCount (maxOrderedTable π s hdom u) u (π u) := by
  let S := (Finset.range (n_max + 2)).filter (fun k : ℕ =>
    ∃ T' : UniformProbing.Table U (numBuckets n_max),
      DoubleHashing.OrderedTableRep π s T' ∧ probeCount T' u (π u) = k)
  have hne := maxOrderedProbe_nonempty π s hdom u
  have hmax := (Finset.mem_filter.mp (Finset.max'_mem S hne)).2
  have heq : probeCount (maxOrderedTable π s hdom u) u (π u) = S.max' hne :=
    (Classical.choose_spec hmax).2
  rw [heq]
  have hle : probeCount T u (π u) ≤ n_max + 1 :=
    probeCount_le_add_one hrep.toTableRep hdom u
  exact Finset.le_max' S (probeCount T u (π u))
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), T, hrep, rfl⟩)

private theorem tsum_probeCount_le {α : Type*} {c_exp U n_max : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp)
    {s : Dictionary.State U} (u : Fin U)
    (ν : PMF (Seed c_exp n_max × α))
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ seedLaw c_exp n_max θ)
    (T_probe : Seed c_exp n_max × α → ℕ)
    (hT : ∀ p ∈ ν.support,
      (Dictionary.dom s).card ≤ n_max ∧
      ∃ T : UniformProbing.Table U (numBuckets n_max),
        DoubleHashing.OrderedTableRep (probePerm p.1) s T ∧
        T_probe p ≤ probeCount T u (probePerm p.1 u)) :
    (∑' p, ν p * (T_probe p : ℝ≥0∞)) ≤ (doubleTabThreshold c_exp : ℝ≥0∞) := by
  obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
  have hdom : (Dictionary.dom s).card ≤ n_max := (hT p₀ hp₀).1
  let T_max : Seed c_exp n_max → UniformProbing.Table U (numBuckets n_max) :=
    fun θ => maxOrderedTable (probePerm θ) s hdom u
  have hpt : ∀ p, ν p * (T_probe p : ℝ≥0∞) ≤
      ν p * (probeCount (T_max p.1) u (probePerm p.1 u) : ℝ≥0∞) := by
    intro p
    by_cases hp : p ∈ ν.support
    · obtain ⟨_, T, hrep_T, hle⟩ := hT p hp
      have hle_max := probeCount_le_maxOrderedTable (probePerm p.1) hdom u hrep_T
      gcongr
      exact hle.trans hle_max
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul, zero_mul]
  have hbound_unif := DoubleHashing.expect_probeCount_oddStride_unconditional_le
    hU (thirtyTwo_mul_max_le_numBuckets n_max)
    (fun θ => orderedTableRep_maxOrderedTable (probePerm θ) s hdom u) hdom u
  have hmax_eq : max (doubleTabThreshold c_exp : ℝ≥0∞) 3 = (doubleTabThreshold c_exp : ℝ≥0∞) := by
    apply max_eq_left
    have h4 := four_le_doubleTabThreshold c_exp
    exact_mod_cast (by omega : 3 ≤ doubleTabThreshold c_exp)
  rw [hmax_eq] at hbound_unif
  calc (∑' p, ν p * (T_probe p : ℝ≥0∞))
      ≤ ∑' p, ν p * (probeCount (T_max p.1) u (probePerm p.1 u) : ℝ≥0∞) :=
        tsum_le_tsum hpt
    _ = ∑' θ, (ν.map Prod.fst) θ * (probeCount (T_max θ) u (probePerm θ u) : ℝ≥0∞) :=
        (Cslib.Probability.PMF.tsum_map_mul ν Prod.fst
          (fun θ => (probeCount (T_max θ) u (probePerm θ u) : ℝ≥0∞))).symm
    _ ≤ ∑' θ, seedLaw c_exp n_max θ * (probeCount (T_max θ) u (probePerm θ u) : ℝ≥0∞) :=
        tsum_le_tsum (fun θ => mul_le_mul_of_nonneg_right (hseed θ) zero_le)
    _ ≤ (doubleTabThreshold c_exp : ℝ≥0∞) := hbound_unif

theorem step_exec_spec {w base c_exp U V n_max : ℕ}
    (hS : Fits w (base + space c_exp n_max))
    (hU_fit : ∀ u : Fin U, Fits w u.val) (hV : Fits w V)
    (hU : U ≤ max n_max 4 ^ c_exp)
    {s : Dictionary.State U} (o : Dictionary.Op U)
    (ν : PMF (Seed c_exp n_max × Data 16))
    (hv : (Dictionary.spec U V n_max).valid s o)
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ 1 * seedLaw c_exp n_max θ)
    (hsupp : ∀ p ∈ ν.support, Rep w base c_exp U V n_max p.1 s p.2 ∧ argMatch o p.2.regs) :
    ∃ (μ_step : Seed c_exp n_max × Data 16 → PMF (Seed c_exp n_max × Data 16))
      (T_step : Seed c_exp n_max × Data 16 → ℝ≥0∞),
      (∀ p ∈ ν.support,
        ExecCodeDist w (opCode c_exp n_max) p.2 ((μ_step p).map Prod.snd) (T_step p) ∧
        ∀ q ∈ (μ_step p).support,
          decodeOp (V := V) (n_max := n_max) o q.2.regs =
            some ((Dictionary.spec U V n_max).stepFn s o).2 ∧
          Rep w base c_exp U V n_max q.1 ((Dictionary.spec U V n_max).stepFn s o).1 q.2 ∧
          Modifies (Block.mk base (space c_exp n_max)).footprint p.2.mem q.2.mem) ∧
      (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ 1 * seedLaw c_exp n_max θ') ∧
      (∑' p, ν p * (T_step p + ∑' q, μ_step p q * ((0 : ℕ) : ℝ≥0∞))) ≤
        (expectedOpCharge c_exp : ℝ≥0∞) + ∑' p, ν p * ((0 : ℕ) : ℝ≥0∞) := by
  classical
  let T_probe : Seed c_exp n_max × Data 16 → ℕ := fun p =>
    if p ∈ ν.support then
      probeCount (extractSlots base c_exp U n_max p.2.mem) (opKey o) (probePerm p.1 (opKey o))
    else 0
  let T_step : Seed c_exp n_max × Data 16 → ℝ≥0∞ := fun p =>
    ((13 * T_probe p + hashEvalSteps c_exp + 8 : ℕ) : ℝ≥0∞)
  have hEx : ∀ p : Seed c_exp n_max × Data 16, ∃ y : Data 16,
      p ∈ ν.support →
        ExecWithin w (opCode c_exp n_max) p.2 y
          (13 * T_probe p + hashEvalSteps c_exp + 8) ∧
        Rep w base c_exp U V n_max p.1 ((Dictionary.spec U V n_max).stepFn s o).1 y ∧
        y.regs regOp = opOutWord s o ∧
        Modifies (Block.mk base (space c_exp n_max)).footprint p.2.mem y.mem := by
    intro p
    by_cases hp : p ∈ ν.support
    · obtain ⟨hrep, harg1, harg2, harg3⟩ := hsupp p hp
      obtain ⟨y, e, hrep_y, hout, hmod⟩ :=
        opCode_execWithin hS hV hrep o hv (hU_fit (opKey o)) harg1 harg2 harg3
      have hTp : 13 * T_probe p + hashEvalSteps c_exp + 8 =
          opPathSteps c_exp U n_max p.1 (extractSlots base c_exp U n_max p.2.mem) (opKey o) := by
        dsimp only [T_probe, opPathSteps]
        simp only [hp, ↓reduceIte]
      exact ⟨y, fun _ => ⟨hTp ▸ e, hrep_y, hout, hmod⟩⟩
    · exact ⟨p.2, fun h => False.elim (hp h)⟩
  let yOf : Seed c_exp n_max × Data 16 → Data 16 := fun p => Classical.choose (hEx p)
  refine ⟨fun p => PMF.pure (p.1, yOf p), T_step, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨e, hrep_y, hout, hmod⟩ := Classical.choose_spec (hEx p) hp
    refine ⟨?_, ?_⟩
    · simpa [yOf, T_step] using ExecCodeDist.of_execWithin e
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
  · simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero]
    have hseed' : ∀ θ, (ν.map Prod.fst) θ ≤ seedLaw c_exp n_max θ := by
      intro θ
      simpa only [one_mul] using hseed θ
    have hprobe_le : (∑' p, ν p * (T_probe p : ℝ≥0∞)) ≤ (doubleTabThreshold c_exp : ℝ≥0∞) := by
      refine tsum_probeCount_le (s := s) hU (opKey o) ν hseed' T_probe ?_
      intro p hp
      obtain ⟨hrep, _⟩ := hsupp p hp
      refine ⟨hrep.dom_le, extractSlots base c_exp U n_max p.2.mem, hrep.table_rep, ?_⟩
      dsimp only [T_probe]
      simp only [hp, ↓reduceIte, le_rfl]
    have hterm : ∀ p, ν p * T_step p =
        13 * (ν p * (T_probe p : ℝ≥0∞)) + ν p * (hashEvalSteps c_exp + 8 : ℝ≥0∞) := by
      intro p
      dsimp only [T_step]
      push_cast
      ring
    simp_rw [hterm]
    rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
    calc 13 * (∑' p, ν p * (T_probe p : ℝ≥0∞)) + (hashEvalSteps c_exp + 8 : ℝ≥0∞)
        ≤ 13 * (doubleTabThreshold c_exp : ℝ≥0∞) + (hashEvalSteps c_exp + 8 : ℝ≥0∞) := by
          gcongr
      _ = (expectedOpCharge c_exp : ℝ≥0∞) := by
          dsimp only [expectedOpCharge]
          push_cast
          ring

/-- **Composable randomized Word-RAM `SubroutineDS` certificate over `Basis.exact`** for the
open-addressed odd-stride double-hashing dictionary realizing `Dictionary.spec U V n_max` with
$O_{c_{\exp}}(1)$ expected operation time (`expectedOpCharge c_exp`) and
$O_{c_{\exp}}(n_{\max} + 1)$ space (`space c_exp n_max`) for every `n_max : ℕ` whenever
`U ≤ max n_max 4 ^ c_exp`. -/
noncomputable abbrev subroutineDS {w base c_exp U V n_max : ℕ}
    (hS : Fits w (base + space c_exp n_max))
    (hU_fit : ∀ u : Fin U, Fits w u.val) (hV : Fits w V)
    (hU : U ≤ max n_max 4 ^ c_exp) :
    Randomized.SubroutineDS (subroutineCode c_exp n_max)
      (Dictionary.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  Randomized.SubroutineDS.ofFn
    (Seed := Seed c_exp n_max)
    (seedLaw := seedLaw c_exp n_max)
    (seedSlack := 1)
    (space := space c_exp n_max)
    (spanTime := 3)
    (setupTime := (setupSteps c_exp n_max : ℝ≥0∞))
    (initPotential := 0)
    (charge := fun _ _ => expectedOpCharge c_exp)
    (rep := Rep w base c_exp U V n_max)
    (potential := fun _ _ => 0)
    (encode := encodeOp)
    (argMatch := argMatch)
    (decode := decodeOp)
    (bounded := fun hrep => hrep.bounded)
    (arguments_fit := fun o hv i _ => arguments_fit hS hU_fit hV o hv i)
    (encode_matches := encode_matches)
    (rep_supported := fun {θ s x x'} hregs hmem hbdd hrep => by
      have hbase : x'.regs regBase = x.regs regBase := hregs regBase rfl
      exact hrep.congr hbdd hbase hmem)
    (potential_supported := fun _ _ _ => rfl)
    (clear_nodup := by
      dsimp only [subroutineCode]
      decide)
    (params_not_clear := fun j => Fin.elim0 j)
    (incCur_eval := fun {x} h1 hfit => by
      dsimp only [subroutineCode] at h1 hfit ⊢
      simp [Op.exactBin, Op.eval, StandardOp.evalExact, Data.put, h1, hfit])
    (span_exec := fun {x} _ hfr _ => by
      obtain ⟨x₁, he, hm, hb, hfr'⟩ := allocSpan_execWithin hS hfr
      exact ⟨x₁, he, hm, hb, hfr', fun j => Fin.elim0 j⟩)
    (setup_exec := fun {x₁} hx₁ hb hfr _ hz =>
      setup_exec_spec hS hx₁ hb hfr hz)
    (step_exec := fun {s} o ν hv hseed hsupp =>
      step_exec_spec hS hU_fit hV hU o ν hv hseed hsupp)

/-- Standard-basis (`Basis.standard`) randomized `SubroutineDS` certificate for the open-addressed
odd-stride double-hashing dictionary. -/
noncomputable abbrev subroutineDSStandard {w base c_exp U V n_max : ℕ}
    (hS : Fits w (base + space c_exp n_max))
    (hU_fit : ∀ u : Fin U, Fits w u.val) (hV : Fits w V)
    (hU : U ≤ max n_max 4 ^ c_exp) :
    Randomized.SubroutineDS (subroutineCode c_exp n_max).toStandard
      (Dictionary.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  (subroutineDS hS hU_fit hV hU).toStandard

/-- **End-to-end multi-operation expected-time theorem (`seq_expected_amortized`)**:
from fresh zeroed memory `[base, base + space c_exp n_max)`, initializing the odd-stride
double-hashing dictionary (`initFresh`) and executing the subroutine operation bodies
(`ExecStepsOfFn`) across any admissible operation history `ops : List (Dictionary.Op U)` fixed
independently of the sampled seed (oblivious adversary) takes at most
`3 + setupSteps c_exp n_max + ops.length * expectedOpCharge c_exp` expected Word-RAM instructions
(charging the $O_{c_{\exp}}(1)$ expected bound `expectedOpCharge c_exp` per operation for every
`n_max : ℕ` whenever `U ≤ max n_max 4 ^ c_exp`). -/
theorem seq_expected_amortized {w base c_exp U V n_max : ℕ}
    (hS : Fits w (base + space c_exp n_max))
    (hU_fit : ∀ u : Fin U, Fits w u.val) (hV : Fits w V)
    (hU : U ≤ max n_max 4 ^ c_exp)
    {x : Data 16} (ops : List (Dictionary.Op U))
    (hx : x.Bounded w) (hfr : x.regs regV = base)
    (hz : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, x.mem a = 0)
    (hv : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    ∃ (ν₀ ν_final : PMF (Seed c_exp n_max × Data 16)) (T_ops : ℝ≥0∞),
      ExecCodeDist w (subroutineCode c_exp n_max).initFresh x (ν₀.map Prod.snd)
        (subroutineDS (V := V) hS hU_fit hV hU).initTime ∧
      (subroutineDS (V := V) hS hU_fit hV hU).ExecStepsOfFn (Dictionary.empty U) ops ν₀ ν_final
        T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ seedLaw c_exp n_max θ) ∧
      (∀ p ∈ ν_final.support,
        Rep w base c_exp U V n_max p.1
          ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1 p.2) ∧
      (subroutineDS (V := V) hS hU_fit hV hU).initTime + T_ops ≤
        (3 + setupSteps c_exp n_max : ℝ≥0∞) +
          ((Dictionary.spec U V n_max).totalCost (fun _ _ => expectedOpCharge c_exp)
            (Dictionary.empty U) ops : ℝ≥0∞) := by
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hrep_final, hbound⟩ :=
    (subroutineDS (V := V) hS hU_fit hV hU).seq_expected_amortized_ofFn ops hx hfr
      (fun j => Fin.elim0 j) hz hv
  refine ⟨ν₀, ν_final, T_ops, he_init, hex_steps, ?_, hrep_final, ?_⟩
  · intro θ
    have h1 : (ν_final.map Prod.fst) θ ≤ 1 * seedLaw c_exp n_max θ := hseed_final θ
    rwa [one_mul] at h1
  · have hinit : (subroutineDS (V := V) hS hU_fit hV hU).initTime =
        (3 + setupSteps c_exp n_max : ℝ≥0∞) := rfl
    rw [hinit]
    have h2 : (3 + (setupSteps c_exp n_max : ℝ≥0∞)) + T_ops +
        ∑' q : Seed c_exp n_max × Data 16, ν_final q * ((0 : ℕ) : ℝ≥0∞) ≤
        (3 + (setupSteps c_exp n_max : ℝ≥0∞)) + ((0 : ℕ) : ℝ≥0∞) +
          ((Dictionary.spec U V n_max).totalCost (fun _ _ => expectedOpCharge c_exp)
            (Dictionary.empty U) ops : ℝ≥0∞) := hbound
    simpa only [Nat.cast_zero, mul_zero, tsum_zero, add_zero, Nat.cast_add, Nat.cast_ofNat] using h2

/-- **Parametric expected-step bound from any expected-probe bound**:
for any permutation distribution `μ : PMF α` and family
`π : α → Equiv.Perm (Fin (numBuckets n_max))` whose expected probe count on table `T` and key `u`
is at most `B`, the expected Word-RAM instruction count of the probe path is at most
`13 * B + (hashEvalSteps c_exp + 8)`. -/
theorem expect_opPathSteps_le_of_probeBound {α : Type*} {c_exp U n_max : ℕ}
    (μ : PMF α) (π : α → Equiv.Perm (Fin (numBuckets n_max)))
    (T : Fin (numBuckets n_max) → Option (Fin U × ℕ)) (u : Fin U) (B : ℝ≥0∞)
    (hB : (∑' a, μ a * (UniformProbing.probeCount T u (π a) : ℝ≥0∞)) ≤ B) :
    (∑' a, μ a *
      ((13 * UniformProbing.probeCount T u (π a) + hashEvalSteps c_exp + 8 : ℕ) : ℝ≥0∞)) ≤
      13 * B + (hashEvalSteps c_exp + 8 : ℝ≥0∞) := by
  have hterm : ∀ a : α,
      μ a * ((13 * UniformProbing.probeCount T u (π a) + hashEvalSteps c_exp + 8 : ℕ) : ℝ≥0∞) =
        13 * (μ a * (UniformProbing.probeCount T u (π a) : ℝ≥0∞)) +
          μ a * (hashEvalSteps c_exp + 8 : ℝ≥0∞) := by
    intro a
    push_cast
    ring
  simp_rw [hterm]
  rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
  gcongr

/-- **Ideal uniform-probing expected-step corollary (`≤ hashEvalSteps c_exp + 34`)**:
when the probe permutation `π` is drawn uniformly from `Equiv.Perm (Fin (numBuckets n_max))` on a
table `T` with at most `n_max` other occupied slots (`(otherOccupiedSlots T u).card ≤ n_max`), the
expected Word-RAM step count `13 * probeCount T u π + hashEvalSteps c_exp + 8` is at most
`hashEvalSteps c_exp + 34` (combining `expect_opPathSteps_le_of_probeBound` with `B = 2` from
`UniformProbing.expect_unsuccessfulProbes_le_two`). -/
theorem expect_idealProbeSteps_le {c_exp U n_max : ℕ}
    (T : Fin (numBuckets n_max) → Option (Fin U × ℕ)) (u : Fin U)
    (hcard : (UniformProbing.otherOccupiedSlots T u).card ≤ n_max) :
    (∑' π : Equiv.Perm (Fin (numBuckets n_max)),
      (PMF.uniformOfFintype (Equiv.Perm (Fin (numBuckets n_max)))) π *
        ((13 * UniformProbing.probeCount T u π + hashEvalSteps c_exp + 8 : ℕ) : ℝ≥0∞)) ≤
      (hashEvalSteps c_exp + 34 : ℝ≥0∞) := by
  have h2m : 2 * (UniformProbing.otherOccupiedSlots T u).card ≤ numBuckets n_max := by
    have h4 := four_mul_le_numBuckets n_max
    omega
  have hB : (∑' π : Equiv.Perm (Fin (numBuckets n_max)),
      (PMF.uniformOfFintype (Equiv.Perm (Fin (numBuckets n_max)))) π *
        (UniformProbing.probeCount T u π : ℝ≥0∞)) ≤ 2 :=
    UniformProbing.expect_unsuccessfulProbes_le_two (numBuckets_pos n_max) h2m
  have hstep := expect_opPathSteps_le_of_probeBound (c_exp := c_exp) (U := U) (n_max := n_max)
    (PMF.uniformOfFintype (Equiv.Perm (Fin (numBuckets n_max)))) id T u 2 hB
  refine hstep.trans ?_
  have heq : (13 : ℝ≥0∞) * 2 + (hashEvalSteps c_exp + 8 : ℝ≥0∞) =
      (hashEvalSteps c_exp + 34 : ℝ≥0∞) := by
    ring
  exact le_of_eq heq

end Cslib.Algorithms.WordRAM.Dictionary.UniformProbing
