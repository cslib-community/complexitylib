/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.GenericRAM.Native.IndexFold
public import Complexity.Foundations.Combinatorics.SubsetPairCount
public import Complexity.Foundations.Data.BitString.Support
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Size

/-!
# Combinatorial subset-pair unranking and streaming folds

For Boolean Möbius reconstruction of low-degree polynomials ([OpenAI2026ETH], Lemma 3.3, eq. (3.10)
and Proposition 3.4, pp. 24–26), the outer loop visits all subset pairs `(E, U)` of `Fin n` with
`#E ≤ q` and `U ⊆ E`, weighted by `(-1) ^ (#E - #U)`, in `C_q = ∑ s ≤ min q n, 2 ^ s * n.choose s`
steps without materializing exponentially many subsets.

## Main definitions

* `Cslib.GenericRAM.SubsetPairFold.pascalTable`, `Cslib.GenericRAM.SubsetPairFold.subsetPairCount`:
  dynamic-programming Pascal table and executable count `C_q`.
* `Cslib.GenericRAM.SubsetPairFold.DecodedPair`, `Cslib.GenericRAM.SubsetPairFold.unrankSubsetPair`,
  `Cslib.GenericRAM.SubsetPairFold.ValidSubsetPair`,
  `Cslib.GenericRAM.SubsetPairFold.unrankValidSubsetPair`,
  `Cslib.GenericRAM.SubsetPairFold.validSubsetPairEquiv`: `(E, U)` unranker and bijection (via
  `Cslib.BitString.supportOfList`).
* `Cslib.GenericRAM.SubsetPairFold.pascalTableCertificate`,
  `Cslib.GenericRAM.SubsetPairFold.subsetPairCountCertificate`,
  `Cslib.GenericRAM.SubsetPairFold.unrankSubsetPairCertificate`,
  `Cslib.GenericRAM.SubsetPairFold.indexBody`, `Cslib.GenericRAM.SubsetPairFold.runPrefix`,
  `Cslib.GenericRAM.SubsetPairFold.run`, `Cslib.GenericRAM.SubsetPairFold.certificate`: native
  resource certificates and streaming fold built on `Cslib.GenericRAM.IndexFold.run`.

## Main results

* `Cslib.GenericRAM.SubsetPairFold.getD_pascalTable_eq_choose`,
  `Cslib.GenericRAM.SubsetPairFold.length_encNat_mem_pascalTable_le`,
  `Cslib.GenericRAM.SubsetPairFold.subsetPairCount_eq_sum`,
  `Cslib.GenericRAM.SubsetPairFold.subsetPairCount_eq`,
  `Cslib.GenericRAM.SubsetPairFold.subsetPairCount_pos`,
  `Cslib.GenericRAM.SubsetPairFold.subsetPairCount_le_three_pow`,
  `Cslib.GenericRAM.SubsetPairFold.length_encNat_subsetPairCount_le`: DP table, `C_q` refinement
  with `Cslib.subsetPairCount`, and binary-length bounds.
* `Cslib.GenericRAM.SubsetPairFold.bijective_unrankValidSubsetPair`,
  `Cslib.GenericRAM.SubsetPairFold.nodup_map_unrankSubsetPair`,
  `Cslib.GenericRAM.SubsetPairFold.existsUnique_unrankSubsetPair`,
  `Cslib.GenericRAM.SubsetPairFold.pascalTable_polyTime`,
  `Cslib.GenericRAM.SubsetPairFold.subsetPairCount_polyTime`,
  `Cslib.GenericRAM.SubsetPairFold.unrankSubsetPair_polyTime`: bijection and `fun_prop` polytime.
* `Cslib.GenericRAM.SubsetPairFold.run_eq_foldl_map`,
  `Cslib.GenericRAM.SubsetPairFold.run_mobius_eq_sum_restricted_subsets`,
  `Cslib.GenericRAM.SubsetPairFold.computableInO`,
  `Cslib.GenericRAM.SubsetPairFold.polyBounded_space_of_polyBounded`: streaming fold and space.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 3.4 (Lemma 3.3,
  eq. (3.10)) and Section 3.5 (eq. (3.14) and Proposition 3.4), printed pp. 24–26.
-/

@[expose] public section

namespace Cslib.GenericRAM.SubsetPairFold

open scoped BigOperators
open Turing.MultiTapeTM Cslib.BitString

namespace Internal

/-- Append one dynamic-programming Pascal row of width `width` to `rows`. -/
def pascalStep (width : ℕ) (rows : List (List ℕ)) : List (List ℕ) :=
  let prev := rows.reverse.headD []
  rows ++ [(List.range width).map fun s =>
    if s == 0 then 1 else prev.getD (s - 1) 0 + prev.getD s 0]

/-- One step of scanning bucket capacities `2 ^ s * C(n, s)` for `s = 0, …, min q n`. -/
def bucketStep (rowN : List ℕ) (state : ℕ × Option (ℕ × ℕ)) (s : ℕ) : ℕ × Option (ℕ × ℕ) :=
  if state.2.isSome then state else
    let cap := 2 ^ s * rowN.getD s 0
    if state.1 < cap then (state.1, some (s, state.1)) else (state.1 - cap, none)

/-- Locate `(s, offset)` for `j < C_q`, or `none` when `j ≥ C_q`. -/
def findBucket (n q j : ℕ) (table : List (List ℕ)) : Option (ℕ × ℕ) :=
  ((List.range (min q n + 1)).foldl (bucketStep (table.getD n [])) (j, none)).2

/-- One step of combinatorial unranking of rank `r < C(n, k)` into an `n`-bit indicator. -/
def unrankCombStep (table : List (List ℕ)) (state : (ℕ × ℕ) × List Bool) (m : ℕ) :
    (ℕ × ℕ) × List Bool :=
  let c := (table.getD m []).getD state.1.1 0
  if state.1.2 < c then ((state.1.1, state.1.2), state.2 ++ [false])
  else ((state.1.1 - 1, state.1.2 - c), state.2 ++ [true])

/-- Unrank `r < C(n, k)` using `table = pascalTable n` into a length-`n` weight-`k` bit list. -/
def unrankComb (n k r : ℕ) (table : List (List ℕ)) : List Bool :=
  ((List.range n).reverse.foldl (unrankCombStep table) ((k, r), [])).2

/-- One step of scattering low-order bits of `uMask` onto the `true` entries of `indE`. -/
def scatterStep (state : ℕ × List Bool) (bitE : Bool) : ℕ × List Bool :=
  if bitE then (state.1 / 2, state.2 ++ [state.1.testBit 0]) else (state.1, state.2 ++ [false])

/-- Scatter the bits of `uMask` across the `true` positions of `indE`. -/
def scatterMask (indE : List Bool) (uMask : ℕ) : List Bool :=
  (indE.foldl scatterStep (uMask, [])).2

end Internal

/-! ## Section 1: Dynamic-programming Pascal table and exact binary clock `C_q` -/

/-- Dynamic-programming `(n + 1) × (n + 1)` Pascal table of `i.choose s` by row addition. -/
def pascalTable (n : ℕ) : List (List ℕ) :=
  (Internal.pascalStep (n + 1))^[n] [1 :: List.replicate n 0]

private theorem pascalStep_iterate_spec (n k : ℕ) :
    let rows := (Internal.pascalStep (n + 1))^[k] [1 :: List.replicate n 0]
    rows.length = k + 1 ∧ rows.reverse.headD [] = rows.getD k [] ∧
      ∀ i (hi : i < rows.length), rows[i].length = n + 1 ∧
        ∀ s (hs : s < rows[i].length), rows[i][s] = i.choose s := by
  induction k with
  | zero =>
    refine ⟨rfl, rfl, fun i hi => ?_⟩
    simp only [Function.iterate_zero_apply, List.length_singleton, Nat.lt_one_iff] at hi; subst hi
    refine ⟨by simp, fun s hs => ?_⟩
    cases s with
    | zero => simp
    | succ s =>
      simp only [Function.iterate_zero_apply, List.getElem_cons_zero, List.length_cons,
        List.length_replicate, Nat.add_lt_add_iff_right] at hs ⊢; simp
  | succ k ih =>
    rcases ih with ⟨hlen, hlast, hrows⟩
    set prevRows := (Internal.pascalStep (n + 1))^[k] [1 :: List.replicate n 0]
    set nextRow := (List.range (n + 1)).map fun s =>
      if s == 0 then 1 else (prevRows.getD k []).getD (s - 1) 0 + (prevRows.getD k []).getD s 0
    have hstep : (Internal.pascalStep (n + 1))^[k + 1] [1 :: List.replicate n 0] =
        prevRows ++ [nextRow] := by
      rw [Function.iterate_succ_apply', Internal.pascalStep]; simp only [hlast, prevRows, nextRow]
    have hk_lt : k < prevRows.length := by omega
    have hprev_k : prevRows.getD k [] = prevRows[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt, Option.getD_some]
    have hk_row := hrows k hk_lt; have hnext_len : nextRow.length = n + 1 := by simp [nextRow]
    have hnext_entry : ∀ s (hs : s < nextRow.length), nextRow[s] = (k + 1).choose s := by
      intro s hs; simp only [nextRow, List.getElem_map, List.getElem_range]
      cases s with
      | zero => simp
      | succ s =>
        have hs1 : s < prevRows[k].length := by omega
        have hs2 : s + 1 < prevRows[k].length := by omega
        simp only [beq_iff_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          Nat.add_sub_cancel, hprev_k, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs1,
          List.getElem?_eq_getElem hs2, Option.getD_some, hk_row.2 s hs1, hk_row.2 (s + 1) hs2,
          Nat.choose_succ_succ]
    refine ⟨by simp only [hstep, List.length_append, hlen, List.length_singleton], ?_, ?_⟩
    · simp only [hstep, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.headD_cons, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]; simp [hlen]
    · simp only [hstep]; intro i hi
      simp only [List.length_append, hlen, List.length_singleton] at hi
      by_cases hik : i < k + 1
      · have hi_prev : i < prevRows.length := by omega
        simpa only [List.getElem_append_left hi_prev] using hrows i hi_prev
      · have hik_eq : i = k + 1 := by omega
        subst hik_eq
        have hget : (prevRows ++ [nextRow])[k + 1]'(by simp [hlen]) = nextRow := by
          rw [List.getElem_append_right (by omega)]; simp [hlen]
        exact ⟨by rw [hget, hnext_len],
          fun s hs => by simpa only [hget] using hnext_entry s (by simpa only [hget] using hs)⟩

/-- `pascalTable n` has `n + 1` rows. -/
@[simp] theorem length_pascalTable (n : ℕ) : (pascalTable n).length = n + 1 :=
  (pascalStep_iterate_spec n n).1

/-- In-bounds lookup in `pascalTable n` returns `i.choose s`. -/
theorem getElem_pascalTable_eq_choose {n i s : ℕ} (hi : i < (pascalTable n).length)
    (hs : s < (pascalTable n)[i].length) : (pascalTable n)[i][s] = i.choose s :=
  ((pascalStep_iterate_spec n n).2.2 i hi).2 s hs

/-- Defaulted lookup in row `i ≤ n` of `pascalTable n` equals `i.choose s` for every `s : ℕ`. -/
theorem getD_pascalTable_eq_choose {n i : ℕ} (hi : i ≤ n) (s : ℕ) :
    ((pascalTable n).getD i []).getD s 0 = i.choose s := by
  have hi_lt : i < (pascalTable n).length := by simp only [length_pascalTable]; omega
  have hrow : (pascalTable n).getD i [] = (pascalTable n)[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_lt, Option.getD_some]
  have hrow_len : (pascalTable n)[i].length = n + 1 := ((pascalStep_iterate_spec n n).2.2 i hi_lt).1
  rw [hrow]
  by_cases hs : s ≤ n
  · have hs_lt : s < (pascalTable n)[i].length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs_lt, Option.getD_some]
    exact getElem_pascalTable_eq_choose hi_lt hs_lt
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
      Nat.choose_eq_zero_of_lt (by omega)]

/-- Every binomial coefficient `i.choose s` for `i ≤ n` has binary length at most `n + 1`. -/
theorem length_encNat_choose_le {n i : ℕ} (hi : i ≤ n) (s : ℕ) :
    (encNat (i.choose s)).length ≤ n + 1 := by
  rw [encNat_apply, Nat.size_eq_bits_len]; refine Nat.size_le.mpr ?_
  have hle : i.choose s ≤ 2 ^ i := by
    by_cases hs : s ≤ i
    · rw [← Nat.sum_range_choose i]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; exact Nat.zero_le _
  have := Nat.two_pow_pos i; have hlt : i.choose s < 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
  exact hlt.trans_le (Nat.pow_le_pow_right (by omega) (by omega))

/-- Every entry stored in `pascalTable n` has binary encoding length at most `n + 1`. -/
theorem length_encNat_mem_pascalTable_le {n : ℕ} {row : List ℕ} {x : ℕ}
    (hrow : row ∈ pascalTable n) (hx : x ∈ row) : (encNat x).length ≤ n + 1 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow; obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hx
  rw [getElem_pascalTable_eq_choose hi hs]
  exact length_encNat_choose_le (by simp only [length_pascalTable] at hi; omega) s

/-- Executable subset-pair count `C_q = ∑ s ≤ min q n, 2 ^ s * n.choose s` ([OpenAI2026ETH]). -/
def subsetPairCount (n q : ℕ) : ℕ :=
  let row := (pascalTable n).getD n []
  ((List.range (min q n + 1)).map fun s => 2 ^ s * row.getD s 0).sum

/-- `subsetPairCount n q` equals `∑ s ∈ Finset.range (min q n + 1), 2 ^ s * n.choose s`. -/
theorem subsetPairCount_eq_sum (n q : ℕ) :
    subsetPairCount n q = ∑ s ∈ Finset.range (min q n + 1), 2 ^ s * n.choose s := by
  dsimp only [subsetPairCount]
  rw [List.map_congr_left fun s _ => by rw [getD_pascalTable_eq_choose le_rfl],
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

/-- Refinement equality equating the DP `subsetPairCount` to `Cslib.subsetPairCount`. -/
theorem subsetPairCount_eq (n q : ℕ) : subsetPairCount n q = Cslib.subsetPairCount n q :=
  subsetPairCount_eq_sum n q

/-- `subsetPairCount n q` is strictly positive for all `n, q` (since `(∅, ∅)` is always valid). -/
theorem subsetPairCount_pos (n q : ℕ) : 0 < subsetPairCount n q :=
  subsetPairCount_eq n q ▸ Cslib.subsetPairCount_pos n q

/-- When `n ≤ q`, `subsetPairCount n q = 3 ^ n` ([OpenAI2026ETH], eq. (3.14)). -/
theorem subsetPairCount_eq_three_pow_of_le {n q : ℕ} (h : n ≤ q) : subsetPairCount n q = 3 ^ n :=
  subsetPairCount_eq n q ▸ Cslib.subsetPairCount_eq_three_pow h

/-- `subsetPairCount n q ≤ 3 ^ n` for all `n, q : ℕ`. -/
theorem subsetPairCount_le_three_pow (n q : ℕ) : subsetPairCount n q ≤ 3 ^ n :=
  subsetPairCount_eq n q ▸ Cslib.subsetPairCount_le_three_pow n q

/-- The binary index bound `subsetPairCount n q` occupies at most `2 * n + 1` bits in `encNat`. -/
theorem length_encNat_subsetPairCount_le (n q : ℕ) :
    (encNat (subsetPairCount n q)).length ≤ 2 * n + 1 := by
  have h3 : 3 ^ n < 2 ^ (2 * n + 1) := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [Nat.pow_succ, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, Nat.pow_add]
      change 3 ^ n * 3 < 2 ^ (2 * n + 1) * 4; omega
  rw [encNat_apply, Nat.size_eq_bits_len]
  exact Nat.size_le.mpr ((subsetPairCount_le_three_pow n q).trans_lt h3)

/-! ## Section 2: Polynomial-time combinatorial `(E, U)` unranker and bijection -/

/-- Decoded `(indE, indU, negSign)` triple: length-`n` indicators and `Odd (#E - #U)` flag. -/
abbrev DecodedPair : Type := List Bool × List Bool × Bool

/-- Combinatorial `(E, U)` unranker: decodes `j < subsetPairCount n q` into `(indE, indU, negSign)`
without materializing subsets, with deterministic empty-pair fallback for `j ≥ C_q`. -/
def unrankSubsetPair (n q j : ℕ) : DecodedPair :=
  let table := pascalTable n
  (Internal.findBucket n q j table).elim
    (List.replicate n false, List.replicate n false, false) fun bo =>
      let indE := Internal.unrankComb n bo.1 (bo.2 / 2 ^ bo.1) table
      let indU := Internal.scatterMask indE (bo.2 % 2 ^ bo.1)
      (indE, indU, (indE.count true - indU.count true) % 2 == 1)

private theorem foldl_bucketStep_spec (rowN : List ℕ) (m j : ℕ) :
    let res := (List.range m).foldl (Internal.bucketStep rowN) (j, none)
    if j < ∑ s ∈ Finset.range m, 2 ^ s * rowN.getD s 0 then
      ∃ s offset, res = (offset, some (s, offset)) ∧ s < m ∧ offset < 2 ^ s * rowN.getD s 0 ∧
        j = (∑ t ∈ Finset.range s, 2 ^ t * rowN.getD t 0) + offset
    else res = (j - ∑ s ∈ Finset.range m, 2 ^ s * rowN.getD s 0, none) := by
  induction m with
  | zero => simp
  | succ m ih =>
    dsimp only at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ]
    set S := ∑ s ∈ Finset.range m, 2 ^ s * rowN.getD s 0
    by_cases hjm : j < S
    · simp only [hjm, ↓reduceIte] at ih; obtain ⟨s, offset, hres, hs_lt, hoff_lt, hj_eq⟩ := ih
      have hjm' : j < S + 2 ^ m * rowN.getD m 0 := by omega
      simp only [hjm', ↓reduceIte, hres, Internal.bucketStep, Option.isSome_some]
      exact ⟨s, offset, rfl, by omega, hoff_lt, hj_eq⟩
    · simp only [hjm, ↓reduceIte] at ih; rw [ih]
      by_cases hjm' : j < S + 2 ^ m * rowN.getD m 0
      · have hlt : j - S < 2 ^ m * rowN.getD m 0 := by omega
        simp only [hjm', ↓reduceIte, Internal.bucketStep, Option.isSome_none, Bool.false_eq_true,
          hlt]
        exact ⟨m, j - S, rfl, by omega, hlt, by omega⟩
      · have hge : ¬(j - S < 2 ^ m * rowN.getD m 0) := by omega
        simp only [hjm', ↓reduceIte, Internal.bucketStep, Option.isSome_none, Bool.false_eq_true,
          hge]
        exact Prod.ext (by omega) rfl

private theorem sum_pascalRow_eq (n k : ℕ) :
    (∑ s ∈ Finset.range k, 2 ^ s * ((pascalTable n).getD n []).getD s 0) =
      ∑ s ∈ Finset.range k, 2 ^ s * n.choose s :=
  Finset.sum_congr rfl fun s _ => by rw [getD_pascalTable_eq_choose le_rfl]

private theorem findBucket_of_lt {n q j : ℕ} (hj : j < subsetPairCount n q) :
    ∃ s offset, Internal.findBucket n q j (pascalTable n) = some (s, offset) ∧
      s ≤ min q n ∧ offset < 2 ^ s * n.choose s ∧
      j = (∑ t ∈ Finset.range s, 2 ^ t * n.choose t) + offset := by
  have hspec := foldl_bucketStep_spec ((pascalTable n).getD n []) (min q n + 1) j
  dsimp only at hspec; rw [sum_pascalRow_eq, ← subsetPairCount_eq_sum] at hspec
  simp only [hj, ↓reduceIte] at hspec
  obtain ⟨s, offset, hres, hs_lt, hoff_lt, hj_eq⟩ := hspec
  rw [getD_pascalTable_eq_choose le_rfl] at hoff_lt; rw [sum_pascalRow_eq] at hj_eq
  exact ⟨s, offset, by simp only [Internal.findBucket, hres], by omega, hoff_lt, hj_eq⟩

private theorem findBucket_of_le {n q j : ℕ} (hj : subsetPairCount n q ≤ j) :
    Internal.findBucket n q j (pascalTable n) = none := by
  have hspec := foldl_bucketStep_spec ((pascalTable n).getD n []) (min q n + 1) j
  dsimp only at hspec; rw [sum_pascalRow_eq, ← subsetPairCount_eq_sum] at hspec
  have hnot : ¬(j < subsetPairCount n q) := by omega
  simp only [hnot, ↓reduceIte] at hspec; simp only [Internal.findBucket, hspec]

private def pureUnrankComb : ℕ → ℕ → ℕ → List Bool
  | 0, _, _ => []
  | m + 1, k, r =>
    if r < m.choose k then false :: pureUnrankComb m k r
    else true :: pureUnrankComb m (k - 1) (r - m.choose k)

private theorem foldl_unrankCombStep_eq {N m : ℕ} (hm : m ≤ N) (k r : ℕ) (acc : List Bool) :
    ((List.range m).reverse.foldl (Internal.unrankCombStep (pascalTable N)) ((k, r), acc)).2 =
      acc ++ pureUnrankComb m k r := by
  induction m generalizing k r acc with
  | zero => simp [pureUnrankComb]
  | succ m ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.foldl_cons, pureUnrankComb]
    have hm_le : m ≤ N := by omega
    simp only [Internal.unrankCombStep, getD_pascalTable_eq_choose hm_le k]; split_ifs
    · rw [ih hm_le k r (acc ++ [false]), List.append_assoc, List.singleton_append]
    · rw [ih hm_le (k - 1) (r - m.choose k) (acc ++ [true]), List.append_assoc,
        List.singleton_append]

private theorem unrankComb_eq_pure (n k r : ℕ) :
    Internal.unrankComb n k r (pascalTable n) = pureUnrankComb n k r := by
  simpa only [Internal.unrankComb, List.nil_append] using foldl_unrankCombStep_eq le_rfl k r []

private theorem length_pureUnrankComb (m k r : ℕ) : (pureUnrankComb m k r).length = m := by
  induction m generalizing k r with
  | zero => rfl
  | succ m ih => simp only [pureUnrankComb]; split_ifs <;> simp [ih]

private theorem count_true_pureUnrankComb {m k r : ℕ} (hr : r < m.choose k) :
    (pureUnrankComb m k r).count true = k := by
  induction m generalizing k r with
  | zero => cases k with | zero => rfl | succ k => simp at hr
  | succ m ih =>
    simp only [pureUnrankComb]; split_ifs with hlt
    · simp [ih hlt]
    · cases k with
      | zero => simp only [Nat.choose_zero_right] at hr hlt; omega
      | succ k =>
        rw [Nat.choose_succ_succ, Nat.succ_eq_add_one] at hr
        simp [ih (by omega : r - m.choose (k + 1) < m.choose k)]

private theorem pureUnrankComb_injective {m k r₁ r₂ : ℕ}
    (hr₁ : r₁ < m.choose k) (hr₂ : r₂ < m.choose k)
    (heq : pureUnrankComb m k r₁ = pureUnrankComb m k r₂) : r₁ = r₂ := by
  induction m generalizing k r₁ r₂ with
  | zero =>
    cases k with
    | zero => simp only [Nat.choose_zero_right, Nat.lt_one_iff] at hr₁ hr₂; omega
    | succ k => simp at hr₁
  | succ m ih =>
    simp only [pureUnrankComb] at heq; split_ifs at heq with h₁ h₂ h₂
    · simp only [List.cons.injEq, true_and] at heq; exact ih h₁ h₂ heq
    · simp at heq
    · simp at heq
    · simp only [List.cons.injEq, true_and] at heq
      cases k with
      | zero => simp only [Nat.choose_zero_right] at hr₁ h₁; omega
      | succ k =>
        rw [Nat.choose_succ_succ, Nat.succ_eq_add_one] at hr₁ hr₂
        have := ih (by omega : r₁ - m.choose (k + 1) < m.choose k) (by omega) heq; omega

private def pureScatter : List Bool → ℕ → List Bool
  | [], _ => []
  | b :: bs, mask =>
    if b then mask.testBit 0 :: pureScatter bs (mask / 2) else false :: pureScatter bs mask

private theorem foldl_scatterStep_eq (indE : List Bool) (mask : ℕ) (acc : List Bool) :
    (indE.foldl Internal.scatterStep (mask, acc)).2 = acc ++ pureScatter indE mask := by
  induction indE generalizing mask acc with
  | nil => simp [pureScatter]
  | cons b bs ih =>
    cases b <;> simp only [List.foldl_cons, Internal.scatterStep, pureScatter, Bool.false_eq_true,
      ↓reduceIte, ih, List.append_assoc, List.singleton_append]

private theorem scatterMask_eq_pure (indE : List Bool) (mask : ℕ) :
    Internal.scatterMask indE mask = pureScatter indE mask := by
  simpa only [Internal.scatterMask, List.nil_append] using foldl_scatterStep_eq indE mask []

private theorem length_pureScatter (indE : List Bool) (mask : ℕ) :
    (pureScatter indE mask).length = indE.length := by
  induction indE generalizing mask with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [pureScatter, ih]

private theorem getD_pureScatter_imp (indE : List Bool) (mask i : ℕ) :
    (pureScatter indE mask).getD i false = true → indE.getD i false = true := by
  induction indE generalizing mask i with
  | nil => simp [pureScatter]
  | cons b bs ih =>
    cases i with
    | zero => cases b <;> simp [pureScatter]
    | succ i =>
      cases b <;> simpa only [pureScatter, Bool.false_eq_true, ↓reduceIte, List.getD_cons_succ]
        using ih _ i

private theorem pureScatter_injective {indE : List Bool} {m₁ m₂ : ℕ}
    (hm₁ : m₁ < 2 ^ indE.count true) (hm₂ : m₂ < 2 ^ indE.count true)
    (heq : pureScatter indE m₁ = pureScatter indE m₂) : m₁ = m₂ := by
  induction indE generalizing m₁ m₂ with
  | nil => simp only [List.count_nil, pow_zero, Nat.lt_one_iff] at hm₁ hm₂; omega
  | cons b bs ih =>
    cases b
    · simp only [pureScatter, Bool.false_eq_true, ↓reduceIte, List.cons.injEq, true_and] at heq
      simp only [List.count_cons_of_ne Bool.false_ne_true] at hm₁ hm₂; exact ih hm₁ hm₂ heq
    · simp only [pureScatter, ↓reduceIte, List.cons.injEq] at heq
      simp only [List.count_cons_self, Nat.pow_succ] at hm₁ hm₂
      have hdiv : m₁ / 2 = m₂ / 2 := ih (by omega) (by omega) heq.2
      have hbit := heq.1; simp only [Nat.testBit_zero, decide_eq_decide] at hbit
      have := Nat.mod_lt m₁ (by omega : 0 < 2); have := Nat.mod_lt m₂ (by omega : 0 < 2)
      have := Nat.div_add_mod m₁ 2; have := Nat.div_add_mod m₂ 2; omega

/-- Out-of-range indices `j ≥ subsetPairCount n q` return the empty-pair fallback. -/
theorem unrankSubsetPair_of_le {n q j : ℕ} (hj : subsetPairCount n q ≤ j) :
    unrankSubsetPair n q j = (List.replicate n false, List.replicate n false, false) := by
  simp [unrankSubsetPair, findBucket_of_le hj]

/-- The first indicator `indE` returned by `unrankSubsetPair n q j` has exact length `n`. -/
@[simp] theorem length_fst_unrankSubsetPair (n q j : ℕ) :
    (unrankSubsetPair n q j).1.length = n := by
  by_cases hj : j < subsetPairCount n q
  · obtain ⟨_, _, hfb, -⟩ := findBucket_of_lt hj
    simp [unrankSubsetPair, hfb, unrankComb_eq_pure, length_pureUnrankComb]
  · rw [unrankSubsetPair_of_le (by omega)]; simp

/-- The second indicator `indU` returned by `unrankSubsetPair n q j` has exact length `n`. -/
@[simp] theorem length_snd_unrankSubsetPair (n q j : ℕ) :
    (unrankSubsetPair n q j).2.1.length = n := by
  by_cases hj : j < subsetPairCount n q
  · obtain ⟨_, _, hfb, -⟩ := findBucket_of_lt hj
    simp [unrankSubsetPair, hfb, scatterMask_eq_pure, length_pureScatter, unrankComb_eq_pure,
      length_pureUnrankComb]
  · rw [unrankSubsetPair_of_le (by omega)]; simp

/-- Pointwise containment: every `true` position of `indU` is also `true` in `indE`. -/
theorem getD_snd_imp_fst_unrankSubsetPair (n q j i : ℕ) :
    (unrankSubsetPair n q j).2.1.getD i false = true →
      (unrankSubsetPair n q j).1.getD i false = true := by
  by_cases hj : j < subsetPairCount n q
  · obtain ⟨_, _, hfb, -⟩ := findBucket_of_lt hj
    simp only [unrankSubsetPair, hfb, Option.elim_some, scatterMask_eq_pure]
    exact getD_pureScatter_imp _ _ i
  · rw [unrankSubsetPair_of_le (by omega)]; exact id

/-- Weight bound: `indE` has at most `min q n` (hence at most `q`) `true` entries. -/
theorem count_true_fst_unrankSubsetPair_le (n q j : ℕ) :
    (unrankSubsetPair n q j).1.count true ≤ min q n := by
  by_cases hj : j < subsetPairCount n q
  · obtain ⟨s, offset, hfb, hs_le, hoff_lt, -⟩ := findBucket_of_lt hj
    have hr_lt : offset / 2 ^ s < n.choose s := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), Nat.mul_comm]; exact hoff_lt
    simp only [unrankSubsetPair, hfb, Option.elim_some, unrankComb_eq_pure,
      count_true_pureUnrankComb hr_lt]; exact hs_le
  · rw [unrankSubsetPair_of_le (by omega)]; simp [List.count_replicate]

/-- The third component `negSign` is `decide (Odd (indE.count true - indU.count true))`. -/
theorem snd_snd_unrankSubsetPair_eq_decide_odd (n q j : ℕ) :
    (unrankSubsetPair n q j).2.2 =
      decide (Odd ((unrankSubsetPair n q j).1.count true -
        (unrankSubsetPair n q j).2.1.count true)) := by
  by_cases hj : j < subsetPairCount n q
  · obtain ⟨_, _, h, -⟩ := findBucket_of_lt hj; simp only [unrankSubsetPair, h, Option.elim_some]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, Nat.odd_iff]
  · rw [unrankSubsetPair_of_le (by omega)]; simp [List.count_replicate]

/-- Valid `(E, U)` subset pairs on `Fin n` with `#E ≤ q` and `U ⊆ E` ([OpenAI2026ETH]). -/
abbrev ValidSubsetPair (n q : ℕ) : Type :=
  {p : Finset (Fin n) × Finset (Fin n) // p.1.card ≤ q ∧ p.2 ⊆ p.1}

/-- Every decoded `unrankSubsetPair n q j` has `#E ≤ q`. -/
theorem card_fst_supportOfList_unrankSubsetPair_le (n q j : ℕ) :
    (supportOfList n (unrankSubsetPair n q j).1).card ≤ q := by
  rw [card_supportOfList_of_length (length_fst_unrankSubsetPair n q j)]
  exact (count_true_fst_unrankSubsetPair_le n q j).trans (Nat.min_le_left q n)

/-- Every decoded `unrankSubsetPair n q j` satisfies `U ⊆ E`. -/
theorem supportOfList_snd_subset_fst_unrankSubsetPair (n q j : ℕ) :
    supportOfList n (unrankSubsetPair n q j).2.1 ⊆
      supportOfList n (unrankSubsetPair n q j).1 := by
  intro i hi; rw [mem_supportOfList] at hi ⊢; exact getD_snd_imp_fst_unrankSubsetPair n q j i.val hi

/-- Map a valid index `j : Fin (subsetPairCount n q)` to its `ValidSubsetPair n q`. -/
def unrankValidSubsetPair (n q : ℕ) (j : Fin (subsetPairCount n q)) : ValidSubsetPair n q :=
  ⟨(supportOfList n (unrankSubsetPair n q j.val).1,
      supportOfList n (unrankSubsetPair n q j.val).2.1),
    ⟨card_fst_supportOfList_unrankSubsetPair_le n q j.val,
      supportOfList_snd_subset_fst_unrankSubsetPair n q j.val⟩⟩

private theorem unrankPair_injective {n q j₁ j₂ : ℕ}
    (hj₁ : j₁ < subsetPairCount n q) (hj₂ : j₂ < subsetPairCount n q)
    (hE : (unrankSubsetPair n q j₁).1 = (unrankSubsetPair n q j₂).1)
    (hU : (unrankSubsetPair n q j₁).2.1 = (unrankSubsetPair n q j₂).2.1) : j₁ = j₂ := by
  obtain ⟨s₁, off₁, hfb₁, _, hoff₁, hj₁_eq⟩ := findBucket_of_lt hj₁
  obtain ⟨s₂, off₂, hfb₂, _, hoff₂, hj₂_eq⟩ := findBucket_of_lt hj₂
  have hr₁ : off₁ / 2 ^ s₁ < n.choose s₁ := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), Nat.mul_comm]; exact hoff₁
  have hr₂ : off₂ / 2 ^ s₂ < n.choose s₂ := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), Nat.mul_comm]; exact hoff₂
  simp only [unrankSubsetPair, hfb₁, hfb₂, Option.elim_some] at hE hU
  have hs_eq : s₁ = s₂ := by
    simpa only [unrankComb_eq_pure, count_true_pureUnrankComb hr₁,
      count_true_pureUnrankComb hr₂] using congrArg (List.count true) hE
  subst hs_eq
  have hr_eq : off₁ / 2 ^ s₁ = off₂ / 2 ^ s₁ := by
    simp only [unrankComb_eq_pure] at hE; exact pureUnrankComb_injective hr₁ hr₂ hE
  have hm₁ : off₁ % 2 ^ s₁ <
      2 ^ (Internal.unrankComb n s₁ (off₁ / 2 ^ s₁) (pascalTable n)).count true := by
    rw [unrankComb_eq_pure, count_true_pureUnrankComb hr₁]; exact Nat.mod_lt off₁ (by positivity)
  have hm₂ : off₂ % 2 ^ s₁ <
      2 ^ (Internal.unrankComb n s₁ (off₁ / 2 ^ s₁) (pascalTable n)).count true := by
    rw [unrankComb_eq_pure, count_true_pureUnrankComb hr₁]; exact Nat.mod_lt off₂ (by positivity)
  rw [← hE] at hU; simp only [scatterMask_eq_pure] at hU
  have hm_eq := pureScatter_injective hm₁ hm₂ hU
  have hd₁ := Nat.div_add_mod off₁ (2 ^ s₁); have hd₂ := Nat.div_add_mod off₂ (2 ^ s₁)
  rw [hr_eq, hm_eq] at hd₁; omega

/-- `unrankValidSubsetPair n q` is injective on `Fin (subsetPairCount n q)`. -/
theorem injective_unrankValidSubsetPair (n q : ℕ) :
    Function.Injective (unrankValidSubsetPair n q) := by
  intro j₁ j₂ h; simp only [unrankValidSubsetPair, Subtype.mk.injEq, Prod.mk.injEq] at h
  exact Fin.ext (unrankPair_injective j₁.isLt j₂.isLt
    (supportOfList_injective_of_length (length_fst_unrankSubsetPair n q j₁.val)
      (length_fst_unrankSubsetPair n q j₂.val) h.1)
    (supportOfList_injective_of_length (length_snd_unrankSubsetPair n q j₁.val)
      (length_snd_unrankSubsetPair n q j₂.val) h.2))

/-- Summing `2 ^ #E` over all `E ⊆ Fin n` with `#E ≤ q` yields `subsetPairCount n q`. -/
theorem sum_two_pow_card_eq_subsetPairCount (n q : ℕ) :
    (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun E => E.card ≤ q), 2 ^ E.card) =
      subsetPairCount n q := by
  simpa only [subsetPairCount_eq, Fintype.card_fin] using
    Cslib.sum_powerset_filter_card_le_two_pow (ι := Fin n) q

private theorem sum_validSubsetPair {M : Type*} [AddCommMonoid M] (n q : ℕ)
    (f : Finset (Fin n) → Finset (Fin n) → M) :
    (∑ p : ValidSubsetPair n q, f p.1.1 p.1.2) =
      ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun E => E.card ≤ q),
        ∑ U ∈ E.powerset, f E U := by
  classical
  let validSet : Finset (Finset (Fin n) × Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powerset.filter (fun E => E.card ≤ q)).biUnion
      fun E => E.powerset.image fun U => (E, U)
  have hbiUnion : (∑ E ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun E => E.card ≤ q),
      ∑ U ∈ E.powerset, f E U) = ∑ p ∈ validSet, f p.1 p.2 := by
    rw [Finset.sum_biUnion]
    · exact Finset.sum_congr rfl fun E _ =>
        (Finset.sum_image (f := fun p : Finset (Fin n) × Finset (Fin n) => f p.1 p.2)
          fun _ _ _ _ h => (Prod.mk.inj h).2).symm
    · intro E₁ _ E₂ _ hne; refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => ?_
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp₁
      obtain ⟨_, _, hp₂_eq⟩ := Finset.mem_image.mp hp₂; exact hne (Prod.mk.inj hp₂_eq).1.symm
  rw [hbiUnion]
  exact Finset.sum_bij (fun (p : ValidSubsetPair n q) _ => p.1)
    (fun ⟨⟨E, U⟩, hE, hU⟩ _ => by simp [validSet, hE, hU]) (fun _ _ _ _ h => Subtype.ext h)
    (fun ⟨E, U⟩ hp => ⟨⟨(E, U), by simpa [validSet] using hp⟩, Finset.mem_univ _, rfl⟩)
    (fun _ _ => rfl)

/-- The finite type `ValidSubsetPair n q` has exact cardinality `subsetPairCount n q`. -/
theorem card_validSubsetPair (n q : ℕ) :
    Fintype.card (ValidSubsetPair n q) = subsetPairCount n q := by
  rw [Fintype.card_subtype, subsetPairCount_eq]
  exact Cslib.card_subsetPairs_eq_subsetPairCount_of_card (Fintype.card_fin n) q

/-- `unrankValidSubsetPair n q` is a bijection onto `ValidSubsetPair n q`. -/
theorem bijective_unrankValidSubsetPair (n q : ℕ) :
    Function.Bijective (unrankValidSubsetPair n q) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨injective_unrankValidSubsetPair n q, by simp [card_validSubsetPair]⟩

/-- Equivalence between binary indices `Fin (subsetPairCount n q)` and `ValidSubsetPair n q`. -/
noncomputable def validSubsetPairEquiv (n q : ℕ) :
    Fin (subsetPairCount n q) ≃ ValidSubsetPair n q :=
  Equiv.ofBijective (unrankValidSubsetPair n q) (bijective_unrankValidSubsetPair n q)

/-- Mapping `unrankSubsetPair n q` over `List.range (subsetPairCount n q)` has no duplicates. -/
theorem nodup_map_unrankSubsetPair (n q : ℕ) :
    ((List.range (subsetPairCount n q)).map (unrankSubsetPair n q)).Nodup := by
  rw [List.nodup_map_iff_inj_on List.nodup_range]; intro j₁ hj₁ j₂ hj₂ heq
  exact unrankPair_injective (List.mem_range.mp hj₁) (List.mem_range.mp hj₂)
    (congrArg Prod.fst heq) (congrArg (fun x => x.2.1) heq)

/-- Exact completeness: every valid pair `(E, U)` with `#E ≤ q` and `U ⊆ E` is decoded at a
unique index `j < subsetPairCount n q`. -/
theorem existsUnique_unrankSubsetPair (n q : ℕ) {E U : Finset (Fin n)}
    (hE : E.card ≤ q) (hU : U ⊆ E) :
    ∃! j, j < subsetPairCount n q ∧
      unrankSubsetPair n q j =
        (List.ofFn (fun i => decide (i ∈ E)), List.ofFn (fun i => decide (i ∈ U)),
          decide (Odd (E.card - U.card))) := by
  obtain ⟨j₀, hj₀, hunique⟩ :=
    (bijective_unrankValidSubsetPair n q).existsUnique ⟨(E, U), ⟨hE, hU⟩⟩
  refine ⟨j₀.val, ⟨j₀.isLt, ?_⟩, fun j ⟨hj_lt, hj_eq⟩ => ?_⟩
  · simp only [unrankValidSubsetPair, Subtype.mk.injEq, Prod.mk.injEq] at hj₀
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rw [← hj₀.1, ofFn_decide_mem_supportOfList (length_fst_unrankSubsetPair n q j₀.val)]
    · rw [← hj₀.2, ofFn_decide_mem_supportOfList (length_snd_unrankSubsetPair n q j₀.val)]
    · rw [snd_snd_unrankSubsetPair_eq_decide_odd,
        ← card_supportOfList_of_length (length_fst_unrankSubsetPair n q j₀.val),
        ← card_supportOfList_of_length (length_snd_unrankSubsetPair n q j₀.val), hj₀.1, hj₀.2]
  · refine congrArg Fin.val (hunique ⟨j, hj_lt⟩ (Subtype.ext ?_))
    simp only [unrankValidSubsetPair, hj_eq, supportOfList_ofFn_decide]

/-! ## Section 3: Plain `ComputableInPolyTime` and `NativeCertificate` witnesses -/

/-- Encoding for unary `(n, q)` dimension/degree parameters. -/
abbrev encParams : (ℕ × ℕ) ↪ List Bool := encPair encUnary encUnary

/-- Encoding for decoded `(indE, indU, negSign)` triples. -/
abbrev encDecodedPair : DecodedPair ↪ List Bool := encPair encBits (encPair encBits encBool)

section PlainProofs

open ComputableInPolyTime

/-- `pascalTable` is computable in polynomial time from `n` in unary. -/
@[fun_prop, program_certificate] theorem pascalTable_polyTime :
    ComputableInPolyTime pascalTable encUnary (encList (encList encNat)) := by
  let encRow := encList encNat; let encTab := encList encRow
  have hrep0 : ComputableInPolyTime (fun n : ℕ => List.replicate n 0) encUnary encRow :=
    ((map (const (encIn := encUnary) (encOut := encNat) 0)).comp range).of_enc_eq fun n => by
      dsimp only [encRow]; simp [List.map_const']
  have hinit : ComputableInPolyTime (fun n : ℕ => [1 :: List.replicate n 0])
      encUnary encTab :=
    ((const (encOut := encNat) 1).cons' hrep0).cons' (const [])
  have hstep : ComputableInPolyTime (fun p : ℕ × List (List ℕ) => Internal.pascalStep p.1 p.2)
      (encPair encUnary encTab) encTab := by
    let encP := encPair encUnary encTab
    have hprev := (headD (encA := encRow) []).comp (listReverseWithInput (snd encUnary encTab))
    have hmap : ComputableInPolyTime (fun p : ℕ × List (List ℕ) => (List.range p.1).map
        fun s => if s == 0 then 1
          else (p.2.reverse.headD []).getD (s - 1) 0 + (p.2.reverse.headD []).getD s 0)
        encP encRow := by
      refine mapWithInput (range.comp (fst encUnary encTab)) ?_
      have hq_prev := hprev.comp (fst encP encUnary); have hq_s := snd encP encUnary
      have hleft := (listGetD (encA := encNat) 0).comp
        (hq_prev.prod (unary_sub.comp (hq_s.prod (const 1))))
      have hright := (listGetD (encA := encNat) 0).comp (hq_prev.prod hq_s)
      exact (hq_s.beq (const 0)).ite (const 1) (binary_add.comp (hleft.prod hright))
    exact listAppend' (snd encUnary encTab) (hmap.cons' (const []))
  exact iterateWith (par := fun n : ℕ => n + 1) (count := fun n : ℕ => n)
    (init := fun n : ℕ => [1 :: List.replicate n 0]) (step := Internal.pascalStep)
    (unary_add.comp (id'.prod (const 1))) id' hinit hstep
    (bound := fun n => (n + 1) * (2 * ((n + 1) * (2 * (n + 1) + 1)) + 1))
    (by
      have h1 := (id' (encIn := encUnary)).polyBounded.add (.const 1)
      have h2 := h1.mul (((PolyBounded.const 2).mul h1).add (.const 1))
      exact h1.mul (((PolyBounded.const 2).mul h2).add (.const 1)))
    (fun n k hk => by
      rcases pascalStep_iterate_spec n k with ⟨hlen, _, hrows⟩
      refine (length_encList_le encRow _
        (b := (n + 1) * (2 * (n + 1) + 1)) fun row hrow => ?_).trans ?_
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
        rcases hrows i hi with ⟨hrlen, hrentry⟩
        refine (length_encList_le encNat _ (b := n + 1) fun x hx => ?_).trans (by rw [hrlen])
        obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hx
        rw [hrentry s hs]; exact length_encNat_choose_le (by omega) s
      · rw [hlen]; exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hk 1))

/-- `subsetPairCount` is computable in polynomial time from `(n, q)` in unary. -/
@[fun_prop, program_certificate] theorem subsetPairCount_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ => subsetPairCount p.1 p.2) encParams encNat := by
  have hfst := fst encUnary encUnary; have hsnd := snd encUnary encUnary
  have hrow := (listGetD (encA := encList encNat) []).comp
    ((pascalTable_polyTime.comp hfst).prod hfst)
  have humin : ComputableInPolyTime (fun p : ℕ × ℕ => min p.1 p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  have hcnt := unary_add.comp ((humin.comp (hsnd.prod hfst)).prod (const 1))
  have hbsum : ComputableInPolyTime List.sum (encList encNat) encNat := by fun_prop
  refine hbsum.comp (mapWithInput (range.comp hcnt) ?_); have hq_s := snd encParams encUnary
  exact binary_mul' (binary_two_pow.comp hq_s)
    ((listGetD (encA := encNat) 0).comp ((hrow.comp (fst encParams encUnary)).prod hq_s))

private theorem length_bucketState_le (rowN : List ℕ) (n j i L : ℕ)
    (hi : i ≤ n + 1) (hj_le : (encNat j).length ≤ L) (hn_le : n ≤ L) :
    (encPair encNat (encOption (encPair encUnary encNat))
      ((List.range i).foldl (Internal.bucketStep rowN) (j, none))).length ≤ 6 * L + 6 := by
  have hspec := foldl_bucketStep_spec rowN i j; dsimp only at hspec
  split_ifs at hspec with hlt
  · obtain ⟨s, off, hres, hs_lt, _, hj_eq⟩ := hspec
    have hoff_le : (encNat off).length ≤ (encNat j).length := by
      simpa [Nat.size_eq_bits_len] using Nat.size_le_size (by omega : off ≤ j)
    have hoff_len := hoff_le.trans hj_le
    rw [hres]
    simp only [length_encPair, encOption_some, List.length_cons, encUnary_apply,
      List.length_replicate]; omega
  · have hsub_le :
        (encNat (j - ∑ s ∈ Finset.range i, 2 ^ s * rowN.getD s 0)).length ≤ (encNat j).length := by
      simpa [Nat.size_eq_bits_len] using
        Nat.size_le_size (Nat.sub_le j (∑ s ∈ Finset.range i, 2 ^ s * rowN.getD s 0))
    have hsub_len := hsub_le.trans hj_le
    rw [hspec]; simp only [length_encPair, encOption_none, List.length_nil]; omega

private theorem computableInPolyTime_bucketStep :
    ComputableInPolyTime
      (fun q : (List ℕ × (ℕ × Option (ℕ × ℕ))) × ℕ => Internal.bucketStep q.1.1 q.1.2 q.2)
      (encPair (encPair (encList encNat) (encPair encNat (encOption (encPair encUnary encNat))))
        encUnary)
      (encPair encNat (encOption (encPair encUnary encNat))) := by
  let encOpt := encOption (encPair encUnary encNat); let encSt := encPair encNat encOpt
  let encQ := encPair (encPair (encList encNat) encSt) encUnary
  have hrow := (fst (encPair (encList encNat) encSt) encUnary).fst'
  have hst := (fst (encPair (encList encNat) encSt) encUnary).snd'
  have hs := snd (encPair (encList encNat) encSt) encUnary; have hrem := hst.fst'
  have hcap := binary_mul' (binary_two_pow.comp hs)
    ((listGetD (encA := encNat) 0).comp (hrow.prod hs))
  have hsome := hrem.prod ((optionSome (encPair encUnary encNat)).comp (hs.prod hrem))
  have hnone := (binary_sub' hrem hcap).prod
    (const (encIn := encQ) (encOut := encOpt) (none : Option (ℕ × ℕ)))
  have hinner : ComputableInPolyTime
      (fun q : (List ℕ × (ℕ × Option (ℕ × ℕ))) × ℕ =>
        if q.1.2.1 < 2 ^ q.2 * q.1.1.getD q.2 0 then (q.1.2.1, some (q.2, q.1.2.1))
        else (q.1.2.1 - 2 ^ q.2 * q.1.1.getD q.2 0, none))
      encQ encSt := by
    dsimp only [encQ, encSt, encOpt]
    simpa only [Function.comp_def, decide_eq_true_eq] using (binary_lt' hrem hcap).ite hsome hnone
  exact hst.snd'.optionIsSome.ite hst hinner

private theorem computableInPolyTime_findBucket :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × List (List ℕ) => Internal.findBucket p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair encParams encNat) (encList (encList encNat)))
      (encOption (encPair encUnary encNat)) := by
  let encTab := encList (encList encNat); let encIn := encPair (encPair encParams encNat) encTab
  let encSt := encPair encNat (encOption (encPair encUnary encNat))
  have hp1 := fst (encPair encParams encNat) encTab
  have hn := hp1.fst'.fst'; have hq := hp1.fst'.snd'
  have hpar := (listGetD (encA := encList encNat) []).comp
    ((snd (encPair encParams encNat) encTab).prod hn)
  have humin : ComputableInPolyTime (fun p : ℕ × ℕ => min p.1 p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  have hlist := range.comp (unary_add.comp ((humin.comp (hq.prod hn)).prod (const 1)))
  have hinit : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × List (List ℕ) => (p.1.2, (none : Option (ℕ × ℕ)))) encIn encSt :=
    hp1.snd'.prod (const none)
  have hfold := foldlWith (encA := encUnary) (encL := encList encUnary) (encP := encList encNat)
    (encB := encSt) hpar hlist hinit computableInPolyTime_bucketStep
    (B := fun p => 6 * (encIn p).length + 6) (((PolyBounded.const 6).mul .self).add (.const 6))
    (fun p i hi => by
      dsimp only [Function.comp_apply] at hi ⊢
      rw [List.length_range] at hi; rw [List.take_range, Nat.min_eq_left hi]
      have hj_le : (encNat p.1.2).length ≤ (encIn p).length :=
        (length_le_encPair_right encParams encNat p.1).trans (length_le_encPair_left _ _ p)
      have hn_le : p.1.1.1 ≤ (encIn p).length := by
        have h12 := (length_le_encPair_left encParams encNat p.1).trans
          (length_le_encPair_left (encPair encParams encNat) encTab p)
        simpa only [encUnary_apply, List.length_replicate] using
          (length_le_encPair_left encUnary encUnary p.1.1).trans h12
      exact length_bucketState_le (p.2.getD p.1.1.1 []) p.1.1.1 p.1.2 i (encIn p).length
        (by omega) hj_le hn_le)
  exact hfold.snd'

private theorem computableInPolyTime_unrankComb :
    ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × List (List ℕ) => Internal.unrankComb p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair encParams encNat) (encList (encList encNat))) encBits := by
  let encTab := encList (encList encNat); let encIn := encPair (encPair encParams encNat) encTab
  let encSt := encPair (encPair encUnary encNat) encBits
  have hp1 := fst (encPair encParams encNat) encTab
  have hstep : ComputableInPolyTime
      (fun q : (List (List ℕ) × ((ℕ × ℕ) × List Bool)) × ℕ =>
        Internal.unrankCombStep q.1.1 q.1.2 q.2)
      (encPair (encPair encTab encSt) encUnary) encSt := by
    have htab := (fst (encPair encTab encSt) encUnary).fst'
    have hst := (fst (encPair encTab encSt) encUnary).snd'
    have hm := snd (encPair encTab encSt) encUnary
    have hk := hst.fst'.fst'; have hr := hst.fst'.snd'; have hbits := hst.snd'
    have hc := (listGetD (encA := encNat) 0).comp
      (((listGetD (encA := encList encNat) []).comp (htab.prod hm)).prod hk)
    dsimp only [encSt]
    simpa only [Internal.unrankCombStep, Function.comp_def, decide_eq_true_eq] using
      (binary_lt' hr hc).ite ((hk.prod hr).prod (bitsAppend hbits (const [false])))
        (((unary_sub.comp (hk.prod (const 1))).prod
          (binary_sub' hr hc)).prod (bitsAppend hbits (const [true])))
  have hinit : ComputableInPolyTime
      (fun p : ((ℕ × ℕ) × ℕ) × List (List ℕ) => ((p.1.1.2, p.1.2), ([] : List Bool)))
      encIn encSt := (hp1.fst'.snd'.prod hp1.snd').prod (const [])
  refine (foldlWith_of_bounded_growth (encIn := encIn) (encP := encTab) (encA := encUnary)
    (encL := encList encUnary) (encB := encSt) (par := Prod.snd)
    (list := fun p => (List.range p.1.1.1).reverse) (init := fun p => ((p.1.1.2, p.1.2), []))
    (step := Internal.unrankCombStep) (snd (encPair encParams encNat) encTab)
    (listReverseWithInput (range.comp hp1.fst'.fst')) hinit hstep
    (growth := fun _ => 1) (.const 1) fun p state m _ => ?_).snd'
  simp only [encSt, Internal.unrankCombStep]; split_ifs
  · simp only [length_encPair, encBits_apply, List.length_append, List.length_singleton]; omega
  · have : (encNat (state.1.2 - (p.2.getD m []).getD state.1.1 0)).length ≤
        (encNat state.1.2).length := by
      simpa [Nat.size_eq_bits_len] using
        Nat.size_le_size (Nat.sub_le state.1.2 ((p.2.getD m []).getD state.1.1 0))
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply,
      List.length_append, List.length_singleton]; omega

private theorem computableInPolyTime_scatterMask :
    ComputableInPolyTime (fun p : List Bool × ℕ => Internal.scatterMask p.1 p.2)
      (encPair encBits encNat) encBits := by
  let encSt := encPair encNat encBits
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × Bool => Internal.scatterStep q.1 q.2)
      (encPair encSt encBool) encSt := by
    have hmask := (fst encSt encBool).fst'; have hbits := (fst encSt encBool).snd'
    have hyes := (binary_div.comp (hmask.prod (const 2))).prod
      (bitsAppend hbits (bitsCons (binary_testBit hmask (const 0)) (const [])))
    exact (snd encSt encBool).ite hyes (hmask.prod (bitsAppend hbits (const [false])))
  refine (foldl_of_bounded_growth (encIn := encPair encBits encNat) (encA := encBool)
    (encL := encBits) (encB := encSt) (list := Prod.fst) (init := fun p => (p.2, []))
    (step := Internal.scatterStep) (fst encBits encNat) ((snd encBits encNat).prod (const []))
    hstep (growth := 1) fun state bitE => ?_).snd'
  simp only [encSt, Internal.scatterStep]; cases bitE
  · simp only [Bool.false_eq_true, ↓reduceIte, length_encPair, encBits_apply,
      List.length_append, List.length_singleton]; omega
  · have : (encNat (state.1 / 2)).length ≤ (encNat state.1).length := by
      simpa [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.div_le_self state.1 2)
    simp only [↓reduceIte, length_encPair, encBits_apply, List.length_append,
      List.length_singleton]; omega

/-- `unrankSubsetPair` is computable in polynomial time from `(n, q)` in unary and `j` in binary. -/
@[fun_prop, program_certificate] theorem unrankSubsetPair_polyTime :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => unrankSubsetPair p.1.1 p.1.2 p.2)
      (encPair encParams encNat) encDecodedPair := by
  let encIn := encPair encParams encNat
  have hn_in := (fst encParams encNat).fst'; have htab := pascalTable_polyTime.comp hn_in
  have hfb := computableInPolyTime_findBucket.comp (id'.prod htab)
  have hrepF : ComputableInPolyTime (fun n : ℕ => List.replicate n false) encUnary encBits := by
    fun_prop
  have hzeros := hrepF.comp hn_in
  have hfall := hzeros.prod (hzeros.prod (const (encOut := encBool) false))
  have hq_fst := fst encIn (encPair encUnary encNat)
  have hq_snd := snd encIn (encPair encUnary encNat)
  have hq_pow := binary_two_pow.comp hq_snd.fst'
  have hq_indE := computableInPolyTime_unrankComb.comp
    ((((hn_in.comp hq_fst).prod hq_snd.fst').prod (binary_div.comp (hq_snd.snd'.prod hq_pow))).prod
      (htab.comp hq_fst))
  have hq_indU := computableInPolyTime_scatterMask.comp
    (hq_indE.prod (binary_mod.comp (hq_snd.snd'.prod hq_pow)))
  have hq_diff := unary_sub.comp
    ((bitsCountWithInput hq_indE (const true)).prod (bitsCountWithInput hq_indU (const true)))
  have hq_sign := (binary_mod.comp ((unary_to_binary.comp hq_diff).prod (const 2))).beq (const 1)
  exact optionElimWithInput hfb hfall (hq_indE.prod (hq_indU.prod hq_sign))

end PlainProofs

/-- Native certificate for `pascalTable`, selected via `NativeCertificate.ofPolyTime`. -/
noncomputable def pascalTableCertificate :
    NativeCertificate pascalTable encUnary (encList (encList encNat)) :=
  NativeCertificate.ofPolyTime pascalTable_polyTime

/-- `pascalTableCertificate` has polynomial time and workspace bounds. -/
theorem pascalTableCertificate_isPolynomial : pascalTableCertificate.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial pascalTable_polyTime

/-- Native certificate for `subsetPairCount`, selected via `NativeCertificate.ofPolyTime`. -/
noncomputable def subsetPairCountCertificate :
    NativeCertificate (fun p : ℕ × ℕ => subsetPairCount p.1 p.2) encParams encNat :=
  NativeCertificate.ofPolyTime subsetPairCount_polyTime

/-- `subsetPairCountCertificate` has polynomial time and workspace bounds. -/
theorem subsetPairCountCertificate_isPolynomial : subsetPairCountCertificate.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial subsetPairCount_polyTime

/-- Native certificate for `unrankSubsetPair`, selected via `NativeCertificate.ofPolyTime`. -/
noncomputable def unrankSubsetPairCertificate :
    NativeCertificate (fun p : (ℕ × ℕ) × ℕ => unrankSubsetPair p.1.1 p.1.2 p.2)
      (encPair encParams encNat) encDecodedPair :=
  NativeCertificate.ofPolyTime unrankSubsetPair_polyTime

/-- `unrankSubsetPairCertificate` has polynomial time and workspace bounds. -/
theorem unrankSubsetPairCertificate_isPolynomial : unrankSubsetPairCertificate.IsPolynomial :=
  NativeCertificate.ofPolyTime_isPolynomial unrankSubsetPair_polyTime

/-! ## Section 4: Streaming `IndexFold` combinator (`SubsetPairFold.run` & `computableInO`) -/

section Streaming

variable {α β : Type}

/-- Retained accumulator encoding pairing unary `(n, q)` parameters with the caller's `encB`. -/
abbrev encLoopAcc (encB : β ↪ List Bool) : ((ℕ × ℕ) × β) ↪ List Bool := encPair encParams encB

/-- Per-index round body for `IndexFold.run`, retaining `(n, q)` and decoding `j` on the fly. -/
def indexBody (body : DecodedPair × β → β) (p : ℕ × ((ℕ × ℕ) × β)) : (ℕ × ℕ) × β :=
  (p.2.1, body (unrankSubsetPair p.2.1.1 p.2.1.2 p.1, p.2.2))

/-- Streaming prefix after `m` binary-indexed steps of `IndexFold.run`. -/
def runPrefix (body : DecodedPair × β → β) (n q m : ℕ) (initial : β) : ℕ × ((ℕ × ℕ) × β) :=
  IndexFold.run (indexBody body) m ((n, q), initial)

/-- Stream all `subsetPairCount n q` valid `(E, U)` subset pairs through `IndexFold.run`. -/
def run (body : DecodedPair × β → β) (n q : ℕ) (initial : β) : β :=
  (runPrefix body n q (subsetPairCount n q) initial).2.2

@[simp] theorem runPrefix_index (body : DecodedPair × β → β) (n q m : ℕ) (initial : β) :
    (runPrefix body n q m initial).1 = m := IndexFold.run_index _ _ _

/-- The retained unary parameter pair `(n, q)` is invariant across all streaming prefixes. -/
@[simp] theorem runPrefix_params (body : DecodedPair × β → β) (n q m : ℕ) (initial : β) :
    (runPrefix body n q m initial).2.1 = (n, q) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [runPrefix, IndexFold.run_succ, IndexFold.step, indexBody] at ih ⊢; exact ih

/-- Every prefix accumulator equals the ordered range fold over decoded indices `0, …, m - 1`. -/
theorem runPrefix_acc (body : DecodedPair × β → β) (n q m : ℕ) (initial : β) :
    (runPrefix body n q m initial).2.2 =
      (List.range m).foldl (fun acc j => body (unrankSubsetPair n q j, acc)) initial := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hst : runPrefix body n q m initial =
        (m, ((n, q), (List.range m).foldl (fun acc j => body (unrankSubsetPair n q j, acc))
          initial)) :=
      Prod.ext (runPrefix_index body n q m initial) (Prod.ext (runPrefix_params _ n q m initial) ih)
    simp only [runPrefix, IndexFold.run_succ, IndexFold.step, indexBody, List.range_succ,
      List.foldl_append, List.foldl_cons, List.foldl_nil] at hst ⊢; rw [hst]

/-- `SubsetPairFold.run` agrees with folding over `List.range (subsetPairCount n q)`. -/
theorem run_eq_foldl_range (body : DecodedPair × β → β) (n q : ℕ) (initial : β) :
    run body n q initial =
      (List.range (subsetPairCount n q)).foldl
        (fun acc j => body (unrankSubsetPair n q j, acc)) initial :=
  runPrefix_acc body n q (subsetPairCount n q) initial

/-- `SubsetPairFold.run` agrees with folding over the mapped list of decoded pairs. -/
theorem run_eq_foldl_map (body : DecodedPair × β → β) (n q : ℕ) (initial : β) :
    run body n q initial =
      ((List.range (subsetPairCount n q)).map (unrankSubsetPair n q)).foldl
        (fun acc item => body (item, acc)) initial := by
  rw [run_eq_foldl_range, List.foldl_map]

/-- Commutative-monoid accumulation via `run` sums over all `E ⊆ Fin n` (`#E ≤ q`) and `U ⊆ E`. -/
theorem run_add_eq_sum_validSubsetPairs {M : Type} [AddCommMonoid M]
    (n q : ℕ) (f : Finset (Fin n) → Finset (Fin n) → Bool → M) :
    run (fun p => p.2 + f (supportOfList n p.1.1) (supportOfList n p.1.2.1) p.1.2.2) n q 0 =
      ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun E => E.card ≤ q),
        ∑ U ∈ E.powerset, f E U (decide (Odd (E.card - U.card))) := by
  rw [run_eq_foldl_range]
  change (List.range (subsetPairCount n q)).foldl (fun a j => a +
      f (supportOfList n (unrankSubsetPair n q j).1)
        (supportOfList n (unrankSubsetPair n q j).2.1) (unrankSubsetPair n q j).2.2) 0 = _
  rw [← List.foldl_map, ← List.sum_eq_foldl, ← List.sum_toFinset _ List.nodup_range,
    List.toFinset_range, ← Fin.sum_univ_eq_sum_range]
  let φ : ValidSubsetPair n q → M :=
    fun v => f v.1.1 v.1.2 (decide (Odd (v.1.1.card - v.1.2.card)))
  have hcongr : (∑ j : Fin (subsetPairCount n q),
      f (supportOfList n (unrankSubsetPair n q j.val).1)
        (supportOfList n (unrankSubsetPair n q j.val).2.1) (unrankSubsetPair n q j.val).2.2) =
      ∑ j : Fin (subsetPairCount n q), φ (validSubsetPairEquiv n q j) :=
    Finset.sum_congr rfl fun j _ => by
      simp only [φ, validSubsetPairEquiv, Equiv.ofBijective_apply, unrankValidSubsetPair,
        snd_snd_unrankSubsetPair_eq_decide_odd,
        card_supportOfList_of_length (length_fst_unrankSubsetPair n q j.val),
        card_supportOfList_of_length (length_snd_unrankSubsetPair n q j.val)]
  rw [hcongr, Equiv.sum_comp (validSubsetPairEquiv n q) φ]
  exact sum_validSubsetPair n q fun E U => f E U (decide (Odd (E.card - U.card)))

/-- Signed Möbius accumulation via `run` computes `∑_{#E ≤ q} ∑_{U ⊆ E} (-1) ^ (#E - #U) * g E U`
over any commutative ring `R` ([OpenAI2026ETH], Lemma 3.3 eq. (3.10), Proposition 3.4). -/
theorem run_mobius_eq_sum_restricted_subsets {R : Type} [CommRing R]
    (n q : ℕ) (g : Finset (Fin n) → Finset (Fin n) → R) :
    run (fun p =>
      let term := g (supportOfList n p.1.1) (supportOfList n p.1.2.1)
      if p.1.2.2 then p.2 - term else p.2 + term) n q 0 =
      ∑ E ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun E => E.card ≤ q),
        ∑ U ∈ E.powerset, (-1 : R) ^ (E.card - U.card) * g E U := by
  have hbody : (fun p : DecodedPair × R =>
      let term := g (supportOfList n p.1.1) (supportOfList n p.1.2.1)
      if p.1.2.2 then p.2 - term else p.2 + term) =
      fun p => p.2 + (if p.1.2.2 then (-1 : R) else 1) *
        g (supportOfList n p.1.1) (supportOfList n p.1.2.1) := by
    funext ⟨⟨_, _, negSign⟩, _⟩; cases negSign <;> simp [sub_eq_add_neg]
  rw [hbody, run_add_eq_sum_validSubsetPairs n q
    (fun E U neg => (if neg then (-1 : R) else 1) * g E U)]
  refine Finset.sum_congr rfl fun E _ => Finset.sum_congr rfl fun U _ => ?_
  by_cases hodd : Odd (E.card - U.card)
  · simp [hodd, Odd.neg_one_pow hodd]
  · simp [hodd, Even.neg_one_pow (Nat.not_odd_iff_even.mp hodd)]

variable {encB : β ↪ List Bool}

/-- Native certificate for one `indexBody` round, retaining `(n, q)` in unary. -/
noncomputable def indexBodyCertificate {body : DecodedPair × β → β}
    (cb : NativeCertificate body (encPair encDecodedPair encB) encB) :
    NativeCertificate (indexBody body) (encPair encNat (encLoopAcc encB)) (encLoopAcc encB) :=
  let cIdx := NativeCertificate.linear (ComputableInO.fst encNat (encLoopAcc encB))
  let cLoop := NativeCertificate.linear (ComputableInO.snd encNat (encLoopAcc encB))
  let cParams := NativeCertificate.fst cLoop
  cParams.prod (cb.comp ((unrankSubsetPairCertificate.comp (cParams.prod cIdx)).prod (.snd cLoop)))

/-- Native certificate for `SubsetPairFold.run`, built on `IndexFold.certificate`. -/
noncomputable def certificate {encIn : α ↪ List Bool} {dim deg : α → ℕ}
    {initial : α → β} {body : DecodedPair × β → β}
    (cn : NativeCertificate dim encIn encUnary) (cq : NativeCertificate deg encIn encUnary)
    (ci : NativeCertificate initial encIn encB)
    (cb : NativeCertificate body (encPair encDecodedPair encB) encB) :
    NativeCertificate (fun a => run body (dim a) (deg a) (initial a)) encIn encB :=
  NativeCertificate.snd (NativeCertificate.snd
    (IndexFold.certificate (subsetPairCountCertificate.comp (cn.prod cq))
      ((cn.prod cq).prod ci) (indexBodyCertificate cb)))

end Streaming

end Cslib.GenericRAM.SubsetPairFold

end

public section

namespace Cslib.GenericRAM.SubsetPairFold

open Turing.MultiTapeTM

section OverheadAndBounds

variable {α β : Type} {encB : β ↪ List Bool}

private theorem exists_decodeOverhead :
    ∃ f : ℕ → ℕ, Cslib.PolynomiallyBounded f ∧ (∀ m, (m + 1) ^ 2 ≤ f m) ∧
      (∀ n q, subsetPairCountCertificate.time (n, q) ≤ f (n + q) ∧
        subsetPairCountCertificate.space (n, q) ≤ f (n + q)) ∧
      (∀ n q j, j ≤ subsetPairCount n q →
        unrankSubsetPairCertificate.time ((n, q), j) ≤ f (n + q) ∧
        unrankSubsetPairCertificate.space ((n, q), j) ≤ f (n + q)) := by
  obtain ⟨c₁, d₁, h₁⟩ := subsetPairCountCertificate_isPolynomial.1.exists_le
  obtain ⟨c₂, d₂, h₂⟩ := subsetPairCountCertificate_isPolynomial.2.exists_le
  obtain ⟨c₃, d₃, h₃⟩ := unrankSubsetPairCertificate_isPolynomial.1.exists_le
  obtain ⟨c₄, d₄, h₄⟩ := unrankSubsetPairCertificate_isPolynomial.2.exists_le
  refine ⟨fun m => (m + 1) ^ 2 + c₁ * (2 * m + 2) ^ d₁ + c₂ * (2 * m + 2) ^ d₂ +
      c₃ * (6 * m + 5) ^ d₃ + c₄ * (6 * m + 5) ^ d₄,
    by fun_prop, fun _ => by dsimp only; omega, fun n q => ?_, fun n q j hj => ?_⟩
  · dsimp only
    have hlen : (encParams (n, q)).length + 1 ≤ 2 * (n + q) + 2 := by
      simp only [encParams, length_encPair, encUnary_apply, List.length_replicate]; omega
    have := (h₁ (n, q)).trans (Nat.mul_le_mul_left c₁ (Nat.pow_le_pow_left hlen d₁))
    have := (h₂ (n, q)).trans (Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left hlen d₂)); omega
  · dsimp only
    have hj_len : (encNat j).length ≤ (encNat (subsetPairCount n q)).length := by
      simpa [Nat.size_eq_bits_len] using Nat.size_le_size hj
    have := hj_len.trans (length_encNat_subsetPairCount_le n q)
    have hlen : (encPair encParams encNat ((n, q), j)).length + 1 ≤ 6 * (n + q) + 5 := by
      simp only [encParams, length_encPair, encUnary_apply, List.length_replicate]; omega
    have := (h₃ ((n, q), j)).trans (Nat.mul_le_mul_left c₃ (Nat.pow_le_pow_left hlen d₃))
    have := (h₄ ((n, q), j)).trans (Nat.mul_le_mul_left c₄ (Nat.pow_le_pow_left hlen d₄)); omega

/-- Polynomial overhead in `n + q` for `subsetPairCount`, unranking, and index maintenance. -/
noncomputable def decodeOverhead : ℕ → ℕ := exists_decodeOverhead.choose

/-- `decodeOverhead` is polynomially bounded in `n + q`. -/
@[fun_prop] theorem polynomiallyBounded_decodeOverhead :
    Cslib.PolynomiallyBounded decodeOverhead := exists_decodeOverhead.choose_spec.1

/-- Streaming resource bound for `SubsetPairFold.run` via `IndexFold.computableInO`: time scales
with `subsetPairCount (dim a) (deg a) + 1` while live workspace is independent of `C_q`. -/
theorem computableInO {encIn : α ↪ List Bool} {dim deg : α → ℕ}
    {initial : α → β} {body : DecodedPair × β → β}
    (cn : NativeCertificate dim encIn encUnary) (cq : NativeCertificate deg encIn encUnary)
    (ci : NativeCertificate initial encIn encB)
    (cb : NativeCertificate body (encPair encDecodedPair encB) encB) (R Q B : α → ℕ)
    (hR : ∀ a j, j ≤ subsetPairCount (dim a) (deg a) →
      cb.time (unrankSubsetPair (dim a) (deg a) j,
        (runPrefix body (dim a) (deg a) j (initial a)).2.2) ≤ R a)
    (hQ : ∀ a j, j ≤ subsetPairCount (dim a) (deg a) →
      cb.space (unrankSubsetPair (dim a) (deg a) j,
        (runPrefix body (dim a) (deg a) j (initial a)).2.2) ≤ Q a)
    (hB : ∀ a j, j ≤ subsetPairCount (dim a) (deg a) →
      (encB (runPrefix body (dim a) (deg a) j (initial a)).2.2).length ≤ B a) :
    ComputableInO (fun a => run body (dim a) (deg a) (initial a)) encIn encB
      (fun a => (encIn a).length + cn.time a + cq.time a + ci.time a +
        decodeOverhead (dim a + deg a) +
        (subsetPairCount (dim a) (deg a) + 1) * (decodeOverhead (dim a + deg a) + B a + R a))
      (fun a => (encIn a).length + cn.space a + cq.space a + ci.space a +
        decodeOverhead (dim a + deg a) + B a + Q a) := by
  let cCount := subsetPairCountCertificate.comp (cn.prod cq)
  let cInit := (cn.prod cq).prod ci; let cStep := indexBodyCertificate cb
  let BLoop (a : α) := 4 * (dim a + deg a) + 3 + B a
  let RLoop (a : α) := 4 * (8 * (dim a + deg a) + 6 + B a) + decodeOverhead (dim a + deg a) + R a
  let QLoop (a : α) := 4 * (8 * (dim a + deg a) + 6 + B a) + decodeOverhead (dim a + deg a) + Q a
  have hspec := exists_decodeOverhead.choose_spec
  rw [← show decodeOverhead = exists_decodeOverhead.choose from rfl] at hspec
  rcases hspec with ⟨_, hsq_all, hcnt_all, hunr_all⟩
  have hB_loop : ∀ a j, j ≤ subsetPairCount (dim a) (deg a) →
      (encLoopAcc encB (runPrefix body (dim a) (deg a) j (initial a)).2).length ≤ BLoop a := by
    intro a j hj; have := hB a j hj
    simp only [encLoopAcc, encParams, length_encPair, runPrefix_params, encUnary_apply,
      List.length_replicate, BLoop]; omega
  have hlenP : ∀ a j, j ≤ subsetPairCount (dim a) (deg a) →
      (encPair encNat (encLoopAcc encB) (runPrefix body (dim a) (deg a) j (initial a))).length ≤
        8 * (dim a + deg a) + 6 + B a := by
    intro a j hj
    have h1 := IndexFold.length_run_le (encB := encLoopAcc encB) (indexBody body)
      ((dim a, deg a), initial a) hj (hB_loop a j hj)
    have := length_encNat_subsetPairCount_le (dim a) (deg a)
    dsimp only [runPrefix]; simp only [BLoop] at h1; omega
  have hR_loop : ∀ a j, j ≤ subsetPairCount (dim a) (deg a) →
      cStep.time (runPrefix body (dim a) (deg a) j (initial a)) ≤ RLoop a := by
    intro a j hj; have := hlenP a j hj; have := (hunr_all (dim a) (deg a) j hj).1; have := hR a j hj
    dsimp only [cStep, indexBodyCertificate, RLoop]
    simp only [NativeCertificate.prod_time, NativeCertificate.comp_time, NativeCertificate.fst_time,
      NativeCertificate.snd_time, NativeCertificate.linear_time, runPrefix_index, runPrefix_params]
    omega
  have hQ_loop : ∀ a j, j ≤ subsetPairCount (dim a) (deg a) →
      cStep.space (runPrefix body (dim a) (deg a) j (initial a)) ≤ QLoop a := by
    intro a j hj; have := hlenP a j hj; have := (hunr_all (dim a) (deg a) j hj).2; have := hQ a j hj
    dsimp only [cStep, indexBodyCertificate, QLoop]
    simp only [NativeCertificate.prod_space, NativeCertificate.comp_space,
      NativeCertificate.fst_space, NativeCertificate.snd_space, NativeCertificate.linear_space,
      runPrefix_index, runPrefix_params]
    omega
  have hfold := IndexFold.computableInO cCount cInit cStep RLoop QLoop BLoop hR_loop hQ_loop hB_loop
  have hproj : ComputableInO (fun a => run body (dim a) (deg a) (initial a)) encIn encB _ _ :=
    (ComputableInO.snd encParams encB).comp_linear
      ((ComputableInO.snd encNat (encLoopAcc encB)).comp_linear hfold)
  refine hproj.mono 128 (fun a => ?_) (fun a => ?_)
  · dsimp only [cCount, cInit, BLoop, RLoop]
    simp only [NativeCertificate.comp_time, NativeCertificate.prod_time, Function.comp_apply]
    have := (hcnt_all (dim a) (deg a)).1; have := length_encNat_subsetPairCount_le (dim a) (deg a)
    have := hsq_all (dim a + deg a)
    have : dim a + deg a + 1 ≤ (dim a + deg a + 1) ^ 2 := by
      rw [sq]; exact Nat.le_mul_of_pos_right _ (by omega)
    have : ((encNat (subsetPairCount (dim a) (deg a))).length + 1) ^ 2 ≤
        4 * (dim a + deg a + 1) ^ 2 := by
      calc ((encNat (subsetPairCount (dim a) (deg a))).length + 1) ^ 2
          ≤ (2 * (dim a + deg a + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 4 * (dim a + deg a + 1) ^ 2 := by ring
    let L := (encNat (subsetPairCount (dim a) (deg a))).length
    have hstep_le : 2 * L + 1 + (4 * (dim a + deg a) + 3 + B a) + (L + 1) ^ 2 +
        (4 * (8 * (dim a + deg a) + 6 + B a) + decodeOverhead (dim a + deg a) + R a) +
        (2 * L + 1 + (4 * (dim a + deg a) + 3 + B a)) + (L + 1) ^ 2 ≤
        128 * (decodeOverhead (dim a + deg a) + B a + R a) := by dsimp only [L]; omega
    have hmul := Nat.mul_le_mul_left (subsetPairCount (dim a) (deg a) + 1) hstep_le
    rw [Nat.mul_left_comm] at hmul; dsimp only [L] at hmul; omega
  · dsimp only [cCount, cInit, BLoop, QLoop]
    simp only [NativeCertificate.comp_space, NativeCertificate.prod_space, Function.comp_apply]
    have := (hcnt_all (dim a) (deg a)).2; have := length_encNat_subsetPairCount_le (dim a) (deg a)
    have := hsq_all (dim a + deg a)
    have : dim a + deg a + 1 ≤ (dim a + deg a + 1) ^ 2 := by
      rw [sq]; exact Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- When `dim`, `deg`, and `initial` have polynomial certificates and `B` and `Q` are polynomially
bounded in the input length, the live workspace of `SubsetPairFold.computableInO` is polynomial. -/
theorem polyBounded_space_of_polyBounded {encIn : α ↪ List Bool} {dim deg : α → ℕ}
    {initial : α → β} {B Q : α → ℕ}
    (cn : NativeCertificate dim encIn encUnary) (cq : NativeCertificate deg encIn encUnary)
    (ci : NativeCertificate initial encIn encB)
    (hcn : cn.IsPolynomial) (hcq : cq.IsPolynomial) (hci : ci.IsPolynomial)
    (hB : PolyBounded (fun a => (encIn a).length) B)
    (hQ : PolyBounded (fun a => (encIn a).length) Q) :
    PolyBounded (fun a => (encIn a).length)
      (fun a => (encIn a).length + cn.space a + cq.space a + ci.space a +
        decodeOverhead (dim a + deg a) + B a + Q a) := by
  have hdim : PolyBounded (fun a => (encIn a).length) dim := by
    simpa only [encUnary_apply, List.length_replicate] using (cn.polyTime hcn).polyBounded_length
  have hdeg : PolyBounded (fun a => (encIn a).length) deg := by
    simpa only [encUnary_apply, List.length_replicate] using (cq.polyTime hcq).polyBounded_length
  have hdec : PolyBounded (fun a => (encIn a).length) (fun a => decodeOverhead (dim a + deg a)) :=
    (PolyBounded.of_polynomiallyBounded id polynomiallyBounded_decodeOverhead).comp
      (hdim.add hdeg)
  exact ((((((PolyBounded.self.add hcn.2).add hcq.2).add hci.2).add hdec).add hB).add hQ)

end OverheadAndBounds

end Cslib.GenericRAM.SubsetPairFold

end
