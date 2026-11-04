/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.KMP.Basic
public import Cslib.Algorithms.Lean.TimeM

/-!
# Knuth–Morris–Pratt Failure Table Construction and Exact String Matching

This module implements the Knuth–Morris–Pratt (`[KnuthMorrisPratt1977]`, Sections 1–2;
`[CLRS2009]`, Section 32.4) failure-table construction (`computePrefixM`, `computePrefix`) and
linear-time exact string matcher (`kmpSearchWithPrefixM`, `kmpSearchM`, `kmpMatches`,
`kmpMatchesList`) in `Cslib.Algorithms.Lean.TimeM`, proving soundness, completeness, strict output
ordering, and amortized linear character-comparison bounds over arbitrary alphabets
`[DecidableEq α]`.

## Source Conventions

* **Indexing:** arrays are `0`-indexed, so `pi[j] = borderLen p.toList (j + 1)` (`0 ≤ j < p.size`)
  stores `[CLRS2009]`'s `1`-indexed prefix table $\pi[1..m]$ at `j = q - 1`. Reported match shifts
  `s` are `0`-based (`t.extract s (s + p.size) = p`), matching `[CLRS2009]`'s shift
  $s \in \{0, \dots, n - m\}$.
* **Alphabet and empty pattern:** all operations are universe-polymorphic over any
  `[DecidableEq α]` in `Type*` (rather than a fixed finite alphabet $\Sigma$) and handle empty
  patterns `p.size = 0` unconditionally by returning `List.range (t.size + 1)` with `0`
  comparisons (whereas `[CLRS2009]` assumes $m \ge 1$).
* **Resource bounds:** `TimeM ℕ` counts exact character comparisons `p[k] = c` rather than
  asymptotic RAM step bounds $\Theta(m)$ and $\Theta(n)$.

## Cost Model

* **Charged (`1` `TimeM` tick):** every character equality comparison `p[k] = c` inside the shared
  KMP automaton step `advanceM` (covering both matching extensions and mismatch fallback checks).
  Because each recursive fallback in `advanceM` follows a charged mismatch,
  `(advanceM p pi k c).time` also bounds the number of fallback steps.
* **Uncharged (`0` `TimeM` ticks):** integer arithmetic, loop/recursion control, array reads
  (`p[k]`, `pi[k - 1]`, `t[i]`), `Array.push` during failure-table construction, list consing when
  collecting match shifts (including `List.range (t.size + 1)` when `p.size = 0`), and
  `List.toArray` conversion in `kmpMatchesList`.

Using the potential $\Phi = k$ (the current matched prefix length), every call to `advanceM`
satisfies `(advanceM p pi k c).time + (advanceM p pi k c).ret ≤ k + 2`
(`advanceM_time_add_ret_le`), telescoping to:

* `(computePrefixM p).time ≤ 2 * (p.size - 1)` character comparisons
  (`[KnuthMorrisPratt1977]`, Section 2; `[CLRS2009]`, Section 32.4);
* `(kmpSearchWithPrefixM p pi t).time ≤ 2 * t.size` character comparisons when `pi` satisfies
  `pi[j] ≤ j` (in particular for `pi = computePrefix p`);
* `(kmpSearchM p t).time ≤ 2 * (p.size - 1) + 2 * t.size` character comparisons end-to-end
  (`[KnuthMorrisPratt1977]`, Sections 1–2; `[CLRS2009]`, Section 32.4).

## Main definitions

* `Cslib.Algorithms.Lean.KMP.IsPrefixTableFor`: `pi.size ≤ p.size` and
  `pi[j] = borderLen p.toList (j + 1)` for `j < pi.size`.
* `Cslib.Algorithms.Lean.KMP.IsMatchAt`: exact occurrence `s + p.size ≤ t.size` and
  `t.extract s (s + p.size) = p`.
* `Cslib.Algorithms.Lean.KMP.advanceM`: single-character KMP automaton transition in `TimeM ℕ`.
* `Cslib.Algorithms.Lean.KMP.computePrefixM`, `computePrefix`: failure-table construction.
* `Cslib.Algorithms.Lean.KMP.kmpSearchWithPrefixM`, `kmpSearchM`, `kmpMatches`: exact string
  matching on `Array α` returning all match shifts in strictly increasing order.
* `Cslib.Algorithms.Lean.KMP.kmpMatchesList`: list wrapper returning all shifts `s ≤ t.length`
  where `p <+: t.drop s`.

## Main results

* `Cslib.Algorithms.Lean.KMP.computePrefix_size` and `getElem_computePrefix`: `computePrefix p`
  has size `p.size` and entry `q` equal to `borderLen p.toList (q + 1)`.
* `Cslib.Algorithms.Lean.KMP.computePrefixM_time_le`: `(computePrefixM p).time ≤ 2 * (p.size - 1)`.
* `Cslib.Algorithms.Lean.KMP.mem_kmpMatches_iff`: `s ∈ kmpMatches p t ↔ IsMatchAt p t s`
  (unconditionally for all `p` and `t`, including empty patterns and overlapping matches).
* `Cslib.Algorithms.Lean.KMP.pairwise_lt_kmpMatches` and `nodup_kmpMatches`: match shifts are
  strictly increasing and duplicate-free.
* `Cslib.Algorithms.Lean.KMP.kmpSearchM_time_le`:
  `(kmpSearchM p t).time ≤ 2 * (p.size - 1) + 2 * t.size`.
* `Cslib.Algorithms.Lean.KMP.mem_kmpMatchesList_iff`:
  `s ∈ kmpMatchesList p t ↔ s ≤ t.length ∧ p <+: t.drop s`.

## References

* [D. E. Knuth, J. H. Morris, Jr., and V. R. Pratt, *Fast Pattern Matching in
  Strings*][KnuthMorrisPratt1977]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to Algorithms*,
  3rd ed., Section 32.4][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.KMP

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

/-! ## Prefix-table and exact-match specifications -/

/-- `pi` is a valid partial KMP failure table for `p` if `pi.size ≤ p.size` and each entry `pi[j]`
equals `borderLen p.toList (j + 1)`. -/
@[expose] def IsPrefixTableFor {α : Type*} [DecidableEq α] (p : Array α) (pi : Array ℕ) : Prop :=
  pi.size ≤ p.size ∧ ∀ (j : ℕ) (hj : j < pi.size), pi[j]'hj = borderLen p.toList (j + 1)

/-- Structural fallback bound `pi[j] ≤ j` for every `j < pi.size`. -/
@[expose] def IsDecreasingTable (pi : Array ℕ) : Prop :=
  ∀ (j : ℕ) (hj : j < pi.size), pi[j]'hj ≤ j

theorem IsPrefixTableFor.isDecreasingTable {α : Type*} [DecidableEq α]
    {p : Array α} {pi : Array ℕ} (h : IsPrefixTableFor p pi) : IsDecreasingTable pi := by
  intro j hj
  rw [h.2 j hj]
  have hsize : 0 < p.size := by have := h.1; omega
  have hp : p.toList ≠ [] := by
    intro hnil
    have h0 : p.size = 0 := by
      simpa only [Array.length_toList, List.length_nil] using congrArg List.length hnil
    omega
  have hlt : borderLen p.toList (j + 1) < j + 1 := borderLen_lt (by omega) hp
  omega

/-- Pattern `p` occurs in text `t` at shift `s` (`0`-indexed). -/
@[expose] def IsMatchAt {α : Type*} (p t : Array α) (s : ℕ) : Prop :=
  s + p.size ≤ t.size ∧ t.extract s (s + p.size) = p

theorem isMatchAt_iff_toList {α : Type*} {p t : Array α} {s : ℕ} :
    IsMatchAt p t s ↔ s + p.size ≤ t.size ∧ p.toList <+: t.toList.drop s := by
  unfold IsMatchAt
  constructor
  · rintro ⟨hs, hext⟩
    refine ⟨hs, ?_⟩
    have hlist : (t.extract s (s + p.size)).toList = p.toList := congrArg Array.toList hext
    rw [Array.toList_extract, List.extract_eq_take_drop] at hlist
    have hsub : s + p.size - s = p.size := by omega
    rw [hsub] at hlist
    rw [List.prefix_iff_eq_take, Array.length_toList]
    exact hlist.symm
  · rintro ⟨hs, hpref⟩
    refine ⟨hs, Array.toList_inj.mp ?_⟩
    rw [Array.toList_extract, List.extract_eq_take_drop]
    have hsub : s + p.size - s = p.size := by omega
    rw [hsub]
    have htake := List.prefix_iff_eq_take.mp hpref
    rw [Array.length_toList] at htake
    exact htake.symm

/-- For `i < t.size`, `p.toList` is a suffix of `t.toList.take (i + 1)` iff
`p.size ≤ i + 1` and `p` matches `t` at shift `i + 1 - p.size`. -/
theorem toList_isSuffix_take_iff_isMatchAt {α : Type*} {p t : Array α} {i : ℕ}
    (hit : i < t.size) :
    p.toList <:+ t.toList.take (i + 1) ↔
      p.size ≤ i + 1 ∧ IsMatchAt p t (i + 1 - p.size) := by
  rw [isMatchAt_iff_toList]
  constructor
  · intro hsuf
    have hlen_le : p.toList.length ≤ (t.toList.take (i + 1)).length := hsuf.length_le
    rw [Array.length_toList, List.length_take_of_le (by rw [Array.length_toList]; omega)] at hlen_le
    refine ⟨hlen_le, ⟨by omega, ?_⟩⟩
    set s := i + 1 - p.size
    have hsplit : i + 1 = s + p.size := by omega
    have htake_add : t.toList.take (s + p.size) =
        t.toList.take s ++ (t.toList.drop s).take p.size := List.take_add
    rw [hsplit, htake_add] at hsuf
    obtain ⟨u, hu⟩ := hsuf
    have hplen : u.length = (t.toList.take s).length := by
      have h := congrArg List.length hu
      simp only [List.length_append, Array.length_toList, List.length_take,
         List.length_drop] at h ⊢
      omega
    obtain ⟨_, hmatch⟩ := List.append_inj hu hplen
    rw [List.prefix_iff_eq_take, Array.length_toList]
    exact hmatch
  · rintro ⟨hlen_le, _, hpref⟩
    set s := i + 1 - p.size
    have hsplit : i + 1 = s + p.size := by omega
    have htake_eq : p.toList = (t.toList.drop s).take p.size := by
      have h := List.prefix_iff_eq_take.mp hpref
      rwa [Array.length_toList] at h
    rw [hsplit, List.take_add, ← htake_eq]
    exact ⟨t.toList.take s, rfl⟩

/-! ## KMP automaton transition (`advanceM`) -/

/-- Single-character transition of the KMP automaton on pattern `p` with failure table `pi`,
charging `1` `TimeM` tick per character comparison `p[k] = c`. -/
def advanceM {α : Type*} [DecidableEq α] (p : Array α) (pi : Array ℕ) (k : ℕ) (c : α) :
    TimeM ℕ ℕ :=
  if hk : k < p.size then
    if p[k]'hk = c then do
      ✓ return k + 1
    else if k = 0 then do
      ✓ return 0
    else do
      ✓ if hpi : k - 1 < pi.size then
          if _hlt : pi[k - 1]'hpi < k then
            advanceM p pi (pi[k - 1]'hpi) c
          else
            return 0
        else
          return 0
  else
    return 0
termination_by k

/-- Amortized potential bound for `advanceM` with potential $\Phi = k$:
comparisons plus new state never exceed `k + 2`. -/
theorem advanceM_time_add_ret_le {α : Type*} [DecidableEq α]
    (p : Array α) (pi : Array ℕ) (k : ℕ) (c : α) :
    (advanceM p pi k c).time + (advanceM p pi k c).ret ≤ k + 2 := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rw [advanceM]
    split_ifs with hk hmatch hk0 hpi hlt
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, TimeM.ret_bind,
        TimeM.ret_pure]
      omega
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, TimeM.ret_bind,
        TimeM.ret_pure]
      omega
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.ret_bind]
      have hsub := ih (pi[k - 1]'hpi) hlt
      omega
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, TimeM.ret_bind,
        TimeM.ret_pure]
      omega
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, TimeM.ret_bind,
        TimeM.ret_pure]
      omega
    · simp only [TimeM.time_pure, TimeM.ret_pure]
      omega

/-- Under a valid partial prefix table `IsPrefixTableFor p pi` covering `k ≤ pi.size` with
`k < p.size`, `advanceM` computes `nextLen p.toList k c`. -/
theorem ret_advanceM_eq_nextLen {α : Type*} [DecidableEq α]
    {p : Array α} {pi : Array ℕ} {k : ℕ} (c : α)
    (htab : IsPrefixTableFor p pi) (hkpi : k ≤ pi.size) (hkp : k < p.size) :
    (advanceM p pi k c).ret = nextLen p.toList k c := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have hklist : k < p.toList.length := by simpa only [Array.length_toList] using hkp
    have hget : p[k]'hkp = p.toList[k]'hklist := (Array.getElem_toList hkp).symm
    rw [advanceM, nextLen]
    simp only [hkp, hklist, ↓reduceDIte, hget]
    split_ifs with hmatch hk0 hpi hlt
    · simp only [TimeM.ret_bind, TimeM.ret_pure]
    · simp only [TimeM.ret_bind, TimeM.ret_pure]
    · have hsub1 : k - 1 + 1 = k := by omega
      have hval : pi[k - 1]'hpi = borderLen p.toList k := by
        simpa only [hsub1] using htab.2 (k - 1) hpi
      simp only [TimeM.ret_bind]
      rw [hval] at hlt ⊢
      exact ih (borderLen p.toList k) hlt (by omega) (by omega)
    · have hsub1 : k - 1 + 1 = k := by omega
      have hval : pi[k - 1]'hpi = borderLen p.toList k := by
        simpa only [hsub1] using htab.2 (k - 1) hpi
      have hpne : p.toList ≠ [] := by
        intro hnil
        simp only [hnil, List.length_nil] at hklist
        omega
      have hblt : borderLen p.toList k < k := borderLen_lt (by omega) hpne
      exact False.elim (hlt (hval ▸ hblt))
    · omega

/-! ## Failure-table construction (`computePrefixM`, `computePrefix`) -/

private def computePrefixLoopM {α : Type*} [DecidableEq α] (p : Array α)
    (q : ℕ) (k : ℕ) (pi : Array ℕ) : TimeM ℕ (Array ℕ) :=
  if hq : q < p.size then do
    let k' ← advanceM p pi k (p[q]'hq)
    computePrefixLoopM p (q + 1) k' (pi.push k')
  else
    return pi
termination_by p.size - q

/-- Construct the KMP failure table of `p` in `TimeM ℕ`, charging `1` tick per character
comparison (`[KnuthMorrisPratt1977]`; `[CLRS2009]`, Section 32.4). -/
def computePrefixM {α : Type*} [DecidableEq α] (p : Array α) : TimeM ℕ (Array ℕ) :=
  if p.size = 0 then
    return #[]
  else
    computePrefixLoopM p 1 0 #[0]

/-- Pure KMP failure table `(computePrefixM p).ret`. -/
@[expose] def computePrefix {α : Type*} [DecidableEq α] (p : Array α) : Array ℕ :=
  (computePrefixM p).ret

theorem ret_computePrefixM {α : Type*} [DecidableEq α] (p : Array α) :
    (computePrefixM p).ret = computePrefix p := rfl

private theorem computePrefixLoopM_time_le {α : Type*} [DecidableEq α]
    (p : Array α) (q k : ℕ) (pi : Array ℕ) :
    (computePrefixLoopM p q k pi).time ≤ k + 2 * (p.size - q) := by
  generalize hrem : p.size - q = rem
  induction rem generalizing q k pi with
  | zero =>
    rw [computePrefixLoopM]
    have hnot : ¬ (q < p.size) := by omega
    simp only [hnot, ↓reduceDIte, TimeM.time_pure]
    omega
  | succ rem ih =>
    have hq : q < p.size := by omega
    rw [computePrefixLoopM]
    simp only [hq, ↓reduceDIte, TimeM.time_bind]
    have hadv := advanceM_time_add_ret_le p pi k (p[q]'hq)
    set k' := (advanceM p pi k (p[q]'hq)).ret
    have hsub := ih (q + 1) k' (pi.push k') (by omega)
    omega

/-- `computePrefixM p` performs at most `2 * (p.size - 1)` character comparisons
(`[KnuthMorrisPratt1977]`, Section 2; `[CLRS2009]`, Section 32.4). -/
theorem computePrefixM_time_le {α : Type*} [DecidableEq α] (p : Array α) :
    (computePrefixM p).time ≤ 2 * (p.size - 1) := by
  unfold computePrefixM
  split_ifs with hp0
  · simp only [TimeM.time_pure]
    omega
  · simpa only [Nat.zero_add] using computePrefixLoopM_time_le p 1 0 #[0]

private theorem computePrefixLoopM_spec {α : Type*} [DecidableEq α]
    {p : Array α} {q k : ℕ} {pi : Array ℕ}
    (hq1 : 1 ≤ q) (hqp : q ≤ p.size) (hsize : pi.size = q)
    (htab : IsPrefixTableFor p pi) (hk : k = borderLen p.toList q) :
    (computePrefixLoopM p q k pi).ret.size = p.size ∧
      IsPrefixTableFor p (computePrefixLoopM p q k pi).ret := by
  generalize hrem : p.size - q = rem
  induction rem generalizing q k pi with
  | zero =>
    have hqe : q = p.size := by omega
    subst hqe
    rw [computePrefixLoopM]
    simp only [Nat.lt_irrefl, ↓reduceDIte, TimeM.ret_pure]
    exact ⟨hsize, htab⟩
  | succ rem ih =>
    have hqlt : q < p.size := by omega
    have hqlist : q < p.toList.length := by simpa only [Array.length_toList] using hqlt
    have hpne : p.toList ≠ [] := by
      intro hnil
      simp only [hnil, List.length_nil] at hqlist
      omega
    have hklt_q : k < q := hk ▸ borderLen_lt (by omega) hpne
    have hadv_eq : (advanceM p pi k (p[q]'hqlt)).ret = borderLen p.toList (q + 1) := by
      rw [ret_advanceM_eq_nextLen (p[q]'hqlt) htab (by omega) (by omega), hk]
      have hget : p[q]'hqlt = p.toList[q]'hqlist := (Array.getElem_toList hqlt).symm
      rw [hget, ← borderLen_succ hq1 hqlist]
    set k' := (advanceM p pi k (p[q]'hqlt)).ret
    have htab' : IsPrefixTableFor p (pi.push k') := by
      refine ⟨by simp only [Array.size_push]; omega, fun j hj => ?_⟩
      simp only [Array.size_push] at hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (by omega : j < q + 1)) with hjlt | rfl
      · rw [Array.getElem_push_lt (hsize ▸ hjlt)]
        exact htab.2 j (hsize ▸ hjlt)
      · have hj_eq : j = pi.size := hsize.symm
        subst hj_eq
        rw [Array.getElem_push_eq, hsize]
        exact hadv_eq
    rw [computePrefixLoopM]
    simp only [hqlt, ↓reduceDIte, TimeM.ret_bind]
    exact ih (by omega) (by omega) (by simp only [Array.size_push, hsize]) htab' hadv_eq (by omega)

theorem isPrefixTableFor_computePrefix {α : Type*} [DecidableEq α] (p : Array α) :
    (computePrefix p).size = p.size ∧ IsPrefixTableFor p (computePrefix p) := by
  unfold computePrefix computePrefixM
  split_ifs with hp0
  · simp only [TimeM.ret_pure]
    refine ⟨by simp only [Array.size_empty, hp0],
      ⟨by simp only [Array.size_empty, Nat.zero_le], ?_⟩⟩
    intro j hj
    simp only [Array.size_empty] at hj
    omega
  · have hsz0 : #[0].size = 1 := rfl
    have htab0 : IsPrefixTableFor p #[0] := by
      refine ⟨by rw [hsz0]; omega, fun j hj => ?_⟩
      have hj0 : j = 0 := by rw [hsz0] at hj; omega
      subst hj0
      simp only [Nat.zero_add, borderLen_one]
      rfl
    exact computePrefixLoopM_spec (by omega) (by omega) hsz0 htab0 (borderLen_one p.toList).symm

@[simp]
theorem computePrefix_size {α : Type*} [DecidableEq α] (p : Array α) :
    (computePrefix p).size = p.size :=
  (isPrefixTableFor_computePrefix p).1

theorem getElem_computePrefix {α : Type*} [DecidableEq α] (p : Array α)
    (q : ℕ) (hq : q < (computePrefix p).size) :
    (computePrefix p)[q]'hq = borderLen p.toList (q + 1) :=
  (isPrefixTableFor_computePrefix p).2.2 q hq

theorem isDecreasingTable_computePrefix {α : Type*} [DecidableEq α] (p : Array α) :
    IsDecreasingTable (computePrefix p) :=
  (isPrefixTableFor_computePrefix p).2.isDecreasingTable

/-! ## KMP exact string matching (`kmpSearchWithPrefixM`, `kmpSearchM`, `kmpMatches`) -/

private def resetFullMatch (pSize : ℕ) (pi : Array ℕ) : ℕ :=
  if h : pSize - 1 < pi.size then pi[pSize - 1]'h else 0

private theorem resetFullMatch_le {pSize : ℕ} {pi : Array ℕ} (hdec : IsDecreasingTable pi) :
    resetFullMatch pSize pi ≤ pSize := by
  unfold resetFullMatch
  split_ifs with h
  · have hle := hdec (pSize - 1) h
    omega
  · omega

private def kmpSearchLoopM {α : Type*} [DecidableEq α] (p : Array α) (pi : Array ℕ)
    (t : Array α) (i : ℕ) (k : ℕ) : TimeM ℕ (List ℕ) :=
  if hi : i < t.size then do
    let k' ← advanceM p pi k (t[i]'hi)
    if k' = p.size then
      let rest ← kmpSearchLoopM p pi t (i + 1) (resetFullMatch p.size pi)
      return (i + 1 - p.size) :: rest
    else
      kmpSearchLoopM p pi t (i + 1) k'
  else
    return []
termination_by t.size - i

/-- Exact KMP string matching in `TimeM ℕ` using a precomputed failure table `pi`
(`[KnuthMorrisPratt1977]`; `[CLRS2009]`, Section 32.4).
Returns all `0`-indexed match shifts in strictly increasing order; when `p.size = 0`, returns
`List.range (t.size + 1)` with `0` character comparisons. -/
def kmpSearchWithPrefixM {α : Type*} [DecidableEq α] (p : Array α) (pi : Array ℕ)
    (t : Array α) : TimeM ℕ (List ℕ) :=
  if p.size = 0 then
    return List.range (t.size + 1)
  else
    kmpSearchLoopM p pi t 0 0

/-- End-to-end KMP string matching in `TimeM ℕ`: builds the failure table via `computePrefixM p`
and scans `t` via `kmpSearchWithPrefixM` (`[KnuthMorrisPratt1977]`, Sections 1–2;
`[CLRS2009]`, Section 32.4). -/
def kmpSearchM {α : Type*} [DecidableEq α] (p t : Array α) : TimeM ℕ (List ℕ) := do
  let pi ← computePrefixM p
  kmpSearchWithPrefixM p pi t

/-- Pure KMP exact string matcher returning all `0`-indexed match shifts of `p` in `t` in strictly
increasing order. -/
@[expose] def kmpMatches {α : Type*} [DecidableEq α] (p t : Array α) : List ℕ :=
  (kmpSearchM p t).ret

/-- Pure KMP exact string matcher on `List α`. -/
@[expose] def kmpMatchesList {α : Type*} [DecidableEq α] (p t : List α) : List ℕ :=
  kmpMatches p.toArray t.toArray

theorem ret_kmpSearchM {α : Type*} [DecidableEq α] (p t : Array α) :
    (kmpSearchM p t).ret = kmpMatches p t := rfl

private theorem kmpSearchLoopM_time_le {α : Type*} [DecidableEq α]
    (p : Array α) {pi : Array ℕ} (hdec : IsDecreasingTable pi) (t : Array α) (i k : ℕ) :
    (kmpSearchLoopM p pi t i k).time ≤ k + 2 * (t.size - i) := by
  generalize hrem : t.size - i = rem
  induction rem generalizing i k with
  | zero =>
    rw [kmpSearchLoopM]
    have hnot : ¬ (i < t.size) := by omega
    simp only [hnot, ↓reduceDIte, TimeM.time_pure]
    omega
  | succ rem ih =>
    have hi : i < t.size := by omega
    rw [kmpSearchLoopM]
    simp only [hi, ↓reduceDIte, TimeM.time_bind]
    have hadv := advanceM_time_add_ret_le p pi k (t[i]'hi)
    set k' := (advanceM p pi k (t[i]'hi)).ret
    split_ifs with hfull
    · simp only [TimeM.time_bind, TimeM.time_pure]
      have hkNext_le : resetFullMatch p.size pi ≤ k' := hfull ▸ resetFullMatch_le hdec
      have hsub := ih (i + 1) (resetFullMatch p.size pi) (by omega)
      omega
    · have hsub := ih (i + 1) k' (by omega)
      omega

/-- With any decreasing failure table `pi` (such as `computePrefix p`), `kmpSearchWithPrefixM`
performs at most `2 * t.size` character comparisons. -/
theorem kmpSearchWithPrefixM_time_le {α : Type*} [DecidableEq α]
    (p : Array α) {pi : Array ℕ} (hdec : IsDecreasingTable pi) (t : Array α) :
    (kmpSearchWithPrefixM p pi t).time ≤ 2 * t.size := by
  unfold kmpSearchWithPrefixM
  split_ifs with hp0
  · simp only [TimeM.time_pure]
    omega
  · simpa only [Nat.zero_add, Nat.sub_zero] using kmpSearchLoopM_time_le p hdec t 0 0

/-- End-to-end KMP character-comparison bound (`[KnuthMorrisPratt1977]`, Sections 1–2;
`[CLRS2009]`, Section 32.4):
`(kmpSearchM p t).time ≤ 2 * (p.size - 1) + 2 * t.size`. -/
theorem kmpSearchM_time_le {α : Type*} [DecidableEq α] (p t : Array α) :
    (kmpSearchM p t).time ≤ 2 * (p.size - 1) + 2 * t.size := by
  unfold kmpSearchM
  simp only [TimeM.time_bind, ret_computePrefixM]
  have h1 := computePrefixM_time_le p
  have h2 := kmpSearchWithPrefixM_time_le p (isDecreasingTable_computePrefix p) t
  omega

private theorem kmpSearchLoopM_spec {α : Type*} [DecidableEq α]
    {p : Array α} {pi : Array ℕ} {t : Array α} {i k : ℕ}
    (hp : 0 < p.size) (hp_pi : pi.size = p.size) (htab : IsPrefixTableFor p pi)
    (hit : i ≤ t.size)
    (hk : k = maxPrefixSuffixUpTo p.toList (t.toList.take i) (p.size - 1)) :
    (∀ s, s ∈ (kmpSearchLoopM p pi t i k).ret ↔ i + 1 ≤ s + p.size ∧ IsMatchAt p t s) ∧
      (kmpSearchLoopM p pi t i k).ret.Pairwise (· < ·) := by
  generalize hrem : t.size - i = rem
  induction rem generalizing i k with
  | zero =>
    have hie : i = t.size := by omega
    subst hie
    rw [kmpSearchLoopM]
    simp only [Nat.lt_irrefl, ↓reduceDIte, TimeM.ret_pure, List.not_mem_nil, false_iff,
      List.Pairwise.nil, and_true]
    rintro s ⟨hge, hs_le, _⟩
    omega
  | succ rem ih =>
    have hilt : i < t.size := by omega
    have hilt_list : i < t.toList.length := by simpa only [Array.length_toList] using hilt
    have hplist : 0 < p.toList.length := by simpa only [Array.length_toList] using hp
    have hkp : k < p.size := by
      have hbound := maxPrefixSuffixUpTo_le_bound p.toList (t.toList.take i) (p.size - 1)
      omega
    have hadv_eq : (advanceM p pi k (t[i]'hilt)).ret =
        maxPrefixSuffixUpTo p.toList (t.toList.take (i + 1)) p.size := by
      rw [ret_advanceM_eq_nextLen (t[i]'hilt) htab (by omega) hkp, hk]
      have hget : t[i]'hilt = t.toList[i]'hilt_list := (Array.getElem_toList hilt).symm
      have htake : t.toList.take (i + 1) = t.toList.take i ++ [t.toList[i]'hilt_list] := by
        rw [List.take_add_one, getElem?_pos t.toList i hilt_list, Option.toList_some]
      have hpsub : (p.size - 1) + 1 = p.size := by omega
      have hstep := maxPrefixSuffixUpTo_append_singleton p.toList (t.toList.take i)
        (t.toList[i]'hilt_list) (B := p.size - 1) (by rw [Array.length_toList]; omega)
      rw [hget, htake, ← hpsub]
      exact hstep.symm
    set k' := (advanceM p pi k (t[i]'hilt)).ret
    rw [kmpSearchLoopM]
    simp only [hilt, ↓reduceDIte, TimeM.ret_bind]
    split_ifs with hfull
    · have hfull_max : maxPrefixSuffixUpTo p.toList (t.toList.take (i + 1)) p.toList.length =
          p.toList.length := by
        simpa only [Array.length_toList, hadv_eq.symm] using hfull
      have hpsuf : p.toList <:+ t.toList.take (i + 1) := by
        have h := take_maxPrefixSuffixUpTo_isSuffix p.toList (t.toList.take (i + 1)) p.toList.length
        rwa [hfull_max, List.take_length] at h
      obtain ⟨hple_i1, hmatch_here⟩ := (toList_isSuffix_take_iff_isMatchAt hilt).mp hpsuf
      have hpi_idx : p.size - 1 < pi.size := by omega
      simp only [TimeM.ret_bind, TimeM.ret_pure]
      have hkNext_eq : resetFullMatch p.size pi =
          maxPrefixSuffixUpTo p.toList (t.toList.take (i + 1)) (p.size - 1) := by
        unfold resetFullMatch
        simp only [hpi_idx, ↓reduceDIte, htab.2 (p.size - 1) hpi_idx]
        have hsub1 : p.size - 1 + 1 = p.toList.length := by
          rw [Array.length_toList]; omega
        rw [hsub1, ← maxPrefixSuffixUpTo_pred_of_eq_length hplist hfull_max, Array.length_toList]
      obtain ⟨hmem_rest, hpw_rest⟩ := ih (by omega) hkNext_eq (by omega)
      refine ⟨fun s => ?_, List.Pairwise.cons (fun s hs => ?_) hpw_rest⟩
      · simp only [List.mem_cons, hmem_rest]
        constructor
        · rintro (rfl | ⟨hge, hm⟩)
          · exact ⟨by omega, hmatch_here⟩
          · exact ⟨by omega, hm⟩
        · rintro ⟨hge, hm⟩
          rcases Nat.eq_or_lt_of_le hge with heq | hgt
          · left; omega
          · right; exact ⟨by omega, hm⟩
      · obtain ⟨hge, _⟩ := (hmem_rest s).mp hs
        omega
    · have hk'_le : k' ≤ p.size := by
        rw [hadv_eq, ← Array.length_toList (xs := p)]
        exact maxPrefixSuffixUpTo_le_length _ _ _
      have hk'_lt : maxPrefixSuffixUpTo p.toList (t.toList.take (i + 1)) p.toList.length <
          p.toList.length := by
        rw [Array.length_toList, ← hadv_eq]
        omega
      have hk'_pred : k' = maxPrefixSuffixUpTo p.toList (t.toList.take (i + 1)) (p.size - 1) := by
        rw [hadv_eq]
        have h := maxPrefixSuffixUpTo_pred_of_lt_length hk'_lt
        simpa only [Array.length_toList] using h.symm
      have hnot_suf : ¬ (p.toList <:+ t.toList.take (i + 1)) := by
        intro hsuf
        have hle := le_maxPrefixSuffixUpTo (B := p.toList.length) (Nat.le_refl _) (Nat.le_refl _)
          (by simpa only [List.take_length] using hsuf)
        omega
      obtain ⟨hmem_rest, hpw_rest⟩ := ih (by omega) hk'_pred (by omega)
      refine ⟨fun s => ?_, hpw_rest⟩
      rw [hmem_rest]
      constructor
      · rintro ⟨hge, hm⟩
        exact ⟨by omega, hm⟩
      · rintro ⟨hge, hm⟩
        rcases Nat.eq_or_lt_of_le hge with heq | hgt
        · exfalso
          have hs_eq : s = i + 1 - p.size := by omega
          subst hs_eq
          exact hnot_suf ((toList_isSuffix_take_iff_isMatchAt hilt).mpr ⟨by omega, hm⟩)
        · exact ⟨by omega, hm⟩

theorem kmpSearchWithPrefixM_spec {α : Type*} [DecidableEq α]
    {p : Array α} {pi : Array ℕ} (t : Array α)
    (hsize : pi.size = p.size) (htab : IsPrefixTableFor p pi) :
    (∀ s, s ∈ (kmpSearchWithPrefixM p pi t).ret ↔ IsMatchAt p t s) ∧
      (kmpSearchWithPrefixM p pi t).ret.Pairwise (· < ·) := by
  unfold kmpSearchWithPrefixM
  split_ifs with hp0
  · simp only [TimeM.ret_pure, List.mem_range]
    refine ⟨fun s => ?_, List.pairwise_lt_range⟩
    unfold IsMatchAt
    have hp_empty : p = #[] := Array.eq_empty_of_size_eq_zero hp0
    subst hp_empty
    simp only [Array.size_empty, Nat.add_zero]
    constructor
    · intro hlt
      exact ⟨by omega, Array.extract_empty_of_stop_le_start (Nat.le_refl s)⟩
    · rintro ⟨hle, _⟩
      omega
  · have hp_pos : 0 < p.size := by omega
    have hk0 : 0 = maxPrefixSuffixUpTo p.toList (t.toList.take 0) (p.size - 1) := by
      apply eq_maxPrefixSuffixUpTo_iff.mpr
      refine ⟨Nat.zero_le _, Nat.zero_le _, List.nil_suffix, fun k hk0 _ hkp hsuf => ?_⟩
      simp only [List.take_zero] at hsuf
      have hlen := hsuf.length_le
      simp only [List.length_take, List.length_nil] at hlen
      omega
    obtain ⟨hmem, hpw⟩ := kmpSearchLoopM_spec hp_pos hsize htab (Nat.zero_le _) hk0
    refine ⟨fun s => ?_, hpw⟩
    rw [hmem]
    exact ⟨fun ⟨_, hm⟩ => hm, fun hm => ⟨by omega, hm⟩⟩

/-- Unconditional soundness and completeness of `kmpMatches` (`[KnuthMorrisPratt1977]`,
Sections 1–2; `[CLRS2009]`, Section 32.4):
`s ∈ kmpMatches p t` iff `p` occurs in `t` at shift `s`. -/
theorem mem_kmpMatches_iff {α : Type*} [DecidableEq α] (p t : Array α) (s : ℕ) :
    s ∈ kmpMatches p t ↔ IsMatchAt p t s := by
  unfold kmpMatches kmpSearchM
  simp only [TimeM.ret_bind, ret_computePrefixM]
  obtain ⟨hsize, htab⟩ := isPrefixTableFor_computePrefix p
  exact (kmpSearchWithPrefixM_spec t hsize htab).1 s

/-- `kmpMatches p t` lists all match shifts in strictly increasing order. -/
theorem pairwise_lt_kmpMatches {α : Type*} [DecidableEq α] (p t : Array α) :
    (kmpMatches p t).Pairwise (· < ·) := by
  unfold kmpMatches kmpSearchM
  simp only [TimeM.ret_bind, ret_computePrefixM]
  obtain ⟨hsize, htab⟩ := isPrefixTableFor_computePrefix p
  exact (kmpSearchWithPrefixM_spec t hsize htab).2

/-- `kmpMatches p t` contains no duplicate shifts. -/
theorem nodup_kmpMatches {α : Type*} [DecidableEq α] (p t : Array α) :
    (kmpMatches p t).Nodup :=
  (pairwise_lt_kmpMatches p t).imp (fun h => Nat.ne_of_lt h)

/-- Soundness and completeness of `kmpMatchesList` on `List α`. -/
theorem mem_kmpMatchesList_iff {α : Type*} [DecidableEq α] (p t : List α) (s : ℕ) :
    s ∈ kmpMatchesList p t ↔ s ≤ t.length ∧ p <+: t.drop s := by
  rw [kmpMatchesList, mem_kmpMatches_iff, isMatchAt_iff_toList]
  simp only [List.size_toArray]
  constructor
  · rintro ⟨hs, hpref⟩
    exact ⟨by omega, hpref⟩
  · rintro ⟨hs, hpref⟩
    have hlen : p.length ≤ (t.drop s).length := hpref.length_le
    simp only [List.length_drop] at hlen
    exact ⟨by omega, hpref⟩

theorem pairwise_lt_kmpMatchesList {α : Type*} [DecidableEq α] (p t : List α) :
    (kmpMatchesList p t).Pairwise (· < ·) :=
  pairwise_lt_kmpMatches p.toArray t.toArray

theorem nodup_kmpMatchesList {α : Type*} [DecidableEq α] (p t : List α) :
    (kmpMatchesList p t).Nodup :=
  nodup_kmpMatches p.toArray t.toArray

end Cslib.Algorithms.Lean.KMP
