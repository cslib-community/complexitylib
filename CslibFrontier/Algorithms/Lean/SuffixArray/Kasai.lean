/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SuffixArray.Basic
public import Cslib.Algorithms.Lean.TimeM

/-!
# Kasai et al.'s linear-time LCP array construction

Given a word `w` and its suffix array `sa`, the algorithm of Kasai, Lee, Arimura, Arikawa and Park
(`[KasaiLeeArimuraArikawaPark2001]`) computes the LCP array by visiting the suffixes in text order
`i = 0, 1, …, |w| - 1`. It compares the suffix at `i` with its predecessor in `sa` starting from
the previous common-prefix length minus one, which the height lemma
(`IsSuffixArray.getElem_lcpArray_sub_one_le`) shows is already a common prefix. The common-prefix
length drops by at most one per step and never exceeds the remaining length, so the total number
of character comparisons is linear.

## Source Conventions

* **Indexing:** `0`-based positions and ranks, as in `Cslib.Algorithms.Lean.SuffixArray.Basic`;
  the result has `lcp[0] = 0`.
* **Rank array:** `rankArray w.size sa.toList` stores `r` at position `sa[r]`, the inverse
  permutation of `sa`.
* **Resource bounds:** `TimeM ℕ` counts exact character comparisons rather than asymptotic RAM
  steps; the bound `2 * |w|` holds for every input pair `(w, sa)`, valid suffix array or not.

## Cost Model

* **Charged (`1` `TimeM` tick):** every character equality comparison `w[j + h] = w[i + h]` in
  `extendM`.
* **Uncharged (`0` `TimeM` ticks):** construction of the rank array, array reads and writes
  (`sa[r]!`, `rk[i]!`, `Array.set!`), allocation of the output array, integer arithmetic, loop
  control and the conversions in the list wrapper `kasai`.

A call to `extendM` starting from a common prefix `h` makes at most `ret - h + 1` comparisons, at
most one of them a mismatch; the potential `min h (|w| - i)` then telescopes to at most `2 * |w|`
comparisons in total (`kasaiM_time_le`).

## Main definitions

* `Cslib.Algorithms.Lean.SuffixArray.rankArray`: inverse of a list of distinct positions.
* `Cslib.Algorithms.Lean.SuffixArray.extendM`: extend a known common prefix of two suffixes,
  one charged comparison per character.
* `Cslib.Algorithms.Lean.SuffixArray.kasaiM`, `kasai`: the LCP construction on arrays in
  `TimeM ℕ`, and its list wrapper.

## Main results

* `Cslib.Algorithms.Lean.SuffixArray.getElem!_rankArray`: `rankArray n sa` inverts `sa`.
* `Cslib.Algorithms.Lean.SuffixArray.ret_extendM`: `extendM w j i h` returns
  `h + List.lcpLen (w.drop (j + h)) (w.drop (i + h))`.
* `Cslib.Algorithms.Lean.SuffixArray.extendM_time_add_le`: one comparison per matched character
  plus at most one mismatch, and none when the extension reaches the end of the text
  (`extendM_time_add_le_of_size_le`).
* `Cslib.Algorithms.Lean.SuffixArray.ret_kasaiM` and `kasai_eq_lcpArray`: on a suffix array the
  algorithm returns the LCP array.
* `Cslib.Algorithms.Lean.SuffixArray.kasaiM_time_le`: at most `2 * |w|` character comparisons.

## References

* [T. Kasai, G. Lee, H. Arimura, S. Arikawa, and K. Park, *Linear-Time Longest-Common-Prefix
  Computation in Suffix Arrays and Its Applications*][KasaiLeeArimuraArikawaPark2001]
-/

public section

namespace Cslib.Algorithms.Lean.SuffixArray

open Cslib.Algorithms.Lean

variable {α : Type*}

/-! ## Kasai et al.: the algorithm -/

/-- Inverse of a list of positions: `rankArray n sa` has size `n` and stores `r` at position
`sa[r]`. -/
def rankArray (n : ℕ) (sa : List ℕ) : Array ℕ :=
  go sa 0 (Array.replicate n 0)
where
  /-- Store ranks `r, r + 1, …` at the positions listed in `l`. -/
  go : List ℕ → ℕ → Array ℕ → Array ℕ
    | [], _, rk => rk
    | i :: l, r, rk => go l (r + 1) (rk.set! i r)

private theorem rankArray_go_getElem?_of_not_mem (l : List ℕ) (r : ℕ) (rk : Array ℕ) {x : ℕ}
    (hx : x ∉ l) : (rankArray.go l r rk)[x]? = rk[x]? := by
  induction l generalizing r rk with
  | nil => rfl
  | cons i l ih =>
    rw [List.mem_cons, not_or] at hx
    rw [rankArray.go, ih _ _ hx.2, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp only [Ne.symm hx.1, ↓reduceIte]

private theorem size_rankArray_go (l : List ℕ) (r : ℕ) (rk : Array ℕ) :
    (rankArray.go l r rk).size = rk.size := by
  induction l generalizing r rk with
  | nil => rfl
  | cons i l ih => rw [rankArray.go, ih, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

private theorem rankArray_go_getElem? {l : List ℕ} (hl : l.Nodup) (r : ℕ) {rk : Array ℕ}
    (hlt : ∀ i ∈ l, i < rk.size) (k : ℕ) (hk : k < l.length) :
    (rankArray.go l r rk)[l[k]]? = some (r + k) := by
  induction l generalizing r rk k with
  | nil => simp only [List.length_nil] at hk; omega
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    have hi : i < rk.size := hlt i List.mem_cons_self
    rw [rankArray.go]
    cases k with
    | zero =>
      rw [List.getElem_cons_zero, rankArray_go_getElem?_of_not_mem _ _ _ hl.1,
        Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hi, Nat.add_zero]
    | succ k =>
      rw [List.getElem_cons_succ, ih hl.2 (r + 1) (fun j hj => by
        rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
        exact hlt j (List.mem_cons_of_mem i hj)) k (by simp only [List.length_cons] at hk; omega)]
      congr 1
      omega

@[simp] theorem size_rankArray (n : ℕ) (sa : List ℕ) : (rankArray n sa).size = n := by
  rw [rankArray, size_rankArray_go, Array.size_replicate]

/-- `rankArray n sa` inverts `sa` when `sa` lists distinct positions below `n`. -/
theorem getElem!_rankArray {n : ℕ} {sa : List ℕ} (hnd : sa.Nodup) (hlt : ∀ i ∈ sa, i < n)
    {r : ℕ} (hr : r < sa.length) : (rankArray n sa)[sa[r]]! = r := by
  have h := rankArray_go_getElem? hnd 0 (rk := Array.replicate n 0)
    (fun i hi => by rw [Array.size_replicate]; exact hlt i hi) r hr
  rw [Nat.zero_add] at h
  have hlt' : sa[r] < (rankArray n sa).size := by
    rw [size_rankArray]; exact hlt _ (List.getElem_mem hr)
  rw [getElem!_pos (rankArray n sa) sa[r] hlt']
  have h' : (rankArray n sa)[sa[r]]? = some r := by rw [rankArray]; exact h
  rw [getElem?_pos (rankArray n sa) sa[r] hlt'] at h'
  exact Option.some.inj h'

section Algorithm

variable [DecidableEq α]

/-- Starting from a known common prefix length `h`, extend the common prefix of the suffixes
of `w` at positions `j` and `i` one character at a time, charging one tick per character
comparison. -/
def extendM (w : Array α) (j i h : ℕ) : TimeM ℕ ℕ :=
  if hlt : j + h < w.size ∧ i + h < w.size then do
    ✓ if w[j + h]'hlt.1 = w[i + h]'hlt.2 then
        extendM w j i (h + 1)
      else
        return h
  else
    return h
termination_by w.size - (i + h)

/-- The main loop of `kasaiM` at text position `i`, with current common-prefix length `h`. -/
private def kasaiLoopM (w : Array α) (sa rk : Array ℕ) (i h : ℕ) (lcp : Array ℕ) :
    TimeM ℕ (Array ℕ) :=
  if hi : i < w.size then
    if rk[i]! = 0 then
      kasaiLoopM w sa rk (i + 1) h lcp
    else do
      let h' ← extendM w sa[rk[i]! - 1]! i h
      kasaiLoopM w sa rk (i + 1) (h' - 1) (lcp.set! rk[i]! h')
  else
    return lcp
termination_by w.size - i

/-- Kasai et al.'s LCP construction in `TimeM ℕ`, charging one tick per character comparison:
visit the positions `i = 0, 1, …` in text order, extend the common prefix of the suffix at `i`
and its predecessor in `sa` from the previous length minus one, and record it at rank `rank[i]`.
-/
def kasaiM (w : Array α) (sa : Array ℕ) : TimeM ℕ (Array ℕ) :=
  kasaiLoopM w sa (rankArray w.size sa.toList) 0 0 (Array.replicate w.size 0)

/-- Kasai et al.'s LCP construction on lists. -/
def kasai (w : List α) (sa : List ℕ) : List ℕ :=
  (kasaiM w.toArray sa.toArray).ret.toList

/-! ## Character comparisons -/

/-- `extendM` makes one comparison per matched character plus at most one mismatch. -/
theorem extendM_time_add_le (w : Array α) (j i h : ℕ) :
    (extendM w j i h).time + h ≤ (extendM w j i h).ret + 1 := by
  generalize hk : w.size - (i + h) = k
  induction k generalizing h with
  | zero =>
    rw [extendM]
    simp only [show ¬(j + h < w.size ∧ i + h < w.size) by omega, ↓reduceDIte, TimeM.time_pure,
      TimeM.ret_pure]
    omega
  | succ k ih =>
    rw [extendM]
    split_ifs with hlt heq
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.ret_bind]
      have := ih (h + 1) (by omega)
      omega
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, TimeM.ret_bind,
        TimeM.ret_pure]
      omega
    · simp only [TimeM.time_pure, TimeM.ret_pure]
      omega

/-- An extension that reaches the end of the suffix at `i` makes no mismatch comparison:
one comparison per matched character. -/
theorem extendM_time_add_le_of_size_le (w : Array α) (j i h : ℕ)
    (hend : w.size ≤ i + (extendM w j i h).ret) :
    (extendM w j i h).time + h ≤ (extendM w j i h).ret := by
  generalize hk : w.size - (i + h) = k
  induction k generalizing h with
  | zero =>
    rw [extendM] at hend ⊢
    simp only [show ¬(j + h < w.size ∧ i + h < w.size) by omega, ↓reduceDIte, TimeM.time_pure,
      TimeM.ret_pure] at hend ⊢
    omega
  | succ k ih =>
    rw [extendM] at hend ⊢
    split_ifs at hend ⊢ with hlt heq
    · simp only [TimeM.time_bind, TimeM.time_tick, TimeM.ret_bind] at hend ⊢
      have := ih (h + 1) hend (by omega)
      omega
    · simp only [TimeM.ret_bind, TimeM.ret_pure] at hend
      omega
    · simp only [TimeM.time_pure, TimeM.ret_pure]
      omega

/-- Extending the common prefix of the suffixes at `j` and `i` from `h` yields
`h + List.lcpLen (w.drop (j + h)) (w.drop (i + h))`. -/
theorem ret_extendM (w : Array α) (j i h : ℕ) :
    (extendM w j i h).ret = h + List.lcpLen (w.toList.drop (j + h)) (w.toList.drop (i + h)) := by
  generalize hk : w.size - (i + h) = k
  induction k generalizing h with
  | zero =>
    rw [extendM]
    simp only [show ¬(j + h < w.size ∧ i + h < w.size) by omega, ↓reduceDIte, TimeM.ret_pure]
    have := List.lcpLen_le_length_right (w.toList.drop (j + h)) (w.toList.drop (i + h))
    simp only [List.length_drop, Array.length_toList] at this
    omega
  | succ k ih =>
    rw [extendM]
    split_ifs with hlt heq
    · simp only [TimeM.ret_bind]
      rw [ih (h + 1) (by omega),
        List.drop_eq_getElem_cons (i := j + h) (l := w.toList) (by simpa using hlt.1),
        List.drop_eq_getElem_cons (i := i + h) (l := w.toList) (by simpa using hlt.2),
        Array.getElem_toList, Array.getElem_toList, heq, List.lcpLen_cons_cons_self,
        show j + (h + 1) = j + h + 1 by omega, show i + (h + 1) = i + h + 1 by omega]
      omega
    · simp only [TimeM.ret_bind, TimeM.ret_pure]
      rw [List.drop_eq_getElem_cons (i := j + h) (l := w.toList) (by simpa using hlt.1),
        List.drop_eq_getElem_cons (i := i + h) (l := w.toList) (by simpa using hlt.2),
        Array.getElem_toList, Array.getElem_toList, List.lcpLen_cons_cons]
      simp only [heq, ↓reduceIte]
      omega
    · simp only [TimeM.ret_pure]
      have h1 := List.lcpLen_le_length_left (w.toList.drop (j + h)) (w.toList.drop (i + h))
      have h2 := List.lcpLen_le_length_right (w.toList.drop (j + h)) (w.toList.drop (i + h))
      simp only [List.length_drop, Array.length_toList] at h1 h2
      omega

/-- `extendM` never extends past the end of the suffix at `i`. -/
theorem ret_extendM_le (w : Array α) (j i h : ℕ) :
    (extendM w j i h).ret ≤ max h (w.size - i) := by
  rw [ret_extendM]
  have := List.lcpLen_le_length_right (w.toList.drop (j + h)) (w.toList.drop (i + h))
  simp only [List.length_drop, Array.length_toList] at this
  omega

/-- Amortized cost of the main loop, with potential `min h (|w| - i)`. -/
private theorem kasaiLoopM_time_add_le (w : Array α) (sa rk : Array ℕ) (i h : ℕ)
    (lcp : Array ℕ) :
    (kasaiLoopM w sa rk i h lcp).time + min h (w.size - i) ≤ 2 * (w.size - i) := by
  generalize hk : w.size - i = k
  induction k generalizing i h lcp with
  | zero =>
    rw [kasaiLoopM]
    simp only [show ¬(i < w.size) by omega, ↓reduceDIte, TimeM.time_pure]
    omega
  | succ k ih =>
    have hi : i < w.size := by omega
    rw [kasaiLoopM]
    simp only [hi, ↓reduceDIte]
    split_ifs with hr
    · have := ih (i + 1) h lcp (by omega)
      omega
    · simp only [TimeM.time_bind]
      have h1 := extendM_time_add_le w sa[rk[i]! - 1]! i h
      have h2 := ret_extendM_le w sa[rk[i]! - 1]! i h
      have := ih (i + 1) ((extendM w sa[rk[i]! - 1]! i h).ret - 1)
        (lcp.set! rk[i]! (extendM w sa[rk[i]! - 1]! i h).ret) (by omega)
      omega

/-- **Kasai et al.'s linear bound.** `kasaiM w sa` performs at most `2 * |w|` character
comparisons, for every input (including inputs where `sa` is not a suffix array). -/
theorem kasaiM_time_le (w : Array α) (sa : Array ℕ) : (kasaiM w sa).time ≤ 2 * w.size := by
  have := kasaiLoopM_time_add_le w sa (rankArray w.size sa.toList) 0 0
    (Array.replicate w.size 0)
  rw [kasaiM]
  omega

end Algorithm

/-! ## Correctness -/

section Correctness

variable [LinearOrder α]

/-- Loop invariant: `h` is a lower bound for the LCP entry of the suffix at `i`, and the entries
of all ranks whose suffixes start before `i` (and rank `0`) are already correct. -/
private theorem kasaiLoopM_spec {w : Array α} {sa rk : Array ℕ}
    (hsa : IsSuffixArray w.toList sa.toList)
    (hrk : ∀ (r : ℕ) (hr : r < sa.size), rk[sa[r]]! = r) {i h : ℕ} {lcp : Array ℕ}
    (hi : i ≤ w.size) (hsize : lcp.size = w.size)
    (hh : ∀ (r : ℕ) (hr : r < sa.size), sa[r] = i →
      h ≤ (lcpArray w.toList sa.toList)[r]'(by simpa using hr))
    (hdone : ∀ (r : ℕ) (hr : r < sa.size), (r = 0 ∨ sa[r] < i) →
      lcp[r]'(by have := hsa.length_eq; simp only [Array.length_toList] at this; omega) =
        (lcpArray w.toList sa.toList)[r]'(by simpa using hr)) :
    (kasaiLoopM w sa rk i h lcp).ret.toList = lcpArray w.toList sa.toList := by
  have hlen : sa.size = w.size := by
    have := hsa.length_eq; simp only [Array.length_toList] at this; exact this
  have hinj : ∀ (r r' : ℕ) (hr : r < sa.size) (hr' : r' < sa.size), sa[r] = sa[r'] → r = r' := by
    grind
  have hsalt : ∀ (r : ℕ) (hr : r < sa.size), sa[r] < w.size := by
    intro r hr
    have := hsa.getElem_lt (r := r) (by simpa using hr)
    simpa only [Array.getElem_toList, Array.length_toList] using this
  generalize hk : w.size - i = k
  induction k generalizing i h lcp with
  | zero =>
    rw [kasaiLoopM]
    simp only [show ¬(i < w.size) by omega, ↓reduceDIte, TimeM.ret_pure]
    apply List.ext_getElem (by simp only [Array.length_toList, length_lcpArray]; omega)
    intro r h1 h2
    simp only [Array.length_toList] at h1
    rw [Array.getElem_toList]
    exact hdone r (by omega) (Or.inr (by have := hsalt r (by omega); omega))
  | succ k ih =>
    have hiw : i < w.size := by omega
    rw [kasaiLoopM]
    simp only [hiw, ↓reduceDIte]
    obtain ⟨r, hr, hri⟩ := hsa.exists_getElem_eq (by simpa only [Array.length_toList] using hiw)
    simp only [Array.length_toList, Array.getElem_toList] at hr hri
    have hrki : rk[i]! = r := hri ▸ hrk r hr
    rw [hrki]
    split_ifs with hr0
    · subst hr0
      refine ih (by omega) hsize (fun r' hr' hr'i => ?_) (fun r' hr' hr'd => ?_) (by omega)
      · have h0 := hh 0 hr hri
        rw [getElem_lcpArray_zero] at h0
        omega
      · rcases hr'd with h0 | hlt
        · exact hdone r' hr' (Or.inl h0)
        · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with hlt | heq
          · exact hdone r' hr' (Or.inr hlt)
          · exact hdone r' hr' (Or.inl (hinj r' 0 hr' hr (heq.trans hri.symm)))
    · simp only [TimeM.ret_bind]
      have hr1 : r - 1 < sa.size := by omega
      rw [getElem!_pos sa (r - 1) hr1]
      obtain ⟨j, hj⟩ : ∃ j, sa[r - 1] = j := ⟨_, rfl⟩
      have hlcpr : (lcpArray w.toList sa.toList)[r]'(by simpa using hr) =
          List.lcpLen (w.toList.drop j) (w.toList.drop i) := by
        rw [getElem_lcpArray_of_pos _ _ _ (Nat.pos_of_ne_zero hr0)]
        simp only [Array.getElem_toList, hj, hri]
      have hhr := hh r hr hri
      rw [hlcpr] at hhr
      have hext : (extendM w sa[r - 1] i h).ret = (lcpArray w.toList sa.toList)[r]'(by
          simpa using hr) := by
        rw [hj, ret_extendM, hlcpr, List.lcpLen_eq_add_lcpLen_drop hhr, List.drop_drop,
          List.drop_drop]
      rw [hext]
      have hsize' : (lcp.set! r ((lcpArray w.toList sa.toList)[r]'(by simpa using hr))).size =
          w.size := by
        rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
        exact hsize
      refine ih (by omega) hsize' (fun r' hr' hr'i => ?_) (fun r' hr' hr'd => ?_) (by omega)
      · have := hsa.getElem_lcpArray_sub_one_le (r := r) (r' := r') (by simpa using hr)
          (by simpa using hr') (by simp only [Array.getElem_toList, hri, hr'i])
        exact this
      · simp only [Array.set!_eq_setIfInBounds]
        by_cases hrr : r = r'
        · subst hrr
          rw [Array.getElem_setIfInBounds_self]
        · rw [Array.getElem_setIfInBounds_ne (by omega) hrr]
          rcases hr'd with h0 | hlt
          · exact hdone r' hr' (Or.inl h0)
          · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with hlt | heq
            · exact hdone r' hr' (Or.inr hlt)
            · exact absurd (hinj r r' hr hr' (hri.trans heq.symm)) hrr

/-- **Correctness of Kasai et al.'s algorithm**: on a suffix array, `kasaiM` returns the LCP
array. -/
theorem ret_kasaiM {w : Array α} {sa : Array ℕ} (hsa : IsSuffixArray w.toList sa.toList) :
    (kasaiM w sa).ret.toList = lcpArray w.toList sa.toList := by
  have hlen : sa.size = w.size := by
    have := hsa.length_eq; simp only [Array.length_toList] at this; exact this
  refine kasaiLoopM_spec hsa (fun r hr => ?_) (Nat.zero_le _) Array.size_replicate
    (fun _ _ _ => Nat.zero_le _) (fun r hr hr0 => ?_)
  · have := getElem!_rankArray (n := w.size) hsa.nodup (fun i hi => by
      simpa only [Array.length_toList] using hsa.mem_iff.mp hi) (r := r) (by simpa using hr)
    simpa only [Array.getElem_toList] using this
  · rcases hr0 with rfl | hlt
    · rw [Array.getElem_replicate, getElem_lcpArray_zero]
    · omega

/-- **Correctness of Kasai et al.'s algorithm** on lists. -/
theorem kasai_eq_lcpArray {w : List α} {sa : List ℕ} (hsa : IsSuffixArray w sa) :
    kasai w sa = lcpArray w sa :=
  ret_kasaiM (w := w.toArray) (sa := sa.toArray) hsa

end Correctness

end Cslib.Algorithms.Lean.SuffixArray
