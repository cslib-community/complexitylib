/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TimeM.Loops
public import CslibFrontier.Foundations.BooleanAnalysis.CoveringProduct
public import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Trimmed Yates passes and selected entries of the subset convolution

Selected entries of the ranked subset convolution by the trimmed fast zeta transform, following
the proof of [ChanItakuraMaYu2026], Theorem 2.2 (Section 2.1), after
[BjorklundHusfeldtKaskiKoivisto2007] and the trimmed transform of
[BjorklundHusfeldtKaskiKoivisto2010] cited there.

Fix a duplicate-free list `l` of coordinates and a threshold `s`. Stage `k` of Yates's algorithm on
`F` is `yatesTransform c (l.take k) F`; its value at `X` reads stage `k - 1` only at `X` and at `X`
minus one coordinate.

* **Preprocessing** (`preprocessM`) runs every stage of the zeta transforms of `f` and `g`, of
  their pointwise product and of its Möbius transform on the *low* sets: the subsets of `l` with at
  most `s` elements (`layers l 0 s`), keeping every stage (`Tables`).
* **A query** `C` (`queryM`) runs the same stages on the *high* sets of `C`: its subsets with at
  least `s` elements (`layers (l.filter (· ∈ C)) s #C`). A value at a set with fewer than `s`
  elements is read from the preprocessed stage of the same index (`stagesM`).

The query returns the covering product `coveringProduct f g C`
(`ret_queryM_preprocessM`), which for ranked inputs and `#C = t₁ + t₂` is the subset convolution
(`ret_queryM_preprocessM_eq_subsetConvolution`). `solveM` answers a list of queries after one
preprocessing (`ret_solveM`).

## Cost model

* **Charged (`1` `TimeM` tick):** computing one table cell (`tabulateM`): either reading the
  input `f` or `g` at one set, multiplying two transform values, or one Yates pass at one set
  (`yatesPass`: one membership test, one or two table reads, one scalar multiplication and one
  addition). Each table read is one dictionary look-up keyed by a set, and includes the
  comparison `s ≤ #Y` deciding whether to read the current stage or the preprocessed one.
* **Uncharged:** enumerating the cells of a domain (`layers`), building the dictionary of a
  table, loop control, and selecting stages from the lists of tables.

This is a unit-cost model in which a set of coordinates of `l` is a key and a ring element is a
word, as in [ChanItakuraMaYu2026], footnote 7, which assumes a word RAM with words of at least
`d = l.length` bits and ignores dictionary look-ups costing `d ^ O(1)`. The inputs `f` and `g` are
given as look-up functions, so the term `n` of Theorem 2.2 (storing the `n` input sets) does not
appear. The counts are exact: preprocessing takes `3 * (l.length + 1)` ticks per low set
(`time_preprocessM`) and a query `3 * (l.length + 1)` ticks per high set (`time_queryM`), i.e.
`3 (d + 1) ∑_{j ≤ s} (d choose j)` and `3 (d + 1) ∑_{s ≤ j ≤ #C} (#C choose j)` ticks
(`time_preprocessM_eq_sum_choose`, `time_queryM_eq_sum_choose`). This gives Theorem 2.2's bound
`(binom(d, ≤ s) + |𝒞| binom(2t, ≥ s)) d ^ O(1)` with explicit constants (`time_solveM`).

## Main definitions

* `Cslib.Algorithms.Lean.TrimmedYates.tabulateM`: one tick per cell of a table.
* `Cslib.Algorithms.Lean.TrimmedYates.layers`: the subsets of a list with a given range of sizes.
* `Cslib.Algorithms.Lean.TrimmedYates.stagesM`: Yates's passes on a domain of sets, with a
  fallback table for small sets.
* `Cslib.Algorithms.Lean.TrimmedYates.Tables`, `preprocessM`, `queryM`, `solveM`: selected
  entries of the covering product.

## Main results

* `Cslib.Algorithms.Lean.TrimmedYates.getD_ret_stagesM`: correctness of the trimmed passes.
* `Cslib.Algorithms.Lean.TrimmedYates.ret_queryM_preprocessM`,
  `ret_queryM_preprocessM_eq_subsetConvolution`, `ret_solveM`: the queries return selected
  entries of the covering product, and of the subset convolution for ranked inputs.
* `Cslib.Algorithms.Lean.TrimmedYates.time_preprocessM_eq_sum_choose`,
  `time_queryM_eq_sum_choose`, `time_solveM`: exact tick counts.

## References

* [A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto, *Fourier meets Möbius: fast subset
  convolution*][BjorklundHusfeldtKaskiKoivisto2007]
* [A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto, *Trimmed Moebius inversion and graphs of
  bounded degree*][BjorklundHusfeldtKaskiKoivisto2010]
* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.TrimmedYates

open Finset Cslib.Algorithms.Lean.TimeM Cslib.BitString

/- A table `κ → M` and the list of its values are bound in one `TimeM` computation, so keys and
values share a universe. -/
universe u

/-! ### Tables -/

section Tabulate

variable {κ M : Type u} [DecidableEq κ] [Zero M]

/-- The table of `cell` on the keys `dom`, at one tick per key: a dictionary from each key of
`dom` to its value, read as `0` off `dom`. -/
@[expose] def tabulateM (dom : List κ) (cell : κ → M) : TimeM ℕ (κ → M) := do
  let vals : List M ← dom.mapM fun X => do ✓ pure (cell X)
  pure fun X : κ => ((dom.zip vals).lookup X).getD 0

private theorem lookup_zip_map {dom : List κ} (cell : κ → M) {X : κ} (hX : X ∈ dom) :
    ((dom.zip (dom.map cell)).lookup X).getD 0 = cell X := by
  induction dom with
  | nil => simp at hX
  | cons Y dom ih =>
    rw [List.map_cons, List.zip_cons_cons, List.lookup_cons]
    by_cases h : X = Y
    · subst h
      simp
    · rw [beq_false_of_ne h]
      exact ih ((List.mem_cons.mp hX).resolve_left h)

/-- The table of `cell` reads `cell X` at every key `X` of `dom`. -/
theorem ret_tabulateM {dom : List κ} (cell : κ → M) {X : κ} (hX : X ∈ dom) :
    (tabulateM dom cell).ret X = cell X := by
  simp only [tabulateM, ret_bind, ret_pure, ret_listMapM]
  exact lookup_zip_map cell hX

/-- A table costs one tick per key. -/
@[simp] theorem time_tabulateM (dom : List κ) (cell : κ → M) :
    (tabulateM dom cell).time = dom.length := by
  simp only [tabulateM, time_bind, time_pure, time_listMapM, time_tick, add_zero,
    List.map_const', List.sum_replicate, smul_eq_mul, mul_one]

end Tabulate

/-! ### Layers of subsets -/

section Layers

variable {ι : Type*} [DecidableEq ι]

/-- The subsets of the elements of `L` with at least `lo` and at most `hi` elements, layer by
layer, each as the set of a sublist of `L`. -/
@[expose] def layers (L : List ι) (lo hi : ℕ) : List (Finset ι) :=
  (List.range' lo (hi + 1 - lo)).flatMap fun j => (L.sublistsLen j).map List.toFinset

theorem mem_layers {L : List ι} (hL : L.Nodup) {lo hi : ℕ} {X : Finset ι} :
    X ∈ layers L lo hi ↔ X ⊆ L.toFinset ∧ lo ≤ #X ∧ #X ≤ hi := by
  simp only [layers, List.mem_flatMap, List.mem_range'_1, List.mem_map, List.mem_sublistsLen]
  constructor
  · rintro ⟨j, hj, L', ⟨hsub, hlen⟩, rfl⟩
    have hnd : L'.Nodup := hL.sublist hsub
    rw [List.toFinset_card_of_nodup hnd, hlen]
    exact ⟨fun x hx => List.mem_toFinset.mpr (hsub.subset (List.mem_toFinset.mp hx)),
      hj.1, by omega⟩
  · rintro ⟨hX, hlo, hhi⟩
    refine ⟨#X, ⟨hlo, by omega⟩, L.filter (· ∈ X), ⟨List.filter_sublist, ?_⟩, ?_⟩
    · rw [← List.toFinset_card_of_nodup (hL.filter _), List.toFinset_filter]
      congr 1
      ext x
      simp only [mem_filter, List.mem_toFinset, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hX h), h⟩⟩
    · ext x
      simp only [List.toFinset_filter, mem_filter, List.mem_toFinset, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hX h), h⟩⟩

/-- There are `∑_{lo ≤ j ≤ hi} (L.length choose j)` layered subsets. -/
theorem length_layers (L : List ι) (lo hi : ℕ) :
    (layers L lo hi).length = ∑ j ∈ Icc lo hi, L.length.choose j := by
  rw [layers, List.length_flatMap]
  simp only [List.length_map, List.length_sublistsLen]
  rw [← List.sum_toFinset _ List.nodup_range']
  congr 1
  ext j
  simp only [List.mem_toFinset, List.mem_range'_1, mem_Icc]
  omega

end Layers

/-! ### Trimmed passes -/

section Stages

variable {ι M : Type u} {R : Type*} [DecidableEq ι] [AddCommMonoid M] [Monoid R]
  [DistribMulAction R M]

/-- Yates's passes with coefficient `c` in the coordinates `l`, on the cells `dom`, returning
every stage: stage `0` is `t`, and stage `k + 1` is the pass in coordinate `k` of `l` applied to
stage `k`. A cell reads stage `k` at sets with at least `s` elements and the `k`-th table of `fb`
at smaller sets. -/
@[expose] def stagesM (c : R) (s : ℕ) (dom : List (Finset ι)) :
    List ι → List (Finset ι → M) → (Finset ι → M) → TimeM ℕ (List (Finset ι → M))
  | [], _, t => pure [t]
  | i :: l, fb, t => do
    let t' ← tabulateM dom (yatesPass c i fun Y => if s ≤ #Y then t Y else fb.headD 0 Y)
    let ts ← stagesM c s dom l fb.tail t'
    pure (t :: ts)

/-- The trimmed passes cost one tick per coordinate and cell. -/
@[simp] theorem time_stagesM (c : R) (s : ℕ) (dom : List (Finset ι)) :
    ∀ (l : List ι) (fb : List (Finset ι → M)) (t : Finset ι → M),
      (stagesM c s dom l fb t).time = l.length * dom.length
  | [], _, _ => by simp [stagesM]
  | i :: l, fb, t => by
    simp only [stagesM, time_bind, time_tabulateM, time_pure, add_zero, time_stagesM c s dom l,
      List.length_cons]
    ring

/-- **Correctness of the trimmed passes.** Suppose that every cell of `dom` has at least `s`
elements, that `t` agrees with `G` on `dom`, and that removing a coordinate of `l` from a cell gives
a cell or a set satisfying `P` with fewer than `s` elements. If the `k`-th table of `fb` agrees
with stage `k` of `G` on the sets satisfying `P` with fewer than `s` elements, then every returned
stage `k ≤ l.length` agrees with stage `k` of `G` on `dom`. -/
theorem getD_ret_stagesM (c : R) {s : ℕ} {dom : List (Finset ι)} (P : Finset ι → Prop)
    (hs : ∀ X ∈ dom, s ≤ #X)
    (hdom : ∀ X ∈ dom, ∀ i, i ∈ X → (s ≤ #(X.erase i) → X.erase i ∈ dom) ∧
      (#(X.erase i) < s → P (X.erase i))) :
    ∀ (l : List ι) (fb : List (Finset ι → M)) (t G : Finset ι → M),
      (∀ X ∈ dom, t X = G X) →
      (∀ k < l.length, ∀ Y, #Y < s → P Y → fb.getD k 0 Y = yatesTransform c (l.take k) G Y) →
      ∀ k ≤ l.length, ∀ X ∈ dom,
        (stagesM c s dom l fb t).ret.getD k 0 X = yatesTransform c (l.take k) G X
  | [], _, t, G, ht, _, k, hk, X, hX => by
    obtain rfl : k = 0 := by simpa using hk
    simpa [stagesM] using ht X hX
  | i :: l, fb, t, G, ht, hfb, k, hk, X, hX => by
    set rd : Finset ι → M := fun Y => if s ≤ #Y then t Y else fb.headD 0 Y
    have hrd : ∀ Y, (s ≤ #Y → Y ∈ dom) → (#Y < s → P Y) → rd Y = G Y := by
      intro Y hY hP
      by_cases h : s ≤ #Y
      · simp only [rd, h, ↓reduceIte]
        exact ht Y (hY h)
      · simp only [rd, h, ↓reduceIte]
        have := hfb 0 (by simp) Y (by omega) (hP (by omega))
        simpa [List.getD_eq_getElem?_getD, List.head?_eq_getElem?] using this
    have ht' : ∀ X ∈ dom, (tabulateM dom (yatesPass c i rd)).ret X = yatesPass c i G X := by
      intro X hX
      rw [ret_tabulateM _ hX, yatesPass, yatesPass,
        hrd X (fun _ => hX) fun h => absurd (hs X hX) (by omega)]
      split_ifs with hiX
      · rw [hrd (X.erase i) (hdom X hX i hiX).1 (hdom X hX i hiX).2]
      · rfl
    have hfb' : ∀ k < l.length, ∀ Y, #Y < s → P Y →
        fb.tail.getD k 0 Y = yatesTransform c (l.take k) (yatesPass c i G) Y := by
      intro k hk Y hY hP
      have := hfb (k + 1) (by simp; omega) Y hY hP
      rw [List.take_succ_cons, yatesTransform_cons] at this
      rw [← this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_tail]
    simp only [stagesM, ret_bind, ret_pure]
    rcases k with _ | k
    · simpa using ht X hX
    · rw [List.getD_cons_succ, List.take_succ_cons, yatesTransform_cons]
      exact getD_ret_stagesM c P hs hdom l fb.tail _ _ ht' hfb' k (by simpa using hk) X hX

end Stages

/-! ### Selected entries of the covering product -/

/-- The tables kept by the preprocessing phase: every stage of the trimmed transforms on the sets
with at most `s` elements. -/
structure Tables (ι M : Type*) where
  /-- Stage `k` of the zeta transform of the left input. -/
  zetaLeft : List (Finset ι → M)
  /-- Stage `k` of the zeta transform of the right input. -/
  zetaRight : List (Finset ι → M)
  /-- Stage `k` of the Möbius transform of the pointwise product of the two zeta transforms. -/
  cover : List (Finset ι → M)

variable {ι R : Type u} [DecidableEq ι] [CommRing R]

/-- The **preprocessing phase**: every stage of the zeta transforms of `f` and `g`, and of the
Möbius transform of their pointwise product, on the subsets of `l` with at most `s` elements. -/
@[expose] def preprocessM (l : List ι) (s : ℕ) (f g : Finset ι → R) : TimeM ℕ (Tables ι R) := do
  let low := layers l 0 s
  let f₀ ← tabulateM low f
  let fs ← stagesM (1 : ℕ) 0 low l [] f₀
  let g₀ ← tabulateM low g
  let gs ← stagesM (1 : ℕ) 0 low l [] g₀
  let h₀ ← tabulateM low fun X => fs.getD l.length 0 X * gs.getD l.length 0 X
  let hs ← stagesM (-1 : ℤ) 0 low l [] h₀
  pure ⟨fs, gs, hs⟩

/-- The **query phase** for `C`: the same stages on the subsets of `C` with at least `s` elements,
reading the preprocessed stages `T` at smaller sets. Returns the last stage at `C`. -/
@[expose] def queryM (l : List ι) (s : ℕ) (T : Tables ι R) (f g : Finset ι → R)
    (C : Finset ι) : TimeM ℕ R := do
  let high := layers (l.filter (· ∈ C)) s #C
  let f₀ ← tabulateM high f
  let fs ← stagesM (1 : ℕ) s high l T.zetaLeft f₀
  let g₀ ← tabulateM high g
  let gs ← stagesM (1 : ℕ) s high l T.zetaRight g₀
  let h₀ ← tabulateM high fun X => fs.getD l.length 0 X * gs.getD l.length 0 X
  let hs ← stagesM (-1 : ℤ) s high l T.cover h₀
  pure (hs.getD l.length 0 C)

/-- **Selected entries of the covering product**: preprocess once, then answer each query. -/
@[expose] def solveM (l : List ι) (s : ℕ) (f g : Finset ι → R) (Cs : List (Finset ι)) :
    TimeM ℕ (List R) := do
  let T ← preprocessM l s f g
  Cs.mapM (queryM l s T f g)

/-! #### Correctness -/

/-- The stages of the zeta transform reach `subsetZeta` once every coordinate is processed. -/
private theorem yatesTransform_one_take_length {l : List ι} (hl : l.Nodup) (F : Finset ι → R)
    {X : Finset ι} (hX : X ⊆ l.toFinset) :
    yatesTransform (1 : ℕ) (l.take l.length) F X = subsetZeta F X := by
  rw [List.take_length, yatesTransform_one_apply hl F hX]

/-- What the preprocessed tables hold: stage `k` of each transform on the subsets of `l` with at
most `s` elements. -/
private theorem preprocessM_spec {l : List ι} (hl : l.Nodup) (s : ℕ) (f g : Finset ι → R) :
    let T := (preprocessM l s f g).ret
    let H : Finset ι → R := fun S => subsetZeta f S * subsetZeta g S
    ∀ k ≤ l.length, ∀ X, X ⊆ l.toFinset → #X ≤ s →
      T.zetaLeft.getD k 0 X = yatesTransform (1 : ℕ) (l.take k) f X ∧
      T.zetaRight.getD k 0 X = yatesTransform (1 : ℕ) (l.take k) g X ∧
      T.cover.getD k 0 X = yatesTransform (-1 : ℤ) (l.take k) H X := by
  intro T H k hk X hXl hXs
  have hlow : ∀ {Y}, Y ∈ layers l 0 s ↔ Y ⊆ l.toFinset ∧ #Y ≤ s := by
    intro Y; rw [mem_layers hl]; simp
  have hs : ∀ X ∈ layers l 0 s, 0 ≤ #X := fun _ _ => Nat.zero_le _
  have hdom : ∀ X ∈ layers l 0 s, ∀ i, i ∈ X → (0 ≤ #(X.erase i) → X.erase i ∈ layers l 0 s) ∧
      (#(X.erase i) < 0 → False) := by
    intro X hX i _
    refine ⟨fun _ => hlow.mpr ⟨(erase_subset i X).trans (hlow.mp hX).1, ?_⟩, by omega⟩
    exact (card_erase_le).trans (hlow.mp hX).2
  have hnofb : ∀ (c' : R) (G : Finset ι → R), ∀ k < l.length, ∀ Y, #Y < 0 → False →
      ([] : List (Finset ι → R)).getD k 0 Y = yatesTransform c' (l.take k) G Y := by
    intro _ _ _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  have hX : X ∈ layers l 0 s := hlow.mpr ⟨hXl, hXs⟩
  have stage := fun {R' : Type _} [Monoid R'] [DistribMulAction R' R] (c' : R') (t G : Finset ι → R)
      (ht : ∀ X ∈ layers l 0 s, t X = G X) =>
    getD_ret_stagesM (M := R) c' (fun _ => False) hs hdom l [] t G ht
      (fun k hk Y hY _ => absurd hY (Nat.not_lt_zero _))
  have hf := stage (1 : ℕ) _ f fun Y hY => ret_tabulateM f hY
  have hg := stage (1 : ℕ) _ g fun Y hY => ret_tabulateM g hY
  refine ⟨hf k hk X hX, hg k hk X hX, stage (-1 : ℤ) _ H (fun Y hY => ?_) k hk X hX⟩
  rw [ret_tabulateM _ hY, hf _ le_rfl Y hY, hg _ le_rfl Y hY,
    yatesTransform_one_take_length hl f (hlow.mp hY).1,
    yatesTransform_one_take_length hl g (hlow.mp hY).1]

/-- **Correctness of a query**: if `C` is a set of coordinates of `l` with at least `s` elements,
the query after preprocessing returns the covering product `coveringProduct f g C`. -/
theorem ret_queryM_preprocessM {l : List ι} (hl : l.Nodup) {s : ℕ} (f g : Finset ι → R)
    {C : Finset ι} (hC : C ⊆ l.toFinset) (hsC : s ≤ #C) :
    (queryM l s (preprocessM l s f g).ret f g C).ret = coveringProduct f g C := by
  have pre := preprocessM_spec hl s f g
  set T := (preprocessM l s f g).ret
  set H : Finset ι → R := fun S => subsetZeta f S * subsetZeta g S
  have hCl : (l.filter (· ∈ C)).toFinset = C := by
    ext x
    simp only [List.toFinset_filter, mem_filter, List.mem_toFinset, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hC h), h⟩⟩
  have hhigh : ∀ {Y}, Y ∈ layers (l.filter (· ∈ C)) s #C ↔ Y ⊆ C ∧ s ≤ #Y := by
    intro Y
    rw [mem_layers (hl.filter _), hCl]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, card_le_card h.1⟩⟩
  have hs : ∀ X ∈ layers (l.filter (· ∈ C)) s #C, s ≤ #X := fun X hX => (hhigh.mp hX).2
  let P : Finset ι → Prop := fun Y => Y ⊆ l.toFinset ∧ #Y ≤ s
  have hdom : ∀ X ∈ layers (l.filter (· ∈ C)) s #C, ∀ i, i ∈ X →
      (s ≤ #(X.erase i) → X.erase i ∈ layers (l.filter (· ∈ C)) s #C) ∧
      (#(X.erase i) < s → P (X.erase i)) := by
    intro X hX i _
    have hXC := (hhigh.mp hX).1
    exact ⟨fun h => hhigh.mpr ⟨(erase_subset i X).trans hXC, h⟩,
      fun h => ⟨(erase_subset i X).trans (hXC.trans hC), by omega⟩⟩
  have hYl : ∀ {Y}, Y ∈ layers (l.filter (· ∈ C)) s #C → Y ⊆ l.toFinset :=
    fun hY => (hhigh.mp hY).1.trans hC
  have hf := getD_ret_stagesM (1 : ℕ) P hs hdom l T.zetaLeft
    (tabulateM (layers (l.filter (· ∈ C)) s #C) f).ret f
    (fun Y hY => ret_tabulateM f hY) fun k hk Y _ hP => (pre k hk.le Y hP.1 hP.2).1
  have hg := getD_ret_stagesM (1 : ℕ) P hs hdom l T.zetaRight
    (tabulateM (layers (l.filter (· ∈ C)) s #C) g).ret g
    (fun Y hY => ret_tabulateM g hY) fun k hk Y _ hP => (pre k hk.le Y hP.1 hP.2).2.1
  have hCmem : C ∈ layers (l.filter (· ∈ C)) s #C := hhigh.mpr ⟨subset_rfl, hsC⟩
  simp only [queryM, ret_bind, ret_pure]
  rw [getD_ret_stagesM (-1 : ℤ) P hs hdom l T.cover _ H ?_
      (fun k hk Y _ hP => (pre k hk.le Y hP.1 hP.2).2.2) _ le_rfl C hCmem,
    List.take_length, yatesTransform_neg_one_apply hl H hC, coveringProduct_eq_subsetMobius]
  intro Y hY
  rw [ret_tabulateM _ hY, hf _ le_rfl Y hY, hg _ le_rfl Y hY,
    yatesTransform_one_take_length hl f (hYl hY), yatesTransform_one_take_length hl g (hYl hY)]

/-- **Ranked queries** ([ChanItakuraMaYu2026], Problem 2.1): if `f` is supported on sets with `t₁`
elements and `g` on sets with `t₂` elements, a query at a set `C` of `t₁ + t₂` coordinates of `l`
returns the subset convolution `∑_{A ⊆ C} f A * g (C \ A)`, for every threshold
`s ≤ t₁ + t₂`. -/
theorem ret_queryM_preprocessM_eq_subsetConvolution {l : List ι} (hl : l.Nodup) {s t₁ t₂ : ℕ}
    {f g : Finset ι → R} (hf : ∀ A, f A ≠ 0 → #A = t₁) (hg : ∀ B, g B ≠ 0 → #B = t₂)
    {C : Finset ι} (hC : C ⊆ l.toFinset) (hCcard : #C = t₁ + t₂) (hs : s ≤ t₁ + t₂) :
    (queryM l s (preprocessM l s f g).ret f g C).ret = subsetConvolution f g C := by
  rw [ret_queryM_preprocessM hl f g hC (hCcard ▸ hs),
    coveringProduct_eq_subsetConvolution hf hg hCcard]

/-- **Correctness of `solveM`**: for queries at sets of `t₁ + t₂` coordinates of `l`, the answers
are the selected entries of the subset convolution of ranked inputs. -/
theorem ret_solveM {l : List ι} (hl : l.Nodup) {s t₁ t₂ : ℕ} {f g : Finset ι → R}
    (hf : ∀ A, f A ≠ 0 → #A = t₁) (hg : ∀ B, g B ≠ 0 → #B = t₂) {Cs : List (Finset ι)}
    (hCs : ∀ C ∈ Cs, C ⊆ l.toFinset ∧ #C = t₁ + t₂) (hs : s ≤ t₁ + t₂) :
    (solveM l s f g Cs).ret = Cs.map (subsetConvolution f g) := by
  simp only [solveM, ret_bind, ret_listMapM]
  refine List.map_congr_left fun C hC => ?_
  exact ret_queryM_preprocessM_eq_subsetConvolution hl hf hg (hCs C hC).1 (hCs C hC).2 hs

/-! #### Cost -/

/-- Preprocessing costs `3 * (l.length + 1)` ticks per subset of `l` with at most `s` elements. -/
theorem time_preprocessM (l : List ι) (s : ℕ) (f g : Finset ι → R) :
    (preprocessM l s f g).time = 3 * (l.length + 1) * (layers l 0 s).length := by
  simp only [preprocessM, time_bind, time_tabulateM, time_stagesM, time_pure]
  ring

/-- A query costs `3 * (l.length + 1)` ticks per subset of `C` with at least `s` elements, for any
preprocessed tables. -/
theorem time_queryM (l : List ι) (s : ℕ) (T : Tables ι R) (f g : Finset ι → R)
    (C : Finset ι) :
    (queryM l s T f g C).time = 3 * (l.length + 1) * (layers (l.filter (· ∈ C)) s #C).length := by
  simp only [queryM, time_bind, time_tabulateM, time_stagesM, time_pure]
  ring

/-- **Preprocessing time**: `3 (d + 1) ∑_{j ≤ s} (d choose j)` ticks for `d = l.length`. -/
theorem time_preprocessM_eq_sum_choose (l : List ι) (s : ℕ) (f g : Finset ι → R) :
    (preprocessM l s f g).time = 3 * (l.length + 1) * ∑ j ∈ range (s + 1), l.length.choose j := by
  rw [time_preprocessM, length_layers]
  congr 2
  ext j
  simp only [mem_Icc, mem_range]
  omega

/-- **Query time**: `3 (d + 1) ∑_{s ≤ j ≤ #C} (#C choose j)` ticks for a set `C` of coordinates
of the duplicate-free list `l` of length `d`. -/
theorem time_queryM_eq_sum_choose {l : List ι} (hl : l.Nodup) (s : ℕ) (T : Tables ι R)
    (f g : Finset ι → R) {C : Finset ι} (hC : C ⊆ l.toFinset) :
    (queryM l s T f g C).time = 3 * (l.length + 1) * ∑ j ∈ Icc s #C, (#C).choose j := by
  have hlen : (l.filter (· ∈ C)).length = #C := by
    rw [← List.toFinset_card_of_nodup (hl.filter _)]
    congr 1
    ext x
    simp only [List.toFinset_filter, mem_filter, List.mem_toFinset, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hC h), h⟩⟩
  rw [time_queryM, length_layers, hlen]

/-- **The cost of [ChanItakuraMaYu2026], Theorem 2.2**, exactly: for `d = l.length` coordinates
and queries at sets of `2t` coordinates, `solveM` takes
`3 (d + 1) (∑_{j ≤ s} (d choose j) + |𝒞| ∑_{s ≤ j ≤ 2t} (2t choose j))` ticks. -/
theorem time_solveM {l : List ι} (hl : l.Nodup) (s t : ℕ) (f g : Finset ι → R)
    {Cs : List (Finset ι)} (hCs : ∀ C ∈ Cs, C ⊆ l.toFinset ∧ #C = 2 * t) :
    (solveM l s f g Cs).time = 3 * (l.length + 1) *
      (∑ j ∈ range (s + 1), l.length.choose j +
        Cs.length * ∑ j ∈ Icc s (2 * t), (2 * t).choose j) := by
  simp only [solveM, time_bind, time_listMapM, time_preprocessM_eq_sum_choose]
  rw [List.map_congr_left fun C hC => by
    rw [time_queryM_eq_sum_choose hl s _ f g (hCs C hC).1, (hCs C hC).2]]
  rw [List.map_const', List.sum_replicate, smul_eq_mul]
  ring

end Cslib.Algorithms.Lean.TrimmedYates
