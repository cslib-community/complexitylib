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
# Trimmed Yates passes and selected entries of ranked convolutions

Selected entries of the ranked subset convolution by the trimmed fast zeta transform, following
the proof of [ChanItakuraMaYu2026], Theorem 2.2 (Section 2.1), after
[BjorklundHusfeldtKaskiKoivisto2007] and the trimmed transform of
[BjorklundHusfeldtKaskiKoivisto2010] cited there.

The algorithm is stated for a **scheme of passes** (`Passes`): coordinates processed in order, a
zeta and a Möbius pass for each coordinate on cells of some type `κ`, a grading `size` of the cells
and a cost per cell of a pass. Stage `k` of a transform is the first `k` passes applied to the
input, and the trimmed passes (`stagesM`) read a smaller cell of stage `k` either from the current
domain or, below the threshold `s`, from a fallback table of stage `k`.

* **Preprocessing** (`Passes.preprocessM`) runs every stage of the zeta transforms of `f` and `g`,
  of their pointwise product and of its Möbius transform on the *low* cells, keeping every stage
  (`Tables`).
* **A query** `C` (`Passes.queryM`) runs the same stages on the *high* cells below `C`, those with
  `s ≤ size`, reading the preprocessed stage of the same index at smaller cells.

If each pass at a cell only reads cells below it, the grading is monotone and the cells of interest
are closed downwards (`Passes.Local`), a query returns the full Möbius transform of the product of
the full zeta transforms at `C` (`Passes.ret_queryM_preprocessM`, `Passes.ret_solveM`).

**Subsets of coordinates** (`setPasses`): cells are the subsets of a duplicate-free list `l` of
coordinates, the passes are Yates's (`yatesPass`) and the grading is the cardinality. The low cells
are the subsets with at most `s` elements (`layers l 0 s`) and the high cells of a query `C` its
subsets with at least `s` elements. A query returns the covering product `coveringProduct f g C`
(`ret_queryM_preprocessM`), which for ranked inputs and `#C = t₁ + t₂` is the subset convolution
(`ret_queryM_preprocessM_eq_subsetConvolution`, `ret_solveM`). The second scheme, binomial passes
on vectors for [ChanItakuraMaYu2026], Section 3.1, is in
`CslibFrontier.Algorithms.Lean.VectorConvolution`.

## Cost model

* **Charged:** computing one table cell (`tabulateM`): `1` tick for reading the input `f` or `g`
  at one cell or multiplying two transform values, and `cost` ticks for one pass at one cell. For
  Yates's passes `cost = 1`: one membership test, one or two table reads, one scalar multiplication
  and one addition. Each table read is one dictionary look-up keyed by a cell, and includes the
  comparison `s ≤ size Y` deciding whether to read the current stage or the preprocessed one.
* **Uncharged:** enumerating the cells of a domain (`layers`), building the dictionary of a
  table, loop control, and selecting stages from the lists of tables.

This is a unit-cost model in which a cell is a key and a ring element is a word, as in
[ChanItakuraMaYu2026], footnote 7, which assumes a word RAM with words of at least `d = l.length`
bits and ignores dictionary look-ups costing `d ^ O(1)`. The inputs `f` and `g` are given as
look-up functions, so the term `n` of Theorem 2.2 (storing the `n` input sets) does not appear.
The counts are exact: `3 (cost · d + 1)` ticks per low cell and per high cell of each query
(`Passes.time_solveM`). For subsets, preprocessing takes `3 (d + 1) ∑_{j ≤ s} (d choose j)` ticks
and a query `3 (d + 1) ∑_{s ≤ j ≤ #C} (#C choose j)` (`time_preprocessM_eq_sum_choose`,
`time_queryM_eq_sum_choose`). This gives Theorem 2.2's bound
`(binom(d, ≤ s) + |𝒞| binom(2t, ≥ s)) d ^ O(1)` with explicit constants (`time_solveM`).

## Main definitions

* `Cslib.Algorithms.Lean.TrimmedYates.tabulateM`: `w` ticks per cell of a table.
* `Cslib.Algorithms.Lean.TrimmedYates.stagesM`: trimmed passes on a domain of cells, with a
  fallback table for small cells.
* `Cslib.Algorithms.Lean.TrimmedYates.Passes`, `Passes.preprocessM`, `Passes.queryM`,
  `Passes.solveM`, `Passes.Local`: the algorithm for a scheme of passes.
* `Cslib.Algorithms.Lean.TrimmedYates.layers`: the subsets of a list with a given range of sizes.
* `Cslib.Algorithms.Lean.TrimmedYates.setPasses`, `preprocessM`, `queryM`, `solveM`: selected
  entries of the covering product.

## Main results

* `Cslib.Algorithms.Lean.TrimmedYates.getD_ret_stagesM`: correctness of the trimmed passes.
* `Cslib.Algorithms.Lean.TrimmedYates.Passes.ret_queryM_preprocessM`, `Passes.ret_solveM`,
  `Passes.time_solveM`: correctness and exact cost for a scheme of passes.
* `Cslib.Algorithms.Lean.TrimmedYates.ret_queryM_preprocessM`,
  `ret_queryM_preprocessM_eq_subsetConvolution`, `ret_solveM`: the queries return selected
  entries of the covering product, and of the subset convolution for ranked inputs.
* `Cslib.Algorithms.Lean.TrimmedYates.time_preprocessM_eq_sum_choose`,
  `time_queryM_eq_sum_choose`, `time_solveM`: exact tick counts for subsets.

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

/-- The table of `cell` on the keys `dom`, at `w` ticks per key: a dictionary from each key of
`dom` to its value, read as `0` off `dom`. -/
@[expose] def tabulateM (w : ℕ) (dom : List κ) (cell : κ → M) : TimeM ℕ (κ → M) := do
  let vals : List M ← dom.mapM fun X => do ✓[w] pure (cell X)
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
theorem ret_tabulateM (w : ℕ) {dom : List κ} (cell : κ → M) {X : κ} (hX : X ∈ dom) :
    (tabulateM w dom cell).ret X = cell X := by
  simp only [tabulateM, ret_bind, ret_pure, ret_listMapM]
  exact lookup_zip_map cell hX

/-- A table costs `w` ticks per key. -/
@[simp] theorem time_tabulateM (w : ℕ) (dom : List κ) (cell : κ → M) :
    (tabulateM w dom cell).time = w * dom.length := by
  simp only [tabulateM, time_bind, time_pure, time_listMapM, time_tick, add_zero,
    List.map_const', List.sum_replicate, smul_eq_mul, mul_comm]

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

variable {ι κ M : Type u} [DecidableEq κ] [Zero M]

/-- The passes `pass i` for the coordinates `i` of `l`, in order, at `w` ticks per cell of `dom`,
returning every stage: stage `0` is `t`, and stage `k + 1` is the pass in coordinate `k` of `l`
applied to stage `k`. A cell reads stage `k` at cells `Y` with `s ≤ size Y` and the `k`-th table
of `fb` at smaller cells. -/
@[expose] def stagesM (pass : ι → (κ → M) → κ → M) (size : κ → ℕ) (w s : ℕ) (dom : List κ) :
    List ι → List (κ → M) → (κ → M) → TimeM ℕ (List (κ → M))
  | [], _, t => pure [t]
  | i :: l, fb, t => do
    let t' ← tabulateM w dom (pass i fun Y => if s ≤ size Y then t Y else fb.headD 0 Y)
    let ts ← stagesM pass size w s dom l fb.tail t'
    pure (t :: ts)

/-- The trimmed passes cost `w` ticks per coordinate and cell. -/
@[simp] theorem time_stagesM (pass : ι → (κ → M) → κ → M) (size : κ → ℕ) (w s : ℕ)
    (dom : List κ) : ∀ (l : List ι) (fb : List (κ → M)) (t : κ → M),
      (stagesM pass size w s dom l fb t).time = l.length * (w * dom.length)
  | [], _, _ => by simp [stagesM]
  | i :: l, fb, t => by
    simp only [stagesM, time_bind, time_tabulateM, time_pure, add_zero,
      time_stagesM pass size w s dom l, List.length_cons]
    ring

/-- **Correctness of the trimmed passes.** Suppose that each pass at a cell only reads cells
below it, that every cell `X` of `dom` has `s ≤ size X`, and that every cell below `X` is a cell
of `dom` or a cell satisfying `P` with `size < s`. If `t` agrees with `G` on `dom` and the `k`-th
table of `fb` agrees with stage `k` of `G` on the cells satisfying `P` with `size < s`, then every
returned stage `k ≤ l.length` agrees with stage `k` of `G` on `dom`. -/
theorem getD_ret_stagesM [Preorder κ] {pass : ι → (κ → M) → κ → M}
    (hpass : ∀ i (F F' : κ → M) X, (∀ Y ≤ X, F Y = F' Y) → pass i F X = pass i F' X)
    {size : κ → ℕ} (w : ℕ) {s : ℕ} {dom : List κ} (P : κ → Prop)
    (hdom : ∀ X ∈ dom, s ≤ size X ∧
      ∀ Y ≤ X, (s ≤ size Y → Y ∈ dom) ∧ (size Y < s → P Y)) :
    ∀ (l : List ι) (fb : List (κ → M)) (t G : κ → M),
      (∀ X ∈ dom, t X = G X) →
      (∀ k < l.length, ∀ Y, size Y < s → P Y →
        fb.getD k 0 Y = (l.take k).foldl (fun F i => pass i F) G Y) →
      ∀ k ≤ l.length, ∀ X ∈ dom,
        (stagesM pass size w s dom l fb t).ret.getD k 0 X =
          (l.take k).foldl (fun F i => pass i F) G X
  | [], _, t, G, ht, _, k, hk, X, hX => by
    obtain rfl : k = 0 := by simpa using hk
    simpa [stagesM] using ht X hX
  | i :: l, fb, t, G, ht, hfb, k, hk, X, hX => by
    set rd : κ → M := fun Y => if s ≤ size Y then t Y else fb.headD 0 Y
    have ht' : ∀ X ∈ dom, (tabulateM w dom (pass i rd)).ret X = pass i G X := by
      intro X hX
      rw [ret_tabulateM w _ hX]
      refine hpass i rd G X fun Y hY => ?_
      obtain ⟨hdY, hPY⟩ := (hdom X hX).2 Y hY
      by_cases h : s ≤ size Y
      · simp only [rd, h, ↓reduceIte]
        exact ht Y (hdY h)
      · simp only [rd, h, ↓reduceIte]
        have := hfb 0 (by simp) Y (by omega) (hPY (by omega))
        simpa [List.getD_eq_getElem?_getD, List.head?_eq_getElem?] using this
    have hfb' : ∀ k < l.length, ∀ Y, size Y < s → P Y →
        fb.tail.getD k 0 Y = (l.take k).foldl (fun F i => pass i F) (pass i G) Y := by
      intro k hk Y hY hP
      have := hfb (k + 1) (by simp; omega) Y hY hP
      rw [List.take_succ_cons, List.foldl_cons] at this
      rw [← this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_tail]
    simp only [stagesM, ret_bind, ret_pure]
    rcases k with _ | k
    · simpa using ht X hX
    · rw [List.getD_cons_succ, List.take_succ_cons, List.foldl_cons]
      exact getD_ret_stagesM hpass w P hdom l fb.tail _ _ ht' hfb' k (by simpa using hk) X hX

end Stages

/-! ### Selected entries of ranked convolutions -/

/-- The tables kept by the preprocessing phase: every stage of the trimmed transforms on the low
cells. -/
structure Tables (κ M : Type*) where
  /-- Stage `k` of the zeta transform of the left input. -/
  zetaLeft : List (κ → M)
  /-- Stage `k` of the zeta transform of the right input. -/
  zetaRight : List (κ → M)
  /-- Stage `k` of the Möbius transform of the pointwise product of the two zeta transforms. -/
  cover : List (κ → M)

/-- A **scheme of passes** for the trimmed algorithm: a zeta and a Möbius pass for each
coordinate of `coords`, on cells of type `κ` graded by `size`, at `cost` ticks per cell of one
pass. Subsets of coordinates with Yates's passes (`setPasses`) and vectors with binomial passes
(`CslibFrontier.Algorithms.Lean.VectorConvolution`) are the two schemes. -/
structure Passes (ι κ R : Type u) where
  /-- The coordinates, processed in order. -/
  coords : List ι
  /-- The zeta pass in one coordinate. -/
  zeta : ι → (κ → R) → κ → R
  /-- The Möbius pass in one coordinate. -/
  mobius : ι → (κ → R) → κ → R
  /-- The grading of the cells; the threshold `s` separates low from high cells. -/
  size : κ → ℕ
  /-- The ticks charged for one pass at one cell. -/
  cost : ℕ

namespace Passes

variable {ι κ R : Type u} [DecidableEq κ] [CommRing R] (P : Passes ι κ R)

/-- The full zeta transform: every zeta pass, in order. -/
@[expose] def zetaAll (F : κ → R) : κ → R := P.coords.foldl (fun F i => P.zeta i F) F

/-- The full Möbius transform: every Möbius pass, in order. -/
@[expose] def mobiusAll (F : κ → R) : κ → R := P.coords.foldl (fun F i => P.mobius i F) F

/-- The **preprocessing phase** on the low cells `low`: every stage of the zeta transforms of `f`
and `g`, and of the Möbius transform of their pointwise product. -/
@[expose] def preprocessM (low : List κ) (f g : κ → R) : TimeM ℕ (Tables κ R) := do
  let f₀ ← tabulateM 1 low f
  let fs ← stagesM P.zeta P.size P.cost 0 low P.coords [] f₀
  let g₀ ← tabulateM 1 low g
  let gs ← stagesM P.zeta P.size P.cost 0 low P.coords [] g₀
  let h₀ ← tabulateM 1 low fun X => fs.getD P.coords.length 0 X * gs.getD P.coords.length 0 X
  let hs ← stagesM P.mobius P.size P.cost 0 low P.coords [] h₀
  pure ⟨fs, gs, hs⟩

/-- The **query phase** at `C`: the same stages on the high cells `high` below `C`, reading the
preprocessed stages `T` at cells `Y` with `size Y < s`. Returns the last stage at `C`. -/
@[expose] def queryM (s : ℕ) (T : Tables κ R) (high : List κ) (f g : κ → R) (C : κ) :
    TimeM ℕ R := do
  let f₀ ← tabulateM 1 high f
  let fs ← stagesM P.zeta P.size P.cost s high P.coords T.zetaLeft f₀
  let g₀ ← tabulateM 1 high g
  let gs ← stagesM P.zeta P.size P.cost s high P.coords T.zetaRight g₀
  let h₀ ← tabulateM 1 high fun X => fs.getD P.coords.length 0 X * gs.getD P.coords.length 0 X
  let hs ← stagesM P.mobius P.size P.cost s high P.coords T.cover h₀
  pure (hs.getD P.coords.length 0 C)

/-- **Selected entries**: preprocess the low cells once, then answer each query `C` on its high
cells `high C`. -/
@[expose] def solveM (s : ℕ) (low : List κ) (high : κ → List κ) (f g : κ → R) (Cs : List κ) :
    TimeM ℕ (List R) := do
  let T ← P.preprocessM low f g
  Cs.mapM fun C => P.queryM s T (high C) f g C

/-- Hypotheses on a scheme of passes under which the trimmed algorithm is correct: each pass at a
cell only reads cells below it, the grading is monotone, and the cells of interest `U` are closed
downwards. -/
structure Local [Preorder κ] (U : κ → Prop) : Prop where
  zeta_congr : ∀ i (F F' : κ → R) X, (∀ Y ≤ X, F Y = F' Y) → P.zeta i F X = P.zeta i F' X
  mobius_congr : ∀ i (F F' : κ → R) X, (∀ Y ≤ X, F Y = F' Y) → P.mobius i F X = P.mobius i F' X
  size_mono : Monotone P.size
  closed : ∀ {X Y}, Y ≤ X → U X → U Y

variable {P}

/-- What the preprocessed tables hold: stage `k` of each transform at the low cells. -/
private theorem preprocessM_spec [Preorder κ] {U : κ → Prop} (hP : P.Local U) {s : ℕ}
    {low : List κ} (hlow : ∀ Y, Y ∈ low ↔ U Y ∧ P.size Y ≤ s) (f g : κ → R) :
    let T := (P.preprocessM low f g).ret
    let H : κ → R := fun X => P.zetaAll f X * P.zetaAll g X
    ∀ k ≤ P.coords.length, ∀ X, U X → P.size X ≤ s →
      T.zetaLeft.getD k 0 X = (P.coords.take k).foldl (fun F i => P.zeta i F) f X ∧
      T.zetaRight.getD k 0 X = (P.coords.take k).foldl (fun F i => P.zeta i F) g X ∧
      T.cover.getD k 0 X = (P.coords.take k).foldl (fun F i => P.mobius i F) H X := by
  intro T H k hk X hUX hXs
  have hdom : ∀ X ∈ low, 0 ≤ P.size X ∧
      ∀ Y ≤ X, (0 ≤ P.size Y → Y ∈ low) ∧ (P.size Y < 0 → False) := by
    intro X hX
    obtain ⟨hU, hs⟩ := (hlow X).mp hX
    exact ⟨Nat.zero_le _, fun Y hY =>
      ⟨fun _ => (hlow Y).mpr ⟨hP.closed hY hU, (hP.size_mono hY).trans hs⟩, by omega⟩⟩
  have hX : X ∈ low := (hlow X).mpr ⟨hUX, hXs⟩
  have stage := fun (pass : ι → (κ → R) → κ → R)
      (hpass : ∀ i (F F' : κ → R) X, (∀ Y ≤ X, F Y = F' Y) → pass i F X = pass i F' X)
      (t G : κ → R) (ht : ∀ X ∈ low, t X = G X) =>
    getD_ret_stagesM hpass P.cost (fun _ => False) hdom P.coords [] t G ht
      (fun k hk Y hY _ => absurd hY (Nat.not_lt_zero _))
  have hf := stage _ hP.zeta_congr _ f fun Y hY => ret_tabulateM 1 f hY
  have hg := stage _ hP.zeta_congr _ g fun Y hY => ret_tabulateM 1 g hY
  refine ⟨hf k hk X hX, hg k hk X hX, stage _ hP.mobius_congr _ H (fun Y hY => ?_) k hk X hX⟩
  rw [ret_tabulateM _ _ hY, hf _ le_rfl Y hY, hg _ le_rfl Y hY, List.take_length]
  rfl

/-- **Correctness of a query**: for a cell `C` of `U` with `s ≤ size C`, if `low` lists the cells
of `U` with `size ≤ s` and `high` lists the cells below `C` with `s ≤ size`, the query after
preprocessing returns the Möbius transform of the product of the zeta transforms at `C`. -/
theorem ret_queryM_preprocessM [Preorder κ] {U : κ → Prop} (hP : P.Local U) {s : ℕ}
    {low high : List κ} (hlow : ∀ Y, Y ∈ low ↔ U Y ∧ P.size Y ≤ s) {C : κ} (hC : U C)
    (hhigh : ∀ Y, Y ∈ high ↔ Y ≤ C ∧ s ≤ P.size Y) (hsC : s ≤ P.size C) (f g : κ → R) :
    (P.queryM s (P.preprocessM low f g).ret high f g C).ret =
      P.mobiusAll (fun X => P.zetaAll f X * P.zetaAll g X) C := by
  have pre := preprocessM_spec hP hlow f g
  set T := (P.preprocessM low f g).ret
  set H : κ → R := fun X => P.zetaAll f X * P.zetaAll g X
  let Q : κ → Prop := fun Y => U Y ∧ P.size Y ≤ s
  have hdom : ∀ X ∈ high, s ≤ P.size X ∧
      ∀ Y ≤ X, (s ≤ P.size Y → Y ∈ high) ∧ (P.size Y < s → Q Y) := by
    intro X hX
    obtain ⟨hXC, hs⟩ := (hhigh X).mp hX
    exact ⟨hs, fun Y hY => ⟨fun h => (hhigh Y).mpr ⟨hY.trans hXC, h⟩,
      fun h => ⟨hP.closed (hY.trans hXC) hC, h.le⟩⟩⟩
  have hf := getD_ret_stagesM hP.zeta_congr P.cost Q hdom P.coords T.zetaLeft
    (tabulateM 1 high f).ret f (fun Y hY => ret_tabulateM 1 f hY)
    fun k hk Y _ hQ => (pre k hk.le Y hQ.1 hQ.2).1
  have hg := getD_ret_stagesM hP.zeta_congr P.cost Q hdom P.coords T.zetaRight
    (tabulateM 1 high g).ret g (fun Y hY => ret_tabulateM 1 g hY)
    fun k hk Y _ hQ => (pre k hk.le Y hQ.1 hQ.2).2.1
  have hCmem : C ∈ high := (hhigh C).mpr ⟨le_rfl, hsC⟩
  simp only [queryM, ret_bind, ret_pure]
  rw [getD_ret_stagesM hP.mobius_congr P.cost Q hdom P.coords T.cover _ H ?_
      (fun k hk Y _ hQ => (pre k hk.le Y hQ.1 hQ.2).2.2) _ le_rfl C hCmem, List.take_length]
  · rfl
  · intro Y hY
    rw [ret_tabulateM _ _ hY, hf _ le_rfl Y hY, hg _ le_rfl Y hY, List.take_length]
    rfl

/-- **Correctness of `solveM`**: each answer is the Möbius transform of the product of the zeta
transforms at its query. -/
theorem ret_solveM [Preorder κ] {U : κ → Prop} (hP : P.Local U) {s : ℕ} {low : List κ}
    (hlow : ∀ Y, Y ∈ low ↔ U Y ∧ P.size Y ≤ s) {high : κ → List κ} {Cs : List κ}
    (hCs : ∀ C ∈ Cs, U C ∧ s ≤ P.size C ∧ ∀ Y, Y ∈ high C ↔ Y ≤ C ∧ s ≤ P.size Y)
    (f g : κ → R) :
    (P.solveM s low high f g Cs).ret =
      Cs.map (P.mobiusAll fun X => P.zetaAll f X * P.zetaAll g X) := by
  simp only [solveM, ret_bind, ret_listMapM]
  refine List.map_congr_left fun C hC => ?_
  obtain ⟨hU, hs, hh⟩ := hCs C hC
  exact ret_queryM_preprocessM hP hlow hU hh hs f g

/-- Preprocessing costs `3 (cost · d + 1)` ticks per low cell, for `d` coordinates. -/
theorem time_preprocessM (low : List κ) (f g : κ → R) :
    (P.preprocessM low f g).time = 3 * (P.cost * P.coords.length + 1) * low.length := by
  simp only [preprocessM, time_bind, time_tabulateM, time_stagesM, time_pure]
  ring

/-- A query costs `3 (cost · d + 1)` ticks per high cell, for any preprocessed tables. -/
theorem time_queryM (s : ℕ) (T : Tables κ R) (high : List κ) (f g : κ → R) (C : κ) :
    (P.queryM s T high f g C).time = 3 * (P.cost * P.coords.length + 1) * high.length := by
  simp only [queryM, time_bind, time_tabulateM, time_stagesM, time_pure]
  ring

/-- `solveM` costs `3 (cost · d + 1)` ticks per low cell and per high cell of each query. -/
theorem time_solveM (s : ℕ) (low : List κ) (high : κ → List κ) (f g : κ → R) (Cs : List κ) :
    (P.solveM s low high f g Cs).time = 3 * (P.cost * P.coords.length + 1) *
      (low.length + (Cs.map fun C => (high C).length).sum) := by
  simp only [solveM, time_bind, time_listMapM, time_preprocessM, time_queryM]
  rw [List.sum_map_mul_left]
  ring

end Passes

/-! ### Subsets of coordinates -/

section Sets

variable {ι R : Type u} [DecidableEq ι] [CommRing R]

/-- **Yates's passes** on subsets of the coordinates `l`, at one tick per cell of a pass. -/
@[expose] def setPasses (l : List ι) : Passes ι (Finset ι) R where
  coords := l
  zeta := yatesPass (1 : ℕ)
  mobius := yatesPass (-1 : ℤ)
  size := card
  cost := 1

/-- The **preprocessing phase**: every stage of the zeta transforms of `f` and `g`, and of the
Möbius transform of their pointwise product, on the subsets of `l` with at most `s` elements. -/
@[expose] def preprocessM (l : List ι) (s : ℕ) (f g : Finset ι → R) :
    TimeM ℕ (Tables (Finset ι) R) :=
  (setPasses l).preprocessM (layers l 0 s) f g

/-- The **query phase** for `C`: the same stages on the subsets of `C` with at least `s` elements,
reading the preprocessed stages `T` at smaller sets. Returns the last stage at `C`. -/
@[expose] def queryM (l : List ι) (s : ℕ) (T : Tables (Finset ι) R) (f g : Finset ι → R)
    (C : Finset ι) : TimeM ℕ R :=
  (setPasses l).queryM s T (layers (l.filter (· ∈ C)) s #C) f g C

/-- **Selected entries of the covering product**: preprocess once, then answer each query. -/
@[expose] def solveM (l : List ι) (s : ℕ) (f g : Finset ι → R) (Cs : List (Finset ι)) :
    TimeM ℕ (List R) :=
  (setPasses l).solveM s (layers l 0 s) (fun C => layers (l.filter (· ∈ C)) s #C) f g Cs

/-- Yates's passes read a set and the set minus one coordinate. -/
theorem setPasses_local (l : List ι) :
    (setPasses (R := R) l).Local fun X => X ⊆ l.toFinset where
  zeta_congr i F F' X h := by
    simp only [setPasses, yatesPass]
    rw [h X le_rfl, h (X.erase i) (erase_subset i X)]
  mobius_congr i F F' X h := by
    simp only [setPasses, yatesPass]
    rw [h X le_rfl, h (X.erase i) (erase_subset i X)]
  size_mono _ _ h := card_le_card h
  closed h hX := h.trans hX

private theorem mem_layers_low {l : List ι} (hl : l.Nodup) (s : ℕ) (Y : Finset ι) :
    Y ∈ layers l 0 s ↔ Y ⊆ l.toFinset ∧ #Y ≤ s := by
  rw [mem_layers hl]; simp

private theorem filter_mem_toFinset {l : List ι} {C : Finset ι} (hC : C ⊆ l.toFinset) :
    (l.filter (· ∈ C)).toFinset = C := by
  ext x
  simp only [List.toFinset_filter, mem_filter, List.mem_toFinset, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hC h), h⟩⟩

private theorem mem_layers_high {l : List ι} (hl : l.Nodup) (s : ℕ) {C : Finset ι}
    (hC : C ⊆ l.toFinset) (Y : Finset ι) :
    Y ∈ layers (l.filter (· ∈ C)) s #C ↔ Y ≤ C ∧ s ≤ #Y := by
  rw [mem_layers (hl.filter _), filter_mem_toFinset hC]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, card_le_card h.1⟩⟩

/-- The full passes on a duplicate-free list are the subset zeta and Möbius transforms. -/
private theorem setPasses_mobiusAll {l : List ι} (hl : l.Nodup) (f g : Finset ι → R)
    {C : Finset ι} (hC : C ⊆ l.toFinset) :
    (setPasses l).mobiusAll (fun X => (setPasses l).zetaAll f X * (setPasses l).zetaAll g X) C =
      coveringProduct f g C := by
  have hz : ∀ (F : Finset ι → R) X, X ⊆ l.toFinset →
      (setPasses l).zetaAll F X = subsetZeta F X := fun F X hX =>
    yatesTransform_one_apply hl F hX
  change yatesTransform (-1 : ℤ) l _ C = _
  rw [yatesTransform_neg_one_apply hl _ hC, coveringProduct_eq_subsetMobius]
  refine subsetMobius_congr fun X hX => ?_
  rw [hz f X (hX.trans hC), hz g X (hX.trans hC)]

/-- **Correctness of a query**: if `C` is a set of coordinates of `l` with at least `s` elements,
the query after preprocessing returns the covering product `coveringProduct f g C`. -/
theorem ret_queryM_preprocessM {l : List ι} (hl : l.Nodup) {s : ℕ} (f g : Finset ι → R)
    {C : Finset ι} (hC : C ⊆ l.toFinset) (hsC : s ≤ #C) :
    (queryM l s (preprocessM l s f g).ret f g C).ret = coveringProduct f g C := by
  rw [queryM, preprocessM, Passes.ret_queryM_preprocessM (setPasses_local l)
    (mem_layers_low hl s) hC (mem_layers_high hl s hC) hsC, setPasses_mobiusAll hl f g hC]

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
  rw [solveM, Passes.ret_solveM (setPasses_local l) (mem_layers_low hl s)
    (fun C hC => ⟨(hCs C hC).1, show s ≤ #C from (hCs C hC).2 ▸ hs,
      mem_layers_high hl s (hCs C hC).1⟩)]
  refine List.map_congr_left fun C hC => ?_
  rw [setPasses_mobiusAll hl f g (hCs C hC).1,
    coveringProduct_eq_subsetConvolution hf hg (hCs C hC).2]

/-! #### Cost -/

/-- Preprocessing costs `3 * (l.length + 1)` ticks per subset of `l` with at most `s` elements. -/
theorem time_preprocessM (l : List ι) (s : ℕ) (f g : Finset ι → R) :
    (preprocessM l s f g).time = 3 * (l.length + 1) * (layers l 0 s).length := by
  rw [preprocessM, Passes.time_preprocessM]
  simp [setPasses]

/-- A query costs `3 * (l.length + 1)` ticks per subset of `C` with at least `s` elements, for any
preprocessed tables. -/
theorem time_queryM (l : List ι) (s : ℕ) (T : Tables (Finset ι) R) (f g : Finset ι → R)
    (C : Finset ι) :
    (queryM l s T f g C).time = 3 * (l.length + 1) * (layers (l.filter (· ∈ C)) s #C).length := by
  rw [queryM, Passes.time_queryM]
  simp [setPasses]

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
theorem time_queryM_eq_sum_choose {l : List ι} (hl : l.Nodup) (s : ℕ) (T : Tables (Finset ι) R)
    (f g : Finset ι → R) {C : Finset ι} (hC : C ⊆ l.toFinset) :
    (queryM l s T f g C).time = 3 * (l.length + 1) * ∑ j ∈ Icc s #C, (#C).choose j := by
  have hlen : (l.filter (· ∈ C)).length = #C := by
    rw [← List.toFinset_card_of_nodup (hl.filter _), filter_mem_toFinset hC]
  rw [time_queryM, length_layers, hlen]

/-- **The cost of [ChanItakuraMaYu2026], Theorem 2.2**, exactly: for `d = l.length` coordinates
and queries at sets of `2t` coordinates, `solveM` takes
`3 (d + 1) (∑_{j ≤ s} (d choose j) + |𝒞| ∑_{s ≤ j ≤ 2t} (2t choose j))` ticks. -/
theorem time_solveM {l : List ι} (hl : l.Nodup) (s t : ℕ) (f g : Finset ι → R)
    {Cs : List (Finset ι)} (hCs : ∀ C ∈ Cs, C ⊆ l.toFinset ∧ #C = 2 * t) :
    (solveM l s f g Cs).time = 3 * (l.length + 1) *
      (∑ j ∈ range (s + 1), l.length.choose j +
        Cs.length * ∑ j ∈ Icc s (2 * t), (2 * t).choose j) := by
  have hpre := time_preprocessM_eq_sum_choose l s f g
  rw [preprocessM, Passes.time_preprocessM] at hpre
  have hq : ∀ C ∈ Cs, (layers (l.filter (· ∈ C)) s #C).length =
      ∑ j ∈ Icc s (2 * t), (2 * t).choose j := by
    intro C hC
    have := time_queryM_eq_sum_choose hl s ⟨[], [], []⟩ f g (hCs C hC).1
    rw [time_queryM, (hCs C hC).2] at this
    rw [(hCs C hC).2]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3 * (l.length + 1)) this
  rw [solveM, Passes.time_solveM, List.map_congr_left hq, List.map_const', List.sum_replicate,
    smul_eq_mul]
  simp only [setPasses, one_mul] at hpre ⊢
  rw [mul_add, hpre]
  ring

end Sets

end Cslib.Algorithms.Lean.TrimmedYates
