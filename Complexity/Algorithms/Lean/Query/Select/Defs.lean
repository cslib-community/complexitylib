/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Algorithms.Lean.Query.Sort.Merge.Defs

/-!
# Deterministic selection by the median of medians

`Cslib.Query.select k xs` finds an element of rank `k` (counting from `0`) of `xs` in the
comparison-query model `FreeM (LEQuery α)`, by the groups-of-five median-of-medians algorithm of
Blum, Floyd, Pratt, Rivest and Tarjan: split the list into groups of five, take the lower median
of each group, select the median of these medians recursively as the pivot, partition the list
around the pivot, and recurse into the part that holds rank `k`. Lists of at most
`Cslib.Query.selectCutoff` elements are sorted with `Cslib.Query.mergeSort` instead.

The partition is three-way (below, equivalent to, and above the pivot), so the algorithm is
correct for total preorders with ties; this costs at most two comparisons per element.

Each recursive call on one side of the partition first checks, without comparisons, that the side
has at most `Cslib.Query.selectSideBound n` elements, and returns `none` otherwise. Under an
oracle implementing a total preorder the check always passes
(`Cslib.Query.select_isOrderStatistic`); it makes the recursion well founded and the comparison
bound `Cslib.Query.select_upperBound` hold for every oracle, as `Cslib.Query.UpperBound`
requires.

## Main definitions

* `Cslib.Query.groupMedian`: the lower median of a nonempty group, by sorting it.
* `Cslib.Query.medians`: the lower medians of consecutive groups of five.
* `Cslib.Query.partition3`: split a list into the elements below, equivalent to, and above a
  pivot.
* `Cslib.Query.selectCutoff`, `Cslib.Query.selectSideBound`: the base-case size and the bound on
  each side of the partition.
* `Cslib.Query.select`: deterministic selection by the median of medians.

## References

* [M. Blum, R. W. Floyd, V. Pratt, R. L. Rivest and R. E. Tarjan, *Time bounds for
  selection*][BlumFloydPrattRivestTarjan1973].
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 9.3.
-/

public section

namespace Cslib.Query

variable {α : Type}

/-- The lower median of the nonempty group `x :: xs`: sort it with `mergeSort` and take the entry
at index `(length - 1) / 2`. -/
def groupMedian (x : α) (xs : List α) : FreeM (LEQuery α) α := do
  let s ← mergeSort (x :: xs)
  return s.getD (xs.length / 2) x

/-- The lower medians of consecutive groups of five elements of `xs`; the last group may be
shorter. -/
def medians : List α → FreeM (LEQuery α) (List α)
  | [] => return []
  | x :: xs => do
    let m ← groupMedian x (xs.take 4)
    let ms ← medians (xs.drop 4)
    return m :: ms
termination_by xs => xs.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- Split `xs` into the elements below, equivalent to, and above the pivot `p`, preserving their
order. An element `x` is above `p` when `x ≤ p` fails, below `p` when `x ≤ p` holds and `p ≤ x`
fails, and equivalent otherwise; this takes at most two comparisons per element. -/
def partition3 (p : α) : List α → FreeM (LEQuery α) (List α × List α × List α)
  | [] => return ([], [], [])
  | x :: xs => do
    let (L, E, G) ← partition3 p xs
    if ← LEQuery.ask x p then
      if ← LEQuery.ask p x then
        return (L, x :: E, G)
      else
        return (x :: L, E, G)
    else
      return (L, E, x :: G)

/-- Lists of at most this many elements are sorted directly. It is the smallest cutoff for which
the inductive accounting of `Cslib.Query.select_countQueries_le` closes with the constant `37`. -/
abbrev selectCutoff : ℕ := 730

/-- The bound on each side of the partition around the median of medians, for a list of `n`
elements: with `g = ⌈n / 5⌉` groups and the pivot of rank `⌊(g - 1) / 2⌋` among the medians, at
most `n - 3 * ⌊(g - 1) / 2⌋ - 1` elements lie strictly on either side of the pivot. -/
abbrev selectSideBound (n : ℕ) : ℕ := n - 3 * (((n + 4) / 5 - 1) / 2) - 1

/-- Deterministic selection by the median of medians: an element of rank `k` of `xs`, or `none`
when `xs.length ≤ k`. -/
def select (k : ℕ) (xs : List α) : FreeM (LEQuery α) (Option α) :=
  if _hsmall : xs.length ≤ selectCutoff then do
    let s ← mergeSort xs
    return s[k]?
  else do
    let M ← medians xs
    if _hM : M.length < xs.length then
      let some p ← select ((M.length - 1) / 2) M | return none
      let (L, E, G) ← partition3 p xs
      if _hL : L.length ≤ selectSideBound xs.length then
        if _hG : G.length ≤ selectSideBound xs.length then
          if k < L.length then
            select k L
          else if k < L.length + E.length then
            return some p
          else
            select (k - L.length - E.length) G
        else return none
      else return none
    else return none
termination_by xs.length
decreasing_by all_goals (simp only [selectSideBound, selectCutoff] at *; omega)

end Cslib.Query
