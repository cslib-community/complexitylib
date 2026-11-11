/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Algorithms.Lean.Query.Bounds
public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-!
# The minimum, and the minimum and maximum together, by comparisons

Two specifications and two algorithms in cslib's comparison-query model `FreeM (LEQuery α)`, where
every comparison `a ≤ b` is an oracle query and everything else is free.

`Cslib.Query.IsMinAlg alg` says that against every oracle implementing a linear order, `alg xs`
returns a least element of every nonempty list `xs`; `Cslib.Query.IsMinMaxAlg alg` says the same
for a least and a greatest element returned together. Only linear orders are required, so a
lower bound proved from these specifications applies to every algorithm that is correct on
distinct keys.

`Cslib.Query.findMin` is the linear scan, which makes exactly `n - 1` comparisons on a list of
`n` elements. `Cslib.Query.findMinMax` processes the elements in pairs: it compares the two
elements of a pair with each other, then the smaller with the current minimum and the larger with
the current maximum. It makes exactly `⌈3n/2⌉ - 2` comparisons for `n ≥ 1` ([CLRS2009], Section
9.1; [Knuth1998], Section 5.3.3). Both are correct for total preorders with ties. The matching
lower bounds are in `Complexity.Algorithms.Lean.Query.Select.MinMax.LowerBound`.

## Main definitions

* `Cslib.Query.IsMinAlg`, `Cslib.Query.IsMinMaxAlg`: correctness of a comparison algorithm for
  the minimum, and for the minimum and maximum together.
* `Cslib.Query.findMin`: the minimum by a linear scan.
* `Cslib.Query.findMinMax`: the minimum and maximum by pairwise comparison.

## Main results

* `Cslib.Query.findMin_correct`, `Cslib.Query.findMin_isMinAlg`: `findMin` returns a least
  element against every total preorder.
* `Cslib.Query.countQueries_findMin`, `Cslib.Query.findMin_upperBound`: `findMin` makes exactly
  `n - 1` comparisons under every oracle.
* `Cslib.Query.findMinMax_correct`, `Cslib.Query.findMinMax_isMinMaxAlg`: `findMinMax` returns a
  least and a greatest element against every total preorder.
* `Cslib.Query.countQueries_findMinMax`, `Cslib.Query.findMinMax_upperBound`: `findMinMax` makes
  exactly `(3n + 1) / 2 - 2 = ⌈3n/2⌉ - 2` comparisons under every oracle.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 9.1.
* [D. E. Knuth, *The Art of Computer Programming, Volume 3: Sorting and Searching*][Knuth1998],
  Section 5.3.3.
* [I. Pohl, *A sorting problem and its complexity*][Pohl1972].
-/

public section

namespace Cslib.Query

variable {α : Type}

/-! ## Specifications -/

/-- `IsMinAlg alg` asserts that against every oracle implementing a linear order `r`, `alg xs`
returns an element of every nonempty list `xs` that is `r`-below all elements of `xs`. Nothing is
required on the empty list or against other oracles. -/
structure IsMinAlg (alg : List α → FreeM (LEQuery α) (Option α)) : Prop where
  /-- Against a linear order, the result on a nonempty list is a least element of the list. -/
  correct : ∀ (r : α → α → Prop) [DecidableRel r] [IsLinearOrder α r]
    (oracle : {ι : Type} → LEQuery α ι → ι), (∀ a b, oracle (.le a b) = decide (r a b)) →
    ∀ xs : List α, xs ≠ [] → ∃ m, (alg xs).eval oracle = some m ∧ m ∈ xs ∧ ∀ x ∈ xs, r m x

/-- `IsMinMaxAlg alg` asserts that against every oracle implementing a linear order `r`, `alg xs`
returns a pair `(m, M)` of elements of every nonempty list `xs` with `m` below and `M` above all
elements of `xs`. Nothing is required on the empty list or against other oracles. -/
structure IsMinMaxAlg (alg : List α → FreeM (LEQuery α) (Option (α × α))) : Prop where
  /-- Against a linear order, the result on a nonempty list is a least and a greatest element of
  the list. -/
  correct : ∀ (r : α → α → Prop) [DecidableRel r] [IsLinearOrder α r]
    (oracle : {ι : Type} → LEQuery α ι → ι), (∀ a b, oracle (.le a b) = decide (r a b)) →
    ∀ xs : List α, xs ≠ [] → ∃ m M, (alg xs).eval oracle = some (m, M) ∧ m ∈ xs ∧ M ∈ xs ∧
      ∀ x ∈ xs, r m x ∧ r x M

/-! ## The linear scan -/

/-- Scan `xs`, keeping the smaller of the current minimum `m` and each new element. -/
def findMinFrom (m : α) : List α → FreeM (LEQuery α) α
  | [] => return m
  | x :: xs => do
    if ← LEQuery.ask m x then findMinFrom m xs else findMinFrom x xs

/-- The minimum of a list by a linear scan, or `none` for the empty list. -/
def findMin : List α → FreeM (LEQuery α) (Option α)
  | [] => return none
  | x :: xs => some <$> findMinFrom x xs

/-- The scan makes one comparison per remaining element. -/
@[simp] theorem countQueries_findMinFrom (oracle : {ι : Type} → LEQuery α ι → ι) (m : α)
    (xs : List α) : (findMinFrom m xs).countQueries oracle = xs.length := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih =>
    simp only [findMinFrom, FreeM.countQueries_bind, LEQuery.ask, FreeM.countQueries_lift,
      FreeM.eval_lift, List.length_cons]
    rcases Bool.eq_false_or_eq_true (oracle (.le m x)) with h | h <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte, ih] <;> omega

/-- `findMin` makes exactly `n - 1` comparisons on a list of `n` elements, under every oracle. -/
@[simp] theorem countQueries_findMin (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (findMin xs).countQueries oracle = xs.length - 1 := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [findMin]

/-- **Upper bound for the minimum**: `findMin` makes at most `n - 1` comparisons on lists of
length at most `n`, under every oracle. -/
theorem findMin_upperBound : UpperBound (findMin (α := α)) List.length (· - 1) :=
  UpperBound.of_pointwise (fun _ _ h => Nat.sub_le_sub_right h 1)
    fun oracle xs => (countQueries_findMin oracle xs).le

private theorem findMinFrom_correct (r : α → α → Prop) [DecidableRel r] [Std.Total r]
    [IsTrans α r] (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) (m : α) (xs : List α) :
    ((findMinFrom m xs).eval oracle = m ∨ (findMinFrom m xs).eval oracle ∈ xs) ∧
      r ((findMinFrom m xs).eval oracle) m ∧
      ∀ x ∈ xs, r ((findMinFrom m xs).eval oracle) x := by
  have hrefl : ∀ a, r a a := fun a => (Std.Total.total a a).elim id id
  induction xs generalizing m with
  | nil => exact ⟨Or.inl rfl, hrefl m, by simp⟩
  | cons x xs ih =>
    simp only [findMinFrom, FreeM.eval_bind, LEQuery.ask, FreeM.eval_lift, horacle]
    by_cases hmx : r m x
    · simp only [hmx, decide_true, ↓reduceIte]
      obtain ⟨hmem, hle, hall⟩ := ih m
      refine ⟨hmem.imp_right (List.mem_cons_of_mem x), hle, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact _root_.trans hle hmx
      · exact hall y hy
    · simp only [hmx, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hxm : r x m := (Std.Total.total m x).resolve_left hmx
      obtain ⟨hmem, hle, hall⟩ := ih x
      refine ⟨Or.inr ?_, _root_.trans hle hxm, ?_⟩
      · rcases hmem with h | h
        · rw [h]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem x h
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hle
      · exact hall y hy

/-- **Correctness of the linear scan.** Against an oracle implementing a total preorder `r`,
`findMin xs` returns an element of `xs` that is `r`-below all elements of `xs`, for every nonempty
list `xs`. No antisymmetry is assumed. -/
theorem findMin_correct (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    {xs : List α} (hxs : xs ≠ []) :
    ∃ m, (findMin xs).eval oracle = some m ∧ m ∈ xs ∧ ∀ x ∈ xs, r m x := by
  obtain _ | ⟨y, ys⟩ := xs
  · exact absurd rfl hxs
  obtain ⟨hmem, hle, hall⟩ := findMinFrom_correct r oracle horacle y ys
  refine ⟨(findMinFrom y ys).eval oracle, by simp [findMin], ?_, ?_⟩
  · rcases hmem with h | h
    · rw [h]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem y h
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hle
    · exact hall x hx

/-- `findMin` is a correct algorithm for the minimum. -/
theorem findMin_isMinAlg : IsMinAlg (findMin (α := α)) where
  correct r _ _ oracle horacle _ hxs := findMin_correct r oracle horacle hxs

/-! ## Pairwise comparison -/

/-- Process `xs` in pairs, starting from the current minimum `m` and maximum `M`: compare the two
elements of a pair with each other, then the smaller with `m` and the larger with `M`; a last
unpaired element is compared with both `m` and `M`. -/
def findMinMaxFrom (m M : α) : List α → FreeM (LEQuery α) (α × α)
  | [] => return (m, M)
  | [x] => do
    let m' := if ← LEQuery.ask m x then m else x
    let M' := if ← LEQuery.ask x M then M else x
    return (m', M')
  | x :: y :: xs => do
    let b ← LEQuery.ask x y
    let s := if b then x else y
    let l := if b then y else x
    let m' := if ← LEQuery.ask m s then m else s
    let M' := if ← LEQuery.ask l M then M else l
    findMinMaxFrom m' M' xs

/-- The minimum and maximum of a list by pairwise comparison, or `none` for the empty list. A list
of even length starts from the comparison of its first two elements, a list of odd length from its
first element. -/
def findMinMax : List α → FreeM (LEQuery α) (Option (α × α))
  | [] => return none
  | [x] => return some (x, x)
  | x :: y :: xs =>
    if xs.length % 2 = 0 then do
      let b ← LEQuery.ask x y
      some <$> findMinMaxFrom (if b then x else y) (if b then y else x) xs
    else
      some <$> findMinMaxFrom x x (y :: xs)

/-- From a given minimum and maximum, three comparisons per pair and two for a last unpaired
element. -/
@[simp] theorem countQueries_findMinMaxFrom (oracle : {ι : Type} → LEQuery α ι → ι) (m M : α) :
    ∀ xs : List α,
      (findMinMaxFrom m M xs).countQueries oracle = 3 * (xs.length / 2) + 2 * (xs.length % 2)
  | [] => by simp [findMinMaxFrom]
  | [x] => by simp [findMinMaxFrom]
  | x :: y :: xs => by
    simp only [findMinMaxFrom, FreeM.countQueries_bind, LEQuery.ask, FreeM.countQueries_lift,
      FreeM.eval_lift, countQueries_findMinMaxFrom, List.length_cons]
    omega

/-- `findMinMax` makes exactly `(3n + 1) / 2 - 2 = ⌈3n/2⌉ - 2` comparisons on a list of `n`
elements, under every oracle (and none when `n ≤ 1`). -/
@[simp] theorem countQueries_findMinMax (oracle : {ι : Type} → LEQuery α ι → ι) (xs : List α) :
    (findMinMax xs).countQueries oracle = (3 * xs.length + 1) / 2 - 2 := by
  match xs with
  | [] => simp [findMinMax]
  | [x] => simp [findMinMax]
  | x :: y :: xs =>
    by_cases h : xs.length % 2 = 0
    · simp only [findMinMax, h, ↓reduceIte, FreeM.countQueries_bind, LEQuery.ask,
        FreeM.countQueries_lift, FreeM.countQueries_map, countQueries_findMinMaxFrom,
        List.length_cons]
      omega
    · simp only [findMinMax, h, ↓reduceIte, FreeM.countQueries_map, countQueries_findMinMaxFrom,
        List.length_cons]
      omega

/-- **Upper bound for the minimum and maximum**: `findMinMax` makes at most `⌈3n/2⌉ - 2`
comparisons on lists of length at most `n`, under every oracle. -/
theorem findMinMax_upperBound :
    UpperBound (findMinMax (α := α)) List.length (fun n => (3 * n + 1) / 2 - 2) :=
  UpperBound.of_pointwise (fun _ _ h => by omega)
    fun oracle xs => (countQueries_findMinMax oracle xs).le

section Correctness

variable {r : α → α → Prop} [DecidableRel r]

private theorem min_eq_or (a b : α) :
    (if r a b then a else b) = a ∨ (if r a b then a else b) = b := by
  split_ifs <;> simp

private theorem max_eq_or (a b : α) :
    (if r a b then b else a) = a ∨ (if r a b then b else a) = b := by
  split_ifs <;> simp

private theorem min_rel_left [Std.Total r] (a b : α) : r (if r a b then a else b) a := by
  split_ifs with h
  · exact (Std.Total.total a a).elim id id
  · exact (Std.Total.total a b).resolve_left h

private theorem min_rel_right [Std.Total r] (a b : α) : r (if r a b then a else b) b := by
  split_ifs with h
  · exact h
  · exact (Std.Total.total b b).elim id id

private theorem max_rel_left [Std.Total r] (a b : α) : r a (if r a b then b else a) := by
  split_ifs with h
  · exact h
  · exact (Std.Total.total a a).elim id id

private theorem max_rel_right [Std.Total r] (a b : α) : r b (if r a b then b else a) := by
  split_ifs with h
  · exact (Std.Total.total b b).elim id id
  · exact (Std.Total.total a b).resolve_left h

variable (r) in
/-- The invariant of `findMinMaxFrom m M xs` with result `p`: each component of `p` is the
corresponding one of `m`, `M` or an element of `xs`, and `p` bounds `m`, `M` and `xs`. -/
private def MinMaxInv (m M : α) (xs : List α) (p : α × α) : Prop :=
  (p.1 = m ∨ p.1 ∈ xs) ∧ (p.2 = M ∨ p.2 ∈ xs) ∧ r p.1 m ∧ r M p.2 ∧ ∀ x ∈ xs, r p.1 x ∧ r x p.2

omit [DecidableRel r] in
private theorem MinMaxInv.cons_cons [IsTrans α r] {m M m' M' x y : α} {xs : List α}
    {p : α × α} (h : MinMaxInv r m' M' xs p)
    (hm : m' = m ∨ m' = x ∨ m' = y) (hM : M' = M ∨ M' = x ∨ M' = y)
    (hmm : r m' m) (hmx : r m' x) (hmy : r m' y) (hMM : r M M') (hMx : r x M') (hMy : r y M') :
    MinMaxInv r m M (x :: y :: xs) p := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, _root_.trans h3 hmm, _root_.trans hMM h4, ?_⟩
  · rcases h1 with h1 | h1
    · rcases hm with hm | hm | hm <;> simp [h1, hm]
    · simp [h1]
  · rcases h2 with h2 | h2
    · rcases hM with hM | hM | hM <;> simp [h2, hM]
    · simp [h2]
  · intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨_root_.trans h3 hmx, _root_.trans hMx h4⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨_root_.trans h3 hmy, _root_.trans hMy h4⟩
    exact h5 z hz

private theorem findMinMaxFrom_correct [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    (m M : α) : ∀ xs : List α, MinMaxInv r m M xs ((findMinMaxFrom m M xs).eval oracle)
  | [] => by
    refine ⟨Or.inl rfl, Or.inl rfl, ?_, ?_, by simp⟩ <;>
      exact (Std.Total.total _ _).elim id id
  | [x] => by
    simp only [findMinMaxFrom, FreeM.eval_bind, LEQuery.ask, FreeM.eval_lift, horacle,
      decide_eq_true_eq, FreeM.eval_pure]
    refine ⟨?_, ?_, min_rel_left m x, max_rel_right x M, ?_⟩
    · rcases min_eq_or (r := r) m x with h | h <;> simp [h]
    · rcases max_eq_or (r := r) x M with h | h <;> simp [h]
    · simp only [List.mem_singleton, forall_eq]
      exact ⟨min_rel_right m x, max_rel_left x M⟩
  | x :: y :: xs => by
    simp only [findMinMaxFrom, FreeM.eval_bind, LEQuery.ask, FreeM.eval_lift, horacle,
      decide_eq_true_eq]
    refine MinMaxInv.cons_cons (findMinMaxFrom_correct oracle horacle _ _ xs) ?_ ?_
      (min_rel_left _ _) (_root_.trans (min_rel_right _ _) (min_rel_left x y))
      (_root_.trans (min_rel_right _ _) (min_rel_right x y)) (max_rel_right _ _)
      (_root_.trans (max_rel_left x y) (max_rel_left _ _))
      (_root_.trans (max_rel_right x y) (max_rel_left _ _))
    · have hs := min_eq_or (r := r) x y
      generalize (if r x y then x else y) = s at hs ⊢
      rcases min_eq_or (r := r) m s with h | h
      · exact Or.inl h
      · rcases hs with rfl | rfl <;> simp [h]
    · have hl := max_eq_or (r := r) x y
      generalize (if r x y then y else x) = l at hl ⊢
      rcases max_eq_or (r := r) l M with h | h
      · rcases hl with rfl | rfl <;> simp [h]
      · exact Or.inl h

/-- **Correctness of pairwise comparison.** Against an oracle implementing a total preorder `r`,
`findMinMax xs` returns a pair `(m, M)` of elements of `xs` with `m` below and `M` above all
elements of `xs`, for every nonempty list `xs`. No antisymmetry is assumed. -/
theorem findMinMax_correct (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    {xs : List α} (hxs : xs ≠ []) :
    ∃ m M, (findMinMax xs).eval oracle = some (m, M) ∧ m ∈ xs ∧ M ∈ xs ∧
      ∀ x ∈ xs, r m x ∧ r x M := by
  match xs, hxs with
  | [x], _ =>
    have hx : r x x := (Std.Total.total x x).elim id id
    exact ⟨x, x, rfl, by simp, by simp, by simp [hx]⟩
  | x :: y :: xs, _ =>
    by_cases h : xs.length % 2 = 0
    · simp only [findMinMax, h, ↓reduceIte, FreeM.eval_bind, LEQuery.ask, FreeM.eval_lift,
        FreeM.eval_map, horacle, decide_eq_true_eq]
      obtain ⟨h1, h2, h3, h4, h5⟩ :=
        findMinMaxFrom_correct oracle horacle (if r x y then x else y) (if r x y then y else x) xs
      generalize (findMinMaxFrom (if r x y then x else y) (if r x y then y else x) xs).eval oracle
        = p at h1 h2 h3 h4 h5 ⊢
      refine ⟨p.1, p.2, rfl, ?_, ?_, ?_⟩
      · rcases h1 with h1 | h1
        · rw [h1]; rcases min_eq_or (r := r) x y with h' | h' <;> rw [h'] <;> simp
        · simp [h1]
      · rcases h2 with h2 | h2
        · rw [h2]; rcases max_eq_or (r := r) x y with h' | h' <;> rw [h'] <;> simp
        · simp [h2]
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨_root_.trans h3 (min_rel_left _ y), _root_.trans (max_rel_left _ y) h4⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨_root_.trans h3 (min_rel_right x _), _root_.trans (max_rel_right x _) h4⟩
        exact h5 z hz
    · simp only [findMinMax, h, ↓reduceIte, FreeM.eval_map]
      obtain ⟨h1, h2, h3, h4, h5⟩ := findMinMaxFrom_correct oracle horacle x x (y :: xs)
      generalize (findMinMaxFrom x x (y :: xs)).eval oracle = p at h1 h2 h3 h4 h5 ⊢
      refine ⟨p.1, p.2, rfl, ?_, ?_, ?_⟩
      · rcases h1 with h1 | h1 <;> simp [h1]
      · rcases h2 with h2 | h2 <;> simp [h2]
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨h3, h4⟩
        exact h5 z hz

end Correctness

/-- `findMinMax` is a correct algorithm for the minimum and maximum. -/
theorem findMinMax_isMinMaxAlg : IsMinMaxAlg (findMinMax (α := α)) where
  correct r _ _ oracle horacle _ hxs := findMinMax_correct r oracle horacle hxs

end Cslib.Query
