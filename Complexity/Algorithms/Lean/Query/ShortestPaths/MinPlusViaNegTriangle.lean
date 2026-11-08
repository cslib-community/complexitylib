/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Query.Arith.MatMul
public import Complexity.Algorithms.ShortestPaths.NegativeTriangle
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Group.Abs

/-!
# The (min,+) product from all pairs on negative triangles, and the converse

The last step of the reduction of Vassilevska Williams and Williams from the (min,+) product to
negative triangle detection, and the easy converse, as programs in the query model `FreeM Q` that
call subroutines. Weights are `MinTropical (WithTop ℤ)`: integers and `⊤` (no edge).

* **The product by simultaneous binary search** (Theorem 4.2). `Cslib.Query.minPlusViaAPNT W apnt`
  computes `A * B` with an all-pairs subroutine `apnt`, which decides for every pair `(i, j)`
  whether it lies on a negative triangle of the tripartite graph with weights `A`, `B`, `C`. It
  keeps an interval `[lo, hi)` for every entry and calls `apnt` once per round, with
  `C i j = -mid` for the midpoint `mid` of the interval; the pair lies on a negative triangle iff
  `(A * B) i j < mid`. If the finite entries of `A * B` lie in `[-W, W]`, after
  `⌈log₂ (2 W + 2)⌉` rounds every interval has length `1`, and the program costs exactly
  `⌈log₂ (2 W + 2)⌉` calls of `apnt`. An entry `⊤` is tracked as the value `W + 1`.
* **The converse.** `Cslib.Query.negTriViaMinPlus mp` decides whether a tripartite graph has a
  negative triangle with one call of a (min,+) product subroutine `mp`, by testing
  `(A * B) i j + C i j < 0` for every pair. With the schoolbook product this is a cubic detector.

**What is charged.** `FreeM` charges only the subroutine calls. The interval bookkeeping (the
midpoints, the weights `-mid` and the updates) of the binary search and the `n ^ 2` final
comparisons of the converse are pure code and are free, as in the other query-model reductions in
this library. In a RAM implementation they cost `O(n ^ 2)` per round, and `O(n ^ 2)`.

**Scope.** Vassilevska Williams and Williams allow weights in `{-W, …, W} ∪ {-∞, ∞}`; here there is
no `-∞`. The weights `-mid` of the queries lie in `[-(W + 1), W]`.

## Main definitions

* `Cslib.Query.bsRounds`: rounds of simultaneous binary search with an all-pairs subroutine.
* `Cslib.Query.minPlusViaAPNT`: the (min,+) product by simultaneous binary search.
* `Cslib.Query.negTriViaMinPlus`: negative triangle detection with one (min,+) product.

## Main results

* `Cslib.Query.eval_minPlusViaAPNT`, `Cslib.Query.cost_minPlusViaAPNT_le`,
  `Cslib.Query.cost_minPlusViaAPNT`: the product by `⌈log₂ (2 W + 2)⌉` all-pairs calls.
* `Cslib.Query.eval_negTriViaMinPlus`, `Cslib.Query.cost_negTriViaMinPlus`: detection by one
  product.
* `Cslib.Query.eval_negTriViaMinPlus_schoolbook`, `Cslib.Query.cost_negTriViaMinPlus_schoolbook`:
  the schoolbook detector.

## References

* [Vassilevska Williams and Williams, *Subcubic Equivalences Between Path, Matrix, and Triangle
  Problems*][VassilevskaWilliamsWilliams2018], Theorem 4.1 and Theorem 4.2.
-/

public section

open MinTropical Cslib.Algorithms.ShortestPaths

namespace Cslib.Query

variable {Q : Type → Type}

/-! ### The (min,+) product by simultaneous binary search (Theorem 4.2) -/

section BinarySearch

variable {I : Type}

/-- The midpoint `⌊(lo + hi) / 2⌋` of the interval `[lo, hi)`. -/
@[expose] def bsMid (lo hi : ℤ) : ℤ := (lo + hi) / 2

/-- The `I`–`J` weights of a round: `-mid` for the midpoint `mid` of the interval of each pair. -/
@[expose] def bsQuery (s : I → I → ℤ × ℤ) : Matrix I I (MinTropical (WithTop ℤ)) :=
  Matrix.of fun i j => trop (((-bsMid (s i j).1 (s i j).2 : ℤ)) : WithTop ℤ)

/-- `r` rounds of simultaneous binary search. Each round calls `apnt` with the weights
`bsQuery s` and replaces the interval `[lo, hi)` of `(i, j)` by `[lo, mid)` if the pair lies on a
negative triangle, and by `[mid, hi)` otherwise. -/
@[expose] def bsRounds
    (apnt : Matrix I I (MinTropical (WithTop ℤ)) → Matrix I I (MinTropical (WithTop ℤ)) →
      Matrix I I (MinTropical (WithTop ℤ)) → FreeM Q (I → I → Bool))
    (A B : Matrix I I (MinTropical (WithTop ℤ))) :
    ℕ → (I → I → ℤ × ℤ) → FreeM Q (I → I → ℤ × ℤ)
  | 0, s => pure s
  | r + 1, s => do
    let P ← apnt A B (bsQuery s)
    bsRounds apnt A B r fun i j =>
      if P i j then ((s i j).1, bsMid (s i j).1 (s i j).2)
      else (bsMid (s i j).1 (s i j).2, (s i j).2)

/-- Read an entry off the lower end `lo` of its final interval: `W + 1` stands for `⊤`. -/
@[expose] def bsDecode (W : ℕ) (lo : ℤ) : MinTropical (WithTop ℤ) :=
  if lo = W + 1 then trop ⊤ else trop (lo : WithTop ℤ)

/-- **The (min,+) product by simultaneous binary search** (Vassilevska Williams–Williams,
Theorem 4.2): start with the interval `[-W, W + 2)` for every entry, run `⌈log₂ (2 W + 2)⌉`
rounds of `bsRounds`, and decode the lower ends. -/
@[expose] def minPlusViaAPNT (W : ℕ)
    (apnt : Matrix I I (MinTropical (WithTop ℤ)) → Matrix I I (MinTropical (WithTop ℤ)) →
      Matrix I I (MinTropical (WithTop ℤ)) → FreeM Q (I → I → Bool))
    (A B : Matrix I I (MinTropical (WithTop ℤ))) : FreeM Q (Matrix I I (MinTropical (WithTop ℤ))) :=
  do
    let s ← bsRounds apnt A B (Nat.clog 2 (2 * W + 2)) fun _ _ => (-(W : ℤ), (W : ℤ) + 2)
    return Matrix.of fun i j => bsDecode W (s i j).1

/-! #### Cost -/

theorem cost_bsRounds_le {T : Type} [AddCommMonoid T] [PartialOrder T] [IsOrderedAddMonoid T]
    (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → T)
    {apnt : Matrix I I (MinTropical (WithTop ℤ)) → Matrix I I (MinTropical (WithTop ℤ)) →
      Matrix I I (MinTropical (WithTop ℤ)) → FreeM Q (I → I → Bool)}
    {A B : Matrix I I (MinTropical (WithTop ℤ))} {τ : T}
    (happnt : ∀ C, (apnt A B C).cost oracle weight ≤ τ) :
    ∀ (r : ℕ) (s : I → I → ℤ × ℤ), (bsRounds apnt A B r s).cost oracle weight ≤ r • τ
  | 0, s => by simp [bsRounds]
  | r + 1, s => by
    rw [bsRounds, FreeM.cost_bind, _root_.succ_nsmul']
    exact add_le_add (happnt _) (cost_bsRounds_le oracle weight happnt r _)

theorem cost_bsRounds {T : Type} [AddMonoid T] (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → T)
    {apnt : Matrix I I (MinTropical (WithTop ℤ)) → Matrix I I (MinTropical (WithTop ℤ)) →
      Matrix I I (MinTropical (WithTop ℤ)) → FreeM Q (I → I → Bool)}
    {A B : Matrix I I (MinTropical (WithTop ℤ))} {τ : T}
    (happnt : ∀ C, (apnt A B C).cost oracle weight = τ) :
    ∀ (r : ℕ) (s : I → I → ℤ × ℤ), (bsRounds apnt A B r s).cost oracle weight = r • τ
  | 0, s => by simp [bsRounds]
  | r + 1, s => by
    rw [bsRounds, FreeM.cost_bind, _root_.succ_nsmul', happnt, cost_bsRounds oracle weight happnt r]

/-- **Theorem 4.2, cost.** If every call of `apnt A B` costs at most `τ` under `oracle`, then
`minPlusViaAPNT W apnt A B` costs at most `⌈log₂ (2 W + 2)⌉ τ`. -/
theorem cost_minPlusViaAPNT_le {T : Type} [AddCommMonoid T] [PartialOrder T]
    [IsOrderedAddMonoid T] (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → T)
    (W : ℕ) {apnt : Matrix I I (MinTropical (WithTop ℤ)) → Matrix I I (MinTropical (WithTop ℤ)) →
      Matrix I I (MinTropical (WithTop ℤ)) → FreeM Q (I → I → Bool)}
    {A B : Matrix I I (MinTropical (WithTop ℤ))} {τ : T}
    (happnt : ∀ C, (apnt A B C).cost oracle weight ≤ τ) :
    (minPlusViaAPNT W apnt A B).cost oracle weight ≤ Nat.clog 2 (2 * W + 2) • τ := by
  rw [minPlusViaAPNT, FreeM.cost_bind, FreeM.cost_pure, add_zero]
  exact cost_bsRounds_le oracle weight happnt _ _

/-- The cost of `minPlusViaAPNT W apnt A B`: exactly `⌈log₂ (2 W + 2)⌉` times the cost of a call
of `apnt A B`, when that cost does not depend on the weights `C`. -/
theorem cost_minPlusViaAPNT {T : Type} [AddMonoid T] (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → T) (W : ℕ)
    {apnt : Matrix I I (MinTropical (WithTop ℤ)) → Matrix I I (MinTropical (WithTop ℤ)) →
      Matrix I I (MinTropical (WithTop ℤ)) → FreeM Q (I → I → Bool)}
    {A B : Matrix I I (MinTropical (WithTop ℤ))} {τ : T}
    (happnt : ∀ C, (apnt A B C).cost oracle weight = τ) :
    (minPlusViaAPNT W apnt A B).cost oracle weight = Nat.clog 2 (2 * W + 2) • τ := by
  rw [minPlusViaAPNT, FreeM.cost_bind, FreeM.cost_pure, add_zero]
  exact cost_bsRounds oracle weight happnt _ _

/-! #### Correctness -/

/-- An entry `w` with finite part in `[-W, W]` has a threshold value `v ∈ [-W, W + 1]` (`W + 1`
for `⊤`): `w - m < 0` iff `v < m` for every `m ≤ W + 1`, and `bsDecode W v = trop w`. -/
private theorem exists_threshold {W : ℕ} :
    ∀ {w : WithTop ℤ}, (∀ x : ℤ, w = x → |x| ≤ W) →
      ∃ v : ℤ, -(W : ℤ) ≤ v ∧ v ≤ W + 1 ∧ bsDecode W v = trop w ∧
        ∀ m : ℤ, m ≤ W + 1 → (w + ((-m : ℤ) : WithTop ℤ) < 0 ↔ v < m)
  | ⊤, _ => by
    refine ⟨W + 1, by omega, le_rfl, by rw [bsDecode, ite_eq_left rfl],
      fun m hm => ?_⟩
    rw [top_add]
    exact ⟨fun h => absurd h not_top_lt, fun h => absurd hm (not_le.2 h)⟩
  | (x : ℤ), hd => by
    obtain ⟨h1, h2⟩ := abs_le.1 (hd x rfl)
    refine ⟨x, h1, by omega, ?_, fun m _ => ?_⟩
    · rw [bsDecode, ite_eq_right (by omega)]
    · rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_lt_coe]
      omega

variable [Fintype I]

/-- **Theorem 4.2, correctness.** If the finite entries of `A * B` lie in `[-W, W]` and `apnt A B`
decides, for all weights `C`, which pairs lie on a negative triangle, then
`minPlusViaAPNT W apnt A B` computes the (min,+) product `A * B`. -/
theorem eval_minPlusViaAPNT (oracle : {ι : Type} → Q ι → ι) {W : ℕ}
    {apnt : Matrix I I (MinTropical (WithTop ℤ)) → Matrix I I (MinTropical (WithTop ℤ)) →
      Matrix I I (MinTropical (WithTop ℤ)) → FreeM Q (I → I → Bool)}
    {A B : Matrix I I (MinTropical (WithTop ℤ))} (hAB : FiniteEntriesBounded (A * B) W)
    (happnt : ∀ C x y, (apnt A B C).eval oracle x y = decide (OnNegTriangle A B C x y)) :
    (minPlusViaAPNT W apnt A B).eval oracle = A * B := by
  choose v hv using fun i j => exists_threshold (hAB i j)
  -- The invariant `lo ≤ v < hi ≤ W + 2` with `hi - lo ≤ 2 ^ r` before the last `r` rounds.
  have key : ∀ (r : ℕ) (s : I → I → ℤ × ℤ), (∀ i j, (s i j).1 ≤ v i j ∧ v i j < (s i j).2 ∧
      (s i j).2 ≤ W + 2 ∧ (s i j).2 - (s i j).1 ≤ 2 ^ r) →
      ∀ i j, ((bsRounds apnt A B r s).eval oracle i j).1 = v i j := by
    intro r
    induction r with
    | zero =>
      intro s hs i j
      obtain ⟨h1, h2, -, h4⟩ := hs i j
      rw [bsRounds, FreeM.eval_pure]
      rw [pow_zero] at h4
      omega
    | succ r ih =>
      intro s hs
      rw [bsRounds, FreeM.eval_bind]
      apply ih
      intro i j
      obtain ⟨h1, h2, h3, h4⟩ := hs i j
      have hm : bsMid (s i j).1 (s i j).2 ≤ W + 1 := by rw [bsMid]; omega
      have hP : (apnt A B (bsQuery s)).eval oracle i j = true ↔
          v i j < bsMid (s i j).1 (s i j).2 := by
        rw [happnt, decide_eq_true_iff, onNegTriangle_iff, bsQuery, Matrix.of_apply, untrop_trop,
          (hv i j).2.2.2 _ hm]
      rw [pow_succ] at h4
      generalize (2 : ℤ) ^ r = p at h4 ⊢
      by_cases hb : (apnt A B (bsQuery s)).eval oracle i j = true
      · have := hP.1 hb
        simp only [hb, ite_true]
        rw [bsMid] at this ⊢
        refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
      · have := mt hP.2 hb
        simp only [hb, Bool.false_eq_true, ite_false]
        rw [bsMid] at this ⊢
        refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  have hW : ((2 * W + 2 : ℕ) : ℤ) ≤ 2 ^ Nat.clog 2 (2 * W + 2) := by
    exact_mod_cast Nat.le_pow_clog one_lt_two _
  push_cast at hW
  have h := key (Nat.clog 2 (2 * W + 2)) (fun _ _ => (-(W : ℤ), (W : ℤ) + 2)) fun i j => by
    have := (hv i j).1
    have := (hv i j).2.1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega
  rw [minPlusViaAPNT, FreeM.eval_bind, FreeM.eval_pure]
  ext i j
  rw [Matrix.of_apply, h i j]
  exact (hv i j).2.2.1.trans (trop_untrop _)

end BinarySearch

/-! ### Detection from one (min,+) product (the converse) -/

section Converse

variable {R : Type} [LinearOrderedAddCommMonoidWithTop R] {I : Type} [Fintype I]

/-- **Negative triangle detection with one (min,+) product**: compute `D = A * B` with `mp` and
test whether `D i j + C i j < 0` for some pair. -/
@[expose] def negTriViaMinPlus
    (mp : Matrix I I (MinTropical R) → Matrix I I (MinTropical R) →
      FreeM Q (Matrix I I (MinTropical R)))
    (A B C : Matrix I I (MinTropical R)) : FreeM Q Bool := do
  let D ← mp A B
  return decide (∃ i j, untrop (D i j) + untrop (C i j) < 0)

/-- The cost of `negTriViaMinPlus mp A B C` is the cost of its one call of `mp`. -/
theorem cost_negTriViaMinPlus {T : Type} [AddMonoid T] (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → T)
    (mp : Matrix I I (MinTropical R) → Matrix I I (MinTropical R) →
      FreeM Q (Matrix I I (MinTropical R)))
    (A B C : Matrix I I (MinTropical R)) :
    (negTriViaMinPlus mp A B C).cost oracle weight = (mp A B).cost oracle weight := by
  rw [negTriViaMinPlus, FreeM.cost_bind, FreeM.cost_pure, add_zero]

/-- **Detection reduces to the (min,+) product.** If `mp A B` computes `A * B` under `oracle`,
then `negTriViaMinPlus mp A B C` decides whether the tripartite graph has a negative triangle. -/
theorem eval_negTriViaMinPlus (oracle : {ι : Type} → Q ι → ι)
    {mp : Matrix I I (MinTropical R) → Matrix I I (MinTropical R) →
      FreeM Q (Matrix I I (MinTropical R))}
    {A B : Matrix I I (MinTropical R)} (hmp : (mp A B).eval oracle = A * B)
    (C : Matrix I I (MinTropical R)) :
    (negTriViaMinPlus mp A B C).eval oracle = decide (HasNegTriangle A B C) := by
  rw [negTriViaMinPlus, FreeM.eval_bind, hmp, FreeM.eval_pure]
  exact decide_eq_decide.2 (hasNegTriangle_iff A B C).symm

/-- The schoolbook detector decides negative triangles. -/
theorem eval_negTriViaMinPlus_schoolbook
    (oracle : {ι : Type} → ArithQuery (MinTropical R) ι → ι)
    (hadd : ∀ a b, oracle (.add a b) = a + b) (hmul : ∀ a b, oracle (.mul a b) = a * b) (n : ℕ)
    (A B C : Matrix (Fin n) (Fin n) (MinTropical R)) :
    (negTriViaMinPlus (schoolbookMatMul n) A B C).eval oracle = decide (HasNegTriangle A B C) :=
  eval_negTriViaMinPlus oracle (eval_schoolbookMatMul oracle hadd hmul n A B) C

/-- The schoolbook detector costs `n ^ 2 (n cMul + (n - 1) cAdd)` under every oracle. -/
theorem cost_negTriViaMinPlus_schoolbook
    (oracle : {ι : Type} → ArithQuery (MinTropical R) ι → ι) (cAdd cMul n : ℕ)
    (A B C : Matrix (Fin n) (Fin n) (MinTropical R)) :
    (negTriViaMinPlus (schoolbookMatMul n) A B C).cost oracle (ArithQuery.weight cAdd cMul) =
      n ^ 2 * (n * cMul + (n - 1) * cAdd) := by
  rw [cost_negTriViaMinPlus, cost_schoolbookMatMul]

end Converse

end Cslib.Query
