/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Query.ShortestPaths.MinPlusViaNegTriangle
public import Complexity.Algorithms.Lean.Query.ShortestPaths.NegTriangleFinding
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A truly subcubic negative triangle detector gives a truly subcubic (min,+) product

The reduction of Vassilevska Williams and Williams (Theorem 4.2) from the (min,+) product of
`n × n` matrices to negative triangle detection, in the query model `FreeM Q`, assembled from its
three steps: finding by halving (Lemma 4.1), all pairs on negative triangles by blocking
(Lemma 4.2), and simultaneous binary search (Theorem 4.2). Weights are
`MinTropical (WithTop ℤ)`: integers and `⊤` (no edge).

`Cslib.Query.minPlusViaNegTri det W` uses blocks of size `s = 2 ^ L` with
`L = ⌊⌊log₂ n⌋ / 3⌋`, so `s ^ 3 ≤ n < 8 s ^ 3`, and `t = ⌊n / s⌋ + 1` blocks, padding the graph
with isolated vertices to `t s` vertices per part. It calls the detection subroutine `det` only
on sub-instances with `2 ^ l ≤ s` vertices per part.

* **Correctness** (`Cslib.Query.eval_minPlusViaNegTri`). If `det` decides negative triangles and
  the finite entries of `A * B` lie in `[-W, W]`, the result is `A * B`.
* **Cost** (`Cslib.Query.cost_minPlusViaNegTri_le`). If every call of `det m` with `m ≠ 0` costs
  at most `τ m`, and `τ ≥ 0`, the program costs at most
  `⌈log₂ (2 W + 2)⌉ (t ^ 3 + (t s) ^ 2) (τ 1 + ∑_{l < L} 8 τ (2 ^ l))`.
* **Exponent** (`Cslib.Query.cost_minPlusViaNegTri_le_rpow`). If `τ m = c m ^ (3 - δ)` for
  `m ≠ 0`, with `c ≥ 0` and `δ ≤ 2`, the cost is at most
  `544 c ⌈log₂ (2 W + 2)⌉ n ^ (3 - δ / 3)` for `n ≥ 1`.
  So a detector with `O(n ^ (3 - δ))` cost gives a (min,+) product with `O(n ^ (3 - δ / 3) log W)`
  cost: truly subcubic detection gives a truly subcubic product, with `δ' = δ / 3`. This is the
  bound `O(n ^ 2 T(n ^ (1 / 3)) log W)` of Theorem 4.2 for `T(n) = n ^ (3 - δ)`.

**What is charged.** `FreeM` charges only the calls of `det`. Building sub-instances, the loops,
the padding, the bookkeeping of removed edges and the binary search intervals are pure code and
are free; see the module docstrings of the three steps. The cost bounds hold under every oracle
and weight, given nonnegative per-call bounds. They transfer the reduction's pattern of detector
calls and are not intrinsic bounds on either problem: in this model a detector that decides in
pure code, issuing no queries, satisfies the hypothesis of `cost_minPlusViaNegTri_le_rpow` with
`c = 0`.

**Scope.** Vassilevska Williams and Williams allow weights in `{-W, …, W} ∪ {-∞, ∞}`; here there is
no `-∞`. Their `W` is the largest finite weight of the structure, which bounds the inputs, and
their product saturates outside `[-W, W]` (footnote 6). Here weights are added in `ℤ ∪ {⊤}`
without saturation, and `W` bounds the finite entries of the product `A * B`; inputs with finite
entries in `[-M, M]` give `W = 2 M` (`Cslib.Query.eval_minPlusViaNegTri_of_bounded`). The
detector must be correct on all weights in `ℤ ∪ {⊤}`; the binary search queries it with `I`–`J`
weights in `[-(W + 1), W]` and the given `A`, `B`.

## Main definitions

* `Cslib.Query.negTriBlockExp`, `Cslib.Query.negTriBlocks`: the block size `2 ^ L` and the number
  of blocks `t`.
* `Cslib.Query.negTriPad`: padding `Fin n` to `Fin t × Fin (2 ^ L)`.
* `Cslib.Query.minPlusViaNegTri`: the (min,+) product with a negative triangle detector.

## Main results

* `Cslib.Query.lt_negTriBlocks_mul`, `Cslib.Query.negTriBlockExp_pow_le`,
  `Cslib.Query.lt_eight_mul_negTriBlockExp_pow`: `n < t 2 ^ L` and
  `(2 ^ L) ^ 3 ≤ n < 8 (2 ^ L) ^ 3`.
* `Cslib.Query.negTriBlocks_calls_le`: the blocking reduction makes
  `t ^ 3 + (t 2 ^ L) ^ 2 ≤ 68 n ^ 2` finder calls.
* `Cslib.Query.findNegTriCost_rpow_le`: Lemma 4.1 for polynomial costs, `T'(n) = O(T(n))`.
* `Cslib.Query.eval_minPlusViaNegTri`, `Cslib.Query.eval_minPlusViaNegTri_of_bounded`: correctness.
* `Cslib.Query.cost_minPlusViaNegTri_le`: the cost in terms of per-call bounds.
* `Cslib.Query.cost_minPlusViaNegTri_le_rpow`: the exponent `3 - δ / 3`.

## References

* [Vassilevska Williams and Williams, *Subcubic Equivalences Between Path, Matrix, and Triangle
  Problems*][VassilevskaWilliamsWilliams2018], Lemma 4.1, Lemma 4.2 and Theorem 4.2.
-/

public section

open MinTropical Cslib.Algorithms.ShortestPaths

namespace Cslib.Query

/-! ### Block sizes and padding -/

/-- The block size exponent `L = ⌊⌊log₂ n⌋ / 3⌋`: blocks have `2 ^ L ≈ n ^ (1 / 3)` vertices. -/
@[expose] def negTriBlockExp (n : ℕ) : ℕ := Nat.log 2 n / 3

/-- The number of blocks `t = ⌊n / 2 ^ L⌋ + 1`, so that `n < t 2 ^ L`. -/
@[expose] def negTriBlocks (n : ℕ) : ℕ := n / 2 ^ negTriBlockExp n + 1

theorem lt_negTriBlocks_mul (n : ℕ) : n < negTriBlocks n * 2 ^ negTriBlockExp n := by
  rw [negTriBlocks, add_mul, one_mul]
  exact Nat.lt_div_mul_add (pow_pos two_pos _)

/-- Pad `Fin n` with isolated vertices to `t` blocks of `2 ^ L` vertices. -/
@[expose] def negTriPad (n : ℕ) :
    Fin (negTriBlocks n) × Fin (2 ^ negTriBlockExp n) ≃
      Fin n ⊕ Fin (negTriBlocks n * 2 ^ negTriBlockExp n - n) :=
  finProdFinEquiv.trans
    ((finCongr (Nat.add_sub_cancel' (lt_negTriBlocks_mul n).le).symm).trans finSumFinEquiv.symm)

theorem negTriBlockExp_pow_le {n : ℕ} (hn : n ≠ 0) : (2 ^ negTriBlockExp n) ^ 3 ≤ n := by
  rw [← pow_mul]
  exact (Nat.pow_le_pow_right two_pos (Nat.div_mul_le_self _ _)).trans (Nat.pow_log_le_self 2 hn)

theorem lt_eight_mul_negTriBlockExp_pow (n : ℕ) : n < 8 * (2 ^ negTriBlockExp n) ^ 3 := by
  rw [← pow_mul, show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_add]
  refine (Nat.lt_pow_succ_log_self one_lt_two n).trans_le (Nat.pow_le_pow_right two_pos ?_)
  rw [negTriBlockExp]
  omega

/-- The number of calls of the finder: `t ^ 3 + (t 2 ^ L) ^ 2 ≤ 68 n ^ 2` for `n ≥ 1`. -/
theorem negTriBlocks_calls_le {n : ℕ} (hn : n ≠ 0) :
    negTriBlocks n ^ 3 + (negTriBlocks n * 2 ^ negTriBlockExp n) ^ 2 ≤ 68 * n ^ 2 := by
  have h1 := negTriBlockExp_pow_le hn
  have h2 := lt_eight_mul_negTriBlockExp_pow n
  have hs : 1 ≤ 2 ^ negTriBlockExp n := Nat.one_le_two_pow
  have hts : negTriBlocks n * 2 ^ negTriBlockExp n ≤ 2 * n := by
    have := Nat.div_mul_le_self n (2 ^ negTriBlockExp n)
    have : 2 ^ negTriBlockExp n ≤ (2 ^ negTriBlockExp n) ^ 3 := Nat.le_self_pow (by norm_num) _
    rw [negTriBlocks, add_mul, one_mul]
    omega
  generalize negTriBlocks n = t at hts ⊢
  generalize 2 ^ negTriBlockExp n = s at h1 h2 hs hts ⊢
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  have ht3 : t ^ 3 < 64 * n ^ 2 := by
    have h3 : (t * s) ^ 3 ≤ (2 * n) ^ 3 := Nat.pow_le_pow_left hts 3
    have h4 : t ^ 3 * n < t ^ 3 * (8 * s ^ 3) ∨ t = 0 := by
      rcases Nat.eq_zero_or_pos t with ht | ht
      · exact .inr ht
      · exact .inl (Nat.mul_lt_mul_of_pos_left h2 (pow_pos ht _))
    rcases h4 with h4 | rfl
    · refine Nat.lt_of_mul_lt_mul_right (a := n) ?_
      calc t ^ 3 * n < t ^ 3 * (8 * s ^ 3) := h4
        _ = 8 * (t * s) ^ 3 := by ring
        _ ≤ 8 * (2 * n) ^ 3 := Nat.mul_le_mul_left _ h3
        _ = 64 * n ^ 2 * n := by ring
    · positivity
  have hts2 : (t * s) ^ 2 ≤ 4 * n ^ 2 := by
    calc (t * s) ^ 2 ≤ (2 * n) ^ 2 := Nat.pow_le_pow_left hts 2
      _ = 4 * n ^ 2 := by ring
  omega

/-! ### The reduction -/

section Reduction

variable {Q : Type → Type}

/-- **The (min,+) product with a negative triangle detector** (Vassilevska Williams–Williams,
Theorem 4.2): simultaneous binary search, where each round runs the blocking reduction on the
padded graph with blocks of size `2 ^ L`, finding triangles in blocks by halving with `det`. -/
@[expose] def minPlusViaNegTri
    (det : (m : ℕ) → Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) →
      Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) →
      Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) → FreeM Q Bool)
    (W : ℕ) {n : ℕ} (A B : Matrix (Fin n) (Fin n) (MinTropical (WithTop ℤ))) :
    FreeM Q (Matrix (Fin n) (Fin n) (MinTropical (WithTop ℤ))) :=
  minPlusViaAPNT W
    (padAPNT (negTriPad n) (allPairsNegTri (findNegTri det (negTriBlockExp n)))) A B

/-- **Theorem 4.2, correctness.** If `det` decides negative triangles under `oracle` and the
finite entries of `A * B` lie in `[-W, W]`, then `minPlusViaNegTri det W A B` computes `A * B`. -/
theorem eval_minPlusViaNegTri (oracle : {ι : Type} → Q ι → ι)
    {det : (m : ℕ) → Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) →
      Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) →
      Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) → FreeM Q Bool}
    (hdet : ∀ m A B C, (det m A B C).eval oracle = decide (HasNegTriangle A B C)) {W n : ℕ}
    {A B : Matrix (Fin n) (Fin n) (MinTropical (WithTop ℤ))}
    (hAB : FiniteEntriesBounded (A * B) W) :
    (minPlusViaNegTri det W A B).eval oracle = A * B :=
  eval_minPlusViaAPNT oracle hAB fun C =>
    padAPNT_eval oracle (negTriPad n) A B C
      (allPairsNegTri_eval oracle (isNegTriangleAnswer_findNegTri oracle hdet _) _ _ _)

/-- Correctness when the finite entries of `A` and `B` lie in `[-M, M]`: binary search on
`[-2M, 2M]`. -/
theorem eval_minPlusViaNegTri_of_bounded (oracle : {ι : Type} → Q ι → ι)
    {det : (m : ℕ) → Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) →
      Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) →
      Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) → FreeM Q Bool}
    (hdet : ∀ m A B C, (det m A B C).eval oracle = decide (HasNegTriangle A B C)) {M n : ℕ}
    {A B : Matrix (Fin n) (Fin n) (MinTropical (WithTop ℤ))} (hA : FiniteEntriesBounded A M)
    (hB : FiniteEntriesBounded B M) :
    (minPlusViaNegTri det (2 * M) A B).eval oracle = A * B :=
  eval_minPlusViaNegTri oracle hdet (hA.mul hB)

/-- **Theorem 4.2, cost.** If every call of `det m` with `m ≠ 0` costs at most `τ m` under
`oracle`, and `τ ≥ 0`, then
`minPlusViaNegTri det W A B` costs at most
`⌈log₂ (2 W + 2)⌉ (t ^ 3 + (t 2 ^ L) ^ 2) (τ 1 + ∑_{l < L} 8 τ (2 ^ l))`. -/
theorem cost_minPlusViaNegTri_le {T : Type} [AddCommMonoid T] [PartialOrder T]
    [IsOrderedAddMonoid T] (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → T)
    {det : (m : ℕ) → Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) →
      Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) →
      Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) → FreeM Q Bool}
    {τ : ℕ → T} (hτ : ∀ m, 0 ≤ τ m)
    (hdet : ∀ m, m ≠ 0 → ∀ A B C, (det m A B C).cost oracle weight ≤ τ m) (W : ℕ) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (MinTropical (WithTop ℤ))) :
    (minPlusViaNegTri det W A B).cost oracle weight ≤
      Nat.clog 2 (2 * W + 2) • ((negTriBlocks n ^ 3 +
        (negTriBlocks n * 2 ^ negTriBlockExp n) ^ 2) • findNegTriCost τ (negTriBlockExp n)) := by
  refine cost_minPlusViaAPNT_le oracle weight W fun C => ?_
  rw [cost_padAPNT]
  refine (cost_allPairsNegTri_le oracle weight (findNegTriCost_nonneg hτ _)
    (cost_findNegTri_le oracle weight hτ hdet _) _ _ _).trans (le_of_eq ?_)
  rw [Fintype.card_fin]

/-! ### The exponent -/

/-- **Lemma 4.1 for polynomial costs.** With `τ m = c m ^ e`, `c ≥ 0` and `e ≥ 1`, the finding
cost bound `findNegTriCost τ L` is at most `8 c (2 ^ L) ^ e`: finding a negative triangle costs
`O(T(n))` when detection costs `T(n) = c n ^ e`. -/
theorem findNegTriCost_rpow_le {c e : ℝ} (hc : 0 ≤ c) (he : 1 ≤ e) (L : ℕ) :
    findNegTriCost (fun m : ℕ => c * (m : ℝ) ^ e) L ≤ 8 * c * ((2 ^ L : ℕ) : ℝ) ^ e := by
  have hx : (2 : ℝ) ≤ (2 : ℝ) ^ e := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  have hpow : ∀ l : ℕ, ((2 ^ l : ℕ) : ℝ) ^ e = ((2 : ℝ) ^ e) ^ l := fun l => by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  induction L with
  | zero =>
    rw [findNegTriCost_zero, pow_zero, Nat.cast_one, Real.one_rpow, mul_one, mul_one]
    linarith
  | succ L ih =>
    rw [findNegTriCost_succ, nsmul_eq_mul, hpow, hpow] at *
    rw [pow_succ]
    have h0 : 0 ≤ ((2 : ℝ) ^ e) ^ L := pow_nonneg (by positivity) _
    have h1 : 0 ≤ c * ((2 : ℝ) ^ e) ^ L := mul_nonneg hc h0
    push_cast
    nlinarith

/-- **A truly subcubic detector gives a truly subcubic (min,+) product** (Vassilevska
Williams–Williams, Theorem 4.2 with `T(n) = n ^ (3 - δ)`). If every call of `det m` costs at most
`c m ^ (3 - δ)` under `oracle` for `m ≠ 0`, with `c ≥ 0` and `δ ≤ 2`, then for `n ≥ 1`,
`minPlusViaNegTri det W A B` costs at most `544 c ⌈log₂ (2 W + 2)⌉ n ^ (3 - δ / 3)`. -/
theorem cost_minPlusViaNegTri_le_rpow (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → ℝ)
    {det : (m : ℕ) → Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) →
      Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) →
      Matrix (Fin m) (Fin m) (MinTropical (WithTop ℤ)) → FreeM Q Bool}
    {c δ : ℝ} (hc : 0 ≤ c) (hδ : δ ≤ 2)
    (hdet : ∀ m, m ≠ 0 → ∀ A B C, (det m A B C).cost oracle weight ≤ c * (m : ℝ) ^ (3 - δ))
    (W : ℕ) {n : ℕ} (hn : n ≠ 0) (A B : Matrix (Fin n) (Fin n) (MinTropical (WithTop ℤ))) :
    (minPlusViaNegTri det W A B).cost oracle weight ≤
      544 * c * Nat.clog 2 (2 * W + 2) * (n : ℝ) ^ (3 - δ / 3) := by
  have he : 1 ≤ 3 - δ := by linarith
  have hτ : ∀ m : ℕ, 0 ≤ c * (m : ℝ) ^ (3 - δ) := fun m => mul_nonneg hc (by positivity)
  refine (cost_minPlusViaNegTri_le oracle weight hτ hdet W A B).trans ?_
  set L := negTriBlockExp n
  set F := findNegTriCost (fun m : ℕ => c * (m : ℝ) ^ (3 - δ)) L
  have hF0 : 0 ≤ F := findNegTriCost_nonneg hτ L
  have hF : F ≤ 8 * c * (n : ℝ) ^ ((3 - δ) / 3) := by
    refine (findNegTriCost_rpow_le hc he L).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h3 : (((2 ^ L : ℕ) : ℝ) ^ 3) ≤ n := by exact_mod_cast negTriBlockExp_pow_le hn
    calc ((2 ^ L : ℕ) : ℝ) ^ (3 - δ) = ((((2 ^ L : ℕ) : ℝ) ^ 3) ^ ((3 - δ) / 3)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          congr 1
          push_cast
          ring
      _ ≤ (n : ℝ) ^ ((3 - δ) / 3) := Real.rpow_le_rpow (by positivity) h3 (by linarith)
  have hcalls : ((negTriBlocks n ^ 3 + (negTriBlocks n * 2 ^ L) ^ 2 : ℕ) : ℝ) ≤ 68 * (n : ℝ) ^ 2 :=
    by exact_mod_cast negTriBlocks_calls_le hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hexp : (n : ℝ) ^ (3 - δ / 3) = (n : ℝ) ^ 2 * (n : ℝ) ^ ((3 - δ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn']
    congr 1
    push_cast
    ring
  rw [nsmul_eq_mul, nsmul_eq_mul, hexp]
  have hk : (0 : ℝ) ≤ Nat.clog 2 (2 * W + 2) := Nat.cast_nonneg _
  calc (Nat.clog 2 (2 * W + 2) : ℝ) * (((negTriBlocks n ^ 3 + (negTriBlocks n * 2 ^ L) ^ 2 : ℕ) :
          ℝ) * F)
      ≤ (Nat.clog 2 (2 * W + 2) : ℝ) * ((68 * (n : ℝ) ^ 2) * (8 * c * (n : ℝ) ^ ((3 - δ) / 3))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hcalls hF hF0 (by positivity)) hk
    _ = 544 * c * Nat.clog 2 (2 * W + 2) * ((n : ℝ) ^ 2 * (n : ℝ) ^ ((3 - δ) / 3)) := by ring

end Reduction

end Cslib.Query
