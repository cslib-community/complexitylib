/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.List.Operations
public import Complexity.Probability.BitString.AffineHash
public import Complexity.Probability.KWiseIndependent
import Complexity.Probability.PMF.Map
import Complexity.Probability.Uniform

/-!
# Three-wise independence and prefix-collision conditioning of Boolean affine hashes

Over the two-element Boolean ring `Bool`, any two distinct nonzero vectors `u, v : BitString n`
are linearly independent over `GF(2)`: there is no non-unit scalar in `{0, 1}`, so `u ≠ 0`,
`v ≠ 0`, and `u ≠ v` suffice to solve `(a ⬝ᵥ u, a ⬝ᵥ v) = (d₂, d₃)` simultaneously for every pair
`(d₂, d₃)`. Consequently, the Boolean affine family `Cslib.BitString.LinearHash.affineHash`
(`x ↦ A x + b`) is **three-wise independent** (`IsKWiseIndependentHash 3`) for all dimensions
`k, n : ℕ`, with no finite-field extension arithmetic.

Postcomposing with the prefix restriction `prefixProj k r` preserves three-wise independence.
Furthermore, for distinct inputs `y ≠ y₀` (`δ = y + y₀ ≠ 0`), conditioning a uniform affine seed
`(A, b)` on the prefix collision `prefixProj k r (A y + b) = prefixProj k r (A y₀ + b)` is realized
explicitly by an idempotent additive homomorphism `adjustAffineSeed r (y + y₀)` that projects the
first `min r k` rows of `A` onto `{row | row ⬝ᵥ (y + y₀) = false}` along the first `true`
coordinate of `y + y₀`, scaling each supported seed's probability by `(2 : ℝ) ^ (min r k)`. This
supplies the constructible three-wise independent hash family used in `[HHRVW2020]`, Section 4.2,
Theorem 4.5 (pp. 21–25).

## Main definitions

* `Cslib.BitString.LinearHash.prefixProj`: additive homomorphism taking the first `min r k` bits.
* `Cslib.BitString.LinearHash.zeroPadPrefix`: zero-padded `k`-bit view of the first `r` bits.
* `Cslib.BitString.LinearHash.pivotMask`, `Cslib.BitString.LinearHash.adjustRow`,
  `Cslib.BitString.LinearHash.adjustAffineSeed`: additive projection onto the prefix-collision
  seed subgroup.
* `Cslib.BitString.LinearHash.packAffineSeed`, `Cslib.BitString.LinearHash.unpackAffineSeed`,
  `Cslib.BitString.LinearHash.wordAffineHash`,
  `Cslib.BitString.LinearHash.wordAdjustAffineSeed`: total word-level implementations.

## Main results

* `Cslib.BitString.LinearHash.isThreeWiseIndependentHash_affineHash`: `affineHash` is `3`-wise
  independent for all `k, n : ℕ`.
* `Cslib.BitString.LinearHash.isKWiseIndependentHash_dotProduct_cons_true`: the one-bit family
  `x ↦ t ⬝ (1, x)` is `3`-wise independent, a sample space of `2 ^ (d + 1)` points for `2 ^ d`
  inputs [AlonBabaiItai1986].
* `Cslib.BitString.LinearHash.isThreeWiseIndependentHash_prefixProj_affineHash`: truncated Boolean
  affine hashing is `3`-wise independent.
* `Cslib.BitString.LinearHash.toReal_map_adjustAffineSeed_eq`: mapping a uniform seed by
  `adjustAffineSeed r (y + y₀)` scales every prefix-colliding seed's mass by `2 ^ (min r k)`.
* `Cslib.BitString.LinearHash.wordAffineHash_eq_ofFn`,
  `Cslib.BitString.LinearHash.wordAdjustAffineSeed_eq_packAffineSeed`: exact agreement between the
  word implementations and the finite operations.

## References

* [N. Alon, L. Babai, A. Itai, *A fast and simple randomized parallel algorithm for the maximal
  independent set problem*][AlonBabaiItai1986]
* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Section 4.2, Theorem 4.5, pp. 21–25][HHRVW2020]
-/

public section

namespace Cslib.BitString.LinearHash

open Cslib.Probability Finset

/-! ### Simultaneous Boolean dot products and 3-wise independence -/

private theorem exists_true_coord {n : ℕ} {u : BitString n} (hu : u ≠ 0) :
    ∃ j : Fin n, u j = true := by
  by_contra! h
  exact hu (funext fun j => by
    cases hj : u j
    · rfl
    · exact False.elim (h j hj))

private theorem exists_dotProduct_single {n : ℕ} {u : BitString n} (hu : u ≠ 0) (d : Bool) :
    ∃ a : BitString n, a ⬝ᵥ u = d := by
  obtain ⟨j, hj⟩ := exists_true_coord hu
  refine ⟨Pi.single j d, ?_⟩
  rw [single_dotProduct, hj, Bool.mul_eq_and, Bool.and_true]

private theorem exists_dotProduct_pair {n : ℕ} {u v : BitString n}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (d₂ d₃ : Bool) :
    ∃ a : BitString n, a ⬝ᵥ u = d₂ ∧ a ⬝ᵥ v = d₃ := by
  obtain ⟨j₁, hj₁⟩ := exists_true_coord hu
  cases hv₁ : v j₁
  · obtain ⟨j₂, hj₂⟩ := exists_true_coord hv
    cases hu₂ : u j₂
    · refine ⟨Pi.single j₁ d₂ + Pi.single j₂ d₃, ?_, ?_⟩
      · rw [add_dotProduct, single_dotProduct, single_dotProduct, hj₁, hu₂]
        cases d₂ <;> cases d₃ <;> rfl
      · rw [add_dotProduct, single_dotProduct, single_dotProduct, hv₁, hj₂]
        cases d₂ <;> cases d₃ <;> rfl
    · refine ⟨Pi.single j₁ (d₂ + d₃) + Pi.single j₂ d₃, ?_, ?_⟩
      · rw [add_dotProduct, single_dotProduct, single_dotProduct, hj₁, hu₂]
        cases d₂ <;> cases d₃ <;> rfl
      · rw [add_dotProduct, single_dotProduct, single_dotProduct, hv₁, hj₂]
        cases d₂ <;> cases d₃ <;> rfl
  · have hdiff : u + v ≠ 0 := by
      intro h0
      apply huv
      funext j
      have hj := congrFun h0 j
      change u j + v j = false at hj
      cases hx : u j <;> cases hy : v j <;> simp_all [Bool.add_eq_xor]
    obtain ⟨j₂, hj₂⟩ := exists_true_coord hdiff
    change u j₂ + v j₂ = true at hj₂
    cases hu₂ : u j₂ <;> cases hv₂ : v j₂
    · rw [hu₂, hv₂] at hj₂
      cases hj₂
    · refine ⟨Pi.single j₁ d₂ + Pi.single j₂ (d₂ + d₃), ?_, ?_⟩
      · rw [add_dotProduct, single_dotProduct, single_dotProduct, hj₁, hu₂]
        cases d₂ <;> cases d₃ <;> rfl
      · rw [add_dotProduct, single_dotProduct, single_dotProduct, hv₁, hv₂]
        cases d₂ <;> cases d₃ <;> rfl
    · refine ⟨Pi.single j₁ d₃ + Pi.single j₂ (d₂ + d₃), ?_, ?_⟩
      · rw [add_dotProduct, single_dotProduct, single_dotProduct, hj₁, hu₂]
        cases d₂ <;> cases d₃ <;> rfl
      · rw [add_dotProduct, single_dotProduct, single_dotProduct, hv₁, hv₂]
        cases d₂ <;> cases d₃ <;> rfl
    · rw [hu₂, hv₂] at hj₂
      cases hj₂

/-- **Boolean affine hashing is three-wise independent** for all output and input widths `k, n`. -/
theorem isThreeWiseIndependentHash_affineHash (k n : ℕ) :
    IsKWiseIndependentHash 3 (affineHash (k := k) (n := n)) := by
  let g : ((Fin k → BitString n) × BitString k) →+ (BitString n → BitString k) :=
    { toFun := affineHash
      map_zero' := by
        funext x i
        simp [affineHash, hash]
      map_add' := fun s₁ s₂ => by
        funext x i
        change (s₁.1 i + s₂.1 i) ⬝ᵥ x + (s₁.2 i + s₂.2 i) =
          (s₁.1 i ⬝ᵥ x + s₁.2 i) + (s₂.1 i ⬝ᵥ x + s₂.2 i)
        rw [add_dotProduct]
        abel }
  refine isKWiseIndependentHash_of_surjective g fun T hT c => ?_
  interval_cases hc : #T
  · have hT0 := card_eq_zero.mp hc
    exact ⟨0, funext fun ⟨x, hx⟩ => by rw [hT0] at hx; exact (notMem_empty _ hx).elim⟩
  · obtain ⟨x₁, hT₁⟩ := card_eq_one.mp hc
    have hx₁ : x₁ ∈ T := by rw [hT₁]; exact mem_singleton_self x₁
    refine ⟨(0, c ⟨x₁, hx₁⟩), funext fun ⟨x, hx⟩ => ?_⟩
    have hxeq : x = x₁ := by rw [hT₁] at hx; exact mem_singleton.mp hx
    subst hxeq
    funext i
    change (0 : BitString n) ⬝ᵥ x + c ⟨x, hx₁⟩ i = c ⟨x, hx⟩ i
    simp
  · obtain ⟨x₁, x₂, hx₁₂, hT₂⟩ := card_eq_two.mp hc
    have hx₁ : x₁ ∈ T := by rw [hT₂]; simp
    have hx₂ : x₂ ∈ T := by rw [hT₂]; simp
    have hu : x₁ + x₂ ≠ 0 := by
      intro h0
      apply hx₁₂
      funext j
      have hj := congrFun h0 j
      change x₁ j + x₂ j = false at hj
      cases hx : x₁ j <;> cases hy : x₂ j <;> simp_all [Bool.add_eq_xor]
    let c₁ := c ⟨x₁, hx₁⟩
    let c₂ := c ⟨x₂, hx₂⟩
    choose rows hrows using fun i : Fin k => exists_dotProduct_single hu (c₁ i + c₂ i)
    refine ⟨(rows, fun i => rows i ⬝ᵥ x₁ + c₁ i), funext fun ⟨x, hx⟩ => ?_⟩
    have hx' : x = x₁ ∨ x = x₂ := by
      rw [hT₂] at hx
      simpa using hx
    rcases hx' with rfl | rfl
    · funext i
      change rows i ⬝ᵥ x + (rows i ⬝ᵥ x + c₁ i) = c₁ i
      cases rows i ⬝ᵥ x <;> cases c₁ i <;> rfl
    · funext i
      have hi := hrows i
      rw [dotProduct_add] at hi
      change rows i ⬝ᵥ x + (rows i ⬝ᵥ x₁ + c₁ i) = c₂ i
      cases h1 : rows i ⬝ᵥ x₁ <;> cases h2 : rows i ⬝ᵥ x <;>
        cases hc1 : c₁ i <;> cases hc2 : c₂ i <;> simp_all [Bool.add_eq_xor]
  · obtain ⟨x₁, x₂, x₃, hx₁₂, hx₁₃, hx₂₃, hT₃⟩ := card_eq_three.mp hc
    have hx₁ : x₁ ∈ T := by rw [hT₃]; simp
    have hx₂ : x₂ ∈ T := by rw [hT₃]; simp
    have hx₃ : x₃ ∈ T := by rw [hT₃]; simp
    have hu : x₁ + x₂ ≠ 0 := by
      intro h0
      apply hx₁₂
      funext j
      have hj := congrFun h0 j
      change x₁ j + x₂ j = false at hj
      cases hx : x₁ j <;> cases hy : x₂ j <;> simp_all [Bool.add_eq_xor]
    have hv : x₁ + x₃ ≠ 0 := by
      intro h0
      apply hx₁₃
      funext j
      have hj := congrFun h0 j
      change x₁ j + x₃ j = false at hj
      cases hx : x₁ j <;> cases hy : x₃ j <;> simp_all [Bool.add_eq_xor]
    have huv : x₁ + x₂ ≠ x₁ + x₃ := fun h => hx₂₃ (add_left_cancel h)
    let c₁ := c ⟨x₁, hx₁⟩
    let c₂ := c ⟨x₂, hx₂⟩
    let c₃ := c ⟨x₃, hx₃⟩
    choose rows hrows using fun i : Fin k =>
      exists_dotProduct_pair hu hv huv (c₁ i + c₂ i) (c₁ i + c₃ i)
    refine ⟨(rows, fun i => rows i ⬝ᵥ x₁ + c₁ i), funext fun ⟨x, hx⟩ => ?_⟩
    have hx' : x = x₁ ∨ x = x₂ ∨ x = x₃ := by
      rw [hT₃] at hx
      simpa using hx
    rcases hx' with rfl | rfl | rfl
    · funext i
      change rows i ⬝ᵥ x + (rows i ⬝ᵥ x + c₁ i) = c₁ i
      cases rows i ⬝ᵥ x <;> cases c₁ i <;> rfl
    · funext i
      have hi := (hrows i).1
      rw [dotProduct_add] at hi
      change rows i ⬝ᵥ x + (rows i ⬝ᵥ x₁ + c₁ i) = c₂ i
      cases h1 : rows i ⬝ᵥ x₁ <;> cases h2 : rows i ⬝ᵥ x <;>
        cases hc1 : c₁ i <;> cases hc2 : c₂ i <;> simp_all [Bool.add_eq_xor]
    · funext i
      have hi := (hrows i).2
      rw [dotProduct_add] at hi
      change rows i ⬝ᵥ x + (rows i ⬝ᵥ x₁ + c₁ i) = c₃ i
      cases h1 : rows i ⬝ᵥ x₁ <;> cases h3 : rows i ⬝ᵥ x <;>
        cases hc1 : c₁ i <;> cases hc3 : c₃ i <;> simp_all [Bool.add_eq_xor]

/-- **One-bit affine hashing as a single dot product** is three-wise independent:
`x ↦ t ⬝ (1, x)` for a uniformly random `t ∈ {0,1}^(d+1)`. It is the one-row family `affineHash`
with seed `(Fin.tail t, t 0)`. Labelling `n` points by `d = ⌈log₂ n⌉` binary digits gives a
three-wise independent sample space of `2 ^ (d + 1) < 4 n` points [AlonBabaiItai1986]. -/
theorem isKWiseIndependentHash_dotProduct_cons_true (d : ℕ) :
    IsKWiseIndependentHash 3
      (fun (t : BitString (d + 1)) (x : BitString d) => t ⬝ᵥ Fin.cons true x) := by
  let e : BitString (d + 1) ≃ (Fin 1 → BitString d) × BitString 1 :=
    { toFun := fun t => (fun _ => Fin.tail t, fun _ => t 0)
      invFun := fun s => Fin.cons (s.2 0) (s.1 0)
      left_inv := fun t => Fin.cons_self_tail t
      right_inv := fun s => by
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
        · rw [Subsingleton.elim i 0]
          exact Fin.tail_cons (α := fun _ => Bool) (s.2 0) (s.1 0)
        · rw [Subsingleton.elim i 0]
          exact Fin.cons_zero (α := fun _ => Bool) (s.2 0) (s.1 0) }
  have heq : (fun (t : BitString (d + 1)) (x : BitString d) => t ⬝ᵥ Fin.cons true x) =
      fun t x => Equiv.funUnique (Fin 1) Bool (affineHash (e t) x) := by
    funext t x
    change t ⬝ᵥ Matrix.vecCons true x = Fin.tail t ⬝ᵥ x + t 0
    rw [Matrix.dotProduct_cons, add_comm (Matrix.vecHead t * true)]
    change Fin.tail t ⬝ᵥ x + (t 0 && true) = Fin.tail t ⬝ᵥ x + t 0
    rw [Bool.and_true]
  rw [heq]
  exact ((isThreeWiseIndependentHash_affineHash 1 d).comp_seedEquiv e).map_equiv
    (Equiv.funUnique (Fin 1) Bool)

/-! ### Prefix restriction and fixed-width zero padding -/

/-- Additive homomorphism projecting a `k`-bit string onto its first `min r k` coordinates. -/
@[expose] def prefixProj (k r : ℕ) : BitString k →+ BitString (min r k) where
  toFun v := v ∘ Fin.castLE (Nat.min_le_right r k)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restricting to the first `min r k` coordinates is surjective. -/
theorem prefixProj_surjective (k r : ℕ) : Function.Surjective (prefixProj k r) :=
  (Fin.castLE_injective (Nat.min_le_right r k)).surjective_comp_right

/-- Truncating `affineHash` to its first `min r k` output bits preserves `3`-wise independence. -/
theorem isThreeWiseIndependentHash_prefixProj_affineHash (k n r : ℕ) :
    IsKWiseIndependentHash 3 (fun s x => prefixProj k r (affineHash (k := k) (n := n) s x)) :=
  (isThreeWiseIndependentHash_affineHash k n).comp_surjective_addMonoidHom (prefixProj k r)
    (prefixProj_surjective k r)

/-- Zero-pad a `k`-bit string after its first `r` coordinates, retaining fixed output width `k`. -/
@[expose] def zeroPadPrefix (k r : ℕ) (v : BitString k) : BitString k :=
  fun i => if i.val < r then v i else false

/-- Two `k`-bit strings have equal zero-padded `r`-prefixes iff their `min r k`-bit prefixes
agree. -/
theorem zeroPadPrefix_eq_iff_prefixProj_eq {k r : ℕ} (u v : BitString k) :
    zeroPadPrefix k r u = zeroPadPrefix k r v ↔ prefixProj k r u = prefixProj k r v := by
  constructor
  · intro h
    funext i
    have hi : i.val < r := lt_of_lt_of_le i.isLt (Nat.min_le_left r k)
    have hcoord := congrFun h (Fin.castLE (Nat.min_le_right r k) i)
    simp only [zeroPadPrefix, Fin.val_castLE, hi, ↓reduceIte] at hcoord
    exact hcoord
  · intro h
    funext i
    by_cases hi : i.val < r
    · have hmin : i.val < min r k := Nat.lt_min.mpr ⟨hi, i.isLt⟩
      have hcoord := congrFun h ⟨i.val, hmin⟩
      simpa only [zeroPadPrefix, hi, ↓reduceIte, prefixProj, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Function.comp_apply, Fin.castLE_mk] using hcoord
    · simp [zeroPadPrefix, hi]

/-- On words, `zeroPadPrefix` takes `min r k` bits and pads the remaining `k - min r k` bits with
`false`. -/
theorem ofFn_zeroPadPrefix (k r : ℕ) (v : BitString k) :
    List.ofFn (zeroPadPrefix k r v) =
      (List.ofFn v).take (min r k) ++ List.replicate (k - min r k) false := by
  have hle : min r k ≤ k := Nat.min_le_right r k
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  simp only [List.length_ofFn] at hi₁
  simp only [List.getElem_ofFn, zeroPadPrefix, List.getElem_append, List.length_take,
    List.length_ofFn, Nat.min_eq_left hle]
  by_cases hir : i < min r k
  · have hir' : i < r := lt_of_lt_of_le hir (Nat.min_le_left r k)
    simp [hir, hir']
  · have hir' : ¬ i < r := fun h => hir (Nat.lt_min.mpr ⟨h, hi₁⟩)
    simp [hir, hir']

/-! ### Additive projection onto prefix-colliding affine seeds -/

/-- Basis mask at the first `true` coordinate of `δ`, or `0` when `δ = 0`. -/
@[expose] def pivotMask {n : ℕ} (δ : BitString n) : BitString n :=
  ofList n (listSingle n ((List.ofFn δ).idxOf true))

/-- The word representation of `pivotMask δ` is `listSingle n ((List.ofFn δ).idxOf true)`. -/
theorem ofFn_pivotMask {n : ℕ} (δ : BitString n) :
    List.ofFn (pivotMask δ) = listSingle n ((List.ofFn δ).idxOf true) :=
  ofFn_ofList (by simp [listSingle])

private theorem pivotMask_eq_single_of_ne_zero {n : ℕ} {δ : BitString n} (hδ : δ ≠ 0) :
    ∃ p : Fin n, δ p = true ∧ pivotMask δ = Pi.single p true := by
  obtain ⟨j, hj⟩ := exists_true_coord hδ
  have hmem : true ∈ List.ofFn δ := List.mem_ofFn.mpr ⟨j, hj⟩
  have hp_lt : (List.ofFn δ).idxOf true < n := by
    simpa only [List.length_ofFn] using List.idxOf_lt_length_of_mem hmem
  let p : Fin n := ⟨(List.ofFn δ).idxOf true, hp_lt⟩
  have hδp : δ p = true := by
    have hget := List.getElem_idxOf (xs := List.ofFn δ) (x := true) (by simpa using hp_lt)
    simpa only [List.getElem_ofFn] using hget
  refine ⟨p, hδp, ?_⟩
  rw [pivotMask, listSingle_eq_ofFn_single p, ofList_ofFn]

private theorem pivotMask_dotProduct_of_ne_zero {n : ℕ} {δ : BitString n} (hδ : δ ≠ 0) :
    pivotMask δ ⬝ᵥ δ = true := by
  obtain ⟨p, hδp, hmask⟩ := pivotMask_eq_single_of_ne_zero hδ
  rw [hmask, single_dotProduct, hδp, Bool.mul_eq_and, Bool.and_true]

private theorem pivotMask_ne_zero {n : ℕ} {δ : BitString n} (hδ : δ ≠ 0) :
    pivotMask δ ≠ 0 := by
  intro h0
  have h := pivotMask_dotProduct_of_ne_zero hδ
  rw [h0, zero_dotProduct] at h
  exact Bool.false_ne_true h

/-- Additive homomorphism projecting a row `row : BitString n` onto `{row | row ⬝ᵥ δ = false}`
when `δ ≠ 0`. -/
@[expose] def adjustRow {n : ℕ} (δ : BitString n) : BitString n →+ BitString n where
  toFun row := row + if row ⬝ᵥ δ then pivotMask δ else 0
  map_zero' := by simp
  map_add' r₁ r₂ := by
    rw [add_dotProduct]
    funext j
    simp only [Pi.add_apply, apply_ite (fun f : BitString n => f j), Pi.zero_apply]
    change (r₁ j + r₂ j) + (if (r₁ ⬝ᵥ δ) + (r₂ ⬝ᵥ δ) then pivotMask δ j else false) =
      (r₁ j + if r₁ ⬝ᵥ δ then pivotMask δ j else false) +
        (r₂ j + if r₂ ⬝ᵥ δ then pivotMask δ j else false)
    cases r₁ j <;> cases r₂ j <;> cases r₁ ⬝ᵥ δ <;> cases r₂ ⬝ᵥ δ <;>
      cases pivotMask δ j <;> rfl

private theorem adjustRow_dotProduct_eq_false {n : ℕ} {δ : BitString n} (hδ : δ ≠ 0)
    (row : BitString n) : adjustRow δ row ⬝ᵥ δ = false := by
  simp only [adjustRow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_dotProduct]
  cases h : row ⬝ᵥ δ
  · simp
  · simp [pivotMask_dotProduct_of_ne_zero hδ, Bool.add_eq_xor]

private theorem adjustRow_eq_self_of_dotProduct_eq_false {n : ℕ} (δ row : BitString n)
    (hrow : row ⬝ᵥ δ = false) : adjustRow δ row = row := by
  simp [adjustRow, hrow]

private theorem card_ker_adjustRow {n : ℕ} {δ : BitString n} (hδ : δ ≠ 0) :
    #{row : BitString n | adjustRow δ row = 0} = 2 := by
  have hset : ({row : BitString n | adjustRow δ row = 0} : Finset (BitString n)) =
      {0, pivotMask δ} := by
    ext row
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro h
      simp only [adjustRow, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
      cases hd : row ⬝ᵥ δ
      · left
        simpa [hd] using h
      · right
        simp only [hd, ↓reduceIte] at h
        funext j
        have hj := congrFun h j
        change row j + pivotMask δ j = false at hj
        cases hr : row j <;> cases hm : pivotMask δ j <;> simp_all [Bool.add_eq_xor]
    · rintro (rfl | rfl)
      · exact (adjustRow δ).map_zero
      · simp only [adjustRow, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          pivotMask_dotProduct_of_ne_zero hδ, ↓reduceIte]
        funext j
        change pivotMask δ j + pivotMask δ j = false
        cases pivotMask δ j <;> rfl
  rw [hset, card_pair (pivotMask_ne_zero hδ).symm]

/-- Additive homomorphism projecting an affine hash seed `(A, b)` onto the subgroup of seeds whose
first `min r k` rows are orthogonal to `δ`. For `δ = y + y₀` (`y ≠ y₀`), this is exactly the set of
seeds where `prefixProj k r (affineHash s y) = prefixProj k r (affineHash s y₀)`. -/
@[expose] def adjustAffineSeed {k n : ℕ} (r : ℕ) (δ : BitString n) :
    ((Fin k → BitString n) × BitString k) →+ ((Fin k → BitString n) × BitString k) where
  toFun s := (fun i => if i.val < r then adjustRow δ (s.1 i) else s.1 i, s.2)
  map_zero' := by
    ext i j
    · simp only [Prod.fst_zero, Pi.zero_apply]
      split_ifs
      · simp
      · rfl
    · rfl
  map_add' s₁ s₂ := by
    ext i j
    · simp only [Prod.fst_add, Pi.add_apply]
      split_ifs
      · simp [map_add]
      · rfl
    · rfl

private theorem prefixProj_affineHash_eq_iff {k n : ℕ} (r : ℕ)
    (s : (Fin k → BitString n) × BitString k) (y y₀ : BitString n) :
    prefixProj k r (affineHash s y) = prefixProj k r (affineHash s y₀) ↔
      ∀ i : Fin k, i.val < r → s.1 i ⬝ᵥ (y + y₀) = false := by
  constructor
  · intro h i hir
    have hmin : i.val < min r k := Nat.lt_min.mpr ⟨hir, i.isLt⟩
    have hcoord := congrFun h ⟨i.val, hmin⟩
    simp only [prefixProj, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
      Fin.castLE_mk, affineHash, Pi.add_apply, hash] at hcoord
    rw [dotProduct_add]
    change (s.1 i ⬝ᵥ y) + (s.1 i ⬝ᵥ y₀) = false
    cases hy : s.1 i ⬝ᵥ y <;> cases hy₀ : s.1 i ⬝ᵥ y₀ <;> simp_all [Bool.add_eq_xor]
  · intro h
    funext ⟨i, hi⟩
    have hir : i < r := lt_of_lt_of_le hi (Nat.min_le_left r k)
    have hdot := h ⟨i, lt_of_lt_of_le hi (Nat.min_le_right r k)⟩ hir
    rw [dotProduct_add] at hdot
    simp only [prefixProj, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
      Fin.castLE_mk, affineHash, Pi.add_apply, hash]
    change (s.1 ⟨i, _⟩ ⬝ᵥ y) + s.2 ⟨i, _⟩ = (s.1 ⟨i, _⟩ ⬝ᵥ y₀) + s.2 ⟨i, _⟩
    change (s.1 ⟨i, _⟩ ⬝ᵥ y) + (s.1 ⟨i, _⟩ ⬝ᵥ y₀) = false at hdot
    cases hy : s.1 ⟨i, _⟩ ⬝ᵥ y <;> cases hy₀ : s.1 ⟨i, _⟩ ⬝ᵥ y₀ <;>
      cases hb : s.2 ⟨i, _⟩ <;> simp_all [Bool.add_eq_xor]

/-- For distinct `y ≠ y₀`, every seed output by `adjustAffineSeed r (y + y₀)` collides on the first
`min r k` bits of `y` and `y₀`. -/
theorem prefixProj_affineHash_adjustAffineSeed {k n : ℕ} (r : ℕ)
    {y y₀ : BitString n} (hy : y ≠ y₀) (s : (Fin k → BitString n) × BitString k) :
    prefixProj k r (affineHash (adjustAffineSeed r (y + y₀) s) y) =
      prefixProj k r (affineHash (adjustAffineSeed r (y + y₀) s) y₀) := by
  have hδ : y + y₀ ≠ 0 := by
    intro h0
    apply hy
    funext j
    have hj := congrFun h0 j
    change y j + y₀ j = false at hj
    cases h1 : y j <;> cases h2 : y₀ j <;> simp_all [Bool.add_eq_xor]
  rw [prefixProj_affineHash_eq_iff]
  intro i hir
  simp only [adjustAffineSeed, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hir, ↓reduceIte]
  exact adjustRow_dotProduct_eq_false hδ (s.1 i)

private theorem adjustAffineSeed_eq_self_of_prefixProj_eq {k n : ℕ} (r : ℕ)
    {y y₀ : BitString n} {s : (Fin k → BitString n) × BitString k}
    (hs : prefixProj k r (affineHash s y) = prefixProj k r (affineHash s y₀)) :
    adjustAffineSeed r (y + y₀) s = s := by
  have hdot := (prefixProj_affineHash_eq_iff r s y y₀).mp hs
  ext i j
  · simp only [adjustAffineSeed, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    split_ifs with hir
    · rw [adjustRow_eq_self_of_dotProduct_eq_false _ _ (hdot i hir)]
    · rfl
  · rfl

private theorem card_fiber_adjustAffineSeed {k n : ℕ} (r : ℕ)
    {y y₀ : BitString n} (hy : y ≠ y₀)
    {s₀ : (Fin k → BitString n) × BitString k}
    (hs₀ : prefixProj k r (affineHash s₀ y) = prefixProj k r (affineHash s₀ y₀)) :
    #{s : (Fin k → BitString n) × BitString k | adjustAffineSeed r (y + y₀) s = s₀} =
      2 ^ min r k := by
  let δ := y + y₀
  have hδ : δ ≠ 0 := by
    intro h0
    apply hy
    funext j
    have hj := congrFun h0 j
    change y j + y₀ j = false at hj
    cases h1 : y j <;> cases h2 : y₀ j <;> simp_all [Bool.add_eq_xor]
  have hs₀_fix : adjustAffineSeed r δ s₀ = s₀ :=
    adjustAffineSeed_eq_self_of_prefixProj_eq r hs₀
  have hshift :
      #{s : (Fin k → BitString n) × BitString k | adjustAffineSeed r δ s = s₀} =
        #{s : (Fin k → BitString n) × BitString k | adjustAffineSeed r δ s = 0} := by
    refine card_equiv (Equiv.addRight (-s₀)) fun s => ?_
    simp only [mem_filter, mem_univ, true_and, Equiv.coe_addRight, map_add, map_neg, hs₀_fix]
    exact ⟨fun h => by rw [h, add_neg_cancel], fun h => eq_of_sub_eq_zero h⟩
  rw [hshift]
  let kerRow (i : Fin k) : Finset (BitString n) :=
    if i.val < r then univ.filter (fun row => adjustRow δ row = 0) else {0}
  have hker : ({s : (Fin k → BitString n) × BitString k | adjustAffineSeed r δ s = 0} :
      Finset _) = (Fintype.piFinset kerRow).product ({0} : Finset (BitString k)) := by
    ext ⟨rows, b⟩
    simp only [mem_filter, mem_univ, true_and, product_eq_sprod, mem_product,
      Fintype.mem_piFinset, mem_singleton, Prod.ext_iff, adjustAffineSeed,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.fst_zero, Prod.snd_zero, kerRow]
    rw [funext_iff]
    refine and_congr_left' (forall_congr' fun i => ?_)
    simp only [Pi.zero_apply]
    split_ifs with hir
    · simp only [mem_filter, mem_univ, true_and]
    · simp only [mem_singleton]
  rw [hker, product_eq_sprod, card_product, card_singleton, mul_one, Fintype.card_piFinset]
  have hcard (i : Fin k) : #(kerRow i) = if i.val < r then 2 else 1 := by
    dsimp only [kerRow]
    split_ifs
    · exact card_ker_adjustRow hδ
    · exact card_singleton 0
  simp only [hcard, prod_ite, prod_const_one, mul_one, prod_const]
  congr 1
  rw [Fin.card_filter_val_lt, Nat.min_comm]

/-- **Exact conditional-seed scaling**: for distinct `y ≠ y₀`, mapping a uniformly random affine
seed by `adjustAffineSeed r (y + y₀)` assigns to every prefix-colliding seed `s₀` mass exactly
`(2 : ℝ) ^ (min r k)` times its uniform mass. -/
theorem toReal_map_adjustAffineSeed_eq {k n : ℕ} (r : ℕ)
    {y y₀ : BitString n} (hy : y ≠ y₀)
    {s₀ : (Fin k → BitString n) × BitString k}
    (hs₀ : prefixProj k r (affineHash s₀ y) = prefixProj k r (affineHash s₀ y₀)) :
    (((PMF.uniformOfFintype ((Fin k → BitString n) × BitString k)).map
      (adjustAffineSeed r (y + y₀))) s₀).toReal =
      (2 : ℝ) ^ (min r k) *
        ((PMF.uniformOfFintype ((Fin k → BitString n) × BitString k)) s₀).toReal := by
  rw [PMF.toReal_uniformOfFintype_map_apply, Finset.dens_eq_card_div_card,
    card_fiber_adjustAffineSeed r hy hs₀]
  simp [PMF.uniformOfFintype_apply, div_eq_mul_inv]

/-! ### Word-level implementations and exact agreement -/

/-- Pack an affine seed `(A, b) : (Fin k → BitString n) × BitString k` as a `(k * n + k)`-bit
word. -/
@[expose] def packAffineSeed {k n : ℕ} (s : (Fin k → BitString n) × BitString k) : List Bool :=
  List.ofFn (blocksEquiv.symm s.1) ++ List.ofFn s.2

/-- Unpack a word into an affine seed `(A, b) : (Fin k → BitString n) × BitString k`, padding
missing bits with `false` and ignoring extra trailing bits. -/
@[expose] def unpackAffineSeed (k n : ℕ) (seed : List Bool) :
    (Fin k → BitString n) × BitString k :=
  (block (ofList (k * n) (seed.take (k * n))), ofList k (seed.drop (k * n)))

@[simp] theorem length_packAffineSeed {k n : ℕ} (s : (Fin k → BitString n) × BitString k) :
    (packAffineSeed s).length = k * n + k := by
  simp [packAffineSeed]

@[simp] theorem unpackAffineSeed_packAffineSeed {k n : ℕ}
    (s : (Fin k → BitString n) × BitString k) :
    unpackAffineSeed k n (packAffineSeed s) = s := by
  ext i j
  · simp only [unpackAffineSeed, packAffineSeed,
      List.take_left' (List.length_ofFn (f := blocksEquiv.symm s.1)), ofList_ofFn]
    exact congrFun (congrFun (blocksEquiv.apply_symm_apply s.1) i) j
  · simp [unpackAffineSeed, packAffineSeed,
      List.drop_left' (List.length_ofFn (f := blocksEquiv.symm s.1))]

theorem packAffineSeed_unpackAffineSeed {k n : ℕ} {seed : List Bool}
    (hseed : seed.length = k * n + k) :
    packAffineSeed (unpackAffineSeed k n seed) = seed := by
  have htake : (seed.take (k * n)).length = k * n := by simp [hseed]
  have hdrop : (seed.drop (k * n)).length = k := by simp [hseed]
  have hblock : blocksEquiv.symm (block (ofList (k * n) (seed.take (k * n)))) =
      ofList (k * n) (seed.take (k * n)) := by
    rw [← blocksEquiv_apply]
    exact blocksEquiv.symm_apply_apply _
  rw [packAffineSeed, unpackAffineSeed, hblock, ofFn_ofList htake, ofFn_ofList hdrop,
    List.take_append_drop]

/-- Word-level Boolean affine hash `x ↦ A x + b`, reading `k * input.length` matrix bits followed
by `k` shift bits. -/
@[expose] def wordAffineHash (k : ℕ) (seed input : List Bool) : List Bool :=
  listXor k [wordHash k (seed.take (k * input.length)) input, seed.drop (k * input.length)]

@[simp] theorem length_wordAffineHash (k : ℕ) (seed input : List Bool) :
    (wordAffineHash k seed input).length = k := by
  simp [wordAffineHash]

/-- On a fixed-width input, `wordAffineHash` computes `affineHash` on the unpacked seed. -/
theorem wordAffineHash_eq_ofFn {k n : ℕ} (seed : List Bool) (x : BitString n) :
    wordAffineHash k seed (List.ofFn x) =
      List.ofFn (affineHash (unpackAffineSeed k n seed) x) := by
  simp only [wordAffineHash, List.length_ofFn, wordHash_eq_ofFn, listXor_pair, ofList_ofFn,
    affineHash, unpackAffineSeed]

/-- Word-level implementation of `adjustAffineSeed`: adjust each of the first `min r k` rows of the
`k × n` matrix prefix of `seed` to be orthogonal to `y + y₀`, preserving the remaining rows and the
`k`-bit offset. -/
@[expose] def wordAdjustAffineSeed (k n r : ℕ) (y y₀ seed : List Bool) : List Bool :=
  let diff := listXor n [y, y₀]
  let mask := listSingle n (diff.idxOf true)
  let matBits := seed.take (k * n)
  let adjRows := (List.range k).map fun i =>
    let row := listRow n i matBits
    let dot := (row.zipWith Bool.and diff).foldl Bool.xor false
    if decide (i < r) && dot then listXor n [row, mask] else row
  adjRows.flatten ++ listRow k 0 (seed.drop (k * n))

@[simp] theorem length_wordAdjustAffineSeed (k n r : ℕ) (y y₀ seed : List Bool) :
    (wordAdjustAffineSeed k n r y y₀ seed).length = k * n + k := by
  have hrow : ∀ w ∈ ((List.range k).map fun i =>
      let diff := listXor n [y, y₀]
      let mask := listSingle n (diff.idxOf true)
      let row := listRow n i (seed.take (k * n))
      let dot := (row.zipWith Bool.and diff).foldl Bool.xor false
      if decide (i < r) && dot then listXor n [row, mask] else row), w.length = n := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
    dsimp only
    split_ifs <;> simp
  simp only [wordAdjustAffineSeed, List.length_append, length_listRow,
    List.length_flatten, List.map_map]
  have hsum : (((List.range k).map fun i =>
      (let diff := listXor n [y, y₀]
       let mask := listSingle n (diff.idxOf true)
       let row := listRow n i (seed.take (k * n))
       let dot := (row.zipWith Bool.and diff).foldl Bool.xor false
       if decide (i < r) && dot then listXor n [row, mask] else row).length)).sum = k * n := by
    have hconst : ((List.range k).map fun i =>
        (let diff := listXor n [y, y₀]
         let mask := listSingle n (diff.idxOf true)
         let row := listRow n i (seed.take (k * n))
         let dot := (row.zipWith Bool.and diff).foldl Bool.xor false
         if decide (i < r) && dot then listXor n [row, mask] else row).length) =
        List.replicate k n := by
      apply List.ext_getElem (by simp)
      intro i hi₁ hi₂
      simp only [List.length_map, List.length_range] at hi₁
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      exact hrow _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi₁, rfl⟩)
    rw [hconst, List.sum_replicate, smul_eq_mul]
  simpa only [Function.comp_def] using congrArg (· + k) hsum

/-- On fixed-width words, `wordAdjustAffineSeed` agrees with `adjustAffineSeed` under
`packAffineSeed` and `unpackAffineSeed`. -/
theorem wordAdjustAffineSeed_eq_packAffineSeed (k n r : ℕ) (y y₀ seed : List Bool) :
    wordAdjustAffineSeed k n r y y₀ seed =
      packAffineSeed (adjustAffineSeed r (ofList n y + ofList n y₀)
        (unpackAffineSeed k n seed)) := by
  let δ := ofList n y + ofList n y₀
  let s := unpackAffineSeed k n seed
  have hdiff : listXor n [y, y₀] = List.ofFn δ := listXor_pair n y y₀
  have hmask : listSingle n ((listXor n [y, y₀]).idxOf true) = List.ofFn (pivotMask δ) := by
    rw [hdiff, ofFn_pivotMask]
  have hadjRows : ((List.range k).map fun i =>
      let diff := listXor n [y, y₀]
      let mask := listSingle n (diff.idxOf true)
      let row := listRow n i (seed.take (k * n))
      let dot := (row.zipWith Bool.and diff).foldl Bool.xor false
      if decide (i < r) && dot then listXor n [row, mask] else row) =
      List.ofFn (fun i : Fin k =>
        List.ofFn (if i.val < r then adjustRow δ (s.1 i) else s.1 i)) := by
    apply List.ext_getElem (by simp)
    intro i hi₁ hi₂
    simp only [List.length_map, List.length_range] at hi₁
    let idx : Fin k := ⟨i, hi₁⟩
    have hrow : listRow n idx.val (seed.take (k * n)) = List.ofFn (s.1 idx) :=
      listRow_eq_ofFn n idx (seed.take (k * n))
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    change (let diff := listXor n [y, y₀]
      let mask := listSingle n (diff.idxOf true)
      let row := listRow n idx.val (seed.take (k * n))
      let dot := (row.zipWith Bool.and diff).foldl Bool.xor false
      if decide (idx.val < r) && dot then listXor n [row, mask] else row) =
      List.ofFn (if idx.val < r then adjustRow δ (s.1 idx) else s.1 idx)
    dsimp only
    rw [hrow, hmask, hdiff, ← dotProduct_eq_foldl]
    by_cases hir : idx.val < r
    · simp only [hir, decide_true, Bool.true_and, ↓reduceIte, adjustRow,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      cases hd : s.1 idx ⬝ᵥ δ
      · simp
      · simp [listXor_pair]
    · simp [hir]
  simp only [wordAdjustAffineSeed, packAffineSeed, adjustAffineSeed, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]
  rw [hadjRows, ← ofFn_blocksEquiv_symm, listRow_zero]
  rfl

end Cslib.BitString.LinearHash
