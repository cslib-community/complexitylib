/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Log

/-!
# Linear hashing on base-`p` digits

For a prime `p`, a number `x < q` has `D = ⌊log_p q⌋ + 1` digits `xᵢ` in base `p`. A seed
`a ∈ (ZMod p) ^ D` gives the map `x ↦ ∑ᵢ aᵢ xᵢ` with values below `p`. Two distinct numbers
below `q` differ in some digit, so they collide for exactly a `1 / p` fraction of the seeds.
By a union bound over the ordered pairs of distinct elements of a set `S` of numbers below `q`,
fewer than `p` such pairs leave a seed whose map is injective on `S`.

This reduces a universe of size `q` to one of size `p` with at most `p * q` maps, and is the
first step of the perfect hash family of
`CslibFrontier.Foundations.Combinatorics.PerfectHashFamily.Basic`.

## Main definitions

* `Cslib.linearHash`: the family of the maps `x ↦ ∑ᵢ aᵢ xᵢ`, as maps `ℕ → ℕ`.

## Main results

* `Cslib.linearHash_lt`: the maps take values below `p`.
* `Cslib.card_linearHash_le`: there are at most `p * q` of them.
* `Cslib.exists_injOn_linearHash`: some map is injective on a given set of numbers below `q`
  with fewer than `p` ordered pairs of distinct elements.
-/

public section

namespace Cslib

open Finset

variable (p q : ℕ) [Fact p.Prime]

/-- The base-`p` digits of `x` at the positions below `⌊log_p q⌋ + 1`, as residues. -/
private def digitVec (x : ℕ) : Fin (Nat.log p q + 1) → ZMod p := fun i => (x / p ^ i.val : ℕ)

open scoped Classical in
/-- The linear hash maps from numbers below `q` to numbers below the prime `p`: a seed
`a ∈ (ZMod p) ^ D`, where `D = ⌊log_p q⌋ + 1`, sends `x` to `∑ᵢ aᵢ xᵢ`, where `xᵢ` are the
base-`p` digits of `x`. -/
noncomputable def linearHash : Finset (ℕ → ℕ) :=
  (univ : Finset (Fin (Nat.log p q + 1) → ZMod p)).image fun a x => (a ⬝ᵥ digitVec p q x).val

variable {p q}

/-- The linear hash maps take values below `p`. -/
theorem linearHash_lt {u : ℕ → ℕ} (hu : u ∈ linearHash p q) (x : ℕ) : u x < p := by
  classical
  obtain ⟨a, -, rfl⟩ := mem_image.1 hu
  exact ZMod.val_lt _

/-- There are at most `p * q` linear hash maps. -/
theorem card_linearHash_le (hq : q ≠ 0) : #(linearHash p q) ≤ p * q := by
  classical
  refine card_image_le.trans ?_
  rw [card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, pow_succ']
  exact Nat.mul_le_mul_left p (Nat.pow_log_le_self p hq)

/-- Numbers below `q` are determined by their digits. -/
private lemma eq_of_digitVec_eq {x y : ℕ} (hx : x < q) (hy : y < q)
    (h : digitVec p q x = digitVec p q y) : x = y := by
  have hq : q < p ^ (Nat.log p q + 1) := Nat.lt_pow_succ_log_self (Fact.out : p.Prime).one_lt q
  have := finFunctionFinEquiv.symm.injective (a₁ := ⟨x, hx.trans hq⟩) (a₂ := ⟨y, hy.trans hq⟩)
    (funext fun i => Fin.ext <| by
      simpa [digitVec, ZMod.natCast_eq_natCast_iff'] using congrFun h i)
  simpa using this

/-- A nonzero vector over `ZMod p` is orthogonal to at most a `1 / p` fraction of all vectors:
translating along a coordinate where it does not vanish separates the residues. -/
private lemma mul_card_dotProduct_eq_zero_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v : ι → ZMod p} (hv : v ≠ 0) :
    p * #{a : ι → ZMod p | a ⬝ᵥ v = 0} ≤ Fintype.card (ι → ZMod p) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  rw [← card_univ]
  refine le_of_eq_of_le (b := #((univ : Finset (ZMod p)) ×ˢ
    ({a | a ⬝ᵥ v = 0} : Finset (ι → ZMod p)))) (by rw [card_product, card_univ, ZMod.card]) ?_
  refine card_le_card_of_injOn (fun t => t.2 + Pi.single i t.1) (fun _ _ => mem_univ _) ?_
  rintro ⟨c, a⟩ hca ⟨c', a'⟩ hca' h
  simp only [mem_coe, mem_product, mem_univ, mem_filter, true_and] at hca hca'
  have hc := congrArg (· ⬝ᵥ v) h
  simp only [add_dotProduct, single_dotProduct, hca, hca', zero_add] at hc
  obtain rfl := mul_right_cancel₀ hi hc
  simpa using h

/-- Some linear hash map is injective on a set of numbers below `q` that has fewer than `p`
ordered pairs of distinct elements. -/
theorem exists_injOn_linearHash {S : Finset ℕ} (hS : S ⊆ range q) (hp : #S.offDiag < p) :
    ∃ u ∈ linearHash p q, Set.InjOn u S := by
  classical
  by_contra! h
  have hcover : (univ : Finset (Fin (Nat.log p q + 1) → ZMod p)) ⊆ S.offDiag.biUnion fun xy =>
      {a | a ⬝ᵥ (digitVec p q xy.1 - digitVec p q xy.2) = 0} := fun a _ => by
    have ha := h _ (mem_image_of_mem _ (mem_univ a))
    simp only [Set.InjOn, not_forall] at ha
    obtain ⟨x, hx, y, hy, hxy, hne⟩ := ha
    exact mem_biUnion.2 ⟨(x, y), mem_offDiag.2 ⟨hx, hy, hne⟩, by
      simpa [dotProduct_sub, sub_eq_zero] using ZMod.val_injective _ hxy⟩
  have hle : p * #(univ : Finset (Fin (Nat.log p q + 1) → ZMod p)) ≤
      #S.offDiag * #(univ : Finset (Fin (Nat.log p q + 1) → ZMod p)) :=
    calc _ ≤ p * ∑ xy ∈ S.offDiag, #{a | a ⬝ᵥ (digitVec p q xy.1 - digitVec p q xy.2) = 0} :=
          Nat.mul_le_mul_left _ ((card_le_card hcover).trans card_biUnion_le)
      _ = ∑ xy ∈ S.offDiag, p * #{a | a ⬝ᵥ (digitVec p q xy.1 - digitVec p q xy.2) = 0} :=
          mul_sum ..
      _ ≤ ∑ _xy ∈ S.offDiag, #(univ : Finset (Fin (Nat.log p q + 1) → ZMod p)) :=
          sum_le_sum fun xy hxy => by
            obtain ⟨hx, hy, hne⟩ := mem_offDiag.1 hxy
            exact mul_card_dotProduct_eq_zero_le <| sub_ne_zero.2 fun h =>
              hne (eq_of_digitVec_eq (mem_range.1 (hS hx)) (mem_range.1 (hS hy)) h)
      _ = _ := by rw [sum_const, smul_eq_mul]
  exact hp.not_ge (Nat.le_of_mul_le_mul_right hle (card_pos.2 univ_nonempty))

end Cslib
