/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Fourier
public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Complexity.Foundations.Data.BitString.Block
public import Complexity.Foundations.Data.BitString.Threshold
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
import Complexity.Foundations.Data.BitString.Basic
import Complexity.Foundations.Combinatorics.CentralBinomial
import Complexity.Foundations.LinearAlgebra.Interpolation
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exponential correlation bounds for polynomials over `𝔽₂`

For odd `ℓ`, the exclusive or of the majorities of `k` disjoint blocks of `ℓ` bits
(`BitString.xorMajority`) has correlation at most `(2 d / √ℓ) ^ k` with every Boolean function of
degree at most `d` over `𝔽₂ = ZMod 2` (`BitString.abs_expect_signVal_xorMajority_mul_signVal_le`)
[Chattopadhyay et al., Theorem 1.1][CHLLTV2026].

Write `ℓ = 2 m + 1`; the proof counts dimensions [Chattopadhyay et al., Section 2][CHLLTV2026].
Every function on a block is `q + Maj · r` with `q` and `r` of degree at most `m`
(`BitString.exists_eq_add_majority_mul`), so the products over the blocks of a monomial of at most
`m` bits of the block, possibly times the majority of the block, span all functions on the `k`
blocks. Weigh a block by the size of its monomial, or by `m + 1` when it carries its majority, and a
product by the sum of the weights of its blocks: multiplying by a function of degree `d` raises the
weight by at most `d` [Chattopadhyay et al., Lemma 2.2][CHLLTV2026]. Where a function `P` of degree
`d` agrees with the exclusive or of the majorities, the majority of a block is `P` plus the other
majorities. So if the first block whose monomial has at most `m - d` bits carries its majority, the
product agrees there with a combination of products of smaller weight and of products in which that
block does not carry its majority. By induction on the weight, the latter products span all
functions on the inputs where `P` agrees with the exclusive or of the majorities
[Chattopadhyay et al., Lemma 2.3][CHLLTV2026], and there are about half as many of them as there
are inputs. Hence `P` agrees with the exclusive or of the majorities on at most
`(2 ^ (k ℓ) + (2 N) ^ k) / 2` inputs, where `N` counts the sets `A` of bits of a block with
`m - d < |A| ≤ m` (`BitString.two_mul_card_agree_xorMajority_le`). This bounds the correlation by
`(2 N / 2 ^ ℓ) ^ k` (`BitString.abs_expect_signVal_xorMajority_mul_signVal_le_card`), and
`N ≤ d C(ℓ, m) ≤ d 2 ^ ℓ / √ℓ`.

## Main definitions

* `Cslib.BitString.xorMajority`: the exclusive or of the majorities of `k` blocks of `ℓ` bits.

## Main results

* `Cslib.BitString.exists_mem_lowDegree_forall_weight_le_eq`: every function agrees on the strings
  of weight at most `D` with a function of degree at most `D`.
* `Cslib.BitString.exists_eq_add_majority_mul`: every function on `2 m + 1` bits is `q + Maj · r`
  with `q` and `r` of degree at most `m`.
* `Cslib.BitString.two_mul_card_agree_xorMajority_le`: a function of degree `d` over `𝔽₂` agrees
  with the exclusive or of the majorities on few inputs.
* `Cslib.BitString.abs_expect_signVal_xorMajority_mul_signVal_le_card`: the correlation bound in
  terms of the number of sets of bits just below half of a block.
* `Cslib.BitString.abs_expect_signVal_xorMajority_mul_signVal_le`: the correlation is at most
  `(2 d / √ℓ) ^ k`.

## References

* [E. Chattopadhyay, P. Hatami, C. H. Lee, S. Lovett, A. Tal, E. Viola, *Exponential Correlation
  Bounds for Polynomials*][CHLLTV2026]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

/-- The exclusive or of the majorities of the `k` blocks `block x i` of `ℓ` consecutive bits of a
string `x` of `k * ℓ` bits. -/
def xorMajority (k ℓ : ℕ) : BooleanFunction (k * ℓ) :=
  fun x => parity k fun i => majority ℓ (block x i)

/-! ### Interpolation and the majority decomposition -/

section Interpolation

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **Interpolation on a Hamming ball**: every function agrees on the strings of weight at most `D`
with a function of degree at most `D`. -/
theorem exists_mem_lowDegree_forall_weight_le_eq (D : ℕ) (f : BitString n → R) :
    ∃ q ∈ lowDegree R (Fin n) D, ∀ x, weight x ≤ D → q x = f x := by
  have hf := mem_lowDegree_self f
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨S, -, rfl⟩ := hg
    by_cases hS : #S ≤ D
    · exact ⟨monomial R S, monomial_mem_lowDegree hS, fun _ _ => rfl⟩
    · refine ⟨0, zero_mem _, fun x hx => ?_⟩
      rw [Pi.zero_apply, monomial_apply, ite_eq_right fun h => hS ?_]
      exact (card_le_card fun i hi => by simpa using h i hi).trans hx
  | zero => exact ⟨0, zero_mem _, fun _ _ => rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨p, hp, hpx⟩ := hf
    obtain ⟨q, hq, hqx⟩ := hg
    exact ⟨p + q, add_mem hp hq, fun x hx => by simp [hpx x hx, hqx x hx]⟩
  | smul c f _ hf =>
    obtain ⟨p, hp, hpx⟩ := hf
    exact ⟨c • p, Submodule.smul_mem _ c hp, fun x hx => by simp [hpx x hx]⟩

/-- **The majority decomposition**: every function on `2 m + 1` bits is `q + Maj · r`, with the
majority read as `0` or `1` in `R` and `q` and `r` of degree at most `m`. The function `q`
interpolates on the strings of weight at most `m`, where the majority is false, and `r` on the
others, which are the negations of the former [Chattopadhyay et al., Section 2.1][CHLLTV2026]. -/
theorem exists_eq_add_majority_mul {m : ℕ} (f : BitString (2 * m + 1) → R) :
    ∃ q ∈ lowDegree R (Fin (2 * m + 1)) m, ∃ r ∈ lowDegree R (Fin (2 * m + 1)) m,
      ∀ x, f x = q x + bitVal R (majority (2 * m + 1) x) * r x := by
  obtain ⟨q, hq, hqf⟩ := exists_mem_lowDegree_forall_weight_le_eq m f
  obtain ⟨r, hr, hrf⟩ := exists_mem_lowDegree_forall_weight_le_eq m
    fun x => f (fun i => !x i) - q (fun i => !x i)
  refine ⟨q, hq, _, comp_not_mem_lowDegree hr, fun x => ?_⟩
  by_cases hx : weight x ≤ m
  · have hmaj : majority (2 * m + 1) x = false := by
      rw [← Bool.not_eq_true, majority_eq_true_iff]
      omega
    simp [hmaj, hqf x hx]
  · have hmaj : majority (2 * m + 1) x = true := by
      rw [majority_eq_true_iff]
      omega
    have hnot : weight (fun i => !x i) ≤ m := by
      rw [weight_not, Fintype.card_fin]
      omega
    simp only [hmaj, bitVal_true, one_mul, hrf _ hnot, Bool.not_not]
    ring

end Interpolation

/-! ### Counting the tuples whose first good flag is unset -/

section Counting

variable {α : Type*} {k : ℕ}

/-- The flag of the first coordinate of `a` whose first component satisfies `g` is unset. -/
private def FirstFlagUnset (g : α → Prop) (a : Fin k → α × Bool) : Prop :=
  ∀ i, g (a i).1 → (∀ j < i, ¬g (a j).1) → (a i).2 = false

private instance (g : α → Prop) [DecidablePred g] : DecidablePred (FirstFlagUnset (k := k) g) :=
  fun a => inferInstanceAs (Decidable (∀ i, g (a i).1 → (∀ j < i, ¬g (a j).1) → (a i).2 = false))

/-- Flip the flag of the first coordinate of `a` whose first component satisfies `g`. -/
private def flipFirst (g : α → Prop) [DecidablePred g] (a : Fin k → α × Bool) (i : Fin k) :
    α × Bool :=
  if g (a i).1 ∧ ∀ j < i, ¬g (a j).1 then ((a i).1, !(a i).2) else a i

variable {g : α → Prop} [DecidablePred g]

private theorem flipFirst_apply (a : Fin k → α × Bool) (i : Fin k) :
    flipFirst g a i = if g (a i).1 ∧ ∀ j < i, ¬g (a j).1 then ((a i).1, !(a i).2) else a i :=
  rfl

private theorem fst_flipFirst (a : Fin k → α × Bool) (i : Fin k) :
    (flipFirst g a i).1 = (a i).1 := by
  rw [flipFirst_apply]
  split_ifs <;> rfl

private theorem flipFirst_flipFirst (a : Fin k → α × Bool) : flipFirst g (flipFirst g a) = a := by
  funext i
  rw [flipFirst_apply (flipFirst g a) i]
  simp only [fst_flipFirst]
  split_ifs with h
  · rw [flipFirst_apply, ite_eq_left h, Bool.not_not]
  · rw [flipFirst_apply, ite_eq_right h]

/-- At most one coordinate is the first to satisfy `p`. -/
private theorem eq_of_forall_lt_not {p : Fin k → Prop} {i j : Fin k} (hi : p i)
    (hmi : ∀ t < i, ¬p t) (hj : p j) (hmj : ∀ t < j, ¬p t) : i = j := by
  obtain h | h | h := lt_trichotomy i j
  · exact absurd hi (hmj i h)
  · exact h
  · exact absurd hj (hmi j h)

omit [DecidablePred g] in
private theorem firstFlagUnset_iff {a : Fin k → α × Bool} {i : Fin k} (hi : g (a i).1)
    (hmi : ∀ j < i, ¬g (a j).1) : FirstFlagUnset g a ↔ (a i).2 = false :=
  ⟨fun h => h i hi hmi, fun h _ hj hmj => eq_of_forall_lt_not hi hmi hj hmj ▸ h⟩

/-- For each tuple `a`, `a` and `flipFirst g a` together satisfy `FirstFlagUnset g` once when some
coordinate satisfies `g`, and twice when none does. -/
private theorem ite_firstFlagUnset_add_flipFirst (a : Fin k → α × Bool) :
    ((if FirstFlagUnset g a then 1 else 0) +
      if FirstFlagUnset g (flipFirst g a) then 1 else 0) =
      1 + if ∀ i, ¬g (a i).1 then 1 else 0 := by
  by_cases h : ∃ i, g (a i).1
  · have hi := Fin.find_spec h
    have hmi : ∀ j < Fin.find _ h, ¬g (a j).1 := fun j hj => Fin.find_min h hj
    have hfi : g (flipFirst g a (Fin.find _ h)).1 := by rwa [fst_flipFirst]
    have hfmi : ∀ j < Fin.find _ h, ¬g (flipFirst g a j).1 := by simpa only [fst_flipFirst]
    have e₁ := firstFlagUnset_iff hi hmi
    have e₂ := firstFlagUnset_iff hfi hfmi
    rw [flipFirst_apply, ite_eq_left ⟨hi, hmi⟩] at e₂
    have h' : ¬∀ i, ¬g (a i).1 := fun h' => h.elim fun i hi => h' i hi
    cases hb : (a (Fin.find _ h)).2 <;> simp_all
  · push Not at h
    have h₁ : FirstFlagUnset g a := fun i hi => absurd hi (h i)
    have h₂ : FirstFlagUnset g (flipFirst g a) := fun i hi =>
      absurd (by rwa [fst_flipFirst] at hi) (h i)
    simp [h₁, h₂, h]

/-- Flipping the flag of the first coordinate whose first component satisfies `g` pairs the tuples
in which that flag is unset with the others, except for the tuples without such a coordinate. -/
private theorem two_mul_card_filter_firstFlagUnset (S : Finset α) (k : ℕ) :
    2 * #{a ∈ Fintype.piFinset fun _ : Fin k => S ×ˢ (univ : Finset Bool) | FirstFlagUnset g a} =
      (2 * #S) ^ k + (2 * #{A ∈ S | ¬g A}) ^ k := by
  set P := Fintype.piFinset fun _ : Fin k => S ×ˢ (univ : Finset Bool)
  have hP (a : Fin k → α × Bool) : flipFirst g a ∈ P ↔ a ∈ P := by
    simp only [P, Fintype.mem_piFinset, mem_product, mem_univ, and_true, fst_flipFirst]
  have hflip : #{a ∈ P | FirstFlagUnset g (flipFirst g a)} = #{a ∈ P | FirstFlagUnset g a} := by
    refine card_nbij' (flipFirst g) (flipFirst g) (fun a ha => ?_) (fun a ha => ?_)
      (fun a _ => flipFirst_flipFirst a) (fun a _ => flipFirst_flipFirst a)
    · simp only [coe_filter, Set.mem_ofPred_eq] at ha ⊢
      exact ⟨(hP a).2 ha.1, ha.2⟩
    · simp only [coe_filter, Set.mem_ofPred_eq] at ha ⊢
      exact ⟨(hP a).2 ha.1, by rw [flipFirst_flipFirst]; exact ha.2⟩
  have hsum : ∑ a ∈ P, (((if FirstFlagUnset g a then 1 else 0) +
      if FirstFlagUnset g (flipFirst g a) then 1 else 0) : ℕ) =
        ∑ a ∈ P, (1 + if ∀ i, ¬g (a i).1 then 1 else 0) :=
    sum_congr rfl fun a _ => ite_firstFlagUnset_add_flipFirst a
  simp only [sum_add_distrib, ← card_filter, hflip, sum_const, smul_eq_mul, mul_one] at hsum
  have hnone : {a ∈ P | ∀ i, ¬g (a i).1} =
      Fintype.piFinset fun _ : Fin k => {A ∈ S | ¬g A} ×ˢ (univ : Finset Bool) := by
    ext a
    simp only [P, mem_filter, Fintype.mem_piFinset, mem_product, mem_univ, and_true, ← forall_and]
  rw [two_mul, hsum, hnone, Fintype.card_piFinset, Fintype.card_piFinset, prod_const, prod_const,
    card_univ, Fintype.card_fin, card_product, card_product, card_univ, Fintype.card_bool,
    mul_comm #S, mul_comm #{A ∈ S | ¬g A}]

end Counting

/-! ### Products of monomials and majorities of blocks -/

section Blocks

variable {k m : ℕ}

/-- The majority of `2 m + 1` bits, in `ZMod 2`. -/
private def majVal (y : BitString (2 * m + 1)) : ZMod 2 :=
  bitVal (ZMod 2) (majority (2 * m + 1) y)

/-- The monomial of `c.1` on a block, times the majority of the block if `c.2`. -/
private def atom (c : Finset (Fin (2 * m + 1)) × Bool) : BitString (2 * m + 1) → ZMod 2 :=
  (if c.2 then majVal else 1) * monomial (ZMod 2) c.1

/-- The weight of `atom c`: the size of its monomial, or `m + 1` if it carries the majority. -/
private def atomWeight (m : ℕ) (c : Finset (Fin (2 * m + 1)) × Bool) : ℕ :=
  if c.2 then m + 1 else #c.1

/-- The span of the atoms of weight at most `w` whose monomials have at most `m` bits. -/
private def atomSpan (m w : ℕ) : Submodule (ZMod 2) (BitString (2 * m + 1) → ZMod 2) :=
  Submodule.span (ZMod 2) (atom '' {c | #c.1 ≤ m ∧ atomWeight m c ≤ w})

/-- The product over the blocks of the atoms `a i`. -/
private def gen (a : Fin k → Finset (Fin (2 * m + 1)) × Bool) (x : BitString (k * (2 * m + 1))) :
    ZMod 2 :=
  ∏ i, atom (a i) (block x i)

/-- The weight of `gen a`: the sum of the weights of its atoms. -/
private def genWeight (m : ℕ) (a : Fin k → Finset (Fin (2 * m + 1)) × Bool) : ℕ :=
  ∑ i, atomWeight m (a i)

/-- The span of the products of weight at most `r` whose monomials have at most `m` bits. -/
private def genSpan (k m r : ℕ) : Submodule (ZMod 2) (BitString (k * (2 * m + 1)) → ZMod 2) :=
  Submodule.span (ZMod 2) (gen '' {a | (∀ i, #(a i).1 ≤ m) ∧ genWeight m a ≤ r})

private theorem majVal_mul_atom (c : Finset (Fin (2 * m + 1)) × Bool) :
    majVal * atom c = atom (c.1, true) := by
  have h : (majVal : BitString (2 * m + 1) → ZMod 2) * majVal = majVal := by
    funext y
    simp only [Pi.mul_apply, majVal]
    cases majority (2 * m + 1) y <;> simp
  obtain ⟨A, b⟩ := c
  cases b <;> simp [atom, ← mul_assoc, h]

private theorem atom_false (A : Finset (Fin (2 * m + 1))) :
    atom (A, false) = monomial (ZMod 2) A := by
  simp [atom]

private theorem atomSpan_mono {w w' : ℕ} (h : w ≤ w') : atomSpan m w ≤ atomSpan m w' :=
  Submodule.span_mono (Set.image_mono fun _ hc => ⟨hc.1, hc.2.trans h⟩)

/-- The atoms span all functions on a block. -/
private theorem atomSpan_eq_top : atomSpan m (m + 1) = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨q, hq, r, hr, hf⟩ := exists_eq_add_majority_mul (R := ZMod 2) f
  have hlow : lowDegree (ZMod 2) (Fin (2 * m + 1)) m ≤ atomSpan m (m + 1) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨A, hA, rfl⟩
    exact Submodule.subset_span
      ⟨(A, false), ⟨hA, by simpa [atomWeight] using Nat.le_succ_of_le hA⟩, atom_false A⟩
  have hmaj : lowDegree (ZMod 2) (Fin (2 * m + 1)) m ≤
      (atomSpan m (m + 1)).comap (LinearMap.mulLeft (ZMod 2) majVal) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨A, hA, rfl⟩
    refine Submodule.subset_span ⟨(A, true), ⟨hA, by simp [atomWeight]⟩, ?_⟩
    rw [← majVal_mul_atom (A, false), atom_false]
    rfl
  rw [show f = q + majVal * r from funext hf]
  exact add_mem (hlow hq) (hmaj hr)

/-- Multiplying an atom by a variable of its block raises its weight by at most one. -/
private theorem bitVal_mul_atom_mem {c : Finset (Fin (2 * m + 1)) × Bool} (hc : #c.1 ≤ m)
    (j : Fin (2 * m + 1)) :
    (fun y : BitString (2 * m + 1) => bitVal (ZMod 2) (y j)) * atom c ∈
      atomSpan m (atomWeight m c + 1) := by
  obtain ⟨A, b⟩ := c
  by_cases h : b = false ∧ #A < m
  · obtain ⟨rfl, hA⟩ := h
    have hcard := card_insert_le j A
    refine Submodule.subset_span
      ⟨(insert j A, false), ⟨show #(insert j A) ≤ m by omega, ?_⟩, ?_⟩
    · simp only [atomWeight, Bool.false_eq_true, ↓reduceIte]
      omega
    · rw [atom_false, atom_false, ← monomial_singleton, monomial_mul, insert_eq]
  · refine atomSpan_mono ?_ (atomSpan_eq_top (m := m) ▸ Submodule.mem_top)
    cases b
    · simp only [true_and, not_lt] at h
      simp only [atomWeight, Bool.false_eq_true, ↓reduceIte]
      omega
    · simp [atomWeight]

private theorem gen_update (a : Fin k → Finset (Fin (2 * m + 1)) × Bool) (i : Fin k)
    (c : Finset (Fin (2 * m + 1)) × Bool) (x : BitString (k * (2 * m + 1))) :
    gen (Function.update a i c) x =
      atom c (block x i) * ∏ j ∈ univ.erase i, atom (a j) (block x j) := by
  rw [gen, ← mul_prod_erase univ _ (mem_univ i), Function.update_self]
  congr 1
  exact prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]

private theorem genWeight_update (a : Fin k → Finset (Fin (2 * m + 1)) × Bool) (i : Fin k)
    (c : Finset (Fin (2 * m + 1)) × Bool) :
    genWeight m (Function.update a i c) =
      atomWeight m c + ∑ j ∈ univ.erase i, atomWeight m (a j) := by
  rw [genWeight, ← add_sum_erase univ _ (mem_univ i), Function.update_self]
  congr 1
  exact sum_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]

private theorem genWeight_eq (a : Fin k → Finset (Fin (2 * m + 1)) × Bool) (i : Fin k) :
    genWeight m a = atomWeight m (a i) + ∑ j ∈ univ.erase i, atomWeight m (a j) :=
  (add_sum_erase univ (fun j => atomWeight m (a j)) (mem_univ i)).symm

/-- Setting the flag of a block multiplies a product by the majority of the block. -/
private theorem gen_update_true (a : Fin k → Finset (Fin (2 * m + 1)) × Bool) (i : Fin k)
    (x : BitString (k * (2 * m + 1))) :
    gen (Function.update a i ((a i).1, true)) x = majVal (block x i) * gen a x := by
  conv_rhs => rw [← Function.update_eq_self i a, gen_update]
  rw [gen_update, ← mul_assoc, ← majVal_mul_atom]
  rfl

private theorem genSpan_mono {r s : ℕ} (h : r ≤ s) : genSpan k m r ≤ genSpan k m s :=
  Submodule.span_mono (Set.image_mono fun _ ha => ⟨ha.1, ha.2.trans h⟩)

/-- Putting a combination of atoms in place of the atom of one block of a product. -/
private theorem comp_block_mul_mem_genSpan {a : Fin k → Finset (Fin (2 * m + 1)) × Bool}
    (ha : ∀ i, #(a i).1 ≤ m) (i : Fin k) {w : ℕ} {f : BitString (2 * m + 1) → ZMod 2}
    (hf : f ∈ atomSpan m w) :
    (fun x => f (block x i) * ∏ j ∈ univ.erase i, atom (a j) (block x j)) ∈
      genSpan k m (w + ∑ j ∈ univ.erase i, atomWeight m (a j)) := by
  let L := LinearMap.mulRight (ZMod 2) (fun x => ∏ j ∈ univ.erase i, atom (a j) (block x j)) ∘ₗ
    LinearMap.funLeft (ZMod 2) (ZMod 2) fun x : BitString (k * (2 * m + 1)) => block x i
  suffices h : atomSpan m w ≤ (genSpan k m (w + ∑ j ∈ univ.erase i, atomWeight m (a j))).comap L
    from h hf
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, ⟨hc, hcw⟩, rfl⟩
  refine Submodule.subset_span ⟨Function.update a i c, ⟨fun j => ?_, ?_⟩, ?_⟩
  · by_cases hj : j = i
    · subst hj
      simpa using hc
    · simpa [Function.update_of_ne hj] using ha j
  · rw [genWeight_update]
    omega
  · funext x
    simp [L, gen_update]

/-- Multiplying by a variable raises the weight by at most one. -/
private theorem bitVal_mul_mem_genSpan (v : Fin (k * (2 * m + 1))) {r : ℕ}
    {f : BitString (k * (2 * m + 1)) → ZMod 2} (hf : f ∈ genSpan k m r) :
    (fun x => bitVal (ZMod 2) (x v)) * f ∈ genSpan k m (r + 1) := by
  suffices h : genSpan k m r ≤
      (genSpan k m (r + 1)).comap (LinearMap.mulLeft (ZMod 2) fun x => bitVal (ZMod 2) (x v))
    from h hf
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ⟨ha, har⟩, rfl⟩
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective v
  have hmem := comp_block_mul_mem_genSpan ha i (bitVal_mul_atom_mem (ha i) j)
  rw [add_right_comm, ← genWeight_eq] at hmem
  refine genSpan_mono (r := genWeight m a + 1) (by omega) ?_
  convert hmem using 1
  funext x
  simp only [LinearMap.mulLeft_apply, Pi.mul_apply, gen, ← mul_prod_erase univ _ (mem_univ i),
    mul_assoc]
  rfl

/-- Multiplying by a monomial raises the weight by at most its degree. -/
private theorem monomial_mul_mem_genSpan (S : Finset (Fin (k * (2 * m + 1)))) {r : ℕ}
    {f : BitString (k * (2 * m + 1)) → ZMod 2} (hf : f ∈ genSpan k m r) :
    monomial (ZMod 2) S * f ∈ genSpan k m (r + #S) := by
  induction S using Finset.induction_on with
  | empty => simpa using hf
  | insert v S hv ih =>
    rw [insert_eq, ← monomial_mul, monomial_singleton, mul_assoc, ← insert_eq,
      card_insert_of_notMem hv, ← add_assoc]
    exact bitVal_mul_mem_genSpan v ih

/-- **The multiplication lemma**: multiplying by a function of degree at most `d` raises the
weight by at most `d` [Chattopadhyay et al., Lemma 2.2][CHLLTV2026]. -/
private theorem mul_mem_genSpan {d r : ℕ} {P f : BitString (k * (2 * m + 1)) → ZMod 2}
    (hP : P ∈ lowDegree (ZMod 2) (Fin (k * (2 * m + 1))) d) (hf : f ∈ genSpan k m r) :
    P * f ∈ genSpan k m (r + d) := by
  suffices h : lowDegree (ZMod 2) (Fin (k * (2 * m + 1))) d ≤
      (genSpan k m (r + d)).comap (LinearMap.mulRight (ZMod 2) f) from h hP
  refine Submodule.span_le.2 ?_
  rintro _ ⟨S, hS, rfl⟩
  exact genSpan_mono (Nat.add_le_add_left hS r) (monomial_mul_mem_genSpan S hf)

/-- The products span all functions. -/
private theorem mem_genSpan (f : BitString (k * (2 * m + 1)) → ZMod 2) :
    f ∈ genSpan k m (k * (2 * m + 1)) := by
  have h1 : (1 : BitString (k * (2 * m + 1)) → ZMod 2) ∈ genSpan k m 0 := by
    refine Submodule.subset_span ⟨fun _ => (∅, false), ⟨fun _ => by simp, by
      simp [genWeight, atomWeight]⟩, ?_⟩
    funext x
    simp [gen, atom_false]
  simpa using mul_mem_genSpan (mem_lowDegree_self f) h1

/-- Parity in `ZMod 2` is the sum of the bits. -/
private theorem bitVal_parityOn {n : ℕ} (s : Finset (Fin n)) (y : BitString n) :
    bitVal (ZMod 2) (parityOn s y) = ∑ i ∈ s, bitVal (ZMod 2) (y i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [parityOn_insert hi, sum_insert hi, ← ih]
    cases y i <;> cases parityOn s y <;> decide

/-- The exclusive or of the majorities, in `ZMod 2`. -/
private theorem bitVal_xorMajority (x : BitString (k * (2 * m + 1))) :
    bitVal (ZMod 2) (xorMajority k (2 * m + 1) x) = ∑ i, majVal (block x i) :=
  bitVal_parityOn univ _

/-- Clearing the flag at the first block `i` where `#(a i).1 + d ≤ m` and setting the flag at any
other block `j ≠ i` yields a generator in the allowed span. -/
private theorem gen_update_update_mem_span_firstFlagUnset {d : ℕ}
    {a : Fin k → Finset (Fin (2 * m + 1)) × Bool} (ha : ∀ t, #(a t).1 ≤ m) {i j : Fin k}
    (hi : #(a i).1 + d ≤ m) (hmi : ∀ t < i, ¬#(a t).1 + d ≤ m) (hj : j ≠ i) :
    let a' := Function.update a i ((a i).1, false)
    gen (Function.update a' j ((a' j).1, true)) ∈
      Submodule.span (ZMod 2) (gen '' {b | (∀ t, #(b t).1 ≤ m) ∧
        FirstFlagUnset (fun A : Finset (Fin (2 * m + 1)) => #A + d ≤ m) b}) := by
  intro a'
  have hfst (t : Fin k) : (a' t).1 = (a t).1 := by
    by_cases ht : t = i
    · subst ht
      simp [a']
    · simp [a', Function.update_of_ne ht]
  have hfst' (t : Fin k) : (Function.update a' j ((a' j).1, true) t).1 = (a t).1 := by
    by_cases ht : t = j
    · subst ht
      simp [hfst]
    · simp [Function.update_of_ne ht, hfst]
  refine Submodule.subset_span ⟨_, ⟨fun t => hfst' t ▸ ha t, fun t ht hmt => ?_⟩, rfl⟩
  simp only [hfst'] at ht hmt
  rw [← eq_of_forall_lt_not hi hmi ht hmt, Function.update_of_ne hj.symm]
  simp [a']

/-- The submodule of functions on `BitString (k * (2 * m + 1))` that agree on `E` with some element
of `V`. -/
private def agreeSubmodule (E : Finset (BitString (k * (2 * m + 1))))
    (V : Submodule (ZMod 2) (BitString (k * (2 * m + 1)) → ZMod 2)) :
    Submodule (ZMod 2) (BitString (k * (2 * m + 1)) → ZMod 2) where
  carrier := {f | ∃ g ∈ V, ∀ x ∈ E, g x = f x}
  add_mem' := fun ⟨g, hg, hgx⟩ ⟨g', hg', hgx'⟩ =>
    ⟨g + g', add_mem hg hg', fun x hx => by simp [hgx x hx, hgx' x hx]⟩
  zero_mem' := ⟨0, zero_mem _, fun _ _ => rfl⟩
  smul_mem' := fun c _ ⟨g, hg, hgx⟩ =>
    ⟨c • g, Submodule.smul_mem _ c hg, fun x hx => by simp [hgx x hx]⟩

/-- When `P x = ∑ j, majVal (block x j)` and `(a i).2 = true`, replacing the majority of block `i`
using `P` decomposes `gen a` at `x` into `P * gen a'` plus the sum over `j ≠ i`. -/
private theorem mul_gen_update_false_add_sum_erase_eq
    {P : BitString (k * (2 * m + 1)) → ZMod 2} {x : BitString (k * (2 * m + 1))}
    (hx : P x = ∑ j, majVal (block x j))
    {a : Fin k → Finset (Fin (2 * m + 1)) × Bool} {i : Fin k} (hb : (a i).2 = true) :
    let a' := Function.update a i ((a i).1, false)
    (P * gen a' + ∑ j ∈ univ.erase i, gen (Function.update a' j ((a' j).1, true))) x =
      gen a x := by
  intro a'
  have ha_eq : Function.update a' i ((a' i).1, true) = a := by
    dsimp only [a']
    rw [Function.update_self, Function.update_idem,
      show ((a i).1, true) = a i from Prod.ext rfl hb.symm, Function.update_eq_self]
  rw [← ha_eq]
  simp only [Pi.add_apply, Pi.mul_apply, Finset.sum_apply, gen_update_true]
  rw [← sum_mul, ← add_mul, hx, ← add_sum_erase univ (fun j => majVal (block x j))
    (mem_univ i), add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- **The agreement lemma**: on inputs where `P` agrees with the exclusive or of the majorities,
every function agrees with a combination of products in which the first block whose monomial has
at most `m - d` bits does not carry its majority [Chattopadhyay et al., Lemma 2.3][CHLLTV2026]. -/
private theorem exists_mem_span_firstFlagUnset_eq {d : ℕ}
    {P : BitString (k * (2 * m + 1)) → ZMod 2}
    (hP : P ∈ lowDegree (ZMod 2) (Fin (k * (2 * m + 1))) d)
    {E : Finset (BitString (k * (2 * m + 1)))} (hE : ∀ x ∈ E, P x = ∑ i, majVal (block x i))
    (f : BitString (k * (2 * m + 1)) → ZMod 2) :
    ∃ g ∈ Submodule.span (ZMod 2) (gen '' {a | (∀ i, #(a i).1 ≤ m) ∧
        FirstFlagUnset (fun A : Finset (Fin (2 * m + 1)) => #A + d ≤ m) a}),
      ∀ x ∈ E, g x = f x := by
  set V := Submodule.span (ZMod 2) (gen '' {a | (∀ i, #(a i).1 ≤ m) ∧
    FirstFlagUnset (fun A : Finset (Fin (2 * m + 1)) => #A + d ≤ m) a})
  let U := agreeSubmodule E V
  have hgen (n : ℕ) : ∀ a : Fin k → Finset (Fin (2 * m + 1)) × Bool,
      (∀ i, #(a i).1 ≤ m) → genWeight m a = n → gen a ∈ U := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro a ha hn
    by_cases hall : FirstFlagUnset (fun A : Finset (Fin (2 * m + 1)) => #A + d ≤ m) a
    · exact ⟨gen a, Submodule.subset_span ⟨a, ⟨ha, hall⟩, rfl⟩, fun _ _ => rfl⟩
    -- the first block with room for `d` more bits carries its majority
    obtain ⟨i, hi, hmi, hb⟩ : ∃ i, #(a i).1 + d ≤ m ∧ (∀ j < i, ¬#(a j).1 + d ≤ m) ∧
        (a i).2 = true := by
      simpa [FirstFlagUnset] using hall
    set a' := Function.update a i ((a i).1, false) with ha'_def
    have ha' (j : Fin k) : #(a' j).1 ≤ m := by
      rcases eq_or_ne j i with rfl | hj <;> simp [a', Function.update_of_ne, ha j, *]
    -- without the majority of block `i`, and times `P`, the product has smaller weight
    have hlow : P * gen a' ∈ U := by
      have hw : genWeight m a' + d < n := by
        rw [← hn, ha'_def, genWeight_update, genWeight_eq a i]
        simp only [atomWeight, hb, ↓reduceIte, Bool.false_eq_true]
        omega
      refine (Submodule.span_le.2 ?_ : genSpan k m (genWeight m a' + d) ≤ U)
        (mul_mem_genSpan hP (Submodule.subset_span ⟨a', ⟨ha', le_rfl⟩, rfl⟩))
      rintro _ ⟨b, ⟨hb', hbw⟩, rfl⟩
      exact ih _ (by omega) b hb' rfl
    -- with the majority of another block instead, the product is allowed
    have hrest : ∀ j ∈ univ.erase i, gen (Function.update a' j ((a' j).1, true)) ∈ U := fun j hj =>
      ⟨_, gen_update_update_mem_span_firstFlagUnset ha hi hmi (ne_of_mem_erase hj), fun _ _ => rfl⟩
    obtain ⟨g, hg, hgx⟩ := add_mem hlow (Submodule.sum_mem U hrest)
    exact ⟨g, hg, fun x hx =>
      (hgx x hx).trans (mul_gen_update_false_add_sum_erase_eq (hE x hx) hb)⟩
  suffices h : genSpan k m (k * (2 * m + 1)) ≤ U from h (mem_genSpan f)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
  exact hgen _ a ha rfl

end Blocks

/-! ### Counting dimensions -/

/-- **A function of low degree agrees with the exclusive or of majorities on few inputs**: if `P`
has degree at most `d` over `ZMod 2` on `k` blocks of `2 m + 1` bits, twice the number of inputs on
which `P` agrees with the exclusive or of the majorities of the blocks is at most
`2 ^ (k (2 m + 1)) + (2 N) ^ k`, where `N` is the number of sets `A` of bits of a block with
`m - d < |A| ≤ m` [Chattopadhyay et al., Section 2.3][CHLLTV2026]. -/
theorem two_mul_card_agree_xorMajority_le {k m d : ℕ}
    {P : BitString (k * (2 * m + 1)) → ZMod 2}
    (hP : P ∈ lowDegree (ZMod 2) (Fin (k * (2 * m + 1))) d) :
    2 * #{x | P x = bitVal (ZMod 2) (xorMajority k (2 * m + 1) x)} ≤
      2 ^ (k * (2 * m + 1)) +
        (2 * #{A : Finset (Fin (2 * m + 1)) | #A ≤ m ∧ m < #A + d}) ^ k := by
  set S : Finset (Finset (Fin (2 * m + 1))) := {A | #A ≤ m}
  set T := {a ∈ Fintype.piFinset fun _ : Fin k => S ×ˢ (univ : Finset Bool) |
    FirstFlagUnset (fun A : Finset (Fin (2 * m + 1)) => #A + d ≤ m) a}
  set E := ({x | P x = bitVal (ZMod 2) (xorMajority k (2 * m + 1) x)} : Finset _)
  have hE : #E ≤ #T := LinearAlgebra.card_le_of_forall_exists_mem_span_eq E T gen fun f => by
    obtain ⟨g, hg, hgx⟩ := exists_mem_span_firstFlagUnset_eq hP (E := E)
      (fun x hx => by rw [← bitVal_xorMajority]; exact (mem_filter.1 hx).2) f
    refine ⟨g, ?_, hgx⟩
    convert hg using 3
    ext a
    simp [T, S, Fintype.mem_piFinset]
  have hS : 2 * #S ≤ 2 ^ (2 * m + 1) := by
    convert two_mul_card_small_le (2 * m + 1) using 3
    ext A
    simp only [S, mem_filter, mem_univ, true_and]
    omega
  have hband : #{A ∈ S | ¬#A + d ≤ m} =
      #{A : Finset (Fin (2 * m + 1)) | #A ≤ m ∧ m < #A + d} := by
    simp only [S, filter_filter, not_le]
  calc
    2 * #E ≤ 2 * #T := Nat.mul_le_mul_left 2 hE
    _ = (2 * #S) ^ k + (2 * #{A ∈ S | ¬#A + d ≤ m}) ^ k :=
      two_mul_card_filter_firstFlagUnset S k
    _ ≤ (2 ^ (2 * m + 1)) ^ k + (2 * #{A ∈ S | ¬#A + d ≤ m}) ^ k := by gcongr
    _ = _ := by rw [hband, ← pow_mul, Nat.mul_comm (2 * m + 1)]

/-! ### Correlation -/

/-- If `p` and its negation each agree with `f` on at most `(2 ^ n + B) / 2` inputs, the
correlation of `f` and `p` is at most `B / 2 ^ n`. -/
private theorem abs_expect_signVal_mul_le_of_two_mul_card_le {n : ℕ} {f p : BooleanFunction n}
    {B : ℝ} (h₁ : 2 * (#{x | p x = f x} : ℝ) ≤ 2 ^ n + B)
    (h₂ : 2 * (#{x | (!p x) = f x} : ℝ) ≤ 2 ^ n + B) :
    |𝔼 x, signVal (f x) * signVal (p x)| ≤ B / 2 ^ n := by
  have hd : #{x | (!p x) = f x} = hammingDist f p := by
    simp only [hammingDist]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    cases f x <;> cases p x <;> decide
  have hsum : (#{x | p x = f x} : ℝ) + #{x | (!p x) = f x} = 2 ^ n := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (BitString n)))
      fun x => p x = f x
    rw [card_univ, BitString.card] at h
    have he : #{x | ¬p x = f x} = #{x | (!p x) = f x} := by
      congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and]
      cases f x <;> cases p x <;> decide
    rw [he] at h
    exact_mod_cast h
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have key : 1 - 2 * (hammingDist f p : ℝ) / 2 ^ n = (2 * #{x | p x = f x} - 2 ^ n) / 2 ^ n := by
    rw [eq_div_iff hpos.ne', sub_mul, div_mul_cancel₀ _ hpos.ne', one_mul, ← hd]
    linarith
  rw [expect_signVal_mul_signVal, Fintype.card_fin, key, abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) hpos.le

/-- **The correlation bound by the middle band**: for a Boolean function `p` of degree at most `d`
over `ZMod 2` on `k` blocks of `2 m + 1` bits, the correlation of the exclusive or of the
majorities of the blocks with `p`, read as signs, is at most `(2 N / 2 ^ (2 m + 1)) ^ k` in absolute
value, where `N` is the number of sets `A` of bits of a block with `m - d < |A| ≤ m`
[Chattopadhyay et al., Section 2.3][CHLLTV2026]. -/
theorem abs_expect_signVal_xorMajority_mul_signVal_le_card {k m d : ℕ}
    {p : BooleanFunction (k * (2 * m + 1))}
    (hp : (fun x => bitVal (ZMod 2) (p x)) ∈ lowDegree (ZMod 2) (Fin (k * (2 * m + 1))) d) :
    |𝔼 x, signVal (xorMajority k (2 * m + 1) x) * signVal (p x)| ≤
      (2 * #{A : Finset (Fin (2 * m + 1)) | #A ≤ m ∧ m < #A + d} /
        2 ^ (2 * m + 1)) ^ k := by
  have hinj (a b : Bool) : bitVal (ZMod 2) a = bitVal (ZMod 2) b ↔ a = b := by
    cases a <;> cases b <;> decide
  have h₁ := two_mul_card_agree_xorMajority_le hp
  have h₂ := two_mul_card_agree_xorMajority_le (P := fun x => bitVal (ZMod 2) (!p x)) (by
    have h : (fun x => bitVal (ZMod 2) (!p x)) = 1 - fun x => bitVal (ZMod 2) (p x) := by
      funext x
      simp [bitVal_not]
    rw [h]
    exact one_sub_mem_lowDegree hp)
  simp only [hinj] at h₁ h₂
  rw [div_pow, ← pow_mul, Nat.mul_comm (2 * m + 1)]
  exact abs_expect_signVal_mul_le_of_two_mul_card_le (by exact_mod_cast h₁) (by exact_mod_cast h₂)

/-- The sets of bits just below half of a block are few: at most `d` middle binomial
coefficients. -/
private theorem card_filter_card_le_le_choose (m d : ℕ) :
    #{A : Finset (Fin (2 * m + 1)) | #A ≤ m ∧ m < #A + d} ≤ d * (2 * m + 1).choose m := by
  calc
    _ ≤ #((Icc (m + 1 - d) m).biUnion fun s => powersetCard s (univ : Finset (Fin (2 * m + 1)))) :=
      card_le_card fun A hA => by
        simp only [mem_filter, mem_univ, true_and] at hA
        simp only [mem_biUnion, mem_Icc, mem_powersetCard]
        exact ⟨#A, ⟨by omega, hA.1⟩, subset_univ A, rfl⟩
    _ ≤ ∑ s ∈ Icc (m + 1 - d) m, #(powersetCard s (univ : Finset (Fin (2 * m + 1)))) :=
      card_biUnion_le
    _ ≤ ∑ _s ∈ Icc (m + 1 - d) m, (2 * m + 1).choose m := by
      refine sum_le_sum fun s _ => ?_
      rw [card_powersetCard, card_univ, Fintype.card_fin]
      simpa [show (2 * m + 1) / 2 = m by omega] using Nat.choose_le_middle s (2 * m + 1)
    _ ≤ d * (2 * m + 1).choose m := by
      rw [sum_const, Nat.card_Icc, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (by omega)

/-- The middle binomial coefficient of an odd number `ℓ` is at most `2 ^ ℓ / √ℓ`. -/
private theorem choose_mul_sqrt_le (m : ℕ) :
    ((2 * m + 1).choose m : ℝ) * √((2 * m + 1 : ℕ) : ℝ) ≤ 2 ^ (2 * m + 1) := by
  have h := choose_half_sq_mul_le (2 * m + 1)
  rw [show (2 * m + 1) / 2 = m by omega] at h
  have h' : ((2 * m + 1).choose m : ℝ) ^ 2 * (2 * m + 1 : ℕ) ≤ (2 ^ (2 * m + 1)) ^ 2 := by
    have : (2 * m + 1).choose m ^ 2 * (2 * m + 1) ≤ (2 ^ (2 * m + 1)) ^ 2 :=
      calc
        _ ≤ (2 * m + 1).choose m ^ 2 * (2 * m + 1 + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
        _ ≤ 4 ^ (2 * m + 1) := h
        _ = (2 ^ (2 * m + 1)) ^ 2 := by rw [← pow_mul, pow_mul']; norm_num
    exact_mod_cast this
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 ^ (2 * m + 1)),
    ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (2 * m + 1).choose m),
    ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt h'

/-- **Exponential correlation bound for polynomials**: for odd `ℓ`, the correlation of the
exclusive or of the majorities of `k` disjoint blocks of `ℓ` bits with a Boolean function `p` of
degree at most `d` over `ZMod 2`, read as signs, is at most `(2 d / √ℓ) ^ k` in absolute value
[Chattopadhyay et al., Theorem 1.1][CHLLTV2026]. -/
theorem abs_expect_signVal_xorMajority_mul_signVal_le {k ℓ d : ℕ} (hℓ : Odd ℓ)
    {p : BooleanFunction (k * ℓ)}
    (hp : (fun x => bitVal (ZMod 2) (p x)) ∈ lowDegree (ZMod 2) (Fin (k * ℓ)) d) :
    |𝔼 x, signVal (xorMajority k ℓ x) * signVal (p x)| ≤ (2 * d / √ℓ) ^ k := by
  obtain ⟨m, rfl⟩ := hℓ
  refine (abs_expect_signVal_xorMajority_mul_signVal_le_card hp).trans
    (pow_le_pow_left₀ (by positivity) ?_ k)
  have hN : (#{A : Finset (Fin (2 * m + 1)) | #A ≤ m ∧ m < #A + d} : ℝ) ≤
      d * (2 * m + 1).choose m := by
    exact_mod_cast card_filter_card_le_le_choose m d
  have hC := choose_mul_sqrt_le m
  have hs : 0 < √((2 * m + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  rw [div_le_div_iff₀ (by positivity) hs]
  calc
    _ ≤ 2 * (d * (2 * m + 1).choose m) * √((2 * m + 1 : ℕ) : ℝ) := by gcongr
    _ = 2 * d * ((2 * m + 1).choose m * √((2 * m + 1 : ℕ) : ℝ)) := by ring
    _ ≤ 2 * d * 2 ^ (2 * m + 1) := by gcongr

end Cslib.BitString
