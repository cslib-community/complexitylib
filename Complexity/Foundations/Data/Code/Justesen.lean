/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.AsymptoticallyGood
public import Complexity.Foundations.Data.Code.Concatenation
public import Complexity.Foundations.Data.Code.ReedSolomon
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Fintype.Prod
import Complexity.Foundations.Data.BitString.Weight
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finiteness

/-!
# Justesen codes

Let `F` be a finite field whose elements are written as `b` bits through an additive bijection
`φ : F ≃+ BitString b`, so that `F` has `q = 2 ^ b` elements; every field of characteristic two with
`2 ^ b` elements has such a bijection (`Cslib.nonempty_addEquiv_bitString`). The *Justesen
code* [Justesen1972], [GuruswamiRudraSudan2019] of outer dimension `K` concatenates the Reed–Solomon
code of dimension `K` whose evaluation points are the `q - 1` nonzero elements `u` of `F` with inner
codes that vary with the position: the symbol `a` at the position `u` becomes the `2 * b` bits of
`(a, u * a)`, its *Wozencraft encoding* `Cslib.Code.wozencraft` (`Cslib.Code.justesen`,
`Cslib.Code.justesenCode`). No search over inner codes is involved, which is what makes the
construction explicit.

Nonzero symbols at distinct positions have distinct Wozencraft encodings, since `(a, u * a)`
determines `a` and then `u` (`Cslib.Code.wozencraft_inj`). Two distinct Reed–Solomon codewords
differ at `s ≥ q - K` positions; the differences of their inner blocks there are `s` distinct
nonzero binary words of length `2 * b`, at most `V(r) = ∑_{j ≤ r} C(2 * b, j)` of which have
weight at most `r` (`Cslib.BitString.card_filter_weight_le`). So their Justesen
encodings are at distance at least `(q - K - V(r)) * (r + 1)` for every `r`
(`Cslib.Code.le_minDist_justesenCode`), by the counting bound
`Cslib.Code.sub_card_mul_le_sum_hammingNorm`.

With the binomial estimate `V(r) * 4 ^ (2 * b) ≤ 4 ^ r * 5 ^ (2 * b)`
(`Cslib.Code.sum_range_choose_mul_four_pow_le`), this shows that Justesen codes are
*asymptotically good* (`Cslib.Code.IsAsymptoticallyGood`): for `b = 16 * s` and
`K = 2 ^ (16 * s - 1)`, the Justesen code is a binary code of length
`n = 32 * s * (2 ^ (16 * s) - 1)` with `2 ^ k` codewords, where `n ≤ 4 * k`, and minimum distance
at least `n / 128` (`Cslib.Code.card_le_mul_minDist_justesenCode`,
`Cslib.Code.isAsymptoticallyGood_justesenCode`); the lengths grow without bound with `s`, while the
rate stays at least `1 / 4` and the relative distance at least `1 / 128`. These constants are not
optimized: estimating `V(r)` by the binary entropy function `H` instead gives relative distance
approaching `(1 - 2 R) H⁻¹(1 / 2) ≈ 0.11 * (1 - 2 R)` at rate `R < 1 / 2`
[GuruswamiRudraSudan2019]; this is not formalized here.

## Main definitions

* `Cslib.Code.wozencraft`: the Wozencraft inner encoding with a given multiplier.
* `Cslib.Code.justesen`: the Justesen encoding of an outer word.
* `Cslib.Code.justesenCode`: the Justesen code.

## Main results

* `Cslib.Code.wozencraft_inj`: nonzero symbols at distinct positions have distinct encodings.
* `Cslib.Code.sub_card_mul_le_sum_hammingNorm`: many distinct words have large total weight.
* `Cslib.Code.le_minDist_justesenCode`: the minimum distance of Justesen codes.
* `Cslib.Code.card_justesenCode`: the number of codewords.
* `Cslib.Code.card_le_mul_minDist_justesenCode`: the relative distance of Justesen codes at rate at
  least `1 / 4`.
* `Cslib.Code.isAsymptoticallyGood_justesenCode`: Justesen codes are asymptotically good.

## References

* [J. Justesen, *Class of constructive asymptotically good algebraic codes*][Justesen1972]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*]
  [GuruswamiRudraSudan2019]
-/

@[expose] public section

namespace Cslib.Code

open Finset

/-! ### Weights of distinct words -/

section Weights

variable {σ κ β : Type*} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β] [Zero β]

/-- **Distinct words are heavy.** If `g` is injective on `S`, the words `g u` for `u ∈ S` have
total weight at least `(#S - V) * (r + 1)`, where `V` is the number of words of weight at most
`r`. -/
theorem sub_card_mul_le_sum_hammingNorm {S : Finset σ} {g : σ → κ → β} (hg : Set.InjOn g S)
    (r : ℕ) :
    (#S - #{x : κ → β | hammingNorm x ≤ r}) * (r + 1) ≤ ∑ u ∈ S, hammingNorm (g u) := by
  classical
  -- the light words among the `g u` are distinct words in the ball of radius `r`
  have hlight : #{u ∈ S | hammingNorm (g u) ≤ r} ≤ #{x : κ → β | hammingNorm x ≤ r} := by
    rw [← card_image_of_injOn (hg.mono (coe_subset.2 (filter_subset _ S)))]
    refine card_le_card fun x hx => ?_
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hx
    exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hu).2⟩
  have hsplit := card_filter_add_card_filter_not (s := S) fun u => hammingNorm (g u) ≤ r
  calc (#S - #{x : κ → β | hammingNorm x ≤ r}) * (r + 1)
      ≤ #{u ∈ S | ¬hammingNorm (g u) ≤ r} * (r + 1) := Nat.mul_le_mul_right _ (by omega)
    _ = ∑ u ∈ S with ¬hammingNorm (g u) ≤ r, (r + 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ ∑ u ∈ S with ¬hammingNorm (g u) ≤ r, hammingNorm (g u) :=
        sum_le_sum fun u hu => Nat.succ_le_of_lt (not_le.1 (mem_filter.1 hu).2)
    _ ≤ ∑ u ∈ S, hammingNorm (g u) := sum_le_sum_of_subset (filter_subset _ S)

end Weights

/-- **A binomial estimate** for the size of a Hamming ball: `V * 4 ^ ℓ ≤ 4 ^ r * 5 ^ ℓ` for
`V = ∑_{j ≤ r} C(ℓ, j)`, since `5 ^ ℓ = ∑_j C(ℓ, j) * 4 ^ (ℓ - j)`. -/
theorem sum_range_choose_mul_four_pow_le (ℓ r : ℕ) :
    (∑ j ∈ range (r + 1), ℓ.choose j) * 4 ^ ℓ ≤ 4 ^ r * 5 ^ ℓ := by
  have hterm : ∀ j ∈ range (r + 1),
      ℓ.choose j * 4 ^ ℓ ≤ 4 ^ r * (1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j) := by
    intro j hj
    rcases lt_or_ge ℓ j with hℓj | hjℓ
    · rw [Nat.choose_eq_zero_of_lt hℓj, zero_mul]
      exact Nat.zero_le _
    have hjr := Nat.lt_succ_iff.1 (mem_range.1 hj)
    calc ℓ.choose j * 4 ^ ℓ = ℓ.choose j * (4 ^ j * 4 ^ (ℓ - j)) := by
          rw [← pow_add, Nat.add_sub_cancel' hjℓ]
      _ ≤ ℓ.choose j * (4 ^ r * 4 ^ (ℓ - j)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hjr))
      _ = 4 ^ r * (1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j) := by ring
  -- the binomial expansion of `5 ^ ℓ`, whose terms beyond `ℓ` vanish
  have htail : ∑ j ∈ range (r + 1), 1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j ≤ 5 ^ ℓ := by
    calc ∑ j ∈ range (r + 1), 1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j
        ≤ ∑ j ∈ range (ℓ + 1 + (r + 1)), 1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j :=
          sum_le_sum_of_subset (range_subset_range.2 (by omega))
      _ = 5 ^ ℓ := by
          have h0 : ∑ j ∈ range (r + 1), 1 ^ (ℓ + 1 + j) * 4 ^ (ℓ - (ℓ + 1 + j)) *
              ℓ.choose (ℓ + 1 + j) = 0 :=
            sum_eq_zero fun j _ => by rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
          rw [sum_range_add, h0, add_zero, show (5 : ℕ) = 1 + 4 by rfl, add_pow]
          simp only [Nat.cast_id]
  calc (∑ j ∈ range (r + 1), ℓ.choose j) * 4 ^ ℓ
      = ∑ j ∈ range (r + 1), ℓ.choose j * 4 ^ ℓ := sum_mul _ _ _
    _ ≤ ∑ j ∈ range (r + 1), 4 ^ r * (1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j) := sum_le_sum hterm
    _ = 4 ^ r * ∑ j ∈ range (r + 1), 1 ^ j * 4 ^ (ℓ - j) * ℓ.choose j := (mul_sum _ _ _).symm
    _ ≤ 4 ^ r * 5 ^ ℓ := Nat.mul_le_mul_left _ htail

/-! ### The Wozencraft encoding -/

variable {F : Type*} [Field F] {b : ℕ}

/-- The *Wozencraft encoding* of the symbol `a` with multiplier `u`: the binary word on
`Fin 2 × Fin b` holding the bits of `a` in its first half and the bits of `u * a` in its second,
read through the additive bijection `φ : F ≃+ BitString b`. -/
def wozencraft (φ : F ≃+ BitString b) (u a : F) : Fin 2 × Fin b → Bool :=
  fun j => φ (if j.1 = 0 then a else u * a) j.2

/-- The Wozencraft encoding with a fixed multiplier is additive. -/
theorem wozencraft_sub (φ : F ≃+ BitString b) (u a a' : F) :
    wozencraft φ u (a - a') = wozencraft φ u a - wozencraft φ u a' := by
  funext j
  simp only [wozencraft, Pi.sub_apply]
  split_ifs
  · rw [map_sub, Pi.sub_apply]
  · rw [mul_sub, map_sub, Pi.sub_apply]

/-- The Wozencraft encoding with a fixed multiplier is injective: the first half of the encoding
holds the bits of the symbol. -/
theorem wozencraft_injective (φ : F ≃+ BitString b) (u : F) :
    Function.Injective (wozencraft φ u) := fun a a' h =>
  φ.injective (funext fun t => by simpa [wozencraft] using congrFun h (0, t))

/-- **Distinct inner codes.** The Wozencraft encoding of a nonzero symbol determines the symbol and
the multiplier: nonzero symbols at distinct positions of a Justesen codeword have distinct
encodings. -/
theorem wozencraft_inj (φ : F ≃+ BitString b) {u u' a a' : F} (ha : a ≠ 0)
    (h : wozencraft φ u a = wozencraft φ u' a') : u = u' ∧ a = a' := by
  have hfirst : a = a' :=
    φ.injective (funext fun t => by simpa [wozencraft] using congrFun h (0, t))
  subst hfirst
  have hsecond : u * a = u' * a :=
    φ.injective (funext fun t => by simpa [wozencraft] using congrFun h (1, t))
  exact ⟨mul_right_cancel₀ ha hsecond, rfl⟩

/-! ### Justesen codes -/

/-- The *Justesen encoding* of an outer word `c` on the nonzero elements of `F`: the concatenation
whose block at the position `u` is the Wozencraft encoding of `c u` with multiplier `u`. -/
def justesen (φ : F ≃+ BitString b) (c : Fˣ → F) : Fˣ × (Fin 2 × Fin b) → Bool :=
  concat (fun p : Fˣ × F => wozencraft φ (p.1 : F) p.2) fun u => (u, c u)

/-- The Justesen encoding is injective. -/
theorem justesen_injective (φ : F ≃+ BitString b) : Function.Injective (justesen φ) :=
  fun _ _ h => funext fun u =>
    wozencraft_injective φ u (funext fun j => congrFun h (u, j))

/-- The *Justesen code* of outer dimension `K`: the Justesen encodings of the codewords of the
Reed–Solomon code of dimension `K` whose evaluation points are the nonzero elements of `F`. -/
noncomputable def justesenCode (φ : F ≃+ BitString b) (K : ℕ) :
    Set (Fˣ × (Fin 2 × Fin b) → Bool) :=
  justesen φ '' (reedSolomon (fun u : Fˣ => (u : F)) K : Set (Fˣ → F))

variable [Fintype F] [DecidableEq F]

/-- **The distance of Justesen codes** [Justesen1972]. For a field with `q` elements written as
`b` bits, the Justesen code of outer dimension `K` has minimum distance at least
`(q - K - V(r)) * (r + 1)` for every `r`, where `V(r) = ∑_{j ≤ r} C(2 * b, j)` is the number of
binary words of length `2 * b` and weight at most `r`. -/
theorem le_minDist_justesenCode (φ : F ≃+ BitString b) (K r : ℕ) :
    (((Fintype.card F - K - ∑ j ∈ range (r + 1), (2 * b).choose j) * (r + 1) : ℕ) : ℕ∞) ≤
      minDist (justesenCode φ K) := by
  classical
  refine le_minDist_iff.2 ?_
  rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ hne
  have hcc' : c ≠ c' := fun h => hne (h ▸ rfl)
  -- the outer codewords differ at `#S ≥ q - K` positions
  let S : Finset Fˣ := {u | c u ≠ c' u}
  have hS : Fintype.card F - K ≤ #S := by
    have h := le_minDist_iff.1 (le_minDist_reedSolomon (F := F) Units.val_injective K) c hc c' hc'
      hcc'
    rw [Nat.cast_le, Fintype.card_units] at h
    change _ ≤ hammingDist c c'
    omega
  -- where the inner blocks differ by the encodings of the nonzero differences
  let g : Fˣ → Fin 2 × Fin b → Bool := fun u => wozencraft φ u (c' u - c u)
  have hg : Set.InjOn g S := by
    intro u hu u' _ h
    have hu : c' u - c u ≠ 0 := sub_ne_zero.2 fun h' => (mem_filter.1 hu).2 h'.symm
    exact Units.val_injective (wozencraft_inj φ hu h).1
  have hball : #{x : Fin 2 × Fin b → Bool | hammingNorm x ≤ r} =
      ∑ j ∈ range (r + 1), (2 * b).choose j := by
    simp only [← BitString.weight_eq_hammingNorm, BitString.card_filter_weight_le,
      Fintype.card_prod, Fintype.card_fin]
  have hweight := sub_card_mul_le_sum_hammingNorm hg r
  rw [hball] at hweight
  refine Nat.cast_le.2 ((Nat.mul_le_mul_right _ (Nat.sub_le_sub_right hS _)).trans
    (hweight.trans ?_))
  rw [justesen, justesen, hammingDist_concat]
  calc ∑ u ∈ S, hammingNorm (g u) ≤ ∑ u, hammingNorm (g u) := sum_le_sum_of_subset (subset_univ _)
    _ = ∑ u : Fˣ, hammingDist (wozencraft φ (u : F) (c u)) (wozencraft φ (u : F) (c' u)) := by
        refine sum_congr rfl fun u _ => ?_
        rw [hammingDist_eq_hammingNorm, neg_add_eq_sub, ← wozencraft_sub]

omit [DecidableEq F] in
/-- **The number of Justesen codewords.** For a field with `q` elements written as `b` bits and
`K ≤ q - 1`, the Justesen code of outer dimension `K` has `q ^ K = 2 ^ (b * K)` codewords. -/
theorem card_justesenCode (φ : F ≃+ BitString b) {K : ℕ} (hK : K ≤ Fintype.card F - 1) :
    Nat.card (justesenCode φ K) = 2 ^ (b * K) := by
  classical
  have hq : Fintype.card F = 2 ^ b := by
    rw [Fintype.card_congr φ.toEquiv, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [justesenCode, Nat.card_image_of_injective (justesen_injective φ), Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := F),
    finrank_reedSolomon Units.val_injective (by rwa [Fintype.card_units]), hq, ← pow_mul]

/-- For `s ≥ 1`, the Hamming ball of radius `s` in `32 s` bits has at most `2 ^ (16 s - 2)`
words. -/
private theorem sum_range_choose_two_mul_sixteen_mul_le {s : ℕ} (hs : 1 ≤ s) :
    ∑ j ∈ range (s + 1), (2 * (16 * s)).choose j ≤ 2 ^ (16 * s - 2) := by
  have h := sum_range_choose_mul_four_pow_le (2 * (16 * s)) s
  have hconst : 4 * (4 * 5 ^ 32) ≤ 2 ^ 80 := by norm_num
  have hlhs : 4 * (4 ^ s * 5 ^ (2 * (16 * s))) ≤ 2 ^ (80 * s) := by
    calc 4 * (4 ^ s * 5 ^ (2 * (16 * s))) ≤ 4 ^ s * (4 ^ s * 5 ^ (2 * (16 * s))) :=
          Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 4)
      _ = (4 * (4 * 5 ^ 32)) ^ s := by
          rw [show 2 * (16 * s) = 32 * s by ring, pow_mul, mul_pow, mul_pow]
      _ ≤ (2 ^ 80) ^ s := Nat.pow_le_pow_left hconst s
      _ = 2 ^ (80 * s) := (pow_mul _ _ _).symm
  have h4 : 4 ^ (2 * (16 * s)) * 2 ^ (16 * s - 2) * 4 = 2 ^ (80 * s) := by
    rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul, mul_assoc, ← pow_add, ← pow_add]
    congr 1
    omega
  have h4pos : 0 < 4 ^ (2 * (16 * s)) := by positivity
  nlinarith

/-- **The relative distance of Justesen codes at rate at least `1 / 4`** [Justesen1972]. Let `s ≥ 1`
and let `F` be a field written as `b = 16 * s` bits, which then has `2 ^ (16 * s)` elements. The
Justesen code of outer dimension `K = 2 ^ (16 * s - 1)` is a binary code of length
`n = 32 * s * (2 ^ (16 * s) - 1)` whose minimum distance `d` satisfies `n ≤ 128 * d`. -/
theorem card_le_mul_minDist_justesenCode {s : ℕ} (hs : 1 ≤ s) (φ : F ≃+ BitString (16 * s)) :
    (Fintype.card (Fˣ × (Fin 2 × Fin (16 * s))) : ℕ∞) ≤
      128 * minDist (justesenCode φ (2 ^ (16 * s - 1))) := by
  have hq : Fintype.card F = 2 ^ (16 * s) := by
    rw [Fintype.card_congr φ.toEquiv, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hpow : 2 ^ (16 * s) = 2 * 2 ^ (16 * s - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hlen : Fintype.card (Fˣ × (Fin 2 × Fin (16 * s))) = 32 * s * (2 ^ (16 * s) - 1) := by
    rw [Fintype.card_prod, Fintype.card_units, hq, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    ring
  rw [hlen]
  have hball := sum_range_choose_two_mul_sixteen_mul_le hs
  have hquarter : 2 ^ (16 * s - 1) = 2 * 2 ^ (16 * s - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have hsub : 2 ^ (16 * s - 2) ≤
      Fintype.card F - 2 ^ (16 * s - 1) - ∑ j ∈ range (s + 1), (2 * (16 * s)).choose j := by
    omega
  have key : 32 * s * (2 ^ (16 * s) - 1) ≤ 128 * ((Fintype.card F - 2 ^ (16 * s - 1) -
      ∑ j ∈ range (s + 1), (2 * (16 * s)).choose j) * (s + 1)) :=
    calc 32 * s * (2 ^ (16 * s) - 1) ≤ 32 * s * 2 ^ (16 * s) :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 128 * (2 ^ (16 * s - 2) * s) := by rw [hpow, hquarter]; ring
      _ ≤ 128 * (2 ^ (16 * s - 2) * (s + 1)) := by gcongr; omega
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hsub)
  calc ((32 * s * (2 ^ (16 * s) - 1) : ℕ) : ℕ∞)
      ≤ ((128 * ((Fintype.card F - 2 ^ (16 * s - 1) -
          ∑ j ∈ range (s + 1), (2 * (16 * s)).choose j) * (s + 1)) : ℕ) : ℕ∞) :=
        Nat.cast_le.2 key
    _ = 128 * (((Fintype.card F - 2 ^ (16 * s - 1) -
          ∑ j ∈ range (s + 1), (2 * (16 * s)).choose j) * (s + 1) : ℕ) : ℕ∞) := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ 128 * minDist (justesenCode φ (2 ^ (16 * s - 1))) := by
        gcongr
        exact le_minDist_justesenCode φ _ s

/-- **Justesen codes are asymptotically good** [Justesen1972]. Given for each `s` a field `F s`
written as `16 * (s + 1)` bits through `φ s : F s ≃+ BitString (16 * (s + 1))`, the Justesen codes
`justesenCode (φ s) (2 ^ (16 * (s + 1) - 1))` form an asymptotically good family of binary codes:
their lengths `32 * (s + 1) * (2 ^ (16 * (s + 1)) - 1)` grow without bound, with rate at least
`1 / 4` and relative distance at least `1 / 128`. -/
theorem isAsymptoticallyGood_justesenCode
    {F : ℕ → Type*} [∀ s, Field (F s)] [∀ s, Fintype (F s)] [∀ s, DecidableEq (F s)]
    (φ : ∀ s, F s ≃+ BitString (16 * (s + 1))) :
    IsAsymptoticallyGood fun s => justesenCode (φ s) (2 ^ (16 * (s + 1) - 1)) where
  exists_le_card N := by
    refine ⟨N, ?_⟩
    have hq : Fintype.card (F N) = 2 ^ (16 * (N + 1)) := by
      rw [Fintype.card_congr (φ N).toEquiv, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [Fintype.card_prod, Fintype.card_units, hq, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    have hpow : 1 ≤ 2 ^ (16 * (N + 1)) - 1 := by
      have : 2 ≤ 2 ^ (16 * (N + 1)) :=
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (16 * (N + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc N ≤ 1 * (2 * (16 * (N + 1))) := by omega
      _ ≤ (2 ^ (16 * (N + 1)) - 1) * (2 * (16 * (N + 1))) := Nat.mul_le_mul_right _ hpow
  exists_rate := by
    refine ⟨4, by norm_num, fun s => ⟨16 * (s + 1) * 2 ^ (16 * (s + 1) - 1), ?_, ?_⟩⟩
    · have hq : Fintype.card (F s) = 2 ^ (16 * (s + 1)) := by
        rw [Fintype.card_congr (φ s).toEquiv, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin]
      have hpow : 2 ^ (16 * (s + 1)) = 2 * 2 ^ (16 * (s + 1) - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      rw [Fintype.card_prod, Fintype.card_units, hq, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, hpow]
      have := Nat.sub_le (2 * 2 ^ (16 * (s + 1) - 1)) 1
      nlinarith
    · have hq : Fintype.card (F s) = 2 ^ (16 * (s + 1)) := by
        rw [Fintype.card_congr (φ s).toEquiv, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin]
      have hpow : 2 ^ (16 * (s + 1)) = 2 * 2 ^ (16 * (s + 1) - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      have hK : 2 ^ (16 * (s + 1) - 1) ≤ Fintype.card (F s) - 1 := by
        have := Nat.one_le_two_pow (n := 16 * (s + 1) - 1)
        omega
      rw [Fintype.card_bool, card_justesenCode (φ s) hK]
  exists_minDist :=
    ⟨128, by norm_num, fun s => by
      simpa using card_le_mul_minDist_justesenCode (Nat.succ_pos s) (φ s)⟩

end Cslib.Code
