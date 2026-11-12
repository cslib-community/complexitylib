/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Smolensky.Approximation
public import CslibFrontier.Foundations.BooleanAnalysis.Mobius
public import CslibFrontier.Foundations.Data.BitString.Weight
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Rank
import CslibFrontier.Foundations.BooleanAnalysis.LowDegree.Addition
import CslibFrontier.Foundations.Combinatorics.CentralBinomial
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank

/-!
# Razborov's GF(2) rank property against AC⁰[2]

This module proves that a rank property of truth tables is large and useful against AC⁰[2], the
property that [Razborov and Rudich, §3.2, p. 27][RazborovRudich1997] extract from Razborov's lower
bound for constant-depth circuits with parity gates [Razborov1987].

The **zero-sum matrix** of `h : (ι → Bool) → ZMod 2` at level `a` (`zeroSumMatrix`) has rows and
columns indexed by the `a`-subsets of `ι`. Its entry at `(I, J)` is the coefficient of `h` at the
monomial of `(I ∪ J)ᶜ` (a subset Möbius transform, `BitString.subsetMobius`). Over `ZMod 2` that
coefficient is the sum of `h` over the points vanishing on `I ∪ J` (`zeroSumMatrix_apply`). Three
facts about the matrix drive the argument:

* a function of degree `D` with `D + 2 a < |ι|` has zero matrix, because `(I ∪ J)ᶜ` has more than
  `D` elements (`zeroSumMatrix_eq_zero_of_mem_lowDegree`);
* a function supported on `E` has matrix rank at most `#E`, because its matrix factors through
  `E` (`rank_zeroSumMatrix_le_card`);
* the indicator of the points with exactly `a` zeros has the identity matrix
  (`zeroSumMatrix_exactWeight`).

The **rank test** (`rankTest n a`) accepts a Boolean function `f` on `n` inputs when the rank of
the zero-sum matrix of `f` is at least `C(n, a) / 2`.

* **Usefulness.** Smolensky's approximation (`Smolensky.exists_lowDegree_approx`, over `ZMod 2`)
  writes a depth-`d` circuit as a polynomial of degree `ℓ ^ d` plus an error supported on at most
  `size · 2 ^ n / 2 ^ ℓ` inputs. When `ℓ ^ d + 2 a < n` the polynomial has zero matrix, so the rank
  of the circuit's matrix is at most the size of that support (`rank_mul_two_pow_le_size`).
* **Largeness.** The matrices of `f` and of `f` XOR the identity witness sum to the identity, so
  one of the two passes the test. That pairing is an involution, so the test accepts at least half
  of all functions, at every `n` and `a` (`two_pow_two_pow_le_two_mul_ncard_rankTest`).
* **Tradeoff.** At level `a = ⌈n/2⌉ - s` with `1 ≤ s` and `100 s² ≤ n + 1`, the coefficient
  `C(n, a)` is at least `4 · 2 ^ n / (5 (n + 1))` (`Cslib.four_mul_two_pow_le_mul_choose_sub`). So a
  depth-`d` AC⁰[2] circuit computing a function that passes the test has size at least
  `2 · 2 ^ ℓ / (5 (n + 1))` whenever `ℓ ^ d + 2 ≤ 2 s` (`two_mul_two_pow_le_size_of_mem_rankTest`).

The constructivity of the test, a circuit of size `173 · 8 ^ n` deciding it from truth tables, is
in `CslibFrontier.Computability.Circuit.Boolean.Razborov.Natural`.

**Sources and variant.** [Razborov and Rudich, §3.2, p. 27][RazborovRudich1997] state the rank
property only abstractly and leave its largeness as an exercise. The explicit form for `p = 2` is
the sketch in [Carmosino et al., p. 10:20][CarmosinoImpagliazzoKabanetsKolokolova2016], who
accept when some matrix of level `b ≤ a`,
`a = n/2 - √n`, has rank at least `2 ^ n / (140 n²)`. This module uses a variant: one square
matrix at a single level `a`, the threshold `C(n, a) / 2` (which makes largeness exactly `1/2`),
and the level `a = ⌈n/2⌉ - s`. Razborov's original paper [Razborov1987] was not checked for its
own form of the property.

## Main definitions

* `Cslib.Circuits.Boolean.Razborov.zeroSumMatrix`: the zero-sum matrix of a `ZMod 2`-valued
  function.
* `Cslib.Circuits.Boolean.Razborov.exactWeight`: the indicator of the points of a given weight.
* `Cslib.Circuits.Boolean.Razborov.rankTest`: the rank test at level `a`.

## Main results

* `Cslib.Circuits.Boolean.Razborov.zeroSumMatrix_apply`: entries as sums over subcubes.
* `Cslib.Circuits.Boolean.Razborov.zeroSumMatrix_eq_zero_of_mem_lowDegree`: low-degree functions
  have zero matrix.
* `Cslib.Circuits.Boolean.Razborov.rank_zeroSumMatrix_le_card`: rank at most the support size.
* `Cslib.Circuits.Boolean.Razborov.zeroSumMatrix_exactWeight`: the identity witness.
* `Cslib.Circuits.Boolean.Razborov.two_pow_two_pow_le_two_mul_ncard_rankTest`: largeness.
* `Cslib.Circuits.Boolean.Razborov.rank_mul_two_pow_le_size`: usefulness against AC⁰[2].
* `Cslib.Circuits.Boolean.Razborov.two_mul_two_pow_le_size_of_mem_rankTest`: the size–depth
  tradeoff for functions passing the test.

## References

* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
* [A. A. Razborov, S. Rudich, *Natural proofs*][RazborovRudich1997]
* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.Circuits.Boolean.Razborov

open Finset BitString

/-! ### The zero-sum matrix -/

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **zero-sum matrix** of `h` at level `a`: rows and columns are the `a`-subsets of `ι`, and
the entry at `(I, J)` is the subset Möbius transform of `h` at `(I ∪ J)ᶜ`, the coefficient of the
monomial of `(I ∪ J)ᶜ`. Over `ZMod 2` it is the sum of `h` over the points vanishing on `I ∪ J`
(`zeroSumMatrix_apply`). -/
noncomputable def zeroSumMatrix (a : ℕ) (h : (ι → Bool) → ZMod 2) :
    Matrix {I : Finset ι // #I = a} {I : Finset ι // #I = a} (ZMod 2) :=
  Matrix.of fun I J => subsetMobius (fun T => h fun i => decide (i ∈ T)) (I.1 ∪ J.1)ᶜ

/-- The entry of the zero-sum matrix at `(I, J)` is the subset Möbius transform at `(I ∪ J)ᶜ`. -/
theorem zeroSumMatrix_apply_eq_subsetMobius (a : ℕ) (h : (ι → Bool) → ZMod 2) (I J) :
    zeroSumMatrix a h I J = subsetMobius (fun T => h fun i => decide (i ∈ T)) (I.1 ∪ J.1)ᶜ := by
  rfl

/-- Over `ZMod 2`, the subset Möbius transform at `S` is the sum over the points vanishing off
`S`. -/
private theorem subsetMobius_eq_sum (h : (ι → Bool) → ZMod 2) (S : Finset ι) :
    subsetMobius (fun T => h fun i => decide (i ∈ T)) S = ∑ x with ∀ i ∉ S, x i = false, h x := by
  rw [subsetMobius]
  refine sum_nbij' (fun T i => decide (i ∈ T)) (fun x => univ.filter fun i => x i = true)
    ?_ ?_ ?_ ?_ ?_
  · intro T hT
    rw [mem_powerset] at hT
    exact mem_filter.mpr ⟨mem_univ _, fun i hi => decide_eq_false fun hiT => hi (hT hiT)⟩
  · intro x hx
    refine mem_powerset.mpr fun i hi => ?_
    by_contra hiS
    have hxi := (mem_filter.mp hi).2
    rw [(mem_filter.mp hx).2 i hiS] at hxi
    exact Bool.false_ne_true hxi
  · intro T _
    ext i
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq]
  · intro x _
    funext i
    simp only [mem_filter, mem_univ, true_and, Bool.decide_eq_true]
  · intro T _
    rw [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, CharTwo.neg_one_eq_one, one_pow,
      one_mul]

/-- **The entries of the zero-sum matrix** over `ZMod 2`: the entry at `(I, J)` is the sum of `h`
over the points vanishing on `I ∪ J`. -/
theorem zeroSumMatrix_apply (a : ℕ) (h : (ι → Bool) → ZMod 2) (I J) :
    zeroSumMatrix a h I J = ∑ x with ∀ i ∈ I.1 ∪ J.1, x i = false, h x := by
  rw [zeroSumMatrix_apply_eq_subsetMobius, subsetMobius_eq_sum]
  simp only [mem_compl, not_not]

/-- The zero-sum matrix is additive. -/
theorem zeroSumMatrix_add (a : ℕ) (g h : (ι → Bool) → ZMod 2) :
    zeroSumMatrix a (g + h) = zeroSumMatrix a g + zeroSumMatrix a h := by
  ext I J
  simp only [zeroSumMatrix_apply, Pi.add_apply, Matrix.add_apply, sum_add_distrib]

/-- The zero-sum matrix commutes with subtraction. -/
theorem zeroSumMatrix_sub (a : ℕ) (g h : (ι → Bool) → ZMod 2) :
    zeroSumMatrix a (g - h) = zeroSumMatrix a g - zeroSumMatrix a h := by
  ext I J
  simp only [zeroSumMatrix_apply, Pi.sub_apply, Matrix.sub_apply, sum_sub_distrib]

/-- **Low-degree functions have zero matrix**: if `h` has degree at most `D` and
`D + 2 a < |ι|`, then the complement of the union of two `a`-sets has more than `D` elements, so
every entry of the zero-sum matrix of `h` is a vanishing coefficient. -/
theorem zeroSumMatrix_eq_zero_of_mem_lowDegree {a D : ℕ} {h : (ι → Bool) → ZMod 2}
    (hh : h ∈ lowDegree (ZMod 2) ι D) (hD : D + 2 * a < Fintype.card ι) :
    zeroSumMatrix a h = 0 := by
  ext I J
  rw [zeroSumMatrix_apply_eq_subsetMobius, Matrix.zero_apply]
  refine subsetMobius_eq_zero_of_mem_lowDegree hh ?_
  have hIJ : #(I.1 ∪ J.1) ≤ 2 * a := (card_union_le _ _).trans (by rw [I.2, J.2, two_mul])
  rw [card_compl]
  omega

/-- **The rank of the zero-sum matrix is at most the support size**: if `h` vanishes off `E`, the
matrix of `h` is the product of the `a`-sets-by-`E` incidence matrix `[I ⊆ zeros x]` with a matrix
with `#E` rows, so its rank is at most `#E`. -/
theorem rank_zeroSumMatrix_le_card {a : ℕ} {h : (ι → Bool) → ZMod 2} {E : Finset (ι → Bool)}
    (hE : ∀ x ∉ E, h x = 0) : (zeroSumMatrix a h).rank ≤ #E := by
  let U : Matrix {I : Finset ι // #I = a} E (ZMod 2) :=
    Matrix.of fun I x => if ∀ i ∈ I.1, x.1 i = false then 1 else 0
  let V : Matrix E {I : Finset ι // #I = a} (ZMod 2) :=
    Matrix.of fun x J => if ∀ i ∈ J.1, x.1 i = false then h x.1 else 0
  have hUV : zeroSumMatrix a h = U * V := by
    ext I J
    have hterm : ∀ x : E, U I x * V x J =
        if ∀ i ∈ I.1 ∪ J.1, x.1 i = false then h x.1 else 0 := by
      intro x
      simp only [U, V, Matrix.of_apply, forall_mem_union]
      split_ifs <;> simp_all
    rw [zeroSumMatrix_apply, Matrix.mul_apply, sum_filter, Fintype.sum_congr _ _ hterm,
      sum_coe_sort E fun x => if ∀ i ∈ I.1 ∪ J.1, x i = false then h x else 0]
    exact (sum_subset (subset_univ E) fun x _ hx => by rw [hE x hx, ite_self]).symm
  rw [hUV]
  exact (Matrix.rank_mul_le_left U V).trans ((Matrix.rank_le_card_width U).trans_eq
    (Fintype.card_coe E))

/-- The indicator of the points of weight `k`: `exactWeight k x` holds when `x` has exactly `k`
true coordinates. -/
def exactWeight (k : ℕ) (x : ι → Bool) : Bool :=
  decide (weight x = k)

omit [DecidableEq ι] in
/-- `exactWeight k x` holds exactly when `x` has weight `k`. -/
@[simp] theorem exactWeight_eq_true_iff {k : ℕ} {x : ι → Bool} :
    exactWeight k x = true ↔ weight x = k :=
  decide_eq_true_iff

/-- **The identity witness**: the zero-sum matrix at level `a` of the indicator of the points with
exactly `a` zeros (weight `|ι| - a`) is the identity. A point vanishing on `I ∪ J` with exactly
`a` zeros has zero set `I = J`, and for `I = J` there is exactly one such point. -/
theorem zeroSumMatrix_exactWeight (a : ℕ) :
    zeroSumMatrix (ι := ι) a (fun x => bitVal (ZMod 2) (exactWeight (Fintype.card ι - a) x)) =
      1 := by
  ext I J
  rw [zeroSumMatrix_apply]
  -- the points vanishing on `I ∪ J` with exactly `a` zeros
  have key : ∀ x : ι → Bool, ((∀ i ∈ I.1 ∪ J.1, x i = false) ∧
      weight x = Fintype.card ι - a) ↔ I = J ∧ x = fun i => decide (i ∉ I.1) := by
    intro x
    constructor
    · rintro ⟨hx, hw⟩
      set S := univ.filter fun i => x i = false
      have hSw : #S = Fintype.card ι - weight x := card_filter_eq_false_eq_card_sub_weight x
      have hwle : weight x ≤ Fintype.card ι := weight_le x
      have haI : a ≤ Fintype.card ι := I.2 ▸ card_le_univ I.1
      have hS : #S = a := by omega
      have hIS : I.1 ⊆ S := fun i hi => mem_filter.mpr ⟨mem_univ i, hx i (mem_union_left _ hi)⟩
      have hJS : J.1 ⊆ S := fun i hi => mem_filter.mpr ⟨mem_univ i, hx i (mem_union_right _ hi)⟩
      have hI : I.1 = S := eq_of_subset_of_card_le hIS (by rw [hS, I.2])
      have hJ : J.1 = S := eq_of_subset_of_card_le hJS (by rw [hS, J.2])
      refine ⟨Subtype.ext (hI.trans hJ.symm), funext fun i => ?_⟩
      rw [hI]
      cases hxi : x i <;> simp [S, hxi]
    · rintro ⟨rfl, rfl⟩
      refine ⟨fun i hi => by simpa only [decide_eq_false_iff_not, not_not, union_self] using hi,
        ?_⟩
      have hfalse : (univ.filter fun i => decide (i ∉ I.1) = false) = I.1 := by
        ext i
        simp only [mem_filter, mem_univ, true_and, decide_eq_false_iff_not, not_not]
      have h1 := card_filter_eq_false_eq_card_sub_weight fun i => decide (i ∉ I.1)
      have h2 := weight_le fun i => decide (i ∉ I.1)
      rw [hfalse, I.2] at h1
      omega
  by_cases hIJ : I = J
  · subst hIJ
    rw [Matrix.one_apply_eq]
    refine (sum_eq_single_of_mem (fun i => decide (i ∉ I.1)) ?_ fun x hx hne => ?_).trans ?_
    · rw [mem_filter]
      exact ⟨mem_univ _, ((key _).mpr ⟨rfl, rfl⟩).1⟩
    · rw [mem_filter] at hx
      have hw : weight x ≠ Fintype.card ι - a := fun hw => hne ((key x).mp ⟨hx.2, hw⟩).2
      rw [show exactWeight (Fintype.card ι - a) x = false from
        decide_eq_false hw, bitVal_false]
    · rw [show exactWeight (Fintype.card ι - a) (fun i => decide (i ∉ I.1)) = true from
        exactWeight_eq_true_iff.mpr ((key _).mpr ⟨rfl, rfl⟩).2, bitVal_true]
  · rw [Matrix.one_apply_ne hIJ]
    refine sum_eq_zero fun x hx => ?_
    rw [mem_filter] at hx
    have hw : weight x ≠ Fintype.card ι - a := fun hw => hIJ ((key x).mp ⟨hx.2, hw⟩).1
    rw [show exactWeight (Fintype.card ι - a) x = false from decide_eq_false hw, bitVal_false]

end Matrix

/-! ### The rank test -/

variable {n : ℕ}

/-- The **rank test** at level `a`: a Boolean function `f` on `n` inputs passes when the zero-sum
matrix of `f` (read in `ZMod 2`) has rank at least `C(n, a) / 2`. This is a variant of the rank
property of [Razborov and Rudich, §3.2][RazborovRudich1997] with one square matrix and the
threshold `C(n, a) / 2`; see the module docstring. -/
def rankTest (n a : ℕ) : Set (BooleanFunction n) :=
  {f | n.choose a ≤ 2 * (zeroSumMatrix a fun x => bitVal (ZMod 2) (f x)).rank}

/-- Membership in the rank test. -/
theorem mem_rankTest {a : ℕ} {f : BooleanFunction n} :
    f ∈ rankTest n a ↔ n.choose a ≤ 2 * (zeroSumMatrix a fun x => bitVal (ZMod 2) (f x)).rank :=
  Iff.rfl

/-- The identity matrix of the `a`-subsets of `Fin n` has rank `C(n, a)`. -/
private theorem rank_one_finsetLen (a : ℕ) :
    (1 : Matrix {I : Finset (Fin n) // #I = a} {I : Finset (Fin n) // #I = a} (ZMod 2)).rank =
      n.choose a := by
  rw [Matrix.rank_one, Fintype.card_finset_len, Fintype.card_fin]

/-- The indicator of the points with exactly `a` zeros passes the rank test at level `a`: its
zero-sum matrix is the identity, of full rank `C(n, a)`. -/
theorem exactWeight_mem_rankTest (a : ℕ) : exactWeight (n - a) ∈ rankTest n a := by
  rw [mem_rankTest]
  have h := zeroSumMatrix_exactWeight (ι := Fin n) a
  rw [Fintype.card_fin] at h
  rw [h, rank_one_finsetLen]
  omega

/-- **Largeness of the rank test**: at every `n` and `a`, at least half of the Boolean functions on
`n` inputs pass the rank test at level `a`. The zero-sum matrices of `f` and of `f` XOR the
identity witness `exactWeight (n - a)` sum to the identity, so one of the two has rank at least
`C(n, a) / 2`, and XOR with a fixed function is an involution. -/
theorem two_pow_two_pow_le_two_mul_ncard_rankTest (n a : ℕ) :
    2 ^ 2 ^ n ≤ 2 * (rankTest n a).ncard := by
  set g : BooleanFunction n := exactWeight (n - a)
  set φ : BooleanFunction n → BooleanFunction n := fun f x => f x ^^ g x
  have hφ : Function.Involutive φ := fun f => funext fun x => by
    simp only [φ, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  -- every function or its partner passes
  have hcover : ∀ f, f ∈ rankTest n a ∨ φ f ∈ rankTest n a := by
    intro f
    have hsum : (zeroSumMatrix a fun x => bitVal (ZMod 2) (f x)) +
        (zeroSumMatrix a fun x => bitVal (ZMod 2) (φ f x)) = 1 := by
      have h := zeroSumMatrix_exactWeight (ι := Fin n) a
      rw [Fintype.card_fin] at h
      rw [← zeroSumMatrix_add, ← h]
      congr 1
      funext x
      simp only [φ, g, Pi.add_apply, bitVal_xor_of_char_two, ← add_assoc,
        CharTwo.add_self_eq_zero, zero_add]
    have hle := Matrix.rank_add_le (zeroSumMatrix a fun x => bitVal (ZMod 2) (f x))
      (zeroSumMatrix a fun x => bitVal (ZMod 2) (φ f x))
    rw [hsum, rank_one_finsetLen] at hle
    simp only [mem_rankTest]
    omega
  have huniv : (Set.univ : Set (BooleanFunction n)) ⊆ rankTest n a ∪ φ ⁻¹' rankTest n a :=
    fun f _ => hcover f
  have hpre : (φ ⁻¹' rankTest n a).ncard = (rankTest n a).ncard := by
    rw [← hφ.image_eq_preimage_symm, Set.ncard_image_of_injective _ hφ.injective]
  have hcard := (Set.ncard_le_ncard huniv (Set.toFinite _)).trans (Set.ncard_union_le _ _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, hpre] at hcard
  omega

/-- **Usefulness of the rank test against AC⁰[2]**: if a circuit of the AC⁰[2] basis of depth `d`
computes `f`, then for every `ℓ ≥ 1` with `ℓ ^ d + 2 a < n`, the zero-sum matrix of `f` at level
`a` has rank at most `size · 2 ^ n / 2 ^ ℓ`. Smolensky's approximation over `ZMod 2` gives a
polynomial of degree `ℓ ^ d`, which has zero matrix, agreeing with `f` off at most
`size · 2 ^ n / 2 ^ ℓ` inputs. -/
theorem rank_mul_two_pow_le_size {f : BooleanFunction n} {C : Circuit Unbounded.extSignature n 1}
    (hC : C.Computes (Unbounded.extInterpretation (modGate 2)) (single f)) {ℓ a : ℕ} (hℓ : 1 ≤ ℓ)
    (hd : ℓ ^ C.depth + 2 * a < n) :
    (zeroSumMatrix a fun x => bitVal (ZMod 2) (f x)).rank * 2 ^ ℓ ≤ C.size * 2 ^ n := by
  classical
  obtain ⟨Q, hQ, herr⟩ := Smolensky.exists_lowDegree_approx (R := ZMod 2) (p := 2) hℓ C
  rw [show (2 - 1) * ℓ = ℓ by omega] at hQ
  have heval : ∀ x, C.eval (Unbounded.extInterpretation (modGate 2)) x 0 = f x := fun x =>
    congrFun (hC x) 0
  simp only [heval] at herr
  set E := univ.filter fun x => Q x ≠ bitVal (ZMod 2) (f x)
  have hkill : zeroSumMatrix a Q = 0 :=
    zeroSumMatrix_eq_zero_of_mem_lowDegree hQ (by rwa [Fintype.card_fin])
  have hrank : (zeroSumMatrix a fun x => bitVal (ZMod 2) (f x)).rank ≤ #E := by
    have h := zeroSumMatrix_sub a (fun x => bitVal (ZMod 2) (f x)) Q
    rw [hkill, sub_zero] at h
    rw [← h]
    refine rank_zeroSumMatrix_le_card fun x hx => ?_
    simp only [E, mem_filter, mem_univ, true_and, not_not] at hx
    rw [Pi.sub_apply, hx, sub_self]
  exact (Nat.mul_le_mul_right _ hrank).trans herr

/-- **The size–depth tradeoff for the rank test**: let `1 ≤ s` and `100 s² ≤ n + 1`. If `f` passes
the rank test at level `⌈n/2⌉ - s` and a circuit of the AC⁰[2] basis of depth `d` computes `f`,
then its size is at least `2 · 2 ^ ℓ / (5 (n + 1))` for every `ℓ ≥ 1` with `ℓ ^ d + 2 ≤ 2 s`. -/
theorem two_mul_two_pow_le_size_of_mem_rankTest {f : BooleanFunction n} {s : ℕ}
    (hs : 1 ≤ s) (h : 100 * s ^ 2 ≤ n + 1) (hf : f ∈ rankTest n ((n + 1) / 2 - s))
    {C : Circuit Unbounded.extSignature n 1}
    (hC : C.Computes (Unbounded.extInterpretation (modGate 2)) (single f)) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hd : ℓ ^ C.depth + 2 ≤ 2 * s) : 2 * 2 ^ ℓ ≤ 5 * (n + 1) * C.size := by
  set a := (n + 1) / 2 - s with ha_def
  have hs2 : s ≤ s ^ 2 := Nat.le_self_pow two_ne_zero s
  set r := (zeroSumMatrix a fun x => bitVal (ZMod 2) (f x)).rank
  have hr : r * 2 ^ ℓ ≤ C.size * 2 ^ n := rank_mul_two_pow_le_size hC hℓ (by omega)
  have hb := four_mul_two_pow_le_mul_choose_sub hs h
  rw [← ha_def] at hb
  have hf' : n.choose a ≤ 2 * r := mem_rankTest.mp hf
  -- `2 · 2 ^ n · 2 · 2 ^ ℓ ≤ 5 (n + 1) C(n, a) 2 ^ ℓ ≤ 10 (n + 1) r 2 ^ ℓ ≤ 10 (n + 1) size 2 ^ n`
  have key : 2 * 2 ^ n * (2 * 2 ^ ℓ) ≤ 2 * 2 ^ n * (5 * (n + 1) * C.size) := by
    calc 2 * 2 ^ n * (2 * 2 ^ ℓ) = 4 * 2 ^ n * 2 ^ ℓ := by ring
      _ ≤ 5 * (n + 1) * n.choose a * 2 ^ ℓ := Nat.mul_le_mul_right _ hb
      _ ≤ 5 * (n + 1) * (2 * r) * 2 ^ ℓ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hf')
      _ = 2 * (5 * (n + 1)) * (r * 2 ^ ℓ) := by ring
      _ ≤ 2 * (5 * (n + 1)) * (C.size * 2 ^ n) := Nat.mul_le_mul_left _ hr
      _ = 2 * 2 ^ n * (5 * (n + 1) * C.size) := by ring
  exact Nat.le_of_mul_le_mul_left key (by positivity)

end Cslib.Circuits.Boolean.Razborov
