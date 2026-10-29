/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Synthesis
public import Complexity.Foundations.Data.BitString.Convolution
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Complexity.Computability.Circuit.Synthesis
import Complexity.Foundations.Combinatorics.Additive.SumsetCover
import Complexity.Foundations.Combinatorics.SmallSubsets
import Mathlib.Tactic.Ring

/-!
# Circuits for existential convolution

Small translate covers yield small circuits for sumset membership. All input negations are
computed once, after which translating a Boolean circuit by a fixed bit string only rewires
its inputs. The finite disjunction then costs one gate per term and an initial constant.

Applying Ellenberg's sumset cover [Ellenberg2017Sumsets, Theorem 1] gives the exact nonuniform
bound `n + 3 M (max(C(f), C(g)) + 1) + 1` for existential XOR convolution, where
`M = ∑_{j ≤ ⌊n/3⌋} binom(n,j)`. No degree restriction is imposed on the input functions.
Gate counts use the De Morgan basis, counting constants and negations as well as binary gates.
The exact integer inequality for the cube of the circuit-size excess certifies the exponential
base `(27/4)^(1/3) = 2^(H₂(1/3))`, approximately `1.88988`, without rounding an exponent.

## Main results

* `Cslib.Circuits.Boolean.complexity_exists_translate_le`: compile any finite disjunction of
  translated functions, sharing the input negations across all terms.
* `Cslib.Circuits.Boolean.complexity_sumset_le_of_cover`: compile any two-sided translate cover
  into a circuit for sumset membership.
* `Cslib.Circuits.Boolean.complexity_orConvolution_le`: the binomial-sum circuit bound for
  arbitrary Boolean functions.
* `Cslib.Circuits.Boolean.exists_orConvolution_circuit`: an exact circuit attaining that bound.
* `Cslib.Circuits.Boolean.complexity_orConvolution_sub_pow_three_mul_four_pow_le`: the exact
  exponential improvement, stated using integer powers.

## References

* [J. S. Ellenberg, *Sumsets as unions of sumsets of subsets*][Ellenberg2017Sumsets],
  arXiv:1612.01929v2, Theorem 1, pp. 1–2; the circuit compilation is a corollary proved here.
-/

public section

namespace Cslib.Circuits.Boolean

open Finset
open scoped Pointwise

variable {n : ℕ}

/-- A finite disjunction of translated functions pays for the input negations only once.
Each term uses a circuit for its function, with free rewiring of the translated inputs. -/
theorem complexity_exists_translate_le {α : Type*}
    (s : Finset α) (f : α → BooleanFunction n) (shift : α → BitString n) :
    complexity interpretation (single fun x =>
      decide (∃ i ∈ s, f i (x + shift i) = true)) ≤
      n + (∑ i ∈ s, (complexity interpretation (single (f i)) + 1)) + 1 := by
  classical
  let negated : Set (BooleanFunction n) := Set.range fun i (x : BitString n) => !x i
  have hneg : Synthesis interpretation (inputs n) negated n := by
    have h := Synthesis.family (fun i (x : BitString n) => !x i) (fun _ : Fin n => 1)
      fun i => (Synthesis.of_mem (s := inputs n) ⟨i, rfl⟩).not
    simpa [negated] using h
  have hterm (i : α) : Synthesis interpretation (inputs n ∪ negated)
      {fun x => f i (x + shift i)} (complexity interpretation (single (f i))) := by
    obtain ⟨c, hc, hsize⟩ :=
      exists_computes_size_eq_complexity (I := interpretation) (f := single (f i))
    have hinputs (j : Fin n) : (fun x : BitString n => (x + shift i) j) ∈ inputs n ∪ negated := by
      cases hbit : shift i j
      · left
        refine ⟨j, funext fun x => ?_⟩
        change x j = (x j ^^ shift i j)
        rw [hbit, Bool.xor_false]
      · right
        refine ⟨j, funext fun x => ?_⟩
        change (!x j) = (x j ^^ shift i j)
        rw [hbit, Bool.xor_true]
    have h := Synthesis.circuit (I := interpretation) c
      (fun j (x : BitString n) => (x + shift i) j) hinputs
    have heval (y : BitString n) (j : Fin 1) : c.eval interpretation y j = f i y :=
      congrFun (hc y) j
    simpa only [heval, Set.range_const, hsize] using h
  have h := hneg.trans (Synthesis.exists_mem s (fun i x => f i (x + shift i))
    (fun i => complexity interpretation (single (f i))) fun i _ => hterm i)
  simpa only [Nat.add_assoc] using h.complexity_le

/-- If every sum is covered by a translate whose left endpoint lies in `A₀` or whose right
endpoint lies in `B₀`, compile that cover. The sets and their cover may be selected nonuniformly;
the conclusion concerns the size of an exact circuit. -/
theorem complexity_sumset_le_of_cover (A B A₀ B₀ : Finset (BitString n))
    (hcover : A + B = (A₀ + B) ∪ (A + B₀)) :
    complexity interpretation (single fun x => decide (x ∈ A + B)) ≤
      n + A₀.card * (complexity interpretation (single fun x => decide (x ∈ B)) + 1) +
        B₀.card * (complexity interpretation (single fun x => decide (x ∈ A)) + 1) + 1 := by
  classical
  let family : BitString n ⊕ BitString n → BooleanFunction n :=
    Sum.elim (fun _ x => decide (x ∈ B)) (fun _ x => decide (x ∈ A))
  let shift : BitString n ⊕ BitString n → BitString n := Sum.elim id id
  have heq : (fun x => decide (∃ i ∈ A₀.disjSum B₀, family i (x + shift i) = true)) =
      fun x => decide (x ∈ A + B) := by
    funext x
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, hcover, mem_union]
    simp only [Sum.exists, inl_mem_disjSum, inr_mem_disjSum, family, shift, Sum.elim_inl,
      Sum.elim_inr, id_eq, decide_eq_true_iff]
    constructor
    · rintro (⟨a, ha, hb⟩ | ⟨b, hb, ha⟩)
      · exact Or.inl (mem_add.2
          ⟨a, ha, x + a, hb, by rw [add_left_comm, BitString.add_self, add_zero]⟩)
      · exact Or.inr (mem_add.2 ⟨x + b, ha, b, hb, by simp⟩)
    · rintro (hx | hx)
      · obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
        exact Or.inl ⟨a, ha, by rwa [add_right_comm, BitString.add_self, zero_add]⟩
      · obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
        exact Or.inr ⟨b, hb, by simpa using ha⟩
  have h := complexity_exists_translate_le (A₀.disjSum B₀) family shift
  rw [heq, sum_disjSum] at h
  simpa only [family, Sum.elim_inl, Sum.elim_inr, sum_const, smul_eq_mul, Nat.add_assoc]
    using h

/-- **Nontrivial exact convolution circuits.** For arbitrary Boolean functions `f` and `g`,
their existential XOR convolution has a De Morgan circuit within the binomial-sum bound.
The circuit and representative sets may depend on the full truth tables; this is a nonuniform
size bound, not a uniform algorithm for constructing the circuit. -/
theorem complexity_orConvolution_le (f g : BooleanFunction n) :
    complexity interpretation (single (BitString.orConvolution f g)) ≤
      n + 3 * (∑ j ∈ range (n / 3 + 1), n.choose j) *
        (max (complexity interpretation (single f)) (complexity interpretation (single g)) + 1) +
        1 := by
  classical
  let A := univ.filter fun x : BitString n => f x = true
  let B := univ.filter fun x : BitString n => g x = true
  have hf : (fun x => decide (x ∈ A)) = f := by
    funext x
    simp [A]
  have hg : (fun x => decide (x ∈ B)) = g := by
    funext x
    simp [B]
  have hfg : (fun x => decide (x ∈ A + B)) = BitString.orConvolution f g := by
    funext x
    rw [Bool.eq_iff_iff, decide_eq_true_iff, BitString.orConvolution_eq_true_iff_exists_add]
    simp only [mem_add, A, B, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨a, b, ha, hb, hab⟩
    · rintro ⟨a, b, ha, hb, hab⟩
      exact ⟨a, ha, b, hb, hab⟩
  obtain ⟨A₀, B₀, -, -, hcover, hcard⟩ := BitString.exists_add_cover A B
  have h := complexity_sumset_le_of_cover A B A₀ B₀ hcover
  rw [hfg, hf, hg] at h
  have hcard' : A₀.card + B₀.card ≤ 3 * ∑ j ∈ range (n / 3 + 1), n.choose j := by
    simpa only [Finset.card_filter_card_le_eq_sum_choose, Fintype.card_fin] using hcard
  have hleft := Nat.mul_le_mul_left A₀.card (Nat.add_le_add_right
    (le_max_right (complexity interpretation (single f)) (complexity interpretation (single g))) 1)
  have hright := Nat.mul_le_mul_left B₀.card (Nat.add_le_add_right
    (le_max_left (complexity interpretation (single f)) (complexity interpretation (single g))) 1)
  calc
    _ ≤ n + A₀.card * (complexity interpretation (single g) + 1) +
        B₀.card * (complexity interpretation (single f) + 1) + 1 := h
    _ ≤ n + (A₀.card + B₀.card) *
        (max (complexity interpretation (single f)) (complexity interpretation (single g)) + 1) +
        1 := by
      rw [add_mul]
      omega
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ hcard') n) 1

/-- There is an actual fan-in-two circuit computing existential convolution within the
binomial-sum bound. All gates, including constants and input negations, are counted. -/
theorem exists_orConvolution_circuit (f g : BooleanFunction n) :
    ∃ c : Circuit signature n 1,
      c.Computes interpretation (single (BitString.orConvolution f g)) ∧
      c.size ≤ n + 3 * (∑ j ∈ range (n / 3 + 1), n.choose j) *
        (max (complexity interpretation (single f)) (complexity interpretation (single g)) + 1) +
        1 :=
  complexity_le_iff.mp (complexity_orConvolution_le f g)

/-- **The exponential base is below two.** Cubing the circuit-size excess beyond `n + 1`
gives an exact integer bound with factor `(27/4)^n`. Thus the original excess is at most
`3 (max(C(f), C(g)) + 1) (27/4)^(n/3)` over the reals, whose exponential base is approximately
`1.88988`. The natural-number subtraction also covers circuits smaller than `n + 1`. -/
theorem complexity_orConvolution_sub_pow_three_mul_four_pow_le (f g : BooleanFunction n) :
    (complexity interpretation (single (BitString.orConvolution f g)) - (n + 1)) ^ 3 * 4 ^ n ≤
      27 ^ n *
        (3 * (max (complexity interpretation (single f))
          (complexity interpretation (single g)) + 1)) ^ 3 := by
  have hsize : complexity interpretation (single (BitString.orConvolution f g)) - (n + 1) ≤
      3 * (∑ j ∈ range (n / 3 + 1), n.choose j) *
        (max (complexity interpretation (single f))
          (complexity interpretation (single g)) + 1) := by
    have h := complexity_orConvolution_le f g
    omega
  have hcount : (∑ j ∈ range (n / 3 + 1), n.choose j) ^ 3 * 4 ^ n ≤ 27 ^ n := by
    have h := card_filter_card_le_third_pow_three_mul_four_pow_le (univ : Finset (Fin n))
    simpa only [card_univ, Fintype.card_fin, powerset_univ,
      Finset.card_filter_card_le_eq_sum_choose] using h
  calc
    _ ≤ (3 * (∑ j ∈ range (n / 3 + 1), n.choose j) *
        (max (complexity interpretation (single f)) (complexity interpretation (single g)) + 1)) ^
          3 * 4 ^ n := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hsize 3)
    _ = ((∑ j ∈ range (n / 3 + 1), n.choose j) ^ 3 * 4 ^ n) *
        (3 * (max (complexity interpretation (single f))
          (complexity interpretation (single g)) + 1)) ^ 3 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hcount

end Cslib.Circuits.Boolean
