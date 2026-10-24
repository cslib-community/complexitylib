/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Classes.ZPP
public import Complexity.Foundations.Order.BooleanSubalgebra
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Complexity.Reduction.ManyOne
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Closure properties of RP, coRP and ZPP

`RP` (`Cslib.Complexity.RP`) is closed under union and intersection, and so are `coRP` and
`ZPP = RP ∩ coRP` [Arora and Barak, Section 7.3][AroraBarak09]. Both constructions run one-sided
error deciders for the two problems on disjoint parts of the random string.

* **Union.** Accept when either decider accepts (`Cslib.Complexity.orVerifier`). On a member of
  one of the problems, its decider rejects at most half of its random strings, so the combined
  decider rejects at most half of all random strings
  (`Cslib.Complexity.acceptCount_orVerifier`); on a non-member of both, neither decider accepts.
* **Intersection.** Accept when both deciders accept (`Cslib.Complexity.andVerifier`). Error
  reduction makes each decider reject at most a quarter of the random strings on a member, so
  the combined decider accepts at least `(3 / 4) ^ 2 ≥ 1 / 2` of them on a common member
  (`Cslib.Complexity.acceptCount_andVerifier`); on a non-member of either, one of them rejects.

A decider ignoring an empty random string shows `P ⊆ RP`; with closure of `P` under complement
(`Cslib.Complexity.compl_mem_P`), `P ⊆ coRP` and `P ⊆ ZPP`. Since `RP ⊆ NP`, `ZPP ⊆ NP ∩ coNP`.

## Main results

* `Cslib.Complexity.P_subset_RP`, `Cslib.Complexity.P_subset_coRP`,
  `Cslib.Complexity.P_subset_ZPP`.
* `Cslib.Complexity.union_mem_RP`, `Cslib.Complexity.inter_mem_RP`: `RP` is closed under union
  and intersection.
* `Cslib.Complexity.union_mem_coRP`, `Cslib.Complexity.inter_mem_coRP`,
  `Cslib.Complexity.union_mem_ZPP`, `Cslib.Complexity.inter_mem_ZPP`,
  `Cslib.Complexity.diff_mem_ZPP`, `Cslib.Complexity.symmDiff_mem_ZPP`,
  `Cslib.Complexity.ZPP.booleanSubalgebra`.
* `Cslib.Complexity.ZPP_subset_NP_inter_coNP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-! ### Inclusions of `P` -/

/-- **`P ⊆ RP`**: a decider is a one-sided-error decider ignoring its random string, of
length `0`. -/
theorem P_subset_RP : P enc ⊆ RP enc := by
  rintro A ⟨f, hf, hA⟩
  refine ⟨0, fun x => f x.1, hf.comp (.fst enc encBits),
    fun a => ⟨fun ha => ?_, fun ha r => ?_⟩⟩
  · simp [(hA a).mp ha]
  · simpa [hA a] using ha

/-- **`P ⊆ coRP`**: `P` is closed under complement. -/
theorem P_subset_coRP : P enc ⊆ coRP enc := fun _ hA => P_subset_RP (compl_mem_P hA)

/-- **`P ⊆ ZPP`**, since `ZPP = RP ∩ coRP`. -/
theorem P_subset_ZPP : P enc ⊆ ZPP enc := fun _ hA => by
  rw [ZPP_eq_RP_inter_coRP]
  exact ⟨P_subset_RP hA, P_subset_coRP hA⟩

/-- **`ZPP ⊆ NP ∩ coNP`.** -/
theorem ZPP_subset_NP_inter_coNP : ZPP enc ⊆ NP enc ∩ coNP enc := fun _ hA =>
  ⟨RP_subset_NP (ZPP_subset_RP hA), coRP_subset_coNP (ZPP_subset_coRP hA)⟩

/-! ### Union and intersection -/

/-- **`RP` is closed under union**: accept when the decider for either problem accepts, on
disjoint parts of the random string. -/
theorem union_mem_RP {A B : Set α} (hA : A ∈ RP enc) (hB : B ∈ RP enc) : A ∪ B ∈ RP enc := by
  obtain ⟨p₁, V₁, hV₁, h₁⟩ := mem_RP.mp hA
  obtain ⟨p₂, V₂, hV₂, h₂⟩ := mem_RP.mp hB
  refine ⟨p₁ + p₂, orVerifier (fun a => p₁.eval (enc a).length) V₁ V₂, by fun_prop,
    fun a => ⟨fun ha => ?_, fun ha r => ?_⟩⟩
  · change 2 ^ (p₁ + p₂).eval (enc a).length ≤
      2 * acceptCount _ a ((p₁ + p₂).eval (enc a).length)
    rw [Polynomial.eval_add]
    generalize hk₁ : p₁.eval (enc a).length = k₁
    generalize hk₂ : p₂.eval (enc a).length = k₂
    have hc := acceptCount_orVerifier (fun a => p₁.eval (enc a).length) V₁ V₂ a k₂
    simp only [hk₁] at hc ⊢
    have n₁ := acceptCount_add_acceptCount_not V₁ a k₁
    have n₂ := acceptCount_add_acceptCount_not V₂ a k₂
    -- the rejected strings make up at most half of all strings
    have hprod : 2 * (acceptCount (fun x => !V₁ x) a k₁ * acceptCount (fun x => !V₂ x) a k₂) ≤
        2 ^ (k₁ + k₂) := by
      rw [pow_add]
      rcases ha with ha | ha
      · have h : 2 ^ k₁ ≤ 2 * acceptCount V₁ a k₁ := hk₁ ▸ (h₁ a).1 ha
        rw [← mul_assoc]
        exact Nat.mul_le_mul (by omega) (by omega)
      · have h : 2 ^ k₂ ≤ 2 * acceptCount V₂ a k₂ := hk₂ ▸ (h₂ a).1 ha
        rw [Nat.mul_left_comm]
        exact Nat.mul_le_mul (by omega) (by omega)
    omega
  · simp only [Set.mem_union, not_or] at ha
    simp only [orVerifier, Bool.or_eq_false_iff]
    refine ⟨Bool.not_eq_true _ ▸ fun hc => ha.1 ((h₁.isVerifier a).2 ⟨_, ?_, hc⟩),
      Bool.not_eq_true _ ▸ fun hc => ha.2 ((h₂.isVerifier a).2 ⟨_, ?_, hc⟩)⟩ <;>
      simp [Polynomial.eval_add]

/-- **`RP` is closed under intersection**: reduce the error of both deciders to `1 / 4`, and
accept when both accept, on disjoint parts of the random string. -/
theorem inter_mem_RP {A B : Set α} (hA : A ∈ RP enc) (hB : B ∈ RP enc) : A ∩ B ∈ RP enc := by
  obtain ⟨p₁, V₁, hV₁, h₁⟩ := mem_RP_iff_forall_decidesWithOneSidedErrorExponent.1 hA 2
  obtain ⟨p₂, V₂, hV₂, h₂⟩ := mem_RP_iff_forall_decidesWithOneSidedErrorExponent.1 hB 2
  refine ⟨p₁ + p₂, andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂, by fun_prop,
    fun a => ⟨fun ha => ?_, fun ha r => ?_⟩⟩
  · have e₁ := (h₁ a).1 ha.1
    have e₂ := (h₂ a).1 ha.2
    have hs₁ := acceptCount_add_card_filter_eq_false (V := V₁) (a := a)
      (n := p₁.eval (enc a).length)
    have hs₂ := acceptCount_add_card_filter_eq_false (V := V₂) (a := a)
      (n := p₂.eval (enc a).length)
    simp only [Polynomial.eval_ofNat] at e₁ e₂
    -- each decider accepts at least three quarters of its random strings
    have f₁ : 3 * 2 ^ p₁.eval (enc a).length ≤ 4 * acceptCount V₁ a (p₁.eval (enc a).length) := by
      omega
    have f₂ : 3 * 2 ^ p₂.eval (enc a).length ≤ 4 * acceptCount V₂ a (p₂.eval (enc a).length) := by
      omega
    change 2 ^ (p₁ + p₂).eval (enc a).length ≤
      2 * acceptCount _ a ((p₁ + p₂).eval (enc a).length)
    rw [Polynomial.eval_add, acceptCount_andVerifier, pow_add]
    nlinarith [Nat.mul_le_mul f₁ f₂]
  · have hA' := (h₁.decidesWithOneSidedError fun _ => by simp).isVerifier a
    have hB' := (h₂.decidesWithOneSidedError fun _ => by simp).isVerifier a
    simp only [andVerifier, Bool.and_eq_false_iff]
    by_contra hc
    simp only [not_or, Bool.not_eq_false] at hc
    exact ha ⟨hA'.2 ⟨_, by simp [Polynomial.eval_add], hc.1⟩,
      hB'.2 ⟨_, by simp [Polynomial.eval_add], hc.2⟩⟩

/-- `coRP` is closed under union. -/
theorem union_mem_coRP {A B : Set α} (hA : A ∈ coRP enc) (hB : B ∈ coRP enc) :
    A ∪ B ∈ coRP enc :=
  compl_union_mem inter_mem_RP hA hB

/-- `coRP` is closed under intersection. -/
theorem inter_mem_coRP {A B : Set α} (hA : A ∈ coRP enc) (hB : B ∈ coRP enc) :
    A ∩ B ∈ coRP enc :=
  compl_inter_mem union_mem_RP hA hB

open scoped symmDiff

/-- `ZPP` is closed under intersection. -/
theorem inter_mem_ZPP {A B : Set α} (hA : A ∈ ZPP enc) (hB : B ∈ ZPP enc) : A ∩ B ∈ ZPP enc := by
  rw [ZPP_eq_RP_inter_coRP] at *
  exact ⟨inter_mem_RP hA.1 hB.1, inter_mem_coRP hA.2 hB.2⟩

/-- `ZPP` as a Boolean subalgebra of `Set α`. -/
def ZPP.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (ZPP enc) (P_subset_ZPP empty_mem_P) (fun _ => compl_mem_ZPP)
    (fun _ _ => inter_mem_ZPP)

@[simp]
theorem ZPP.coe_booleanSubalgebra : (ZPP.booleanSubalgebra enc : Set (Set α)) = ZPP enc := rfl

@[simp]
theorem ZPP.mem_booleanSubalgebra {A : Set α} :
    A ∈ ZPP.booleanSubalgebra enc ↔ A ∈ ZPP enc := Iff.rfl

/-- `ZPP` is closed under union. -/
theorem union_mem_ZPP {A B : Set α} (hA : A ∈ ZPP enc) (hB : B ∈ ZPP enc) : A ∪ B ∈ ZPP enc :=
  (ZPP.booleanSubalgebra enc).sup_mem hA hB

/-- `ZPP` is closed under set difference. -/
theorem diff_mem_ZPP {A B : Set α} (hA : A ∈ ZPP enc) (hB : B ∈ ZPP enc) : A \ B ∈ ZPP enc :=
  (ZPP.booleanSubalgebra enc).sdiff_mem hA hB

/-- `ZPP` is closed under symmetric difference. -/
theorem symmDiff_mem_ZPP {A B : Set α} (hA : A ∈ ZPP enc) (hB : B ∈ ZPP enc) : A ∆ B ∈ ZPP enc :=
  (ZPP.booleanSubalgebra enc).symmDiff_mem hA hB

end Cslib.Complexity
