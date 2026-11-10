/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Full
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Synthesis over the full binary basis

Over the full binary basis `fullInterpretation (k := 2)` every constant and every operation with
at most two arguments is one gate. This module records the synthesis rules used to count gates of
algebraic computations over a carrier `U`: an operation with one or two available arguments costs
one gate (`Synthesis.full_unary`, `Synthesis.full_binary_mem`), a sum of `N` available
functions over an additive commutative monoid costs `N + 1` gates, one of them for the constant
zero (`Synthesis.full_sum`), and a sum of `N` products of available functions over a semiring costs
`2 * N + 1` gates (`Synthesis.full_dot`). A *chain* `v 0 = c`, `v (i + 1) = op i (v i) (g i x)`
of length `len`, fed by available functions `g i`, costs `len + 1` gates for all of its values
(`Synthesis.full_chain`); chains compute prefix tests such as the first nonzero entry of a vector.
Applied to a field, this counts field operations, with every operation that depends on at most two
field elements, including tests and selections, charged one gate.

## Main definitions

* `Cslib.Circuits.Synthesis.chainValue`: the values of a chain.

## Main results

* `Cslib.Circuits.Synthesis.full_unary`: one gate for an operation on one available function.
* `Cslib.Circuits.Synthesis.full_binary_mem`: one gate for an operation on two available functions.
* `Cslib.Circuits.Synthesis.full_sum`: `N + 1` gates for a sum of `N` available functions.
* `Cslib.Circuits.Synthesis.full_dot`: `2 * N + 1` gates for a sum of `N` products.
* `Cslib.Circuits.Synthesis.full_chain`: `len + 1` gates for all values of a chain.

## References

* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity Theory*]
  [BurgisserClausenShokrollahi1997]
-/

@[expose] public section

namespace Cslib.Circuits.Synthesis

open Finset

variable {U : Type*} {n : ℕ} {s : Set ((Fin n → U) → U)} {f g : (Fin n → U) → U}

/-- An operation applied to one available function costs one gate of the full binary basis. -/
theorem full_unary (op : U → U) (hf : f ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s {fun x => op (f x)} 1 :=
  full_gate (k := 2) (r := 1) (by decide) (fun v => op (v 0)) (fun _ => f) fun _ => hf

/-- An operation applied to two available functions costs one gate of the full binary basis. -/
theorem full_binary_mem (op : U → U → U) (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s {fun x => op (f x) (g x)} 1 := by
  simpa using full_binary (of_mem hf) (of_mem hg) op

/-- A sum of available functions, indexed by a finset `S`, costs `#S + 1` gates of the full
binary basis: one addition for each summand and a constant zero to start from. -/
theorem full_sum [AddCommMonoid U] {ι : Type*} (S : Finset ι) (f : ι → (Fin n → U) → U)
    (hf : ∀ i ∈ S, f i ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s {fun x => ∑ i ∈ S, f i x} (#S + 1) := by
  have : Std.Commutative (α := U) (· + ·) := ⟨add_comm⟩
  have : Std.Associative (α := U) (· + ·) := ⟨add_assoc⟩
  have h := finset_fold (I := fullInterpretation (k := 2)) (· + ·) 1
    (fun f g => full_binary_mem (s := {f, g}) (· + ·) (by simp) (by simp)) S
    (full_const (k := 2) (s := s) (0 : U)) (cost := fun _ => 0) (fun i hi => of_mem (hf i hi))
  simp only [zero_add, sum_const, smul_eq_mul, mul_one] at h
  simpa only [sum_eq_fold] using h

/-- A sum of products of available functions, indexed by a finset `S`, costs `2 * #S + 1` gates
of the full binary basis. -/
theorem full_dot [NonUnitalNonAssocSemiring U] {ι : Type*} (S : Finset ι)
    (f g : ι → (Fin n → U) → U) (hf : ∀ i ∈ S, f i ∈ s) (hg : ∀ i ∈ S, g i ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s {fun x => ∑ i ∈ S, f i x * g i x}
      (2 * #S + 1) := by
  classical
  have hprod := biUnion (I := fullInterpretation (k := 2)) (s := s) S
    (fun i => {fun x => f i x * g i x}) (fun _ => 1)
    (fun i hi => full_binary_mem (· * ·) (hf i hi) (hg i hi))
  have hsum := full_sum (s := s ∪ ⋃ i ∈ S, {fun x => f i x * g i x}) S
    (fun i x => f i x * g i x) (fun i hi => Set.mem_union_right _ (Set.mem_biUnion hi rfl))
  refine (hprod.trans hsum).mono Set.Subset.rfl Set.Subset.rfl ?_
  simp only [sum_const, smul_eq_mul, mul_one]
  omega

/-- The values of a *chain*: `v 0 = c` and `v (i + 1) = op i (v i) (g i x)`. -/
def chainValue (c : U) (op : ℕ → U → U → U) (g : ℕ → (Fin n → U) → U) :
    ℕ → (Fin n → U) → U
  | 0 => fun _ => c
  | i + 1 => fun x => op i (chainValue c op g i x) (g i x)

/-- All values `v 0, …, v len` of a chain of length `len` fed by available functions cost
`len + 1` gates of the full binary basis: a constant and one binary gate per link. -/
theorem full_chain (c : U) (op : ℕ → U → U → U) (g : ℕ → (Fin n → U) → U) (len : ℕ)
    (hg : ∀ i < len, g i ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s
      (Set.range fun i : Fin (len + 1) => chainValue c op g i) (len + 1) := by
  induction len with
  | zero =>
    refine (full_const (k := 2) (s := s) c).mono Set.Subset.rfl ?_ le_rfl
    rintro _ ⟨i, rfl⟩
    rw [Fin.fin_one_eq_zero i]
    rfl
  | succ len ih =>
    have hstep := full_binary_mem (s := s ∪ Set.range fun i : Fin (len + 1) =>
      chainValue c op g i) (op len) (Set.mem_union_right _ ⟨Fin.last len, rfl⟩)
      (Set.mem_union_left _ (hg len (Nat.lt_succ_self len)))
    refine ((ih fun i hi => hg i (Nat.lt_succ_of_lt hi)).comp hstep).mono Set.Subset.rfl ?_
      le_rfl
    rintro _ ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · exact Set.mem_union_left _ ⟨i, rfl⟩
    · exact Set.mem_union_right _ rfl

end Cslib.Circuits.Synthesis
