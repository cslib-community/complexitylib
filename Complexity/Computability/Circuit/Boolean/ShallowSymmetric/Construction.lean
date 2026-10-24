/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AltFormula
public import Complexity.Computability.Circuit.Boolean.ShallowSymmetric.Weights
public import Complexity.Computability.Circuit.Boolean.ShallowSymmetric.Covering
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination

/-!
# The finite shallow-circuit construction

The modular tests of Lecomte and Ramakrishnan [LecomteRamakrishnan2026] are conjunctions of
symmetric two-block comparisons after signed input substitution. Their output AND gates can be
merged, retaining the depth of a comparison. A small covering family of these tests is then joined
by one OR layer.

## Main results

* `Cslib.Circuits.Boolean.ShallowSymmetric.exists_pairComparison`: one comparison of two blocks.
* `Cslib.Circuits.Boolean.ShallowSymmetric.exists_exact_altFormula`: the exact-weight tests.
* `Cslib.Circuits.Boolean.ShallowSymmetric.exists_symmetric_altFormula_succ`: one step of the depth
  induction.

## References

* [V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*][LecomteRamakrishnan2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.ShallowSymmetric

open BitString

/-- Lift a symmetric synthesis bound to one modular comparison of two blocks. -/
theorem exists_pairComparison {n k d B M : ℕ}
    (ih : ∀ m ≤ M, ∀ a : ℕ → Bool,
      ∃ f : AltFormula m (d + 2), AltFormula.size f ≤ B ∧
        ∀ x, AltFormula.eval .and f x = a (weight x))
    (hm : 2 * (n / k + 1) ≤ M) (i j si sj : ZMod k) :
    ∃ f : AltFormula n (d + 2), AltFormula.size f ≤ B ∧
      ∀ x, AltFormula.eval .and f x =
        decide ((blockWeight residueBlock x i : ZMod k) + si ≠
          (blockWeight residueBlock x j : ZMod k) + sj) := by
  classical
  let I := {u : Fin n // residueBlock u = i}
  let J := {u : Fin n // residueBlock u = j}
  let V := I ⊕ J
  let m := Fintype.card V
  let e : Fin m ≃ V := (Fintype.equivFin V).symm
  let select : Fin m → Logic.PL.Literal (Fin n) := fun u =>
    Sum.elim (fun v : I => (v.1, true)) (fun v : J => (v.1, false)) (e u)
  let a : ℕ → Bool := fun w =>
    decide ((w : ZMod k) + si ≠ (Fintype.card J : ZMod k) + sj)
  have hm' : m ≤ M := by
    have hi := card_residueBlock_le n k i
    have hj := card_residueBlock_le n k j
    change Fintype.card (I ⊕ J) ≤ M
    rw [Fintype.card_sum]
    dsimp [I, J]
    omega
  obtain ⟨f, hs, he⟩ := ih m hm' a
  refine ⟨AltFormula.mapInputs select f, ?_, fun x => ?_⟩
  · rwa [AltFormula.size_mapInputs]
  rw [AltFormula.eval_mapInputs, he]
  let z : Fin m → Bool := fun u => Logic.PL.Literal.eval x (select u)
  have hz : weight z = weight (Sum.elim (fun u : I => x u.1)
      (fun u : J => !(x u.1))) := by
    rw [weight_eq_sum_toNat, weight_eq_sum_toNat]
    apply Fintype.sum_equiv e
    intro u
    dsimp [z, select]
    cases e u <;> simp [Logic.PL.Literal.eval]
  have hw := weight_pair_not_add (fun u : I => x u.1) (fun u : J => x u.1)
  rw [← hz] at hw
  change weight z + blockWeight residueBlock x j =
    blockWeight residueBlock x i + Fintype.card J at hw
  have hcast : (weight z : ZMod k) + (blockWeight residueBlock x j : ZMod k) =
      (blockWeight residueBlock x i : ZMod k) + (Fintype.card J : ZMod k) := by
    simpa only [Nat.cast_add] using congrArg (fun r : ℕ => (r : ZMod k)) hw
  change decide ((weight z : ZMod k) + si ≠ (Fintype.card J : ZMod k) + sj) = _
  congr 1
  have heq : ((weight z : ZMod k) + si = (Fintype.card J : ZMod k) + sj) ↔
      (blockWeight residueBlock x i : ZMod k) + si =
        (blockWeight residueBlock x j : ZMod k) + sj := by
    constructor <;> intro h
    · linear_combination h - hcast
    · linear_combination hcast + h
  exact propext (not_congr heq)


open Finset

/-- Synthesize a simultaneous modular test without increasing the comparison
depth. The bound counts all ordered pairs, including harmless diagonal pairs. -/
private theorem exists_test_altFormula {n d B M : ℕ} {ι : Type*} [Fintype ι]
    (k : ι → ℕ) [∀ i, NeZero (k i)]
    (ih : ∀ m ≤ M, ∀ a : ℕ → Bool,
      ∃ f : AltFormula m (d + 2), AltFormula.size f ≤ B ∧
        ∀ x, AltFormula.eval .and f x = a (weight x))
    (hm : ∀ i, 2 * (n / k i + 1) ≤ M)
    (t : ℕ) (s : (i : ι) → ZMod (k i) → ZMod (k i)) :
    ∃ f : AltFormula n (d + 2), AltFormula.size f ≤ 2 + (∑ i, (k i) ^ 2) * (B + 2) ∧
      ∀ x, AltFormula.eval .and f x = true ↔
        ∀ i, ShiftTest (t : ZMod (k i))
          (fun a => (blockWeight residueBlock x a : ZMod (k i))) (s i) := by
  classical
  by_cases valid : ∀ i, (∑ a, s i a) = residueSum (ZMod (k i)) - t
  · let P := (i : ι) × (ZMod (k i) × ZMod (k i))
    have hp (p : P) : ∃ f : AltFormula n (d + 2), AltFormula.size f ≤ B + 2 ∧
        ∀ x, AltFormula.eval .and f x = true ↔ p.2.1 ≠ p.2.2 →
          (blockWeight residueBlock x p.2.1 : ZMod (k p.1)) + s p.1 p.2.1 ≠
          (blockWeight residueBlock x p.2.2 : ZMod (k p.1)) + s p.1 p.2.2 := by
      by_cases heq : p.2.1 = p.2.2
      · refine ⟨AltFormula.constant n d .and true,
          (AltFormula.size_constant_le ..).trans (by omega), ?_⟩
        intro x
        simp [AltFormula.eval_constant, heq]
      · obtain ⟨f, hf, he⟩ := exists_pairComparison ih (hm p.1)
          p.2.1 p.2.2 (s p.1 p.2.1) (s p.1 p.2.2)
        exact ⟨f, hf.trans (by omega), fun x => by simp [he x, heq]⟩
    choose fs hs he using hp
    refine ⟨AltFormula.merge fs, ?_, ?_⟩
    · calc
        AltFormula.size (AltFormula.merge fs) ≤ 1 + ∑ p, AltFormula.size (fs p) :=
          AltFormula.size_merge_le fs
        _ ≤ 1 + ∑ _p : P, (B + 2) := Nat.add_le_add_left (sum_le_sum fun p _ => hs p) 1
        _ ≤ 2 + (∑ i, (k i) ^ 2) * (B + 2) := by
          simp only [sum_const, card_univ, smul_eq_mul]
          have hc : Fintype.card P = ∑ i, (k i) ^ 2 := by
            simp [P, Fintype.card_sigma, Fintype.card_prod, ZMod.card, pow_two]
          rw [hc]
          omega
    · intro x
      rw [AltFormula.eval_merge_and]
      simp only [he, shiftTest_iff_pairwise]
      constructor
      · intro h i
        exact ⟨valid i, fun a b hab => h ⟨i, a, b⟩ hab⟩
      · intro h p
        exact (h p.1).2 p.2.1 p.2.2
  · refine ⟨AltFormula.constant n d .and false,
      (AltFormula.size_constant_le ..).trans (by omega), ?_⟩
    intro x
    rw [AltFormula.eval_constant]
    constructor
    · intro h; exact Bool.noConfusion h
    · intro h
      exact (valid (fun i => (h i).1)).elim

/-- Exact-weight circuits obtained by covering every valid input with modular
tests and placing one OR above the test family. -/
theorem exists_exact_altFormula {n d B M : ℕ} {ι : Type*} [Fintype ι]
    (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) (hn : n < ∏ i, k i)
    (ih : ∀ m ≤ M, ∀ a : ℕ → Bool,
      ∃ f : AltFormula m (d + 2), AltFormula.size f ≤ B ∧
        ∀ x, AltFormula.eval .and f x = a (weight x))
    (hm : ∀ i, 2 * (n / k i + 1) ≤ M) (t : Fin (n + 1)) :
    ∃ f : AltFormula n (d + 3),
      AltFormula.size f ≤ 1 + (3 ^ (∑ i, k i) * (n + 1)) *
        (2 + (∑ i, (k i) ^ 2) * (B + 2)) ∧
      ∀ x, AltFormula.eval .or f x = true ↔ weight x = t.val := by
  classical
  let W := {x : BitString n // weight x = t.val}
  have hcard : Fintype.card W ≤ 2 ^ n := by
    simpa [W] using Fintype.card_subtype_le (fun x : BitString n => weight x = t.val)
  have hw (x : W) (i : ι) :
      (∑ a : ZMod (k i), (blockWeight residueBlock x.1 a : ZMod (k i))) = t.val := by
    rw [← Nat.cast_sum, sum_blockWeight (residueBlock (k := k i)) x.1, x.2]
  have cover := exists_simultaneous_shiftTest_cover
    (G := fun i => ZMod (k i)) (fun i => (t.val : ZMod (k i)))
    (fun x : W => fun i a => (blockWeight residueBlock x.1 a : ZMod (k i))) n hcard hw
  rw [show (∑ i, Fintype.card (ZMod (k i))) = ∑ i, k i by simp] at cover
  obtain ⟨tests, hcover⟩ := cover
  choose fs hs he using fun j => exists_test_altFormula k ih hm t.val (tests j)
  refine ⟨AltFormula.gate fs, ?_, ?_⟩
  · rw [AltFormula.size_gate]
    exact Nat.add_le_add_left ((sum_le_sum fun j _ => hs j).trans_eq (by simp)) 1
  · intro x
    rw [AltFormula.eval_gate_or]
    constructor
    · rintro ⟨j, hj⟩
      exact weight_eq_of_shiftTests k hc hn t x (tests j) ((he j x).1 hj)
    · intro hx
      obtain ⟨j, hj⟩ := hcover ⟨x, hx⟩
      exact ⟨j, (he j x).2 hj⟩

/-- The explicit finite recurrence for symmetric functions, in both output
polarities. The constants in the asymptotic theorem are extracted from this
bound, after choosing the moduli. -/
theorem exists_symmetric_altFormula_succ {n d B M : ℕ} {ι : Type*} [Fintype ι]
    (k : ι → ℕ) [∀ i, NeZero (k i)]
    (hc : Pairwise (fun i j => (k i).Coprime (k j))) (hn : n < ∏ i, k i)
    (ih : ∀ m ≤ M, ∀ a : ℕ → Bool,
      ∃ f : AltFormula m (d + 2), AltFormula.size f ≤ B ∧
        ∀ x, AltFormula.eval .and f x = a (weight x))
    (hm : ∀ i, 2 * (n / k i + 1) ≤ M) (a : ℕ → Bool) (op : AltOp) :
    ∃ f : AltFormula n (d + 3),
      AltFormula.size f ≤ 1 + (n + 1) *
        (1 + (3 ^ (∑ i, k i) * (n + 1)) * (2 + (∑ i, (k i) ^ 2) * (B + 2))) ∧
      ∀ x, AltFormula.eval op f x = a (weight x) := by
  classical
  have hor (a : ℕ → Bool) : ∃ f : AltFormula n (d + 3),
      AltFormula.size f ≤ 1 + (n + 1) *
        (1 + (3 ^ (∑ i, k i) * (n + 1)) * (2 + (∑ i, (k i) ^ 2) * (B + 2))) ∧
      ∀ x, AltFormula.eval .or f x = a (weight x) := by
    let T := {t : Fin (n + 1) // a t.val = true}
    choose fs hs he using fun t : T => exists_exact_altFormula k hc hn ih hm t.1
    refine ⟨AltFormula.merge fs, ?_, ?_⟩
    · apply (AltFormula.size_merge_le fs).trans
      apply Nat.add_le_add_left
      have hT : Fintype.card T ≤ n + 1 := by
        simpa [T] using Fintype.card_subtype_le (fun t : Fin (n + 1) => a t.val = true)
      calc
        ∑ t, AltFormula.size (fs t) ≤ ∑ _t : T,
            (1 + (3 ^ (∑ i, k i) * (n + 1)) *
              (2 + (∑ i, (k i) ^ 2) * (B + 2))) := sum_le_sum fun t _ => hs t
        _ ≤ _ := by
          simp only [sum_const, card_univ, smul_eq_mul]
          exact Nat.mul_le_mul_right _ hT
    · intro x
      apply Bool.eq_iff_iff.2
      rw [AltFormula.eval_merge_or]
      constructor
      · rintro ⟨t, ht⟩
        rw [(he t x).1 ht]
        exact t.2
      · intro hx
        have hweight : weight x < n + 1 := by
          have h := weight_le x
          simp only [Fintype.card_fin] at h
          omega
        let t : T := ⟨⟨weight x, hweight⟩, hx⟩
        exact ⟨t, (he t x).2 rfl⟩
  cases op with
  | or => exact hor a
  | and =>
    obtain ⟨f, hs, he⟩ := hor (fun w => !(a w))
    refine ⟨AltFormula.neg f, ?_, ?_⟩
    · simpa only [AltFormula.neg, AltFormula.size_mapInputs] using hs
    · intro x
      exact (AltFormula.eval_neg f .or x).trans (by simp [he])

end Cslib.Circuits.Boolean.ShallowSymmetric
