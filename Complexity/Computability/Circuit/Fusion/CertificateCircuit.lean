/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Certificate
public import Complexity.Computability.Circuit.Monotone.Formula

/-!
# Native formulas for semi-ultrafilter certificates

Consistency violations are grouped by each of the three certificate bits per pair, costing one
AND each. The fixed empty-set group costs none. Pair-preservation violations cost two ANDs each.
Constants and OR gates are free, and the auxiliary labels and their negations are supplied as
input literals. Thus the entire rejection test costs five ANDs per cover pair.

## Main results

* `Cslib.Circuits.Fusion.PairCertificate.exists_formula`: compile the certificate test to a native
  monotone formula of five AND gates per pair from free primary and auxiliary literals.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], Theorem 45. The explicit factor five is obtained by the grouped
  certificate construction, rather than asserted as a constant in the cited characterization.
-/

@[expose] public section

namespace Cslib.Circuits.Fusion.PairCertificate

private def HasFormula {X : Type*} {k : ℕ} (input : X → Fin k → Bool)
    (P : X → Prop) (cost : ℕ) : Prop :=
  ∃ F : Formula Monotone.signature k,
    (∀ x, F.eval Monotone.interpretation (input x) = true ↔ P x) ∧
    F.cost Monotone.andCost = cost

private theorem HasFormula.const {X : Type*} {k : ℕ} (input : X → Fin k → Bool) (b : Bool) :
    HasFormula input (fun _ => b = true) 0 :=
  ⟨Monotone.const b, fun _ => Iff.rfl, by simp [Monotone.const]⟩

private theorem HasFormula.or {X : Type*} {k a b : ℕ} {input : X → Fin k → Bool}
    {P Q : X → Prop} (hP : HasFormula input P a) (hQ : HasFormula input Q b) :
    HasFormula input (fun x => P x ∨ Q x) (a + b) := by
  obtain ⟨F, hF, cF⟩ := hP
  obtain ⟨G, hG, cG⟩ := hQ
  exact ⟨Monotone.or F G, fun x => by simp [hF x, hG x],
    by simp [Monotone.or, Fin.sum_univ_two, cF, cG]⟩

private theorem HasFormula.and {X : Type*} {k a b : ℕ} {input : X → Fin k → Bool}
    {P Q : X → Prop} (hP : HasFormula input P a) (hQ : HasFormula input Q b) :
    HasFormula input (fun x => P x ∧ Q x) (a + b + 1) := by
  obtain ⟨F, hF, cF⟩ := hP
  obtain ⟨G, hG, cG⟩ := hQ
  exact ⟨Monotone.and F G, fun x => by simp [hF x, hG x],
    by simp [Monotone.and, Fin.sum_univ_two, cF, cG]⟩

private theorem HasFormula.guard {X : Type*} {k : ℕ} {input : X → Fin k → Bool}
    {P : X → Prop} (hP : HasFormula input P 0) (Q : Prop) :
    HasFormula input (fun x => Q ∧ P x) 0 := by
  classical
  by_cases hQ : Q
  · simpa only [hQ, true_and] using hP
  · simpa only [hQ, false_and, Bool.false_eq_true] using HasFormula.const input false

private theorem HasFormula.exists_finset {X α : Type*} {k : ℕ} {input : X → Fin k → Bool}
    (s : Finset α) (P : α → X → Prop) (cost : α → ℕ)
    (h : ∀ i ∈ s, HasFormula input (P i) (cost i)) :
    HasFormula input (fun x => ∃ i ∈ s, P i x) (∑ i ∈ s, cost i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasFormula.const input false
  | @insert i s hi ih =>
    have htail := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi, Finset.mem_insert, exists_prop, exists_eq_or_imp] using
      (h i (Finset.mem_insert_self _ _)).or htail

private theorem HasFormula.exists_fintype {X α : Type*} [Fintype α] {k : ℕ}
    {input : X → Fin k → Bool} (P : α → X → Prop) (cost : α → ℕ)
    (h : ∀ i, HasFormula input (P i) (cost i)) :
    HasFormula input (fun x => ∃ i, P i x) (∑ i, cost i) := by
  simpa only [Finset.mem_univ, true_and] using
    HasFormula.exists_finset Finset.univ P cost (fun i _ => h i)

private theorem HasFormula.congr {X : Type*} {k c : ℕ} {input : X → Fin k → Bool}
    {P Q : X → Prop} (hP : HasFormula input P c) (h : ∀ x, P x ↔ Q x) :
    HasFormula input Q c := by
  obtain ⟨F, hF, cF⟩ := hP
  exact ⟨F, fun x => (hF x).trans (h x), cF⟩

/-- Pair-preservation violations `BreaksPair pairs (y z)` can be compiled with `2 * pairs.length`
AND gates when all auxiliary label polarities have zero-cost formulas. -/
private theorem hasFormula_breaksPair {U X : Type*} {k : ℕ} (pairs : List (Set U × Set U))
    (input : X → Fin k → Bool) (y : X → Fin (size pairs) → Bool)
    (hy : ∀ i b, HasFormula input (fun z => y z i = b) 0) :
    HasFormula input (fun z => BreaksPair pairs (y z)) (2 * pairs.length) := by
  simpa [BreaksPair, Nat.mul_comm] using
    HasFormula.exists_fintype _ (fun _ : Fin pairs.length => 2) fun i =>
      (hy (left pairs i) true).and ((hy (right pairs i) true).and (hy (inter pairs i) false))

/-- Compile consistency and pair-preservation violations using exactly five AND gates per pair.
The primary source values and both polarities of each auxiliary label are supplied at zero cost. -/
theorem exists_formula {U X : Type*} {n k : ℕ} (pairs : List (Set U × Set U))
    (sources : Fin n → Set U) (input : X → Fin k → Bool)
    (x : X → Fin n → Bool) (y : X → Fin (size pairs) → Bool)
    (hx : ∀ l, ∃ F : Formula Monotone.signature k,
      (∀ z, F.eval Monotone.interpretation (input z) = true ↔ x z l = true) ∧
      F.cost Monotone.andCost = 0)
    (hy : ∀ i b, ∃ F : Formula Monotone.signature k,
      (∀ z, F.eval Monotone.interpretation (input z) = true ↔ y z i = b) ∧
      F.cost Monotone.andCost = 0) :
    ∃ F : Formula Monotone.signature k,
      (∀ z, F.eval Monotone.interpretation (input z) = true ↔
        Invalid pairs sources (x z) (y z) ∨ BreaksPair pairs (y z)) ∧
      F.cost Monotone.andCost = 5 * pairs.length := by
  classical
  have hlabel (i : Option (Fin (size pairs))) (b : Bool) :
      HasFormula input (fun z => label pairs (y z) i = b) 0 := by
    cases i with
    | none =>
      cases b
      · simpa only [label, eq_self] using HasFormula.const input true
      · simpa only [label] using HasFormula.const input false
    | some i => exact hy i b
  let inner (j : Option (Fin (size pairs))) (z : X) : Prop :=
    (∃ i, sets pairs i ⊆ sets pairs j ∧ label pairs (y z) i = true) ∨
    (∃ l, sets pairs j ∪ sets pairs l = Set.univ ∧ label pairs (y z) l = false) ∨
    (∃ l, sources l ⊆ sets pairs j ∧ x z l = true)
  have hinner (j) : HasFormula input (inner j) 0 := by
    have h₁ := HasFormula.exists_fintype _ (fun _ => 0)
      (fun i => (hlabel i true).guard (sets pairs i ⊆ sets pairs j))
    have h₂ := HasFormula.exists_fintype _ (fun _ => 0)
      (fun i => (hlabel i false).guard (sets pairs j ∪ sets pairs i = Set.univ))
    have h₃ := HasFormula.exists_fintype _ (fun _ => 0)
      (fun l => (show HasFormula input (fun z => x z l = true) 0 from hx l).guard
        (sources l ⊆ sets pairs j))
    simpa only [Finset.sum_const_zero, Nat.add_zero] using h₁.or (h₂.or h₃)
  have hgroups : HasFormula input
      (fun z => ∃ j, label pairs (y z) (some j) = false ∧ inner (some j) z)
      (size pairs) := by
    simpa using HasFormula.exists_fintype _ (fun _ => 1)
      (fun j => (hlabel (some j) false).and (hinner (some j)))
  have hinvalid : HasFormula input (fun z => Invalid pairs sources (x z) (y z))
      (size pairs) := by
    refine (show HasFormula input _ (size pairs) from by
      simpa only [Nat.zero_add] using (hinner none).or hgroups).congr fun z =>
      ⟨?_, fun ⟨j, hj, h⟩ => by
        cases j with | none => exact Or.inl h | some j => exact Or.inr ⟨j, hj, h⟩⟩
    rintro (h | ⟨j, hj, h⟩)
    · exact ⟨none, rfl, h⟩
    · exact ⟨some j, hj, h⟩
  have hcost : size pairs + 2 * pairs.length = 5 * pairs.length := by dsimp [size]; lia
  simpa only [HasFormula, hcost] using hinvalid.or (hasFormula_breaksPair pairs input y hy)

end Cslib.Circuits.Fusion.PairCertificate
