/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.VCOne

/-!
# Overlapping local tables in shared global columns

The mathematical compilation step of [ChenJiangZhu2027], Theorem 6.3,
PDF pp. 20–21. Scope embeddings are injective within each table; different scopes
may overlap arbitrarily. Local tuples are restricted from one global assignment.
Separators are derived from each actual table and aligned in the same global
columns before row selection. No independence/disjointness of scopes is assumed.
This is a finite mathematical construction, without a polynomial-bit-time program.
-/

public section

noncomputable section

namespace Cslib.Logic.PL.VCOne

variable {V W : Type*} [Fintype V] [LinearOrder V]

/-- Declared counts, including unused bits, survive the zero-auxiliary inclusion. -/
private theorem count_relabel_zero (B : CNF V) :
    Fintype.card {x : V ⊕ Fin 0 → Bool // (B.relabel Sum.inl).eval x = true} =
      Fintype.card {x : V → Bool // B.eval x = true} := by
  classical
  let e : (V ⊕ Fin 0 → Bool) ≃ (V → Bool) :=
    { toFun := fun x => x ∘ Sum.inl
      invFun := fun x => Sum.elim x Fin.elim0
      left_inv := fun x => by
        funext v
        cases v with
        | inl v => rfl
        | inr v => exact Fin.elim0 v
      right_inv := fun _ => rfl }
  exact Fintype.card_congr (e.subtypeEquiv fun x => by
    change (B.relabel Sum.inl).eval x = true ↔ B.eval (x ∘ Sum.inl) = true
    rw [CNF.eval_relabel])

private theorem direct_queries (B : CNF V) (hw : ∀ c ∈ B, c.length ≤ 3)
    (hl : B.length ≤ 13 * Fintype.card V ^ 2) (hr : 2 ≤ Fintype.card V) :
    ∃ k : ℕ, ∃ Q : Bool → CNF (V ⊕ Fin k),
      Fintype.card {x : V → Bool // B.eval x = true} =
        Fintype.card {x : V ⊕ Fin k → Bool // (Q false).eval x = true} -
        Fintype.card {x : V ⊕ Fin k → Bool // (Q true).eval x = true} ∧
      (∀ β c, c ∈ Q β → c.length ≤ 3) ∧
      (∀ β, (Q β).length ≤ 13 * Fintype.card V ^ 2) ∧
      Fintype.card (V ⊕ Fin k) ≤ 2 * Fintype.card V - 2 := by
  classical
  let Q : Bool → CNF (V ⊕ Fin 0) := fun β => if β then [[]] else B.relabel Sum.inl
  have hz : Fintype.card {x : V ⊕ Fin 0 → Bool // (Q true).eval x = true} = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun x => by simpa [Q] using x.property⟩
  refine ⟨0, Q, ?_, ?_, ?_, ?_⟩
  · rw [hz, Nat.sub_zero]
    exact (count_relabel_zero B).symm
  · intro β c hc
    cases β
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      simpa using hw d hd
    · have he : c = [] := by simpa [Q] using hc
      simp [he]
  · intro β
    cases β
    · simpa [Q, CNF.relabel] using hl
    · simp only [Q, ite_true, List.length_singleton]
      nlinarith
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega

open scoped Classical in
/-- Unit clauses fixing precisely one original assignment. -/
@[expose] def fixing (x : V → Bool) : CNF V :=
  (Finset.univ.sort (· ≤ ·)).map fun v => [(v, x v)]

/-- The direct unique-candidate formula fixes all declared bits. -/
theorem fixing_eval (x u : V → Bool) : (fixing x).eval u = true ↔ u = x := by
  classical
  simp [fixing, CNF.eval_eq_true_iff, Clause.eval, Literal.eval, funext_iff]


variable {I : Type*} [Fintype I]
    (w : I → ℕ) (scope : (i : I) → Fin (w i) ↪ V)
    (R : (i : I) → Finset (Fin (w i) → Bool))

/-- The original table constraints, evaluated on the same global bits. -/
@[expose] def Satisfies (x : V → Bool) : Prop := ∀ i, x ∘ scope i ∈ R i

open scoped Classical in
/-- Direct enumeration on the declared bits, used for zero or one global variable. -/
@[expose] def directCount : ℕ :=
  (Finset.univ.filter fun x : V → Bool => Satisfies w scope R x).card

open scoped Classical in
omit [Fintype I] in
/-- The small-instance branch counts exactly the original global assignments. -/
theorem directCount_correct : directCount w scope R =
    Fintype.card {x : V → Bool // Satisfies w scope R x} := by
  rw [Fintype.card_subtype]
  rfl

omit [Fintype I] in
/-- At most two candidates are examined when at most one bit is declared. -/
theorem directCount_small (hr : Fintype.card V ≤ 1) :
    directCount w scope R ≤ 2 := by
  classical
  have hc := Finset.card_le_card (Finset.filter_subset
    (fun x : V → Bool => Satisfies w scope R x) Finset.univ)
  have hb : Fintype.card (V → Bool) ≤ 2 := by
    simp only [Fintype.card_fun, Fintype.card_bool]
    exact (Nat.pow_le_pow_right (by decide) hr).trans (by decide)
  exact hc.trans (by simpa using hb)

open scoped Classical in
/-- One common index for all locally derived separating equations. -/
@[expose] def EquationIndex := (i : I) × ↥(closure (R i) \ R i)

open scoped Classical in
instance : Fintype (EquationIndex w R) :=
  inferInstanceAs (Fintype ((i : I) × ↥(closure (R i) \ R i)))

open scoped Classical in
/-- Union of relabelled unary/binary restrictions; overlaps share their global variable. -/
@[expose] def tableSide : CNF V :=
  (Finset.univ.toList : List I).flatMap fun i => (binary (R i)).relabel (scope i)

omit [Fintype V] [LinearOrder V] in
/-- Every relabelled side clause still has width at most two. -/
theorem tableSide_width (c : Clause V) (hc : c ∈ tableSide w scope R) : c.length ≤ 2 := by
  classical
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  simpa using binary_width (R i) d hd

open scoped Classical in
/-- The local separator scope embedded into the global columns. -/
@[expose] def tableScope
    (j : EquationIndex w R) : Finset V :=
  (separatorScope (R j.1) j.2).map (scope j.1)

/-- Polarity at an embedded coordinate is the complement of the unwanted local tuple. -/
@[expose] def tablePolarity (j : EquationIndex w R) : V → Bool :=
  Function.extend (scope j.1) (fun k => !(j.2.val k)) (fun _ => false)

omit [Fintype V] [LinearOrder V] in
/-- Exact pointwise compilation across arbitrarily overlapping scopes.
No auxiliary assignments are introduced by the local representations. -/
theorem tables_iff (hR : ∀ i, DimensionOne (R i)) (x : V → Bool) :
    Satisfies w scope R x ↔
      (tableSide w scope R).eval x = true ∧
        ∀ j : EquationIndex w R,
          ExactOne.Holds (tableScope w scope R j) (tablePolarity w scope R j) x := by
  classical
  have hb : (tableSide w scope R).eval x = true ↔
      ∀ i, (binary (R i)).eval (x ∘ scope i) = true := by
    simp [tableSide, CNF.eval_flatMap_eq_true_iff]
  rw [hb]
  constructor
  · intro hx
    have h (i : I) := (representation_iff (R i) (hR i) (x ∘ scope i)).mp (hx i)
    exact ⟨fun i => (h i).1, fun j =>
      (ExactOne.holds_map (scope j.1) _ _ x).mpr ((h j.1).2 j.2)⟩
  · rintro ⟨hb, he⟩ i
    apply (representation_iff (R i) (hR i) (x ∘ scope i)).mpr
    exact ⟨hb i, fun y => (ExactOne.holds_map (scope i) _ _ x).mp (he ⟨i, y⟩)⟩

open scoped Classical in
omit [Fintype I] in
/-- Global row selection uses the number of declared global variables, regardless
of the number of tables or their overlaps. The witnesses only distinguish the
rationally nonunique branch; they are not required to be Boolean or meet the CNF. -/
theorem tables_queries_of_two_rational_solutions [Finite I]
    (hR : ∀ i, DimensionOne (R i)) [Nonempty (EquationIndex w R)] (a b : V → ℚ)
    (ha : ∀ j, dotProduct (ExactOne.coefficients (tableScope w scope R j)
      (tablePolarity w scope R j)) a =
      ExactOne.rhs (tableScope w scope R j) (tablePolarity w scope R j))
    (hb : ∀ j, dotProduct (ExactOne.coefficients (tableScope w scope R j)
      (tablePolarity w scope R j)) b =
      ExactOne.rhs (tableScope w scope R j) (tablePolarity w scope R j)) (hne : a ≠ b) :
    ∃ k : ℕ, ∃ Q : Bool → CNF (V ⊕ Fin k),
      Fintype.card {x : V → Bool // Satisfies w scope R x} =
        Fintype.card {x : V ⊕ Fin k → Bool // (Q false).eval x = true} -
        Fintype.card {x : V ⊕ Fin k → Bool // (Q true).eval x = true} ∧
      (∀ β c, c ∈ Q β → c.length ≤ 3) ∧
      (∀ β, (Q β).length ≤ 13 * Fintype.card V ^ 2) ∧
      Fintype.card (V ⊕ Fin k) ≤ 2 * Fintype.card V - 2 := by
  classical
  let := Fintype.ofFinite I
  obtain ⟨k, Q, _, _, hc, hw, hl, _, hv⟩ :=
    ExactOne.exists_queries_of_two_rational_solutions (tableSide w scope R)
      (tableSide_width w scope R) (tableScope w scope R) (tablePolarity w scope R)
      a b ha hb hne
  refine ⟨k, Q, ?_, hw, hl, hv⟩
  rw [← hc]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (tables_iff w scope R hR))

open scoped Classical in
omit [Fintype I] in
/-- Theorem 6.3's mathematical query budget, with every direct branch included.
The only hypotheses concern the actual tables and the declared variable count.
Classical table enumeration/row choice here does not certify polynomial bit time. -/
theorem tables_queries [Finite I] (hR : ∀ i, DimensionOne (R i)) (hr : 2 ≤ Fintype.card V) :
    ∃ k : ℕ, ∃ Q : Bool → CNF (V ⊕ Fin k),
      Fintype.card {x : V → Bool // Satisfies w scope R x} =
        Fintype.card {x : V ⊕ Fin k → Bool // (Q false).eval x = true} -
        Fintype.card {x : V ⊕ Fin k → Bool // (Q true).eval x = true} ∧
      (∀ β c, c ∈ Q β → c.length ≤ 3) ∧
      (∀ β, (Q β).length ≤ 13 * Fintype.card V ^ 2) ∧
      Fintype.card (V ⊕ Fin k) ≤ 2 * Fintype.card V - 2 := by
  classical
  let := Fintype.ofFinite I
  by_cases hi : Nonempty (EquationIndex w R)
  swap
  · have he : IsEmpty (EquationIndex w R) := not_nonempty_iff.mp hi
    let := he
    let B : CNF V := (tableSide w scope R).dedup
    have hc : Fintype.card {x : V → Bool // Satisfies w scope R x} =
        Fintype.card {x : V → Bool // B.eval x = true} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro x
      rw [tables_iff w scope R hR]
      simp [B, CNF.eval_eq_true_iff]
    rw [hc]
    apply direct_queries B
    · intro c hc
      exact (tableSide_width w scope R c (List.mem_dedup.mp hc)).trans (by decide)
    · have hb := ExactOne.dedup_binary_length (tableSide w scope R) (tableSide_width w scope R)
      change (tableSide w scope R).dedup.length ≤ _
      nlinarith
    · exact hr
  let S := tableScope w scope R
  let p := tablePolarity w scope R
  let Sol (a : V → ℚ) := ∀ j, dotProduct (ExactOne.coefficients (S j) (p j)) a =
    ExactOne.rhs (S j) (p j)
  by_cases hn : ∃ a b : V → ℚ, Sol a ∧ Sol b ∧ a ≠ b
  · obtain ⟨a, b, ha, hb, hab⟩ := hn
    let := hi
    exact tables_queries_of_two_rational_solutions w scope R hR a b ha hb hab
  have hu (x y : V → Bool) (hx : Satisfies w scope R x) (hy : Satisfies w scope R y) :
      x = y := by
    apply ExactOne.rationalPoint_injective
    by_contra hne
    apply hn
    refine ⟨ExactOne.rationalPoint x, ExactOne.rationalPoint y, ?_, ?_, hne⟩
    · exact fun j => (ExactOne.equation_iff _ _ _).mpr (((tables_iff w scope R hR x).mp hx).2 j)
    · exact fun j => (ExactOne.equation_iff _ _ _).mpr (((tables_iff w scope R hR y).mp hy).2 j)
  by_cases hx : ∃ x : V → Bool, Satisfies w scope R x
  · obtain ⟨x, hx⟩ := hx
    have hc : Fintype.card {u : V → Bool // Satisfies w scope R u} =
        Fintype.card {u : V → Bool // (fixing x).eval u = true} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight fun u =>
        (show Satisfies w scope R u ↔ u = x from
          ⟨fun h => hu u x h hx, fun h => h ▸ hx⟩).trans (fixing_eval x u).symm
    rw [hc]
    apply direct_queries (fixing x)
    · intro c hc
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hc
      simp
    · simp only [fixing, List.length_map, Finset.length_sort, Finset.card_univ]
      nlinarith
    · exact hr
  · have hc : Fintype.card {u : V → Bool // Satisfies w scope R u} =
        Fintype.card {u : V → Bool // CNF.eval u ([[]] : CNF V) = true} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight fun u => by simp [show ¬ Satisfies w scope R u from
        fun h => hx ⟨u, h⟩]
    rw [hc]
    apply direct_queries [[]]
    · intro c hc
      have he : c = [] := by simpa using hc
      simp [he]
    · simp only [List.length_singleton]
      nlinarith
    · exact hr

end Cslib.Logic.PL.VCOne
