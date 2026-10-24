/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Graph.Canonical
public import Complexity.Computability.Circuit.Monotone.Formula

/-!
# Exact cover complexity of the inequality graph

The complement of the inequality graph is its diagonal. Its canonical semifilter at `(u,v)`
accepts a set exactly when it contains `(u,u)` or `(v,v)`. Any pair defeating this semifilter
distinguishes these diagonal points by membership in its first component. Thus a cover of
length `k` injectively labels the vertices by `k` bits. For `n`-bit vertices this forces `n ≤ k`.

## Main definitions

* `Cslib.Circuits.Fusion.Graph.inequality`: the bipartite graph of unequal vertex labels.
* `Cslib.Circuits.Fusion.Graph.diagonal`: a diagonal point of its complement.

## Main results

* `Cslib.Circuits.Fusion.Graph.le_length_inequality`: every canonical cover has at least `n` pairs.
* `Cslib.Circuits.Fusion.Graph.exists_inequality_circuit`: a native circuit with `n` AND gates.
* `Cslib.Circuits.Fusion.Graph.inequality_complexities`: all three complexities equal `n`,
  including the empty graph at `n = 0`.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], Proposition 40. The injective-label proof below is an equivalent
  counting argument on the diagonal.
-/

@[expose] public section

namespace Cslib.Circuits.Fusion.Graph

variable {V : Type*}

/-- The bipartite inequality graph. -/
def inequality (V : Type*) : Set (V × V) := {x | x.1 ≠ x.2}

/-- A diagonal pair is outside the inequality graph. -/
def diagonal (v : V) : ↥((inequality V)ᶜ) := ⟨(v, v), not_not_intro rfl⟩

/-- Every inequality edge has nonempty complementary row and column. -/
def inequalityEdge (u v : V) (h : u ≠ v) : CanonicalEdge (inequality V) :=
  ⟨(u, v), h, ⟨diagonal u, rfl⟩, ⟨diagonal v, rfl⟩⟩

/-- On the diagonal, canonical semifilters accept membership of either endpoint. -/
theorem canonicalFilter_inequality (u v : V) (h : u ≠ v)
    (s : Set ↥((inequality V)ᶜ)) :
    canonicalFilter (inequality V) (inequalityEdge u v h) s ↔
      diagonal u ∈ s ∨ diagonal v ∈ s := by
  have row : outsideRow (inequality V) u = {diagonal u} := by
    ext x
    constructor
    · intro hx
      have heq : x.val.1 = x.val.2 := Classical.not_not.mp x.property
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact Prod.ext hx (heq.symm.trans hx)
    · rintro rfl
      rfl
  have col : outsideColumn (inequality V) v = {diagonal v} := by
    ext x
    constructor
    · intro hx
      have heq : x.val.1 = x.val.2 := Classical.not_not.mp x.property
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact Prod.ext (heq.trans hx) hx
    · rintro rfl
      rfl
  change (outsideRow (inequality V) u ⊆ s ∨ outsideColumn (inequality V) v ⊆ s) ↔ _
  rw [row, col, Set.singleton_subset_iff, Set.singleton_subset_iff]

/-- Canonical inequality semifilters are semi-ultrafilters (Proposition 47's witness fact). -/
theorem canonicalFilter_inequality_isUltra (u v : V) (h : u ≠ v) :
    (canonicalFilter (inequality V) (inequalityEdge u v h)).IsUltra := by
  classical
  intro s
  simp only [canonicalFilter_inequality, Set.mem_compl_iff]
  by_cases hu : diagonal u ∈ s
  · exact Or.inl (Or.inl hu)
  · exact Or.inr (Or.inl hu)

variable [Fintype V]

/-- The first components of a canonical cover give distinct bit signatures to distinct vertices. -/
theorem inequality_signature_injective
    (c : PairCover (inequality V) sources (canonicalClass (inequality V))) :
    Function.Injective (fun v : V => fun i : Fin c.pairs.length =>
      (c.pairs[i.val]).1.boolIndicator (diagonal v)) := by
  classical
  intro u v heq
  by_contra hne
  let e := inequalityEdge u v hne
  apply c.isCover (canonicalWitness (inequality V) e)
  intro p hp
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
  have hs := congrFun heq i
  have he : diagonal u ∈ p.1 ↔ diagonal v ∈ p.1 := by
    rw [Set.mem_iff_boolIndicator, Set.mem_iff_boolIndicator]
    change c.pairs[i.val] = p at hi
    change c.pairs[i.val].1.boolIndicator (diagonal u) =
      c.pairs[i.val].1.boolIndicator (diagonal v) at hs
    rw [hi] at hs
    rw [hs]
  change canonicalFilter (inequality V) e p.1 →
    canonicalFilter (inequality V) e p.2 → canonicalFilter (inequality V) e (p.1 ∩ p.2)
  simp only [e, canonicalFilter_inequality, Set.mem_inter_iff]
  tauto

/-- A canonical cover needs enough bit signatures to label all vertices. -/
private theorem card_le_two_pow_length_inequality
    (c : PairCover (inequality V) sources (canonicalClass (inequality V))) :
    Fintype.card V ≤ 2 ^ c.pairs.length := by
  simpa using Fintype.card_le_of_injective _ (inequality_signature_injective c)

/-- Every canonical cover of inequality on `2^n` vertices has at least `n` pairs. -/
theorem le_length_inequality {n : ℕ}
    (c : PairCover (inequality (Fin n → Bool)) sources
      (canonicalClass (inequality (Fin n → Bool)))) : n ≤ c.pairs.length := by
  have h := card_le_two_pow_length_inequality c
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h

private theorem exists_union_formula {U α : Type*} {m : ℕ}
    (input : Fin m → Set U) (s : Finset α) (f : α → Set U) (cost : α → ℕ)
    (h : ∀ a ∈ s, ∃ F : Formula Monotone.signature m,
      F.eval (Monotone.setInterpretation U) input = f a ∧ F.cost Monotone.andCost = cost a) :
    ∃ F : Formula Monotone.signature m,
      F.eval (Monotone.setInterpretation U) input = ⋃ a ∈ s, f a ∧
      F.cost Monotone.andCost = ∑ a ∈ s, cost a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨Monotone.const false, by simp [Monotone.const, Monotone.setInterpretation],
      by simp [Monotone.const]⟩
  | @insert a s ha ih =>
    obtain ⟨F, hF, cF⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨G, hG, cG⟩ := ih (fun a ha => h a (Finset.mem_insert_of_mem ha))
    refine ⟨Monotone.or F G, ?_, ?_⟩
    · simp [Monotone.or, Monotone.setInterpretation, hF, hG]
    · simp [Monotone.or, Fin.sum_univ_two, cF, cG, ha]

private theorem exists_coordinate_formula (P : V → Prop) (right : Bool) :
    ∃ F : Formula Monotone.signature (Fintype.card V + Fintype.card V),
      F.eval (Monotone.setInterpretation (V × V)) sources =
        {x | P (if right then x.2 else x.1)} ∧ F.cost Monotone.andCost = 0 := by
  classical
  let s := Finset.univ.filter P
  have h (v : V) (_ : v ∈ s) :
      ∃ F : Formula Monotone.signature (Fintype.card V + Fintype.card V),
        F.eval (Monotone.setInterpretation (V × V)) sources =
          {x | (if right then x.2 else x.1) = v} ∧ F.cost Monotone.andCost = 0 := by
    cases right
    · exact ⟨.input (Fin.castAdd _ (Fintype.equivFin V v)), row_source v, rfl⟩
    · exact ⟨.input (Fin.natAdd _ (Fintype.equivFin V v)), column_source v, rfl⟩
  obtain ⟨F, hF, cF⟩ := exists_union_formula sources s
    (fun v => {x | (if right then x.2 else x.1) = v}) (fun _ => 0) h
  refine ⟨F, ?_, by simpa using cF⟩
  rw [hF]
  ext x
  simp [s]

private theorem exists_bit_inequality_formula {n : ℕ} (i : Fin n) :
    ∃ F : Formula Monotone.signature
      (Fintype.card (Fin n → Bool) + Fintype.card (Fin n → Bool)),
      F.eval (Monotone.setInterpretation ((Fin n → Bool) × (Fin n → Bool))) sources =
        {x | x.1 i ≠ x.2 i} ∧ F.cost Monotone.andCost = 1 := by
  obtain ⟨L₁, hL₁, cL₁⟩ := exists_coordinate_formula (fun x : Fin n → Bool => x i = true) false
  obtain ⟨R₁, hR₁, cR₁⟩ := exists_coordinate_formula (fun x : Fin n → Bool => x i = true) true
  obtain ⟨L₀, hL₀, cL₀⟩ := exists_coordinate_formula (fun x : Fin n → Bool => x i = false) false
  obtain ⟨R₀, hR₀, cR₀⟩ := exists_coordinate_formula (fun x : Fin n → Bool => x i = false) true
  refine ⟨Monotone.and (Monotone.or L₁ R₁) (Monotone.or L₀ R₀), ?_, ?_⟩
  · simp only [Monotone.and, Monotone.or, Formula.eval_gate, Monotone.setInterpretation,
      Matrix.cons_val_zero, Matrix.cons_val_one, hL₁, hR₁, hL₀, hR₀, Bool.false_eq_true,
      ↓reduceIte]
    ext x
    change ((x.1 i = true ∨ x.2 i = true) ∧ (x.1 i = false ∨ x.2 i = false)) ↔
      x.1 i ≠ x.2 i
    cases x.1 i <;> cases x.2 i <;> simp
  · simp [Monotone.and, Monotone.or, Fin.sum_univ_two, cL₁, cR₁, cL₀, cR₀]

/-- Inequality of two `n`-bit vertices is constructed with exactly `n` AND gates. All supplied
rows/columns, constants and OR gates are free for this cost. Includes `n = 0`. -/
theorem exists_inequality_circuit (n : ℕ) :
    ∃ c : Circuit Monotone.signature
      (Fintype.card (Fin n → Bool) + Fintype.card (Fin n → Bool)) 1,
      c.eval (Monotone.setInterpretation ((Fin n → Bool) × (Fin n → Bool))) sources 0 =
        inequality (Fin n → Bool) ∧ c.program.cost Monotone.andCost = n := by
  obtain ⟨F, hF, cF⟩ := exists_union_formula sources (Finset.univ : Finset (Fin n))
    (fun i => {x : (Fin n → Bool) × (Fin n → Bool) | x.1 i ≠ x.2 i}) (fun _ => 1)
    (fun i _ => exists_bit_inequality_formula i)
  refine ⟨F.toCircuit, ?_, ?_⟩
  · rw [Formula.eval_toCircuit, hF]
    ext x
    simp [inequality, funext_iff]
  · rw [Formula.cost_toCircuit, cF]
    simp

/-- Proposition 40: canonical cover, full cover, and intersection complexity of inequality
on `2^n` vertices per side all equal `n`. -/
theorem inequality_complexities (n : ℕ) :
    pairCoverComplexity (inequality (Fin n → Bool)) sources
        (canonicalClass (inequality (Fin n → Bool))) = n ∧
    pairCoverComplexity (inequality (Fin n → Bool)) sources = n ∧
    ecomplexityFrom (Monotone.setInterpretation ((Fin n → Bool) × (Fin n → Bool)))
        Monotone.andCost (fun _ : Unit => fun _ : Fin 1 => inequality (Fin n → Bool))
        (fun _ : Unit => sources) = n := by
  have lower : (n : ℕ∞) ≤ pairCoverComplexity (inequality (Fin n → Bool)) sources
      (canonicalClass (inequality (Fin n → Bool))) :=
    le_pairCoverComplexity_iff.mpr fun c => by exact_mod_cast le_length_inequality c
  have canon := canonical_pairCoverComplexity_le (inequality (Fin n → Bool))
  have full := pairCoverComplexity_le_ecomplexityFrom (fun _ : Unit => sources)
    (fun _ : Unit => fun _ : Fin 1 => inequality (Fin n → Bool)) () 0
  obtain ⟨c, hc, cc⟩ := exists_inequality_circuit n
  have upper : ecomplexityFrom (Monotone.setInterpretation ((Fin n → Bool) × (Fin n → Bool)))
      Monotone.andCost (fun _ : Unit => fun _ : Fin 1 => inequality (Fin n → Bool))
      (fun _ : Unit => sources) ≤ n := by
    apply (ecomplexityFrom_le_of_computesFrom c ?_).trans_eq (congrArg (fun k : ℕ => (k : ℕ∞)) cc)
    intro _
    funext i
    have : i = 0 := Subsingleton.elim _ _
    simpa only [this] using hc
  exact ⟨le_antisymm (canon.trans (full.trans upper)) lower,
    le_antisymm (full.trans upper) (lower.trans canon),
    le_antisymm upper (lower.trans (canon.trans full))⟩

end Cslib.Circuits.Fusion.Graph
