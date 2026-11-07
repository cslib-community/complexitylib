/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CuttingPlanes
public import Complexity.Logics.Propositional.SemanticDerivation
import Complexity.Computability.Communication.BinarySearch
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Feasible interpolation for cutting planes

Let `Γ_A(x, y)` and `Γ_B(x, z)` be systems of integer linear inequalities over `n` shared variables
`x` and private variables `y` and `z`. Krajíček's interpolation theorem for cutting
planes [Krajíček, Theorem 6.4][Krajicek1997] says that a cutting planes refutation of
`Γ_A ∪ Γ_B` with `k` lines, all of whose coefficients are at most `M` in absolute value, gives a
circuit with `k · (M N) ^ O(1) · (M n) ^ O(log n)` gates, where `N` counts all variables, that is
true on every `u` with `Γ_A(u, q)` for some `q` and false on every `v` with `Γ_B(v, r)` for some
`r`. If the shared variables occur in `Γ_A` with nonnegative coefficients only, the circuit can be
taken monotone.

The proof goes through Krajíček's interpolation theorem for semantic derivations
(`Cslib.Logic.PL.IsSemanticRefutation.exists_circuit`). The solution sets of the lines of a
cutting planes refutation, read from its first line, form a semantic refutation of the cylinders
over the solution sets of `Γ_A` and `Γ_B`
(`Cslib.Logic.PL.CuttingPlanes.IsProof.isSemanticRefutation`): each rule has at most two premises
and is sound, and the axioms hold everywhere. The communication complexity of a line is small:

* Alice, holding `(u, q)`, and Bob, holding `(v, r)`, decide whether `(v, q, r)` satisfies a line
  when Alice sends the contribution of `q` to its left-hand side, an integer in `[-M |y|, M |y|]`,
  in `⌈log₂ (2 M |y| + 1)⌉` bits (`Cslib.Logic.PL.CuttingPlanes.ecomplexity_memRight_holds_le`);
* if `(u, q)` satisfies an inequality `E` of `Γ_A` and `(v, q)` does not, the contributions
  `Eᵢ uᵢ` of the shared variables add up to more than the `Eᵢ vᵢ`, and binary search
  (`Cslib.Communication.Protocol.exists_search_lt`) finds `i` with `Eᵢ vᵢ < Eᵢ uᵢ`, hence `uᵢ ≠ vᵢ`,
  in `⌈log₂ n⌉ (⌈log₂ (2 M₀ n + 1)⌉ + 1)` bits when the shared coefficients of `E` are at most `M₀`
  (`Cslib.Logic.PL.CuttingPlanes.ecomplexity_search_holds_le`). If `Eᵢ ≥ 0`, moreover `uᵢ = 1` and
  `vᵢ = 0`.

So for `t` at least both costs, a circuit with at most `(k · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates
interpolates (`Cslib.Logic.PL.CuttingPlanes.IsProof.exists_circuit`). Since `2 ^ t` is polynomial
in `M |y|` and `(M₀ n) ^ O(log n)`, this is the bound of Theorem 6.4.

## Main results

* `Cslib.Logic.PL.CuttingPlanes.IsProof.isSemanticRefutation`: cutting planes refutations are
  semantic refutations.
* `Cslib.Logic.PL.CuttingPlanes.ecomplexity_memRight_holds_le`,
  `Cslib.Logic.PL.CuttingPlanes.ecomplexity_search_holds_le`: the communication complexity of an
  inequality.
* `Cslib.Logic.PL.CuttingPlanes.IsProof.exists_circuit`,
  `Cslib.Logic.PL.CuttingPlanes.IsProof.exists_monotone_circuit`: interpolation, with separate
  bounds on the shared coefficients of `Γ_A` and on the coefficients of `y` in the refutation.
* `Cslib.Logic.PL.CuttingPlanes.IsProof.exists_circuit_of_abs_coeff_le`,
  `Cslib.Logic.PL.CuttingPlanes.IsProof.exists_monotone_circuit_of_abs_coeff_le`:
  **Krajíček's interpolation theorem for cutting planes** [Krajíček, Theorem 6.4][Krajicek1997],
  for refutations all of whose coefficients are at most `M` in absolute value.

## Implementation notes

* The systems are sets of inequalities over `Fin n ⊕ Y` and `Fin n ⊕ Z`, renamed into
  `Fin n ⊕ (Y ⊕ Z)` along `Sum.map id Sum.inl` and `Sum.map id Sum.inr` (`Ineq.relabel`), the
  layout of `Cslib.Logic.PL.CNF.appendShared`. The private variables range over finite types.
* The protocol of `IsSemanticRefutation.exists_dagProtocol` decides membership of `(v, q, r)` at
  every line and searches only at inequalities of `Γ_A`, so only the coefficients of `y` in the
  refutation (bounded by `M`) and the shared coefficients of `Γ_A` (bounded by `M₀`) matter. For
  translations of clauses `M₀ = 1`. Theorem 6.4 bounds every coefficient of the refutation by `M`;
  the `_of_abs_coeff_le` forms take this hypothesis and discard the inequalities of `Γ_A` that the
  refutation does not use (`CuttingPlanes.IsProof.restrict`).
* In the monotone case the search runs only at inequalities of `Γ_A`, whose shared coefficients
  are nonnegative, so Krajíček's second case (a coordinate of `u` that can be raised) does not
  arise.
* Only the monotone case for `Γ_A` is stated; Theorem 6.4 also has the case in which the shared
  variables occur in `Γ_B` with nonpositive coefficients only, which needs the monotone case of the
  interpolation theorem for semantic derivations with respect to `V`.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*, Theorem 6.4][Krajicek1997]
-/

public section

open Finset Cslib.Communication Cslib.Circuits Cslib.Logic.PL.SemanticDerivation

namespace Cslib.Logic.PL

namespace CuttingPlanes

/-! ### Cutting planes refutations as semantic refutations -/

section Semantic

variable {V : Type*}

/-- Line `j` of a proof read from its first line is in `Γ`, holds everywhere, or follows
semantically from two earlier lines. -/
private def LineOK (Γ : Set (Ineq V)) (L : List (Ineq V)) (j : ℕ) (I : Ineq V) : Prop :=
  I ∈ Γ ∨ (∀ σ, I.Holds σ) ∨ ∃ j₁ j₂ I₁ I₂, j₁ < j ∧ j₂ < j ∧ L[j₁]? = some I₁ ∧
    L[j₂]? = some I₂ ∧ ∀ σ, I₁.Holds σ → I₂.Holds σ → I.Holds σ

private theorem LineOK.append {Γ : Set (Ineq V)} {L : List (Ineq V)} {j : ℕ} {I : Ineq V}
    (h : LineOK Γ L j I) (hj : j < L.length) (L' : List (Ineq V)) : LineOK Γ (L ++ L') j I := by
  rcases h with h | h | ⟨j₁, j₂, I₁, I₂, h₁, h₂, e₁, e₂, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨j₁, j₂, I₁, I₂, h₁, h₂, ?_, ?_, h⟩)
    · rw [List.getElem?_append_left (by omega), e₁]
    · rw [List.getElem?_append_left (by omega), e₂]

/-- An earlier line of a proof has a smaller index when the proof is read from its first line. -/
private theorem exists_lt_of_mem {ls : List (Ineq V)} {I J : Ineq V} (hI : I ∈ ls) :
    ∃ j < ls.length, (ls.reverse ++ [J])[j]? = some I := by
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem (List.mem_reverse.2 hI)
  refine ⟨j, by simpa using hj, ?_⟩
  rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, e]

private theorem lineOK_of_isProof {Γ : Set (Ineq V)} {ls : List (Ineq V)} (h : IsProof Γ ls)
    {j : ℕ} {I : Ineq V} (hj : ls.reverse[j]? = some I) : LineOK Γ ls.reverse j I := by
  induction h generalizing j I with
  | @hyp ls J h hJ ih | @nonneg ls h v ih | @leOne ls h v ih | @add ls I₁ I₂ h hI₁ hI₂ ih
  | @smul ls I₁ h c hc hI₁ ih | @div ls I₁ h c hc hdvd hI₁ ih =>
    rw [List.reverse_cons] at hj ⊢
    by_cases hjl : j < ls.length
    · rw [List.getElem?_append_left (by simpa using hjl)] at hj
      exact (ih hj).append (by simpa using hjl) _
    · have hjl' : j = ls.length := by
        have := (List.getElem?_eq_some_iff.1 hj).1
        simp only [List.length_append, List.length_reverse, List.length_singleton] at this
        omega
      subst hjl'
      rw [List.getElem?_append_right (by simp)] at hj
      simp only [List.length_reverse, Nat.sub_self, List.getElem?_cons_zero,
        Option.some.injEq] at hj
      subst hj
      first
      | exact Or.inl hJ
      | exact Or.inr (Or.inl fun σ => Ineq.holds_nonneg σ v)
      | exact Or.inr (Or.inl fun σ => Ineq.holds_leOne σ v)
      | obtain ⟨j₁, hj₁, e₁⟩ := exists_lt_of_mem (J := I₁ + I₂) hI₁
        obtain ⟨j₂, hj₂, e₂⟩ := exists_lt_of_mem (J := I₁ + I₂) hI₂
        exact Or.inr (Or.inr ⟨j₁, j₂, I₁, I₂, hj₁, hj₂, e₁, e₂, fun σ h₁ h₂ => h₁.add h₂⟩)
      | obtain ⟨j₁, hj₁, e₁⟩ := exists_lt_of_mem (J := c • I₁) hI₁
        exact Or.inr (Or.inr ⟨j₁, j₁, I₁, I₁, hj₁, hj₁, e₁, e₁, fun σ h₁ _ => h₁.nsmul c⟩)
      | obtain ⟨j₁, hj₁, e₁⟩ := exists_lt_of_mem (J := I₁.div c) hI₁
        exact Or.inr (Or.inr ⟨j₁, j₁, I₁, I₁, hj₁, hj₁, e₁, e₁, fun σ h₁ _ => h₁.div hc hdvd⟩)
  | nil => simp at hj

variable {X Y Z : Type*}

/-- The solution set of an inequality over the shared variables and those of `Γ_A`, renamed into
all variables, is the cylinder over its solution set. -/
theorem setOf_holds_relabel_inl (E : Ineq (X ⊕ Y)) :
    {σ : X ⊕ (Y ⊕ Z) → Bool | (E.relabel (Sum.map id Sum.inl)).Holds σ} =
      leftCylinder {σ | E.Holds σ} := by
  ext σ
  simp [leftCylinder]

/-- The solution set of an inequality over the shared variables and those of `Γ_B`, renamed into
all variables, is the cylinder over its solution set. -/
theorem setOf_holds_relabel_inr (E : Ineq (X ⊕ Z)) :
    {σ : X ⊕ (Y ⊕ Z) → Bool | (E.relabel (Sum.map id Sum.inr)).Holds σ} =
      rightCylinder {σ | E.Holds σ} := by
  ext σ
  simp [rightCylinder]

/-- **Cutting planes refutations are semantic refutations** [Krajíček, Section 6][Krajicek1997].
The solution sets of the lines of a cutting planes refutation of `Γ_A(x, y) ∪ Γ_B(x, z)`, read
from the first line, form a semantic refutation of the cylinders over the solution sets of the
inequalities of `Γ_A` and of `Γ_B`, with as many lines. -/
theorem IsProof.isSemanticRefutation {ΓA : Set (Ineq (X ⊕ Y))} {ΓB : Set (Ineq (X ⊕ Z))}
    {ls : List (Ineq (X ⊕ (Y ⊕ Z)))}
    (h : IsProof (Ineq.relabel (Sum.map id Sum.inl) '' ΓA ∪
      Ineq.relabel (Sum.map id Sum.inr) '' ΓB) ls) (hc : Ineq.contra ∈ ls) :
    IsSemanticRefutation (initSets ((fun E => {σ | E.Holds σ}) '' ΓA)
      ((fun E => {σ | E.Holds σ}) '' ΓB)) fun j : Fin ls.reverse.length =>
        {σ | ls.reverse[j].Holds σ} := by
  refine ⟨fun j => ?_, ?_⟩
  · rcases lineOK_of_isProof h (List.getElem?_eq_getElem j.2) with
      (⟨E, hE, he⟩ | ⟨E, hE, he⟩) | hu | ⟨j₁, j₂, I₁, I₂, h₁, h₂, e₁, e₂, himp⟩
    · refine Or.inl (Or.inl ⟨_, ⟨E, hE, rfl⟩, ?_⟩)
      rw [← setOf_holds_relabel_inl, he]
      rfl
    · refine Or.inl (Or.inr ⟨_, ⟨E, hE, rfl⟩, ?_⟩)
      rw [← setOf_holds_relabel_inr, he]
      rfl
    · exact Or.inr (Or.inl (Set.eq_univ_of_forall hu))
    · obtain ⟨hj₁, e₁⟩ := List.getElem?_eq_some_iff.1 e₁
      obtain ⟨hj₂, e₂⟩ := List.getElem?_eq_some_iff.1 e₂
      refine Or.inr (Or.inr ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩, h₁, h₂, fun σ hσ => ?_⟩)
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Fin.getElem_fin, e₁, e₂] at hσ ⊢
      exact himp σ hσ.1 hσ.2
  · obtain ⟨j, hj, e⟩ := List.getElem_of_mem (List.mem_reverse.2 hc)
    refine ⟨⟨j, hj⟩, Set.eq_empty_of_forall_notMem fun σ hσ => ?_⟩
    simp only [Set.mem_ofPred_eq, Fin.getElem_fin, e] at hσ
    exact Ineq.not_holds_contra σ hσ

/-- The models of the solution sets of a system of inequalities are its 0/1 solutions. -/
theorem mem_models_iff {Γ : Set (Ineq (X ⊕ Y))} {u : X → Bool} {q : Y → Bool} :
    (u, q) ∈ Models ((fun E => {σ | E.Holds σ}) '' Γ) ↔ ∀ E ∈ Γ, E.Holds (Sum.elim u q) := by
  simp [Models]

end Semantic

/-! ### The communication complexity of an inequality -/

section Communication

variable {n : ℕ} {Y Z : Type*}

/-- A weighted sum of 0/1 values with weights at most `M` in absolute value is at most `M` times
the number of terms in absolute value. -/
private theorem abs_sum_mul_toInt_le {ι : Type*} [Fintype ι] {a : ι → ℤ} {M : ℕ}
    (ha : ∀ i, |a i| ≤ M) (σ : ι → Bool) : |∑ i, a i * (σ i).toInt| ≤ M * Fintype.card ι := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i ∈ (univ : Finset ι), |a i * (σ i).toInt| ≤ M := fun i _ => by
    rw [abs_mul]
    cases σ i <;> simp [ha i]
  simpa [mul_comm] using sum_le_sum this

private theorem abs_list_sum_le {ι : Type*} (h : ι → ℤ) {M : ℕ} (hh : ∀ i, |h i| ≤ M)
    (l : List ι) : |(l.map h).sum| ≤ M * l.length := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    refine (abs_add_le _ _).trans ?_
    push_cast
    linarith [hh i]

/-- `(v, q, r)` satisfies an inequality over all variables. -/
private theorem holds_sum_elim_sum_elim_iff [Fintype Y] [Fintype Z] (I : Ineq (Fin n ⊕ (Y ⊕ Z)))
    (v : Fin n → Bool) (q : Y → Bool) (r : Z → Bool) :
    I.Holds (Sum.elim v (Sum.elim q r)) ↔
      I.bound ≤ (∑ i, I.coeff (.inl i) * (v i).toInt + ∑ z, I.coeff (.inr (.inr z)) *
        (r z).toInt) + ∑ y, I.coeff (.inr (.inl y)) * (q y).toInt := by
  rw [Ineq.Holds, Ineq.lhs_eq_sum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  constructor <;> intro h <;> linarith

/-- `(u, q)` satisfies an inequality over the shared variables and those of `Γ_A`. -/
private theorem holds_sum_elim_iff [Fintype Y] (E : Ineq (Fin n ⊕ Y)) (u : Fin n → Bool)
    (q : Y → Bool) :
    E.Holds (Sum.elim u q) ↔ E.bound ≤ ∑ i, E.coeff (.inl i) * (u i).toInt +
      ∑ y, E.coeff (.inr y) * (q y).toInt := by
  rw [Ineq.Holds, Ineq.lhs_eq_sum, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]

/-- **Deciding a line** [Krajíček, proof of Theorem 6.4][Krajicek1997]. If the coefficients of the
variables `y` of Alice in an inequality are at most `M` in absolute value, Alice holding `(u, q)`
and Bob holding `(v, r)` decide whether `(v, q, r)` satisfies it with
`⌈log₂ (2 M |y| + 1)⌉ + 1` bits: Alice sends the contribution of `q` to the left-hand side, and Bob
answers. -/
theorem ecomplexity_memRight_holds_le [Fintype Y] [Finite Z] (I : Ineq (Fin n ⊕ (Y ⊕ Z)))
    {M : ℕ} (hM : ∀ y, |I.coeff (.inr (.inl y))| ≤ M) (A : Set ((Fin n → Bool) × (Y → Bool)))
    (B : Set ((Fin n → Bool) × (Z → Bool))) :
    Protocol.ecomplexity (Decides (MemRight {σ | I.Holds σ})) A B ≤
      Nat.clog 2 (2 * M * Fintype.card Y + 1) + 1 := by
  classical
  have := Fintype.ofFinite Z
  refine Protocol.ecomplexity_decides_le.trans ?_
  set K : ℕ := M * Fintype.card Y with hK
  have h := Protocol.ecomplexityFun_le_clog_card_finset_succ (Finset.Icc (-(K : ℤ)) K)
    (fun a : (Fin n → Bool) × (Y → Bool) => ∑ y, I.coeff (.inr (.inl y)) * (a.2 y).toInt)
    (fun a => Finset.mem_Icc.2 (abs_le.1 (abs_sum_mul_toInt_le hM a.2)))
    (fun w (b : (Fin n → Bool) × (Z → Bool)) => decide (I.bound ≤
      (∑ i, I.coeff (.inl i) * (b.1 i).toInt + ∑ z, I.coeff (.inr (.inr z)) * (b.2 z).toInt) + w))
  have hcard : (Finset.Icc (-(K : ℤ)) K).card = 2 * M * Fintype.card Y + 1 := by
    rw [Int.card_Icc]
    have : (2 * M * Fintype.card Y + 1 : ℕ) = 2 * K + 1 := by rw [hK]; ring
    rw [this]
    omega
  rw [hcard] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  funext a b
  simp only [MemRight, Set.mem_ofPred_eq, holds_sum_elim_sum_elim_iff]

/-- **The search at an inequality of `Γ_A`** [Krajíček, proof of Theorem 6.4][Krajicek1997]. Let
`E` be an inequality over the shared variables and the variables of Alice whose shared
coefficients are at most `M₀` in absolute value, and let `R u v i` hold whenever
`Eᵢ vᵢ < Eᵢ uᵢ`. If `(u, q)` satisfies `E` and `(v, q)` does not, Alice holding `(u, q)` and Bob
holding `(v, r)` find `i` with `R u v i` with `⌈log₂ n⌉ (⌈log₂ (2 M₀ n + 1)⌉ + 1)` bits, by binary
search on the contributions of the shared variables. -/
theorem ecomplexity_search_holds_le [Finite Y] (E : Ineq (Fin n ⊕ Y)) {M₀ : ℕ}
    (hM₀ : ∀ i, |E.coeff (.inl i)| ≤ M₀) {R : (Fin n → Bool) → (Fin n → Bool) → Fin n → Prop}
    (hR : ∀ u v i, E.coeff (.inl i) * (v i).toInt < E.coeff (.inl i) * (u i).toInt → R u v i)
    (A : Set ((Fin n → Bool) × (Y → Bool))) (B : Set ((Fin n → Bool) × (Z → Bool))) :
    Protocol.ecomplexity (Search {σ | E.Holds σ} R) A B ≤
      Nat.clog 2 n * (Nat.clog 2 (2 * M₀ * n + 1) + 1) := by
  classical
  have := Fintype.ofFinite Y
  set f : (Fin n → Bool) × (Y → Bool) → Fin n → ℤ := fun a i => E.coeff (.inl i) * (a.1 i).toInt
  set g : (Fin n → Bool) × (Z → Bool) → Fin n → ℤ := fun b i => E.coeff (.inl i) * (b.1 i).toInt
  have hf : ∀ a i, |f a i| ≤ M₀ := fun a i => by
    simp only [f, abs_mul]
    cases a.1 i <;> simp [hM₀ i]
  have hcmp : ∀ l : List (Fin n), l.length ≤ n → ∃ p : Protocol _ _ Bool,
      p.depth ≤ Nat.clog 2 (2 * M₀ * n + 1) + 1 ∧
        ∀ a b, p.run a b = true ↔ (l.map (g b)).sum < (l.map (f a)).sum := by
    intro l hl
    set K : ℕ := M₀ * n with hK
    have hmem : ∀ a, (l.map (f a)).sum ∈ Finset.Icc (-(K : ℤ)) K := fun a => by
      refine Finset.mem_Icc.2 (abs_le.1 ((abs_list_sum_le _ (hf a) l).trans ?_))
      rw [hK]; push_cast
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hl) (Nat.cast_nonneg _)
    have h := Protocol.ecomplexityFun_le_clog_card_finset_succ (Finset.Icc (-(K : ℤ)) K)
      (fun a => (l.map (f a)).sum) hmem fun w b => decide ((l.map (g b)).sum < w)
    have hcard : (Finset.Icc (-(K : ℤ)) K).card = 2 * M₀ * n + 1 := by
      rw [Int.card_Icc]
      have : (2 * M₀ * n + 1 : ℕ) = 2 * K + 1 := by rw [hK]; ring
      rw [this]
      omega
    rw [hcard] at h
    obtain ⟨p, hp, hd⟩ := Protocol.ecomplexityFun_le_iff.1 (by exact_mod_cast h)
    refine ⟨p, hd, fun a b => ?_⟩
    rw [hp]
    simp
  obtain ⟨p, hd, hp⟩ := Protocol.exists_search_lt f g n _ hcmp (List.finRange n) (by simp)
  rw [List.length_finRange] at hd
  refine (Protocol.ecomplexity_le_depth (p := p) ?_).trans (by exact_mod_cast hd)
  intro a _ b _ h₁ h₂
  simp only [Set.mem_ofPred_eq, holds_sum_elim_iff] at h₁ h₂
  have hlt : ((List.finRange n).map (g b)).sum < ((List.finRange n).map (f a)).sum := by
    simp only [f, g, ← Fin.sum_univ_def]
    linarith
  obtain ⟨i, hi, hgi⟩ := hp a b hlt
  exact ⟨i, hi, hR _ _ _ hgi⟩

/-- A drop in the contribution of a shared variable is a coordinate where the inputs differ. -/
private theorem differsAt_of_mul_toInt_lt {a : ℤ} {u v : Fin n → Bool} {i : Fin n}
    (h : a * (v i).toInt < a * (u i).toInt) : DiffersAt u v i := by
  intro he
  rw [he] at h
  exact lt_irrefl _ h

/-- With a nonnegative coefficient, a drop in the contribution of a shared variable is a
coordinate where it is one for Alice and zero for Bob. -/
private theorem exceedsAt_of_mul_toInt_lt {a : ℤ} (ha : 0 ≤ a) {u v : Fin n → Bool} {i : Fin n}
    (h : a * (v i).toInt < a * (u i).toInt) : ExceedsAt u v i := by
  cases hu : u i <;> cases hv : v i <;> simp_all [ExceedsAt]
  all_goals omega

end Communication

/-! ### Interpolation -/

variable {n : ℕ} {Y Z : Type*}

/-- **Interpolation for cutting planes**, with separate coefficient bounds
[Krajíček, Theorem 6.4][Krajicek1997]. Let `ls` be a cutting planes refutation of
`Γ_A(x, y) ∪ Γ_B(x, z)` over `n` shared variables. Suppose that the shared coefficients of `Γ_A`
are at most `M₀`, and the coefficients of the variables `y` in `ls` at most `M`, in absolute value,
and that `t` is at least `⌈log₂ (2 M |y| + 1)⌉ + 1` and `⌈log₂ n⌉ (⌈log₂ (2 M₀ n + 1)⌉ + 1)`.
Then a circuit with at most `(|ls| · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates is true on every `u`
with `Γ_A(u, q)` for some `q` and false on every `v` with `Γ_B(v, r)` for some `r`. -/
theorem IsProof.exists_circuit [Fintype Y] [Finite Z] {ΓA : Set (Ineq (Fin n ⊕ Y))}
    {ΓB : Set (Ineq (Fin n ⊕ Z))} {ls : List (Ineq (Fin n ⊕ (Y ⊕ Z)))}
    (h : IsProof (Ineq.relabel (Sum.map id Sum.inl) '' ΓA ∪
      Ineq.relabel (Sum.map id Sum.inr) '' ΓB) ls) (hc : Ineq.contra ∈ ls) {M₀ M t : ℕ}
    (hM₀ : ∀ E ∈ ΓA, ∀ i, |E.coeff (.inl i)| ≤ M₀)
    (hM : ∀ I ∈ ls, ∀ y, |I.coeff (.inr (.inl y))| ≤ M)
    (ht₂ : Nat.clog 2 (2 * M * Fintype.card Y + 1) + 1 ≤ t)
    (ht₃ : Nat.clog 2 n * (Nat.clog 2 (2 * M₀ * n + 1) + 1) ≤ t) :
    ∃ C : Circuit Boolean.signature n 1,
      C.size ≤ (ls.length * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) ∧
      (∀ u q, (∀ E ∈ ΓA, E.Holds (Sum.elim u q)) → C.eval Boolean.interpretation u 0 = true) ∧
      ∀ v r, (∀ E ∈ ΓB, E.Holds (Sum.elim v r)) → C.eval Boolean.interpretation v 0 = false := by
  obtain ⟨C, hsize, hU, hV⟩ := (h.isSemanticRefutation hc).exists_circuit (t := t)
    (fun j => (ecomplexity_memRight_holds_le _ (hM _ (List.mem_reverse.1 (List.getElem_mem _)))
      _ _).trans (by exact_mod_cast ht₂))
    (fun j S hS _ => by
      obtain ⟨E, hE, rfl⟩ := hS
      exact (ecomplexity_search_holds_le E (hM₀ E hE) (fun _ _ _ => differsAt_of_mul_toInt_lt)
        _ _).trans (by exact_mod_cast ht₃))
  rw [List.length_reverse] at hsize
  exact ⟨C, hsize, fun u q hq => hU u q (mem_models_iff.2 hq),
    fun v r hr => hV v r (mem_models_iff.2 hr)⟩

/-- **Monotone interpolation for cutting planes**, with separate coefficient bounds
[Krajíček, Theorem 6.4][Krajicek1997]. If moreover the shared variables occur in `Γ_A` with
nonnegative coefficients only, the circuit of `CuttingPlanes.IsProof.exists_circuit` can be taken
monotone. -/
theorem IsProof.exists_monotone_circuit [Fintype Y] [Finite Z] {ΓA : Set (Ineq (Fin n ⊕ Y))}
    {ΓB : Set (Ineq (Fin n ⊕ Z))} {ls : List (Ineq (Fin n ⊕ (Y ⊕ Z)))}
    (h : IsProof (Ineq.relabel (Sum.map id Sum.inl) '' ΓA ∪
      Ineq.relabel (Sum.map id Sum.inr) '' ΓB) ls) (hc : Ineq.contra ∈ ls) {M₀ M t : ℕ}
    (hpos : ∀ E ∈ ΓA, ∀ i, 0 ≤ E.coeff (.inl i))
    (hM₀ : ∀ E ∈ ΓA, ∀ i, |E.coeff (.inl i)| ≤ M₀)
    (hM : ∀ I ∈ ls, ∀ y, |I.coeff (.inr (.inl y))| ≤ M)
    (ht₂ : Nat.clog 2 (2 * M * Fintype.card Y + 1) + 1 ≤ t)
    (ht₃ : Nat.clog 2 n * (Nat.clog 2 (2 * M₀ * n + 1) + 1) ≤ t) :
    ∃ C : Circuit Monotone.signature n 1,
      C.size ≤ (ls.length * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) ∧
      (∀ u q, (∀ E ∈ ΓA, E.Holds (Sum.elim u q)) → C.eval Monotone.interpretation u 0 = true) ∧
      ∀ v r, (∀ E ∈ ΓB, E.Holds (Sum.elim v r)) → C.eval Monotone.interpretation v 0 = false := by
  obtain ⟨C, hsize, hU, hV⟩ := (h.isSemanticRefutation hc).exists_monotone_circuit (t := t)
    (fun j => (ecomplexity_memRight_holds_le _ (hM _ (List.mem_reverse.1 (List.getElem_mem _)))
      _ _).trans (by exact_mod_cast ht₂))
    (fun j S hS _ => by
      obtain ⟨E, hE, rfl⟩ := hS
      exact (ecomplexity_search_holds_le E (hM₀ E hE)
        (fun _ _ i => exceedsAt_of_mul_toInt_lt (hpos E hE i)) _ _).trans
          (by exact_mod_cast ht₃))
  rw [List.length_reverse] at hsize
  exact ⟨C, hsize, fun u q hq => hU u q (mem_models_iff.2 hq),
    fun v r hr => hV v r (mem_models_iff.2 hr)⟩

/-- A refutation of `Γ_A ∪ Γ_B` is a refutation of `Γ'_A ∪ Γ_B`, where `Γ'_A` consists of the
inequalities of `Γ_A` used in it. -/
private theorem isProof_restrict_left {X : Type*} {ΓA : Set (Ineq (X ⊕ Y))}
    {ΓB : Set (Ineq (X ⊕ Z))} {ls : List (Ineq (X ⊕ (Y ⊕ Z)))}
    (h : IsProof (Ineq.relabel (Sum.map id Sum.inl) '' ΓA ∪
      Ineq.relabel (Sum.map id Sum.inr) '' ΓB) ls) :
    IsProof (Ineq.relabel (Sum.map id Sum.inl) ''
      {E | E ∈ ΓA ∧ E.relabel (Sum.map id Sum.inl) ∈ ls} ∪
      Ineq.relabel (Sum.map id Sum.inr) '' ΓB) ls := by
  refine h.restrict.mono ?_
  rintro I ⟨⟨E, hE, rfl⟩ | hI, hls⟩
  · exact Or.inl ⟨E, ⟨hE, hls⟩, rfl⟩
  · exact Or.inr hI

/-- The shared coefficients of an inequality of `Γ_A` used in `ls` are coefficients of `ls`. -/
private theorem abs_coeff_le_of_relabel_mem {X : Type*} {ls : List (Ineq (X ⊕ (Y ⊕ Z)))} {M : ℕ}
    (hM : ∀ I ∈ ls, ∀ w, |I.coeff w| ≤ M) {E : Ineq (X ⊕ Y)}
    (hE : E.relabel (Sum.map id Sum.inl) ∈ ls) (x : X) : |E.coeff (.inl x)| ≤ M := by
  have := hM _ hE (.inl x)
  rwa [show (Sum.inl x : X ⊕ (Y ⊕ Z)) = Sum.map id Sum.inl (.inl x) from rfl,
    Ineq.coeff_relabel_apply (Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩)]
    at this

/-- **Krajíček's interpolation theorem for cutting planes** [Krajíček, Theorem 6.4][Krajicek1997].
If a cutting planes refutation `ls` of `Γ_A(x, y) ∪ Γ_B(x, z)` over `n` shared variables has all
coefficients at most `M` in absolute value, and `t` is at least `⌈log₂ (2 M |y| + 1)⌉ + 1` and
`⌈log₂ n⌉ (⌈log₂ (2 M n + 1)⌉ + 1)`, then a circuit with at most
`(|ls| · 2 ^ (2 t) + 1) · 2 ^ (2 t + 1)` gates is true on every `u` with `Γ_A(u, q)` for some `q`
and false on every `v` with `Γ_B(v, r)` for some `r`. -/
theorem IsProof.exists_circuit_of_abs_coeff_le [Fintype Y] [Finite Z]
    {ΓA : Set (Ineq (Fin n ⊕ Y))} {ΓB : Set (Ineq (Fin n ⊕ Z))}
    {ls : List (Ineq (Fin n ⊕ (Y ⊕ Z)))}
    (h : IsProof (Ineq.relabel (Sum.map id Sum.inl) '' ΓA ∪
      Ineq.relabel (Sum.map id Sum.inr) '' ΓB) ls) (hc : Ineq.contra ∈ ls) {M t : ℕ}
    (hM : ∀ I ∈ ls, ∀ w, |I.coeff w| ≤ M)
    (ht₂ : Nat.clog 2 (2 * M * Fintype.card Y + 1) + 1 ≤ t)
    (ht₃ : Nat.clog 2 n * (Nat.clog 2 (2 * M * n + 1) + 1) ≤ t) :
    ∃ C : Circuit Boolean.signature n 1,
      C.size ≤ (ls.length * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) ∧
      (∀ u q, (∀ E ∈ ΓA, E.Holds (Sum.elim u q)) → C.eval Boolean.interpretation u 0 = true) ∧
      ∀ v r, (∀ E ∈ ΓB, E.Holds (Sum.elim v r)) → C.eval Boolean.interpretation v 0 = false := by
  obtain ⟨C, hsize, hU, hV⟩ := (isProof_restrict_left h).exists_circuit hc
    (fun E hE i => abs_coeff_le_of_relabel_mem hM hE.2 i) (fun I hI y => hM I hI _) ht₂ ht₃
  exact ⟨C, hsize, fun u q hq => hU u q fun E hE => hq E hE.1, hV⟩

/-- **Krajíček's monotone interpolation theorem for cutting planes**
[Krajíček, Theorem 6.4][Krajicek1997]. If moreover the shared variables occur in `Γ_A` with
nonnegative coefficients only, the circuit of
`CuttingPlanes.IsProof.exists_circuit_of_abs_coeff_le` can be taken monotone. -/
theorem IsProof.exists_monotone_circuit_of_abs_coeff_le [Fintype Y] [Finite Z]
    {ΓA : Set (Ineq (Fin n ⊕ Y))} {ΓB : Set (Ineq (Fin n ⊕ Z))}
    {ls : List (Ineq (Fin n ⊕ (Y ⊕ Z)))}
    (h : IsProof (Ineq.relabel (Sum.map id Sum.inl) '' ΓA ∪
      Ineq.relabel (Sum.map id Sum.inr) '' ΓB) ls) (hc : Ineq.contra ∈ ls) {M t : ℕ}
    (hpos : ∀ E ∈ ΓA, ∀ i, 0 ≤ E.coeff (.inl i))
    (hM : ∀ I ∈ ls, ∀ w, |I.coeff w| ≤ M)
    (ht₂ : Nat.clog 2 (2 * M * Fintype.card Y + 1) + 1 ≤ t)
    (ht₃ : Nat.clog 2 n * (Nat.clog 2 (2 * M * n + 1) + 1) ≤ t) :
    ∃ C : Circuit Monotone.signature n 1,
      C.size ≤ (ls.length * 2 ^ (2 * t) + 1) * 2 ^ (2 * t + 1) ∧
      (∀ u q, (∀ E ∈ ΓA, E.Holds (Sum.elim u q)) → C.eval Monotone.interpretation u 0 = true) ∧
      ∀ v r, (∀ E ∈ ΓB, E.Holds (Sum.elim v r)) → C.eval Monotone.interpretation v 0 = false := by
  obtain ⟨C, hsize, hU, hV⟩ := (isProof_restrict_left h).exists_monotone_circuit hc
    (fun E hE i => hpos E hE.1 i) (fun E hE i => abs_coeff_le_of_relabel_mem hM hE.2 i)
    (fun I hI y => hM I hI _) ht₂ ht₃
  exact ⟨C, hsize, fun u q hq => hU u q fun E hE => hq E hE.1, hV⟩

end CuttingPlanes

end Cslib.Logic.PL
