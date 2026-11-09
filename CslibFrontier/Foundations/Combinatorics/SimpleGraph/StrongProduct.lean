/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Prod.lean`, see mathlib4#43170)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.IndepNum
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Strong products of simple graphs and the independence number

The *strong product* `G ⊠ H` of simple graphs `G` on `V` and `H` on `W` is the graph on `V × W`
in which two distinct vertices are adjacent when each coordinate is equal or adjacent. The
*strong power* `G.strongPow k` is the analogous graph on words `Fin k → V`. In Shannon's
zero-error model, `G` is the confusability graph of a channel, `G.strongPow k` is the
confusability graph of words of length `k`, and an independent set of `G.strongPow k` is a
zero-error code of block length `k` [Shannon1956].

The independence number is supermultiplicative under the strong product: a product of
independent sets is independent (`SimpleGraph.indepNum_mul_le_indepNum_strongProd`). Since
`G.strongPow (m + n) ≃g G.strongPow m ⊠ G.strongPow n` (`SimpleGraph.strongPowAddIso`) and the
independence number is invariant under isomorphism (`SimpleGraph.Iso.indepNum_eq`), the
independence numbers of the strong powers are supermultiplicative
(`SimpleGraph.indepNum_strongPow_add`).

The notation `⊠` is scoped to `SimpleGraph` (use `open SimpleGraph`) because `CategoryTheory`
uses the same symbol. The name and notation follow the open Mathlib pull request
[mathlib4#43170](https://github.com/leanprover-community/mathlib4/pull/43170), which defines
`G ⊠ H` as `G □ H ⊔ G ×g H` in `Mathlib/Combinatorics/SimpleGraph/Prod.lean`; here the adjacency
is stated directly.

## Main definitions

* `SimpleGraph.strongProd`, notation `G ⊠ H`: the strong product.
* `SimpleGraph.strongPow`: the `k`-th strong power on `Fin k → V`.
* `SimpleGraph.strongPowAddIso`: `G.strongPow (m + n) ≃g G.strongPow m ⊠ G.strongPow n`.

## Main results

* `SimpleGraph.indepNum_mul_le_indepNum_strongProd`: `α(G) α(H) ≤ α(G ⊠ H)`.
* `SimpleGraph.indepNum_strongPow_add`: `α(Gᵐ) α(Gⁿ) ≤ α(Gᵐ⁺ⁿ)`.
* `SimpleGraph.indepNum_strongPow_le`: `α(Gᵏ) ≤ |V| ^ k`.

## References

* [C. E. Shannon, *The zero error capacity of a noisy channel*][Shannon1956]
-/

public section

open Finset

namespace SimpleGraph

variable {V W X : Type*}

/-- The strong product of `G` and `H`: distinct pairs are adjacent when each coordinate is equal or
adjacent. -/
@[expose] def strongProd (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) where
  Adj x y := x ≠ y ∧ (x.1 = y.1 ∨ G.Adj x.1 y.1) ∧ (x.2 = y.2 ∨ H.Adj x.2 y.2)
  symm := ⟨fun _ _ ⟨hne, h₁, h₂⟩ =>
    ⟨hne.symm, h₁.imp Eq.symm fun h => h.symm, h₂.imp Eq.symm fun h => h.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[inherit_doc] scoped infixl:70 " ⊠ " => strongProd

variable {G : SimpleGraph V} {H : SimpleGraph W}

@[simp]
theorem strongProd_adj {x y : V × W} :
    (G ⊠ H).Adj x y ↔ x ≠ y ∧ (x.1 = y.1 ∨ G.Adj x.1 y.1) ∧ (x.2 = y.2 ∨ H.Adj x.2 y.2) :=
  Iff.rfl

instance [DecidableEq V] [DecidableEq W] [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G ⊠ H).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The `k`-th strong power of `G`, on words of length `k`: distinct words are adjacent when they
are equal or adjacent in every coordinate. -/
@[expose] def strongPow (G : SimpleGraph V) (k : ℕ) : SimpleGraph (Fin k → V) where
  Adj x y := x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, fun i => (h i).imp Eq.symm fun h => h.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp]
theorem strongPow_adj {k : ℕ} {x y : Fin k → V} :
    (G.strongPow k).Adj x y ↔ x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i) :=
  Iff.rfl

instance [DecidableEq V] [DecidableRel G.Adj] {k : ℕ} : DecidableRel (G.strongPow k).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem eq_or_strongProd_adj {x y : V × W} :
    (x = y ∨ (G ⊠ H).Adj x y) ↔ (x.1 = y.1 ∨ G.Adj x.1 y.1) ∧ (x.2 = y.2 ∨ H.Adj x.2 y.2) := by
  refine ⟨?_, fun h => (em (x = y)).imp id fun hxy => ⟨hxy, h⟩⟩
  rintro (rfl | ⟨-, h⟩)
  · exact ⟨.inl rfl, .inl rfl⟩
  · exact h

theorem eq_or_strongPow_adj {k : ℕ} {x y : Fin k → V} :
    (x = y ∨ (G.strongPow k).Adj x y) ↔ ∀ i, x i = y i ∨ G.Adj (x i) (y i) := by
  refine ⟨?_, fun h => (em (x = y)).imp id fun hxy => ⟨hxy, h⟩⟩
  rintro (rfl | ⟨-, h⟩)
  · exact fun _ => .inl rfl
  · exact h

/-- A bijection preserving "equal or adjacent" in both directions is a graph isomorphism. -/
private def isoOfEqOrAdj {G' : SimpleGraph X} (e : V ≃ X)
    (h : ∀ x y, (x = y ∨ G.Adj x y) ↔ (e x = e y ∨ G'.Adj (e x) (e y))) : G ≃g G' where
  toEquiv := e
  map_rel_iff' {x y} := by
    constructor
    · intro hadj
      rcases (h x y).2 (.inr hadj) with h' | h'
      · exact absurd (congrArg e h') hadj.ne
      · exact h'
    · intro hadj
      rcases (h x y).1 (.inr hadj) with h' | h'
      · exact absurd (e.injective h') hadj.ne
      · exact h'

/-- Splitting a word of length `m + n` into its first `m` and last `n` letters is an isomorphism
`G.strongPow (m + n) ≃g G.strongPow m ⊠ G.strongPow n`. -/
def strongPowAddIso (G : SimpleGraph V) (m n : ℕ) :
    G.strongPow (m + n) ≃g G.strongPow m ⊠ G.strongPow n :=
  isoOfEqOrAdj (Fin.appendEquiv m n).symm fun x y => by
    rw [eq_or_strongPow_adj, eq_or_strongProd_adj, eq_or_strongPow_adj, eq_or_strongPow_adj,
      Fin.forall_fin_add]
    rfl

/-- Words of length one are letters: `G.strongPow 1 ≃g G`. -/
def strongPowOneIso (G : SimpleGraph V) : G.strongPow 1 ≃g G :=
  isoOfEqOrAdj (Equiv.funUnique (Fin 1) V) fun x y => by
    rw [eq_or_strongPow_adj, Fin.forall_fin_one]
    rfl

/-! ### The independence number -/

/-- **Supermultiplicativity of the independence number** under the strong product: a product of
independent sets is independent in `G ⊠ H`. -/
theorem indepNum_mul_le_indepNum_strongProd [Finite V] [Finite W] :
    G.indepNum * H.indepNum ≤ (G ⊠ H).indepNum := by
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  obtain ⟨t, ht⟩ := H.exists_isNIndepSet_indepNum
  have hind : (G ⊠ H).IsIndepSet (s ×ˢ t : Finset (V × W)) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd hne ⟨-, h₁, h₂⟩
    simp only [coe_product, Set.mem_prod, mem_coe] at hab hcd
    have h₁ : a = c := h₁.resolve_right fun h => hs.isIndepSet hab.1 hcd.1 h.ne h
    have h₂ : b = d := h₂.resolve_right fun h => ht.isIndepSet hab.2 hcd.2 h.ne h
    exact hne (by rw [h₁, h₂])
  have h := hind.card_le_indepNum
  rwa [card_product, hs.card_eq, ht.card_eq] at h

theorem indepNum_strongPow_zero : (G.strongPow 0).indepNum = 1 :=
  le_antisymm (by simpa using (G.strongPow 0).indepNum_le_natCard) one_le_indepNum

theorem indepNum_strongPow_one [Finite V] : (G.strongPow 1).indepNum = G.indepNum :=
  G.strongPowOneIso.indepNum_eq

/-- The independence numbers of the strong powers are supermultiplicative. -/
theorem indepNum_strongPow_add [Finite V] (m n : ℕ) :
    (G.strongPow m).indepNum * (G.strongPow n).indepNum ≤ (G.strongPow (m + n)).indepNum := by
  rw [(G.strongPowAddIso m n).indepNum_eq]
  exact indepNum_mul_le_indepNum_strongProd

theorem pow_indepNum_le_indepNum_strongPow [Finite V] (k : ℕ) :
    G.indepNum ^ k ≤ (G.strongPow k).indepNum := by
  induction k with
  | zero => rw [pow_zero, indepNum_strongPow_zero]
  | succ k ih =>
    calc G.indepNum ^ (k + 1) = G.indepNum ^ k * (G.strongPow 1).indepNum := by
          rw [pow_succ, indepNum_strongPow_one]
      _ ≤ (G.strongPow k).indepNum * (G.strongPow 1).indepNum := Nat.mul_le_mul_right _ ih
      _ ≤ _ := indepNum_strongPow_add k 1

theorem indepNum_strongPow_le [Finite V] (k : ℕ) :
    (G.strongPow k).indepNum ≤ Nat.card V ^ k := by
  simpa [Nat.card_fun] using (G.strongPow k).indepNum_le_natCard

end SimpleGraph
