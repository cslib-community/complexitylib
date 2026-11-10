/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, beside Mathlib/Order/KrullDimension.lean)

public import Complexity.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Antichain
public import Mathlib.Order.KrullDimension

/-!
# Chain–antichain duality and Mirsky's theorem

A *colouring* `f : α → ι` with antichain fibres (each `f ⁻¹' {i}` is an antichain) is a covering of
`α` by antichains indexed by `ι`; one with chain fibres is a covering by chains. A chain meets each
antichain at most once and vice versa, which gives weak duality in both directions
(`IsChain.card_le_of_isAntichain_fibre`, `IsAntichain.card_le_of_isChain_fibre`).

*Mirsky's theorem* ([Mirsky1971]; [Schrijver2017], Theorem 7.5) is the strong duality for chains:
in a finite poset, the maximum size of a chain equals the minimum number of antichains covering it.
The proof colours each element by its height (`Order.height`), the length of the longest strictly
increasing series ending there, which is strictly monotone; an element of maximal height ends a
chain with one element per colour. The dual statement, Dilworth's theorem, is
`Cslib.Algorithms.Lean.MaxFlow.exists_isAntichain_and_chain_coloring`.

Chains and antichains are Mathlib's `IsChain (· ≤ ·)` and `IsAntichain (· ≤ ·)`, and finite chains
are `Finset`s. Mirsky's theorem is stated for every finite partial order, including the empty one
(the empty chain and the empty colouring).

## Main results

* `IsChain.injOn_of_isAntichain_fibre`, `IsAntichain.injOn_of_isChain_fibre`: a colouring is
  injective on a chain if its fibres are antichains, and on an antichain if its fibres are chains.
* `IsChain.card_le_of_isAntichain_fibre`, `IsAntichain.card_le_of_isChain_fibre`: weak duality.
* `Order.height_lt_top_of_finite`: in a finite preorder every height is finite.
* `exists_isChain_and_antichain_coloring`: **Mirsky's theorem**, a chain `C` and a covering by
  `|C|` antichains.
* `exists_antichain_coloring_iff`: **Mirsky's theorem**, min–max form: `α` is covered by `k`
  antichains if and only if every chain has at most `k` elements.

## References

* [L. Mirsky, *A dual of Dilworth's decomposition theorem*][Mirsky1971]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], Section 7.3
-/

public section

variable {α ι : Type*}

section WeakDuality

variable {r : α → α → Prop} {s : Set α} {f : α → ι}

/-- A chain meets every antichain fibre of `f` at most once, so `f` is injective on it. -/
theorem IsChain.injOn_of_isAntichain_fibre (hs : IsChain r s)
    (hf : ∀ i, IsAntichain r (f ⁻¹' {i})) : Set.InjOn f s := fun x hx _ hy hxy =>
  inter_subsingleton_of_isChain_of_isAntichain hs (hf (f x)) ⟨hx, rfl⟩ ⟨hy, hxy.symm⟩

/-- An antichain meets every chain fibre of `f` at most once, so `f` is injective on it. -/
theorem IsAntichain.injOn_of_isChain_fibre (hs : IsAntichain r s)
    (hf : ∀ i, IsChain r (f ⁻¹' {i})) : Set.InjOn f s := fun x hx _ hy hxy =>
  inter_subsingleton_of_isAntichain_of_isChain hs (hf (f x)) ⟨hx, rfl⟩ ⟨hy, hxy.symm⟩

/-- **Weak duality for chains** ([Schrijver2017], display (17)): a finite chain has at most as
many elements as there are colours in any colouring with antichain fibres. -/
theorem IsChain.card_le_of_isAntichain_fibre [Fintype ι] {t : Finset α}
    (ht : IsChain r (t : Set α)) (hf : ∀ i, IsAntichain r (f ⁻¹' {i})) :
    t.card ≤ Fintype.card ι := by
  classical
  exact Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    (ht.injOn_of_isAntichain_fibre hf)

/-- **Weak duality for antichains** ([Schrijver2017], display (17)): a finite antichain has at
most as many elements as there are colours in any colouring with chain fibres. -/
theorem IsAntichain.card_le_of_isChain_fibre [Fintype ι] {t : Finset α}
    (ht : IsAntichain r (t : Set α)) (hf : ∀ i, IsChain r (f ⁻¹' {i})) :
    t.card ≤ Fintype.card ι := by
  classical
  exact Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    (ht.injOn_of_isChain_fibre hf)

end WeakDuality

/-- In a finite preorder every element has finite height: a strictly increasing series has fewer
than `Fintype.card β` steps. -/
theorem Order.height_lt_top_of_finite {β : Type*} [Preorder β] [Finite β] (a : β) :
    Order.height a < ⊤ := by
  cases nonempty_fintype β
  exact lt_of_le_of_lt (Order.height_le fun p _ => (by exact_mod_cast p.length_lt_card.le))
    (ENat.natCast_lt_top (Fintype.card β))

section Mirsky

variable [PartialOrder α] [Finite α]

/-- **Mirsky's theorem** ([Mirsky1971]; [Schrijver2017], Theorem 7.5): a finite poset has a chain
`C` and a covering by `|C|` antichains. Colour by height: the colour classes are antichains, and an
element of maximal height `h` ends a chain of `h + 1` elements. By weak duality `C` is a longest
chain and the colouring uses the fewest antichains. -/
theorem exists_isChain_and_antichain_coloring :
    ∃ (C : Finset α) (f : α → Fin C.card),
      IsChain (· ≤ ·) (C : Set α) ∧ ∀ i, IsAntichain (· ≤ ·) (f ⁻¹' {i}) := by
  classical
  cases nonempty_fintype α
  let h : α → ℕ := fun a => (Order.height a).toNat
  have hh : ∀ a, (h a : ℕ∞) = Order.height a := fun a =>
    ENat.natCast_toNat (Order.height_lt_top_of_finite a).ne
  have hmono : ∀ {a b : α}, a < b → h a < h b := fun {a b} hab => by
    have := Order.height_strictMono hab (Order.height_lt_top_of_finite a)
    rw [← hh a, ← hh b] at this
    exact_mod_cast this
  cases isEmpty_or_nonempty α with
  | inl _ =>
    exact ⟨∅, fun a => isEmptyElim a, by simp, fun i x => isEmptyElim x⟩
  | inr hne =>
    obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ h Finset.univ_nonempty
    obtain ⟨p, -, hp⟩ := Order.exists_series_of_height_eq_coe a (hh a).symm
    let C : Finset α := Finset.univ.image p
    have hC : C.card = h a + 1 := by
      rw [Finset.card_image_of_injective _ p.strictMono.injective, Finset.card_univ,
        Fintype.card_fin, hp]
    refine ⟨C, fun x => ⟨h x, hC ▸ Nat.lt_succ_of_le (ha x (Finset.mem_univ x))⟩, ?_, ?_⟩
    · rintro _ hx _ hy -
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      rcases le_total i j with hij | hij
      · exact .inl (p.monotone hij)
      · exact .inr (p.monotone hij)
    · intro i x hx y hy hxy hle
      have hxy' : h x = h y := by
        have h1 : (⟨h x, _⟩ : Fin C.card) = i := hx
        have h2 : (⟨h y, _⟩ : Fin C.card) = i := hy
        exact Fin.mk.inj_iff.mp (h1.trans h2.symm)
      exact (hmono (lt_of_le_of_ne hle hxy)).ne hxy'

/-- **Mirsky's theorem**, min–max form ([Schrijver2017], Theorem 7.5): a finite poset can be
covered by `k` antichains if and only if every chain has at most `k` elements. -/
theorem exists_antichain_coloring_iff {k : ℕ} :
    (∃ f : α → Fin k, ∀ i, IsAntichain (· ≤ ·) (f ⁻¹' {i})) ↔
      ∀ C : Finset α, IsChain (· ≤ ·) (C : Set α) → C.card ≤ k := by
  constructor
  · rintro ⟨f, hf⟩ C hC
    simpa using hC.card_le_of_isAntichain_fibre hf
  · intro hk
    obtain ⟨C, f, hC, hf⟩ := exists_isChain_and_antichain_coloring (α := α)
    refine ⟨fun x => Fin.castLE (hk C hC) (f x), fun i x hx y hy => ?_⟩
    have hxy : f x = f y := Fin.castLE_injective _ (hx.trans hy.symm)
    exact hf (f x) rfl hxy.symm

end Mirsky
