/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.ChainCover
public import CslibFrontier.Foundations.Combinatorics.ErdosSzekeres
import Mathlib.Data.Fintype.Powerset

/-!
# Dilworth, Mirsky and Erdős–Szekeres tests

Kernel-checked examples (without `native_decide`) for `CslibFrontier.Foundations.Order.Mirsky`,
`CslibFrontier.Algorithms.Lean.MaxFlow.Dilworth`, `CslibFrontier.Algorithms.Lean.MaxFlow.ChainCover`
and `CslibFrontier.Foundations.Combinatorics.ErdosSzekeres`:

1. **Divisibility on `{1, …, 12}`:** width `6` (the antichain `{7, …, 12}` and the chains
   `{1, 2, 4, 8}`, `{3, 6, 12}`, `{5, 10}`, `{7}`, `{9}`, `{11}`) and height `4` (the chain
   `{1, 2, 4, 8}` and the antichains of numbers with `0, 1, 2, 3` prime factors counted with
   multiplicity). Both directions of the min–max forms of Dilworth's and Mirsky's theorems are
   used: the explicit coverings bound every antichain and chain, and the explicit antichain and
   chain rule out coverings with one fewer part.
2. **Boolean lattice `Finset (Fin 3)`:** width `3` (the singletons and the chains
   `∅ ⊂ {0} ⊂ {0, 1} ⊂ {0, 1, 2}`, `{1} ⊂ {1, 2}`, `{2} ⊂ {0, 2}`) and height `4` (rank layers).
3. **Solver runs:** complete runs of `minChainCoverM` on divisibility on `{1, …, 6}` (labels into
   `3` chains, the antichain `{4, 5, 6}`, a matching of size `3`) and on the Boolean lattice of
   rank `3` encoded as bitmasks of `Fin 8` (`3` chains, an antichain of size `3`). The
   certificate lemma `card_le_card_antichain_of_isAntichain` then bounds every antichain, and
   `minChainCoverM_time_le` is instantiated.
4. **Erdős–Szekeres:** a positive instance and the tight sequence `2, 1, 4, 3`, which has
   `n = r * s = 4` terms and neither a monotone nor a strictly decreasing subsequence of `3` terms.
-/

public section

namespace ComplexityTests.Dilworth

open Cslib.Algorithms.Lean.MaxFlow

/-- Antichain check through explicit quantifiers over a `Finset`. -/
theorem isAntichain_of_forall {α : Type*} [LE α] {s : Finset α}
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ a ≤ b) : IsAntichain (· ≤ ·) (s : Set α) := h

/-- Chain check through explicit quantifiers over a `Finset`. -/
theorem isChain_of_forall {α : Type*} [LE α] {s : Finset α}
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a ≤ b ∨ b ≤ a) : IsChain (· ≤ ·) (s : Set α) := h

/-- Chain-fibre check for a colouring. -/
theorem isChain_fibre_of_forall {α ι : Type*} [LE α] {f : α → ι}
    (h : ∀ a b, f a = f b → a ≤ b ∨ b ≤ a) : ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i}) :=
  fun _ a ha b hb _ => h a b (ha.trans hb.symm)

/-- Antichain-fibre check for a colouring. -/
theorem isAntichain_fibre_of_forall {α ι : Type*} [LE α] {f : α → ι}
    (h : ∀ a b, f a = f b → a ≤ b → a = b) : ∀ i, IsAntichain (· ≤ ·) (f ⁻¹' {i}) :=
  fun _ a ha b hb hab hle => hab (h a b (ha.trans hb.symm) hle)

/-! ### 1. Divisibility on `{1, …, 12}` -/

/-- `Fin n` ordered by divisibility of `i + 1`: the divisibility order on `{1, …, n}`. -/
@[expose] def DivPos (n : ℕ) : Type := Fin n

instance (n : ℕ) : DecidableEq (DivPos n) := inferInstanceAs (DecidableEq (Fin n))
instance (n : ℕ) : Fintype (DivPos n) := inferInstanceAs (Fintype (Fin n))

instance (n : ℕ) : PartialOrder (DivPos n) where
  le i j := ((i : Fin n).val + 1) ∣ ((j : Fin n).val + 1)
  le_refl _ := dvd_refl _
  le_trans _ _ _ := dvd_trans
  le_antisymm i j h₁ h₂ := Fin.ext (Nat.succ_injective (Nat.dvd_antisymm h₁ h₂))

instance (n : ℕ) : DecidableLE (DivPos n) := fun i j =>
  inferInstanceAs (Decidable (((i : Fin n).val + 1) ∣ ((j : Fin n).val + 1)))

instance (n : ℕ) : DecidableLT (DivPos n) := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The element `k ∈ {1, …, n}` of `DivPos n`. -/
@[expose] def dp {n : ℕ} (k : ℕ) (h : 0 < k ∧ k ≤ n := by decide) : DivPos n :=
  (⟨k - 1, by omega⟩ : Fin n)

example : (dp 3 : DivPos 12) ≤ dp 12 := by decide
example : ¬ (dp 4 : DivPos 12) ≤ dp 6 := by decide

/-- The antichain `{7, …, 12}`. -/
@[expose] def div12Antichain : Finset (DivPos 12) := {dp 7, dp 8, dp 9, dp 10, dp 11, dp 12}

theorem div12Antichain_isAntichain : IsAntichain (· ≤ ·) (div12Antichain : Set (DivPos 12)) :=
  isAntichain_of_forall (by decide)

/-- The chains `{1, 2, 4, 8}`, `{3, 6, 12}`, `{5, 10}`, `{7}`, `{9}`, `{11}`. -/
@[expose] def div12Chains (i : DivPos 12) : Fin 6 := ![0, 0, 1, 0, 2, 1, 3, 0, 4, 2, 5, 1] i

theorem div12Chains_isChain : ∀ c, IsChain (· ≤ ·) (div12Chains ⁻¹' {c}) :=
  isChain_fibre_of_forall (by decide)

/-- The chain `{1, 2, 4, 8}`. -/
@[expose] def div12Chain : Finset (DivPos 12) := {dp 1, dp 2, dp 4, dp 8}

theorem div12Chain_isChain : IsChain (· ≤ ·) (div12Chain : Set (DivPos 12)) :=
  isChain_of_forall (by decide)

/-- The antichains of numbers with `0, 1, 2, 3` prime factors (with multiplicity). -/
@[expose] def div12Layers (i : DivPos 12) : Fin 4 := ![0, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 3] i

theorem div12Layers_isAntichain : ∀ c, IsAntichain (· ≤ ·) (div12Layers ⁻¹' {c}) :=
  isAntichain_fibre_of_forall (by decide)

/-- **Dilworth**, covering to antichain bound: every antichain of `{1, …, 12}` has at most `6`
elements. -/
theorem div12_card_antichain_le (A : Finset (DivPos 12))
    (hA : IsAntichain (· ≤ ·) (A : Set (DivPos 12))) :
    A.card ≤ 6 :=
  exists_chain_coloring_iff.mp ⟨div12Chains, div12Chains_isChain⟩ A hA

/-- **Dilworth**, antichain to covering bound: `{1, …, 12}` is not covered by `5` chains. -/
theorem div12_not_five_chains : ¬ ∃ f : DivPos 12 → Fin 5, ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i}) :=
  fun h => absurd (exists_chain_coloring_iff.mp h _ div12Antichain_isAntichain) (by decide)

/-- **Dilworth**: every antichain-and-covering pair from `exists_isAntichain_and_chain_coloring`
has width `6` here. -/
example (A : Finset (DivPos 12)) (f : DivPos 12 → Fin A.card)
    (hA : IsAntichain (· ≤ ·) (A : Set (DivPos 12))) (hf : ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i})) :
    A.card = 6 :=
  le_antisymm (div12_card_antichain_le A hA) (by
    have h := div12Antichain_isAntichain.card_le_of_isChain_fibre hf
    rwa [Fintype.card_fin, show div12Antichain.card = 6 by decide] at h)

example : ∃ (A : Finset (DivPos 12)) (f : DivPos 12 → Fin A.card),
    IsAntichain (· ≤ ·) (A : Set (DivPos 12)) ∧ ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i}) :=
  exists_isAntichain_and_chain_coloring

/-- **Mirsky**, covering to chain bound: every chain of `{1, …, 12}` has at most `4` elements. -/
theorem div12_card_chain_le (C : Finset (DivPos 12)) (hC : IsChain (· ≤ ·) (C : Set (DivPos 12))) :
    C.card ≤ 4 :=
  exists_antichain_coloring_iff.mp ⟨div12Layers, div12Layers_isAntichain⟩ C hC

/-- **Mirsky**, chain to covering bound: `{1, …, 12}` is not covered by `3` antichains. -/
theorem div12_not_three_antichains :
    ¬ ∃ f : DivPos 12 → Fin 3, ∀ i, IsAntichain (· ≤ ·) (f ⁻¹' {i}) :=
  fun h => absurd (exists_antichain_coloring_iff.mp h _ div12Chain_isChain) (by decide)

/-! ### 2. Boolean lattice `Finset (Fin 3)` -/

/-- The chains `∅ ⊂ {0} ⊂ {0, 1} ⊂ {0, 1, 2}`, `{1} ⊂ {1, 2}` and `{2} ⊂ {0, 2}`. -/
@[expose] def boolChains (s : Finset (Fin 3)) : Fin 3 :=
  if s = {1} ∨ s = {1, 2} then 1 else if s = {2} ∨ s = {0, 2} then 2 else 0

theorem boolChains_isChain : ∀ c, IsChain (· ≤ ·) (boolChains ⁻¹' {c}) :=
  isChain_fibre_of_forall (by decide)

theorem bool_singletons_isAntichain :
    IsAntichain (· ≤ ·) (({{0}, {1}, {2}} : Finset (Finset (Fin 3))) : Set (Finset (Fin 3))) :=
  isAntichain_of_forall (by decide)

/-- The rank layers `s ↦ |s|`. -/
@[expose] def boolRank (s : Finset (Fin 3)) : Fin 4 :=
  ⟨s.card, Nat.lt_succ_of_le (by simpa using s.card_le_univ)⟩

theorem boolRank_isAntichain : ∀ c, IsAntichain (· ≤ ·) (boolRank ⁻¹' {c}) :=
  isAntichain_fibre_of_forall (by decide)

theorem bool_chain_isChain :
    IsChain (· ≤ ·) (({∅, {0}, {0, 1}, {0, 1, 2}} : Finset (Finset (Fin 3))) :
      Set (Finset (Fin 3))) :=
  isChain_of_forall (by decide)

/-- **Dilworth** for the Boolean lattice of rank `3`: width `3`. -/
example : (∀ A : Finset (Finset (Fin 3)), IsAntichain (· ≤ ·) (A : Set (Finset (Fin 3))) →
      A.card ≤ 3) ∧
    ¬ ∃ f : Finset (Fin 3) → Fin 2, ∀ i, IsChain (· ≤ ·) (f ⁻¹' {i}) :=
  ⟨exists_chain_coloring_iff.mp ⟨boolChains, boolChains_isChain⟩,
    fun h => absurd (exists_chain_coloring_iff.mp h _ bool_singletons_isAntichain) (by decide)⟩

/-- **Mirsky** for the Boolean lattice of rank `3`: height `4`. -/
example : (∀ C : Finset (Finset (Fin 3)), IsChain (· ≤ ·) (C : Set (Finset (Fin 3))) → C.card ≤ 4) ∧
    ¬ ∃ f : Finset (Fin 3) → Fin 3, ∀ i, IsAntichain (· ≤ ·) (f ⁻¹' {i}) :=
  ⟨exists_antichain_coloring_iff.mp ⟨boolRank, boolRank_isAntichain⟩,
    fun h => absurd (exists_antichain_coloring_iff.mp h _ bool_chain_isChain) (by decide)⟩

/-! ### 3. Solver runs -/

/-- Enumeration of divisibility on `{1, …, 6}`. -/
@[expose] def div6Enum : Fin 6 ≃ DivPos 6 := Equiv.refl _

example : (minChainCoverM div6Enum).ret.numChains = 3 := by decide

example : (minChainCoverM div6Enum).ret.antichain = {3, 4, 5} := by decide

example : (minChainCoverM div6Enum).ret.matching.card = 3 := by decide

/-- Every antichain of divisibility on `{1, …, 6}` has at most `3` elements, from the solver's
certificate. -/
example (A : Finset (DivPos 6)) (hA : IsAntichain (· ≤ ·) (A : Set (DivPos 6))) : A.card ≤ 3 := by
  have h := card_le_card_antichain_of_isAntichain div6Enum hA
  rwa [show (minChainCoverM div6Enum).ret.antichain.card = 3 by decide] at h

example : (minChainCoverM div6Enum).time ≤
    (2 * Nat.sqrt 6 + 1) * (10 * 6 + 1 + 4 * (6 * 6)) + 2 * (6 * 6) + 6 * 6 :=
  minChainCoverM_time_le div6Enum

/-- `Fin 8` ordered by bitwise inclusion of the binary digits: the Boolean lattice of rank `3`. -/
@[expose] def BitPos : Type := Fin 8

/-- Bitwise inclusion. -/
@[expose] def bitLe (i j : Fin 8) : Prop := i.val &&& j.val = i.val

instance (i j : Fin 8) : Decidable (bitLe i j) :=
  inferInstanceAs (Decidable (i.val &&& j.val = i.val))

theorem bitLe_refl : ∀ i, bitLe i i := by decide
theorem bitLe_trans : ∀ i j k, bitLe i j → bitLe j k → bitLe i k := by decide
theorem bitLe_antisymm : ∀ i j, bitLe i j → bitLe j i → i = j := by decide

instance : PartialOrder BitPos where
  le := bitLe
  le_refl := bitLe_refl
  le_trans := bitLe_trans
  le_antisymm := bitLe_antisymm

instance : DecidableLE BitPos := fun i j =>
  inferInstanceAs (Decidable ((i : Fin 8).val &&& (j : Fin 8).val = (i : Fin 8).val))
instance : DecidableLT BitPos := fun i j =>
  inferInstanceAs (Decidable ((i : Fin 8).val &&& (j : Fin 8).val = (i : Fin 8).val ∧
    ¬ (j : Fin 8).val &&& (i : Fin 8).val = (j : Fin 8).val))

/-- Enumeration of the Boolean lattice of rank `3` by bitmasks. -/
@[expose] def bitEnum : Fin 8 ≃ BitPos := Equiv.refl _

example : (minChainCoverM bitEnum).ret.numChains = 3 := by decide

example : (minChainCoverM bitEnum).ret.antichain.card = 3 := by decide

/-- The solver's certificate: every antichain of the Boolean lattice of rank `3` has at most `3`
elements. -/
example (A : Finset BitPos) (hA : IsAntichain (· ≤ ·) (A : Set BitPos)) : A.card ≤ 3 := by
  have h := card_le_card_antichain_of_isAntichain bitEnum hA
  rwa [show (minChainCoverM bitEnum).ret.antichain.card = 3 by decide] at h

/-! ### 4. Erdős–Szekeres -/

example : (∃ t : Finset (Fin 5), 2 < t.card ∧ MonotoneOn ![(3 : ℕ), 1, 4, 1, 5] t) ∨
    ∃ t : Finset (Fin 5), 2 < t.card ∧ StrictAntiOn ![(3 : ℕ), 1, 4, 1, 5] t :=
  exists_monotoneOn_or_strictAntiOn_of_mul_lt _ (by decide)

example : (∃ t : Finset (Fin 5), 2 < t.card ∧ StrictMonoOn ![(2 : ℕ), 1, 4, 3, 0] t) ∨
    ∃ t : Finset (Fin 5), 2 < t.card ∧ StrictAntiOn ![(2 : ℕ), 1, 4, 3, 0] t :=
  exists_strictMonoOn_or_strictAntiOn_of_mul_lt (by decide) (by decide)

/-- The tight sequence `2, 1, 4, 3`: `n = r * s` for `r = s = 2`. -/
@[expose] def tightSeq : Fin 4 → ℕ := ![2, 1, 4, 3]

/-- `2, 1, 4, 3` has no monotone subsequence of `3` terms. -/
theorem tightSeq_not_monotoneOn (t : Finset (Fin 4)) (ht : 2 < t.card) :
    ¬ MonotoneOn tightSeq t := by
  have h : ∀ t : Finset (Fin 4), 2 < t.card →
      ¬ ∀ a ∈ t, ∀ b ∈ t, a ≤ b → tightSeq a ≤ tightSeq b := by decide
  exact fun hm => h t ht fun a ha b hb hab => hm ha hb hab

/-- `2, 1, 4, 3` has no strictly decreasing subsequence of `3` terms. -/
theorem tightSeq_not_strictAntiOn (t : Finset (Fin 4)) (ht : 2 < t.card) :
    ¬ StrictAntiOn tightSeq t := by
  have h : ∀ t : Finset (Fin 4), 2 < t.card →
      ¬ ∀ a ∈ t, ∀ b ∈ t, a < b → tightSeq b < tightSeq a := by decide
  exact fun hm => h t ht fun a ha b hb hab => hm ha hb hab

end ComplexityTests.Dilworth
