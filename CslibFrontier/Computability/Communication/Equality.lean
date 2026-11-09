/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Functions
public import CslibFrontier.Computability.Communication.Operations

/-!
# Equality on a finite set

Equality of `n`-bit strings needs `n + 1` bits for `0 < n` (`ecomplexity_equality`)
[Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997]. More generally, equality on a finite
type `X` with at least two elements has communication complexity exactly `⌈log₂ |X|⌉ + 1`
(`ecomplexityFun_equality`), which is `n + 1` for the `n`-bit strings. The upper bound is the
trivial protocol (`Protocol.ecomplexityFun_le_clog_card_succ`). The fooling-set bound only gives
`|X| < 2 ^ d` for a protocol sending `d` bits (`card_lt_two_pow_of_run_eq_equality`), which is
weaker when `|X|` is not a power of two. The lower bound instead follows the protocol tree: if a
protocol computes equality on a rectangle `A × B` that contains a pair of distinct elements, then
`2 |A ∩ B| ≤ 2 ^ d` (`two_mul_card_inter_le_two_pow_of_solves_equality`). Indeed, the first bit
splits `A` (or `B`) in two; a part meeting `B` (or `A`) only in pairs of equal elements contains at
most one element of `A ∩ B`, and the other part carries the induction.

Counting leaves, a protocol computing equality on `X` has at least `|X|` leaves labelled `true`,
one for each diagonal pair, and at least two labelled `false`, since the pairs `(a, b)` and
`(b, a)` for `a ≠ b` cannot share a leaf (`card_add_two_le_leafCount_of_run_eq_equality`). Since
negating the output does not change the communication complexity, non-equality costs as much as
equality (`ecomplexityFun_not_equality`).

## Main results

* `Cslib.Communication.two_mul_card_inter_le_two_pow_of_solves_equality`: the lower bound for
  equality on a rectangle.
* `Cslib.Communication.ecomplexityFun_equality`: equality on a finite type `X` costs exactly
  `⌈log₂ |X|⌉ + 1` bits.
* `Cslib.Communication.ecomplexityFun_not_equality`: so does non-equality.
* `Cslib.Communication.card_add_two_le_leafCount_of_run_eq_equality`: a protocol computing equality
  on `X` has at least `|X| + 2` leaves.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

open Finset

variable {X : Type*} [DecidableEq X]

/-- The induction step of `two_mul_card_inter_le_two_pow_of_solves_equality`, splitting `A` by
the bit `s`. -/
private theorem two_mul_card_inter_le_of_split {A B : Finset X} (s : X → Bool) {d₀ d₁ : ℕ}
    (h₀ : (∃ x ∈ A.filter (s · = false), ∃ y ∈ B, x ≠ y) →
      2 * #(A.filter (s · = false) ∩ B) ≤ 2 ^ d₀)
    (h₁ : (∃ x ∈ A.filter (s · = true), ∃ y ∈ B, x ≠ y) →
      2 * #(A.filter (s · = true) ∩ B) ≤ 2 ^ d₁)
    (hne : ∃ x ∈ A, ∃ y ∈ B, x ≠ y) :
    2 * #(A ∩ B) ≤ 2 ^ (max d₀ d₁ + 1) := by
  set A₀ := A.filter (s · = false)
  set A₁ := A.filter (s · = true)
  have hsplit : #(A ∩ B) = #(A₀ ∩ B) + #(A₁ ∩ B) := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext x
      cases h : s x <;> simp [A₀, A₁, h]
    · refine disjoint_left.mpr fun x hx hx' => ?_
      simp only [A₀, A₁, mem_inter, mem_filter] at hx hx'
      exact Bool.false_ne_true (hx.1.2.symm.trans hx'.1.2)
  have small (A' : Finset X) (h : ¬∃ x ∈ A', ∃ y ∈ B, x ≠ y) : #(A' ∩ B) ≤ 1 := by
    push Not at h
    exact card_le_one.mpr fun a ha b hb => h a (mem_inter.1 ha).1 b (mem_inter.1 hb).2
  have hM₀ : 2 ^ d₀ ≤ 2 ^ max d₀ d₁ := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  have hM₁ : 2 ^ d₁ ≤ 2 ^ max d₀ d₁ := Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  have hM : 1 ≤ 2 ^ max d₀ d₁ := Nat.one_le_two_pow
  rw [pow_succ]
  generalize 2 ^ max d₀ d₁ = M at hM₀ hM₁ hM ⊢
  generalize 2 ^ d₀ = M₀ at hM₀ h₀
  generalize 2 ^ d₁ = M₁ at hM₁ h₁
  by_cases e₀ : ∃ x ∈ A₀, ∃ y ∈ B, x ≠ y <;> by_cases e₁ : ∃ x ∈ A₁, ∃ y ∈ B, x ≠ y
  · have := h₀ e₀
    have := h₁ e₁
    omega
  · have := h₀ e₀
    have := small A₁ e₁
    rcases Nat.lt_or_ge M 2 with _ | _ <;> omega
  · have := h₁ e₁
    have := small A₀ e₀
    rcases Nat.lt_or_ge M 2 with _ | _ <;> omega
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := hne
    cases h : s x
    · exact e₀ ⟨x, mem_filter.2 ⟨hx, h⟩, y, hy, hxy⟩
    · exact e₁ ⟨x, mem_filter.2 ⟨hx, h⟩, y, hy, hxy⟩

/-- **Equality on a rectangle.** If a protocol computes equality on `A × B`, and `A × B` contains a
pair of distinct elements, then `2 |A ∩ B| ≤ 2 ^ d` for the number `d` of bits it sends. -/
theorem two_mul_card_inter_le_two_pow_of_solves_equality {p : Protocol X X Bool}
    {A B : Finset X} (hp : p.Solves (fun x y b => equality x y = b) A B)
    (hne : ∃ x ∈ A, ∃ y ∈ B, x ≠ y) : 2 * #(A ∩ B) ≤ 2 ^ p.depth := by
  induction p generalizing A B with
  | output z =>
    obtain ⟨x, hx, y, hy, hxy⟩ := hne
    have hz : z = false := by simpa [equality, hxy] using (hp x hx y hy).symm
    have : A ∩ B = ∅ := by
      refine eq_empty_of_forall_notMem fun c hc => ?_
      have := hp c (mem_inter.1 hc).1 c (mem_inter.1 hc).2
      simp [equality, hz] at this
    simp [this]
  | alice send p₀ p₁ ih₀ ih₁ =>
    rw [Protocol.depth_alice]
    refine two_mul_card_inter_le_of_split send (ih₀ fun x hx y hy => ?_)
      (ih₁ fun x hx y hy => ?_) hne
    · have := hp x (mem_filter.1 hx).1 y hy
      simpa [Protocol.Solves, Communication.Solves, (mem_filter.1 hx).2] using this
    · have := hp x (mem_filter.1 hx).1 y hy
      simpa [Protocol.Solves, Communication.Solves, (mem_filter.1 hx).2] using this
  | bob send p₀ p₁ ih₀ ih₁ =>
    have hsymm {A' B' : Finset X} : (∃ x ∈ A', ∃ y ∈ B', x ≠ y) → ∃ y ∈ B', ∃ x ∈ A', y ≠ x :=
      fun ⟨x, hx, y, hy, hxy⟩ => ⟨y, hy, x, hx, Ne.symm hxy⟩
    rw [Protocol.depth_bob, inter_comm]
    refine two_mul_card_inter_le_of_split send (fun h => ?_) (fun h => ?_) (hsymm hne)
    · rw [inter_comm]
      refine ih₀ (fun x hx y hy => ?_) (hsymm h)
      have := hp x hx y (mem_filter.1 hy).1
      simpa [Protocol.Solves, Communication.Solves, (mem_filter.1 hy).2] using this
    · rw [inter_comm]
      refine ih₁ (fun x hx y hy => ?_) (hsymm h)
      have := hp x hx y (mem_filter.1 hy).1
      simpa [Protocol.Solves, Communication.Solves, (mem_filter.1 hy).2] using this

variable [Fintype X]

/-- **Equality on a finite set**: equality on a finite type `X` with at least two elements has
communication complexity exactly `⌈log₂ |X|⌉ + 1`. -/
theorem ecomplexityFun_equality (hX : 1 < Fintype.card X) :
    Protocol.ecomplexityFun (equality : X → X → Bool) = Nat.clog 2 (Fintype.card X) + 1 := by
  refine le_antisymm (Protocol.ecomplexityFun_le_clog_card_succ _)
    (Protocol.le_ecomplexityFun_iff.mpr fun p hp => ?_)
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hX
  have h := two_mul_card_inter_le_two_pow_of_solves_equality (A := univ) (B := univ)
    (by rw [coe_univ]; exact Protocol.solves_univ_iff.mpr hp) ⟨a, mem_univ _, b, mem_univ _, hab⟩
  rw [inter_self, card_univ] at h
  obtain ⟨d, hd⟩ : ∃ d, p.depth = d + 1 :=
    Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 => by rw [h0] at h; omega)
  rw [hd, pow_succ] at h
  rw [hd]
  exact_mod_cast Nat.succ_le_succ (Nat.clog_le_of_le_pow (by omega))

/-- **Non-equality on a finite set**: on a finite type `X` with at least two elements, deciding
whether the inputs differ has communication complexity exactly `⌈log₂ |X|⌉ + 1`. -/
theorem ecomplexityFun_not_equality (hX : 1 < Fintype.card X) :
    Protocol.ecomplexityFun (fun x y : X => !equality x y) = Nat.clog 2 (Fintype.card X) + 1 := by
  rw [Protocol.ecomplexityFun_not, ecomplexityFun_equality hX]

/-- A protocol computing equality on a finite type `X` with at least two elements has at least
`|X| + 2` leaves: `|X|` labelled `true`, one for each diagonal pair, and two labelled `false`,
reached by `(a, b)` and `(b, a)` for any `a ≠ b`. -/
theorem card_add_two_le_leafCount_of_run_eq_equality (hX : 1 < Fintype.card X)
    {p : Protocol X X Bool} (hp : p.run = equality) : Fintype.card X + 2 ≤ p.leafCount := by
  have hT := (isFoolingSet_equality (univ : Finset X)).card_le hp
  rw [card_image_of_injective _ fun x y h => congrArg Prod.fst h, card_univ] at hT
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hX
  have hout {x y : X} (hxy : x ≠ y) : p.leafOutput (p.leaf x y) = false := by
    rw [← Protocol.run_eq_leafOutput_leaf, hp]
    simpa [equality] using hxy
  have hne : p.leaf a b ≠ p.leaf b a := fun h => by
    have hb : a ∈ p.leafBob (p.leaf a b) := h ▸ Protocol.mem_leafBob_leaf
    have := Protocol.run_eq_leafOutput Protocol.mem_leafAlice_leaf hb
    rw [hp, hout hab] at this
    simp [equality] at this
  have hF : 2 ≤ #{i | p.leafOutput i = false} := by
    have hsub : ({p.leaf a b, p.leaf b a} : Finset (Fin p.leafCount)) ⊆
        univ.filter (p.leafOutput · = false) := by
      intro i hi
      rcases mem_insert.1 hi with rfl | hi
      · simpa using hout hab
      · rw [mem_singleton.1 hi]
        simpa using hout hab.symm
    simpa [card_pair hne] using card_le_card hsub
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin p.leafCount)))
    fun i => p.leafOutput i = true
  simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at hsum
  omega

end Cslib.Communication
