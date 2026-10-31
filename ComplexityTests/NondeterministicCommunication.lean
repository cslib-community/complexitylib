/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

import Complexity.Computability.Communication.Functions
import Complexity.Computability.Communication.Nondeterministic.Basic

/-! Tests for nondeterministic communication complexity by covers: exact values for equality on
three values (`N¹ = 2 = ⌈log₂ 3⌉`, by an explicit cover and the rectangle-size bound) and on `Bool`
(`N⁰ = 1`, by an explicit cover and a fooling set, and `N¹` of inequality by negation); smaller
domains that make equality trivial, and the fooling-set and rectangle-size bounds on a proper
subdomain; a relation with several acceptable answers, which is easier than the function it relaxes,
with its answers exchanged, and one with none, which has no cover; and bounds by deterministic
protocols, for a function and for a relation. -/

namespace ComplexityTests.NondeterministicCommunication

open Finset Cslib Cslib.Communication Cslib.Communication.Nondeterministic

/-! ### Equality on three values -/

/-- The rectangles of equality on `Fin 3` on which it is `true` have at most one pair. -/
private theorem card_mul_le_one_of_equality (S T : Finset (Fin 3))
    (h : ∀ x ∈ S, ∀ y ∈ T, equality x y = true) : #S * #T ≤ 1 := by
  revert h
  decide +revert

-- `N¹(EQ)` on `Fin 3` is `2`: three diagonal pairs need more than `2 ^ 1` rectangles, and the
-- diagonal singletons indexed by two bits are a cover.
example : ecomplexityFun true (equality : Fin 3 → Fin 3 → Bool) Set.univ Set.univ = 2 := by
  refine le_antisymm (ecomplexityFun_le_iff.mpr ?_) (le_ecomplexityFun_iff.mpr fun k hk => ?_)
  · let e := BitString.equivFin 2
    refine ⟨fun w => ({x | (x : ℕ) = e w}, {y | (y : ℕ) = e w}), isCover_fun_iff.mpr ⟨?_, ?_⟩⟩
    · intro w x _ hx y _ hy
      simp only [Set.mem_ofPred_eq] at hx hy
      simp [equality, Fin.ext_iff, hx, hy]
    · intro x _ y _ h
      simp only [equality, decide_eq_true_eq] at h
      exact ⟨e.symm ⟨x, by omega⟩, by simp, by simp [h]⟩
  · have : #{q ∈ (univ : Finset (Fin 3)) ×ˢ univ | equality q.1 q.2 = true} ≤ 2 ^ k * 1 :=
      HasCover.card_le_two_pow_mul (fun S _ T _ h => card_mul_le_one_of_equality S T h)
        (by simpa only [coe_univ] using hk)
    have h3 : #{q ∈ (univ : Finset (Fin 3)) ×ˢ univ | equality q.1 q.2 = true} = 3 := by decide
    rw [h3, mul_one] at this
    have : 2 ≤ k := by
      by_contra! hk
      interval_cases k <;> simp at this
    exact_mod_cast this

/-- On the smaller domain `{0} × Fin 3` one rectangle suffices. -/
private theorem ecomplexityFun_equality_zero_univ :
    ecomplexityFun true (equality : Fin 3 → Fin 3 → Bool) {0} Set.univ = 0 :=
  nonpos_iff_eq_zero.mp <| ecomplexityFun_le_iff.mpr ⟨fun _ => ({0}, {0}), isCover_fun_iff.mpr
    ⟨fun _ x hx _ y _ hy => by simp_all [equality],
      fun x hx y _ h => ⟨0, hx, by simp_all [equality]⟩⟩⟩

-- So it does on any smaller domain.
example : ecomplexityFun true (equality : Fin 3 → Fin 3 → Bool) {0} {0, 1} = 0 :=
  nonpos_iff_eq_zero.mp <| (ecomplexityFun_mono le_rfl (Set.subset_univ _)).trans
    ecomplexityFun_equality_zero_univ.le

-- On `{0, 1} × {0, 1}` the fooling set `{(0, 0), (1, 1)}` lies inside the domain, so `N¹ ≥ 1`.
example : (1 : ℕ∞) ≤ ecomplexityFun true (equality : Fin 3 → Fin 3 → Bool) {0, 1} {0, 1} :=
  le_ecomplexityFun_of_isFoolingSet (isFoolingSet_equality {0, 1}) (by decide) (by decide)

-- The rectangle-size bound on the finite domain `{0, 1} × {0, 1}`: two diagonal pairs and one pair
-- per rectangle need two rectangles.
example : (1 : ℕ∞) ≤ ecomplexityFun true (equality : Fin 3 → Fin 3 → Bool) {0, 1} {0, 1} := by
  refine le_ecomplexityFun_iff.mpr fun k hk => ?_
  have : #{q ∈ ({0, 1} : Finset (Fin 3)) ×ˢ {0, 1} | equality q.1 q.2 = true} ≤ 2 ^ k * 1 :=
    HasCover.card_le_two_pow_mul (fun S _ T _ h => card_mul_le_one_of_equality S T h)
      (by simpa only [coe_insert, coe_singleton] using hk)
  have h2 : #{q ∈ ({0, 1} : Finset (Fin 3)) ×ˢ {0, 1} | equality q.1 q.2 = true} = 2 := by decide
  rw [h2, mul_one] at this
  have : 1 ≤ k := by
    by_contra! hk
    interval_cases k
    simp at this
  exact_mod_cast this

/-! ### Equality on `Bool` -/

/-- `N⁰(EQ)` on `Bool` is `1`: `(false, true)` and `(true, false)` form a fooling set with value
`false`, and `{b} × {!b}` for the two bits `b` are a cover. -/
private theorem ecomplexityFun_false_equality_bool :
    ecomplexityFun false (equality : Bool → Bool → Bool) Set.univ Set.univ = 1 := by
  refine le_antisymm (ecomplexityFun_le_iff.mpr ?_) ?_
  · refine ⟨fun w => ({w 0}, {!w 0}), isCover_fun_iff.mpr ⟨?_, ?_⟩⟩
    · intro w x _ hx y _ hy
      simp only [Set.mem_singleton_iff] at hx hy
      simp [equality, hx, hy]
    · intro x _ y _ h
      refine ⟨fun _ => x, rfl, ?_⟩
      cases x <;> cases y <;> simp_all [equality]
  · refine le_ecomplexityFun_of_isFoolingSet (S := {(false, true), (true, false)}) ?_ (by simp)
      (by decide)
    simp [IsFoolingSet, equality]

example : ecomplexityFun false (equality : Bool → Bool → Bool) Set.univ Set.univ = 1 :=
  ecomplexityFun_false_equality_bool

-- Negation exchanges the answers: `N¹` of inequality is `N⁰` of equality.
example : ecomplexityFun true (fun x y : Bool => !equality x y) Set.univ Set.univ = 1 := by
  rw [ecomplexityFun_not, Bool.not_true, ecomplexityFun_false_equality_bool]

/-! ### Relations -/

/-- Equality under the promise `x = y`: off the diagonal every answer is acceptable. -/
private def promiseEq (x y : Bool) (b : Bool) : Prop := x = y → b = true

/-- No pair must be covered with `false`, since `true` is acceptable everywhere: one empty
rectangle is a `0`-cover, although `N⁰` of equality itself is `1`. -/
private theorem ecomplexity_false_promiseEq : ecomplexity false promiseEq Set.univ Set.univ = 0 :=
  nonpos_iff_eq_zero.mp <| ecomplexity_le_iff.mpr
    ⟨fun _ => (∅, ∅), fun _ _ _ hx => hx.elim, fun _ _ _ _ h => (h fun _ => rfl).elim⟩

-- Exchanging the answers of the relation exchanges `N⁰` and `N¹`.
example : ecomplexity true (fun x y b => promiseEq x y (!b)) Set.univ Set.univ = 0 := by
  rw [ecomplexity_not, Bool.not_true, ecomplexity_false_promiseEq]

-- The relation is weaker than equality, so it is no harder.
example : ecomplexity false promiseEq Set.univ Set.univ ≤
    ecomplexityFun false (equality : Bool → Bool → Bool) Set.univ Set.univ :=
  ecomplexity_le_of_imp fun _ _ b h hxy => by simp_all [equality]

-- A relation with no acceptable answer has no cover, as it has no protocol.
example : ecomplexity true (fun (_ _ _ : Bool) => False) Set.univ Set.univ = ⊤ :=
  top_le_iff.mp <| le_ecomplexity_iff.mpr fun _ ⟨C, hmem, hcov⟩ => by
    obtain ⟨w, hx, hy⟩ := hcov false trivial false trivial id
    exact (hmem w _ trivial hx _ trivial hy).elim

/-! ### Deterministic protocols -/

/-- Alice sends her bit, then Bob sends whether his bit is equal. -/
private def eqProtocol : Protocol Bool Bool Bool :=
  .alice id (.bob id (.output true) (.output false)) (.bob id (.output false) (.output true))

-- The protocol computes equality with two bits, so `N¹(EQ) ≤ 2` on `Bool`.
example : ecomplexityFun true (equality : Bool → Bool → Bool) Set.univ Set.univ ≤ 2 :=
  (ecomplexityFun_le_protocol true).trans <|
    (Protocol.ecomplexityFun_le_depth (p := eqProtocol)
      (funext₂ fun x y => by cases x <;> cases y <;> rfl)).trans (by decide)

-- The relation `promiseEq` is solved without communication, so its `N¹` is `0`.
example : ecomplexity true promiseEq Set.univ Set.univ = 0 :=
  nonpos_iff_eq_zero.mp <| (ecomplexity_le_protocol true).trans <|
    (Protocol.ecomplexity_le_depth (p := .output true) (R := promiseEq) (A := Set.univ)
      (B := Set.univ) fun _ _ _ _ _ => rfl).trans (by simp)

end ComplexityTests.NondeterministicCommunication
