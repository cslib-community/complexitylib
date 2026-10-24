/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.UP
public import Complexity.Foundations.Order.BooleanSubalgebra
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
# Modular counting classes

For fixed `k ≥ 2`, `ModP k` accepts when a `#P` count is nonzero modulo `k`. This is the convention
of [Fortnow, Classification 4.7][Fortnow1997]; in particular `ModP 2 = ParityP`. The definition is
total in `k`: at `0` it gives NP, and at `1` it contains only the empty language. The modulus is a
class parameter, not part of the input.

We use verifier counts, not a claimed equivalence with nondeterministic counting machines.
Reduction closure follows from exact-count precomposition. For a prime modulus, intersection
uses the absence of zero divisors and complement uses Fermat's little theorem: if `f` is the
original count, `1 + (p - 1) * f ^ (p - 1)` is nonzero modulo `p` exactly when `f` is zero modulo
`p`. These are elementary algebraic derivations; the prime-modulus closure framework is classical
[Papadimitriou and Zachos][PapadimitriouZachos1983]. No such closure is claimed here for arbitrary
composite moduli.

## Main definitions

* `Cslib.Complexity.ModP`: nonzero-modulus accepting counts.

## Main results

* `Cslib.Complexity.ModP_two`, `Cslib.Complexity.P_subset_ModP`.
* `Cslib.Complexity.PolyTimeReducible.mem_ModP`.
* `Cslib.Complexity.inter_mem_ModP`, `Cslib.Complexity.compl_mem_ModP`,
  `Cslib.Complexity.union_mem_ModP`: prime-modulus closure.

The complement class `coModP` is defined by zero residues. For prime moduli it equals
`ModP`, by the complement theorem above; no such equality is asserted for composite moduli.

## References

* [L. Fortnow, *Counting Complexity*][Fortnow1997], Classification 4.7.
* [C. Papadimitriou, S. Zachos, *Two remarks on the power of counting*][PapadimitriouZachos1983]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α} {k : ℕ}

/-- For a fixed modulus `k`, languages recognized by a nonzero residue of a `#P` count
[Fortnow, Classification 4.7][Fortnow1997]. The standard modular counting classes use `k ≥ 2`. -/
def ModP (k : ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpP enc, ∀ a, a ∈ A ↔ f a % k ≠ 0}

/-- Modulo two, nonzero residue is oddness [Fortnow, after Classification 4.7][Fortnow1997]. -/
theorem ModP_two : ModP 2 enc = ParityP enc := by
  ext A
  simp only [ModP, Set.mem_ofPred_eq, mem_ParityP_iff_exists_SharpP]
  congr! 3
  simp [← Nat.not_odd_iff]

/-- Modulus zero specializes to the positive-count characterization of NP. -/
theorem ModP_zero : ModP 0 enc = NP enc := by
  ext A
  simp [ModP, mem_NP_iff_exists_SharpP, Nat.pos_iff_ne_zero]

/-- Modulus one recognizes only the empty language. -/
theorem mem_ModP_one : A ∈ ModP 1 enc ↔ A = ∅ := by
  constructor
  · rintro ⟨f, -, hA⟩
    ext a
    simpa [Nat.mod_one] using hA a
  · rintro rfl
    exact ⟨0, SharpP.zero_mem, fun _ => by simp⟩

/-- Unambiguous counts are zero or one, so any modulus at least two recognizes them. -/
theorem UP_subset_ModP (hk : 2 ≤ k) : UP enc ⊆ ModP k enc := by
  rintro A ⟨f, hf, hle, hA⟩
  refine ⟨f, hf, fun a => ?_⟩
  rw [hA a, Nat.mod_eq_of_lt (by have := hle a; omega)]
  have := hle a
  omega

/-- `P ⊆ ModP k` for every fixed `k ≥ 2`. -/
theorem P_subset_ModP (hk : 2 ≤ k) : P enc ⊆ ModP k enc :=
  fun _ h => UP_subset_ModP hk (P_subset_UP h)

/-- Exact-count precomposition preserves every modulus. -/
theorem PolyTimeReducible.mem_ModP {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ ModP k encB) : A ∈ ModP k enc := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨f, hf, hB⟩ := hB
  exact ⟨f ∘ g, SharpP.comp_mem hf hg, fun a => (hAB a).trans (hB (g a))⟩

/-- Prime divisibility of a product gives intersection closure. -/
theorem inter_mem_ModP (hk : k.Prime) (hA : A ∈ ModP k enc) (hB : B ∈ ModP k enc) :
    A ∩ B ∈ ModP k enc := by
  obtain ⟨f, hf, hA⟩ := hA
  obtain ⟨g, hg, hB⟩ := hB
  exact ⟨f * g, SharpP.mul_mem hf hg, fun a => by
    simp [hA a, hB a, ← Nat.dvd_iff_mod_eq_zero, hk.dvd_mul]⟩

/-- Fermat's little theorem turns a zero residue into a one residue and conversely. -/
theorem compl_mem_ModP (hk : k.Prime) (hA : A ∈ ModP k enc) : Aᶜ ∈ ModP k enc := by
  obtain ⟨f, hf, hA⟩ := hA
  let : Fact k.Prime := ⟨hk⟩
  refine ⟨1 + (fun _ => k - 1) * f ^ (k - 1),
    SharpP.add_mem SharpP.one_mem
      (SharpP.mul_mem (SharpP.natCast_mem (k - 1)) (SharpP.pow_mem hf (k - 1))), fun a => ?_⟩
  have hcast : ((k - 1 : ℕ) : ZMod k) = -1 := by
    rw [Nat.cast_sub hk.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hc : ((1 + (k - 1) * f a ^ (k - 1) : ℕ) : ZMod k) =
      1 - (f a : ZMod k) ^ (k - 1) := by
    push_cast
    rw [hcast]
    ring
  simp only [Set.mem_compl_iff, hA a, not_not, Pi.add_apply, Pi.one_apply, Pi.mul_apply,
    Pi.pow_apply]
  simp only [ne_eq, ← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
  rw [hc, ZMod.pow_card_sub_one]
  split_ifs with h
  · simp [h]
  · simp [of_not_not h]

open scoped symmDiff

/-- For prime `k`, `ModP k` as a Boolean subalgebra of `Set α`. -/
def ModP.booleanSubalgebra (hk : k.Prime) (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (ModP k enc) (P_subset_ModP hk.two_le empty_mem_P) (fun _ => compl_mem_ModP hk)
    (fun _ _ => inter_mem_ModP hk)

@[simp]
theorem ModP.coe_booleanSubalgebra (hk : k.Prime) :
    (ModP.booleanSubalgebra hk enc : Set (Set α)) = ModP k enc := rfl

@[simp]
theorem ModP.mem_booleanSubalgebra (hk : k.Prime) :
    A ∈ ModP.booleanSubalgebra hk enc ↔ A ∈ ModP k enc := Iff.rfl

/-- Prime-modulus union closure follows by De Morgan's law. -/
theorem union_mem_ModP (hk : k.Prime) (hA : A ∈ ModP k enc) (hB : B ∈ ModP k enc) :
    A ∪ B ∈ ModP k enc :=
  (ModP.booleanSubalgebra hk enc).sup_mem hA hB

/-- Prime-modulus set-difference closure. -/
theorem diff_mem_ModP (hk : k.Prime) (hA : A ∈ ModP k enc) (hB : B ∈ ModP k enc) :
    A \ B ∈ ModP k enc :=
  (ModP.booleanSubalgebra hk enc).sdiff_mem hA hB

/-- Prime-modulus symmetric-difference closure. -/
theorem symmDiff_mem_ModP (hk : k.Prime) (hA : A ∈ ModP k enc) (hB : B ∈ ModP k enc) :
    A ∆ B ∈ ModP k enc :=
  (ModP.booleanSubalgebra hk enc).symmDiff_mem hA hB

/-- The complementary modular class: a #P count is divisible by the fixed modulus. -/
def coModP (k : ℕ) (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ ModP k enc}

/-- Zero residues characterize the complementary modular class. -/
theorem mem_coModP_iff_exists_SharpP :
    A ∈ coModP k enc ↔ ∃ f ∈ SharpP enc, ∀ a, a ∈ A ↔ f a % k = 0 :=
  exists_forall_mem_compl_iff fun _ _ => not_not

/-- Complementary modular counting is closed under polynomial-time reductions. -/
theorem PolyTimeReducible.mem_coModP {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ coModP k encB) : A ∈ coModP k enc :=
  h.mem_compl PolyTimeReducible.mem_ModP hB

/-- For prime moduli, complement closure identifies the two modular classes. -/
theorem coModP_eq_ModP (hk : k.Prime) : coModP k enc = ModP k enc := by
  ext A
  constructor
  · intro h
    simpa using compl_mem_ModP hk h
  · exact compl_mem_ModP hk

end Cslib.Complexity
