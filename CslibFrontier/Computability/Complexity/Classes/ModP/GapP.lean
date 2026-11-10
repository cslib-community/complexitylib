/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ModP
public import CslibFrontier.Computability.Complexity.Classes.SPP.FewP

/-!
# GapP and modular counting

A fixed positive modulus turns every GapP difference `f - g` into the congruent #P count
`f + (k - 1) * g`. Thus zero and nonzero residue tests may use either counting model.
In particular, the zero-one gaps defining SPP work for every modulus at least two, including
composite moduli. This does not assert complement closure for arbitrary modular languages.
These are algebraic consequences of the counting-class definitions in [Fortnow][Fortnow1997]
and the GapP ring operations of [Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994].

## Main results

* `GapP.exists_SharpP_emod`: a #P representative of a GapP function modulo a fixed positive integer.
* `mem_ModP_iff_exists_GapP`, `mem_coModP_iff_exists_GapP`: signed-gap characterizations.
* `SPP_subset_ModP`, `SPP_subset_coModP`, `SPP_subset_ParityP`: modular containments.
* `FewP_subset_ModP`, `FewP_subset_coModP`: few accepting witnesses suffice for both residue tests.

## References

* [L. Fortnow, *Counting Complexity*][Fortnow1997]
* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
-/

public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A : Set α} {k : ℕ}

/-- A positive fixed modulus admits a #P count with the same residue as any GapP function.
The modulus is fixed before the input, so scaling by `k - 1` uses #P constant multiplication. -/
theorem GapP.exists_SharpP_emod {g : α → ℤ} (hg : g ∈ GapP enc) (hk : 0 < k) :
    ∃ f ∈ SharpP enc, ∀ a, (f a : ℤ) % k = g a % k := by
  obtain ⟨f₁, h₁, f₂, h₂, hg⟩ := hg
  refine ⟨f₁ + (fun _ => k - 1) * f₂,
    SharpP.add_mem h₁ (SharpP.mul_mem (SharpP.natCast_mem (k - 1)) h₂), fun a => ?_⟩
  have heq : ((f₁ a + (k - 1) * f₂ a : ℕ) : ℤ) =
      (f₁ a : ℤ) - f₂ a + k * f₂ a := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by lia : 1 ≤ k)]
    push_cast
    ring
  change ((f₁ a + (k - 1) * f₂ a : ℕ) : ℤ) % k = g a % k
  rw [heq, hg a, Int.add_mul_emod_self_left]

/-- For a positive fixed modulus, nonzero residues of GapP functions define `ModP`. -/
theorem mem_ModP_iff_exists_GapP (hk : 0 < k) :
    A ∈ ModP k enc ↔ ∃ g ∈ GapP enc, ∀ a, a ∈ A ↔ g a % k ≠ 0 := by
  constructor
  · rintro ⟨f, hf, hA⟩
    exact ⟨fun a => (f a : ℤ), SharpP.natCast_mem_GapP hf,
      fun a => by simpa only [← Int.natCast_emod, ne_eq, Int.natCast_eq_zero] using hA a⟩
  · rintro ⟨g, hg, hA⟩
    obtain ⟨f, hf, hfg⟩ := GapP.exists_SharpP_emod hg hk
    refine ⟨f, hf, fun a => ?_⟩
    rw [hA a, ← hfg a]
    simp only [← Int.natCast_emod, ne_eq, Int.natCast_eq_zero]

/-- For a positive fixed modulus, zero residues of GapP functions define `coModP`. -/
theorem mem_coModP_iff_exists_GapP (hk : 0 < k) :
    A ∈ coModP k enc ↔ ∃ g ∈ GapP enc, ∀ a, a ∈ A ↔ g a % k = 0 :=
  (mem_ModP_iff_exists_GapP hk).trans (exists_forall_mem_compl_iff fun _ _ => not_not)

/-- Zero-one gaps are recognized modulo every fixed `k ≥ 2`; primality is unnecessary. -/
theorem SPP_subset_ModP (hk : 2 ≤ k) : SPP enc ⊆ ModP k enc := by
  rintro A ⟨g, hg, hrange, hA⟩
  refine (mem_ModP_iff_exists_GapP (by lia)).mpr ⟨g, hg, fun a => ?_⟩
  rw [hA a]
  have hmod : (1 : ℤ) % k = 1 := Int.emod_eq_of_lt (by decide) (by exact_mod_cast hk)
  rcases hrange a with h | h <;> simp [h, hmod]

/-- Complement closure of SPP gives its containment in the zero-residue class too. -/
theorem SPP_subset_coModP (hk : 2 ≤ k) : SPP enc ⊆ coModP k enc :=
  fun _ hA => SPP_subset_ModP hk (compl_mem_SPP hA)

/-- A zero-one GapP characteristic function in particular determines parity. -/
theorem SPP_subset_ParityP : SPP enc ⊆ ParityP enc :=
  ModP_two (enc := enc) ▸ SPP_subset_ModP (by decide : 2 ≤ 2)

/-- FewP is recognized by nonzero residues for every fixed modulus at least two. -/
theorem FewP_subset_ModP (hk : 2 ≤ k) : FewP enc ⊆ ModP k enc :=
  FewP_subset_SPP.trans (SPP_subset_ModP hk)

/-- FewP is also recognized by zero residues for every fixed modulus at least two. -/
theorem FewP_subset_coModP (hk : 2 ≤ k) : FewP enc ⊆ coModP k enc :=
  FewP_subset_SPP.trans (SPP_subset_coModP hk)

end Cslib.Complexity
