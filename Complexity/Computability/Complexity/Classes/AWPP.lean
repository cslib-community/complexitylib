/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SPP
public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.PP
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import Complexity.Computability.Complexity.Classes.PP.Characterization
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Almost-wide probabilistic polynomial time

We use the constant-error, power-of-two characterization of AWPP from
[Fenner][Fenner2003]: a GapP function divided by `2 ^ p(n)` lies in `[2/3, 1]` on
members and `[0, 1/3]` on nonmembers. Integer inequalities avoid division and rounding.
The counting functions are verifier-based. Uniform error reduction is proved in
`Complexity/Computability/Complexity/Classes/AWPP/Amplification.lean`, and PP-lowness for the strict
adaptive oracle-verifier model in
`Complexity/Computability/Complexity/Classes/AWPP/Lowness.lean`.

## Main definitions

* `AWPP`: bounded-error GapP ratios with a length-dependent dyadic denominator.

## Main results

* `BPP_subset_AWPP`, `SPP_subset_AWPP`, `AWPP_subset_PP`.
* `compl_mem_AWPP`, `PolyTimeReducible.mem_AWPP`: complement and reduction closure.
* `mem_AWPP_of_polyTime_exponent`: padding input-dependent dyadic denominators.

## References

* [S. Fenner, *PP-Lowness and a Simple Definition of AWPP*][Fenner2003]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- A GapP ratio in `[0, 1]`, at least `2/3` on members and at most `1/3` otherwise, Fenner's
characterization of AWPP [Fenner][Fenner2003]. -/
def AWPP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ g ∈ GapP enc, ∃ p : Polynomial ℕ, ∀ a,
    (0 ≤ g a ∧ g a ≤ (2 : ℤ) ^ p.eval (enc a).length) ∧
    (a ∈ A → 2 * (2 : ℤ) ^ p.eval (enc a).length ≤ 3 * g a) ∧
    (a ∉ A → 3 * g a ≤ (2 : ℤ) ^ p.eval (enc a).length)}

/-- Acceptance counts are GapP functions, so bounded-error computation gives an AWPP ratio. -/
theorem BPP_subset_AWPP : BPP enc ⊆ AWPP enc := by
  rintro A ⟨p, V, hV, hA⟩
  have hf : (fun a => acceptCount V a (p.eval (enc a).length)) ∈ SharpP enc :=
    ⟨p, V, hV, fun _ => rfl⟩
  refine ⟨_, SharpP.natCast_mem_GapP hf, p, fun a => ⟨⟨by positivity, ?_⟩, ?_, ?_⟩⟩
  · exact_mod_cast (acceptCount_le_two_pow (V := V) (a := a)
      (n := p.eval (enc a).length))
  · intro ha
    exact_mod_cast (hA a).1 ha
  · intro ha
    have hs := acceptCount_add_card_filter_eq_false (V := V) (a := a)
      (n := p.eval (enc a).length)
    have hn := (hA a).2 ha
    have : 3 * acceptCount V a (p.eval (enc a).length) ≤ 2 ^ p.eval (enc a).length := by
      lia
    exact_mod_cast this

/-- The characteristic GapP function has denominator one. -/
theorem SPP_subset_AWPP : SPP enc ⊆ AWPP enc := by
  rintro A ⟨g, hg, hr, hA⟩
  refine ⟨g, hg, 0, fun a => ?_⟩
  rcases hr a with h | h <;> simp [hA a, h]

/-- Subtracting the gap from its dyadic denominator exchanges yes and no instances. -/
theorem compl_mem_AWPP (hA : A ∈ AWPP enc) : Aᶜ ∈ AWPP enc := by
  obtain ⟨g, hg, p, hA⟩ := hA
  have hd := GapP.two_pow_mem (enc := enc) p
  refine ⟨_, GapP.sub_mem' hd hg, p, fun a => ?_⟩
  obtain ⟨⟨h0, h1⟩, hy, hn⟩ := hA a
  change (0 ≤ (2 : ℤ) ^ p.eval (enc a).length - g a ∧ _) ∧ _
  simp only [Set.mem_compl_iff, not_not, Pi.sub_apply]
  constructor
  · constructor <;> lia
  · constructor <;> intro ha
    · have := hn ha
      lia
    · have := hy ha
      lia

/-- The sign of twice the gap minus the denominator recognizes the language in PP. -/
theorem AWPP_subset_PP : AWPP enc ⊆ PP enc := by
  rintro A ⟨g, hg, p, hA⟩
  have hd := GapP.two_pow_mem (enc := enc) p
  refine mem_PP_iff_exists_GapP.mpr
    ⟨_, GapP.sub_mem' (GapP.add_mem hg hg) hd, fun a => ?_⟩
  have hp : 0 < (2 : ℤ) ^ p.eval (enc a).length := by positivity
  change a ∈ A ↔ 0 < g a + g a - (2 : ℤ) ^ p.eval (enc a).length
  by_cases ha : a ∈ A
  · have := (hA a).2.1 ha
    simp only [ha, true_iff]
    lia
  · have := (hA a).2.2 ha
    simp only [ha, false_iff]
    lia

/-- An efficiently computed unary exponent can be padded to a polynomial in input length.
Multiplying numerator and denominator by the same power of two preserves the ratio. -/
theorem mem_AWPP_of_polyTime_exponent {g : α → ℤ} {r : α → ℕ}
    (hg : g ∈ GapP enc) (hr : ComputableInPolyTime r enc encUnary)
    (hA : ∀ a, (0 ≤ g a ∧ g a ≤ (2 : ℤ) ^ r a) ∧
      (a ∈ A → 2 * (2 : ℤ) ^ r a ≤ 3 * g a) ∧
      (a ∉ A → 3 * g a ≤ (2 : ℤ) ^ r a)) : A ∈ AWPP enc := by
  obtain ⟨p, hle⟩ := hr.polyBounded.exists_polynomial
  have hs : ComputableInPolyTime
      (fun a => 2 ^ (p.eval (enc a).length - r a)) enc encNat := by fun_prop
  have hsG := SharpP.natCast_mem_GapP (mem_SharpP_of_polyTime hs)
  refine ⟨_, GapP.mul_mem hg hsG, p, fun a => ?_⟩
  have he : (2 : ℤ) ^ p.eval (enc a).length =
      (2 : ℤ) ^ r a * (2 : ℤ) ^ (p.eval (enc a).length - r a) := by
    rw [← pow_add, Nat.add_sub_of_le (hle a)]
  have hp : 0 ≤ (2 : ℤ) ^ (p.eval (enc a).length - r a) := by positivity
  obtain ⟨⟨h0, h1⟩, hy, hn⟩ := hA a
  simp only [Pi.mul_apply, Nat.cast_pow, Nat.cast_ofNat, he]
  refine ⟨⟨mul_nonneg h0 hp, mul_le_mul_of_nonneg_right h1 hp⟩, ?_, ?_⟩
  · intro ha
    nlinarith only [mul_le_mul_of_nonneg_right (hy ha) hp]
  · intro ha
    nlinarith only [mul_le_mul_of_nonneg_right (hn ha) hp]

/-- Polynomial-time many-one reductions preserve AWPP after dyadic denominator padding. -/
theorem PolyTimeReducible.mem_AWPP {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ AWPP encB) : A ∈ AWPP enc := by
  obtain ⟨r, hr, hAB⟩ := h
  obtain ⟨g, hg, p, hB⟩ := hB
  refine mem_AWPP_of_polyTime_exponent (GapP.comp_mem hg hr)
    (r := fun a => p.eval (encB (r a)).length) (by fun_prop)
    (fun a => ?_)
  simpa only [Function.comp_apply, ← hAB a] using hB (r a)

end Cslib.Complexity
