/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Space
public import Complexity.Computability.Complexity.Classes.ModP
public import Complexity.Computability.Complexity.Classes.PP.Characterization
public import Complexity.Computability.Complexity.Classes.Space.Closure
public import Complexity.Computability.Complexity.Classes.Oracle.Space
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# Counting classes within polynomial space

Exact #P counts have polynomially many binary digits and can be evaluated in polynomial space.
Comparing the count to a majority threshold therefore gives `PP ⊆ PSPACE`. For modular classes,
divisibility is tested by a polynomially long binary quotient certificate, searched in polynomial
space. This works for every fixed modulus, including the degenerate moduli zero and one.

The oracle corollaries use languages over words with their identity encoding. They make no
claim that the image of an arbitrary encoding is decidable.

## Main results

* `Cslib.Complexity.PP_subset_PSPACE`.
* `Cslib.Complexity.ModP_subset_PSPACE`, `Cslib.Complexity.coModP_subset_PSPACE`.
* `Cslib.Complexity.PWithOracle_subset_PSPACE_of_mem_PP`,
  `Cslib.Complexity.NPWithOracle_subset_PSPACE_of_mem_PP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [L. Fortnow, *Counting Complexity*][Fortnow1997]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- Majority counting is decidable in polynomial space by evaluating the exact count in binary
and comparing it with the threshold [AroraBarak09]. -/
theorem PP_subset_PSPACE : PP enc ⊆ PSPACE enc := by
  intro A hA
  obtain ⟨f, hf, p, hA⟩ := mem_PP_iff_exists_SharpP.mp hA
  have hpow : ComputableTidilyInPolyTime (fun a => 2 ^ p.eval (enc a).length) enc encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp (by fun_prop)
  have hdouble : ComputableTidilyInPolyTime (fun n : ℕ => 2 * n) encNat encNat := by
    fun_prop
  have htest := (ComputableTidilyInPolySpace.of_polyTime
    ComputableTidilyInPolyTime.binary_lt).comp
      ((ComputableTidilyInPolySpace.of_polyTime hpow).prod
        ((ComputableTidilyInPolySpace.of_polyTime hdouble).comp
          (SharpP.computableInPolySpace hf).tidy))
  exact mem_PSPACE_of_computableInPolySpace (.of_tidy htest) fun a => by simpa using hA a

/-- Testing whether a fixed modulus divides a #P count is in polynomial space. A quotient has
at most one more bit than the verifier's certificate length, even for moduli zero and one. -/
theorem coModP_subset_PSPACE (k : ℕ) : coModP k enc ⊆ PSPACE enc := by
  intro A hA
  obtain ⟨f, hf, hA⟩ := mem_coModP_iff_exists_SharpP.mp hA
  obtain ⟨p, hp⟩ := SharpP.exists_le_two_pow hf
  have hleft : ComputableTidilyInPolySpace (fun x : α × List Bool => f x.1)
      (encPair enc encBits) encNat :=
    (SharpP.computableInPolySpace hf).tidy.comp
      (.of_polyTime (ComputableTidilyInPolyTime.fst _ _))
  have hright : ComputableTidilyInPolyTime (fun x : α × List Bool => k * ofBits x.2)
      (encPair enc encBits) encNat := by
    have hread := ComputableTidilyInPolyTime.bitsToNat
    fun_prop
  have htest : ComputableTidilyInPolySpace (fun x : α × List Bool =>
      decide (f x.1 ≤ k * ofBits x.2) && decide (k * ofBits x.2 ≤ f x.1))
      (encPair enc encBits) encBool := by
    have hle := ComputableTidilyInPolySpace.of_polyTime ComputableTidilyInPolyTime.binary_le
    exact (ComputableTidilyInPolySpace.of_polyTime ComputableTidilyInPolyTime.bool_and).comp
      ((hle.comp (hleft.prod (.of_polyTime hright))).prod
        (hle.comp ((ComputableTidilyInPolySpace.of_polyTime hright).prod hleft)))
  have hB : {x : α × List Bool | f x.1 = k * ofBits x.2} ∈
      PSPACE (encPair enc encBits) :=
    mem_PSPACE_of_computableInPolySpace (.of_tidy htest) fun x => by
      simp only [Set.mem_ofPred_eq, Bool.and_eq_true, decide_eq_true_eq]
      exact le_antisymm_iff
  have hbound : ComputableTidilyInPolyTime (fun a => p.eval (enc a).length + 1)
      enc encUnary := by fun_prop
  have h := setOf_exists_mem_PSPACE hB (.of_tidy hbound)
  convert h using 1
  ext a
  rw [hA a]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hdiv
    have hlt : f a / k < 2 ^ (p.eval (enc a).length + 1) :=
      (Nat.div_le_self _ _).trans_lt ((hp a).trans_lt
        (Nat.pow_lt_pow_right (by norm_num) (by lia)))
    obtain ⟨hv, hl⟩ := BitString.iterate_increment _ _ hlt
    refine ⟨_, hl, ?_⟩
    rw [ofBits, ← BitString.lsbValue_eq_foldr_bit, hv]
    exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdiv)).symm
  · rintro ⟨w, _, hw⟩
    exact Nat.mod_eq_zero_of_dvd ⟨ofBits w, hw⟩

/-- Nonzero-modular counting is in polynomial space, for every fixed modulus. -/
theorem ModP_subset_PSPACE (k : ℕ) : ModP k enc ⊆ PSPACE enc := by
  intro A hA
  have hc : Aᶜ ∈ coModP k enc := by simpa [coModP] using hA
  simpa using compl_mem_PSPACE (coModP_subset_PSPACE k hc)

/-- Polynomial time with a PP word oracle stays within polynomial space. -/
theorem PWithOracle_subset_PSPACE_of_mem_PP {A : Set (List Bool)} (hA : A ∈ PP encBits) :
    PWithOracle A enc ⊆ PSPACE enc :=
  PWithOracle_subset_PSPACE (PP_subset_PSPACE hA)

/-- Nondeterministic polynomial time with a PP word oracle stays within polynomial space. -/
theorem NPWithOracle_subset_PSPACE_of_mem_PP {A : Set (List Bool)} (hA : A ∈ PP encBits) :
    NPWithOracle A enc ⊆ PSPACE enc :=
  NPWithOracle_subset_PSPACE (PP_subset_PSPACE hA)

end Cslib.Complexity
