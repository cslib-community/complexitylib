/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.BooleanSearch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable

/-!
# Bounded existential search with independent resources

A test is run on the words of a runtime unary width, retaining the context and one candidate.
The search reuses the test's workspace. Its time is the number of candidates times the test-time
bound and polynomial bookkeeping; its space is the test-space bound plus polynomial bookkeeping.
Neither test bound has to be polynomial or monotone. The list of all candidates is used only in
the specification, not stored by the native machine.
## Main results

* `Turing.MultiTapeTM.ComputableInO.exists_bits`: streamed existential search with independent
  test-time and test-space bounds, plus polynomial bookkeeping.
* `Turing.MultiTapeTM.IsComputable.exists_bits`, `Turing.MultiTapeTM.IsComputable.forall_bits`:
  bounded existential and universal search over words of exact unary length preserve
  `IsComputable`.

-/

public section

namespace Turing.MultiTapeTM

open Cslib.GenericRAM

/-- **Bounded existential search.** Uniform bounds on the tests of words of width `n` give a
single search machine for all contexts and widths. The polynomial overhead includes encoding
conversion, binary counters, preparation and the retained input. Encoded outputs are charged to
space, as in `ComputableInO`; this is not a sublinear transducer-space theorem. -/
theorem ComputableInO.exists_bits {C : Type} {encC : C ↪ List Bool}
    {test : C × List Bool → Bool} {Tf Sf : C × List Bool → ℕ}
    (hf : ComputableInO test (encPair encC encBits) encBool Tf Sf)
    {T S : C × ℕ → ℕ}
    (hT : ∀ p w, w.length = p.2 → Tf (p.1, w) ≤ T p)
    (hS : ∀ p w, w.length = p.2 → Sf (p.1, w) ≤ S p) :
    ∃ overhead : C × ℕ → ℕ,
      PolyBounded (fun p => (encPair encC encUnary p).length) overhead ∧
      ComputableInO (fun p => (Cslib.BitString.enumList p.2).any fun w => test (p.1, w))
        (encPair encC encUnary) encBool
        (fun p => (2 ^ p.2 + 1) * (overhead p + T p)) (fun p => overhead p + S p) := by
  have hconvert : ComputableInPolyTime (fun p : C × List Bool => p)
      (encPair encC (encList encBool)) (encPair encC encBits) :=
    (ComputableInPolyTime.fst _ _).prod
      (ComputableInPolyTime.listToBits.comp (ComputableInPolyTime.snd _ _))
  obtain ⟨Tc, Sc, hTc, hSc, hc⟩ := hconvert.exists_computableInO
  let ct : NativeCertificate test (encPair encC (encList encBool)) encBool :=
    ⟨fun p => Tc p + Tf p, fun p => Sc p + Sf p,
      by simpa only [Function.comp_def] using hf.comp hc⟩
  let size := fun p : C × ℕ => (encPair encC encUnary p).length
  let B := fun p : C × ℕ => 2 * (encC p.1).length + 3 * p.2 + 1
  have hlen (p : C × ℕ) (w : List Bool) (hw : w.length = p.2) :
      (encPair encC (encList encBool) (p.1, w)).length ≤ B p := by
    simp [length_encList, encBool_apply, hw, B]
    omega
  obtain ⟨a, b, ht⟩ := hTc.exists_le
  obtain ⟨c, d, hs⟩ := hSc.exists_le
  let PT := fun p => a * (B p + 1) ^ b
  let PS := fun p => c * (B p + 1) ^ d
  obtain ⟨overhead, ho, h⟩ := BooleanSearch.exists_computableInO_of_bounds ct
    (T := fun p => PT p + T p) (S := fun p => PS p + S p)
    (fun p w hw => Nat.add_le_add
      ((ht _).trans (Nat.mul_le_mul_left a
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hlen p w hw) 1) b))) (hT p w hw))
    (fun p w hw => Nat.add_le_add
      ((hs _).trans (Nat.mul_le_mul_left c
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hlen p w hw) 1) d))) (hS p w hw))
  have hB : PolyBounded size B := (PolyBounded.self.mul (.const 3)).mono fun p => by
    simp only [size, B, length_encPair, encUnary_apply, List.length_replicate]
    omega
  have hpost := (ComputableInDegree.isSome (encList encBool)).inO_one.comp_linear h
  have heq (p : C × ℕ) : (BooleanSearch.run test p).isSome =
      (Cslib.BitString.enumList p.2).any (fun w => test (p.1, w)) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true]
    constructor
    · intro hp
      have hn : BooleanSearch.run test p ≠ none := by intro hn; simp [hn] at hp
      obtain ⟨w, hw, ht⟩ := (BooleanSearch.run_ne_none_iff test p).mp hn
      exact ⟨w, Cslib.BitString.mem_enumList.mpr hw, ht⟩
    · rintro ⟨w, hw, ht⟩
      have hn := (BooleanSearch.run_ne_none_iff test p).mpr
        ⟨w, Cslib.BitString.mem_enumList.mp hw, ht⟩
      cases hh : BooleanSearch.run test p with
      | none => exact (hn hh).elim
      | some _ => rfl
  refine ⟨fun p => overhead p + PT p + PS p,
    (ho.add (NativeCertificate.polyBounded_pow_of_polyBounded hB a b)).add
      (NativeCertificate.polyBounded_pow_of_polyBounded hB c d),
    (hpost.of_enc_eq fun p => congrArg encBool (heq p).symm).mono_le ?_ ?_⟩
  · intro p; dsimp only [Function.comp_apply]; exact Nat.mul_le_mul_left _ (by omega)
  · intro p; dsimp only [Function.comp_apply]; omega

/-- Bounded existential search over words of exact unary length preserves `IsComputable`. -/
theorem IsComputable.exists_bits {C : Type} {encC : C ↪ List Bool}
    {test : C × List Bool → Bool} (htest : IsComputable test (encPair encC encBits) encBool) :
    IsComputable (fun p : C × ℕ => (Cslib.BitString.enumList p.2).any fun w => test (p.1, w))
      (encPair encC encUnary) encBool := by
  obtain ⟨Tf, Sf, hc⟩ := htest
  have hcO : ComputableInO test (encPair encC encBits) encBool Tf Sf :=
    ⟨1, hc.mono (fun _ => by omega) fun _ => by omega,
      fun x => by cases test x <;> (simp only [encBool_apply, List.length_singleton]; omega)⟩
  let T : C × ℕ → ℕ := fun p => listMax (fun w => Tf (p.1, w)) (Cslib.BitString.enumList p.2)
  let S : C × ℕ → ℕ := fun p => listMax (fun w => Sf (p.1, w)) (Cslib.BitString.enumList p.2)
  obtain ⟨_, _, _, hsearch, -⟩ := ComputableInO.exists_bits hcO (T := T) (S := S)
    (fun p w hw => le_listMax (f := fun w => Tf (p.1, w)) (Cslib.BitString.mem_enumList.mpr hw))
    (fun p w hw => le_listMax (f := fun w => Sf (p.1, w)) (Cslib.BitString.mem_enumList.mpr hw))
  exact hsearch.isComputable

/-- Bounded universal search over words of exact unary length preserves `IsComputable`. -/
theorem IsComputable.forall_bits {C : Type} {encC : C ↪ List Bool}
    {test : C × List Bool → Bool} (htest : IsComputable test (encPair encC encBits) encBool) :
    IsComputable (fun p : C × ℕ => (Cslib.BitString.enumList p.2).all fun w => test (p.1, w))
      (encPair encC encUnary) encBool := by
  have hnot := (IsComputable.of_finite (encIn := encBool) (encMid := encBool) Bool.not).comp
    (((IsComputable.of_finite (encIn := encBool) (encMid := encBool) Bool.not).comp
      htest).exists_bits)
  convert hnot using 1
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, List.all_eq_true, Bool.not_eq_true', List.any_eq_false]
  exact forall₂_congr fun x _ => by cases test (p.1, x) <;> decide

end Turing.MultiTapeTM
