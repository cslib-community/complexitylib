/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n

/-!
# Tests for the `4n - 10d` circuit lower bound

Non-vacuous client examples checking `0/6` parameter weights, zero-locus pair operations (`addPair`,
`restrict`), concrete `2`- and `4`-input circuits against `four_mul_le_size_add`,
`exists_affine_subspace_const_of_size_lt`, `exists_disagreeing_input_of_size_lt`, and concrete
numerical consequences (`390 ≤ C.size` at `n = 100, d = 1`).
-/

namespace CslibFrontierTests.AffineDisperser4n

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.AffineDisperser4n

/-- Basic checks on `0/6` weights and zero-locus pairs. -/
example : weight 0 = 0 ∧ weight 1 = 6 ∧ weight 3 = 6 ∧
    (⟨0, false, 1, true⟩ : ZeroPair).Holds (fun i => if i = 0 then false else false) ∧
    ¬ (⟨0, false, 1, true⟩ : ZeroPair).Holds (fun i => if i = 0 then true else false) := by
  refine ⟨rfl, rfl, rfl, Or.inl rfl, ?_⟩
  decide

/-- A concrete `2`-input `2`-affine disperser `f x = x 0 && x 1` and a `1`-gate circuit computing
it, witnessing `4 * 2 ≤ 1 + 10 * 2`. -/
private def and2Fn : BooleanFunction 2 := fun x => x 0 && x 1

private theorem and2Fn_disperser : IsAffineDisperser and2Fn 2 := by
  intro g _ hinj
  have himg : (Finset.univ.image g : Finset (BitString 2)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by
      rw [Finset.card_image_of_injective _ hinj]
      decide)
  obtain ⟨u, _, hu⟩ := Finset.mem_image.1 (himg ▸ Finset.mem_univ (fun _ => false))
  obtain ⟨v, _, hv⟩ := Finset.mem_image.1 (himg ▸ Finset.mem_univ (fun _ => true))
  exact ⟨u, v, by rw [hu, hv]; decide⟩

private def and2Circuit : Circuit (fullSignature 2 Bool) 2 1 :=
  ⟨Program.gate Program.empty
    ⟨FullOp.fn fun xs => xs 0 && xs 1, fun i => Wire.input i⟩,
    fun _ => Wire.gate ⟨0, by decide⟩⟩

example : and2Circuit.size = 1 ∧ 4 * 2 ≤ and2Circuit.size + 10 * 2 := by
  have hcomp : and2Circuit.Computes fullInterpretation (single and2Fn) := by
    intro x
    ext i
    rw [Fin.eq_zero i]
    rfl
  exact ⟨rfl, four_mul_le_size_add and2Fn_disperser and2Circuit hcomp⟩

/-- A `0`-gate circuit on `4` bits has `size + 10 * 1 < 4 * 4`, so it is constant on some
`1`-dimensional injective affine subspace and must disagree with any `1`-affine disperser. -/
private def proj4Circuit : Circuit (fullSignature 2 Bool) 4 1 :=
  ⟨Program.empty, fun _ => Wire.input ⟨0, by decide⟩⟩

example : ∃ g : BitString 1 → BitString 4, IsAffine g ∧ Function.Injective g ∧
    ∃ b : Bool, ∀ u, proj4Circuit.eval fullInterpretation (g u) 0 = b :=
  exists_affine_subspace_const_of_size_lt proj4Circuit (by decide)

example {f : BooleanFunction 4} (hf : IsAffineDisperser f 1) :
    ∃ x : BitString 4, proj4Circuit.eval fullInterpretation x 0 ≠ f x :=
  exists_disagreeing_input_of_size_lt hf proj4Circuit (by decide)

/-- Non-trivial numerical consequence at `n = 100, d = 1`: `390 ≤ C.size`, strictly improving on
the earlier `3.5n - 7d` bound (`343 ≤ C.size`). -/
example {f : BooleanFunction 100} (hf : IsAffineDisperser f 1)
    (C : Circuit (fullSignature 2 Bool) 100 1)
    (hC : C.Computes fullInterpretation (single f)) : 390 ≤ C.size := by
  have h := four_mul_le_size_add hf C hC
  omega

/-- Exercise `(PC)` (`addPair`) on an initial state of `and2Circuit`: pairing `(0, false, 1, false)`
preserves validity and lowers potential by `8`. -/
example :
    let S := initialState and2Circuit
    let pr : ZeroPair := ⟨0, false, 1, false⟩
    S.AddPairOK pr ∧ (S.addPair pr).Valid and2Fn ∧ (S.addPair pr).a + 1 = S.a := by
  have hcomp : and2Circuit.Computes fullInterpretation (single and2Fn) := by
    intro x; ext i; rw [Fin.eq_zero i]; rfl
  have hS : (initialState and2Circuit).Valid and2Fn := initialState_valid hcomp
  have hok : (initialState and2Circuit).AddPairOK ⟨0, false, 1, false⟩ :=
    ⟨by decide, by decide, by decide⟩
  refine ⟨hok, hS.addPair hok, ?_⟩
  have hq := State.addPair_q hok
  have hm : ((initialState and2Circuit).addPair ⟨0, false, 1, false⟩).m =
      (initialState and2Circuit).m := by
    simp [State.m, State.addPair_params]
  have hqm := hS.q_le_m
  have hqm' := (hS.addPair hok).q_le_m
  unfold State.a at *
  omega

end CslibFrontierTests.AffineDisperser4n
