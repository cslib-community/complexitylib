/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterProofs

/-!
# Tests for the deterministic `4n - 10d` refuter
-/

public section

namespace CslibFrontierTests.AffineDisperser4nRefuter

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.AffineDisperser4n
open Cslib.Circuits.Boolean.SemiCircuit

/-- A `0`-gate circuit on `4` bits has `size + 10 * 1 < 4 * 4`. -/
def proj4Circuit : Circuit (fullSignature 2 Bool) 4 1 :=
  ⟨Program.empty, fun _ => Wire.input ⟨0, by decide⟩⟩

/-- Concrete instantiation of `refute_correct` on `proj4Circuit` for `d = 1`. -/
theorem proj4_refute_disagrees (f : BitString 4 → Bool) (hf : IsAffineDisperser f 1) :
    proj4Circuit.eval fullInterpretation (@refute 4 1 proj4Circuit f) 0 ≠
      f (@refute 4 1 proj4Circuit f) :=
  refute_correct proj4Circuit f hf (by decide)

/-- Non-vacuous instantiation at `n = 100, d = 11` using `exists_isAffineDisperser`. -/
def proj100Circuit : Circuit (fullSignature 2 Bool) 100 1 :=
  ⟨Program.empty, fun _ => Wire.input ⟨0, by decide⟩⟩

/-- There exists a genuine `11`-affine disperser on `100` bits on which `refute` produces a
disagreeing input against `proj100Circuit`. -/
theorem exists_disperser_refute_disagrees :
    ∃ f : BitString 100 → Bool, IsAffineDisperser f 11 ∧
      proj100Circuit.eval fullInterpretation (@refute 100 11 proj100Circuit f) 0 ≠
        f (@refute 100 11 proj100Circuit f) := by
  obtain ⟨f, hf⟩ := exists_isAffineDisperser (n := 100) (d := 11) (by norm_num)
  exact ⟨f, hf, refute_correct proj100Circuit f hf (by decide)⟩

/-- Initial state of `proj4Circuit` is already terminal (`chooseStep? = none`) because its output
reads a parameter directly. -/
example : chooseStep? (initialState proj4Circuit) = none :=
  rfl

/--
info: 'Cslib.Circuits.Boolean.AffineDisperser4n.applyStep_valid' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms applyStep_valid

/--
info: 'Cslib.Circuits.Boolean.AffineDisperser4n.refuterLoop_valid' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refuterLoop_valid

/--
info: 'Cslib.Circuits.Boolean.AffineDisperser4n.refute_correct' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms refute_correct

end CslibFrontierTests.AffineDisperser4nRefuter
