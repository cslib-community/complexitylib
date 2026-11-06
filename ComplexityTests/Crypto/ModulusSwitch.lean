/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.SIS.ModulusSwitch

/-! Canonical lifts, negative half ties, modulus-one boundaries, and an actual Module-LWE phase.
The explicit carry example includes negacyclic wraparound at degree two. -/

namespace ComplexityTests.Crypto.ModulusSwitch

open Cslib.Crypto
open scoped Matrix

/-- The canonical lift of the source midpoint is positive. -/
example : (5 : ZMod 10).valMinAbs = 5 := by decide

/-- A negative half tie rounds towards positive infinity, not away from zero. -/
example : round ((3 : ℚ) / 10 * (-5)) = -1 := by norm_num [round_eq]

example : ZMod.modulusSwitch 3 (-5 : ZMod 10) = 2 := by
  norm_num [ZMod.modulusSwitch, show (-5 : ZMod 10).valMinAbs = 5 by decide, round_eq]

example : ZMod.modulusSwitch 3 (5 : ZMod 10) = 2 := by
  norm_num [ZMod.modulusSwitch, show (5 : ZMod 10).valMinAbs = 5 by decide, round_eq]

example : ZMod.modulusSwitch 6 (-3 : ZMod 10) = 4 := by
  norm_num [ZMod.modulusSwitch, show (-3 : ZMod 10).valMinAbs = -3 by decide, round_eq]
  decide

/-- Arbitrary negative representatives give the same residue after conversion. -/
example : ZMod.modulusSwitch 3 (-25 : ZMod 10) =
    (round ((3 : ℚ) / 10 * (-25)) : ℤ) := by
  have h := ZMod.modulusSwitch_intCast (p := 3) (q := 10) (by decide) (-25)
  norm_num [round_eq] at h ⊢
  exact h

example : ZMod.modulusSwitch 6 (7 : ZMod 1) = 0 := by
  norm_num [ZMod.modulusSwitch, show (7 : ZMod 1).valMinAbs = 0 by decide, round_eq]

example : ZMod.modulusSwitch 1 (-3 : ZMod 10) = 0 := Subsingleton.elim _ _

/-- Rounding is not additive: this conversion is not a ring homomorphism. -/
example : ZMod.modulusSwitch 3 ((1 : ZMod 10) + 1) ≠
    ZMod.modulusSwitch 3 (1 : ZMod 10) + ZMod.modulusSwitch 3 (1 : ZMod 10) := by
  norm_num [ZMod.modulusSwitch, show (1 : ZMod 10).valMinAbs = 1 by decide,
    show (2 : ZMod 10).valMinAbs = 2 by decide, round_eq]

private def ct : ModuleLWECiphertext 1 2 10 := (![![4, -3]], ![1, 4])
private def secret : Fin 1 → Fin 2 → ℤ := ![![1, -1]]

private theorem switched_ct : moduleLWEModulusSwitch 6 ct = (![![2, 4]], ![1, 2]) := by
  norm_num [moduleLWEModulusSwitch, ct, ZMod.modulusSwitch,
    show (4 : ZMod 10).valMinAbs = 4 by decide,
    show (-3 : ZMod 10).valMinAbs = -3 by decide,
    show (1 : ZMod 10).valMinAbs = 1 by decide, round_eq,
    funext_iff, Fin.forall_fin_succ]
  decide

example : ct.2 - innerPoly ct.1 (fun j i => (secret j i : ZMod 10)) = ![0, 1] := by
  decide

example : (moduleLWEModulusSwitch 6 ct).2 -
    innerPoly (moduleLWEModulusSwitch 6 ct).1 (fun j i => (secret j i : ZMod 6)) =
    ![1, 0] := by
  rw [switched_ct]
  decide

/-- A nonzero carry is needed: the integer phase is `(0, 11)`, not `(0, 1)`. -/
example : (![1, 4] : Fin 2 → ℤ) - innerPoly (![![4, -3]] : Fin 1 → Fin 2 → ℤ) secret =
    fun i => (![0, 1] : Fin 2 → ℤ) i + 10 * (![0, 1] : Fin 2 → ℤ) i := by decide

/-- The generic carry theorem applies to this ciphertext and supplies the claimed phase bound. -/
example : ∃ e' : Fin 2 → ℤ,
    (moduleLWEModulusSwitch 6 ct).2 -
        innerPoly (moduleLWEModulusSwitch 6 ct).1 (fun j i => (secret j i : ZMod 6)) =
      (fun i => (e' i : ZMod 6)) ∧
    ∀ i, |(e' i : ℚ) - (3 / 5 : ℚ) * (![0, 1] : Fin 2 → ℤ) i| ≤ 3 / 2 := by
  obtain ⟨e', he', hnear, _⟩ := exists_moduleLWEModulusSwitch_phase_of_lifts
    (by decide : 0 < 10) (by decide : 0 < 6) ct ![![4, -3]] secret ![1, 4] ![0, 1] ![0, 1]
    (by decide) (by decide) (by decide)
  refine ⟨e', he', ?_⟩
  norm_num [secret, Fin.sum_univ_succ] at hnear ⊢
  exact hnear

/-- Canonical-phase interpretation requires no supplied no-wrap or carry hypothesis. -/
example (ciphertext : ModuleLWECiphertext 1 2 10) : ∃ e' : Fin 2 → ℤ,
    (moduleLWEModulusSwitch 6 ciphertext).2 -
        innerPoly (moduleLWEModulusSwitch 6 ciphertext).1
          (fun j i => (secret j i : ZMod 6)) = (fun i => (e' i : ZMod 6)) ∧
    ∀ i, |(e' i : ℚ)| ≤ (3 / 5 : ℚ) *
      |(((ciphertext.2 - innerPoly ciphertext.1
        (fun j l => (secret j l : ZMod 10))) i).valMinAbs : ℚ)| + 3 / 2 := by
  obtain ⟨e', he', _, habs⟩ := exists_moduleLWEModulusSwitch_phase
    (by decide : 0 < 10) (by decide : 0 < 6) ciphertext secret
  refine ⟨e', he', ?_⟩
  norm_num [secret, Fin.sum_univ_succ] at habs ⊢
  exact habs

/-- Source and target modulus one are allowed, with an actual instance of the phase theorem. -/
example (ciphertext : ModuleLWECiphertext 1 2 1) : ∃ e' : Fin 2 → ℤ,
    (moduleLWEModulusSwitch 1 ciphertext).2 -
        innerPoly (moduleLWEModulusSwitch 1 ciphertext).1
          (fun j i => (secret j i : ZMod 1)) = (fun i => (e' i : ZMod 1)) := by
  obtain ⟨e', he', _, _⟩ := exists_moduleLWEModulusSwitch_phase
    (by decide : 0 < 1) (by decide : 0 < 1) ciphertext secret
  exact ⟨e', he'⟩

end ComplexityTests.Crypto.ModulusSwitch
