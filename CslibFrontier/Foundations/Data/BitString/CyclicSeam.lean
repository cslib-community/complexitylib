/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Logic.Equiv.Fin.Rotate
import CslibFrontier.Foundations.Data.BitString.CyclicDifference

/-!
# Uniform shifts between cyclic corner colors

Two cyclic corner-color tuples have the same edge differences when their neighboring
entry and exit colors agree with the same indexed edge bits.
Their cyclic differences therefore agree. The existing cyclic-difference kernel theorem
supplies one uniform shift for the entire tuple. At arity zero the shift is explicitly false.
-/

public section

namespace Cslib.BitString

/-- Cyclic corner-color tuples with matching edge bits admit one uniform Boolean shift.
At arity zero, `false` supplies the shift without selecting a coordinate. -/
theorem exists_uniform_colorSeam {n : ℕ}
    (sourceCenter sourceVariable gadgetVariable gadgetCenter : Fin n → Bool)
    (hs : ∀ i, sourceCenter (finRotate n i) = sourceVariable i)
    (hg : ∀ i, gadgetVariable (finRotate n i) = gadgetCenter i)
    (he : ∀ i, (sourceCenter i ^^ sourceVariable i) =
      (gadgetVariable i ^^ gadgetCenter i)) :
    ∃ K : Bool, (n = 0 → K = false) ∧
      (∀ i, (gadgetVariable i ^^ K) = sourceCenter i) ∧
      ∀ i, (gadgetCenter i ^^ K) = sourceVariable i := by
  cases n with
  | zero => exact ⟨false, fun _ => rfl, fun i => i.elim0, fun i => i.elim0⟩
  | succ n =>
    have hd : Cslib.BitString.cyclicDifference sourceCenter =
        Cslib.BitString.cyclicDifference gadgetVariable := by
      funext i
      simpa only [Cslib.BitString.cyclicDifference, hs, hg] using he i
    have hz : Cslib.BitString.cyclicDifference (sourceCenter + gadgetVariable) =
        (fun _ => false) := by
      rw [Cslib.BitString.cyclicDifference_add, hd]
      funext i
      exact Bool.xor_self _
    obtain ⟨K, hK⟩ := (Cslib.BitString.cyclicDifference_eq_zero_iff _).mp hz
    have hcenter (i : Fin (n + 1)) : (gadgetVariable i ^^ K) = sourceCenter i := by
      have hi := congrFun hK i
      change (sourceCenter i ^^ gadgetVariable i) = K at hi
      rw [← hi, Bool.xor_left_comm, Bool.xor_self, Bool.xor_false]
    refine ⟨K, by omega, hcenter, fun i => ?_⟩
    rw [← hg i, hcenter, hs]

end Cslib.BitString
