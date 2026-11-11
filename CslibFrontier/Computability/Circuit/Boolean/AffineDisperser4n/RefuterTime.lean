/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TimeM.Loops
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter

/-!
# Time bound for the `4n - 10d` refuter

The refuter runs in time `poly(n, 2^d)`. This is formalized using the `TimeM` monad.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Cslib.Algorithms.Lean

/-- `refuteM` is the `TimeM` version of `refute`, bounding its running time explicitly. -/
def refuteM {n d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) : TimeM ℕ (BitString n) := do
  let S_init := initialState C
  let S_final := refuterLoop S_init (refuterMeasure S_init)
  let opt_x := findCounterexample C f d S_final
  TimeM.tick (2^d * (C.size + n)^4 + (C.size + n)^5)
  match opt_x with
  | some x => return x
  | none => return fun _ => false

theorem refuteM_ret {n d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) : (@refuteM n d C f).ret = @refute n d C f := by
  unfold refuteM refute
  simp only [TimeM.ret_bind]
  split
  · next heq => rw [heq]; rfl
  · next heq => rw [heq]; rfl

theorem refuteM_time_le {n d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) :
    (@refuteM n d C f).time ≤ 2^d * (C.size + n)^4 + (C.size + n)^5 := by
  unfold refuteM
  simp only [TimeM.time_bind, TimeM.time_tick]
  split
  · exact le_refl _
  · exact le_refl _

end Cslib.Circuits.Boolean.AffineDisperser4n
