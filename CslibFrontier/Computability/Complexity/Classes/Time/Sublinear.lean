/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Sublinear

/-!
# Sublinear deterministic time classes

On all raw bit words, every sublinear deterministic time class equals constant time. The
native machine receives no separate input length, so its sublinear affine clock collapses
to a constant. This is the decision-class consequence of Goldreich's January 2007 draft
Exercise 4.3 (`r2.pdf`, PDF35/printed151) [Goldreich2007DraftR2].

The input encoding is explicitly `encBits`. An arbitrary encoding need not contain its
prefixes, and a certificate says nothing about invalid encoded inputs. No such generalization
or random-access-input claim is made.

## Main results

* `Cslib.Complexity.DTIME_eq_const_of_isLittleO`: `DTIME(t) = DTIME(1)` for `t = o(n)`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- A sublinear deterministic time bound on raw bit words gives exactly constant time.
The affine constants in `DTIME` are absorbed before applying the native collapse theorem. -/
theorem DTIME_eq_const_of_isLittleO {p : ℕ → ℕ}
    (hp : (fun n : ℕ => (p n : ℝ)) =o[Filter.atTop] (fun n : ℕ => (n : ℝ))) :
    DTIME encBits p = DTIME encBits (fun _ => 1) := by
  apply Set.Subset.antisymm
  · rintro L ⟨a, b, s, hL⟩
    have hp' : (fun n : ℕ => ((a * p n + b : ℕ) : ℝ)) =o[Filter.atTop]
        (fun n : ℕ => (n : ℝ)) := by
      simpa only [Nat.cast_add, Nat.cast_mul] using
        (hp.const_mul_left (a : ℝ)).add
          (Asymptotics.isLittleO_const_id_atTop (b : ℝ)).natCast_atTop
    change ComputableInTimeAndSpace (indicator L) encBits encBool
      (fun x => a * p x.length + b) (fun x => s x.length) at hL
    obtain ⟨C, hC⟩ := ComputableInTimeAndSpace.exists_const_time_of_isLittleO hL hp'
    refine ⟨0, C, s, ?_⟩
    simpa only [DecidableInTimeAndSpace, encBits_apply, encBool, Nat.zero_mul, Nat.zero_add]
      using hC
  · exact DTIME_mono_of_le_mul_add (C := 1) fun _ => by omega

end Cslib.Complexity
