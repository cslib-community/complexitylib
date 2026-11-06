/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.PMF.Option.Bind
import Mathlib.Tactic.NormNum

/-! Optional success laws retain abort contributions under genuinely randomized continuations. -/

open Cslib.Probability
open scoped ENNReal

namespace ComplexityTests.PMFOptionBind

private theorem half_success (a : Unit) :
    PMF.uniformOfFintype (Option Unit) (some a) =
      (1 / 2 : ℝ≥0∞) * PMF.pure () a := by
  cases a
  norm_num [PMF.uniformOfFintype_apply]

-- Failure accepts, while success flips a fresh fair bit: dropping failure would give 1/4.
example :
    (((PMF.uniformOfFintype (Option Unit)).bind
      (fun out => out.elim (PMF.pure true) (fun _ => PMF.uniformOfFintype Bool)))
      true).toReal = 3 / 4 := by
  rw [PMF.bind_option_apply_of_some _ (PMF.pure ()) (1 / 2) half_success]
  norm_num only [PMF.uniformOfFintype_apply, Fintype.card_option, Fintype.card_unit,
    Nat.cast_ofNat, Nat.reduceAdd, PMF.pure_apply_self, mul_one, PMF.pure_bind,
    Option.elim_none, Option.elim_some, Fintype.card_bool]
  rw [ENNReal.toReal_add (by simp) (ENNReal.mul_ne_top (by simp) (by simp))]
  norm_num

-- The same successful continuation has mass 1/4 when the actual failure branch rejects.
example :
    (((PMF.uniformOfFintype (Option Unit)).bind
      (fun out => out.elim (PMF.pure false) (fun _ => PMF.uniformOfFintype Bool)))
      true).toReal = 1 / 4 := by
  rw [PMF.bind_option_apply_of_some _ (PMF.pure ()) (1 / 2) half_success]
  norm_num [PMF.uniformOfFintype_apply, ENNReal.toReal_add]

-- Zero success mass is permitted; the continuation of the certain failure remains observable.
example (k : Option Unit → PMF Bool) (b : Bool) :
    ((PMF.pure none).bind k) b = (PMF.pure (none : Option Unit)) none * k none b +
      (0 : ℝ≥0∞) * ((PMF.pure ()).bind (fun a => k (some a))) b :=
  PMF.bind_option_apply_of_some _ _ 0 (by simp) k b

end ComplexityTests.PMFOptionBind
