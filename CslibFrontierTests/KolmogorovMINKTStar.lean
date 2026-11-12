/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Kolmogorov.MINKTStar

/-!
Regression clients for the partial-string problem `MINKT*`: consistency, concrete yes- and
no-instances, `NP` membership and the reduction from `MINKT`.
-/

namespace CslibFrontierTests.KolmogorovMINKTStar

open Cslib Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod Cslib.Complexity
open _root_.Turing _root_.Turing.MultiTapeTM

/-! ### Consistency -/

-- `*` matches either bit; a specified bit must match; lengths must agree.
example : MINKTStar.Consistent [some true, none, some false] [true, true, false] := by decide
example : ¬ MINKTStar.Consistent [some true, none, some false] [false, true, false] := by decide
example : ¬ MINKTStar.Consistent [none, none] [true] := by decide

-- The Boolean test agrees with `Consistent`.
example : MINKTStar.consistentCheck [some true, none] [true, false] = true :=
  MINKTStar.consistentCheck_eq_true_iff.mpr (by decide)

/-! ### Non-vacuous instances -/

-- Yes-instance: an all-`*` pattern of length `n` is completed by the all-`false` string, which
-- the copy program prints within `n + 1` steps.
example (n : ℕ) :
    (⟨List.replicate n none, n + 1, n + copyOverhead⟩ : MINKTStar.Instance) ∈ MINKTStar := by
  refine MINKTStar.mk_mem_iff.mpr ⟨List.replicate n false, ?_, ?_⟩
  · rw [MINKTStar.consistent_iff]
    simp
  · simpa using timeBoundedAt_le_length_add (x := List.replicate n false) (by simp)

-- No-instance: a fully specified incompressible pattern of length `s + 1` at threshold `s`.
example (t s : ℕ) :
    ∃ x : List Bool, x.length = s + 1 ∧
      (⟨x.map some, t, s⟩ : MINKTStar.Instance) ∉ MINKTStar := by
  obtain ⟨x, hx, hall⟩ := exists_length_eq_forall_le_timeBounded (s + 1)
  refine ⟨x, hx, fun hmem => ?_⟩
  have hmem' : (⟨x, t, s⟩ : MINKT.Instance) ∈ MINKT :=
    MINKTStar.ofTotal_mem_iff.mp hmem
  have hle : ((s + 1 : ℕ) : ℕ∞) ≤ timeBoundedAt t x := hall (fun _ => t)
  exact absurd ((ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self s)).trans_le hle)
    (not_lt.mpr (MINKT.mk_mem_iff.mp hmem'))

/-! ### Complexity -/

example : MINKTStar ∈ NP MINKTStar.enc := MINKTStar.mem_NP

-- Fixed-threshold `MINKTAt` reduces to `MINKT*` through `MINKT`.
example (p q : Polynomial ℕ) :
    PolyTimeReducible encBits MINKTStar.enc (MINKTAt p.eval q.eval) MINKTStar :=
  (MINKTAt.polyTimeReducible_MINKT (ComputableInPolyTime.unary_eval p)
    (ComputableInPolyTime.unary_eval q)).trans MINKTStar.polyTimeReducible_MINKT_MINKTStar

end CslibFrontierTests.KolmogorovMINKTStar
