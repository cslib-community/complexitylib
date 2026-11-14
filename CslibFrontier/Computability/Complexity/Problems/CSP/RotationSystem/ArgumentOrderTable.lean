/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate

/-!
# Raw argument-order checks depend only on constraint-end lookups

The original positional argument-order checker reads only the odd entry for each actual
occurrence. Agreement on these entries preserves its complete Boolean result, even for
malformed tables. This original table identity makes no rotation or genus assertion.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

/-- Agreement at every actual constraint-end position preserves the exact argument-order
check, without a wellformedness or certificate-length premise. Variable-end entries and
out-of-range entries are unrestricted. -/
theorem verifyArgumentOrder_congr {Rel V : Type} (F : CSP Rel V)
    (c d : Graph.RotationCertificate)
    (h : ∀ i < F.occurrences.length,
      c.successor.getD (2 * i + 1) 0 = d.successor.getD (2 * i + 1) 0) :
    verifyArgumentOrder F c = verifyArgumentOrder F d := by
  apply Bool.eq_iff_iff.mpr
  simp only [verifyArgumentOrder, List.all_eq_true, decide_eq_true_eq]
  apply forall_congr'
  intro entry
  apply forall_congr'
  intro he
  have hi := List.snd_lt_add_of_mem_zipIdx he
  rw [h entry.2 (by simpa only [Nat.zero_add] using hi)]

end Cslib.Complexity.CSP
