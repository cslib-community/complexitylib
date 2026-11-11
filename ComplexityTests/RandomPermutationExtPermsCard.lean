/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module
-- upstream: local-only (test driver)

import Complexity.Languages.Probabilistic.RandomPermutation.ExtPermsCard

/-! Direct clients of the permutation-extension counts, without any cipher import. -/

open Cslib Cslib.RandomPermutation

-- 1. Two prescribed values at two distinct points of `Fin 3`: at most `3! / (3 * 2) = 1`
-- permutation.
example (ys : Fin 2 → Fin 3) :
    (extPerms (List.ofFn fun i : Fin 2 =>
      ((⟨![0, 1], by decide⟩ : Fin 2 ↪ Fin 3) i, ys i))).card * 6 ≤ 6 := by
  simpa [Nat.factorial] using
    card_extPerms_ofFn_mul_descFactorial_le (⟨![0, 1], by decide⟩ : Fin 2 ↪ Fin 3) ys

-- 2. The extension counts over all injective target pairs in `Fin 3` sum to `3! = 6`.
example :
    ∑ e : Fin 2 ↪ Fin 3,
      (extPerms (List.ofFn fun i => ((⟨![0, 1], by decide⟩ : Fin 2 ↪ Fin 3) i, e i))).card = 6 := by
  simpa [Nat.factorial] using sum_card_extPerms_ofFn (⟨![0, 1], by decide⟩ : Fin 2 ↪ Fin 3)
