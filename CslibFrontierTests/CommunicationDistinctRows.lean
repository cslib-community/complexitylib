/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Communication.DistinctRows

/-!
Regression clients for the distinct-row count of zero/one matrices and the rank bounds of
[AroraBarak07, Chapter 12, Exercises 4 and 6]: equality on `n`-bit strings has pairwise distinct
rows, and the constant function has rank zero, hence a one-bit protocol.
-/

open Cslib Cslib.Communication

namespace CommunicationDistinctRowsTests

/-- Equality on `n`-bit strings has pairwise distinct rows, so it needs `⌈log₂ n⌉` bits. -/
example (n : ℕ) :
    (Nat.clog 2 n : ℕ∞) ≤ Protocol.ecomplexityFun fun x y : BitString n => decide (x = y) :=
  clog_le_ecomplexityFun_of_injective fun x x' h => by simpa [eq_comm] using congrFun h x

/-- The rows of equality on `n`-bit strings are distinct, so its rank over `ℚ` is at least `n`. -/
example (n : ℕ) :
    n ≤ (communicationMatrix ℚ fun x y : BitString n => decide (x = y)).rank :=
  le_rank_of_injective ℚ fun x x' h => by simpa [eq_comm] using congrFun h x

/-- A constant function has a rank-zero matrix, so the rank upper bound gives one bit. -/
example : Protocol.ecomplexityFun (fun (_ : Bool) (_ : Bool) => false) ≤ 1 := by
  have h := ecomplexityFun_le_rank_add_one ℚ fun (_ : Bool) (_ : Bool) => false
  have h0 : communicationMatrix ℚ (fun (_ : Bool) (_ : Bool) => false) = 0 := by
    ext; simp
  simpa [h0] using h

end CommunicationDistinctRowsTests
