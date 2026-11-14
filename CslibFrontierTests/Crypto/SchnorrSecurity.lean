/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SchnorrSignature.Security
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import Mathlib.Tactic.NormNum.Prime

/-!
# Schnorr forking adversary regressions

Check the extraction step of the two-pass forking adversary in the order-11 subgroup modulo `23`:
it extracts only when the first pass names a query, the second pass names the same query, and the
two answers there differ; and then it outputs `(c - c')⁻¹ (z - z')` modulo the group order.
-/

namespace CslibFrontierTests.Crypto.SchnorrSecurity

open Cslib Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM

private def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

private def answers : List (List Bool) := [[true], [false]]

private def answers' : List (List Bool) := [[false], [false]]

-- Distinct answers at query `0`, challenges `1` and `0`, responses `3` and `1`:
-- the witness is `(1 - 0)⁻¹ (3 - 1) = 2` modulo `11`.
example : schnorrGroups.schnorrForkOutput d23 answers answers' (1, [true], [true, true])
    (1, [false], [true]) = [false, true] := by
  decide

-- No named query: nothing is extracted.
example : schnorrGroups.schnorrForkOutput d23 answers answers' (0, [true], [true, true])
    (1, [false], [true]) = [] := by
  decide

-- The second pass names another query: nothing is extracted.
example : schnorrGroups.schnorrForkOutput d23 answers answers' (1, [true], [true, true])
    (2, [false], [true]) = [] := by
  decide

-- Equal answers at the named query: nothing is extracted.
example : schnorrGroups.schnorrForkOutput d23 answers answers' (2, [true], [true, true])
    (2, [false], [true]) = [] := by
  decide

end CslibFrontierTests.Crypto.SchnorrSecurity
