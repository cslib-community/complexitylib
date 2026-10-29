/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.BitString.List.All
import Complexity.Computability.Complexity.Classes.SharpP.Probability
import Complexity.Computability.Complexity.Classes.PCP

/-! Exact repetition probabilities, boundary cases, and the counted-verifier bridge. -/

namespace ComplexityTests.VerifierProbability

open Cslib Cslib.Complexity Cslib.BitString Cslib.Probability
open scoped ENNReal

-- Empty repetition accepts even when the individual check always rejects.
example (width : ℕ) :
    ((uniformList (0 * width)).map
      (fun word => (List.range 0).all fun i => (fun _ => false) (listRow width i word)))
      true = 1 := by
  rw [uniformList_all_listRow_true 0 width (fun _ => false)]
  simp

-- Zero-width rows are still retained, and every one sees the empty word.
example : ((uniformList (3 * 0)).map
    (fun word => (List.range 3).all fun i => (listRow 0 i word).isEmpty)) true = 1 := by
  rw [uniformList_all_listRow_true 3 0 List.isEmpty]
  simp

example : ((uniformList (3 * 0)).map
    (fun word => (List.range 3).all fun i => (fun _ => false) (listRow 0 i word))) true = 0 := by
  rw [uniformList_all_listRow_true 3 0 (fun _ => false)]
  simp

private def firstBit (p : Unit × List Bool) : Bool := p.2.headD false

private theorem firstBit_count : acceptCount firstBit () 1 = 1 := by decide

-- Three disjoint fair-bit checks give an actual acceptance probability of one eighth.
example : (((uniformList (3 * 1)).map
    (fun word => (List.range 3).all fun i => (listRow 1 i word).headD false)) true).toReal =
      1 / 8 := by
  rw [uniformList_all_listRow_true 3 1 (fun word => word.headD false), ENNReal.toReal_pow]
  change (((uniformList 1).map (fun word => firstBit ((), word))) true).toReal ^ 3 = _
  rw [uniformList_acceptCount_toReal, firstBit_count]
  norm_num

-- A two-bit parity check accepts half the strings, independently in each block.
private def parityTwo (p : Unit × List Bool) : Bool :=
  p.2.getD 0 false ^^ p.2.getD 1 false

private theorem parityTwo_count : acceptCount parityTwo () 2 = 2 := by decide

example : (((uniformList (4 * 2)).map
    (fun word => (List.range 4).all fun i => parityTwo ((), listRow 2 i word))) true).toReal =
      1 / 16 := by
  rw [uniformList_all_listRow_true 4 2 (fun word => parityTwo ((), word)),
    ENNReal.toReal_pow, uniformList_acceptCount_toReal, parityTwo_count]
  norm_num

example : (((uniformList 1).map (fun word => firstBit ((), word))) true).toReal ≤ 1 / 2 :=
  (acceptCount_le_half_iff firstBit () 1).mp (by rw [firstBit_count]; decide)

example : ¬ (((uniformList 0).map (fun _ => true)) true).toReal ≤ 1 / 2 := by
  norm_num

private def firstBitVerifier : PCPVerifier Unit where
  coins _ := 1
  queries _ := []
  verdict p := firstBit p.1

-- The same bridge applies directly to the library's nonadaptive PCP verifier contract.
example :
    2 * acceptCount (fun p => firstBitVerifier.accepts p.1 [] p.2) () (firstBitVerifier.coins ()) ≤
      2 ^ firstBitVerifier.coins () :=
  (acceptCount_le_half_iff _ _ _).mpr
    ((acceptCount_le_half_iff firstBit () 1).mp (by rw [firstBit_count]; decide))

end ComplexityTests.VerifierProbability
