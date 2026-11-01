/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.RankDecoder

/-! Exact rank decoding: unequal leaf masses, empty branches, and no-randomness boundaries. -/

namespace ComplexityTests.RankDecoder

open Cslib Cslib.BitString Cslib.BitString.RankDecoder Cslib.Probability

private def unevenMass : List Bool → ℕ
  | [] => 4
  | [false] => 1
  | [true] => 3
  | [false, false] => 1
  | [true, false] => 1
  | [true, true] => 2
  | _ => 0

private theorem unevenMass_add (pre : List Bool) (h : pre.length < 2) :
    unevenMass pre = unevenMass (pre ++ [false]) + unevenMass (pre ++ [true]) := by
  rcases pre with _ | ⟨bit, suffix⟩
  · decide
  rcases suffix with _ | ⟨next, suffix⟩
  · cases bit <;> decide
  · simp only [List.length_cons] at h
    omega

-- The rank at the first boundary moves right; the last leaf receives two ranks.
example : ([0, 1, 2, 3].map (decode unevenMass 2 [])) =
    [[false, false], [true, false], [true, true], [true, true]] := by decide

-- A zero-mass leaf has no preimages, even though the decoder remains total on every rank.
example : ((Finset.range 4).filter
    (fun rank => decode unevenMass 2 [] rank = [false, true])).card = 0 := by
  simpa only [unevenMass, List.length_cons, List.length_nil, List.nil_append,
    Nat.reduceAdd, ite_true] using
    card_filter_decode unevenMass_add 2 [] (by simp) [false, true]

-- Two fair seed bits give the unequal leaf its exact probability, not independent output bits.
example : (((uniformList 2).map (fun seed =>
    decode unevenMass 2 [] (binaryValue seed))) [true, true]).toReal = 1 / 2 := by
  rw [uniformList_decode_apply unevenMass_add 2 (by decide)]
  norm_num [unevenMass, ENNReal.toReal_div]

example : ((uniformList 2).map (fun seed =>
    decode unevenMass 2 [] (binaryValue seed))) [false, true] = 0 := by
  rw [uniformList_decode_apply unevenMass_add 2 (by decide)]
  norm_num [unevenMass]

-- A word of the wrong length receives no mass, including a prefix of a positive-mass leaf.
example : ((uniformList 2).map (fun seed =>
    decode unevenMass 2 [] (binaryValue seed))) [true] = 0 := by
  rw [uniformList_decode_apply unevenMass_add 2 (by decide)]
  simp

-- No output bits and no seed bits give the point mass at the empty word.
example : (uniformList 0).map (fun seed =>
    decode (fun _ => 1) 0 [] (binaryValue seed)) = PMF.pure [] := by
  simp [decode]

-- A right-only tree consumes no randomness and skips an empty left child.
private def rightMass : List Bool → ℕ
  | [] => 1
  | [true] => 1
  | _ => 0

private theorem rightMass_add (pre : List Bool) (h : pre.length < 1) :
    rightMass pre = rightMass (pre ++ [false]) + rightMass (pre ++ [true]) := by
  have : pre = [] := List.length_eq_zero_iff.mp (by omega)
  subst pre
  decide

example : (uniformList 0).map (fun seed =>
    decode rightMass 1 [] (binaryValue seed)) = PMF.pure [true] := by
  simp [decode, rightMass, binaryValue]

example : ((uniformList 0).map (fun seed =>
    decode rightMass 1 [] (binaryValue seed))) [true] = 1 := by
  rw [uniformList_decode_apply rightMass_add 0 (by decide)]
  norm_num [rightMass]

-- The pure cardinality theorem also handles a tree whose total mass is zero.
example : ((Finset.range 0).filter (fun rank =>
    decode (fun _ => 0) 3 [] rank = [true, false, true])).card = 0 := by
  exact card_filter_decode (mass := fun _ => 0) (depth := 3)
    (by simp) 3 [] (by simp) [true, false, true]

end ComplexityTests.RankDecoder
