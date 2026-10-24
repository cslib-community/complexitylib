/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BPP.Derandomization
import Complexity.Computability.Complexity.Classes.BPP.Derandomization.Generator
import Complexity.Computability.Circuit.Boolean.Hierarchy

/-! Derandomizing `BPP` with the Nisan–Wigderson generator: average-case hardness on concrete
functions, both satisfied and violated; greedy designs, their size bound and their generator on
concrete masks; the decider on a verifier that ignores its random string; and named axiom guards
for the headline theorems. -/

namespace ComplexityTests.Derandomization

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.PRG.NisanWigderson Finset

/-! ### Average-case hardness -/

/-- Against circuits without gates, which compute coordinate projections, parity on two bits is
average-case hard with the bound `1 / 2 + 1 / 0 = 1 / 2`: each projection agrees with parity on
exactly half of the inputs. -/
example : IsAverageCaseHard (parity 2) 0 := by
  intro g hg
  have hproj : ∃ i, g = fun x => x i := by
    by_contra! h
    exact absurd (one_le_complexity_single (I := interpretation) h) (by omega)
  obtain ⟨i, rfl⟩ := hproj
  have hcount : ∀ i : Fin 2, #{x : BitString 2 | x i = parity 2 x} = 2 := by decide
  rw [hcount i]
  norm_num

/-- No function on `n` bits is average-case hard for size `2 ^ n (2 n + 3) + 1`: it is computed
within that size, and agrees with itself everywhere. So the hypothesis is not trivially true. -/
example {n : ℕ} (f : BooleanFunction n) :
    ¬ IsAverageCaseHard f (2 ^ n * (2 * n + 3) + 1) := by
  intro hf
  have hc : complexity interpretation (single f) ≤ 2 ^ n * (2 * n + 3) + 1 := by
    simpa using complexity_le_of_dependsOn (s := univ) (f := f) fun _ _ _ => by
      congr 1
      funext i
      simp_all
  have h := hf f hc
  have hs : (3 : ℝ) ≤ (2 ^ n * (2 * n + 3) + 1 : ℕ) := by
    have : 3 ≤ 2 ^ n * (2 * n + 3) + 1 := by
      have := Nat.one_le_two_pow (n := n)
      nlinarith
    exact_mod_cast this
  rw [filter_true_of_mem fun _ _ => rfl, card_univ, BitString.card, Nat.cast_pow,
    Nat.cast_ofNat, div_self (by positivity)] at h
  have : 1 / ((2 ^ n * (2 * n + 3) + 1 : ℕ) : ℝ) ≤ 1 / 3 := by
    gcongr
  linarith

/-- Hardness for a size gives hardness for every smaller positive size. -/
example {n s : ℕ} {f : BooleanFunction n} (hf : IsAverageCaseHard f (2 * s + 1)) :
    IsAverageCaseHard f (s + 1) :=
  hf.mono (by omega) (by omega)

/-! ### Greedy designs -/

/-- The greedy design on four positions with blocks of two positions and no shared position. -/
example : greedyMasks 4 2 0 = [[true, true, false, false], [false, false, true, true]] := by
  decide

/-- With one shared position allowed, all six pairs of four positions are kept. -/
example : (greedyMasks 4 2 1).length = 6 := by decide

/-- The size bound: on seeds of `(16 + 1) * 1` bits, with blocks of one position, the greedy
design has at least `4` blocks, since `4 ^ 1 * 4 ≤ 16 ^ 1`. -/
example : 4 ≤ (greedyMasks ((16 + 1) * 1) 1 (1 - 1)).length :=
  le_length_greedyMasks (by norm_num) le_rfl (by norm_num) (by norm_num)

/-- The counting bound on a concrete design: `C(6, 2) ≤ 4 · C(3, 2) ^ 2`. -/
example : (6 : ℕ).choose (1 + 1) ≤ (greedyMasks 6 3 1).length * (3 : ℕ).choose (1 + 1) ^ 2 :=
  choose_le_length_greedyMasks_mul (by norm_num) (by norm_num)

example : (greedyMasks 6 3 1).length = 4 := by decide

/-- Reading the bits of a seed at the ones of a mask, in increasing order of position. -/
example : restrictMask [true, false, true, true] [false, true, true, false] =
    [false, true, false] := by
  decide

/-- The generator on lists with the greedy design on four positions and the conjunction of two
bits: the output bits are the conjunctions of the first and of the last two seed bits. -/
example : listGenerator (fun y => y.all id) 2 (greedyMasks 4 2 0) [true, true, false, true] =
    [true, false] := by
  decide

/-- The generator on lists is the Nisan–Wigderson generator of `Design.greedy`. -/
example (z : Fin 4 → Bool) :
    listGenerator (fun y => y.all id) 2 ((greedyMasks 4 2 0).take 2) (List.ofFn z) =
      List.ofFn (generator (Design.greedy 4 2 0 2 (by decide))
        (fun x => (List.ofFn x).all id) z) :=
  listGenerator_take_greedyMasks _ _ z

/-! ### The decider -/

/-- On a verifier that ignores its random string, the decider returns the verifier's answer,
here on a constant verifier with seeds of two bits. -/
example : Complexity.nwDecider (fun _ : Unit × List Bool => true) (fun _ => false)
    (fun _ => 2) (fun _ => 1) (fun _ => 0) (fun _ => 2) () = true := by
  decide

example : Complexity.nwDecider (fun _ : Unit × List Bool => false) (fun _ => false)
    (fun _ => 2) (fun _ => 1) (fun _ => 0) (fun _ => 2) () = false := by
  decide

/-! ### Axioms -/

/--
info: 'Cslib.Complexity.BPP_subset_P_of_isAverageCaseHard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.BPP_subset_P_of_isAverageCaseHard

/--
info: 'Cslib.Complexity.P_eq_BPP_of_isAverageCaseHard' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.P_eq_BPP_of_isAverageCaseHard

/--
info: 'Cslib.Complexity.computableInPolyTime_nwDecider' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.computableInPolyTime_nwDecider

/--
info: 'Cslib.Complexity.exists_computableInO_of_mem_DTIME' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.exists_computableInO_of_mem_DTIME

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.abs_card_div_sub_card_div_lt' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.abs_card_div_sub_card_div_lt

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.choose_le_length_greedyMasks_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.choose_le_length_greedyMasks_mul

/--
info: 'Cslib.Crypto.PRG.NisanWigderson.computableInPolyTime_greedyMasks' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Crypto.PRG.NisanWigderson.computableInPolyTime_greedyMasks

/--
info: 'Cslib.Circuits.Boolean.isAverageCaseHard_xorPower' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Boolean.isAverageCaseHard_xorPower

end ComplexityTests.Derandomization
