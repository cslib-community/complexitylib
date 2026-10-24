/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Hierarchy.Space
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

/-! The universal machine within a space budget: no step beyond the budget, and the answer of a
concrete machine within an ample budget. The diagonal within space on the padded descriptions of
concrete accepting and rejecting machines; the space hierarchy theorem and its corollaries
on concrete bounds;
and axiom guards for the headline results. -/

namespace ComplexityTests.SpaceHierarchy

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Filter

/-! ### The budget -/

/-- Within the budget `0` no step is taken, since every configuration is encoded by at least one
bit: the simulation stays at the initial configuration, which has not halted. -/
example (d : Desc) (x : List ℕ) (t : ℕ) : budgetedUniversal (d, x, t, 0) = ([], false) := by
  have h (i : ℕ) : (budgetStep d x 0)^[i] (init d, []) = (init d, []) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, budgetStep]
      split_ifs with hb
      · rw [eCfg_apply, length_encPair] at hb
        omega
      · rfl
  simp only [budgetedUniversal, h]
  rfl

/-- Halt at once with output `[b]`. -/
private def answer (b : Bool) : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := some b, state := none }

/-- After its first step, the answering machine has halted with output `[b]`. -/
private theorem runFrom_answer (b : Bool) (x : List Bool) {t : ℕ} (ht : 1 ≤ t) :
    ((answer b).runFrom ((answer b).initCfg x) t).Halted ∧
      ((answer b).runFrom ((answer b).initCfg x) t).output = [b] := by
  have h1 : ((answer b).runFrom ((answer b).initCfg x) 1).state = none ∧
      ((answer b).runFrom ((answer b).initCfg x) 1).output = [b] := by
    change ((answer b).step _).state = none ∧ ((answer b).step _).output = [b]
    rw [MultiTapeTM.step_of_state (q := ()) rfl]
    simp [answer, Action.apply]
  rw [MultiTapeTM.runFrom_eq_of_halt _ _ ht h1.1]
  exact h1

/-- The numbering of the single state. -/
private def unitNum : Unit ↪ ℕ := ⟨fun _ => 0, fun _ _ _ => rfl⟩

/-- Within the budget of its simulated configurations, the budgeted universal function returns the
answer of the answering machine and that it has halted. -/
example (b : Bool) (x : List Bool) :
    budgetedUniversal (desc unitNum eBit (answer b), x.map eBit, 1,
      cfgSpace (desc unitNum eBit (answer b)) (x.map eBit) 1) = ([eBit b], true) := by
  rw [budgetedUniversal_desc unitNum eBit (answer b) x 1 _ le_rfl]
  obtain ⟨h₁, h₂⟩ := runFrom_answer b x le_rfl
  simp only [Cfg.Halted] at h₁
  rw [h₁, h₂]
  rfl

/-! ### The diagonal within space on concrete machines -/

/-- On the padded description of a machine answering `b`, the diagonal within space
`(n + 1) ^ 2` answers `!b`, so its problem is neither empty nor everything. -/
example (b : Bool) (pad : List Bool)
    (hpad : 2 ^ (eDesc (desc unitNum eBit (answer b))).length ≤ pad.length) :
    spaceDiagonal (fun n => (n + 1) ^ 2) (frame (eDesc (desc unitNum eBit (answer b))) ++ pad) =
      !b := by
  have hD : 2 ≤ (eDesc (desc unitNum eBit (answer b))).length := by
    simp only [eDesc_apply, length_encPair]
    omega
  have hlen : (frame (eDesc (desc unitNum eBit (answer b))) ++ pad).length =
      2 * (eDesc (desc unitNum eBit (answer b))).length + 1 + pad.length := by
    rw [List.length_append, length_frame]
  have hpow := Nat.lt_two_pow_self (n := (eDesc (desc unitNum eBit (answer b))).length)
  obtain ⟨hhalt, hout⟩ := runFrom_answer b (frame (eDesc (desc unitNum eBit (answer b))) ++ pad)
    (t := 2 ^ ((frame (eDesc (desc unitNum eBit (answer b))) ++ pad).length + 1) ^ 2)
    Nat.one_le_two_pow
  refine spaceDiagonal_desc unitNum (answer b) pad _ ?_ ?_ hhalt hout
  · rw [Diagonal.shortDesc, unframe_frame_append, hlen]
    exact decide_eq_true (by omega)
  · have hn := length_encNat_le ((List.map eBit (frame (eDesc (desc unitNum eBit
      (answer b))) ++ pad)).length + 1)
    simp only [cfgSpace, simSpace, List.length_map, hlen] at hn ⊢
    change _ + 3 * (2 * (eDesc (desc unitNum eBit (answer b))).length + 5) * 2 *
      ∑ i ∈ Finset.range 0, _ + 0 ≤ _
    simp only [Finset.range_zero, Finset.sum_empty]
    nlinarith

/-! ### The space hierarchy theorem on concrete bounds -/

/-- The diagonal within space `(n + 1) ^ 2` is in `DSPACE ((n + 1) ^ 2)` and not in
`DSPACE n`. -/
example : {x | spaceDiagonal (fun n => (n + 1) ^ 2) x = true} ∈
    DSPACE encBits (fun n => (n + 1) ^ 2) \ DSPACE encBits fun n => n := by
  have hn (n : ℕ) : n ≤ (n + 1) ^ 2 := (Nat.le_succ n).trans (Nat.le_self_pow (by norm_num) _)
  refine ⟨setOf_spaceDiagonal_mem_DSPACE (spaceConstructible_succ_pow 2) hn,
    setOf_spaceDiagonal_notMem_DSPACE hn fun c => ?_⟩
  filter_upwards [eventually_ge_atTop c] with n hc
  nlinarith

/-- Linear space is strictly within space `(n + 1) ^ 2`. -/
example : DSPACE encBits (fun n => n) ⊂ DSPACE encBits fun n => (n + 1) ^ 2 :=
  DSPACE_ssubset_DSPACE (spaceConstructible_succ_pow 2)
    (fun n => (Nat.le_succ n).trans (Nat.le_self_pow (by norm_num) _)) fun c => by
      filter_upwards [eventually_ge_atTop c] with n hc
      nlinarith

/-- The hierarchy does not depend on additive constants: space `n + 1` is strictly within space
`(n + 1) ^ 2`. -/
example : DSPACE encBits (fun n => n + 1) ⊂ DSPACE encBits fun n => (n + 1) ^ 2 :=
  DSPACE_ssubset_DSPACE (spaceConstructible_succ_pow 2)
    (fun n => (Nat.le_succ n).trans (Nat.le_self_pow (by norm_num) _)) fun c => by
      filter_upwards [eventually_ge_atTop c] with n hc
      nlinarith

/-- Constant space is strictly within linear space. -/
example : DSPACE encBits (· ^ 0) ⊂ DSPACE encBits (· ^ 1) := DSPACE_pow_ssubset_DSPACE_pow_succ 0

example : DSPACE encBits (· ^ 2) ⊂ DSPACE encBits (· ^ 3) := DSPACE_pow_ssubset_DSPACE_pow_succ 2

example : L encBits ⊂ PSPACE encBits := L_ssubset_PSPACE

/-! ### Axioms -/

/--
info: 'Turing.MultiTapeTM.Universal.budgetedUniversal_desc' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.budgetedUniversal_desc

/--
info: 'Turing.MultiTapeTM.Universal.computableTidilyInO_budgetedUniversal' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.computableTidilyInO_budgetedUniversal

/--
info: 'Turing.MultiTapeTM.Universal.budgetSpace_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.Universal.budgetSpace_le

/--
info: 'Cslib.Complexity.computableInO_spaceDiagonal' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.computableInO_spaceDiagonal

/--
info: 'Cslib.Complexity.setOf_spaceDiagonal_notMem_DSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.setOf_spaceDiagonal_notMem_DSPACE

/--
info: 'Cslib.Complexity.DSPACE_ssubset_DSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.DSPACE_ssubset_DSPACE

/--
info: 'Cslib.Complexity.DSPACE_pow_ssubset_DSPACE_pow_succ' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.DSPACE_pow_ssubset_DSPACE_pow_succ

/--
info: 'Cslib.Complexity.L_ssubset_PSPACE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.L_ssubset_PSPACE

end ComplexityTests.SpaceHierarchy
