/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.NaorYung

/-!
# Tests for Naor–Yung universal one-way hash functions

Provides concrete execution and collision-characterization checks for `naorYungPivot`,
`naorYungCanon`, `naorYungShrink`, `naorYungStep`, `naorYungCompression`, and `naorYungHash`,
exercises deterministic step-collision extraction (`exists_naorYungCascadeInput_collision`) and
plain `ComputableInPolyTime` / `IsPPTOn` certificates, and proves that `naorYungStep id` is not
target collision-resistant via an explicit two-stage strict PPT adversary achieving success
probability at least `1 / 2` at every parameter `n` (confirming that the `OneWayPermutation`
hypothesis is essential).
-/

namespace ComplexityTests.Crypto.NaorYung

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

-- Concrete pivot, canonical representative, and 1-bit quotient evaluation:
example : naorYungPivot 4 [false, true, false, true] = 1 := rfl

example : naorYungPivot 4 [false, false, false, false] = 0 := rfl

example :
    naorYungShrink 4 [false, true, false, true] [true, false, true, false] =
      naorYungShrink 4 [false, true, false, true] [true, true, true, true] := rfl

example :
    ([true, true, true, true] : List Bool) =
      BitString.listXor 4 [[true, false, true, false], [false, true, false, true]] :=
  naorYungShrink_collision_eq_listXor (m := 4)
    (δ := [false, true, false, true])
    (y₀ := [true, false, true, false])
    (y₁ := [true, true, true, true])
    ⟨1, by decide, rfl⟩ rfl rfl (by decide) rfl

/-- Concrete `KeyedCompressionFamily` instantiated from `naorYungCompression` on `f = id`. -/
def idNaorYungCompression : KeyedCompressionFamily :=
  naorYungCompression ComputableInPolyTime.id'

/-- Concrete `KeyedHashFamily` instantiated from `naorYungHash` on `f = id`. -/
def idNaorYungHash : KeyedHashFamily :=
  naorYungHash ComputableInPolyTime.id'

example (n : ℕ) (K msg : List Bool) (hK : K.length = (n + 1) * ((n + 1) * (n + 2))) :
    (idNaorYungHash.eval n K msg).length = n + 1 :=
  idNaorYungHash.length_eq n K msg hK

-- Concrete 2-step compression collision at `n = 1` (`blockLen 1 = 2`, `2 * blockLen 1 = 4`,
-- `keyLen 1 = 6` with `δ₀ = [true, false, true]` and `δ₁ = [false, true, false]`):
-- `x₀ = [false, false, false, false]` has step-0 input `[false, false, false]`, while
-- `x₁ = [true, false, true, false]` has step-0 input `[true, false, true] = w₀ ⊕ δ₀` and the
-- same remaining tail bit `false`, so both compress to the same 2-bit output.
example :
    naorYungCompressionEval id 1 [true, false, true, false, true, false]
        [false, false, false, false] =
      naorYungCompressionEval id 1 [true, false, true, false, true, false]
        [true, false, true, false] := rfl

example :
    ∃ i < 2,
      let K := [true, false, true, false, true, false]
      let w₀ := naorYungCascadeInput id 1 i K [false, false, false, false]
      let w₁ := naorYungCascadeInput id 1 i K [true, false, true, false]
      w₀ ≠ w₁ ∧
        naorYungStep id 1 (BitString.listRow 3 i K) w₀ =
          naorYungStep id 1 (BitString.listRow 3 i K) w₁ :=
  exists_naorYungCascadeInput_collision (f := id) (n := 1)
    (K := [true, false, true, false, true, false])
    (x₀ := [false, false, false, false]) (x₁ := [true, false, true, false])
    rfl rfl (by decide) rfl

/-- Explicit two-stage strict PPT adversary breaking `naorYungStep id`: Stage 1 commits to
`0^{n+2}` and Stage 2 outputs the sampled key `δ` itself (`= 0^{n+2} ⊕ δ`). -/
def idStepBreakAdversary : TargetCollisionFinder where
  choose n := pure (List.replicate (n + 2) false, [])
  find _ _ δ := pure δ

theorem isPPT_idStepBreakAdversary : idStepBreakAdversary.IsPPT where
  choose := by
    dsimp only [idStepBreakAdversary]
    ppt
  find := by
    dsimp only [idStepBreakAdversary]
    ppt

-- Plain `IsPPT` / `IsPPTOn` certificates for `naorYungStepInverter` and `naorYungCascadeAdversary`:
example : IsPPT encBits (naorYungStepInverter id idStepBreakAdversary) :=
  isPPT_naorYungStepInverter ComputableInPolyTime.id' isPPT_idStepBreakAdversary

example : (naorYungCascadeAdversary id idStepBreakAdversary).IsPPT :=
  isPPT_naorYungCascadeAdversary ComputableInPolyTime.id' isPPT_idStepBreakAdversary

/-- When `f = id` (which is invertible in polynomial time and therefore not one-way),
`naorYungStep id` is not target collision-resistant: `idStepBreakAdversary` succeeds whenever the
first bit of `δ` is `true`, which occurs with probability `1 / 2` at every parameter `n`. -/
theorem not_targetCollisionResistantOn_naorYungStep_id :
    ¬ TargetCollisionResistantOn (fun n => n + 2) (naorYungStep id)
      (fun n w => w.length == n + 2) := by
  have hc : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  refine not_targetCollisionResistantOn_of_le_succProbability hc
    idStepBreakAdversary isPPT_idStepBreakAdversary fun n => ?_
  have hcol_true : ∀ tail : List Bool, tail.length = n + 1 →
      isCollision (naorYungStep id n) (fun m w => w.length == m + 2) n
        (true :: tail) (List.replicate (n + 2) false) (true :: tail) = true := by
    intro tail htail
    have hδ_len : (true :: tail).length = n + 2 := by simp [htail]
    have hne : List.replicate (n + 2) false ≠ true :: tail := by
      intro heq
      rw [List.replicate_succ] at heq
      injection heq with hhead
      exact Bool.noConfusion hhead
    have hpivot : naorYungPivot (n + 2) (true :: tail) = 0 := by
      simp [naorYungPivot, List.range_succ_eq_map]
    have hrow_z :
        BitString.listRow (n + 2) 0 (List.replicate (n + 2) false) =
          List.replicate (n + 2) false := by
      rw [BitString.listRow_zero, BitString.ofFn_ofList List.length_replicate]
    have hrow_d : BitString.listRow (n + 2) 0 (true :: tail) = true :: tail := by
      rw [BitString.listRow_zero, BitString.ofFn_ofList hδ_len]
    have hxor_self :
        BitString.listXor (n + 2) [true :: tail, true :: tail] =
          List.replicate (n + 2) false := by
      rw [BitString.listXor_pair]
      have hsum : BitString.ofList (n + 2) (true :: tail) +
          BitString.ofList (n + 2) (true :: tail) = 0 :=
        funext fun _ => Bool.xor_self _
      rw [hsum]
      change List.ofFn (fun _ : Fin (n + 2) => false) = _
      simp only [List.ofFn_const]
    have hget_z : (List.replicate (n + 2) false).getD 0 false = false := by
      rw [List.replicate_succ]
      rfl
    have hcanon :
        naorYungCanon (n + 2) (true :: tail) (List.replicate (n + 2) false) =
          naorYungCanon (n + 2) (true :: tail) (true :: tail) := by
      unfold naorYungCanon
      rw [hrow_z, hrow_d]
      simp only [hpivot, hget_z, List.getD_cons_zero, Bool.false_eq_true, ↓reduceIte, hxor_self]
    rw [isCollision_eq_true_iff]
    refine ⟨by simp, by simp [htail], hne, ?_⟩
    simp only [naorYungStep, id_eq, hrow_z, hrow_d, naorYungShrink, hcanon]
  have heval_ge :
      (1 / 2 : ENNReal) ≤
        (ProbComp.eval
          (targetCollisionGame (fun m => m + 2) (naorYungStep id)
            (fun m w => w.length == m + 2) idStepBreakAdversary n)) true := by
    simp only [targetCollisionGame, idStepBreakAdversary, pure_bind, ProbComp.eval_bind,
      BitString.eval_sampleList, ProbComp.eval_pure]
    rw [BitString.uniformList_succ]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.bind_apply]
    have hle_sum :
        PMF.uniformOfFintype Bool true *
          ((BitString.uniformList (n + 1)).bind fun tail =>
            PMF.pure
              (isCollision (naorYungStep id n) (fun m w => w.length == m + 2) n
                (true :: tail) (List.replicate (n + 2) false) (true :: tail))) true ≤
          ∑' b : Bool, PMF.uniformOfFintype Bool b *
            ((BitString.uniformList (n + 1)).bind fun tail =>
              PMF.pure
                (isCollision (naorYungStep id n) (fun m w => w.length == m + 2) n
                  (b :: tail) (List.replicate (n + 2) false) (b :: tail))) true := by
      rw [tsum_fintype, Fintype.sum_bool]
      exact le_self_add
    have htail_one :
        ((BitString.uniformList (n + 1)).bind fun tail =>
          PMF.pure
            (isCollision (naorYungStep id n) (fun m w => w.length == m + 2) n
              (true :: tail) (List.replicate (n + 2) false) (true :: tail))) true = 1 := by
      have hcongr :
          ((BitString.uniformList (n + 1)).bind fun tail =>
            PMF.pure
              (isCollision (naorYungStep id n) (fun m w => w.length == m + 2) n
                (true :: tail) (List.replicate (n + 2) false) (true :: tail))) =
            PMF.pure true := by
        calc
          _ = (BitString.uniformList (n + 1)).bind (fun _ => PMF.pure true) := by
                apply PMF.bind_congr_on_support
                intro tail htail
                rw [hcol_true tail (BitString.length_of_mem_support_uniformList htail)]
          _ = PMF.pure true := PMF.bind_const _ _
      rw [hcongr, PMF.pure_apply_self]
    have hbool_half : PMF.uniformOfFintype Bool true = (1 / 2 : ENNReal) := by
      simp [PMF.uniformOfFintype_apply]
    calc
      (1 / 2 : ENNReal) = PMF.uniformOfFintype Bool true * 1 := by rw [hbool_half, mul_one]
      _ = _ := by rw [← htail_one]
      _ ≤ _ := hle_sum
  unfold Game.succProbability
  have hhalf_toNNReal : ((1 / 2 : ENNReal).toNNReal) = (1 / 2 : ℝ≥0) := by
    simp [one_div, ENNReal.toNNReal_ofNat]
  rw [← hhalf_toNNReal]
  exact ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) heval_ge

-- Main `OneWayPermutation` endpoints type-check cleanly:
example {f : List Bool → List Bool} (hf : OneWayPermutation f) :
    (naorYungHash hf.oneWay.polyTime).TargetCollisionResistant :=
  hf.targetCollisionResistant_naorYungHash

example {f : List Bool → List Bool} (hf : OneWayPermutation f) :
    ∃ H : KeyedHashFamily, H.TargetCollisionResistant :=
  hf.exists_targetCollisionResistant_keyedHashFamily

end ComplexityTests.Crypto.NaorYung
