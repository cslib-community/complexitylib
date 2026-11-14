/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveDepthPrepare.Embedded

/-! A real depth-preparation run uses a larger scratch prefix beside occupied protected and
trailing tapes. The count three has depth two in both representations. -/

noncomputable section

namespace CslibFrontierTests.CarrySaveDepthPrepareEmbedded

open Turing Turing.MultiTapeTM Turing.MultiTapeATM.CarrySaveDepthPrepare

private def words (scratch : ℕ) (i : Fin (scratch + 16 + 2)) : List Bool :=
  if i.val = scratch + 7 then encNat 3
  else if i.val = scratch + 6 then [true, false, true]
  else if i.val = scratch + 15 then [false, true]
  else if i.val = scratch + 16 then [true, true, false]
  else if i.val = scratch + 17 then [false]
  else []

example :
    ∃ (k : ℕ) (S : Type) (_ : Finite S)
      (tm : MultiTapeTM ((k + 2) + 16 + 2) Bool S) (c d : ℕ),
      let start : Cfg ((k + 2) + 16 + 2) Bool Unit [true] :=
        { tapesCfg [true] (words (k + 2)) 0 0 [false, true] with inputPos := 0 }
      let result := tm.runFrom (start.withState (some tm.q₀)) (c * 3 ^ d)
      result.state = none ∧ result.inputPos = 0 ∧ result.output = [false, true] ∧
        result.workTapes (Embedded.coreTapes (k + 2) 16 (by decide) 0) = tapeOfList (encNat 2) ∧
        result.workTapes (Embedded.coreTapes (k + 2) 16 (by decide) 4) = tapeOfList [true, true] ∧
        result.workTapes (Embedded.coreTapes (k + 2) 16 (by decide) 7) = tapeOfList (encNat 3) ∧
        result.workTapes (Embedded.coreTapes (k + 2) 16 (by decide) 6) =
          tapeOfList [true, false, true] ∧
        result.workTapes ⟨k + 2 + 15, by omega⟩ = tapeOfList [false, true] ∧
        result.workTapes ⟨k + 2 + 16, by omega⟩ = tapeOfList [true, true, false] ∧
        result.workTapes ⟨k + 2 + 17, by omega⟩ = tapeOfList [false] ∧
        (∀ i, i.val < k + 2 → result.workTapes i = tapeOfList []) ∧
        result.workTapePos = 0 := by
  obtain ⟨k, S, hS, tm, c, d, h⟩ := Embedded.exists_prepare
  refine ⟨k, S, hS, tm.extendTapes (Embedded.embedding k (k + 2) 16 (by omega) (by decide)),
    c, d, ?_⟩
  have hr := h (k + 2) 16 (by omega) (by decide) [true] 3 (words (k + 2)) [false, true]
    (by simp [words]) (by simp [words]) (by simp [words])
    (by
      intro i hi
      simp only [words]
      split_ifs <;> first | rfl | omega)
  dsimp only
  have hclock : (encNat 3).length + 1 = 3 := by decide
  rw [hclock] at hr
  rw [hr.1]
  have hdepth : Nat.clog 2 3 = 2 := by decide
  simp only [hdepth, Cfg.withState, tapesCfg]
  refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals try { solve | simp [Function.update_apply, words, Fin.ext_iff] }
  intro i hi
  funext z
  simp only [Pi.zero_apply, sub_zero]
  congr 1
  simp only [Function.update_apply, words, Fin.ext_iff, Embedded.coreTapes_val]
  split_ifs <;> first | rfl | omega

end CslibFrontierTests.CarrySaveDepthPrepareEmbedded
