/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.MPC.IKNP.SelectiveFailure

/-! # IKNP selective-failure attack: checked concrete instances

* Concrete `κ = 2`, `m = 3`, `L = BitString 2` identity hash witnessing single-bit selective
  failure (`≥ 1 / 2` advantage against any ideal simulator).
* Concrete `κ = 2`, `m = 3`, `L = BitString 2` full key-recovery attack witnessing simultaneous
  recovery of both target messages (`≥ 3 / 4` advantage against any ideal simulator). -/

namespace CslibFrontierTests.Crypto.IKNPSelectiveFailure

open Cslib
open Cslib.Crypto
open Cslib.Crypto.Protocols.MPC
open Cslib.Probability

private def idHash2 (m : ℕ) : Fin m → BitString 2 → BitString 2 :=
  fun _ x => x

private def zeroT (m : ℕ) : Fin m → BitString 2 :=
  fun _ _ => false

private theorem idHash2_sep {m : ℕ} (j : Fin m) (k : Fin 2) :
    idHash2 m j (BitString.flipOn {k} (zeroT m j)) ≠ idHash2 m j (zeroT m j) := by
  intro h
  have hk := congrFun h k
  simp [idHash2, zeroT, BitString.flipOn] at hk

private def sampleX : Fin 3 → Bool → BitString 2 :=
  fun j b i => decide (j.val = 0 ∧ b = true ∧ i.val = 0)

/-- At `κ = 2`, `m = 3`, and `L = BitString 2`, the single-bit selective-failure attack achieves
distinguishing advantage at least `1 / 2` against every ideal simulator `S`. -/
theorem selectiveFailureSBit_concrete
    (S : ProbComp ((Fin 3 → Bool) × ((Fin 3 → BitString 2) → ProbComp Bool))) :
    (1 / 2 : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (iknpSelectiveFailureSBitRealGame (idHash2 3) (zeroT 3) 0 0 sampleX))
        (ProbComp.eval (iknpSelectiveFailureSBitIdealGame 2 3 (BitString 2) sampleX 0 S)) : ℝ) :=
  iknpSelectiveFailureSBit_advantage (idHash2 3) (zeroT 3) 0 0 sampleX (idHash2_sep 0 0) S

/-- Concrete check that flipping bit `k` in `zeroT 3` strictly alters row `k` under `idHash2 3`. -/
theorem idHash2_sep_all (k : Fin 2) :
    idHash2 3 k.castSucc (BitString.flipOn {k} (zeroT 3 k.castSucc)) ≠
      idHash2 3 k.castSucc (zeroT 3 k.castSucc) :=
  idHash2_sep k.castSucc k

private def sampleProbe : Fin 2 → Bool → BitString 2 :=
  fun _ _ _ => false

/-- At `κ = 2`, `m = 3`, and `L = BitString 2` (`|L| = 4`), the full `s`-extraction attack recovers
both target messages simultaneously with advantage at least `1 - 1 / 4 = 3 / 4` against every ideal
simulator `S`. -/
theorem fullAttack_concrete
    (S : ProbComp ((Fin 3 → Bool) ×
      ((Fin 3 → BitString 2) → ProbComp (BitString 2 × BitString 2)))) :
    (3 / 4 : ℝ) ≤
      (Game.advantage
        (ProbComp.eval (iknpFullAttackRealGame (idHash2 3) (zeroT 3) sampleProbe))
        (ProbComp.eval (iknpFullAttackIdealGame sampleProbe S)) : ℝ) := by
  have h := iknpFullAttack_malicious_receiver_advantage (idHash2 3) (zeroT 3) sampleProbe
    idHash2_sep_all S
  have hcard : (Fintype.card (BitString 2) : ℝ) = 4 := by norm_num [Fintype.card_fun]
  rw [hcard] at h
  norm_num at h ⊢
  exact h

end CslibFrontierTests.Crypto.IKNPSelectiveFailure
