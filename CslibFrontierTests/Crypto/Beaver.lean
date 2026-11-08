/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Protocols.MPC.Beaver

/-!
# Concrete Tests for Arithmetic Beaver Multiplication and Tampered-Opening Attack

Non-vacuous concrete evaluations and end-to-end protocol instantiations over `ZMod 5` (`p = 5`,
`m = 1`, `m = 2`, and `m = 3`) exercising `CslibFrontier.Crypto.Protocols.MPC.Beaver`:

1. **Beaver multiplication step & protocol privacy (`ZMod 5`, `m = 3` and `m = 1`):** explicit
   3-party triple `(a, b, c)` with `(1 + 2 + 4) * (3 + 1 + 0) ≡ 2 * 4 ≡ 3 (mod 5)`, concrete
   share reconstruction of `x * y = 4 * 3 = 2`, end-to-end execution output sum via
   `sum_output_beaverMulProtocol`, proper-coalition marginal uniformity and privacy instantiation
   on `I = {0, 1} ⊂ Fin 3`, plus the `m = 1` edge case (`I = ∅`).
2. **Additive-error tampered-opening attack illustration (`ZMod 5`, `m = 2`):** exact secret
   extraction for all `x : ZMod 5` on a concrete 2-party triple and `≥ 1 / 2` distinguishing
   advantage against a constant blind guess.
-/

namespace CslibFrontierTests.Crypto.Beaver

open Cslib Cslib.Probability Cslib.ProbComp Cslib.Crypto
open Cslib.Crypto.Protocols.MPC Cslib.Crypto.Protocols.MPC.Beaver
open scoped ENNReal NNReal

/-! ### 1. Concrete 3-party and 1-party Beaver triples & multiplication over `ZMod 5` -/

/-- Explicit valid 3-party Beaver triple over `ZMod 5`:
`a = (1, 2, 4)` (sum `2`), `b = (3, 1, 0)` (sum `4`), `c = (4, 2, 2)` (sum `3 = 2 * 4`). -/
def sampleTriple3 : Fin 3 → TripleShare (ZMod 5) :=
  ![⟨1, 3, 4⟩, ⟨2, 1, 2⟩, ⟨4, 0, 2⟩]

/-- Explicit 3-party input shares over `ZMod 5`:
`x = (2, 1, 1)` (sum `4`) and `y = (0, 2, 1)` (sum `3`), with product `4 * 3 = 2` in `ZMod 5`. -/
def sampleInputs3 : Fin 3 → ZMod 5 × ZMod 5 :=
  ![(2, 0), (1, 2), (1, 1)]

example : (∑ i : Fin 3, (sampleTriple3 i).c) =
    (∑ i : Fin 3, (sampleTriple3 i).a) * (∑ i : Fin 3, (sampleTriple3 i).b) := by
  decide

example : sampleTriple3 ∈
    (ProbComp.eval (beaverTripleFunctionality 5 3 (fun _ => ()))).support := by
  rw [mem_support_beaverTripleFunctionality_iff]
  decide

/-- Proper-coalition marginal uniformity of `beaverTripleFunctionality 5 3` on `I = {0, 1}`. -/
example :
    (ProbComp.eval (beaverTripleFunctionality 5 3 (fun _ => ()))).map
      ({0, 1} : Finset (Fin 3)).restrict =
    PMF.uniformOfFintype ((i : ({0, 1} : Finset (Fin 3))) → TripleShare (ZMod 5)) :=
  eval_restrict_beaverTripleFunctionality {0, 1} (by decide) (fun _ => ())

/-- Edge case `m = 1`, `I = ∅` for `eval_restrict_beaverTripleFunctionality`. -/
example :
    (ProbComp.eval (beaverTripleFunctionality 5 1 (fun _ => ()))).map
      (∅ : Finset (Fin 1)).restrict =
    PMF.uniformOfFintype ((i : (∅ : Finset (Fin 1))) → TripleShare (ZMod 5)) :=
  eval_restrict_beaverTripleFunctionality ∅ (by decide) (fun _ => ())

/-- Concrete Beaver output shares reconstruct `(2 + 1 + 1) * (0 + 2 + 1) = 4 * 3 = 2` in
`ZMod 5`. -/
example :
    let op := ∑ j : Fin 3, localMaskedOpening (sampleInputs3 j) (sampleTriple3 j)
    (∑ i : Fin 3, beaverMulShare i op (sampleTriple3 i)) = (2 : ZMod 5) := by
  decide

/-- End-to-end execution of `beaverMulProtocol 5 3` on `sampleInputs3`: a supported execution
exists and its output shares sum to `2 : ZMod 5` by `sum_output_beaverMulProtocol`. -/
example :
    ∃ res ∈ ((beaverMulProtocol 5 3).evalWith (beaverTripleWorld 5 3) sampleInputs3).support,
      (∑ i : Fin 3, res.2 i) = (2 : ZMod 5) := by
  obtain ⟨res, hres⟩ :=
    PMF.support_nonempty ((beaverMulProtocol 5 3).evalWith (beaverTripleWorld 5 3) sampleInputs3)
  refine ⟨res, hres, ?_⟩
  rw [sum_output_beaverMulProtocol sampleInputs3 hres]
  decide

/-- Concrete 2-of-3 coalition `{0, 1}` in `beaverMulProtocol 5 3` has identical ideal and real
joint view-and-output distributions on `sampleInputs3`. -/
example :
    let I : Finset (Fin 3) := {0, 1}
    ProbComp.eval (idealJoint (sharedMulFunctionality 3) I
      (beaverMulSim 5 3 I) sampleInputs3) =
    (beaverMulProtocol 5 3).realJoint (beaverTripleWorld 5 3) I sampleInputs3 :=
  perfectSemiHonestPrivateProper_beaverMul 5 3 {0, 1} (by decide) sampleInputs3

/-- Edge case `m = 1`, `I = ∅` for `perfectSemiHonestPrivateProper_beaverMul`. -/
example :
    let I : Finset (Fin 1) := ∅
    let xy : Fin 1 → ZMod 5 × ZMod 5 := ![(3, 4)]
    ProbComp.eval (idealJoint (sharedMulFunctionality 1) I
      (beaverMulSim 5 1 I) xy) =
    (beaverMulProtocol 5 1).realJoint (beaverTripleWorld 5 1) I xy :=
  perfectSemiHonestPrivateProper_beaverMul 5 1 ∅ (by decide) ![(3, 4)]

/-! ### 2. Concrete tampered-opening attack illustration over `ZMod 5` -/

/-- Valid 2-party Beaver triple over `ZMod 5`: `a = (2, 4)` (sum `1`), `b = (3, 3)` (sum `1`),
`c = (4, 2)` (sum `1 = 1 * 1`), on which `tamperedOpeningExtract` recovers every secret `x`. -/
def sampleTriple2 : Fin 2 → TripleShare (ZMod 5) :=
  ![⟨2, 3, 4⟩, ⟨4, 3, 2⟩]

example : ∀ x : ZMod 5,
    let op₀ := localMaskedOpening (x, 0) (sampleTriple2 0)
    let z'₀ := beaverMulShare (m := 2) 0 (op₀ + tamperedOpening (sampleTriple2 1)) (sampleTriple2 0)
    tamperedOpeningExtract (sampleTriple2 1) op₀ z'₀ = x := by
  decide

example (x : ZMod 5) :
    ProbComp.eval (tamperedOpeningReal 5 x) = PMF.pure x :=
  eval_tamperedOpeningReal 5 x

example :
    (1 : ℝ≥0) ≤
      Game.advantage (tamperedOpeningTestOne 5 (tamperedOpeningReal 5 0))
        (tamperedOpeningTestOne 5 (pure (0 : ZMod 5))) +
      Game.advantage (tamperedOpeningTestOne 5 (tamperedOpeningReal 5 1))
        (tamperedOpeningTestOne 5 (pure (0 : ZMod 5))) :=
  one_le_add_advantage_tamperedOpening (by decide) (pure 0)

/-- Against the constant-`0` blind guess `pure 0`, the tampered-opening hidden-bit game over
`ZMod 5` achieves distinguishing advantage at least `1 / 2`. -/
example :
    (1 / 2 : ℝ≥0) ≤
      Game.advantage (tamperedOpeningRealBitGame 5)
        (tamperedOpeningIdealBitGame 5 (pure (0 : ZMod 5))) :=
  le_advantage_tamperedOpeningBitGame (by decide) (pure 0)

end CslibFrontierTests.Crypto.Beaver
