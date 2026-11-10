/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.LocalSelfReducibility.RuntimeAccess
public import CslibFrontier.Computability.Machines.ReadMachine.VirtualWord.Evaluator

/-!
# A native evaluator consuming a reconstructed local query

The supplied runtime header describes the original prefix and the local query's stored suffix.
The consumer scans the exact query twice and retains one Boolean evaluator state across reads.
`runtime_evaluate` identifies actual machine output with a finite-state fold over those reads.
No reconstructed word is stored. The uniform native certificate is
`Turing.VirtualWord.Evaluator.evaluate_inOriginalLogSpace`, with size admissibility supplied by
`runtime_admissible`. Header generation from an arbitrary native query generator is still open.

This is a restricted original implementation supporting Definitions 3.1–3.2 and the proof of
Lemma 3.3 of [GlasserNguyenReitwiessnerSelmanWitek2013], expanded ECCC TR13-047, printed page 6.
It does not certify arbitrary logspace evaluators, answer regeneration, suffix iteration or the
adaptive-to-tt step, and does not prove Lemma 3.3.
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

/-- An actual two-pass native consumer of the reconstructed query, rather than a single read.
The right-hand list is only an output specification, not allocated workspace. -/
theorem LocalSelfReductionQuery.runtime_evaluate {x y : List Bool}
    (h : LocalSelfReductionQuery x y) (δ : Bool × Bool → Bool) :
    let d := localQueryAccessData x.length (y.drop (x.length - Nat.clog 2 x.length)) 0
    VirtualWord.Evaluator.machine δ |>.output (VirtualWord.Runtime.encInput (d, x))
      (2 * (VirtualWord.encData d).length + 2 + 2 * VirtualWord.Evaluator.width d) =
        [(y ++ y).foldl (fun a b => δ (a, b)) false] := by
  dsimp only
  rw [VirtualWord.Evaluator.output]
  dsimp only [localQueryAccessData]
  rw [VirtualWord.Evaluator.evaluate_word δ _ _ _ (Nat.sub_le _ _)]
  have hw : VirtualWord.word x (x.length - Nat.clog 2 x.length)
      (y.drop (x.length - Nat.clog 2 x.length)) = y := h.reconstruct.symm
  rw [hw]

end Cslib.Complexity
