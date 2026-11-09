/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.LocalSelfReducibility.VirtualWord
public import CslibFrontier.Computability.Machines.ReadMachine.VirtualWord.Runtime

/-!
# Runtime access to reconstructed local queries

The fixed runtime machine loads the prefix cut, suffix and address from its input header.
`LocalSelfReductionQuery.runtime_output` identifies its actual output with a bit of the exact
reconstructed query. `runtime_admissible` permits use of the single native compiler certificate
`Turing.VirtualWord.Runtime.access_inOriginalLogSpace`; no query word is stored.

This consumes the reconstruction from Definitions 3.1–3.2 of
[GlasserNguyenReitwiessnerSelmanWitek2013], expanded ECCC TR13-047, printed page 6.
It does not supply evaluator/answer regeneration or the transfer of Lemma 3.3.
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

/-- The variable local-query data fit the runtime compiler's original-length domain. -/
theorem LocalSelfReductionQuery.runtime_admissible {x y : List Bool}
    (h : LocalSelfReductionQuery x y) {i : ℕ} (hi : i ≤ x.length) :
    VirtualWord.Runtime.Admissible
      (localQueryAccessData x.length (y.drop (x.length - Nat.clog 2 x.length)) i, x) :=
  ⟨Nat.sub_le _ _, hi, h.suffix_length⟩

/-- The one fixed runtime machine emits the exact reconstructed query bit at every address.
The address may be out of range; only the logarithmic specialization needs a size bound. -/
theorem LocalSelfReductionQuery.runtime_output {x y : List Bool}
    (h : LocalSelfReductionQuery x y) (i : ℕ) :
    let d := localQueryAccessData x.length (y.drop (x.length - Nat.clog 2 x.length)) i
    VirtualWord.Runtime.machine.output (VirtualWord.Runtime.encInput (d, x))
      (2 * (VirtualWord.encData d).length + 2) = [y.getD i false] := by
  dsimp only [localQueryAccessData]
  rw [VirtualWord.Runtime.output_word (x.length - Nat.clog 2 x.length) i
    (y.drop (x.length - Nat.clog 2 x.length)) x (Nat.sub_le _ _)]
  unfold VirtualWord.word
  rw [← h.reconstruct]

end Cslib.Complexity
