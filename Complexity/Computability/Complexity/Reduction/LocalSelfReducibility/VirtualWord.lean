/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction.LocalSelfReducibility
public import Complexity.Computability.Machines.ReadMachine.VirtualWord

/-!
# Native access to local self-reduction queries

Definitions 3.1–3.2 of [GlasserNguyenReitwiessnerSelmanWitek2013], expanded ECCC TR13-047,
printed page 6, fix the original prefix before the last $\lceil\log_2 n\rceil$ bits.
`LocalSelfReductionQuery.access_output` connects that exact word reconstruction to an actual
native one-bit accessor. Its state stores the suffix, not the reconstructed query word.
`LocalSelfReductionQuery.access_state_bound` supplies a uniform logarithmic storage bound;
`Turing.VirtualWord.access_inSpace` supplies the native multi-tape resource certificate.

These are access and storage lemmas for the proof of Lemma 3.3, not its transfer conclusion.
The suffix is supplied as already stored data. Producing it, consuming regenerated queries or
answers in a certified evaluator, iterating suffixes and adaptive-to-tt conversion remain open.
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

/-- Data stored for one address of a local query. No reconstructed word is stored. -/
@[expose] def localQueryAccessData (n : ℕ) (suffix : List Bool) (i : ℕ) : VirtualWord.Data :=
  (n - Nat.clog 2 n, suffix, i)

/-- The native accessor emits the exact query bit, including its false out-of-range default. -/
theorem LocalSelfReductionQuery.access_output {x y : List Bool}
    (h : LocalSelfReductionQuery x y) (i : ℕ) :
    (VirtualWord.machine (localQueryAccessData x.length
      (y.drop (x.length - Nat.clog 2 x.length)) i)).output x 1 = [y.getD i false] := by
  rw [VirtualWord.output_one]
  have hr := VirtualWord.answer_eq_getD x (x.length - Nat.clog 2 x.length)
    (y.drop (x.length - Nat.clog 2 x.length)) i (Nat.sub_le _ _)
  unfold VirtualWord.word at hr
  rw [← h.reconstruct] at hr
  exact congrArg (fun b => [b]) hr

/-- The exact reconstructed length is the original encoded length. -/
theorem LocalSelfReductionQuery.access_length {x y : List Bool}
    (h : LocalSelfReductionQuery x y) :
    (VirtualWord.word x (x.length - Nat.clog 2 x.length)
      (y.drop (x.length - Nat.clog 2 x.length))).length = x.length := by
  unfold VirtualWord.word
  rw [← h.reconstruct]
  exact h.1

/-- Both the initial and halted states have logarithmic storage. The prefix is excluded. -/
theorem LocalSelfReductionQuery.access_state_bound {x y : List Bool}
    (h : LocalSelfReductionQuery x y) {i : ℕ} (hi : i ≤ x.length) (halt : Bool) :
    (VirtualWord.encState (localQueryAccessData x.length
      (y.drop (x.length - Nat.clog 2 x.length)) i, halt)).length ≤
      16 * (Nat.log2 x.length + 1) :=
  VirtualWord.length_encState_le_log halt (Nat.sub_le _ _) hi h.suffix_length

/-- Actual native logspace access with a fixed stored suffix, on original words of length `n`.
The suffix length and address bounds are data-size conditions, not machine-certificate premises. -/
theorem localQueryAccess_inLogSpace (n i : ℕ) (suffix : List Bool)
    (hi : i ≤ n) (hs : suffix.length ≤ Nat.clog 2 n) :
    ComputableInLogSpace
      (fun x : {x : List Bool // x.length = n} =>
        VirtualWord.answer (localQueryAccessData n suffix i) (x.val.getD i false))
      ((Function.Embedding.subtype (fun x : List Bool => x.length = n)).trans encBits) encBool :=
  VirtualWord.access_inLogSpace _ _
    (fun x hx => by dsimp only [localQueryAccessData]; omega)
    (fun x hx => by dsimp only [localQueryAccessData]; omega)
    (fun x hx => by dsimp only [localQueryAccessData]; simpa only [hx] using hs)

end Cslib.Complexity
