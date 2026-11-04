/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.IterativeCorrect
public import Complexity.Computability.TreeEval.Ary.Packed.Executable

/-!
# Iterative packed Cook–Mertz with counter-based gate updates

Instantiate the existing control loop with the counter implementation of finite-grid
interpolation. The resulting loop adds the encoded tree value to its target and restores the
other registers, from arbitrary initial contents. It uses the existing tree model and packed
encoding contract, with the strict finite-field degree threshold.

## Main results

* `Cslib.TreeEval.Ary.Iter.exists_runFrom_counter_root`: the packed controller computes the
  encoded root value using counter-based gate updates.

This is pure iterative correctness. Native lookup, original-input subroutine composition and
the complete machine-space certificate are not supplied by this result.
-/

public section

namespace Cslib.TreeEval.Ary.Iter

open Packed

/-- A packed root call using the counter-based gate extension adds the encoded root value and
preserves every other global register. The encoding has a left inverse. -/
theorem exists_runFrom_counter_root {p s d b r : ℕ} [Fact p.Prime]
    (hd : 0 < d) (hs : 0 < s) (hsp : s ≤ p)
    (h : Fin s ↪ ZMod p) (hh : ∀ a, h a = (a.val : ZMod p))
    (encode : (Fin b → Bool) → Fin r → Fin s)
    (decode : (Fin r → Fin s) → Fin b → Bool) (hdecode : Function.LeftInverse decode encode)
    (hD : d * r * (s - 1) < p - 1)
    {us : List (ZMod p)ˣ} (hnd : us.Nodup) (hmem : ∀ u, u ∈ us)
    {height : ℕ} (T : Tree d b height) (S : Ary.State (ZMod p) d r)
    (c : ZMod p) (t : Fin (d + 1)) :
    ∃ N, runFrom hd (fun v i => h (encode v i)) (counterGateExtension hs encode decode)
      us T.nodeAt (initialCfg S c t) N =
        ⟨Function.update S t (S t + c • fun i => h (encode T.eval i)), [], .ret⟩ := by
  obtain ⟨N, hN⟩ := exists_runFrom_root hd (fun v i => h (encode v i))
    (counterGateExtension hs encode decode) us T S c t
  refine ⟨N, ?_⟩
  rw [hN]
  have hE : counterGateExtension (p := p) (d := d) hs encode decode =
      gateExtension h encode decode := by
    funext f x i
    exact counterGateExtension_eq hs hsp h hh encode decode f x i
  rw [hE, procWith_gateExtension_eq h encode decode hdecode
    (by simpa only [Fintype.card_fin, ZMod.card] using hD) hnd hmem]

end Cslib.TreeEval.Ary.Iter
