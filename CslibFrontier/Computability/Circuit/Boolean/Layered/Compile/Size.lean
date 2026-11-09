/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Layered.Compile.Correctness
public import CslibFrontier.Computability.Circuit.Boolean.Layered.Size

/-!
# Explicit encoded size of compiled Boolean circuits

For a circuit with `n` inputs, `s` stored gates, `m` designated outputs and output depth `d`,
write `W = n + 3 * s` and `B = log₂ W + 1`. The actual compiled schedule and output selectors
have at most

`4 * d * (2 * W * (6 * B + 21) + 1) + m * (2 * B + 1) + 1`

bits. This includes all node tags, binary references, pair framing, layer framing and repeated
selectors. Unused gates contribute to the working width, but only the designated-output depth
controls the number of layers. When `d = 0`, the schedule contributes no nodes or layers.

## Main results

* `Cslib.Circuits.Boolean.Layered.length_encCompiled_compile_le`: the explicit binary size bound.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Layered

open Turing.MultiTapeTM

/-- The full compiled artifact has size linear in the number of emitted nodes and selectors,
times a logarithmic reference bound. All tags and framing are included. -/
theorem length_encCompiled_compile_le {n m : ℕ} (c : Circuit signature n m) :
    let width := n + 3 * c.size
    let bits := Nat.log2 width + 1
    (encCompiled (compile n c.code)).length ≤
      4 * c.depth * (2 * width * (6 * bits + 21) + 1) + m * (2 * bits + 1) + 1 := by
  dsimp only
  let width := n + 3 * c.size
  let bits := Nat.log2 width + 1
  change (encCompiled (compile n c.code)).length ≤
    4 * c.depth * (2 * width * (6 * bits + 21) + 1) + m * (2 * bits + 1) + 1
  have hwidth : ∀ layer ∈ (compile n c.code).1, layer.length ≤ width := by
    intro layer hlayer
    have h := length_of_mem_schedule n c.code.1 (wireDepthsCode n c.code.1)
      (depthCode n c.code) hlayer
    rw [show c.code.1.length = c.size from c.program.length_code] at h
    exact h.le
  have hschedule := (wellFormed_compile c).length_encList_le
    (width := width) (by dsimp only [width]; omega) hwidth
  rw [length_compile] at hschedule
  change (encList (encList encNode) (compile n c.code).1).length ≤
    2 * c.depth * (2 * width * (6 * bits + 21) + 1) at hschedule
  have houtputs : (encList encNat (compile n c.code).2).length ≤ m * (2 * bits + 1) := by
    have h := Turing.MultiTapeTM.length_encList_le encNat (compile n c.code).2
      (b := bits) (fun i hi => ?_)
    · simpa only [compile_outputs, Circuit.code, List.length_ofFn] using h
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hi
    apply length_encNat_le_log2
    have hwire := (c.outputs j).toNat_lt
    dsimp only [width]
    omega
  rw [length_encPair]
  calc
    _ ≤ 2 * (2 * c.depth * (2 * width * (6 * bits + 21) + 1)) + 1 +
        m * (2 * bits + 1) := by omega
    _ = _ := by ring

end Cslib.Circuits.Boolean.Layered
