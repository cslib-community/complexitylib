/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Images of problems in `NP`

The encodings of the members of a problem in `NP` form a problem in `NP` on words, when the
encoding has a decoder (`Cslib.Complexity.mem_NP_image`): the verifier decodes the word, checks
that it encodes what was decoded, and runs the verifier of the problem. In particular the
encodings of the satisfiable formulas form a problem in `NP` on words
(`Cslib.Complexity.image_SAT_mem_NP`), an oracle language that answers, through the Cook–Levin
reduction, every problem in `NP`.

## Main results

* `Cslib.Complexity.mem_NP_image`: images of problems in `NP` under encodings with decoders.
* `Cslib.Complexity.image_SAT_mem_NP`: the encodings of the satisfiable formulas.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **Images of problems in `NP`.** The encodings of the members of a problem in `NP` form a
problem in `NP` on words, when the encoding has a decoder: the verifier decodes the word, checks
that it encodes what was decoded, and runs the verifier of the problem. -/
theorem mem_NP_image {β : Type} {encB : β ↪ List Bool} (D : Decoder encB) {B : Set β}
    (hB : B ∈ NP encB) : encB '' B ∈ NP encBits := by
  obtain ⟨p, V, hV, hBV⟩ := mem_NP.mp hB
  have hdec : ComputableInPolyTime (fun x : List Bool × List Bool => D.decode x.1)
      (encPair encBits encBits) encB := D.computableInPolyTime.comp (.fst _ _)
  have henc : ComputableInPolyTime (fun b => encB b) encB encBits := .of_eq fun _ => rfl
  refine mem_NP.mpr
    ⟨p, fun x => decide (encB (D.decode x.1) = x.1) && V (D.decode x.1, x.2), by fun_prop,
      fun w => ?_⟩
  simp only [encBits_apply, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hVc⟩ := (hBV b).1 hb
    exact ⟨c, hc, by rw [D.decode_enc], by rw [D.decode_enc]; exact hVc⟩
  · rintro ⟨c, hc, hw, hVc⟩
    exact ⟨D.decode w, (hBV _).2 ⟨c, by rw [hw]; exact hc, hVc⟩, hw⟩

/-- The encodings of the satisfiable formulas form a problem in `NP` on words. -/
theorem image_SAT_mem_NP : encCNF '' SAT ∈ NP encBits :=
  mem_NP_image (.list (.list (.pair .nat .bool))) SAT.mem_NP

end Cslib.Complexity
