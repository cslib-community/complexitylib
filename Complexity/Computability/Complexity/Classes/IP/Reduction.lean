/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP
public import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Probabilistic.Oracle.Composition

/-!
# `IP` is closed under polynomial-time reductions

If `A` reduces to `B` in polynomial time and `B` has an interactive proof, so has `A`: the verifier
for `A` computes the reduction and runs the verifier for `B` on its result, which is still strict
oracle PPT (`Cslib.Probability.IsOraclePPTOn.preprocess'`), with the same provers, completeness and
soundness [Arora and Barak, Chapter 8][AroraBarak09].

## Main results

* `Cslib.Complexity.IsInteractiveProof.comp`: an interactive proof along a reduction.
* `Cslib.Complexity.PolyTimeReducible.mem_IP`: closure of `IP` under reductions.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability

variable {Operation α β : Type}

/-- An interactive proof for `B` gives one for every `A` that `f` maps into `B` exactly. -/
theorem IsInteractiveProof.comp {verifier : β → WordOracleComp Operation Bool} {A : Set α}
    {B : Set β} {c s : ENNReal} (h : IsInteractiveProof verifier B c s) {f : α → β}
    (hf : ∀ a, a ∈ A ↔ f a ∈ B) : IsInteractiveProof (fun a => verifier (f a)) A c s where
  complete a ha := h.complete (f a) ((hf a).1 ha)
  sound a ha := h.sound (f a) fun hb => ha ((hf a).2 hb)

/-- **`IP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_IP {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α}
    {B : Set β} (hAB : PolyTimeReducible encA encB A B) (hB : B ∈ IP encB) : A ∈ IP encA := by
  obtain ⟨f, hf, hfA⟩ := hAB
  obtain ⟨verifier, hV, hproof⟩ := hB
  exact ⟨fun a => verifier (f a), hV.preprocess' hf, hproof.comp hfA⟩

end Cslib.Complexity
