/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Operators
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Advice
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The bounded-error NP operator and Arthur–Merlin verification

`BPOp_NP` identifies the native verifier classes `BP·NP` and `AM`, for arbitrary instance
encodings. The NP predicate existentially quantifies over Merlin's reply; conversely the AM
verifier splits its message at Arthur's prescribed coin length and runs the NP verifier.
The NP certificate bound is evaluated at the encoded pair length, not the instance length.

This is the operator milestone associated with Exercise 8.5 of [AroraBarak07]. The correspondence
with randomized reductions to 3SAT in Definition 7.20, and the nondeterministic circuit endpoint
of Exercise 7.5, are separate obligations.

## Main results

* `Cslib.Complexity.BPOp_NP`: `BP·NP = AM`.
* `Cslib.Complexity.BPOp_NP_subset_NPPoly`: the resulting advice inclusion.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- The native bounded-error NP operator is exactly two-message Arthur–Merlin verification. -/
theorem BPOp_NP : BPOp enc (NP (encPair enc encBits)) = AM enc := by
  classical
  ext A
  constructor
  · rintro ⟨p, B, ⟨s, W, hW, hB⟩, hA⟩
    let q := s.comp (2 * Polynomial.X + 1 + p)
    let V : α × List Bool → Bool := fun x =>
      W ((x.1, x.2.take (p.eval (enc x.1).length)),
        x.2.drop (p.eval (enc x.1).length))
    have hp : ComputableInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.unary_eval p).comp
        ((ComputableInPolyTime.encoding_length enc).comp (.fst enc encBits))
    have hV : ComputableInPolyTime V (encPair enc encBits) encBool :=
      hW.comp (((ComputableInPolyTime.fst enc encBits).prod
        (.bitsTakeWithInput (.snd enc encBits) hp)).prod
        (.bitsDropWithInput (.snd enc encBits) hp))
    refine ⟨p, q, V, hV, ?_⟩
    rw [isArthurMerlinVerifier_iff_decidesWithBoundedError]
    unfold DecidesWithBoundedError PromiseProblem.SolvesWithBoundedError BoundedErrorAt at *
    have he (a : α) (r : Fin (p.eval (enc a).length) → Bool) :
        arthurMerlinSlice enc q V (a, List.ofFn r) = decide ((a, List.ofFn r) ∈ B) := by
      have hlen : s.eval ((encPair enc encBits) (a, List.ofFn r)).length =
          q.eval (enc a).length := by
        simp [q, encBits_apply, Polynomial.eval_comp]
      have hv (y : Fin (q.eval (enc a).length) → Bool) :
          V (a, List.ofFn r ++ List.ofFn y) = W ((a, List.ofFn r), List.ofFn y) := by
        simp [V]
      simp only [arthurMerlinSlice, hv]
      congr 1
      apply propext
      rw [hB, hlen]
      simp only [List.exists_iff_exists_tuple, List.length_ofFn, exists_and_left, exists_eq_left]
    simpa only [he] using hA
  · rintro ⟨p, q, V, hV, hA⟩
    let B : Set (α × List Bool) := {x | ∃ y : List Bool,
      y.length = q.eval (enc x.1).length ∧ V (x.1, x.2 ++ y) = true}
    refine ⟨p, B, mem_NP_setOf_exists_append hV q, ?_⟩
    have he : (fun x => decide (x ∈ B)) = arthurMerlinSlice enc q V := by
      funext x
      unfold arthurMerlinSlice
      congr 1
      apply propext
      change (∃ y : List Bool, y.length = q.eval (enc x.1).length ∧
        V (x.1, x.2 ++ y) = true) ↔ _
      simp only [List.exists_iff_exists_tuple, List.length_ofFn, exists_and_left, exists_eq_left]
    rw [he]
    exact isArthurMerlinVerifier_iff_decidesWithBoundedError.mp hA

/-- The native bounded-error NP operator admits polynomial advice for NP verification. -/
theorem BPOp_NP_subset_NPPoly : BPOp enc (NP (encPair enc encBits)) ⊆ NPPoly enc := by
  rw [BPOp_NP]
  exact AM_subset_NPPoly

end Cslib.Complexity
