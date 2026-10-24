/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.Amplification.Enumeration
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Tactic.PolyTime

/-! Complete finite enumeration, uniform construction, and functional-expression clients. -/

namespace ComplexityTests.PCPEncodedEnumeration

open Cslib Cslib.PCP Cslib.PCP.Encoded Cslib.PCP.HadamardTester Turing.MultiTapeTM
open ComputableTidilyInPolyTime

-- Only these small enumerations are evaluated, not the complete tester's truth-table output.
example : (FinEnum.toList (Graph.PowerLabel Unit 1 2)).length = 8 := by decide
example : (FinEnum.toList Query).length = 17 := by decide
example : (FinEnum.toList (Graph.PowerLabel Unit 1 2)).Nodup := FinEnum.nodup_toList
example (d : Graph.PowerLabel Unit 1 2) : d ∈ FinEnum.toList _ := FinEnum.mem_toList d
example (i : Query) : i ∈ FinEnum.toList _ := FinEnum.mem_toList i

-- Public enumeration values are reusable without recreating implementation-local instances.
example : (@FinEnum.toList (Rand Unit) (Rand.finEnum Unit)).Nodup :=
  @FinEnum.nodup_toList _ (Rand.finEnum Unit)

example (ω : Rand Unit) : ω ∈ @FinEnum.toList _ (Rand.finEnum Unit) :=
  @FinEnum.mem_toList _ (Rand.finEnum Unit) ω

example (slot : Graph.SelectedComposeSlot Unit) :
    (Graph.SelectedComposeSlot.finEnum Unit).equiv.symm
      ((Graph.SelectedComposeSlot.finEnum Unit).equiv slot) =
      slot :=
  (Graph.SelectedComposeSlot.finEnum Unit).equiv.symm_apply_apply slot

private def unitEval (constraint : Bool) (_ _ : Unit) : Bool := constraint

private def rotateLoops (p : ℕ × (ℕ × Unit)) : ℕ × Unit := p.2

private theorem rotateLoops_eq (n : ℕ) (v : Fin n) (d : Unit) :
    rotateLoops (n, v.val, d) =
      (((RotationMap.loops (Fin n) Unit).rot (v, d)).1.val,
        ((RotationMap.loops (Fin n) Unit).rot (v, d)).2) := rfl

private theorem polytime_rotateLoops :
    ComputableTidilyInPolyTime rotateLoops
      (encPair encUnary (encPair encUnary (encFinEnum Unit)))
      (encPair encUnary (encFinEnum Unit)) := by
  unfold rotateLoops
  fun_prop

private theorem polytime_unitEval : ComputableTidilyInPolyTime
    (fun p : Bool × (Unit × Unit) => unitEval p.1 p.2.1 p.2.2)
      (encPair encBool (encPair (encFinEnum Unit) (encFinEnum Unit))) encBool := by
  unfold unitEval
  fun_prop

-- The full complete round has a uniform certificate, including for arbitrary runtime graphs.
example : ComputableInPolyTime
    (fun g : Graph Bool => g.amplifyEnumerated unitEval false rotateLoops 1 2)
    (Graph.encoding encBool) (Graph.encoding (encPi (encPi encBool))) := by
  have hr := polytime_rotateLoops
  have he := polytime_unitEval
  polytime

example : ((⟨0, [⟨4, 7, false⟩]⟩ : Graph Bool).amplifyEnumerated
    unitEval false rotateLoops 1 2).WellFormed :=
  Graph.wellFormed_amplifyEnumerated _ unitEval false
    (fun n => RotationMap.loops (Fin n) Unit) rotateLoops rotateLoops_eq 1 2

-- Already at a one-element alphabet, the complete tester is too large to materialize here.
example (g : Graph Bool) :
    (g.amplifyEnumerated unitEval false rotateLoops 1 2).edges.length =
      131941395333120 * g.edges.length := by
  rw [Graph.length_edges_amplifyEnumerated]
  simp only [Graph.PowerLabel, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Graph.PreprocessLabel, Fintype.card_sum, Fintype.card_unique, Fintype.card_bool,
    Graph.PowerAlphabet]
  ring

section Arbitrary

variable {C α D Input : Type} [FinEnum α] [FinEnum D]
  {input : Input ↪ List Bool} {enc : C ↪ List Bool}
  {alphabet : α ↪ List Bool} {labels : D ↪ List Bool}
  (graph : Input → Graph C) (eval : C → α → α → Bool)
  (rotate : ℕ × (ℕ × D) → ℕ × D) (fallback : C) (T q : ℕ) [NeZero q]
  (hg : ComputableTidilyInPolyTime graph input (Graph.encoding enc))
  (hr : ComputableTidilyInPolyTime rotate
    (encPair encUnary (encPair encUnary labels)) (encPair encUnary labels))
  (he : ComputableTidilyInPolyTime (fun p : C × (α × α) => eval p.1 p.2.1 p.2.2)
    (encPair enc (encPair alphabet alphabet)) encBool)

example : ComputableInPolyTime
    (fun x => (graph x).amplifyEnumerated eval fallback rotate T q)
    input (Graph.encoding (encPi (encPi encBool))) := by
  fail_if_success (clear hg; fun_prop)
  fail_if_success (clear hr; fun_prop)
  fail_if_success (clear he; fun_prop)
  fun_prop

example : ComputableInPolyTime
    (fun x => let g := graph x; g.amplifyEnumerated eval fallback rotate T q)
    input (Graph.encoding (encPi (encPi encBool))) := by
  polytime

end Arbitrary

end ComplexityTests.PCPEncodedEnumeration
