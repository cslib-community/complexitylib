/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.Clique
import Complexity.Tactic.PolyTime

/-!
# Stating P, NP and reduction claims

These examples use plain `ComputableInPolyTime` throughout. The encodings are part of each
statement: bit strings use `encBits`; graph/target pairs use `encPair encGraph encNat`.
The clique example reuses the library's verifier and its certificate-length proof, then builds
the actual graph-complement reduction and transfers known hardness. It is an application of
existing results, not a new completeness theorem.
-/

namespace ComplexityTests.NPCompleteness

open Cslib.Complexity Turing.MultiTapeTM

/-- A P proof supplies a Boolean decider, its cost certificate and its membership equivalence. -/
theorem startsTrue_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

/-- The same ordinary decision problem is in NP by the public class inclusion. -/
example : {w : List Bool | w.headD false = true} ∈ NP encBits :=
  P_subset_NP startsTrue_mem_P

/-- For NP, the verifier also needs a proved certificate bound: here exactly the encoded
instance length, represented by the polynomial `X`. -/
theorem clique_mem_NP : Clique ∈ NP (encPair encGraph encNat) :=
  ⟨Polynomial.X, Clique.verifier, by fun_prop, Clique.isVerifier⟩

/-- Complement the graph on its declared vertices, leaving the requested size unchanged. -/
def complementInstance (x : Graph × ℕ) : Graph × ℕ := (x.1.compl, x.2)

/-- Unfold local definitions so certificate automation sees the registered operations. -/
@[fun_prop] theorem complementInstance_polyTime :
    ComputableInPolyTime complementInstance
      (encPair encGraph encNat) (encPair encGraph encNat) := by
  unfold complementInstance
  polytime

/-- A reduction has a map, its polynomial-time certificate, and a membership equivalence.
The equivalence must point from the source problem to the image in the target problem. -/
theorem independentSet_to_clique :
    PolyTimeReducible (encPair encGraph encNat) (encPair encGraph encNat) IndependentSet Clique :=
  ⟨complementInstance, by fun_prop,
    fun ⟨G, k⟩ => (Graph.compl_mem_Clique_iff G k).symm⟩

/-- Combine NP membership with hardness transferred from the known hard source problem. -/
theorem clique_npComplete : NPComplete (encPair encGraph encNat) Clique :=
  ⟨clique_mem_NP, IndependentSet_npHard.trans independentSet_to_clique⟩

-- The reduction keeps a zero target and complements only the declared vertices.
example : complementInstance (([0, 1], []), 0) = (([0, 1], [(0, 1), (1, 0)]), 0) := by decide

-- The empty graph has a zero-size clique, but no clique of size one.
example : ((([], []) : Graph), 0) ∈ Clique :=
  ⟨∅, by simp, rfl⟩

example : ((([], []) : Graph), 1) ∉ Clique := by
  intro h
  have := Graph.le_card_of_mem_Clique h
  simp at this

/-- Plain `fun_prop` composes the plain `Clique` verifier certificate with a plain map. -/
example {γ : Type} {enc : γ ↪ List Bool} {f : γ → (Graph × ℕ) × List Bool}
    (hf : ComputableInPolyTime f enc (encPair (encPair encGraph encNat) encBits)) :
    ComputableInPolyTime (fun c => Clique.verifier (f c)) enc encBool := by
  fun_prop

end ComplexityTests.NPCompleteness
