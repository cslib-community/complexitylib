/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Binarize
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for binarized tensor networks

A network with one edge over the alphabet `Fin 3`, binarized with the two-bit code of each
letter: its contraction is unchanged, the unused word `(true, true)` gets weight zero, a valid
word reads the original tensor, and the degree doubles.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Frontier.TensorNetworkBinarize

open Cslib.Circuits.Frontier

/-- Two vertices joined by one edge carrying a letter of `Fin 3`, with the tensors
`A = (1, 2, 3)` at vertex `0` and `B = (4, 5, 6)` at vertex `1`. -/
def ternary : TensorNetwork ℕ (Fin 3) (Fin 2) Unit where
  src _ := 0
  tgt _ := 1
  tensor v x := ![![1, 2, 3], ![4, 5, 6]] v (x ())
  tensor_congr v x y h := by
    rw [h () (by fin_cases v <;> simp)]

/-- By hand: `Z = 1·4 + 2·5 + 3·6 = 32`. -/
theorem contraction_ternary : ternary.contraction = 32 := by decide

/-- The two binary digits of a letter, least significant first. -/
def code (u : Fin 3) : Fin 2 → Bool :=
  ![u.val.testBit 0, u.val.testBit 1]

theorem code_injective : Function.Injective code := by decide

/-- Binarization keeps the contraction `32`. -/
example : (ternary.binarize code).contraction = 32 := by
  rw [TensorNetwork.contraction_binarize _ code_injective, contraction_ternary]

/-- The word `(true, true)` codes no letter, so a vertex reading it has weight zero. -/
example : (ternary.binarize code).tensor 0 (fun _ => true) = 0 := by
  have : TensorNetwork.bitsOn (fun _ : Unit × Fin 2 => true) () ∉ Set.range code := by
    rintro ⟨u, hu⟩
    have h0 := congrFun hu 0
    have h1 := congrFun hu 1
    revert h0 h1
    fin_cases u <;> decide
  simp only [TensorNetwork.binarize]
  exact ite_eq_right fun h => this (h () (Or.inl rfl))

/-- The word `(false, true)` codes the letter `2`, so vertex `1` reads its entry `6`. -/
example : (ternary.binarize code).tensor 1 (fun p => p.2 = 1) = 6 := by
  have hword : TensorNetwork.bitsOn (fun p : Unit × Fin 2 => decide (p.2 = 1)) () = code 2 := by
    funext j
    fin_cases j <;> rfl
  have hdec : Function.invFun code (code 2) = 2 :=
    Function.leftInverse_invFun code_injective 2
  simp only [TensorNetwork.binarize]
  rw [ite_eq_left fun e _ => ⟨2, by cases e; exact hword.symm⟩]
  simp only [ternary, hword, hdec]
  rfl

/-- Each vertex has one edge; after binarization it has two, and the network stays bipartite. -/
example : (ternary.binarize code).MaxDegreeLE 2 ∧ (ternary.binarize code).IsBipartite := by
  refine ⟨ternary.maxDegreeLE_binarize code (d := 1) fun v => ?_,
    ternary.isBipartite_binarize code ⟨fun v => v = 0, fun _ => by simp [ternary]⟩⟩
  exact (Set.ncard_le_card _).trans (by simp)

end ComplexityTests.Computability.Circuit.Frontier.TensorNetworkBinarize
