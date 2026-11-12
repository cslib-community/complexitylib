/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.XP
import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique
import CslibFrontier.Computability.Complexity.Parameterized.VertexCover

/-!
# Tests: `W[P]` and `W[t] ⊆ W[P] ⊆ XP`

Nonvacuity checks on `WeightedCircuitSAT` (including weft-`2` circuits and zero-input edge cases),
completeness of `WeightedCircuitSAT` for `WP`, the chain `FPT ⊆ W[t] ⊆ WP ⊆ XP`, and the resulting
`XP` memberships for `WCS t d`, `Clique` and `IndependentSet`.
-/

namespace CslibFrontierTests.WHierarchyXP

open Cslib Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM

/-! ### Nonvacuity of `WeightedCircuitSAT` across wefts and edge cases -/

/-- Two 3-fan-in conjunctions in series (weft `2`, depth `2`). -/
def seriesAnd3 : Σ n, Circuit Unbounded.signature n 1 :=
  ⟨3, ⟨((Program.empty : Program Unbounded.signature 3 0).gate
    ⟨.and 3, fun i => .input i⟩).gate ⟨.and 3, ![.gate 0, .input 1, .input 2]⟩, fun _ => .gate 1⟩⟩

example : seriesAnd3.2.weft = 2 ∧ seriesAnd3.2.depth = 2 := by decide

-- Satisfied by the unique weight-3 input, and unsatisfied at weight 2 and weight 4.
example : (⟨seriesAnd3, 3⟩ : WeightedCircuitSATInstance) ∈ WeightedCircuitSAT :=
  ⟨fun _ => true, by decide, by decide⟩

example : (⟨seriesAnd3, 2⟩ : WeightedCircuitSATInstance) ∉ WeightedCircuitSAT := by
  rintro ⟨x, hk, hx⟩
  revert hk hx
  revert x
  unfold BitString.weight
  decide

example : (⟨seriesAnd3, 4⟩ : WeightedCircuitSATInstance) ∉ WeightedCircuitSAT := by
  rintro ⟨x, hk, -⟩
  change BitString.weight x = 4 at hk
  have hle : 4 ≤ seriesAnd3.1 := hk ▸ BitString.weight_le_length x
  exact absurd hle (by decide)

-- Zero-input edge cases: weight `0` succeeds on `trueCircuit`, fails on `falseCircuit`, and weight
-- `1 > 0` fails even on `trueCircuit`.
example : (⟨WCS.trueCircuit, 0⟩ : WeightedCircuitSATInstance) ∈ WeightedCircuitSAT :=
  ⟨fun _ => false, by simp [BitString.weight], rfl⟩

example : (⟨WCS.trueCircuit, 1⟩ : WeightedCircuitSATInstance) ∉ WeightedCircuitSAT := by
  rintro ⟨x, hk, -⟩
  change BitString.weight x = 1 at hk
  have hle : BitString.weight x ≤ WCS.trueCircuit.1 := BitString.weight_le_length x
  have h0 : WCS.trueCircuit.1 = 0 := rfl
  omega

example : (⟨WCS.falseCircuit, 0⟩ : WeightedCircuitSATInstance) ∉ WeightedCircuitSAT := by
  rintro ⟨_, -, hx⟩
  exact Bool.false_ne_true hx

/-! ### `W[P]` and completeness of `WeightedCircuitSAT` -/

example : WeightedCircuitSAT ∈ WP encWeightedCircuitSAT WeightedCircuitSATInstance.weight ∧
    WPHard encWeightedCircuitSAT WeightedCircuitSATInstance.weight WeightedCircuitSAT :=
  ⟨WeightedCircuitSAT_mem_WP, WeightedCircuitSAT_wPHard⟩

example (t d : ℕ) : WCS t d ∈ WP (encWCS t d) WCSInstance.weight :=
  W_subset_WP t (WCS_mem_W t d)

example : Clique ∈ WP (encPair encGraph encNat) Prod.snd :=
  W_subset_WP 1 Clique_mem_W

example : IndependentSet ∈ WP (encPair encGraph encNat) Prod.snd :=
  W_subset_WP 1 IndependentSet_mem_W

example : VertexCover ∈ WP (encPair encGraph encNat) Prod.snd :=
  FPT_subset_WP VertexCover_mem_FPT

-- Collapse consequence: `WeightedCircuitSAT ∈ FPT` collapses `WP` and every `W[t]` to `FPT`.
example (h : WeightedCircuitSAT ∈ FPT encWeightedCircuitSAT WeightedCircuitSATInstance.weight)
    (t : ℕ)
    {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) :
    W t enc κ = FPT enc κ := by
  have hWP : WP enc κ = FPT enc κ := WP_eq_FPT_iff.2 h enc κ
  exact Set.Subset.antisymm (hWP ▸ W_subset_WP t) (FPT_subset_W t)

/-! ### `XP` memberships and inclusions -/

example : WeightedCircuitSAT ∈ XP encWeightedCircuitSAT WeightedCircuitSATInstance.weight :=
  WeightedCircuitSAT_mem_XP

example {α : Type} (enc : α ↪ List Bool) (κ : α → ℕ) :
    FPT enc κ ⊆ W 1 enc κ ∧ W 1 enc κ ⊆ W 2 enc κ ∧ W 2 enc κ ⊆ WP enc κ ∧ WP enc κ ⊆ XP enc κ :=
  ⟨FPT_subset_W 1, W_mono (by decide), W_subset_WP 2, WP_subset_XP⟩

example (t d : ℕ) : WCS t d ∈ XP (encWCS t d) WCSInstance.weight :=
  WCS_mem_XP t d

example : Clique ∈ XP (encPair encGraph encNat) Prod.snd ∧
    IndependentSet ∈ XP (encPair encGraph encNat) Prod.snd :=
  ⟨Clique_mem_XP, IndependentSet_mem_XP⟩

end CslibFrontierTests.WHierarchyXP
