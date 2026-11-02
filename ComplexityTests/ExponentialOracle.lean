/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Complexity.Classes.Oracle.Exponential
public import Complexity.Computability.Complexity.Classes.Oracle.Closure
public import Complexity.Computability.Complexity.Classes.Hierarchy
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative

/-!
# Regression tests for exponential time relative to an oracle

`E ^ NP` contains a problem outside `P`, and `E` relative to `A` can ask `A` about
exponentially long words, through the preprocessing rule.
-/

@[expose] public section

namespace ComplexityTests.ExponentialOracle

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- `E ^ NP` contains the exponential-time diagonal, which is not in `P`. -/
example : ∃ L ∈ ENP encBits, L ∉ P encBits :=
  ⟨{x | diagonal x = true},
    E_subset_ENP encBits (mem_E_iff.mpr
      ⟨4, setOf_mem_DTIME_of_computableInO computableInO_diagonal fun _ => le_rfl⟩),
    diagonal_notMem_P⟩

/-- Writing `2 ^ |x|` in unary takes time `O(2 ^ (2 * |x|))`. -/
theorem computableInO_two_pow_length :
    ComputableInO (fun x : List Bool => 2 ^ x.length) encBits encUnary
      (fun x => 2 ^ (2 * (encBits x).length)) (fun x => 2 ^ (2 * (encBits x).length)) := by
  refine (ComputableInO.unary_two_pow.comp ComputableInO.lengthUnary).mono 2
    (fun x => ?_) (fun x => ?_)
  all_goals
    have h₁ : x.length + 1 ≤ 2 ^ x.length := Nat.lt_two_pow_self
    have h₂ : 2 ^ x.length ≤ 2 ^ (2 * x.length) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h₃ : (x.length + 1) * 2 ^ x.length ≤ 2 ^ (2 * x.length) := by
      rw [two_mul, pow_add]
      exact Nat.mul_le_mul_right _ h₁
    simp only [encBits, Function.Embedding.coe_refl, id_eq]
    omega

/-- **Exponentially long requests.** Relative to any `A`, exponential time decides whether the
word of `2 ^ |x|` ones is in `A`: pad, then ask once. -/
example (A : Set (List Bool)) :
    {x : List Bool | List.replicate (2 ^ x.length) true ∈ A} ∈ EWithOracle A encBits := by
  have hM : {n : ℕ | List.replicate n true ∈ A} ∈ PWithOracle A encUnary :=
    PolyTimeReducible.mem_PWithOracle
      ⟨fun n => List.replicate n true, ComputableInPolyTime.of_eq fun _ => rfl, fun _ => Iff.rfl⟩
      (mem_PWithOracle_self A)
  have h := preimage_mem_EWithOracle hM computableInO_two_pow_length
  exact h

/-- `NP` lies inside `E ^ NP`; with `E ⊆ E ^ NP`, both inclusions are available. -/
example : NP encBits ⊆ ENP encBits := NP_subset_ENP

end ComplexityTests.ExponentialOracle
