/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Encoding.Evaluation
public import Complexity.Computability.Circuit.Depth
import Mathlib.Data.List.GetD

/-!
# Layers of circuit codes

A *layer* is a list of gates that read only the wires computed before it. Evaluating a layer
appends the value of each of its gates, computed from the values before the layer
(`evalCode_layer`), and in the depth interpretation its values are at most the largest value before
it plus the largest cost of its operations (`le_of_mem_evalCode_depth_layer`). So a circuit given
as a code of layers has a depth with costs bounded by summing the costs of the layers
(`Circuit.depthWith_le_of_evalCode`).

## Main results

* `Cslib.Circuits.evalCode_layer`: the values of a layer.
* `Cslib.Circuits.le_of_mem_evalCode_depth_layer`: depths after a layer.
* `Cslib.Circuits.Circuit.depthWith_le_of_evalCode`: a bound on all the depths computed by the code
  of a circuit bounds its depth with costs.

These are original implementation lemmas for the existing circuit semantics.
-/

@[expose] public section

namespace Cslib.Circuits

universe u v

variable {σ : Signature.{v}} {U : Type u} {n m : ℕ}

/-- A list of gates, each with as many arguments as its arity and reading only the `n` inputs and
the `k` gates before the list, is a code from gate `k`. -/
theorem Program.isCodeFrom_of_forall {n k : ℕ} {gates : List (σ.Op × List ℕ)}
    (h : ∀ g ∈ gates, g.2.length = σ.Arity g.1 ∧ ∀ i ∈ g.2, i < n + k) :
    Program.IsCodeFrom σ n k gates :=
  Program.isCodeFrom_of_getElem fun _ hj =>
    let ⟨h₁, h₂⟩ := h _ (List.getElem_mem hj)
    ⟨h₁, fun i hi => (h₂ i hi).trans_le (Nat.le_add_right _ _)⟩

/-- **Evaluating a layer.** When every gate of `gates` reads only wires below the length of `x`,
evaluating `gates` from `x` appends the value of each gate on the wires of `x`. -/
theorem evalCode_layer (I : Interpretation σ U) (d : U) (x : List U)
    (gates : List (σ.Op × List ℕ)) (h : ∀ g ∈ gates, ∀ i ∈ g.2, i < x.length) :
    evalCode I d x gates =
      x ++ gates.map fun g => I g.1 fun a => g.2[a.val]?.elim d (x.getD · d) := by
  induction gates using List.reverseRecOn with
  | nil => simp
  | append_singleton gates g ih =>
    have ih := ih fun g' hg' => h g' (List.mem_append_left _ hg')
    rw [evalCode_append_singleton, ih, List.map_append, List.map_singleton, List.append_assoc]
    congr 3
    refine congrArg (I g.1) (funext fun a => ?_)
    rcases ha : g.2[a.val]? with _ | i
    · rfl
    · have hi : i < x.length := h g (List.mem_append_right _ (List.mem_singleton_self g)) i
        (List.mem_of_getElem? ha)
      exact List.getD_append _ _ _ _ hi

/-- **Depths after a layer.** In the depth interpretation, if the values of `x` are at most `D`
and every gate of the layer `gates` has cost at most `c`, the values after the layer are at most
`D + c`. -/
theorem le_of_mem_evalCode_depth_layer (cost : σ.Op → ℕ) (x : List ℕ)
    (gates : List (σ.Op × List ℕ)) (h : ∀ g ∈ gates, ∀ i ∈ g.2, i < x.length) {D c : ℕ}
    (hx : ∀ v ∈ x, v ≤ D) (hc : ∀ g ∈ gates, cost g.1 ≤ c) :
    ∀ v ∈ evalCode (depthInterpretation cost) 0 x gates, v ≤ D + c := by
  rw [evalCode_layer _ _ _ _ h]
  intro v hv
  rcases List.mem_append.1 hv with hv | hv
  · exact (hx v hv).trans (Nat.le_add_right _ _)
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hv
    have hargs : ∀ a : Fin (σ.Arity g.1),
        g.2[a.val]?.elim 0 (x.getD · 0) ≤ (fun _ => D) a + 0 := fun a => by
      rcases ha : g.2[a.val]? with _ | i
      · exact Nat.zero_le _
      · have hi : i < x.length := h g hg i (List.mem_of_getElem? ha)
        simp only [Option.elim_some, List.getD_eq_getElem _ _ hi, Nat.add_zero]
        exact hx _ (List.getElem_mem hi)
    have := depthInterpretation_le_add cost g.1 hargs
    simp only [depthInterpretation, Nat.add_zero] at this ⊢
    have hfold : Fin.foldl (σ.Arity g.1) (fun depth k => max depth D) 0 ≤ D := by
      rw [Fin.foldl_max_eq_max_sup]
      exact max_le (Nat.zero_le _) (Finset.sup_le fun _ _ => le_rfl)
    have := hc g hg
    omega

/-- **Depth from the code.** If every value that the code of a circuit computes in the depth
interpretation from zero inputs is at most `D`, the circuit has depth at most `D` with costs. -/
theorem Circuit.depthWith_le_of_evalCode (cost : σ.Op → ℕ) (c : Circuit σ n m) {D : ℕ}
    (h : ∀ v ∈ evalCode (depthInterpretation cost) 0 (List.replicate n 0) c.code.1, v ≤ D) :
    c.depthWith cost ≤ D := by
  rw [Circuit.depthWith_le_iff]
  intro j
  have heval := c.eval_eq_getD (depthInterpretation cost) 0 (fun _ => 0) j
  rw [List.ofFn_const] at heval
  have hw : c.program.wireDepthsWith cost (c.outputs j) = c.eval (depthInterpretation cost)
      (fun _ => 0) j := by
    cases hj : c.outputs j <;> simp [Circuit.eval, Program.trace, Program.wireDepthsWith,
      Program.depthsWith, hj]
  rw [hw, heval, List.getD_eq_getElem?_getD]
  rcases hv : (evalCode (depthInterpretation cost) 0 (List.replicate n 0) c.code.1)[
    (c.outputs j).toNat]? with _ | v
  · exact Nat.zero_le _
  · exact h v (List.mem_of_getElem? hv)

end Cslib.Circuits
