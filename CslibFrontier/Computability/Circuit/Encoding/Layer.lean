/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Encoding.Evaluation
public import CslibFrontier.Computability.Circuit.Depth
import CslibFrontier.Foundations.Data.List.GetD
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
* `Cslib.Circuits.Circuit.isCodeFrom_code`, `Cslib.Circuits.Circuit.toNat_outputs_lt`: the code
  of a circuit is a code from its inputs, and its outputs are wires of it.
* `Cslib.Circuits.getD_evalCode_depth_le`, `Cslib.Circuits.cost_le_getD_evalCode_depth`: in the
  depth interpretation, a gate is deeper than its arguments, and at least as deep as its cost.
* `Cslib.Circuits.Circuit.getD_evalCode_depthInterpretation`: the depth with costs of an output
  is the value of its wire in the depth interpretation.
* `Cslib.Circuits.Circuit.depthWith_le_of_evalCode`: a bound on all the depths computed by the code
  of a circuit bounds its depth with costs.

These are original implementation lemmas for the existing circuit semantics.
-/

public section

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
      · exact hx _ (List.getD_mem 0 (h g hg i (List.mem_of_getElem? ha)))
    have := depthInterpretation_le_add cost g.1 hargs
    simp only [depthInterpretation, Nat.add_zero] at this ⊢
    have hfold : Fin.foldl (σ.Arity g.1) (fun depth k => max depth D) 0 ≤ D := by
      rw [Fin.foldl_max_eq_max_sup]
      exact max_le (Nat.zero_le _) (Finset.sup_le fun _ _ => le_rfl)
    have := hc g hg
    omega

/-- The gate list of a circuit is a code from its inputs. -/
theorem Circuit.isCodeFrom_code (c : Circuit σ n m) : Program.IsCodeFrom σ n 0 c.code.1 :=
  (Circuit.isSome_ofCode_iff.1 (by rw [Circuit.ofCode_code]; rfl)).1

/-- The output wires of a circuit are wires of its code. -/
theorem Circuit.toNat_outputs_lt (c : Circuit σ n m) (j : Fin m) :
    (c.outputs j).toNat < n + c.code.1.length :=
  (Circuit.isSome_ofCode_iff.1 (by rw [Circuit.ofCode_code]; rfl)).2.2 _
    (by simp [Circuit.code])

/-- In the depth interpretation, a gate is deeper than each of its arguments by its cost. -/
theorem getD_evalCode_depth_le (cost : σ.Op → ℕ) {gates : List (σ.Op × List ℕ)}
    (h : Program.IsCodeFrom σ n 0 gates) {j : ℕ} {g : σ.Op × List ℕ} (hg : gates[j]? = some g)
    {c : ℕ} (hc : c ∈ g.2) :
    (evalCode (depthInterpretation cost) 0 (List.replicate n 0) gates).getD c 0 + cost g.1 ≤
      (evalCode (depthInterpretation cost) 0 (List.replicate n 0) gates).getD (n + j) 0 := by
  have h' : Program.IsCodeFrom σ (List.replicate n 0).length 0 gates := by
    rwa [List.length_replicate]
  have hv := getD_evalCode (depthInterpretation cost) 0 (List.replicate n 0) h' hg
  rw [List.length_replicate] at hv
  rw [hv, depthInterpretation, Fin.foldl_max_eq_max_sup, Nat.zero_max]
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hg
  have hlen := (h.getElem j hj).1
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  refine Nat.add_le_add_right (le_trans ?_ (Finset.le_sup (Finset.mem_univ
    (⟨i, hlen ▸ hi⟩ : Fin (σ.Arity gates[j].1))))) _
  simp [List.getElem?_eq_getElem hi]

/-- In the depth interpretation, a gate is at least as deep as its cost. -/
theorem cost_le_getD_evalCode_depth (cost : σ.Op → ℕ) {gates : List (σ.Op × List ℕ)}
    (h : Program.IsCodeFrom σ n 0 gates) {j : ℕ} {g : σ.Op × List ℕ} (hg : gates[j]? = some g) :
    cost g.1 ≤
      (evalCode (depthInterpretation cost) 0 (List.replicate n 0) gates).getD (n + j) 0 := by
  have h' : Program.IsCodeFrom σ (List.replicate n 0).length 0 gates := by
    rwa [List.length_replicate]
  have hv := getD_evalCode (depthInterpretation cost) 0 (List.replicate n 0) h' hg
  rw [List.length_replicate] at hv
  rw [hv, depthInterpretation]
  exact Nat.le_add_left _ _

/-- **Depths through the code.** The depth with costs of the wire of output `j` is the value at
its number of the code of the circuit evaluated in the depth interpretation from zero inputs. -/
theorem Circuit.getD_evalCode_depthInterpretation (cost : σ.Op → ℕ) (c : Circuit σ n m)
    (j : Fin m) :
    (evalCode (depthInterpretation cost) 0 (List.replicate n 0) c.code.1).getD
      (c.outputs j).toNat 0 = c.program.wireDepthsWith cost (c.outputs j) := by
  have heval := c.eval_eq_getD (depthInterpretation cost) 0 (fun _ => 0) j
  rw [List.ofFn_const] at heval
  rw [← heval]
  cases hj : c.outputs j <;> simp [Circuit.eval, Program.trace, Program.wireDepthsWith,
    Program.depthsWith, hj]

/-- **Depth from the code.** If every value that the code of a circuit computes in the depth
interpretation from zero inputs is at most `D`, the circuit has depth at most `D` with costs. -/
theorem Circuit.depthWith_le_of_evalCode (cost : σ.Op → ℕ) (c : Circuit σ n m) {D : ℕ}
    (h : ∀ v ∈ evalCode (depthInterpretation cost) 0 (List.replicate n 0) c.code.1, v ≤ D) :
    c.depthWith cost ≤ D := by
  rw [Circuit.depthWith_le_iff]
  intro j
  rw [← c.getD_evalCode_depthInterpretation cost j]
  exact h _ (List.getD_mem 0 (by
    rw [length_evalCode, List.length_replicate]
    exact c.toNat_outputs_lt j))

end Cslib.Circuits
