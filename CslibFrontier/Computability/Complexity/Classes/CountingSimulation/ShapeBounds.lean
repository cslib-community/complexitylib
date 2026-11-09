/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContractionSize

/-!
# Polynomial bounds along the native contraction recursion

Two bounds on a call reached by the native recursion (`FastContraction.nativeMk`), from its shape
(`FastContraction.Shape`), stated for a root whose numbers fit a single parameter. Both resource
analyses of the recursion use them: `CountingSimulation.fastSizes` for explicit networks and
`CountingSimulation.entry_length_le_of_reach` / `CountingSimulation.entry_reach_facts` for entry
procedures.

* Suppose the root's edges, precision and descriptors are below `Y`, its vertices and rows
  together take at most `2 Y`, and its 0/1 modulus has at most `32 Y ^ 2` coefficients. Then a call
  of its shape, its tagged value and its frames are at most `2 ^ 55 Y ^ 24` long
  (`FastContraction.Shape.length_le_pow`, from `FastContraction.Shape.length_le`).
* If the root has `m ≥ D + 81` edges and precision at most `D m ²`, a call of its shape has
  precision at most `m ^ 4` (`FastContraction.Shape.prec_le_pow_four`).

The declarations live in the `FastContraction` namespace so that dot notation on `Shape` reaches
them, but the file sits beside its only clients under `Classes/CountingSimulation`, as the
`FastContraction.Reach` lemmas of `CountingSimulation.FastLeaves` do.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.Shape.length_le_pow`: polynomial sizes.
* `Cslib.Circuits.Frontier.FastContraction.Shape.prec_le_pow_four`: precision at most `m ^ 4`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.7 (p. 64).
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction

open Turing.MultiTapeTM

variable {T : Type} {encT : T ↪ List Bool} {x₀ x : Call T}

/-- **Polynomial sizes of a call of a given shape**: from a root `x₀` at depth `0`, at scale its
number of edges, with bound one more, whose edges and precision are below `Y`, whose vertices and
rows take at most `2 Y`, whose descriptors are at most `Y` long and whose 0/1 modulus has at most
`32 Y ^ 2` coefficients, a call of its shape, its tagged value and, if it is active, its frames are
at most `2 ^ 55 Y ^ 24` long. -/
theorem Shape.length_le_pow (ev : T → List Bool → List ℕ) (h₀s : x₀.scale = x₀.edges)
    (h₀b : x₀.bound = x₀.edges + 1) (h₀d : x₀.depth = 0) (h : Shape x₀ x) {Y : ℕ}
    (hm : x₀.edges + 1 ≤ Y) (hp : x₀.prec + 1 ≤ Y)
    (hV : x₀.net.vertices.length + (encNat x₀.rows).length ≤ 2 * Y)
    (hfl : x₀.fl.length ≤ 32 * Y ^ 2) (hfl1 : ∀ z ∈ x₀.fl, z ≤ 1)
    (hR₀ : ∀ w ∈ x₀.net.vertices, (VertexDesc.enc encT w.2).length ≤ Y) :
    (encCall encT x).length ≤ 2 ^ 55 * Y ^ 24 ∧
      (encValue (x.depth, value ev nativeMk x)).length ≤ 2 ^ 55 * Y ^ 24 ∧
      (active x = true → ∀ vals c,
        (encPair (encCall encT) encFrame (x, frameAt x vals c)).length ≤ 2 ^ 55 * Y ^ 24) := by
  set Z := 2 ^ 14 * Y ^ 8 with hZ
  have hY1 : 1 ≤ Y := by omega
  have hY2 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY3 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY8 : Y ^ 3 ≤ Y ^ 8 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hm2 : x₀.edges ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm5 : (x₀.edges + 1) ^ 5 ≤ Y ^ 5 := Nat.pow_le_pow_left hm 5
  -- `Z` dominates the root's numbers, as `Shape.length_le` requires.
  have hPm : x₀.prec + (x₀.edges + 1) * (40 * x₀.edges ^ 2) + 1 ≤ 41 * Y ^ 3 := by
    have : (x₀.edges + 1) * (40 * x₀.edges ^ 2) ≤ Y * (40 * Y ^ 2) := Nat.mul_le_mul hm (by omega)
    have : Y * (40 * Y ^ 2) = 40 * Y ^ 3 := by ring
    omega
  have hZ1 : 256 * (x₀.edges + 1) ^ 5 * (x₀.prec + (x₀.edges + 1) * (40 * x₀.edges ^ 2) + 1) +
      x₀.fl.length ≤ Z := by
    have h1 : 256 * (x₀.edges + 1) ^ 5 * (x₀.prec + (x₀.edges + 1) * (40 * x₀.edges ^ 2) + 1) ≤
        256 * Y ^ 5 * (41 * Y ^ 3) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hm5) hPm
    have h2 : 256 * Y ^ 5 * (41 * Y ^ 3) = 10496 * Y ^ 8 := by ring
    omega
  have hZ2 : x₀.net.vertices.length + (x₀.edges + 1) * x₀.edges ^ 2 + (encNat x₀.rows).length ≤
      Z := by
    have : (x₀.edges + 1) * x₀.edges ^ 2 ≤ Y * Y ^ 2 := Nat.mul_le_mul hm hm2
    have : Y * Y ^ 2 = Y ^ 3 := by ring
    omega
  have hR₀' : ∀ w ∈ x₀.net.vertices,
      (VertexDesc.enc encT w.2).length ≤ 200 * (Z + 1) ^ 2 := by
    intro w hw
    have := hR₀ w hw
    have : Z ≤ (Z + 1) ^ 2 := (Nat.le_succ Z).trans (Nat.le_self_pow (by norm_num) _)
    omega
  obtain ⟨hc, hv, hf⟩ := h.length_le ev h₀s h₀b h₀d hZ1 hZ2 hfl1 hR₀'
  -- `1000 (Z + 1) ^ 3 ≤ 2 ^ 55 Y ^ 24`.
  have hfin : 1000 * (Z + 1) ^ 3 ≤ 2 ^ 55 * Y ^ 24 := by
    have h1 : Z + 1 ≤ 2 ^ 15 * Y ^ 8 := by
      have : 1 ≤ Y ^ 8 := Nat.one_le_pow _ _ hY1
      omega
    have h2 : (Z + 1) ^ 3 ≤ (2 ^ 15 * Y ^ 8) ^ 3 := Nat.pow_le_pow_left h1 3
    have h3 : (2 ^ 15 * Y ^ 8) ^ 3 = 2 ^ 45 * Y ^ 24 := by ring
    rw [h3] at h2
    have h4 : 1000 * (2 ^ 45 * Y ^ 24) ≤ 2 ^ 55 * Y ^ 24 := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (by norm_num)
    exact (Nat.mul_le_mul_left 1000 h2).trans h4
  exact ⟨hc.trans hfin, hv.trans hfin, fun ha vals c => (hf ha vals c).trans hfin⟩

/-- **Precision at most `m ^ 4`**: from a root `x₀` at depth `0` with `m ≥ D + 81` edges, bound
`m + 1` and precision at most `D m ²`, every call of its shape has precision at most `m ^ 4`. -/
theorem Shape.prec_le_pow_four {D : ℕ} (h₀b : x₀.bound = x₀.edges + 1) (h₀d : x₀.depth = 0)
    (h : Shape x₀ x) (hD : D + 81 ≤ x₀.edges) (hp : x₀.prec ≤ D * x₀.edges ^ 2) :
    x.prec ≤ x₀.edges ^ 4 := by
  have hbd := h.bound_add_depth_le
  rw [h₀b, h₀d] at hbd
  have hprec := h.prec_le
  set m := x₀.edges
  have hdep : x.depth * (40 * m ^ 2) ≤ (m + 1) * (40 * m ^ 2) := Nat.mul_le_mul_right _ (by omega)
  -- `D m ² + 40 m ² (m + 1) ≤ m ^ 4`.
  have h1 : D * m ^ 2 ≤ m ^ 3 := by
    calc D * m ^ 2 ≤ m * m ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = m ^ 3 := by ring
  have h2 : 81 * m ^ 3 ≤ m ^ 4 := by
    rw [pow_succ m 3, mul_comm (m ^ 3) m]
    exact Nat.mul_le_mul_right _ (by omega)
  have h3 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e : (m + 1) * (40 * m ^ 2) = 40 * m ^ 3 + 40 * m ^ 2 := by ring
  omega

end Cslib.Circuits.Frontier.FastContraction
