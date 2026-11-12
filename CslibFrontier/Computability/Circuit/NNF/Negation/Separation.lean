/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.NNF.Negation.LowerBound
public import CslibFrontier.Computability.Circuit.NNF.Negation.UpperBound

/-!
# d-DNNF is not polynomially closed under negation, given expanders

**[ArenasBroadrickLiewVanDenBroeck2026, Theorem 1.1]** states that for infinitely many `n` there
is `f : {0,1}ⁿ → {0,1}` computed by a d-DNNF of size `O(n)` such that every DNNF computing `¬f`
has size `2^Ω(n)`. Its function is `f_G` for a cubic graph `G` with a proper `3`-edge-colouring
that is a balanced-cut edge expander (`Cslib.CubicEdgeColoring.someButNotAllColors`).

This module proves both bounds for every such graph, with explicit constants
(`CubicEdgeColoring.ddnnf_negation_separation`): on `n ≥ 2` vertices, `f_G` has a d-DNNF with at
most `150 n + 50` nodes (Proposition 5.1), and every DNNF for `¬f_G`, deterministic or not, has at
least `(48/47)^(γ n / 126)` nodes (Theorem 5.3, through Theorem 3.1). Theorem 1.1 then follows
for every family of such expanders on unboundedly many vertices
(`Cslib.Circuits.NNF.exponential_separation_of_expanders`).

**Remaining gap.** The existence of such a family is
[ArenasBroadrickLiewVanDenBroeck2026, Proposition 5.2] (explicit simple `3`-regular bipartite
edge expanders, cited there as \[KMPS24, Alo21\], with König's edge colouring). It is a
hypothesis here, not proved.
Nothing about the function `f_G`, its d-DNNF or the lower bound is assumed.

## Main results

* `Cslib.CubicEdgeColoring.ddnnf_negation_separation`: both bounds for one expander.
* `Cslib.Circuits.NNF.exponential_separation_of_expanders`: Theorem 1.1 from an expander family.

## References

* [M. Arenas, O. Broadrick, V. Liew, G. Van den Broeck, *d-DNNF is not polynomially closed under
  negation*][ArenasBroadrickLiewVanDenBroeck2026]
-/

@[expose] public section

namespace Cslib

namespace CubicEdgeColoring

variable {V : Type*} [Fintype V] [DecidableEq V] (M : CubicEdgeColoring V)

/-- **The separation for one expander.** If a cubic graph with a proper `3`-edge-colouring on
`n ≥ 2` vertices is a balanced-cut `γ`-edge expander, then `f_G` has a d-DNNF with at most
`150 n + 50` nodes, while every DNNF computing `¬f_G` has at least `(48/47)^(γ n / 126)`
nodes. -/
theorem ddnnf_negation_separation {γ : ℝ} (hG : IsBalancedCutExpander M.toSimpleGraph γ)
    (hn : 2 ≤ Fintype.card V) :
    (∃ (N : Type) (_ : Fintype N) (D : Circuits.NNF V N), D.IsDecomposable ∧
      D.IsDeterministic ∧ (∀ x, D.toFun x = M.someButNotAllColors x) ∧
        D.size ≤ 150 * Fintype.card V + 50) ∧
    ∀ {N : Type*} [Fintype N] (D : Circuits.NNF V N), D.IsDecomposable →
      (∀ x, D.toFun x = !M.someButNotAllColors x) →
        (48 / 47 : ℝ) ^ (γ * Fintype.card V / 126) ≤ D.size :=
  ⟨M.exists_dDNNF, fun _ hD hf => M.le_size_of_isDecomposable hG hn hD hf⟩

end CubicEdgeColoring

namespace Circuits.NNF

/-- **[ArenasBroadrickLiewVanDenBroeck2026, Theorem 1.1], from an expander family.** Suppose that
for some `γ` there are cubic graphs with proper `3`-edge-colourings on unboundedly many vertex
counts that are balanced-cut `γ`-edge expanders (Proposition 5.2 of the paper, not proved here).
Then for infinitely many `n` there is `f : (Fin n → Bool) → Bool` with a d-DNNF of at most
`150 n + 50` nodes such that every DNNF computing `¬f` has at least `(48/47)^(γ n / 126)` nodes. -/
theorem exponential_separation_of_expanders {γ : ℝ}
    (hfam : ∀ m, ∃ n ≥ m, ∃ M : CubicEdgeColoring (Fin n),
      IsBalancedCutExpander M.toSimpleGraph γ) (m : ℕ) :
    ∃ n ≥ m, ∃ f : (Fin n → Bool) → Bool,
      (∃ (N : Type) (_ : Fintype N) (D : NNF (Fin n) N), D.IsDecomposable ∧ D.IsDeterministic ∧
        (∀ x, D.toFun x = f x) ∧ D.size ≤ 150 * n + 50) ∧
      ∀ {N : Type*} [Fintype N] (D : NNF (Fin n) N), D.IsDecomposable → (∀ x, D.toFun x = !f x) →
        (48 / 47 : ℝ) ^ (γ * n / 126) ≤ D.size := by
  obtain ⟨n, hn, M, hM⟩ := hfam (max m 2)
  have h2 : 2 ≤ Fintype.card (Fin n) := by simp only [Fintype.card_fin]; omega
  obtain ⟨hup, hlow⟩ := M.ddnnf_negation_separation hM h2
  simp only [Fintype.card_fin] at hup hlow
  exact ⟨n, le_of_max_le_left hn, M.someButNotAllColors, hup, hlow⟩

end Circuits.NNF

end Cslib
