/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.DepthTwo

/-!
# Depth-two threshold circuits whose top gate also reads the inputs

`depthTwo` feeds only bottom-gate outputs to its top gate. Many explicit constructions,
including those for Andreev's function in [cslib-frontier#4640], use a top gate that reads the
bottom gates *and* the original input bits. `depthTwoInputs bottom args u v θ` is this model:
`G` bottom threshold gates `bottom j` read the inputs `args j`, and the top gate outputs
`θ ≤ ∑ j, u j * y_j + ∑ i, v i * x_i`, where `y_j` is the output of bottom gate `j`.

It is an ordinary weighted threshold circuit with `G + 1` gates and depth at most `2`, so lower
bounds stated for general circuits of depth at most `2` (for example those of
`AndreevLowerBound`) apply to it. `depthTwo` is the special case `v = 0`
(`eval_depthTwo_eq_eval_depthTwoInputs`).

A bottom weight vector is *sign-coherent* with respect to a block layout
`blockVar : Fin b → Fin m → Fin n` if, inside every block, its weights are all `≥ 0` or all
`≤ 0`. This is the gate class of the sign-coherent lower bound in [cslib-frontier#4640]
(milestone M3), and the bottom gates of the `5/16` circuit for Andreev's function (milestone M1)
belong to it.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.argWeight`: aggregated input weights of a gate applied
  to an input selection.
* `Cslib.Circuits.Boolean.WeightedThreshold.depthTwoInputs`: the depth-two circuit whose top gate
  reads bottom gates and inputs.
* `Cslib.Circuits.Boolean.WeightedThreshold.IsSignCoherent`: sign coherence of a weight vector
  with respect to a block layout.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.interpretation_comp_eq_ltfEval_argWeight`: a gate on
  selected inputs is the linear threshold function of its aggregated weights.
* `Cslib.Circuits.Boolean.WeightedThreshold.eval_depthTwoInputs`,
  `Cslib.Circuits.Boolean.WeightedThreshold.size_depthTwoInputs`,
  `Cslib.Circuits.Boolean.WeightedThreshold.depth_depthTwoInputs_le`: evaluation, gate count and
  depth.
* `Cslib.Circuits.Boolean.WeightedThreshold.eval_depthTwo_eq_eval_depthTwoInputs`: `depthTwo` as
  the case of zero top input weights.
* `Cslib.Circuits.Boolean.WeightedThreshold.IsSignCoherent.of_mem_zero_one`: weight vectors with
  block weights in `{0, 1}` are sign-coherent; closure under negation and scaling.

## References

* [cslib-frontier#4640](https://github.com/cslib-community/cslib-frontier/issues/4640):
  C. Reitwiessner, *Depth-Two Threshold Circuits for Andreev's Function* (preprint, 2026).
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n G : ℕ}

/-! ### Aggregated input weights of a gate on selected inputs -/

/-- The aggregated weight of input `i` in the gate `op` applied to the input selection `args`:
the sum of the weights of all argument slots reading `i`. -/
def argWeight (op : Op) (args : Fin op.arity → Fin n) (i : Fin n) : ℝ :=
  ∑ a with args a = i, op.weight a

/-- A gate with arity `n` reading the inputs in order has its own weights as aggregated
weights. -/
@[simp]
theorem argWeight_id (w : Fin n → ℝ) (θ : ℝ) :
    argWeight ⟨n, w, θ⟩ id = w := by
  funext i
  simp [argWeight, Finset.filter_eq']

/-- A threshold gate applied to selected inputs `x ∘ args` is the linear threshold function of
its aggregated weights `argWeight op args`. -/
theorem interpretation_comp_eq_ltfEval_argWeight (op : Op) (args : Fin op.arity → Fin n)
    (x : Fin n → Bool) :
    interpretation op (fun a => x (args a)) = ltfEval (argWeight op args) op.threshold x := by
  unfold interpretation ltfEval argWeight
  congr 2
  rw [← sum_fiberwise univ args fun a => op.weight a * (x (args a)).toNat]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_mul]
  exact sum_congr rfl fun a ha => by rw [(mem_filter.mp ha).2]

/-! ### The constructor -/

/-- The top gate of `depthTwoInputs`: weights `u` on the `G` bottom gates, then weights `v` on
the `n` inputs, and threshold `θ`. -/
abbrev depthTwoInputsTop (u : Fin G → ℝ) (v : Fin n → ℝ) (θ : ℝ) : Op :=
  ⟨G + n, Fin.append u v, θ⟩

/-- A depth-two weighted threshold circuit whose top gate reads both the bottom gates and the
original inputs. The `G` bottom gates `bottom j` read the inputs `args j`; the top gate has
weights `u` on the bottom gates, weights `v` on the inputs and threshold `θ`. -/
def depthTwoInputs (bottom : Fin G → Op) (args : ∀ j, Fin (bottom j).arity → Fin n)
    (u : Fin G → ℝ) (v : Fin n → ℝ) (θ : ℝ) : Circuit signature n 1 :=
  (Circuit.oneGate (σ := signature) (depthTwoInputsTop u v θ) id).comp
    ((Circuit.pi fun j => Circuit.oneGate (σ := signature) (bottom j) (args j)).append
      (Circuit.wiring signature id))

/-- Evaluating `depthTwoInputs bottom args u v θ` compares `θ` with the weighted sum of the
bottom-gate outputs and the inputs. -/
@[simp]
theorem eval_depthTwoInputs (bottom : Fin G → Op) (args : ∀ j, Fin (bottom j).arity → Fin n)
    (u : Fin G → ℝ) (v : Fin n → ℝ) (θ : ℝ) (x : Fin n → Bool) (o : Fin 1) :
    (depthTwoInputs bottom args u v θ).eval interpretation x o =
      decide (θ ≤ (∑ j, u j * (interpretation (bottom j) fun a => x (args j a)).toNat) +
        ∑ i, v i * (x i).toNat) := by
  rw [depthTwoInputs, Circuit.eval_comp, Circuit.eval_oneGate]
  simp only [interpretation, depthTwoInputsTop, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, Circuit.eval_append, Circuit.eval_pi, Circuit.eval_oneGate,
    Circuit.eval_wiring, id_eq, Function.comp_apply]

/-- The evaluation of `depthTwoInputs` with every bottom gate written as the linear threshold
function of its aggregated weights. -/
theorem eval_depthTwoInputs_eq_ltfEval (bottom : Fin G → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) (u : Fin G → ℝ) (v : Fin n → ℝ) (θ : ℝ)
    (x : Fin n → Bool) (o : Fin 1) :
    (depthTwoInputs bottom args u v θ).eval interpretation x o =
      decide (θ ≤
        (∑ j, u j * (ltfEval (argWeight (bottom j) (args j)) (bottom j).threshold x).toNat) +
          ∑ i, v i * (x i).toNat) := by
  simp only [eval_depthTwoInputs, interpretation_comp_eq_ltfEval_argWeight]

/-- `depthTwoInputs bottom args u v θ` has `G` bottom gates and one top gate. -/
@[simp]
theorem size_depthTwoInputs (bottom : Fin G → Op) (args : ∀ j, Fin (bottom j).arity → Fin n)
    (u : Fin G → ℝ) (v : Fin n → ℝ) (θ : ℝ) :
    (depthTwoInputs bottom args u v θ).size = G + 1 := by
  simp [depthTwoInputs]

/-- `depthTwoInputs bottom args u v θ` has depth at most `2`, so lower bounds for general weighted
threshold circuits of depth at most `2` apply to it. -/
theorem depth_depthTwoInputs_le (bottom : Fin G → Op) (args : ∀ j, Fin (bottom j).arity → Fin n)
    (u : Fin G → ℝ) (v : Fin n → ℝ) (θ : ℝ) :
    (depthTwoInputs bottom args u v θ).depth ≤ 2 := by
  refine (Circuit.depth_comp_le _ _).trans ?_
  have hpi := Circuit.depth_pi_le (D := 1)
    (fun j => Circuit.oneGate (σ := signature) (bottom j) (args j)) fun _ => by simp
  have happ := Circuit.depth_append_le
    (Circuit.pi fun j => Circuit.oneGate (σ := signature) (bottom j) (args j))
    (Circuit.wiring signature (id : Fin n → Fin n))
  simp only [Circuit.depth_oneGate, Circuit.depth_wiring] at happ ⊢
  omega

/-- `depthTwo top bottom args` computes the same function as `depthTwoInputs` with the top
weights of `top` on the bottom gates and zero weights on the inputs. -/
theorem eval_depthTwo_eq_eval_depthTwoInputs (top : Op) (bottom : Fin top.arity → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) :
    (depthTwo top bottom args).eval interpretation =
      (depthTwoInputs bottom args top.weight 0 top.threshold).eval interpretation := by
  funext x o
  simp only [eval_depthTwo, eval_depthTwoInputs, Pi.zero_apply, zero_mul, sum_const_zero,
    add_zero]
  rfl

/-! ### Sign-coherent weight vectors -/

/-- A weight vector `w` on the inputs is *sign-coherent* with respect to the block layout
`blockVar` if inside every block `j` its weights `w (blockVar j t)` are all `≥ 0` or all `≤ 0`.
Weights outside the blocks are unrestricted. -/
def IsSignCoherent {b m : ℕ} (blockVar : Fin b → Fin m → Fin n) (w : Fin n → ℝ) : Prop :=
  ∀ j, (∀ t, 0 ≤ w (blockVar j t)) ∨ ∀ t, w (blockVar j t) ≤ 0

namespace IsSignCoherent

variable {b m : ℕ} {blockVar : Fin b → Fin m → Fin n} {w : Fin n → ℝ}

/-- A weight vector that is nonnegative on every block is sign-coherent. -/
theorem of_nonneg (h : ∀ j t, 0 ≤ w (blockVar j t)) : IsSignCoherent blockVar w :=
  fun j => .inl (h j)

/-- A weight vector with every block weight in `{0, 1}` is sign-coherent. -/
theorem of_mem_zero_one (h : ∀ j t, w (blockVar j t) = 0 ∨ w (blockVar j t) = 1) :
    IsSignCoherent blockVar w :=
  of_nonneg fun j t => by rcases h j t with h | h <;> simp [h]

/-- The zero weight vector is sign-coherent. -/
theorem zero : IsSignCoherent blockVar (0 : Fin n → ℝ) :=
  of_nonneg fun _ _ => le_rfl

/-- Sign coherence only depends on the block weights. -/
theorem congr {w' : Fin n → ℝ} (hw : IsSignCoherent blockVar w)
    (h : ∀ j t, w (blockVar j t) = w' (blockVar j t)) : IsSignCoherent blockVar w' :=
  fun j => (hw j).imp (fun hj t => h j t ▸ hj t) fun hj t => h j t ▸ hj t

/-- Scaling a sign-coherent weight vector by any real keeps it sign-coherent. -/
theorem smul (hw : IsSignCoherent blockVar w) (c : ℝ) : IsSignCoherent blockVar (c • w) := by
  intro j
  rcases le_total 0 c with hc | hc <;> rcases hw j with hj | hj
  · exact .inl fun t => by simpa using mul_nonneg hc (hj t)
  · exact .inr fun t => by simpa using mul_nonpos_of_nonneg_of_nonpos hc (hj t)
  · exact .inr fun t => by simpa using mul_nonpos_of_nonpos_of_nonneg hc (hj t)
  · exact .inl fun t => by simpa using mul_nonneg_of_nonpos_of_nonpos hc (hj t)

/-- The negation of a sign-coherent weight vector is sign-coherent. -/
theorem neg (hw : IsSignCoherent blockVar w) : IsSignCoherent blockVar (-w) := by
  simpa using hw.smul (-1)

end IsSignCoherent

/-- Sign coherence is invariant under negation. -/
@[simp]
theorem isSignCoherent_neg_iff {b m : ℕ} {blockVar : Fin b → Fin m → Fin n} {w : Fin n → ℝ} :
    IsSignCoherent blockVar (-w) ↔ IsSignCoherent blockVar w :=
  ⟨fun h => by simpa using h.neg, IsSignCoherent.neg⟩

end Cslib.Circuits.Boolean.WeightedThreshold
