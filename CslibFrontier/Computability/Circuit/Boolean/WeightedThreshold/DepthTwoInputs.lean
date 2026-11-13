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
`≤ 0`.

This model and predicate are the API specified in [cslib-frontier#4640] for its milestones M1
(an explicit circuit) and M3 (a lower bound for sign-coherent bottom gates). That issue attributes
them to an unpublished preprint; this module does not verify the correspondence with the preprint,
and it proves no result about Andreev's function.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.inputLine`,
  `Cslib.Circuits.Boolean.WeightedThreshold.argWeight`: the input-only line of a gate applied to an
  input selection, and its aggregated input weights (`lineWeight`).
* `Cslib.Circuits.Boolean.WeightedThreshold.depthTwoInputs`: the depth-two circuit whose top gate
  reads bottom gates and inputs.
* `Cslib.Circuits.Boolean.WeightedThreshold.IsSignCoherent`: sign coherence of a weight vector
  with respect to a block layout.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.interpretation_comp_eq_ltfEval_argWeight`: a gate on
  selected inputs is the linear threshold function of its aggregated weights (a specialization of
  `line_eval_eq`).
* `Cslib.Circuits.Boolean.WeightedThreshold.eval_depthTwoInputs`,
  `Cslib.Circuits.Boolean.WeightedThreshold.size_depthTwoInputs`,
  `Cslib.Circuits.Boolean.WeightedThreshold.depth_depthTwoInputs_le`: evaluation, gate count and
  depth.
* `Cslib.Circuits.Boolean.WeightedThreshold.eval_depthTwo_eq_eval_depthTwoInputs`: `depthTwo` as
  the case of zero top input weights.
* `Cslib.Circuits.Boolean.WeightedThreshold.wireCount_depthTwoInputs_le`: at most
  `(G + 1) A + G + 1 + n` active wires for bottom arities at most `A`.
* `Cslib.Circuits.Boolean.WeightedThreshold.lines_depthTwoInputs_bottom_or_output`,
  `Cslib.Circuits.Boolean.WeightedThreshold.inputWeight_depthTwoInputs_of_ne`: every gate other
  than the output gate is a bottom gate with input weights `argWeight (bottom j) (args j)`.
* `Cslib.Circuits.Boolean.WeightedThreshold.op_lines_depthTwoInputs`,
  `Cslib.Circuits.Boolean.WeightedThreshold.abs_weight_lines_depthTwoInputs_le`,
  `Cslib.Circuits.Boolean.WeightedThreshold.abs_threshold_lines_depthTwoInputs_le`: every gate
  applies a bottom operation or the top operation, so bounds on the bottom and top weights and
  thresholds bound every weight and threshold of the circuit.
* `Cslib.Circuits.Boolean.WeightedThreshold.isSignCoherent_inputWeight_depthTwoInputs`: if every
  `bottom j` read through `args j` is sign-coherent, so are the input weights `inputWeight` of
  every gate read by the output gate.
* `Cslib.Circuits.Boolean.WeightedThreshold.IsSignCoherent.of_mem_zero_one`: weight vectors with
  block weights in `{0, 1}` are sign-coherent; closure under negation and scaling.

## References

* [cslib-frontier#4640](https://github.com/cslib-community/cslib-frontier/issues/4640), which
  specifies this API and cites an unpublished preprint by C. Reitwiessner, *Depth-Two Threshold
  Circuits for Andreev's Function* (2026); the correspondence with the preprint is not verified
  here.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n G : ℕ}

/-! ### Aggregated input weights of a gate on selected inputs -/

/-- The line of a gate `op` reading only the inputs selected by `args`. -/
def inputLine (op : Op) (args : Fin op.arity → Fin n) : Line signature n 0 :=
  ⟨op, fun a => .input (args a)⟩

/-- The aggregated weight of input `i` in the gate `op` applied to the input selection `args`:
the sum of the weights of all argument slots reading `i`. It is the `lineWeight` of the
input-only line `inputLine op args`. -/
def argWeight (op : Op) (args : Fin op.arity → Fin n) (i : Fin n) : ℝ :=
  lineWeight (inputLine op args) (.input i)

/-- A gate with arity `n` reading the inputs in order has its own weights as aggregated
weights. -/
@[simp]
theorem argWeight_id (w : Fin n → ℝ) (θ : ℝ) :
    argWeight ⟨n, w, θ⟩ id = w := by
  funext i
  simp only [argWeight, lineWeight, inputLine, Wire.input.injEq]
  rw [Finset.sum_filter]
  simp only [id_eq, sum_ite_eq', ite_eq_left_iff]
  exact fun h => (h (mem_univ i)).elim

/-- A threshold gate applied to selected inputs `x ∘ args` is the linear threshold function of
its aggregated weights `argWeight op args`; this specializes `line_eval_eq` to the input-only
line `inputLine op args`. -/
theorem interpretation_comp_eq_ltfEval_argWeight (op : Op) (args : Fin op.arity → Fin n)
    (x : Fin n → Bool) :
    interpretation op (fun a => x (args a)) = ltfEval (argWeight op args) op.threshold x := by
  have h := line_eval_eq (inputLine op args) x Fin.elim0
  simp only [univ_eq_empty, sum_empty, add_zero] at h
  exact h

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

/-! ### The bottom gates of `depthTwoInputs` as program gates -/

/-- Every gate of `depthTwoInputs bottom args u v θ` is a bottom gate `bottom j` reading the
original inputs `args j`, or it is the output gate. -/
theorem lines_depthTwoInputs_bottom_or_output (bottom : Fin G → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) (u : Fin G → ℝ) (v : Fin n → ℝ) (θ : ℝ)
    (k : Fin (depthTwoInputs bottom args u v θ).size) :
    (∃ j, (depthTwoInputs bottom args u v θ).program.lines k =
        ⟨bottom j, fun a => .input (args j a)⟩) ∨
      (depthTwoInputs bottom args u v θ).outputs 0 = .gate k := by
  set inner := (Circuit.pi fun j => Circuit.oneGate (σ := signature) (bottom j) (args j)).append
    (Circuit.wiring signature (id : Fin n → Fin n)) with hinner
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ :
      (∃ k', k = Fin.castAdd 1 k') ∨ ∃ k', k = Fin.natAdd inner.size k' :=
    Fin.addCases (motive := fun k => (∃ k', k = Fin.castAdd 1 k') ∨ ∃ k', k = Fin.natAdd _ k')
      (fun k' => .inl ⟨k', rfl⟩) (fun k' => .inr ⟨k', rfl⟩) k
  · refine .inl ?_
    obtain ⟨k, rfl⟩ : ∃ k', k = Fin.castAdd 0 k' := ⟨k, rfl⟩
    obtain ⟨j, k', f, hi, -, hk⟩ := Circuit.exists_lines_pi
      (fun j => Circuit.oneGate (σ := signature) (bottom j) (args j)) k
    refine ⟨j, ?_⟩
    obtain rfl : k' = Fin.last 0 := Fin.fin_one_eq_zero k'
    refine (Program.lines_append_castAdd _ _ _ _).trans ?_
    refine (congrArg (fun l => Line.mapWires l (Wire.castAdd 1))
      (Program.lines_append_castAdd _ _ _ k)).trans ?_
    rw [hk]
    change (((((Program.empty : Program signature n 0).gate
      (⟨bottom j, fun a => Wire.input (args j a)⟩ : Line signature n 0)).lines
        (Fin.last 0)).mapWires f).mapWires (Wire.castAdd 0)).mapWires (Wire.castAdd 1) = _
    rw [Program.lines_gate_last]
    exact congrArg (Line.mk (σ := signature) (bottom j))
      (funext fun a => by
        change Wire.castAdd 1 (Wire.castAdd 0 (f (Wire.input (args j a)))) = _
        rw [hi]
        rfl)
  · refine .inr ?_
    obtain rfl : k = Fin.last 0 := Fin.fin_one_eq_zero k
    rfl

/-- The active wire count of `depthTwoInputs` with `G` bottom gates of arity at most `A` is at most
`(G + 1) A + G + 1 + n`: each gate has at most `A` active wires, and the output gate at most
`G + 1 + n` more. -/
theorem wireCount_depthTwoInputs_le (bottom : Fin G → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) (u : Fin G → ℝ) (v : Fin n → ℝ) (θ : ℝ) {A : ℕ}
    (hA : ∀ j, (bottom j).arity ≤ A) :
    (depthTwoInputs bottom args u v θ).wireCount ≤ (G + 1) * A + (G + 1 + n) := by
  classical
  set c := depthTwoInputs bottom args u v θ
  have hsize : c.size = G + 1 := size_depthTwoInputs bottom args u v θ
  have hk (k : Fin c.size) : #(lineSupport (c.program.lines k)) ≤
      A + if c.outputs 0 = .gate k then G + 1 + n else 0 := by
    rcases lines_depthTwoInputs_bottom_or_output bottom args u v θ k with ⟨j, hj⟩ | hout
    · refine (card_lineSupport_le_arity _).trans ?_
      rw [hj]
      exact (hA j).trans (Nat.le_add_right _ _)
    · have hout' : c.outputs 0 = .gate k := hout
      simp only [hout', ↓reduceIte]
      refine (card_le_univ _).trans ?_
      rw [Fintype.card_congr (Wire.equiv n c.size), Fintype.card_sum, Fintype.card_fin,
        Fintype.card_fin, hsize]
      omega
  have hone : #({k : Fin c.size | c.outputs 0 = .gate k} : Finset _) ≤ 1 := by
    refine card_le_one.mpr fun k hk k' hk' => ?_
    simp only [mem_filter, mem_univ, true_and] at hk hk'
    exact Wire.gate.inj (hk.symm.trans hk')
  calc c.wireCount = ∑ k : Fin c.size, #(lineSupport (c.program.lines k)) := rfl
    _ ≤ ∑ k : Fin c.size, (A + if c.outputs 0 = .gate k then G + 1 + n else 0) :=
        sum_le_sum fun k _ => hk k
    _ = c.size * A + #({k : Fin c.size | c.outputs 0 = .gate k} : Finset _) * (G + 1 + n) := by
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ← sum_filter,
          sum_const, smul_eq_mul]
    _ ≤ (G + 1) * A + (G + 1 + n) := by
        have h1 : c.size * A = (G + 1) * A := by rw [hsize]
        have h2 := Nat.mul_le_mul_right (G + 1 + n) hone
        omega

/-- The input weights of a gate of `depthTwoInputs` other than the output gate are the
aggregated weights `argWeight (bottom j) (args j)` of some bottom gate `j`. -/
theorem inputWeight_depthTwoInputs_of_ne (bottom : Fin G → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) (u : Fin G → ℝ) (v : Fin n → ℝ) (θ : ℝ)
    {k : Fin (depthTwoInputs bottom args u v θ).size}
    (hk : (depthTwoInputs bottom args u v θ).outputs 0 ≠ .gate k) :
    ∃ j, inputWeight (depthTwoInputs bottom args u v θ).program k =
      argWeight (bottom j) (args j) := by
  rcases lines_depthTwoInputs_bottom_or_output bottom args u v θ k with ⟨j, hj⟩ | h
  · refine ⟨j, funext fun i => ?_⟩
    change lineWeight _ _ = _
    rw [hj]
    simp only [argWeight, lineWeight, inputLine, Wire.input.injEq]
    congr 1
  · exact (hk h).elim

/-- Every gate of `depthTwoInputs bottom args u v θ` applies a bottom operation `bottom j` or the
top operation `depthTwoInputsTop u v θ`. -/
theorem op_lines_depthTwoInputs (bottom : Fin G → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) (u : Fin G → ℝ) (v : Fin n → ℝ) (θ : ℝ)
    (k : Fin (depthTwoInputs bottom args u v θ).size) :
    (∃ j, ((depthTwoInputs bottom args u v θ).program.lines k).op = bottom j) ∨
      ((depthTwoInputs bottom args u v θ).program.lines k).op = depthTwoInputsTop u v θ := by
  rcases lines_depthTwoInputs_bottom_or_output bottom args u v θ k with ⟨j, hj⟩ | h
  · exact .inl ⟨j, by rw [hj]⟩
  · refine .inr ?_
    obtain rfl : k = Fin.natAdd _ (0 : Fin 1) := Wire.gate.inj (h.symm.trans rfl)
    refine (congrArg Line.op (Program.lines_append_natAdd _ _ _ (0 : Fin 1))).trans ?_
    rw [Line.mapWires_op]
    rfl

/-- **Weight magnitudes of `depthTwoInputs`.** If every bottom weight and every top weight on
gates and inputs has absolute value at most `W`, then so has every weight of every gate of
the circuit. -/
theorem abs_weight_lines_depthTwoInputs_le (bottom : Fin G → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) (u : Fin G → ℝ) (v : Fin n → ℝ) (θ : ℝ) {W : ℝ}
    (hbottom : ∀ j a, |(bottom j).weight a| ≤ W) (hu : ∀ j, |u j| ≤ W) (hv : ∀ i, |v i| ≤ W)
    (k : Fin (depthTwoInputs bottom args u v θ).size)
    (a : Fin ((depthTwoInputs bottom args u v θ).program.lines k).op.arity) :
    |((depthTwoInputs bottom args u v θ).program.lines k).op.weight a| ≤ W := by
  revert a
  rcases op_lines_depthTwoInputs bottom args u v θ k with ⟨j, h⟩ | h <;> rw [h]
  · exact hbottom j
  · intro a
    refine Fin.addCases (fun j => ?_) (fun i => ?_) a
    · simpa only [Fin.append_left] using hu j
    · simpa only [Fin.append_right] using hv i

/-- **Threshold magnitudes of `depthTwoInputs`.** If every bottom threshold and the top threshold
have absolute value at most `W`, then so has the threshold of every gate of the circuit. -/
theorem abs_threshold_lines_depthTwoInputs_le (bottom : Fin G → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) (u : Fin G → ℝ) (v : Fin n → ℝ) (θ : ℝ) {W : ℝ}
    (hbottom : ∀ j, |(bottom j).threshold| ≤ W) (hθ : |θ| ≤ W)
    (k : Fin (depthTwoInputs bottom args u v θ).size) :
    |((depthTwoInputs bottom args u v θ).program.lines k).op.threshold| ≤ W := by
  rcases op_lines_depthTwoInputs bottom args u v θ k with ⟨j, h⟩ | h <;> rw [h]
  · exact hbottom j
  · exact hθ

/-- **Sign coherence of the bottom gates.** If every bottom gate `bottom j`, read through
`args j`, is sign-coherent, then every gate read by an output gate of
`depthTwoInputs bottom args u v θ` has sign-coherent input weights. This is the hypothesis form of
lower bounds stated over the gate support of the output gate. -/
theorem isSignCoherent_inputWeight_depthTwoInputs {b m : ℕ} {blockVar : Fin b → Fin m → Fin n}
    (bottom : Fin G → Op) (args : ∀ j, Fin (bottom j).arity → Fin n) (u : Fin G → ℝ)
    (v : Fin n → ℝ) (θ : ℝ) (h : ∀ j, IsSignCoherent blockVar (argWeight (bottom j) (args j)))
    {o : Fin 1} {top : Fin (depthTwoInputs bottom args u v θ).size}
    (htop : (depthTwoInputs bottom args u v θ).outputs o = .gate top)
    {k : Fin (depthTwoInputs bottom args u v θ).size}
    (hk : k ∈ gateSupport (depthTwoInputs bottom args u v θ).program top) :
    IsSignCoherent blockVar (inputWeight (depthTwoInputs bottom args u v θ).program k) := by
  obtain rfl : o = 0 := Fin.fin_one_eq_zero o
  have hne : (depthTwoInputs bottom args u v θ).outputs 0 ≠ .gate k := by
    rw [htop]
    intro hkt
    cases hkt
    exact (mem_gateSupport _ _ _).mp hk (gateWeight_eq_zero_of_le _ _ _ le_rfl)
  obtain ⟨j, hj⟩ := inputWeight_depthTwoInputs_of_ne bottom args u v θ hne
  exact hj ▸ h j

end Cslib.Circuits.Boolean.WeightedThreshold
