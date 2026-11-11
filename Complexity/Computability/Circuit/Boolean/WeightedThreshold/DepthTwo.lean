/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.LTF
public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Cut
public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Menus
public import Complexity.Computability.Circuit.CompositionLines
public import Complexity.Computability.Circuit.Simulation
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Depth-two weighted threshold circuits and wire counts

This module defines the canonical depth-two weighted threshold circuit constructor
`WeightedThreshold.depthTwo` (`THR ∘ THR`) and aggregated wire-count measures for weighted
threshold programs and circuits.

For any program `p : Program signature n g`, `lineSupport (p.lines gate)` is the set of wires
(original inputs and earlier gates) with nonzero aggregated coefficient in `gate`, decomposing
disjointly into `inputSupport p gate` and `gateSupport p gate`. The total active wire count
`wireCount p` is the sum of `#(lineSupport (p.lines gate))` over all gates, and `inputWireCount p`
is the sum of `#(inputSupport p gate)` over all gates. Both are bounded by the syntactic slot
count `p.cost Op.arity`.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.lineSupport`: active wires of a weighted threshold gate.
* `Cslib.Circuits.Boolean.WeightedThreshold.inputWireCount`,
  `Cslib.Circuits.Boolean.WeightedThreshold.wireCount`,
  `Cslib.Circuits.Circuit.inputWireCount`,
  `Cslib.Circuits.Circuit.wireCount`: aggregated direct-input and total wire counts.
* `Cslib.Circuits.Boolean.WeightedThreshold.depthTwo`: depth-two weighted threshold circuit built
  from `top.arity` bottom threshold gates and a single output threshold gate `top`.
* `Cslib.Circuits.Boolean.WeightedThreshold.altLinear`: alternating linear function
  `(u.negOnePow : ℤ) * u` used in depth-two threshold telescoping constructions.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.card_lineSupport_eq`,
  `Cslib.Circuits.Boolean.WeightedThreshold.wireCount_eq_inputWireCount_add`: active wires split
  into direct-input wires and internal gate-to-gate wires.
* `Cslib.Circuits.Boolean.WeightedThreshold.card_lineSupport_le_arity`,
  `Cslib.Circuits.Boolean.WeightedThreshold.wireCount_le_cost_arity`: active wire count is at most
  the syntactic argument-slot count `p.cost Op.arity`.
* `Cslib.Circuits.Boolean.WeightedThreshold.eval_depthTwo`,
  `Cslib.Circuits.Boolean.WeightedThreshold.size_depthTwo`,
  `Cslib.Circuits.Boolean.WeightedThreshold.depth_depthTwo_le`,
  `Cslib.Circuits.Boolean.WeightedThreshold.wireCount_depthTwo_le`: evaluation, gate count, depth,
  and wire count of `depthTwo`.
* `Cslib.Circuits.Boolean.WeightedThreshold.lines_depthTwo_bottom_or_top`: every gate of `depthTwo`
  is a bottom gate reading only original inputs or the top gate reading only gates.
* `Cslib.Circuits.Boolean.WeightedThreshold.altLinear_add_add_altLinear_sub`,
  `Cslib.Circuits.Boolean.WeightedThreshold.negOnePow_mul_altLinear_add_sub_altLinear`,
  `Cslib.Circuits.Boolean.WeightedThreshold.sum_sub_mul_decide_le`: alternating linear polarization
  and shift identities, and integer interval telescoping into threshold indicators.

## References

* [D. M. Kane and R. Williams, *Super-Linear Gate and Super-Quadratic Wire Lower Bounds for
  Depth-Two and Depth-Three Threshold Circuits*][KaneWilliams2016]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n g m : ℕ}

/-! ### Active wire supports and wire counts -/

/-- The wires with nonzero aggregated coefficient in `line`. -/
noncomputable def lineSupport (line : Line signature n g) : Finset (Wire n g) :=
  univ.filter fun w => lineWeight line w ≠ 0

/-- A wire belongs to `lineSupport line` if and only if its aggregated weight `lineWeight line w`
is nonzero. -/
@[simp]
theorem mem_lineSupport (line : Line signature n g) (w : Wire n g) :
    w ∈ lineSupport line ↔ lineWeight line w ≠ 0 := by
  classical
  simp [lineSupport]

/-- The number of active wires of a line is at most the syntactic arity of its operation. -/
theorem card_lineSupport_le_arity (line : Line signature n g) :
    #(lineSupport line) ≤ line.op.arity := by
  classical
  have hsub : lineSupport line ⊆ univ.image line.wires := by
    intro w hw
    rw [mem_lineSupport] at hw
    obtain ⟨a, ha, _⟩ := exists_ne_zero_of_sum_ne_zero hw
    exact mem_image.mpr ⟨a, mem_univ a, (mem_filter.mp ha).2⟩
  exact (card_le_card hsub).trans (card_image_le.trans (by simp))

/-- The active wires of a program gate decompose disjointly into its active original inputs and its
active predecessor gates. -/
theorem card_lineSupport_eq (p : Program signature n g) (gate : Fin g) :
    #(lineSupport (p.lines gate)) = #(inputSupport p gate) + #(gateSupport p gate) := by
  classical
  simp only [lineSupport, inputSupport, gateSupport, card_filter]
  rw [← (Wire.equiv n g).symm.sum_comp
    (fun w => if lineWeight (p.lines gate) w ≠ 0 then 1 else 0), Fintype.sum_sum_type]
  rfl

/-- Total number of active direct-input wires across all gates of a weighted threshold program. -/
noncomputable def inputWireCount (p : Program signature n g) : ℕ :=
  ∑ gate : Fin g, #(inputSupport p gate)

/-- Total number of active wires (both direct-input and gate-to-gate) across all gates of a
weighted threshold program. -/
noncomputable def wireCount (p : Program signature n g) : ℕ :=
  ∑ gate : Fin g, #(lineSupport (p.lines gate))

/-- The total active wire count of a program splits into its direct-input wire count and its
internal gate-to-gate wire count. -/
theorem wireCount_eq_inputWireCount_add (p : Program signature n g) :
    wireCount p = inputWireCount p + ∑ gate : Fin g, #(gateSupport p gate) := by
  simp only [wireCount, inputWireCount, card_lineSupport_eq, sum_add_distrib]

/-- The direct-input wire count of a program is at most its total active wire count. -/
theorem inputWireCount_le_wireCount (p : Program signature n g) :
    inputWireCount p ≤ wireCount p := by
  rw [wireCount_eq_inputWireCount_add]
  exact Nat.le_add_right _ _

/-- The active wire count of a program is at most its syntactic argument-slot count
`p.cost Op.arity`. -/
theorem wireCount_le_cost_arity (p : Program signature n g) :
    wireCount p ≤ p.cost Op.arity := by
  rw [wireCount, p.cost_eq_sum]
  exact sum_le_sum fun gate _ => card_lineSupport_le_arity (p.lines gate)

end Cslib.Circuits.Boolean.WeightedThreshold

namespace Cslib.Circuits.Circuit

open Boolean.WeightedThreshold

variable {n m : ℕ}

/-- Total number of active direct-input wires across all gates of a weighted threshold circuit. -/
noncomputable abbrev inputWireCount (c : Circuit signature n m) : ℕ :=
  Boolean.WeightedThreshold.inputWireCount c.program

/-- Total number of active wires across all gates of a weighted threshold circuit. -/
noncomputable abbrev wireCount (c : Circuit signature n m) : ℕ :=
  Boolean.WeightedThreshold.wireCount c.program

/-- The direct-input wire count of a circuit is at most its total active wire count. -/
theorem inputWireCount_le_wireCount (c : Circuit signature n m) :
    c.inputWireCount ≤ c.wireCount :=
  Boolean.WeightedThreshold.inputWireCount_le_wireCount c.program

/-- The active wire count of a circuit is at most its syntactic argument-slot count
`c.program.cost Op.arity`. -/
theorem wireCount_le_cost_arity (c : Circuit signature n m) :
    c.wireCount ≤ c.program.cost Op.arity :=
  Boolean.WeightedThreshold.wireCount_le_cost_arity c.program

end Cslib.Circuits.Circuit

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n : ℕ}

/-! ### Depth-two weighted threshold circuits (`THR ∘ THR`) -/

/-- A depth-two weighted threshold circuit (`THR ∘ THR`) with `top.arity` bottom threshold gates
`bottom j` on input selections `args j`, feeding into the single output threshold gate `top`. -/
def depthTwo (top : Op) (bottom : Fin top.arity → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) : Circuit signature n 1 :=
  (Circuit.oneGate (σ := signature) top id).comp
    (Circuit.pi fun j => Circuit.oneGate (σ := signature) (bottom j) (args j))

/-- Evaluating `depthTwo top bottom args` applies each bottom threshold gate `bottom j` to its
selected inputs `x ∘ args j` and feeds their Boolean outputs into `top`. -/
@[simp]
theorem eval_depthTwo (top : Op) (bottom : Fin top.arity → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) (x : Fin n → Bool) (o : Fin 1) :
    (depthTwo top bottom args).eval interpretation x o =
      interpretation top fun j => interpretation (bottom j) fun a => x (args j a) := by
  simp [depthTwo]

/-- A depth-two circuit `depthTwo top bottom args` has `top.arity` bottom gates and one top gate,
for `top.arity + 1` gates in total. -/
@[simp]
theorem size_depthTwo (top : Op) (bottom : Fin top.arity → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) :
    (depthTwo top bottom args).size = top.arity + 1 := by
  simp [depthTwo]

/-- A depth-two circuit `depthTwo top bottom args` has depth at most `2`. -/
theorem depth_depthTwo_le (top : Op) (bottom : Fin top.arity → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) :
    (depthTwo top bottom args).depth ≤ 2 := by
  refine (Circuit.depth_comp_le _ _).trans ?_
  have := Circuit.depth_pi_le (D := 1)
    (fun j => Circuit.oneGate (σ := signature) (bottom j) (args j)) fun _ => by simp
  simp only [Circuit.depth_oneGate]
  omega

/-- The syntactic argument-slot count of `depthTwo top bottom args` is the sum of the bottom-gate
arities plus `top.arity`. -/
theorem cost_arity_depthTwo (top : Op) (bottom : Fin top.arity → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) :
    (depthTwo top bottom args).program.cost Op.arity =
      (∑ j, (bottom j).arity) + top.arity := by
  rw [depthTwo, Circuit.cost_program_comp, Circuit.cost_program_pi, Circuit.cost_program_oneGate]
  simp_rw [Circuit.cost_program_oneGate]

/-- The active wire count of `depthTwo top bottom args` is at most the sum of the bottom-gate
arities plus `top.arity`. -/
theorem wireCount_depthTwo_le (top : Op) (bottom : Fin top.arity → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) :
    (depthTwo top bottom args).wireCount ≤ (∑ j, (bottom j).arity) + top.arity :=
  (depthTwo top bottom args).wireCount_le_cost_arity.trans_eq
    (cost_arity_depthTwo top bottom args)

/-- Every gate of `depthTwo top bottom args` is either a bottom gate `bottom j`, reading the
original inputs `args j`, or the top gate `top`, reading only gates. -/
theorem lines_depthTwo_bottom_or_top (top : Op) (bottom : Fin top.arity → Op)
    (args : ∀ j, Fin (bottom j).arity → Fin n) (k : Fin (depthTwo top bottom args).size) :
    (∃ j, (depthTwo top bottom args).program.lines k = ⟨bottom j, fun a => .input (args j a)⟩) ∨
      ∃ ws : Fin top.arity → Fin (depthTwo top bottom args).size,
        (depthTwo top bottom args).program.lines k = ⟨top, fun a => .gate (ws a)⟩ := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ :
      (∃ k', k = Fin.castAdd 1 k') ∨ ∃ k', k = Fin.natAdd
        (Circuit.pi fun j => Circuit.oneGate (σ := signature) (bottom j) (args j)).size k' :=
    Fin.addCases (motive := fun k => (∃ k', k = Fin.castAdd 1 k') ∨ ∃ k', k = Fin.natAdd _ k')
      (fun k' => .inl ⟨k', rfl⟩) (fun k' => .inr ⟨k', rfl⟩) k
  · obtain ⟨j, k', f, hi, -, hk⟩ := Circuit.exists_lines_pi _ k
    refine .inl ⟨j, ?_⟩
    obtain rfl : k' = Fin.last 0 := Fin.fin_one_eq_zero k'
    refine (Program.lines_append_castAdd _ _ _ k).trans ?_
    rw [hk]
    change ((((Program.empty : Program signature n 0).gate
      (⟨bottom j, fun a => Wire.input (args j a)⟩ : Line signature n 0)).lines
        (Fin.last 0)).mapWires f).mapWires (Wire.castAdd 1) = _
    rw [Program.lines_gate_last]
    exact congrArg (Line.mk (σ := signature) (bottom j))
      (funext fun a => congrArg (Wire.castAdd 1) (hi (args j a)))
  · obtain rfl : k = Fin.last 0 := Fin.fin_one_eq_zero k
    choose ws hws using Circuit.outputs_pi_eq_gate
      (fun j => Circuit.oneGate (σ := signature) (bottom j) (args j)) (fun _ => ⟨Fin.last 0, rfl⟩)
    refine .inr ⟨fun a => Fin.castAdd 1 (ws a), ?_⟩
    refine (Program.lines_append_natAdd _ _ _ (Fin.last 0)).trans ?_
    change (((Program.empty : Program signature top.arity 0).gate
      (⟨top, fun a => Wire.input a⟩ : Line signature top.arity 0)).lines (Fin.last 0)).mapWires
        (Program.appendedWire _) = _
    rw [Program.lines_gate_last]
    simp only [Line.mapWires, Function.comp_def, Wire.Renaming.castSucc_apply, Wire.castSucc_input,
      Program.appendedWire_input, hws, Wire.castAdd_gate]
    rfl

/-! ### Alternating linear function and integer interval telescoping -/

/-- The alternating linear function `φ(u) = (-1) ^ u * u`, defined via `Int.negOnePow`. -/
def altLinear (u : ℤ) : ℤ :=
  (u.negOnePow : ℤ) * u

/-- `Int.negOnePow` sends a finite sum of integers to the product of their powers of `-1`. -/
theorem negOnePow_sum {α : Type*} (s : Finset α) (f : α → ℤ) :
    ((∑ x ∈ s, f x).negOnePow : ℤ) = ∏ x ∈ s, ((f x).negOnePow : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, Int.negOnePow_add, Units.val_mul, ih, prod_insert ha]

/-- **Alternating linear polarization identity**: for all integers `X` and `t`,
`φ(X + t) + φ(X - t) = 2 * (-1) ^ X * X * (-1) ^ t`. -/
theorem altLinear_add_add_altLinear_sub (X t : ℤ) :
    altLinear (X + t) + altLinear (X - t) = 2 * (X.negOnePow : ℤ) * X * (t.negOnePow : ℤ) := by
  simp only [altLinear, Int.negOnePow_add, Int.negOnePow_sub, Units.val_mul]
  ring

/-- **Alternating linear shift identity**: for all integers `X` and `t`,
`(-1) ^ X * φ(X + t) - φ(t) = X * (-1) ^ t`. For even `X` this is
`φ(X + t) - φ(t) = X * (-1) ^ t`. -/
theorem negOnePow_mul_altLinear_add_sub_altLinear (X t : ℤ) :
    (X.negOnePow : ℤ) * altLinear (X + t) - altLinear t = X * (t.negOnePow : ℤ) := by
  have hX : (X.negOnePow : ℤ) * X.negOnePow = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  simp only [altLinear, Int.negOnePow_add, Units.val_mul]
  have hassoc : (X.negOnePow : ℤ) * ((X.negOnePow : ℤ) * t.negOnePow * (X + t)) =
      ((X.negOnePow : ℤ) * X.negOnePow) * (t.negOnePow * (X + t)) := by ring
  rw [hassoc, hX]
  ring

/-- The discrete derivative of `altLinear` at `u` is `(-1) ^ (u + 1) * (2 * u + 1)`. -/
theorem altLinear_add_one_sub (u : ℤ) :
    altLinear (u + 1) - altLinear u = ((u + 1).negOnePow : ℤ) * (2 * u + 1) := by
  simp only [altLinear, Int.negOnePow_succ, Units.val_neg]
  ring

/-- **Integer interval telescoping**: any function `f : ℤ → ℤ` on an integer `u ∈ [ℓ, ℓ + L]`
equals `f ℓ` plus the sum of its step differences weighted by threshold indicators
`decide (ℓ + k + 1 ≤ u)`. -/
theorem sum_sub_mul_decide_le (f : ℤ → ℤ) {ℓ u : ℤ} {L : ℕ}
    (hlo : ℓ ≤ u) (hhi : u ≤ ℓ + L) :
    f ℓ + ∑ k : Fin L, (f (ℓ + k + 1) - f (ℓ + k)) * (decide (ℓ + k + 1 ≤ u)).toNat = f u := by
  induction L generalizing u with
  | zero =>
    have hu : u = ℓ := by omega
    simp [hu]
  | succ L ih =>
    rw [Fin.sum_univ_castSucc]
    by_cases hle : u ≤ ℓ + L
    · have hlast : ¬ (ℓ + (Fin.last L : ℕ) + 1 ≤ u) := by
        simp only [Fin.val_last]
        omega
      simp only [Fin.val_castSucc, hlast, decide_false, Bool.toNat_false, Nat.cast_zero, mul_zero,
        add_zero]
      exact ih hlo hle
    · push_cast at hhi
      have hu : u = ℓ + L + 1 := by omega
      have hlast : ℓ + L + 1 ≤ u := by omega
      have hcongr :
          ∑ k : Fin L, (f (ℓ + (k.castSucc : ℕ) + 1) - f (ℓ + (k.castSucc : ℕ))) *
              ((decide (ℓ + (k.castSucc : ℕ) + 1 ≤ u)).toNat : ℤ) =
            ∑ k : Fin L, (f (ℓ + (k : ℕ) + 1) - f (ℓ + (k : ℕ))) *
              ((decide (ℓ + (k : ℕ) + 1 ≤ ℓ + L)).toNat : ℤ) := by
        refine sum_congr rfl fun k _ => ?_
        have hk1 : ℓ + (k : ℕ) + 1 ≤ u := by omega
        have hk2 : ℓ + (k : ℕ) + 1 ≤ ℓ + L := by omega
        simp [hk1, hk2]
      rw [hcongr, ← add_assoc, ih (u := ℓ + L) (by omega) le_rfl, Fin.val_last]
      simp only [hlast, decide_true, Bool.toNat_true, Nat.cast_one, mul_one]
      rw [hu]
      ring

/-- Twice the sum of subset cardinalities over `Finset (Fin b)` is `b * 2 ^ b`. -/
theorem two_mul_sum_card_finset (b : ℕ) :
    2 * ∑ S : Finset (Fin b), #S = b * 2 ^ b := by
  let e : Finset (Fin b) ≃ Finset (Fin b) := ⟨compl, compl, compl_compl, compl_compl⟩
  have hcompl : (∑ S : Finset (Fin b), #Sᶜ) = ∑ S : Finset (Fin b), #S :=
    e.sum_comp fun S : Finset (Fin b) => #S
  calc 2 * ∑ S : Finset (Fin b), #S
      = (∑ S : Finset (Fin b), #S) + ∑ S : Finset (Fin b), #Sᶜ := by rw [two_mul, hcompl]
    _ = ∑ S : Finset (Fin b), (#S + #Sᶜ) := sum_add_distrib.symm
    _ = ∑ _S : Finset (Fin b), b := sum_congr rfl fun S _ => by simp [card_add_card_compl]
    _ = b * 2 ^ b := by simp [mul_comm]

/-! ### Linear threshold functions on general finite domains and depth-one gate decomposition -/

/-- The active coordinate support of `inputWeight p gate` is `inputSupport p gate`. -/
@[simp]
theorem ltfSupport_inputWeight_eq_inputSupport {n g : ℕ} (p : Program signature n g)
    (gate : Fin g) :
    ltfSupport (inputWeight p gate) = inputSupport p gate :=
  rfl

/-- Any gate of depth at most `1` in a weighted threshold program has zero aggregated weight from
every gate `k : Fin g`. -/
theorem gateWeight_eq_zero_of_depths_le_one {n g : ℕ} (p : Program signature n g) {gate : Fin g}
    (hd : p.depths gate ≤ 1) (k : Fin g) :
    gateWeight p gate k = 0 := by
  dsimp only [gateWeight, lineWeight]
  refine sum_eq_zero fun i hi => ?_
  exfalso
  have hw : (p.lines gate).wires i = Wire.gate k := (mem_filter.mp hi).2
  have hlt := p.wireDepths_lines_lt gate i
  rw [hw] at hlt
  change p.depths k < p.depths gate at hlt
  have hpos := p.depths_pos k
  omega

/-- Any gate of depth at most `1` in a weighted threshold program has empty `gateSupport`. -/
theorem gateSupport_eq_empty_of_depths_le_one {n g : ℕ} (p : Program signature n g) {gate : Fin g}
    (hd : p.depths gate ≤ 1) :
    gateSupport p gate = ∅ := by
  ext k
  simp [gateSupport, gateWeight_eq_zero_of_depths_le_one p hd k]

/-- Any gate of depth at most `1` in a weighted threshold program evaluates as the linear threshold
function `ltfEval (inputWeight p gate) (p.lines gate).op.threshold` on the primary inputs `x`. -/
theorem eval_eq_ltfEval_inputWeight_of_depths_le_one {n g : ℕ} (p : Program signature n g)
    (x : Fin n → Bool) {gate : Fin g} (hd : p.depths gate ≤ 1) :
    p.eval interpretation x gate =
      ltfEval (inputWeight p gate) (p.lines gate).op.threshold x := by
  rw [eval_gate_eq, ltfEval]
  have hgate_zero :
      (∑ k : Fin g, gateWeight p gate k * (p.eval interpretation x k).toNat) = 0 :=
    sum_eq_zero fun k _ => by simp [gateWeight_eq_zero_of_depths_le_one p hd k]
  rw [hgate_zero, add_zero]

end Cslib.Circuits.Boolean.WeightedThreshold
