/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Andreev
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.AndreevAverage
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.AndreevLowerBound

/-! # Bridges for depth-two threshold circuit bounds on Andreev's function -/

namespace ComplexityAbstracts.AndreevThresholdBridge

/-- A single-output real-weighted threshold circuit on `n` Boolean inputs. -/
abbrev ThrCircuit (n : ℕ) :=
  Cslib.Circuits.Circuit Cslib.Circuits.Boolean.WeightedThreshold.signature n 1

/-- The Boolean function computed by output zero of a weighted threshold circuit. -/
noncomputable def evaluate {n : ℕ} (c : ThrCircuit n) (x : Fin n → Bool) : Bool :=
  c.eval Cslib.Circuits.Boolean.WeightedThreshold.interpretation x 0

/-- Total number of active wires across all gates of a weighted threshold circuit, where a wire
(original input or earlier gate) is active in `gate` when the sum of its incident edge weights in
`gate` is nonzero. -/
noncomputable def wireCount {n : ℕ} (c : ThrCircuit n) : ℕ :=
  open Classical in
  ∑ gate : Fin c.size,
    (Finset.univ.filter fun w : Cslib.Circuits.Wire n c.size =>
      (∑ a : Fin (c.program.lines gate).op.arity with (c.program.lines gate).wires a = w,
        (c.program.lines gate).op.weight a) ≠ 0).card

/-- Parity is true exactly when an odd number of input bits are true. -/
def parity (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i => x i = true).card % 2 = 1)

/-- The binary number represented by a word, with coordinate zero least significant:
the value is `∑ i, (if bits i then 1 else 0) * 2^i`. -/
def tableIndex (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The first `2^b` input bits form the truth table, in address order. -/
def tableInput {b m : ℕ} (x : Fin (2 ^ b + b * m) → Bool) : Fin (2 ^ b) → Bool :=
  fun i => x (Fin.castAdd (b * m) i)

/-- The remaining input is `b` consecutive blocks of `m` bits. Block `j`, position `t`, is
input position `2^b + m*j + t`. -/
def blockInput {b m : ℕ} (x : Fin (2 ^ b + b * m) → Bool) (j : Fin b) : Fin m → Bool :=
  fun t => x (Fin.natAdd (2 ^ b) (finProdFinEquiv (j, t)))

/-- Andreev's function reads the truth-table entry addressed by the `b` block parities. -/
def andreev (b m : ℕ) (x : Fin (2 ^ b + b * m) → Bool) : Bool :=
  tableInput x (tableIndex b fun j => parity m (blockInput x j))

/-- Simultaneous Hoeffding-counting union-bound tail over all active bottom-gate counts
`q < 2 ^ b`, where `(2 ^ b + 1) ^ ((b + 2) * q + b + 1)` bounds the number of functions in
`IsDepthTwoWithGates q` on `b` bits and `exp (-(2 α ^ 2 (q + 1) / 2 ^ b))` bounds the probability
that a fixed function in `IsDepthTwoWithGates q` correlates by more than `α * sqrt(q + 1) / 2 ^ b`
with a random truth table. -/
noncomputable def andreevSimultaneousTail (b : ℕ) (α : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (2 ^ b), ((2 ^ b + 1) ^ ((b + 2) * q + b + 1) : ℝ) *
    Real.exp (-(2 * α ^ 2 * ((q : ℝ) + 1) / (2 : ℝ) ^ b))

/-- **Exact quadratic upper bound.** For all `b, m`, Andreev's function on `n = 2^b + b*m` bits is
computed by a depth-two weighted threshold circuit with `4 * 4^b + b * m * 2^b + 1` gates
(`4 * 4^b + b * m * 2^b` bottom gates and one top gate). -/
theorem exact_upper_bound (b m : ℕ) :
    ∃ c : ThrCircuit (2 ^ b + b * m),
      c.depth ≤ 2 ∧
      c.size = 4 * 4 ^ b + b * m * 2 ^ b + 1 ∧
      wireCount c ≤ (4 * 4 ^ b + b * m * 2 ^ b) * (2 ^ b + b * m + 1) ∧
      (∀ x, evaluate c x = andreev b m x) :=
  ⟨Cslib.Circuits.Boolean.WeightedThreshold.andreevCircuit b m,
    Cslib.Circuits.Boolean.WeightedThreshold.depth_andreevCircuit_le b m,
    Cslib.Circuits.Boolean.WeightedThreshold.size_andreevCircuit b m,
    Cslib.Circuits.Boolean.WeightedThreshold.wireCount_andreevCircuit_le b m,
    fun x => congrFun (Cslib.Circuits.Boolean.WeightedThreshold.computes_andreevCircuit b m x) 0⟩

/-- **High-agreement (`1 - δ`) windowed upper bound.** Restricting the `2^b` parity-character
ladders to closed windows of half-width `B` around their expected centers gives a depth-two
weighted threshold circuit of `4 * 2^b * B + 1` gates whose disagreement fraction is bounded by
the Hoeffding tail `2^(b+1) (exp(-2 t^2 / 2^b) + exp(-2 t^2 / (b m)))` whenever `3 t + 1/2 ≤ B`. -/
theorem high_agreement_upper_bound (b m B : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hB : 3 * t + 1 / 2 ≤ (B : ℝ)) :
    ∃ c : ThrCircuit (2 ^ b + b * m),
      c.depth ≤ 2 ∧
      c.size = 4 * 2 ^ b * B + 1 ∧
      wireCount c ≤ (4 * 2 ^ b * B) * (2 ^ b + b * m + 1) ∧
      ((Finset.univ.filter fun x => evaluate c x ≠ andreev b m x).card : ℝ) ≤
        2 ^ b * (2 * 2 ^ (2 ^ b + b * m)) *
          (Real.exp (-(2 * t ^ 2 / (2 ^ b : ℝ))) + Real.exp (-(2 * t ^ 2 / (b * m : ℝ)))) :=
  ⟨Cslib.Circuits.Boolean.WeightedThreshold.andreevWindowedCircuit b m b B,
    Cslib.Circuits.Boolean.WeightedThreshold.depth_andreevWindowedCircuit_le b m b B,
    Cslib.Circuits.Boolean.WeightedThreshold.size_andreevWindowedCircuit le_rfl m B,
    Cslib.Circuits.Boolean.WeightedThreshold.wireCount_andreevWindowedCircuit_le le_rfl m B,
    Cslib.Circuits.Boolean.WeightedThreshold.card_eval_andreevWindowedCircuit_self_ne_le
      b m B 0 ht hB⟩

/-- **Correlation (`1/2 + ε`) windowed upper bound.** Summing only over the `2^r` prefix subsets
`S ⊆ {0, ..., r - 1}` for `r < b` and window half-width `B ≥ 3 t + 1/2` gives a depth-two weighted
threshold circuit of `4 * 2^r * B + 1` gates achieving correlation advantage
`1 / (2 sqrt(2 · 2^(b - r)))` minus the Hoeffding window tail. -/
theorem weak_agreement_upper_bound {b r : ℕ} (hr : r < b) (m B : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hB : 3 * t + 1 / 2 ≤ (B : ℝ)) :
    ∃ c : ThrCircuit (2 ^ b + b * m),
      c.depth ≤ 2 ∧
      c.size = 4 * 2 ^ r * B + 1 ∧
      wireCount c ≤ (4 * 2 ^ r * B) * (2 ^ b + b * m + 1) ∧
      (2 ^ (2 ^ b + b * m) : ℝ) * (1 / 2 + 1 / (2 * Real.sqrt (2 * 2 ^ (b - r)))) -
        2 ^ r * (2 * 2 ^ (2 ^ b + b * m)) *
          (Real.exp (-(2 * t ^ 2 / (2 ^ b : ℝ))) + Real.exp (-(2 * t ^ 2 / (b * m : ℝ)))) ≤
        ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ) :=
  ⟨Cslib.Circuits.Boolean.WeightedThreshold.andreevWindowedCircuit b m r B,
    Cslib.Circuits.Boolean.WeightedThreshold.depth_andreevWindowedCircuit_le b m r B,
    Cslib.Circuits.Boolean.WeightedThreshold.size_andreevWindowedCircuit hr.le m B,
    Cslib.Circuits.Boolean.WeightedThreshold.wireCount_andreevWindowedCircuit_le hr.le m B,
    Cslib.Circuits.Boolean.WeightedThreshold.card_eval_andreevWindowedCircuit_eq_andreev_ge_sqrt
      hr m B 0 ht hB⟩

/-- **Explicit scale bound for `andreevSimultaneousTail`.** At the canonical deviation scale
`α = (b + 2) * √(2 ^ b)`, the simultaneous union-bound tail over all `q < 2 ^ b` is at most
`(1 / 2) ^ ((b + 2) ^ 2 + 2)`. -/
theorem andreevSimultaneousTail_scale_le (b : ℕ) :
    andreevSimultaneousTail b (((b : ℝ) + 2) * Real.sqrt ((2 : ℝ) ^ b)) ≤
      (1 / 2 : ℝ) ^ ((b + 2) ^ 2 + 2) :=
  Cslib.Circuits.Boolean.WeightedThreshold.andreevSimultaneousTail_scale_le b

/-- **Average-case `Omega(ε² n^(3/2) / log³ n)` gate lower bound.** Any depth-two weighted threshold
circuit agreeing with `andreev b m` on at least a `1/2 + ε` fraction of inputs satisfies the
explicit quadratic-in-`ε` gate lower bound. -/
theorem gate_lower_bound {b m : ℕ} (hm : 0 < m)
    {α ε : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α)
    (htail : andreevSimultaneousTail b α ≤ ε)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ)) :
    (m : ℝ) * (((2 : ℝ) ^ b * (ε - andreevSimultaneousTail b α)) ^ 2 - α ^ 2) ≤
      4 * α ^ 2 * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) :=
  Cslib.Circuits.Boolean.WeightedThreshold.size_ge_of_card_eval_eq_andreev_ge
    hm hα htail c hd 0 hcorr

/-- **Parameter-specialized average-case `Omega(ε² n^(3/2) / log³ n)` gate lower bound.** Whenever
`3 * (b + 2) / √(2 ^ b) ≤ ε`, choosing `α = (b + 2) * √(2 ^ b)` discharges the simultaneous tail
bound and yields an unconditional quadratic-in-`ε` gate lower bound. -/
theorem gate_lower_bound_of_le_eps {b m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ)) :
    (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      12 * ((b : ℝ) + 2) ^ 2 * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) :=
  Cslib.Circuits.Boolean.WeightedThreshold.size_ge_of_card_eval_eq_andreev_ge_of_le_eps
    hm hε c hd 0 hcorr

/-- **Average-case `Omega(ε² n^(5/2) / log^(7/2) n)` wire lower bound.** Any depth-two weighted
threshold circuit agreeing with `andreev b m` on at least a `1/2 + ε` fraction of inputs satisfies
the explicit quadratic-in-`ε` active-wire lower bound. -/
theorem wire_lower_bound {b m : ℕ} (hm : 0 < m)
    {α ε : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α)
    (htail : andreevSimultaneousTail b α ≤ ε)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ)) :
    ((2 : ℝ) ^ b * (ε - andreevSimultaneousTail b α)) ^ 2 - α ^ 2 ≤
      4 * α ^ 2 * (wireCount c : ℝ) * (1 / (m : ℝ)) * Real.sqrt (1 / (m : ℝ)) :=
  Cslib.Circuits.Boolean.WeightedThreshold.wireCount_ge_of_card_eval_eq_andreev_ge
    hm hα htail c hd 0 hcorr

/-- **Parameter-specialized average-case `Omega(ε² n^(5/2) / log^(7/2) n)` wire lower bound.**
Whenever `3 * (b + 2) / √(2 ^ b) ≤ ε`, choosing `α = (b + 2) * √(2 ^ b)` discharges the
simultaneous tail bound and yields an unconditional quadratic-in-`ε` active-wire lower bound. -/
theorem wire_lower_bound_of_le_eps {b m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ)) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      12 * ((b : ℝ) + 2) ^ 2 * (wireCount c : ℝ) :=
  Cslib.Circuits.Boolean.WeightedThreshold.wireCount_ge_of_card_eval_eq_andreev_ge_of_le_eps
    hm hε c hd 0 hcorr

/-- **Worst-case gate lower bound (`ε = 1/2`).** Any depth-two weighted threshold circuit computing
`andreev b m` on all inputs has at least `Omega(n^(3/2) / log³ n)` gates. -/
theorem exact_gate_lower_bound {b m : ℕ} (hm : 0 < m)
    {α : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α)
    (htail : andreevSimultaneousTail b α ≤ 1 / 2)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcomp : ∀ x, evaluate c x = andreev b m x) :
    (m : ℝ) * (((2 : ℝ) ^ b * (1 / 2 - andreevSimultaneousTail b α)) ^ 2 - α ^ 2) ≤
      4 * α ^ 2 * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
  refine Cslib.Circuits.Boolean.WeightedThreshold.size_ge_of_computes_andreev hm hα htail c hd ?_
  intro x
  funext o
  have : o = 0 := Fin.ext (by omega)
  subst o
  exact hcomp x

/-- **Worst-case wire lower bound (`ε = 1/2`).** Any depth-two weighted threshold circuit computing
`andreev b m` on all inputs has at least `Omega(n^(5/2) / log^(7/2) n)` active wires. -/
theorem exact_wire_lower_bound {b m : ℕ} (hm : 0 < m)
    {α : ℝ} (hα : Real.sqrt ((2 : ℝ) ^ b) / 2 ≤ α)
    (htail : andreevSimultaneousTail b α ≤ 1 / 2)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcomp : ∀ x, evaluate c x = andreev b m x) :
    ((2 : ℝ) ^ b * (1 / 2 - andreevSimultaneousTail b α)) ^ 2 - α ^ 2 ≤
      4 * α ^ 2 * (wireCount c : ℝ) * (1 / (m : ℝ)) * Real.sqrt (1 / (m : ℝ)) := by
  refine Cslib.Circuits.Boolean.WeightedThreshold.wireCount_ge_of_computes_andreev
    hm hα htail c hd ?_
  intro x
  funext o
  have : o = 0 := Fin.ext (by omega)
  subst o
  exact hcomp x

end ComplexityAbstracts.AndreevThresholdBridge
