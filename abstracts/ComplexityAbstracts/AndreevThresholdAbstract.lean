/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.AndreevThresholdBridge

/-! # Depth-two threshold circuits for Andreev's function: upper and lower bounds

Andreev's function on `n = 2 ^ b + b * m` bits takes a `2 ^ b`-bit truth table and `b` consecutive
`m`-bit blocks, computes the parity of each block, and outputs the truth-table entry addressed by
those `b` parities. In the balanced regime `N = 2 ^ b = b * m` (`n = 2 N`), Kane and Williams
proved an `O(n ^ 3 / log n)` depth-two linear threshold (`THR ∘ THR`) gate upper bound and
average-case `Omega(ε ^ 3 n ^ (3 / 2) / log ^ 3 n)` gate and
`Omega(ε ^ 3 n ^ (5 / 2) / log ^ (7 / 2) n)` wire lower bounds for circuits agreeing with
Andreev's function on a `1 / 2 + ε` fraction of inputs.

This development formalizes four improvements over the bounds of Kane and Williams:

**Exact quadratic upper bound (`exact_upper_bound`).** By polarizing each Fourier parity term
`2 (-1)^(2^b) X_S (-1)^(t_S) = φ(X_S + t_S) + φ(X_S - t_S)` (where `(-1)^(2^b) = 1` for `b > 0`)
via the alternating linear function `φ(u) = (-1)^u u` and telescoping `φ` into threshold indicators
over its exact integer range, Andreev's function is computed exactly by a depth-two threshold
circuit with `4 * 4 ^ b + b * m * 2 ^ b` bottom gates and one top gate (`(5 / 4) n ^ 2 + 1` gates at
`2 ^ b = b * m`), bottom weights in `{-2, -1, 0, 1, 2}`, and odd integer top weights of absolute
value below `2 n`.

**Windowed high-agreement upper bound (`high_agreement_upper_bound`).** Truncating each unary
threshold ladder to a window of half-width `B ≥ 3 t + 1 / 2` around its expected center reduces
the circuit size to `4 * 2 ^ b * B + 1` while bounding the disagreement fraction by the Hoeffding
tail `2 ^ (b + 1) (exp (-2 t ^ 2 / 2 ^ b) + exp (-2 t ^ 2 / (b m)))`, giving
`O(n ^ (3 / 2) sqrt(log (n / δ)))` gates and `O(n ^ (5 / 2) sqrt(log (n / δ)))` wires for
agreement `1 - δ`.

**Windowed `(1 / 2 + ε)`-correlation upper bound (`weak_agreement_upper_bound`).** Summing only
over the `2 ^ r` prefix subsets `S ⊆ {0, ..., r - 1}` (`r < b`) gives the subcube majority vote
over `2 ^ (b - r)` truth-table entries, whose exact correlation advantage over `1 / 2` is at least
`1 / (2 sqrt(2 · 2 ^ (b - r)))`, while the union bound over all `2 ^ r` prefix subsets contributes
normalized window error `2 ^ (r + 1) (exp (-2 t ^ 2 / 2 ^ b) + exp (-2 t ^ 2 / (b m)))`. Choosing
`2 ^ r = Theta(ε ^ 2 n)` and `B = Theta(sqrt(n log n))` in the balanced regime (`C / sqrt(n) ≤ ε ≤
1 / 2 - c`) yields `O(ε ^ 2 n ^ (3 / 2) sqrt(log n))` gates and `O(ε ^ 2 n ^ (5 / 2) sqrt(log n))`
wires.

**Improved gate and wire lower bounds.** A surviving gate retains a weight vector from the
original circuit; only its threshold changes with the fixed inputs. Counting threshold shifts of
these fixed vectors, then averaging the square root of the survivor count by Cauchy–Schwarz,
gives the resource-sensitive bounds `gate_lower_bound` and `wire_lower_bound`. Splitting at
`2 ^ (3 * b)` removes the logarithm of the circuit resource. For `m ≤ 2 ^ b` and
`3 (b + 2) / sqrt(2 ^ b) ≤ ε ≤ 1 / 2`, the explicit bounds are
`m · 2^b · ε² ≤ 144 (b + 2) · size(c) · sqrt(n)` and
`m · sqrt(m) · 2^b · ε² ≤ 144 (b + 2) · wireCount(c)`.
At `2 ^ b = b * m` these give `Omega(ε² n^(3/2) / log² n)` gates and
`Omega(ε² n^(5/2) / log^(5/2) n)` active wires. Exact computation is the case `ε = 1 / 2`.
These are original improvements to the Kane–Williams bounds, using the repaired restriction
lemmas and an explicit simultaneous Hoeffding tail. The displayed theorems are finite inequalities;
no asymptotic-limit theorem is asserted here.

**Model.** Circuits are straight-line programs of upstream `Cslib.Circuits.Circuit` with one output
over `Cslib.Circuits.Boolean.WeightedThreshold.signature`. Each gate `Op` has an arity `m`, a real
weight vector `Fin m → ℝ`, and a real threshold, outputting `true` when the weighted sum of its
`{0, 1}`-valued inputs is at least that threshold. `c.size` counts all threshold gates, `c.depth`
is the longest path of gates from an output to an input, and `wireCount c` sums over all gates the
number of distinct input or predecessor-gate wires with nonzero aggregated weight in that gate. The
elementary threshold-gate signature and circuit-depth recursion are the two allowed model modules.

## References

* [D. M. Kane and R. Williams, *Super-Linear Gate and Super-Quadratic Wire Lower Bounds for
  Depth-Two and Depth-Three Threshold Circuits*][KaneWilliams2016], STOC 2016 /
  `arXiv:1511.07860v1`: Theorem 1.1, Lemma 1.1, Theorem 1.2, Theorem 2.3 (Section 2), Lemma 3.1,
  Section 5
* [A. E. Andreev, *On a Method for Obtaining More Than Quadratic Effective Lower Bounds for the
  Complexity of π-Schemes*][Andreev1987]
* [P. Erdős, *On a lemma of Littlewood and Offord*][Erdos1945]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

namespace ComplexityAbstracts.AndreevThresholdAbstract

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

/-- **Exact quadratic upper bound.** For all `b, m`, Andreev's function on `n = 2^b + b*m` bits is
computed by a depth-two weighted threshold circuit with `4 * 4^b + b * m * 2^b + 1` gates
(`4 * 4^b + b * m * 2^b` bottom gates and one top gate). -/
theorem exact_upper_bound (b m : ℕ) :
    ∃ c : ThrCircuit (2 ^ b + b * m),
      c.depth ≤ 2 ∧
      c.size = 4 * 4 ^ b + b * m * 2 ^ b + 1 ∧
      wireCount c ≤ (4 * 4 ^ b + b * m * 2 ^ b) * (2 ^ b + b * m + 1) ∧
      (∀ x, evaluate c x = andreev b m x) :=
  AndreevThresholdBridge.exact_upper_bound b m

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
  AndreevThresholdBridge.high_agreement_upper_bound b m B ht hB

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
  AndreevThresholdBridge.weak_agreement_upper_bound hr m B ht hB

/-- Resource-sensitive average-case gate lower bound. The fixed-weight count saves one logarithm. -/
theorem gate_lower_bound {b m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ)) :
    (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      36 * ((b : ℝ) + 2 + Real.log ((c.size : ℝ) + 1)) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b *
        m : ℕ) : ℝ) :=
  AndreevThresholdBridge.gate_lower_bound hm hε c hd hcorr

/-- Explicit average-case gate lower bound. The fixed-weight count saves one logarithm. -/
theorem gate_lower_bound_of_le_eps {b m : ℕ} (hm : 0 < m)
    (hmN : m ≤ 2 ^ b) {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (hε1 : ε ≤ 1 / 2)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ)) :
    (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      144 * ((b : ℝ) + 2) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) :=
  AndreevThresholdBridge.gate_lower_bound_of_le_eps hm hmN hε hε1 c hd hcorr

/-- Exact gate lower bound, specializing the improved bound at advantage `1 / 2`. -/
theorem exact_gate_lower_bound {b m : ℕ} (hm : 0 < m) (hmN : m ≤ 2 ^ b)
    (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / 2)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcomp : ∀ x, evaluate c x = andreev b m x) :
    (m : ℝ) * (2 : ℝ) ^ b * (1 / 2) ^ 2 ≤
      144 * ((b : ℝ) + 2) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) :=
  AndreevThresholdBridge.exact_gate_lower_bound hm hmN hb c hd hcomp

/-- Resource-sensitive average-case wire lower bound. The fixed-weight count saves one logarithm. -/
theorem wire_lower_bound {b m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ)) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      36 * ((b : ℝ) + 2 + Real.log ((wireCount c : ℝ) + 1)) * (wireCount c : ℝ) :=
  AndreevThresholdBridge.wire_lower_bound hm hε c hd hcorr

/-- Explicit average-case wire lower bound. The fixed-weight count saves one logarithm. -/
theorem wire_lower_bound_of_le_eps {b m : ℕ} (hm : 0 < m)
    (hmN : m ≤ 2 ^ b) {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (hε1 : ε ≤ 1 / 2)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ)) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      144 * ((b : ℝ) + 2) * (wireCount c : ℝ) :=
  AndreevThresholdBridge.wire_lower_bound_of_le_eps hm hmN hε hε1 c hd hcorr

/-- Exact wire lower bound, specializing the improved bound at advantage `1 / 2`. -/
theorem exact_wire_lower_bound {b m : ℕ} (hm : 0 < m) (hmN : m ≤ 2 ^ b)
    (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / 2)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcomp : ∀ x, evaluate c x = andreev b m x) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * (1 / 2) ^ 2 ≤
      144 * ((b : ℝ) + 2) * (wireCount c : ℝ) :=
  AndreevThresholdBridge.exact_wire_lower_bound hm hmN hb c hd hcomp

/-- info: abstract audit passed for `ComplexityAbstracts.AndreevThresholdAbstract`: 18 root
declarations -/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.AndreevThresholdAbstract allowing [
  Complexity.Computability.Circuit.Boolean.WeightedThreshold,
  Complexity.Computability.Circuit.Depth
]

end ComplexityAbstracts.AndreevThresholdAbstract
