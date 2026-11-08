/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

-- upstream: local-only (formal abstract library)

import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.Andreev
import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevApproxMajority
import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevAverage
import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevLowerBound

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

/-- **Exact quadratic upper bound.** For all `b, m`, Andreev's function on `n = 2^b + b*m` bits is
computed by a depth-two weighted threshold circuit with `2 * 4^b + b * m * 2^b + 1` gates in which
every gate either reads only original inputs, with integer weights of absolute value at most `2`, or
reads only gates, with odd integer weights of absolute value below `2 n`. The weight conjunct is
`Cslib.Circuits.Boolean.WeightedThreshold.lines_andreevCircuit_bottom_or_top`. -/
theorem exact_upper_bound (b m : ℕ) :
    ∃ c : ThrCircuit (2 ^ b + b * m),
      c.depth ≤ 2 ∧
      c.size = 2 * 4 ^ b + b * m * 2 ^ b + 1 ∧
      wireCount c ≤ (2 * 4 ^ b + b * m * 2 ^ b) * (2 ^ b + b * m + 1) ∧
      (∀ x, evaluate c x = andreev b m x) ∧
      ∀ gate : Fin c.size,
        ((∀ a, ∃ i, (c.program.lines gate).wires a = Cslib.Circuits.Wire.input i) ∧
          ∀ a, ∃ z : ℤ, |z| ≤ 2 ∧ (c.program.lines gate).op.weight a = z) ∨
        ((∀ a, ∃ g, (c.program.lines gate).wires a = Cslib.Circuits.Wire.gate g) ∧
          ∀ a, ∃ z : ℤ, Odd z ∧ |z| < 2 * ((2 ^ b + b * m : ℕ) : ℤ) ∧
            (c.program.lines gate).op.weight a = z) :=
  ⟨Cslib.Circuits.Boolean.WeightedThreshold.andreevCircuit b m,
    Cslib.Circuits.Boolean.WeightedThreshold.depth_andreevCircuit_le b m,
    Cslib.Circuits.Boolean.WeightedThreshold.size_andreevCircuit b m,
    Cslib.Circuits.Boolean.WeightedThreshold.wireCount_andreevCircuit_le b m,
    fun x => congrFun (Cslib.Circuits.Boolean.WeightedThreshold.computes_andreevCircuit b m x) 0,
    Cslib.Circuits.Boolean.WeightedThreshold.lines_andreevCircuit_bottom_or_top b m⟩

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

/-- Resource-sensitive average-case gate lower bound. The fixed-weight count saves one logarithm. -/
theorem gate_lower_bound {b m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ)) :
    (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      36 * ((b : ℝ) + 2 + Real.log ((c.size : ℝ) + 1)) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b *
        m : ℕ) : ℝ) :=
  Cslib.Circuits.Boolean.WeightedThreshold.size_ge_of_card_eval_eq_andreev_ge_of_le_eps hm hε c
    hd 0 hcorr

/-- Explicit average-case gate lower bound. The fixed-weight count saves one logarithm. -/
theorem gate_lower_bound_of_le_eps {b m : ℕ} (hm : 0 < m)
    (hmN : m ≤ 2 ^ b) {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (hε1 : ε ≤ 1 / 2)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ)) :
    (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      144 * ((b : ℝ) + 2) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) :=
  Cslib.Circuits.Boolean.WeightedThreshold.size_ge_of_card_eval_eq_andreev_ge_of_le_two_pow hm
    hmN hε (by linarith) c hd 0 hcorr

/-- Exact gate lower bound, specializing the improved bound at advantage `1 / 2`. -/
theorem exact_gate_lower_bound {b m : ℕ} (hm : 0 < m) (hmN : m ≤ 2 ^ b)
    (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / 2)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcomp : ∀ x, evaluate c x = andreev b m x) :
    (m : ℝ) * (2 : ℝ) ^ b * (1 / 2) ^ 2 ≤
      144 * ((b : ℝ) + 2) * (c.size : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) := by
  apply gate_lower_bound_of_le_eps hm hmN hb (by norm_num) c hd
  have hall : (Finset.univ.filter fun x => evaluate c x = andreev b m x) = Finset.univ :=
    Finset.filter_true_of_mem fun x _ => hcomp x
  rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  push_cast
  linarith

/-- Resource-sensitive average-case wire lower bound. The fixed-weight count saves one logarithm. -/
theorem wire_lower_bound {b m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ)) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      36 * ((b : ℝ) + 2 + Real.log ((wireCount c : ℝ) + 1)) * (wireCount c : ℝ) :=
  Cslib.Circuits.Boolean.WeightedThreshold.wireCount_ge_of_card_eval_eq_andreev_ge_of_le_eps hm
    hε c hd 0 hcorr

/-- Explicit average-case wire lower bound. The fixed-weight count saves one logarithm. -/
theorem wire_lower_bound_of_le_eps {b m : ℕ} (hm : 0 < m)
    (hmN : m ≤ 2 ^ b) {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (hε1 : ε ≤ 1 / 2)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcorr : (2 : ℝ) ^ (2 ^ b + b * m) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun x => evaluate c x = andreev b m x).card : ℝ)) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      144 * ((b : ℝ) + 2) * (wireCount c : ℝ) :=
  Cslib.Circuits.Boolean.WeightedThreshold.wireCount_ge_of_card_eval_eq_andreev_ge_of_le_two_pow
    hm hmN hε (by linarith) c hd 0 hcorr

/-- Exact wire lower bound, specializing the improved bound at advantage `1 / 2`. -/
theorem exact_wire_lower_bound {b m : ℕ} (hm : 0 < m) (hmN : m ≤ 2 ^ b)
    (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / 2)
    (c : ThrCircuit (2 ^ b + b * m)) (hd : c.depth ≤ 2)
    (hcomp : ∀ x, evaluate c x = andreev b m x) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * (1 / 2) ^ 2 ≤
      144 * ((b : ℝ) + 2) * (wireCount c : ℝ) := by
  apply wire_lower_bound_of_le_eps hm hmN hb (by norm_num) c hd
  have hall : (Finset.univ.filter fun x => evaluate c x = andreev b m x) = Finset.univ :=
    Finset.filter_true_of_mem fun x _ => hcomp x
  rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  push_cast
  linarith

/-- Gate lower bound for approximate majorities of depth-two circuits. -/
theorem approx_majority_gate_lower_bound {b m t : ℕ} (hm : 0 < m) (hmN : m ≤ 2 ^ b) (ht : 0 < t)
    {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (C : Fin t → ThrCircuit (2 ^ b + b * m)) (hd : ∀ i, (C i).depth ≤ 2)
    (s : ℕ) (hs : ∀ i, (C i).size ≤ s)
    (hmaj : ∀ x, (t : ℝ) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun i => evaluate (C i) x = andreev b m x).card : ℝ)) :
    (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤
      144 * ((b : ℝ) + 2) * (s : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) :=
  Cslib.Circuits.Boolean.WeightedThreshold.size_ge_of_approxMajority_andreev_of_le_two_pow hm hmN
    ht hε C hd hs hmaj

/-- Wire lower bound for approximate majorities of depth-two circuits. -/
theorem approx_majority_wire_lower_bound {b m t : ℕ} (hm : 0 < m) (hmN : m ≤ 2 ^ b) (ht : 0 < t)
    {ε : ℝ} (hε : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ ε)
    (C : Fin t → ThrCircuit (2 ^ b + b * m)) (hd : ∀ i, (C i).depth ≤ 2)
    (s : ℕ) (hs : ∀ i, wireCount (C i) ≤ s)
    (hmaj : ∀ x, (t : ℝ) * (1 / 2 + ε) ≤
      ((Finset.univ.filter fun i => evaluate (C i) x = andreev b m x).card : ℝ)) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b * ε ^ 2 ≤ 144 * ((b : ℝ) + 2) * (s : ℝ) :=
  Cslib.Circuits.Boolean.WeightedThreshold.wireCount_ge_of_approxMajority_andreev_of_le_two_pow hm
    hmN ht hε C hd hs hmaj

/-- Top fan-in gate lower bound for majority votes of depth-two circuits. -/
theorem majority_vote_gate_lower_bound {b m t : ℕ} (hm : 0 < m) (hmN : m ≤ 2 ^ b)
    (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / (2 * t))
    (C : Fin t → ThrCircuit (2 ^ b + b * m)) (hd : ∀ i, (C i).depth ≤ 2)
    (s : ℕ) (hs : ∀ i, (C i).size ≤ s)
    (hvote : ∀ x, t < 2 * (Finset.univ.filter fun i => evaluate (C i) x = andreev b m x).card) :
    (m : ℝ) * (2 : ℝ) ^ b ≤
      576 * ((b : ℝ) + 2) * (t : ℝ) ^ 2 * (s : ℝ) * Real.sqrt ((2 ^ b + b * m : ℕ) : ℝ) :=
  Cslib.Circuits.Boolean.WeightedThreshold.size_ge_of_majorityVote_andreev_of_le_two_pow hm hmN
    hb C hd hs hvote

/-- Top fan-in wire lower bound for majority votes of depth-two circuits. -/
theorem majority_vote_wire_lower_bound {b m t : ℕ} (hm : 0 < m) (hmN : m ≤ 2 ^ b)
    (hb : 3 * ((b : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ b) ≤ 1 / (2 * t))
    (C : Fin t → ThrCircuit (2 ^ b + b * m)) (hd : ∀ i, (C i).depth ≤ 2)
    (s : ℕ) (hs : ∀ i, wireCount (C i) ≤ s)
    (hvote : ∀ x, t < 2 * (Finset.univ.filter fun i => evaluate (C i) x = andreev b m x).card) :
    (m : ℝ) * Real.sqrt (m : ℝ) * (2 : ℝ) ^ b ≤ 576 * ((b : ℝ) + 2) * (t : ℝ) ^ 2 * (s : ℝ) :=
  Cslib.Circuits.Boolean.WeightedThreshold.wireCount_ge_of_majorityVote_andreev_of_le_two_pow hm
    hmN hb C hd hs hvote

end ComplexityAbstracts.AndreevThresholdBridge
