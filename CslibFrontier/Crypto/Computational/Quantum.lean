/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Quantum

/-!
# Native quantum indistinguishability of word ensembles

A native quantum test is one `UniformOracleCircuitFamily`. At security parameter `n`, a challenge
word `x` is supplied through the existing classical input encoding `(1ⁿ, x)`. Every quantum-input
qubit starts in `|0⟩`; the generated circuit runs against the all-zero XOR oracle; its declared
output prefix is measured in the computational basis; and the first measured bit is the decision.
An empty output therefore rejects. `distinguishingGame` first samples the challenge and then runs
that test.

`ComputationallyIndistinguishable` requires negligible advantage for every such native family.
Generation is polynomial in the security parameter and challenge length. When both ensembles have
a common polynomial support-length bound, `ComputationallyIndistinguishable.of_within` converts a
concrete qubit/gate/query bound into this asymptotic statement using the existing game theorem.

This is a no-advice, no-useful-oracle native submodel of the quantum attackers described in
[Boneh et al.][BonehEtAl2012], §2.1, p. 7. The exact generated gate set, zero initialization and
terminal measurement are part of the definition. No equivalence with every QPPT convention,
gate-approximation theorem, efficient quantum-advice preparation or QROM security is asserted.
The packaging and resource bridge are original formalization infrastructure.

## Main definitions

* `Cslib.Crypto.NativeQuantum.test`: run one native family on one classical word.
* `Cslib.Crypto.NativeQuantum.distinguishingGame`: sample an ensemble and run the test.
* `Cslib.Crypto.NativeQuantum.ComputationallyIndistinguishable`: negligible native quantum
  distinguishing advantage.
* `Cslib.Crypto.NativeQuantum.SupportsLength`: a common support-length contract.
* `Cslib.Crypto.NativeQuantum.IndistinguishableWithin`: concrete security with explicit input and
  circuit-resource bounds.

## Main results

* `Cslib.Crypto.NativeQuantum.ComputationallyIndistinguishable.of_within`: concrete-to-asymptotic
  transfer for polynomially bounded challenge lengths and native circuit resources.

## References

* [Boneh et al., *Random Oracles in a Quantum World*][BonehEtAl2012],
  arXiv:1008.0931v2, §2.1, p. 7.
-/

public section

namespace Cslib.Crypto.NativeQuantum

open Quantum
open scoped NNReal

/-- Run a native uniform quantum circuit on the classical challenge word. All quantum-input
qubits start in the zero basis state. The zero XOR oracle gives no useful oracle access. After
terminal basis measurement, the first output bit is the decision; an empty output rejects. -/
@[expose]
noncomputable def test (family : UniformOracleCircuitFamily) (n : ℕ) (x : List Bool) : Game :=
  (family.output n x (fun _ _ => false) (ket fun _ => false) (norm_ket _)).map
    (fun output => output.headD false)

/-- The native test is the measured output law mapped to its first bit. -/
theorem test_eq (family : UniformOracleCircuitFamily) (n : ℕ) (x : List Bool) :
    test family n x =
      (family.output n x (fun _ _ => false) (ket fun _ => false) (norm_ket _)).map
        (fun output => output.headD false) :=
  rfl

/-- Sample a challenge word from `X n`, then run the native quantum test on the entire word. -/
@[expose]
noncomputable def distinguishingGame (X : ℕ → PMF (List Bool))
    (family : UniformOracleCircuitFamily) (n : ℕ) : Game :=
  (X n).bind (test family n)

/-- The sampling form of the native distinguishing game. -/
theorem distinguishingGame_eq_bind (X : ℕ → PMF (List Bool))
    (family : UniformOracleCircuitFamily) (n : ℕ) :
    distinguishingGame X family n = (X n).bind (test family n) :=
  rfl

/-- Every word supported by ensemble `X` at security parameter `n` has length at most `L n`. -/
@[expose]
def SupportsLengthAt (X : ℕ → PMF (List Bool)) (L : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ x ∈ (X n).support, x.length ≤ L n

/-- A common length schedule bounds every supported word at every security parameter. -/
@[expose]
def SupportsLength (X : ℕ → PMF (List Bool)) (L : ℕ → ℕ) : Prop :=
  ∀ n, SupportsLengthAt X L n

/-- At parameter `n`, both ensembles fit the declared input-length cap and every circuit generated
for a shorter input fits the separate qubit, elementary-gate and query budgets. -/
@[expose]
def Within (X Y : ℕ → PMF (List Bool)) (L : ℕ → ℕ) (n : ℕ)
    (budget : OracleCircuit.Resources) (family : UniformOracleCircuitFamily) : Prop :=
  SupportsLengthAt X L n ∧ SupportsLengthAt Y L n ∧
    Game.WithinOracleCircuits L n budget family

/-- A concrete resource-indexed advantage bound for native quantum tests of two ensembles. -/
@[expose]
def IndistinguishableWithin (X Y : ℕ → PMF (List Bool)) (L : ℕ → ℕ)
    (ε : ℕ → OracleCircuit.Resources → ℝ≥0) : Prop :=
  Game.IndistinguishableWithin (distinguishingGame X) (distinguishingGame Y) (Within X Y L) ε

/-- Two word ensembles are computationally indistinguishable for native uniform quantum tests
with zero-initialized quantum input and no useful oracle. Circuit generation is polynomial in the
unary security parameter and the challenge length; no polynomial challenge-length bound is built
into this definition. -/
def ComputationallyIndistinguishable (X Y : ℕ → PMF (List Bool)) : Prop :=
  Game.Indistinguishable (distinguishingGame X) (distinguishingGame Y) (fun _ => True)

/-- An ensemble is native-quantum computationally indistinguishable from itself. -/
theorem ComputationallyIndistinguishable.refl (X : ℕ → PMF (List Bool)) :
    ComputationallyIndistinguishable X X :=
  Game.Indistinguishable.refl _ _

/-- Swapping the ensembles preserves native quantum computational indistinguishability. -/
theorem ComputationallyIndistinguishable.symm {X Y : ℕ → PMF (List Bool)}
    (h : ComputationallyIndistinguishable X Y) : ComputationallyIndistinguishable Y X :=
  Game.Indistinguishable.symm h

/-- Native quantum computational indistinguishability is transitive. -/
theorem ComputationallyIndistinguishable.trans {X Y Z : ℕ → PMF (List Bool)}
    (hXY : ComputationallyIndistinguishable X Y)
    (hYZ : ComputationallyIndistinguishable Y Z) :
    ComputationallyIndistinguishable X Z :=
  Game.Indistinguishable.trans hXY hYZ

/-- Concrete bounds negligible along every componentwise polynomial resource schedule imply
native quantum computational indistinguishability, provided both ensembles have the same
polynomial support-length cap. -/
theorem ComputationallyIndistinguishable.of_within
    {X Y : ℕ → PMF (List Bool)} {L : ℕ → ℕ}
    {ε : ℕ → OracleCircuit.Resources → ℝ≥0}
    (h : IndistinguishableWithin X Y L ε) (hX : SupportsLength X L)
    (hY : SupportsLength Y L) (hL : PolynomiallyBounded L)
    (hneg : ∀ qubits gates queries : ℕ → ℕ,
      PolynomiallyBounded qubits → PolynomiallyBounded gates → PolynomiallyBounded queries →
      Negligible (fun n => ε n ⟨qubits n, gates n, queries n⟩)) :
    ComputationallyIndistinguishable X Y := by
  apply Game.Indistinguishable.of_uniformOracleCircuits hL _ hneg
  intro n budget family hfamily
  exact h n budget family ⟨hX n, hY n, hfamily⟩

end Cslib.Crypto.NativeQuantum
