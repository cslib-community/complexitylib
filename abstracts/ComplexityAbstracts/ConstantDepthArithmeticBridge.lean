/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

-- upstream: local-only (formal abstract library)

import Complexity.Computability.Circuit.Arithmetic.CircuitLowerBound

/-!
# Bridge for the constant-depth arithmetic circuit lower bound

States the lower bounds of `Complexity.Computability.Circuit.Arithmetic.CircuitLowerBound` over
the unfolded circuit model: the polynomial computed is the circuit evaluated at the variables, the
product-depth is `Cslib.Circuits.Circuit.depthWith` with product gates costing one, simplicity is
injectivity of the wires read by each product gate, and `IMM_{n,d}` is the entry `(0, 0)` of a
product of generic matrices.
-/

namespace ComplexityAbstracts.ConstantDepthArithmeticBridge

open Cslib.Circuits Cslib.Circuits.Arithmetic

/-- The explicit lower bound, over the unfolded model. -/
theorem explicit_bound {K : Type*} [Field K] {n d N k Δ : ℕ} [NeZero n]
    (e : Fin N → Fin d × Fin n × Fin n) (hk : 10 * d ≤ k) (hn : 2 ^ k ≤ n) (hΔ : 1 ≤ Δ)
    (C : Circuit (sigmaPiSignature K) N 1)
    (simple : ∀ g m, (C.program.lines g).op = SigmaPiOp.mul m →
      Function.Injective (C.program.lines g).wires)
    (depth : C.depthWith SigmaPiOp.mulCost ≤ Δ)
    (computes : MvPolynomial.rename e
      (C.eval (sigmaPiInterpretationWith K MvPolynomial.C) MvPolynomial.X 0) =
        (List.ofFn fun i : Fin d => Matrix.of fun a c : Fin n => MvPolynomial.X (i, a, c)).prod
          0 0) :
    (2 : ℝ) ^ ((k : ℝ) * ((d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 20 - 1 / 2)) ≤
      (((4 * (2 * (d + 1) ^ 2) ^ (d + 1)) ^ Δ * (C.size + N + 1) ^ (2 * Δ + 1) : ℕ) : ℝ) := by
  have h := SPCircuit.two_rpow_le_of_imm (C := C) e hk hn hΔ simple depth computes
  have hc : SPFormula.smCost d = 4 * (2 * (d + 1) ^ 2) ^ (d + 1) := by
    rw [SPFormula.smCost, SPFormula.gadgetCost]
    ring
  rw [hc] at h
  exact_mod_cast h

/-- The superpolynomial lower bound, over the unfolded model. -/
theorem superpolynomial (K : Type*) [Field K] (Δ c : ℕ) :
    ∀ᶠ n in Filter.atTop, ∀ [NeZero n] {N : ℕ}
      (e : Fin N ≃ Fin (Nat.log 2 (Nat.log 2 n)) × Fin n × Fin n)
      (C : Circuit (sigmaPiSignature K) N 1),
      (∀ g m, (C.program.lines g).op = SigmaPiOp.mul m →
        Function.Injective (C.program.lines g).wires) →
      C.depthWith SigmaPiOp.mulCost ≤ Δ →
      MvPolynomial.rename e
          (C.eval (sigmaPiInterpretationWith K MvPolynomial.C) MvPolynomial.X 0) =
        (List.ofFn fun i : Fin (Nat.log 2 (Nat.log 2 n)) =>
          Matrix.of fun a c : Fin n => MvPolynomial.X (i, a, c)).prod 0 0 →
      n ^ c < C.size :=
  SPCircuit.eventually_pow_lt_size_of_imm K Δ c

end ComplexityAbstracts.ConstantDepthArithmeticBridge
