/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.ConstantDepthArithmeticBridge

/-! # Constant-depth algebraic circuits for iterated matrix multiplication need superpolynomial size

An algebraic circuit computes a polynomial from variables and field constants with sum gates and
product gates of unbounded fan-in. Its product-depth is the largest number of product gates on a
path from the output to an input. Limaye, Srinivasan and Tavenas proved that circuits of any
constant product-depth `Δ` computing iterated matrix multiplication `IMM_{n,d}` (the top-left
entry of a product of `d` generic `n × n` matrices) need superpolynomial size, over fields of
characteristic `0` or larger than `d`. Forbes extended the result to every field.

Here, over every field `K` and at every fixed `Δ` and exponent `c`, for all sufficiently large `n`
(the filter `∀ᶠ n in Filter.atTop`) and `d = ⌊log₂ ⌊log₂ n⌋⌋`, every such simple circuit, one
whose product gates read distinct wires, has more than `n ^ c` gates (`superpolynomial`). The
explicit bound behind it is `explicit_bound`. It is stated for `10 d ≤ k` and `2 ^ k ≤ n`:

`2 ^ (k (d ^ (1 / (4 ^ Δ - 1)) / 20 - 1 / 2))`
`≤ (4 (2 (d + 1) ^ 2) ^ (d + 1)) ^ Δ (s + N + 1) ^ (2Δ + 1)`

for a circuit with `s` gates and `N` inputs. At `d = ⌊log₂ ⌊log₂ n⌋⌋` the factor
`(4 (2 (d + 1) ^ 2) ^ (d + 1)) ^ Δ` is `n ^ o(1)`, and `d ^ (1 / (4 ^ Δ - 1))` grows without bound.

**Model.** Circuits are the straight-line programs of upstream `Cslib.Circuits.Circuit` with one
output, over the basis `Cslib.Circuits.Arithmetic.sigmaPiSignature K`. That basis has a sum gate
`add m c`, computing `∑ j, c j * x j` with edge constants `c : Fin m → K`, a product gate `mul m`
computing `∏ j, x j`, and a constant gate `const a`, for every arity `m`. The model module is
explicitly allowed below, together with the weighted depth `Cslib.Circuits.Circuit.depthWith`.

* **Polynomial.** A circuit computes a polynomial *formally*: it is evaluated in
  `MvPolynomial (Fin N) K` at the variables (`polynomial`). The lower bound is for this
  syntactic notion (formal polynomials), as in the source.
* **Product-depth.** `productDepth` charges one for product gates and nothing for sum and
  constant gates.
* **Size.** `C.size` counts every gate, constants included; the `N` inputs are not counted.
* **Simplicity.** A product gate reads pairwise distinct wires (`IsSimple`). We read the source's
  circuits as graphs without multiple edges; `IsSimple` is this formalization's rendering of that,
  an original convention. Without it one product gate would compute `x ^ m` from one input. Sum
  gates may read a wire several times.
* **Variables.** The `d n ^ 2` variables `(i, a, c)` of `IMM_{n,d}`, the entry `(a, c)` of the
  `i`-th matrix, are in bijection `e` with the inputs. A renaming that is not injective lets two
  distinct inputs rename to the same variable `v`, so a product gate reading both computes `v ^ 2`
  at cost one, circumventing `IsSimple`. The bijection also bounds the number of inputs by
  `N = d n ^ 2`, which the proof needs. The explicit bound tolerates any renaming `e` only because
  it pays for `N` in the factor `(s + N + 1)`. An injective renaming loses nothing: adding unused
  inputs changes neither the size, the product-depth nor the renamed polynomial, and extends it to
  a bijection (this padding argument is not formalized).

**Relation to the source.** Limaye, Srinivasan and Tavenas state their Theorem 1 over fields of
characteristic `0` or larger than `d`, for growing `Δ`, with `d = o(log N)` and size
`N ^ (d ^ exp (-O(Δ)))`. Their Corollary 4 covers `d ≤ (log n) / 100` with size
`n ^ (d ^ exp (-O(Δ)))`, and a remark extends it to a superpolynomial bound for
`ω(1) ≤ d ≤ poly(n)`. Here the field is arbitrary, by Forbes's set-multilinearization. The
constants are explicit and the exponent is `d ^ (1 / (4 ^ Δ - 1))`. The superpolynomial form is
proved at constant `Δ` and the single value `d = ⌊log₂ ⌊log₂ n⌋⌋`. The growing-`Δ` statement, the
asymptotic exponent and the full range of `d` are not formalized.

A reader only needs to check the definitions and theorem statements below, together with the
allowed model modules. Lean checks the proofs through `ConstantDepthArithmeticBridge`, and
`#check_abstract` audits the dependency boundary.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], ECCC TR21-081 revision 1: Theorem 1 (p. 1),
  Corollary 4 (p. 4)
* [M. A. Forbes, *Low-depth algebraic circuit lower bounds over any field*][Forbes2024],
  Corollary 27 (p. 31:14)
-/

namespace ComplexityAbstracts.ConstantDepthArithmeticAbstract

/-- An algebraic circuit over `K` with `N` inputs and one output: a straight-line program of sum
gates with edge constants, product gates of every arity, and constants. -/
abbrev ArithCircuit (K : Type*) (N : ℕ) :=
  Cslib.Circuits.Circuit (Cslib.Circuits.Arithmetic.sigmaPiSignature K) N 1

/-- The polynomial computed formally by a circuit: its output evaluated in `MvPolynomial (Fin N) K`
at the variables `X i`, a constant gate `const a` denoting the constant polynomial `C a`. -/
noncomputable def polynomial {K : Type*} [CommSemiring K] {N : ℕ} (C : ArithCircuit K N) :
    MvPolynomial (Fin N) K :=
  C.eval (Cslib.Circuits.Arithmetic.sigmaPiInterpretationWith K MvPolynomial.C) MvPolynomial.X 0

/-- The product-depth: the largest number of product gates on a path from the output to an
input. -/
def productDepth {K : Type*} {N : ℕ} (C : ArithCircuit K N) : ℕ :=
  C.depthWith Cslib.Circuits.Arithmetic.SigmaPiOp.mulCost

/-- A circuit is simple when every product gate reads pairwise distinct wires. `C.program.lines g`
is gate `g`: its operation and the wires supplying its arguments. -/
def IsSimple {K : Type*} {N : ℕ} (C : ArithCircuit K N) : Prop :=
  ∀ g m, (C.program.lines g).op = Cslib.Circuits.Arithmetic.SigmaPiOp.mul m →
    Function.Injective (C.program.lines g).wires

/-- Iterated matrix multiplication `IMM_{n,d}`: the entry `(0, 0)` of the product
`X_0 X_1 ⋯ X_{d-1}` of `d` generic `n × n` matrices, the entry `(a, c)` of `X_i` being the
variable `(i, a, c)`. -/
noncomputable def imm (K : Type*) [CommSemiring K] (n d : ℕ) [NeZero n] :
    MvPolynomial (Fin d × Fin n × Fin n) K :=
  (List.ofFn fun i : Fin d => Matrix.of fun a c : Fin n => MvPolynomial.X (i, a, c)).prod 0 0

/-- **Superpolynomial lower bound over any field.** Fix a field `K`, a product-depth `Δ` and an
exponent `c`. For all sufficiently large `n`, with `d = ⌊log₂ ⌊log₂ n⌋⌋`, every simple circuit
over `K` of product-depth at most `Δ` computing `IMM_{n,d}`, its inputs in bijection `e` with the
variables, has more than `n ^ c` gates. -/
theorem superpolynomial (K : Type*) [Field K] (Δ c : ℕ) :
    ∀ᶠ n in Filter.atTop, ∀ [NeZero n] {N : ℕ}
      (e : Fin N ≃ Fin (Nat.log 2 (Nat.log 2 n)) × Fin n × Fin n) (C : ArithCircuit K N),
      IsSimple C → productDepth C ≤ Δ →
      MvPolynomial.rename e (polynomial C) = imm K n (Nat.log 2 (Nat.log 2 n)) →
      n ^ c < C.size :=
  ConstantDepthArithmeticBridge.superpolynomial K Δ c

/-- **Explicit lower bound over any field.** Let `10 d ≤ k`, `2 ^ k ≤ n` and `1 ≤ Δ`. A simple
circuit over a field `K` with `C.size` gates and `N` inputs, of product-depth at most `Δ`,
computing `IMM_{n,d}` after renaming its variables by any `e`, satisfies
`2 ^ (k (d ^ (1 / (4 ^ Δ - 1)) / 20 - 1 / 2)) ≤
(4 (2 (d + 1) ^ 2) ^ (d + 1)) ^ Δ (C.size + N + 1) ^ (2 Δ + 1)`. -/
theorem explicit_bound {K : Type*} [Field K] {n d N k Δ : ℕ} [NeZero n]
    (e : Fin N → Fin d × Fin n × Fin n) (hk : 10 * d ≤ k) (hn : 2 ^ k ≤ n) (hΔ : 1 ≤ Δ)
    (C : ArithCircuit K N) (simple : IsSimple C) (depth : productDepth C ≤ Δ)
    (computes : MvPolynomial.rename e (polynomial C) = imm K n d) :
    (2 : ℝ) ^ ((k : ℝ) * ((d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 20 - 1 / 2)) ≤
      (((4 * (2 * (d + 1) ^ 2) ^ (d + 1)) ^ Δ * (C.size + N + 1) ^ (2 * Δ + 1) : ℕ) : ℝ) :=
  ConstantDepthArithmeticBridge.explicit_bound e hk hn hΔ C simple depth computes

/-- info: abstract audit passed for `ComplexityAbstracts.ConstantDepthArithmeticAbstract`: 8 root
declarations, 145 dependencies checked -/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.ConstantDepthArithmeticAbstract allowing [
  Complexity.Computability.Circuit.Arithmetic.SigmaPi,
  Complexity.Computability.Circuit.Depth
]

end ComplexityAbstracts.ConstantDepthArithmeticAbstract
