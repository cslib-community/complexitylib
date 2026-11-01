/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import ComplexityAbstracts.BQPBridge

/-! # BQP is contained in PP

A quantum computer that answers correctly with probability at least `2/3` can be simulated by a
classical machine that decides by an unbounded-error majority vote. Adleman, DeMarrais and Huang
proved `BQP ⊆ PP` for quantum machines with algebraic amplitudes. The proof sums over computation
paths. Each Hadamard gate splits a path in two with amplitude `±2^{-1/2}`, and classical gates
permute basis strings. The acceptance probability is therefore `g / 2^h`, where `h` counts the
Hadamard gates and `g` is a difference of two counts of polynomially checkable path pairs. Deciding
whether it exceeds `1/2` is a question about a strict majority of certificates, which is the class
`PP`. Fortnow and Rogers sharpened the containment to `BQP ⊆ AWPP`. The library proves that
containment as an intermediate step, but this abstract does not state it.

The model is restated from scratch below. A state of an `m`-qubit register is an amplitude function
on basis strings. Each gate is an explicit formula on amplitudes. A uniform family is computed by
one polynomial-time machine, using the shared foundation `Computation.PolyTime`. The class `PP` uses
the shared `Computation.PolyTimeVerifier`.

**Gate set.** Circuits use one fixed finite gate set: the Hadamard gate and the classical reversible
gates NOT, CNOT and Toffoli. Their matrix entries lie in `{0, ±1, ±2^{-1/2}}`. Arora and Barak
instead allow any elementary operation, a unitary acting on at most three qubits, whose description
a polynomial-time machine outputs. The two definitions give the same class. Toffoli and Hadamard are
universal [Shi; Aharonov], and with the Solovay–Kitaev theorem, circuits over them simulate circuits
of arbitrary elementary operations with polynomial overhead and small error. This equivalence is a
cited remark; it is not formalized here. A fixed finite gate set matters: Adleman, DeMarrais and
Huang show that with arbitrary complex amplitudes, `BQP` would contain uncountably many languages.

A reader only needs to inspect the definitions and the theorem statement in this file, and the
displayed shared foundations, to check that it states the intended claim. Lean checks the proof
through `BQPBridge`. The bridge proves that the formulas here agree with the library's unitary
circuit semantics on well-formed gates. `#check_abstract` audits that the public statements depend
only on this file, the shared foundations `Encoding` and `Computation`, and the background libraries
Lean, Mathlib and upstream CSLib.

## References

* [L. Adleman, J. DeMarrais, M.-D. Huang, *Quantum computability*][AdlemanDeMarraisHuang1997]
* [L. Fortnow, J. Rogers, *Complexity limitations on quantum computation*][FortnowRogers1999]
* [E. Bernstein, U. Vazirani, *Quantum complexity theory*][BernsteinVazirani1997]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [Y. Shi, *Both Toffoli and Controlled-NOT need little help to do universal quantum
  computation*][Shi2003]
* [D. Aharonov, *A simple proof that Toffoli and Hadamard are quantum universal*][Aharonov2003]
-/

namespace ComplexityAbstracts.BQPAbstract

/-! ## Quantum circuits on amplitudes

A basis string of an `m`-qubit register is a bit string `y : Fin m → Bool`. A state is one complex
amplitude `ψ y` for each basis string. Gates act on amplitudes by the explicit formulas below.
Measuring a state `ψ` of norm one gives the outcome `y` with probability `|ψ y|²`.
-/

/-- The state of an `m`-qubit register: one complex amplitude for each basis string. -/
abbrev State (m : ℕ) := (Fin m → Bool) → ℂ

/-- Bit `i` of a basis string `y`, written `y_i`. A position past the end reads `false`; the
well-formed gates below never use one. -/
def bit {m : ℕ} (y : Fin m → Bool) (i : ℕ) : Bool := if h : i < m then y ⟨i, h⟩ else false

/-- The basis string `y[t ↦ c]`, that is, `y` with bit `t` set to `c`. -/
def setBit {m : ℕ} (y : Fin m → Bool) (t : ℕ) (c : Bool) : Fin m → Bool :=
  fun i => if (i : ℕ) = t then c else y i

/-- The **Hadamard gate** on qubit `t`:
`(H ψ)(y) = 2^{-1/2} Σ_{c ∈ {0,1}} (-1)^{c · y_t} ψ(y[t ↦ c])`.
On qubit `t` it maps `|0⟩ ↦ 2^{-1/2}(|0⟩ + |1⟩)` and `|1⟩ ↦ 2^{-1/2}(|0⟩ - |1⟩)`. -/
noncomputable def hadamard {m : ℕ} (t : ℕ) (ψ : State m) : State m := fun y =>
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ∑ c : Bool, (if c && bit y t then -1 else 1) * ψ (setBit y t c)

/-- Flip bit `t` of a basis string when every bit of `cs` is one. With no controls this is NOT,
with one control CNOT, and with two controls Toffoli. When `t ∉ cs` the map is its own inverse. -/
def flip {m : ℕ} (t : ℕ) (cs : List ℕ) (y : Fin m → Bool) : Fin m → Bool :=
  setBit y t (bit y t ^^ cs.all (bit y))

/-- A **classical gate** permutes the basis, `|z⟩ ↦ |flip t cs z⟩`. On amplitudes it is
`ψ ∘ flip t cs`, because `flip t cs` is its own inverse. -/
def classical {m : ℕ} (t : ℕ) (cs : List ℕ) (ψ : State m) : State m := ψ ∘ flip t cs

/-- A **gate code** `(h, t, cs)`. The code `(true, t, [])` is the Hadamard gate on qubit `t`, and
`(false, t, cs)` is the classical gate with target `t` and controls `cs`. Uniform machines output
circuits as lists of gate codes. -/
abbrev GateCode := Bool × ℕ × List ℕ

/-- A gate code is **well formed** on `m` qubits when its qubits are distinct and below `m`. A
Hadamard code has no controls, and a classical code has at most two. -/
def WellFormed (m : ℕ) : GateCode → Prop
  | (true, t, cs) => t < m ∧ cs = []
  | (false, t, cs) => cs.length ≤ 2 ∧ (t :: cs).Nodup ∧ ∀ i ∈ t :: cs, i < m

/-- The gate that a gate code denotes. -/
noncomputable def applyGate {m : ℕ} (g : GateCode) (ψ : State m) : State m :=
  if g.1 then hadamard g.2.1 ψ else classical g.2.1 g.2.2 ψ

/-- Run a circuit, given as a list of gate codes applied first to last, on the state `ψ`. -/
noncomputable def run {m : ℕ} (gs : List GateCode) (ψ : State m) : State m :=
  gs.foldl (fun ψ g => applyGate g ψ) ψ

/-- The basis state `|z⟩`: amplitude one at `z` and zero elsewhere. -/
def basis {m : ℕ} (z : Fin m → Bool) : State m := fun y => if y = z then 1 else 0

/-- The input word `x` padded with zeros to `m` bits, `x 0^{m - |x|}`. -/
def pad (m : ℕ) (x : List Bool) : Fin m → Bool := fun i => x.getD i false

/-- The **acceptance probability** of the circuit `gs` on `m` qubits and input `x`. The circuit
starts in `|x 0^{m - |x|}⟩`, and the whole register is then measured. The circuit accepts when
qubit `0` reads `1`, which has probability `Σ_{y : y_0 = 1} |ψ y|²` for the final state `ψ`. -/
noncomputable def acceptProb (m : ℕ) (gs : List GateCode) (x : List Bool) : ℝ :=
  ∑ y : Fin m → Bool, if bit y 0 then ‖run gs (basis (pad m x)) y‖ ^ 2 else 0

/-! ## Representation details

A uniform machine outputs the list of gate codes. The flag bit is a single bit. The target and
controls are written in unary, so every qubit index is bounded by the machine's output length and
is polynomial in the input length.
-/

/-- The encoding of a gate code `(h, t, cs)`: the bit `h`, then `t` and the list `cs` in unary. -/
abbrev encGateCode : GateCode ↪ List Bool :=
  ComplexityTests.Abstracts.Encoding.encPair ComplexityTests.Abstracts.Encoding.encBool
    (ComplexityTests.Abstracts.Encoding.encPair ComplexityTests.Abstracts.Encoding.encUnary
      (ComplexityTests.Abstracts.Encoding.encList ComplexityTests.Abstracts.Encoding.encUnary))

/-! ## Uniform families and the classes

The circuit for inputs of length `n` acts on `width n` qubits and has the gate codes `gates n`. A
single polynomial-time machine computes both from `n` written in unary, as in Arora and Barak's
uniform circuit families. Qubit `0` is the output qubit, so the register has at least one qubit,
and the input fits into it, so it has at least `n`.
-/

/-- `width` and `gates` form a **polynomial-time uniform circuit family**. Both are computable in
polynomial time from `n` in unary. The register for inputs of length `n` has at least `n` qubits
and at least one, and every gate code of `gates n` is well formed on it. -/
def Uniform (width : ℕ → ℕ) (gates : ℕ → List GateCode) : Prop :=
  ComplexityTests.Abstracts.Computation.PolyTime width
      ComplexityTests.Abstracts.Encoding.encUnary ComplexityTests.Abstracts.Encoding.encUnary ∧
    ComplexityTests.Abstracts.Computation.PolyTime gates
      ComplexityTests.Abstracts.Encoding.encUnary
      (ComplexityTests.Abstracts.Encoding.encList encGateCode) ∧
    ∀ n, n ≤ width n ∧ 0 < width n ∧ ∀ g ∈ gates n, WellFormed (width n) g

/-- **Bounded-error quantum polynomial time** [Bernstein, Vazirani][BernsteinVazirani1997]. A
uniform family decides `A` when it accepts the encoding of every member of `A` with probability
at least `2/3`, and the encoding of every other instance with probability at most `1/3`. -/
def BQP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (width : ℕ → ℕ) (gates : ℕ → List GateCode), Uniform width gates ∧ ∀ a,
    (a ∈ A → 2 / 3 ≤ acceptProb (width (enc a).length) (gates (enc a).length) (enc a)) ∧
    (a ∉ A → acceptProb (width (enc a).length) (gates (enc a).length) (enc a) ≤ 1 / 3)}

/-- The number of binary strings of exactly `n` bits that `V` accepts with the instance `a`. -/
def acceptCount {α : Type} (V : α × List Bool → Bool) (a : α) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Bool => V (a, List.ofFn w) = true).card

/-- **Probabilistic polynomial time with unbounded error.** A problem `A` is in `PP` when one
total polynomial-time verifier `V` and one polynomial `p` exist with the following property:
`a ∈ A` exactly when strictly more than half of the `2^{p(|enc a|)}` strings `r` of length
`p(|enc a|)` give `V (a, r) = true`. -/
def PP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComplexityTests.Abstracts.Computation.PolyTimeVerifier enc V ∧
    ∀ a, a ∈ A ↔ 2 ^ p.eval (enc a).length < 2 * acceptCount V a (p.eval (enc a).length)}

/-! ## Main result -/

/-- **BQP ⊆ PP** [Adleman, DeMarrais, Huang][AdlemanDeMarraisHuang1997]: every problem decided
with bounded error by a uniform family of circuits over the Hadamard, NOT, CNOT and Toffoli gates
is decided by a polynomial-time strict-majority vote, for every instance encoding. -/
theorem BQP_subset_PP {α : Type} (enc : α ↪ List Bool) : BQP enc ⊆ PP enc := by
  rintro A ⟨width, gates, ⟨hwidth, hgates, hn⟩, hdec⟩
  have hwf (m : ℕ) (g : GateCode) (h : WellFormed m g) :
      Cslib.Quantum.GateCode.WellFormed m g := by
    obtain ⟨_ | _, t, cs⟩ := g <;> exact h
  exact BQPBridge.BQP_subset_PP enc
    ⟨width, gates, ⟨hwidth, hgates, fun n => ⟨(hn n).1, (hn n).2.1,
      fun g hg => hwf _ g ((hn n).2.2 g hg)⟩⟩, hdec⟩

/--
info: abstract audit passed for `ComplexityAbstracts.BQPAbstract`: 22 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.BQPAbstract allowing [
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation
]

end ComplexityAbstracts.BQPAbstract
