/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Anton Kovsharov
-/

-- upstream: local-only (formal abstract draft; endpoint pending)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Pi

/-! # Draft: OpenAI: the Exponential Time Hypothesis is false

**Unproved contracts, not headline theorems.** This draft prepares the formal abstract requested
in #1226. `ExactCounting`, `ETHRefutation`, `SETHRefutation`, and `ZeroSATExponents` below are
propositions describing the intended results; this file supplies no proof of any of them. There
is no bridge yet, and this draft is not selected in the public catalogue. In particular, a passing
`#check_abstract` checks the dependency boundary of these definitions, not their truth.

The intended primary result is one deterministic machine for each fixed clause width, counting
exactly over the declared variables. Its target running time is exponential in a constant times
`n (log log (n + 16))² / sqrt (log (n + 16))`, multiplied by a polynomial in the original encoded
input length. Its target work space, including a separate charge for the encoded output, is
polynomial in that same external length. This is the interpolation-scale route of Sections 3–6 and
Proposition 6.4 of [OpenAI2026ETH], not the sharper Theorem 1.1 / Appendix D bound.

The definitions here display the existing CNF semantics, encodings and fine-grained classes;
they are not alternative library interfaces. The accompanying regression module checks their
agreement with the canonical definitions. Machinery is existential, and no private endpoint
preparation is imported. The native endpoint, its proof bridge, and outside source review must
be completed before these contracts can become catalogue theorems.

**What a reader inspects.** Read the definitions below, the displayed `Encoding` foundation,
and the one additional allowed module, `MultiTape.ResourceBounds`. The latter contributes only
the plain native `ComputableInO` resource convention, explained below, over upstream deterministic
machines. No CNF implementation, complexity-class definition or counting construction is
allowlisted. Once a bridge exists, Lean will check its proofs against these statements.

## References and credit

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], revised 25 October 2026,
  Sections 3–6, Proposition 6.4, pp. 43–44, and Appendices A–B. Source revision:
  `openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.
* [R. Impagliazzo and R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]: the
  exponential-time hypotheses and the infimum exponent.

The native port is the joint work recorded in #1226, including Samuel Schlesinger,
Anton Kovsharov, Erik Demaine and the contributing Codex, Claude and Jetski workers. The native
machine and encoding foundations include Christian Reitwiessner's contributions. This draft
does not claim authorship of those implementations. Construction provenance will be recorded in
the bridge when the unconditional endpoint is available.
-/

namespace ComplexityAbstracts.SubexponentialSATAbstract

/-! ## Formulas and declared-variable counting

A literal `(v, b)` asserts that variable `v` has Boolean value `b`. Clauses are disjunctions
and formulas are conjunctions; repeated literals and clauses are permitted. A width bound
counts literal occurrences, including repetitions.
-/

/-- A CNF formula is a list of clauses, each a list of variable/polarity pairs. -/
abbrev Formula := List (List (ℕ × Bool))

/-- Evaluate a formula: every clause must contain a literal of the assigned polarity. -/
def eval (φ : Formula) (σ : ℕ → Bool) : Bool :=
  φ.all fun clause => clause.any fun literal => σ literal.1 == literal.2

/-- A formula is satisfiable when some total Boolean assignment makes it true. -/
def Satisfiable (φ : Formula) : Prop := ∃ σ : ℕ → Bool, eval φ σ = true

/-- Variables in occurrence order, retaining repetitions. -/
def vars (φ : Formula) : List ℕ := φ.flatten.map Prod.fst

/-- The number of distinct occurring variables, independent of their numeric labels. -/
def numVars (φ : Formula) : ℕ := (vars φ).toFinset.card

/-- Count satisfying assignments on the declared range `{0, …, n - 1}`, extending by `false`
outside it. Valid inputs below require every occurring variable to lie in that range. -/
def modelCountOn (φ : Formula) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : (Finset.range n) → Bool =>
    eval φ (fun v => if h : v ∈ Finset.range n then σ ⟨v, h⟩ else false) = true).card

/-- The input has clauses of width at most `k`, with every variable strictly below `n`. -/
def validDeclaredInput (k n : ℕ) (φ : Formula) : Bool :=
  (φ.all fun clause => decide (clause.length ≤ k)) &&
    ((vars φ).all fun v => decide (v < n))

/-- A declared counting instance consists of its variable count and formula. -/
abbrev Input := ℕ × Formula

/-! ## Representation details

The external input is `encPair encUnary encCNF (n, φ)`. Its length is
`2 * n + 1 + (encCNF φ).length`, so even an empty formula retains the cost of its declared
variables. Literal indices are binary; large or non-dense labels are not silently treated as
small. A natural output uses canonical binary digits, with zero encoded by the empty word.
The shared foundation spells out all framing and list conventions.
-/

/-- Encode each literal as a framed binary index followed by its polarity bit; frame the
literals within clauses and the clauses within the formula. This is the native `encCNF`. -/
def encCNF : Formula ↪ List Bool :=
  ComplexityTests.Abstracts.Encoding.encList (ComplexityTests.Abstracts.Encoding.encList
    (ComplexityTests.Abstracts.Encoding.encPair ComplexityTests.Abstracts.Encoding.encNat
      ComplexityTests.Abstracts.Encoding.encBool))

/-- Frame the unary declared-variable count, then append the encoded formula. -/
def encInput : Input ↪ List Bool :=
  ComplexityTests.Abstracts.Encoding.encPair ComplexityTests.Abstracts.Encoding.encUnary encCNF

/-! ## Deterministic machine and resource conventions

The upstream model is a deterministic binary multi-tape Turing machine with finitely many
states and a fixed finite number of work tapes. Each transition performs bounded head moves
and symbol operations. The input tape is read-only, and output is write-only. Time counts
transitions until halting; work space counts visited work-tape cells over every run prefix.
No condition is imposed on bitstrings outside the chosen encoding's image.

The native predicate `Turing.MultiTapeTM.ComputableInO f encIn encOut T S` means that there
exists a constant `C` and one such machine computing `f` on every encoded input `x` within
`C * (T x + 1)` steps and `C * (S x + 1)` work cells, with the additional bound
`(encOut (f x)).length ≤ C * (S x + 1)`. Thus output is charged even though its tape is not a
work tape. Time and space are independent budgets; a time bound does not supply polynomial
space. This is the library's existing resource predicate, not a unit-cost arithmetic machine.

For decision problems below, `DecidableInTimeAndSpace` computes the exact Boolean membership
bit and halts on every encoded instance. Its finite machine and all bounds precede the inputs.
-/

/-- A decision problem is decidable in time `O(T x)`, with some independent space bound. -/
def DecidableInTimeO {α : Type} (A : Set α) (enc : α ↪ List Bool) (T : α → ℝ) : Prop :=
  ∃ c : ℕ, ∃ t s : α → ℕ, (∀ x, (t x : ℝ) ≤ c * T x + c) ∧
    Turing.MultiTapeTM.DecidableInTimeAndSpace A enc t s

/-- Exponential time in a parameter, with a polynomial factor in the encoded input length. -/
def DecidableInExpTime {α : Type} (A : Set α) (enc : α ↪ List Bool)
    (μ : α → ℕ) (δ : ℝ) : Prop :=
  ∃ e : ℕ, DecidableInTimeO A enc fun x => 2 ^ (δ * μ x) * ((enc x).length + 1) ^ e

/-! ## The exponential time hypotheses

The decision parameter is the number of distinct occurring variables, not the declared count
or the largest label. The intended bridge must therefore use the native dense-relabeling
correspondence. Zero infimum exponent alone does not assert a polynomial-time algorithm.
-/

/-- `k`-SAT consists of satisfiable formulas whose clauses have at most `k` literals. -/
def KSAT (k : ℕ) : Set Formula :=
  {φ | (∀ clause ∈ φ, clause.length ≤ k) ∧ Satisfiable φ}

/-- The infimum of all nonnegative exponential rates admitting a `k`-SAT decider. -/
noncomputable def satExponent (k : ℕ) : ℝ :=
  sInf {δ | 0 ≤ δ ∧ DecidableInExpTime (KSAT k) encCNF numVars δ}

/-- ETH asserts that some positive exponential rate is unattainable for 3SAT. -/
def ETH : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ¬DecidableInExpTime (KSAT 3) encCNF numVars δ

/-- SETH asserts that every improvement below rate one fails for some fixed clause width. -/
def SETH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ¬DecidableInExpTime (KSAT k) encCNF numVars (1 - ε)

/-! ## Intended headline contracts — proofs pending

All declarations in this section are definitions of propositions, not theorems. The primary
contract fixes the counter, time and space functions, constants and native machine for each `k`
before every input. It includes `k = 0, 1`, `n = 0`, empty formulas and empty clauses. Invalid
width or variable-range inputs return zero. In particular, a valid empty formula returns `2^n`,
including one assignment when `n = 0`; unused declared variables remain free choices.

The scale uses natural logarithms and a shift by sixteen to cover all natural `n`; this changes
only constants in the asymptotic bound. It is the scale of Proposition 6.4, not the smaller
exponent of Theorem 1.1. The future proof uses width `max 2 k` internally while retaining the
original width guard, one inner support normalization and one outer declared-variable correction.
Those proof details do not weaken the total external contract.
-/

/-- The interpolation-scale exponent, defined at every natural input. -/
noncomputable def interpolationScale (n : ℕ) : ℝ :=
  n * Real.log (Real.log ((n : ℝ) + 16)) ^ 2 / Real.sqrt (Real.log ((n : ℝ) + 16))

/-- Pending primary claim: one exact native counter per fixed width, with interpolation-scale
time and polynomial space in the length of the original declared input. -/
def ExactCounting : Prop :=
  ∀ k : ℕ, ∃ (count : Input → ℕ) (T S : Input → ℕ) (A c e a b : ℕ),
    Turing.MultiTapeTM.ComputableInO count encInput
      ComplexityTests.Abstracts.Encoding.encNat T S ∧
    (∀ x, count x = if validDeclaredInput k x.1 x.2 then modelCountOn x.2 x.1 else 0) ∧
    (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
      (((encInput x).length : ℝ) + 1) ^ e) + c) ∧
    (∀ x, S x ≤ a * ((encInput x).length + 1) ^ b)

/-- Pending headline: the exponential time hypothesis is false. -/
def ETHRefutation : Prop := ¬ETH

/-- Pending headline: the strong exponential time hypothesis is false. -/
def SETHRefutation : Prop := ¬SETH

/-- Pending headline: every fixed-width SAT exponent is zero. -/
def ZeroSATExponents : Prop := ∀ k, satExponent k = 0

end ComplexityAbstracts.SubexponentialSATAbstract

/--
info: abstract audit passed for `ComplexityAbstracts.SubexponentialSATAbstract`:
23 root declarations, 138 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.SubexponentialSATAbstract allowing [
  ComplexityAbstracts.Encoding,
  Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
]
