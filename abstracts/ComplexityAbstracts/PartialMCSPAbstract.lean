/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import ComplexityAbstracts.PartialMCSPBridge
import Cslib.Computability.Circuit.Simulation

/-! # Ilango: Partial MCSP is hard under the Exponential Time Hypothesis

The *Partial Minimum Circuit Size Problem* (`MCSP*` or `PartialMCSP`) asks, given the `2 ^ m`-entry
truth table of a partial Boolean function `f* : {0, 1} ^ m → Option Bool` (where `some b` specifies
a required output `b` and `none` denotes a don't-care entry `*`) and a size threshold `s`, whether
some Boolean circuit of size at most `s` agrees with `f*` on every defined input. While establishing
the fine-grained or `NP`-hardness of total-function `MCSP` under standard worst-case assumptions
remains a central open problem, Rahul Ilango proved that allowing don't-care entries makes
`PartialMCSP` provably hard under the Exponential Time Hypothesis (`ETH`).

Ilango reduces an `n`-parameter instance of `2n × 2n` Bipartite Permutation Independent Set in time
`2 ^ O(n)` to an instance of `PartialMCSP` on `m = 6n` variables (truth-table size `N = 2 ^ m`)
with gate threshold `s = 6n - 1`. At this threshold, every circuit agreeing with the constructed
partial function must depend on all `6n` inputs, forcing it to be a read-once monotone formula
whose top-level wire routing encodes a pair of permutations avoiding the forbidden edges. Combining
this reduction with the Lokshtanov–Marx–Saurabh theorem—which uses the Impagliazzo–Paturi–Zane
sparsification lemma to rule out `2 ^ o(n log n)` algorithms for Bipartite Permutation Independent
Set under `ETH`—shows that `PartialMCSP` cannot be decided in time
`2 ^ o(m log m) = N ^ o(log log N)` under `ETH`.

This abstract states `ETH` on 3-CNF formulas parameterized by the number of distinct variables, and
states Ilango's subexponential lower bound and `NP` membership for `PartialMCSP`. We include both
the all-gates De Morgan circuit size (`C.size`, charging `1` for binary AND/OR, unary NOT, and
constants) and Ilango's binary-gate measure (`binaryGateCount C`, charging `1` for binary AND/OR
and `0` for NOT and constants), as well as both unary (`encInstance`) and binary
(`encInstanceBinary`) encodings of the size threshold. Exact framed bit-string encodings appear in
the appendix. Lean verifies the proofs through `PartialMCSPBridge.lean`, and `#check_abstract`
audits that all public statements depend only on this file, the displayed shared foundations, and
upstream mathematics.

## References

* [R. Ilango, *Constant Depth Formula and Partial Function Versions of MCSP are Hard*, FOCS 2020,
  Theorem I.3; ECCC TR20-183, Theorem 3 and Theorem 11][Ilango2020FOCS]
* [D. Lokshtanov, D. Marx, S. Saurabh, *Slightly Superexponential Parameterized Problems*,
  SODA 2011 / SIAM J. Comput. 2018, Theorem 2.11][LokshtanovMarxSaurabh2018]
* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*, J. Comput. Syst. Sci. 2001]
  [ImpagliazzoPaturi2001]
-/

namespace ComplexityAbstracts.PartialMCSPAbstract

/-! ## 3SAT and the Exponential Time Hypothesis

A CNF formula over natural-number variable indices is a list of clauses, each a list of literals
`(v, b)` where `b = true` represents the positive literal `x_v` and `b = false` represents `¬x_v`.
In fine-grained complexity, running time is measured in an explicit instance parameter `μ a` (for
3SAT, the number `numVars φ` of distinct variables appearing in `φ`) multiplied by a polynomial in
the encoded input length `|enc a|`. The machine model is upstream `Cslib`'s deterministic
finite-state binary multi-tape Turing machine (`Turing.MultiTapeTM.DecidableInTimeAndSpace`).
-/

/-- A literal `(v, b)` pairs a variable index `v : ℕ` with a polarity `b : Bool`. -/
abbrev Literal := ℕ × Bool

/-- A clause is a finite list of literals, read as their disjunction. -/
abbrev Clause := List Literal

/-- A CNF formula is a finite list of clauses, read as their conjunction. -/
abbrev Formula := List Clause

/-- A truth assignment `τ : ℕ → Bool` satisfies `φ` if every clause `c ∈ φ` contains a literal
`(v, b) ∈ c` with `τ v = b`. -/
def Satisfiable (φ : Formula) : Prop :=
  ∃ τ : ℕ → Bool, ∀ c ∈ φ, ∃ l ∈ c, τ l.1 = l.2

/-- `ThreeSAT` is the set of satisfiable CNF formulas whose clauses each have at most three literal
occurrences. -/
def ThreeSAT : Set Formula :=
  {φ | (∀ c ∈ φ, c.length ≤ 3) ∧ Satisfiable φ}

/-- The number of distinct variables occurring in a CNF formula `φ`. -/
def numVars (φ : Formula) : ℕ :=
  (φ.flatten.map Prod.fst).toFinset.card

/-! ## Representation details

Formulas and partial-function MCSP instances are serialized using the self-delimiting framing
combinators in `ComplexityAbstracts.Encoding`. For `PartialMCSP`, the `2 ^ arity` entries of the
partial truth table are listed in standard binary order (`List.ofFn x.table`), with `none` (`*`)
encoded as the empty word `[]` and `some b` encoded as `[true, b]`. We provide both `encInstance`
(unary threshold `1 ^ threshold`) and `encInstanceBinary` (binary threshold `Nat.bits threshold`).
-/

/-- Encode a CNF formula as a framed list of clauses of `(Nat.bits v, [b])` literals. -/
def encodeCNF : Formula → List Bool :=
  ComplexityTests.Abstracts.Encoding.encodeList
    (ComplexityTests.Abstracts.Encoding.encodeList
      (ComplexityTests.Abstracts.Encoding.encodePair Nat.bits (fun b => [b])))

theorem encodeCNF_injective : Function.Injective encodeCNF :=
  PartialMCSPBridge.encodeCNF_injective

/-- Injective framed binary encoding of CNF formulas. -/
def encCNF : Formula ↪ List Bool :=
  ⟨encodeCNF, encodeCNF_injective⟩

/-- Encode an optional Boolean: `none` (`*`) is `[]` and `some b` is `[true, b]`. -/
def encodeOptionBool (o : Option Bool) : List Bool :=
  o.elim [] (fun b => [true, b])

/-- An instance of the Partial Minimum Circuit Size Problem (`MCSP*`): an input arity `arity`, a
partial truth table `table : Fin (2 ^ arity) → Option Bool` (`some b` for a required output `b` and
`none` for a don't-care entry `*`), and a gate-count threshold `threshold`. -/
structure Instance where
  arity : ℕ
  table : Fin (2 ^ arity) → Option Bool
  threshold : ℕ

/-- Encode a `PartialMCSP` instance as the framed list of its `2 ^ arity` truth-table entries
followed by `threshold` in unary (`List.replicate x.threshold true`). -/
def encodeInstance (x : Instance) : List Bool :=
  ComplexityTests.Abstracts.Encoding.encodePair
    (ComplexityTests.Abstracts.Encoding.encodeList encodeOptionBool)
    (fun s => List.replicate s true)
    (List.ofFn x.table, x.threshold)

theorem encodeInstance_injective : Function.Injective encodeInstance := by
  intro ⟨n₁, T₁, s₁⟩ ⟨n₂, T₂, s₂⟩ h
  cases PartialMCSPBridge.eq_of_encodeRawUnary_eq h
  rfl

/-- Injective encoding of `PartialMCSP` instances with unary threshold. -/
def encInstance : Instance ↪ List Bool :=
  ⟨encodeInstance, encodeInstance_injective⟩

/-- Encode a `PartialMCSP` instance as the framed list of its `2 ^ arity` truth-table entries
followed by `threshold` in binary (`Nat.bits x.threshold`). -/
def encodeInstanceBinary (x : Instance) : List Bool :=
  ComplexityTests.Abstracts.Encoding.encodePair
    (ComplexityTests.Abstracts.Encoding.encodeList encodeOptionBool)
    Nat.bits
    (List.ofFn x.table, x.threshold)

theorem encodeInstanceBinary_injective : Function.Injective encodeInstanceBinary := by
  intro ⟨n₁, T₁, s₁⟩ ⟨n₂, T₂, s₂⟩ h
  cases PartialMCSPBridge.eq_of_encodeRawBinary_eq h
  rfl

/-- Injective encoding of `PartialMCSP` instances with binary threshold. -/
def encInstanceBinary : Instance ↪ List Bool :=
  ⟨encodeInstanceBinary, encodeInstanceBinary_injective⟩

/-! ## Parameterized time bounds and ETH

A decision problem `A` with encoding `enc` is decidable in time `O(T a)` when a single
deterministic binary multi-tape Turing machine with finitely many states decides `A` and halts on
every instance `a` within `c * T a + c` steps for a fixed constant `c`. Subexponential time in
parameter `μ` means decidability in time `2 ^ (δ * μ a) * (|enc a| + 1) ^ e` for every real
exponent `δ > 0` (where the machine and polynomial degree `e` may depend on `δ`).
-/

/-- A decision problem `A` is decidable in time `O(T a)` on a deterministic finite-state binary
multi-tape Turing machine. -/
def DecidableInTimeO {α : Type} (A : Set α) (enc : α ↪ List Bool) (T : α → ℝ) : Prop :=
  ∃ c : ℕ, ∃ t s : α → ℕ,
    (∀ a, (t a : ℝ) ≤ c * T a + c) ∧
    Turing.MultiTapeTM.DecidableInTimeAndSpace A enc t s

/-- `A` is decidable in time `2 ^ (δ * μ a)` times a polynomial in the encoded input length
`|enc a|`. -/
def DecidableInExpTime {α : Type} (A : Set α) (enc : α ↪ List Bool) (μ : α → ℕ) (δ : ℝ) : Prop :=
  ∃ e : ℕ, DecidableInTimeO A enc fun a => 2 ^ (δ * μ a) * ((enc a).length + 1) ^ e

/-- `A` is decidable in subexponential time `2 ^ o(μ a) * poly(|enc a|)`: for every `δ > 0`, some
deterministic machine decides `A` in time `2 ^ (δ * μ a) * poly(|enc a|)`. -/
def DecidableInSubexpTime {α : Type} (A : Set α) (enc : α ↪ List Bool) (μ : α → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → DecidableInExpTime A enc μ δ

/-- **The Exponential Time Hypothesis (`ETH`)** ([Impagliazzo and Paturi][ImpagliazzoPaturi2001]):
there is a real constant `δ > 0` such that `ThreeSAT` cannot be decided in time
`2 ^ (δ * numVars φ) * poly(|encCNF φ|)`. -/
def ETH : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ¬DecidableInExpTime ThreeSAT encCNF numVars δ

/-! ## De Morgan circuits and the Partial Minimum Circuit Size Problem

A De Morgan circuit on `n` input variables has binary AND/OR gates, unary NOT gates, and Boolean
constant gates. We consider both the standard all-gates size `C.size` and Ilango's binary-gate
count `binaryGateCount C`, which charges `1` for each binary AND or OR gate and `0` for NOT and
constant gates. Truth tables of `n`-variable partial functions have length
`tableSize x = 2 ^ x.arity`, indexed by `tableIndex n` with coordinate zero least significant.
-/

/-- A single-output Boolean circuit on `n` input bits over the De Morgan basis. -/
abbrev DeMorganCircuit (n : ℕ) :=
  Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature n 1

/-- The Boolean value computed at output wire `0` of a De Morgan circuit `C` on input `x`. -/
def evalCircuit {n : ℕ} (C : DeMorganCircuit n) (x : Fin n → Bool) : Bool :=
  C.eval Cslib.Circuits.Boolean.interpretation x 0

/-- The number of binary AND and OR gates in a De Morgan circuit `C` (with unary NOT and constant
gates counted as free). -/
def binaryGateCount {n : ℕ} (C : DeMorganCircuit n) : ℕ :=
  C.program.cost (fun op : Cslib.Circuits.Boolean.Op =>
    match op with | .and | .or => 1 | .const _ | .not => 0)

/-- The binary number in `Fin (2 ^ n)` represented by `bits : Fin n → Bool`, with coordinate zero
least significant: its value is `∑ i, (if bits i then 1 else 0) * 2 ^ i`. -/
def tableIndex (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The truth-table index of `bits` is its standard binary value with bit zero least significant. -/
theorem tableIndex_val {n : ℕ} (bits : Fin n → Bool) :
    (tableIndex n bits).val = ∑ i : Fin n, (if bits i then 1 else 0) * 2 ^ i.val :=
  PartialMCSPBridge.tableIndex_val bits

/-- The number of entries `N = 2 ^ x.arity` in the partial truth table of `x`. -/
def tableSize (x : Instance) : ℕ :=
  2 ^ x.arity

/-- A De Morgan circuit `C` agrees with (extends) a partial truth table `x` if for every input
`y : Fin x.arity → Bool` and Boolean `b`, whenever `x.table` specifies `some b` at `y`, `C` outputs
`b` on `y`. -/
def AgreesWith (x : Instance) (C : DeMorganCircuit x.arity) : Prop :=
  ∀ y : Fin x.arity → Bool, ∀ b : Bool,
    x.table (tableIndex x.arity y) = some b → evalCircuit C y = b

/-- **The Partial Minimum Circuit Size Problem (`PartialMCSP` / `MCSP*`)** under the all-gates
De Morgan circuit size `C.size`: instances `x` for which some De Morgan circuit with at most
`x.threshold` gates agrees with `x`. -/
def PartialMCSP : Set Instance :=
  {x | ∃ C : DeMorganCircuit x.arity, C.size ≤ x.threshold ∧ AgreesWith x C}

/-- **The Partial Minimum Circuit Size Problem under the binary-gate cost measure**
([Ilango][Ilango2020FOCS]): instances `x` for which some De Morgan circuit with at most
`x.threshold` binary AND/OR gates agrees with `x`. -/
def PartialMCSPBinaryGate : Set Instance :=
  {x | ∃ C : DeMorganCircuit x.arity, binaryGateCount C ≤ x.threshold ∧ AgreesWith x C}

/-- A function `V : α × List Bool → Bool` verifies a decision problem `A` with certificate-length
polynomial `p` if `a ∈ A` holds exactly when some certificate `w` of length `p(|enc a|)` is
accepted by `V`. -/
def IsVerifier {α : Type} (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true

/-- The class `NP` of decision problems with polynomial-length binary certificates verified in
polynomial time by a deterministic multi-tape Turing machine. -/
def NP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComplexityTests.Abstracts.Computation.PolyTimeVerifier enc V ∧ IsVerifier enc p V A}

/-! ## Main results -/

/-- **Theorem (Ilango, ETH lower bound for `PartialMCSP` in arity `m`)**
([Ilango, FOCS 2020, Theorem I.3; ECCC TR20-183, Theorem 3 and Theorem 11][Ilango2020FOCS]):
assuming `ETH`, `PartialMCSP` on `m`-variable partial Boolean functions cannot be decided in
subexponential time `2 ^ o(m log₂ m)` (under unary threshold encoding `encInstance`). -/
theorem not_decidableInSubexpTime_partialMCSP (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSP encInstance
      (fun x => x.arity * Nat.log 2 x.arity) :=
  PartialMCSPBridge.not_decidableInSubexpTime_partialMCSP
    ⟨fun x : Instance => ⟨x.arity, x.table, x.threshold⟩,
      fun x : Cslib.PartialMCSP.Instance => ⟨x.arity, x.table, x.threshold⟩,
      fun _ => rfl, fun _ => rfl⟩
    (fun _ => Iff.rfl) (fun _ => rfl) (fun _ => rfl) h

/-- **Corollary (Ilango, ETH lower bound for `PartialMCSP` in truth-table size `N = 2 ^ m`)**
([Ilango, FOCS 2020, Theorem I.3; ECCC TR20-183, Theorem 3][Ilango2020FOCS]):
assuming `ETH`, `PartialMCSP` on partial truth tables of size `N = tableSize x = 2 ^ x.arity`
cannot be decided in time `2 ^ o(log₂ N * log₂ (log₂ N)) = N ^ o(log log N)`. -/
theorem not_decidableInSubexpTime_partialMCSP_tableSize (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSP encInstance
      (fun x => Nat.log 2 (tableSize x) * Nat.log 2 (Nat.log 2 (tableSize x))) :=
  PartialMCSPBridge.not_decidableInSubexpTime_partialMCSP_tableSize
    ⟨fun x : Instance => ⟨x.arity, x.table, x.threshold⟩,
      fun x : Cslib.PartialMCSP.Instance => ⟨x.arity, x.table, x.threshold⟩,
      fun _ => rfl, fun _ => rfl⟩
    (fun _ => Iff.rfl) (fun _ => rfl) (fun _ => rfl) h

/-- **Theorem (Ilango, ETH lower bound for `PartialMCSP` under binary threshold encoding):**
assuming `ETH`, `PartialMCSP` cannot be decided in time `2 ^ o(m log₂ m)` when the size threshold
is encoded in binary (`encInstanceBinary`). -/
theorem not_decidableInSubexpTime_partialMCSP_encBinary (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSP encInstanceBinary
      (fun x => x.arity * Nat.log 2 x.arity) :=
  PartialMCSPBridge.not_decidableInSubexpTime_partialMCSP_encBinary
    ⟨fun x : Instance => ⟨x.arity, x.table, x.threshold⟩,
      fun x : Cslib.PartialMCSP.Instance => ⟨x.arity, x.table, x.threshold⟩,
      fun _ => rfl, fun _ => rfl⟩
    (fun _ => Iff.rfl) (fun _ => rfl) (fun _ => rfl) h

/-- **Theorem (Ilango, ETH lower bound for `PartialMCSPBinaryGate`):**
assuming `ETH`, deciding whether a partial Boolean function has a De Morgan circuit with at most
`threshold` binary AND/OR gates (`PartialMCSPBinaryGate`) cannot be done in time
`2 ^ o(m log₂ m)`. -/
theorem not_decidableInSubexpTime_partialMCSPBinaryGate (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSPBinaryGate encInstance
      (fun x => x.arity * Nat.log 2 x.arity) :=
  PartialMCSPBridge.not_decidableInSubexpTime_partialMCSPBinaryGate
    ⟨fun x : Instance => ⟨x.arity, x.table, x.threshold⟩,
      fun x : Cslib.PartialMCSP.Instance => ⟨x.arity, x.table, x.threshold⟩,
      fun _ => rfl, fun _ => rfl⟩
    (fun _ => Iff.rfl) (fun _ => rfl) (fun _ => rfl) h

/-- **`PartialMCSP` belongs to `NP` (unary threshold encoding `encInstance`).** -/
theorem partialMCSP_mem_NP : PartialMCSP ∈ NP encInstance :=
  PartialMCSPBridge.partialMCSP_mem_NP
    ⟨fun x : Instance => ⟨x.arity, x.table, x.threshold⟩,
      fun x : Cslib.PartialMCSP.Instance => ⟨x.arity, x.table, x.threshold⟩,
      fun _ => rfl, fun _ => rfl⟩
    (fun _ => Iff.rfl) (fun _ => rfl)

/-- **`PartialMCSP` belongs to `NP` (binary threshold encoding `encInstanceBinary`).** -/
theorem partialMCSP_mem_NP_encBinary : PartialMCSP ∈ NP encInstanceBinary :=
  PartialMCSPBridge.partialMCSP_mem_NP_encBinary
    ⟨fun x : Instance => ⟨x.arity, x.table, x.threshold⟩,
      fun x : Cslib.PartialMCSP.Instance => ⟨x.arity, x.table, x.threshold⟩,
      fun _ => rfl, fun _ => rfl⟩
    (fun _ => Iff.rfl) (fun _ => rfl)

/--
info: abstract audit passed for `ComplexityAbstracts.PartialMCSPAbstract`:
60 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.PartialMCSPAbstract allowing [
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation
]

end ComplexityAbstracts.PartialMCSPAbstract
