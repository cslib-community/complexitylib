/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import ComplexityAbstracts.MagnificationBridge

/-! # McKay–Murray–Williams: barely superlinear circuit lower bounds for MCSP separate P from NP

Proving that an explicit `NP` problem requires superpolynomial Boolean circuits would separate
`P` from `NP`, yet the strongest known general-circuit lower bounds for explicit `NP` functions are
only linear in the input length. *Hardness magnification* shows that for the Minimum Circuit Size
Problem (`MCSP`), even a barely superlinear circuit lower bound on truth tables of length
`N = 2 ^ n` implies the full superpolynomial separation `¬ (NP ⊆ P/poly)`, and hence `P ≠ NP`.

The proof follows [McKay, Murray, and Williams, Lemma 3.1 and Section 5][McKayMurrayWilliams2019]:
they build circuits for `MCSP[s]` from a tree of `Circuit-Min-Merge` gates over the truth table
and, assuming `NP ⊆ P/poly`, replace each gate by a polynomial-size circuit. The library proof
adapts this construction to the binary tree of subcubes of `{0, 1} ^ n`. Its merge problem is a
language in the polynomial hierarchy. It receives a subcube and, for each of its two halves, a
validity bit and a fixed-threshold certificate: a bit string of a length fixed by `n` and `s(n)`
that describes a circuit with at most `s(n)` gates. It outputs the lexicographically least valid
certificate of this kind that agrees with both halves, rather than a minimum-size circuit. The
language is defined by polynomially bounded existential and universal quantifiers over
polynomial-time predicates. Under `NP ⊆ P/poly`, polynomial-size circuits are closed under such
quantifiers (the argument that places the whole polynomial hierarchy in `P/poly`), so the merge
problem has polynomial-size circuits. Composing these merge circuits along the tree yields a circuit
of size `2 ^ n * poly(n + s(n))` that decides `MCSP[s]` on `2 ^ n`-bit truth tables.
Contrapositively, if for some polynomial threshold `s(n) = n ^ k` and every exponent `c > 0`,
deciding `MCSP[n ^ k]` on `N = 2 ^ n`-bit truth tables requires more than
`N * c * (n + 1) ^ c = N * O((log₂ N) ^ c)` gates at some arity `n` (equivalently, infinitely often,
since each fixed arity has finite circuit complexity), then `¬ (NP ⊆ P/poly)` and `P ≠ NP`.

These statements specialize the third bullet of
[McKay, Murray, and Williams, Theorem 1.4][McKayMurrayWilliams2019], which assumes that
`search-MCSP^A[s(n)]`, for an oracle `A` in the polynomial hierarchy, has no circuits of size
`N * poly(s(n))` and depth `poly(s(n))`. Here `MCSP` has no oracle, the problem is the decision
version, and the lower bound constrains size alone. A decision lower bound implies a search lower
bound, and a size-only lower bound implies a size-and-depth lower bound, so these hypotheses are
stronger and the theorems are special cases of the source. Likewise, the upper bound under
`NP ⊆ P/poly` gives decision circuits with a size bound only; it asserts no search circuits and no
depth bound.

Circuits use the standard De Morgan basis of binary AND/OR, unary NOT, and Boolean constants, and
`C.size` counts every operation gate, constants included. Truth tables of `n`-variable Boolean
functions have length `2 ^ n`, indexed in standard binary order with coordinate zero least
significant. The complexity classes `P`, `NP`, and `P/poly` are defined over bit-string languages
using the shared native multi-tape Turing machine foundations in the appendix. Lean verifies the
proofs through `MagnificationBridge.lean`, and `#check_abstract` audits that all public statements
depend only on this file, the displayed shared foundations, and upstream mathematics.

## References

* [D. M. McKay, C. D. Murray, R. R. Williams, *Weak lower bounds on resource-bounded compression
  imply strong separations of complexity classes*, STOC 2019, Lemma 3.1 and Theorem 1.4]
  [McKayMurrayWilliams2019]
* [V. Kabanets, J.-Y. Cai, *Circuit minimization problem*, STOC 2000][KabanetsCai2000]
-/

namespace ComplexityAbstracts.MagnificationAbstract

/-! ## De Morgan circuits and the Minimum Circuit Size Problem -/

/-- A single-output Boolean circuit on `n` input bits over the De Morgan basis (binary AND/OR,
unary NOT, and Boolean constants). Every operation gate costs one in `C.size`. -/
abbrev DeMorganCircuit (n : ℕ) :=
  Cslib.Circuits.Circuit Cslib.Circuits.Boolean.signature n 1

/-- The Boolean value computed at the sole output wire of a De Morgan circuit `C` on input `x`. -/
def evalCircuit {n : ℕ} (C : DeMorganCircuit n) (x : Fin n → Bool) : Bool :=
  C.eval Cslib.Circuits.Boolean.interpretation x 0

/-- A De Morgan circuit `C` computes `f : (Fin n → Bool) → Bool` if it agrees with `f` on every
`n`-bit input. -/
def ComputesFunction {n : ℕ} (C : DeMorganCircuit n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, evalCircuit C x = f x

/-- A Boolean function `f : (Fin n → Bool) → Bool` has a De Morgan circuit with at most `k`
operation gates. -/
def HasCircuitOfSize {n : ℕ} (f : (Fin n → Bool) → Bool) (k : ℕ) : Prop :=
  ∃ C : DeMorganCircuit n, ComputesFunction C f ∧ C.size ≤ k

/-- The binary number in `Fin (2 ^ n)` represented by `bits : Fin n → Bool`, with coordinate zero
least significant: its value is `∑ i, (if bits i then 1 else 0) * 2 ^ i`. -/
def tableIndex (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The truth-table index of `bits` is its standard binary value with bit zero least significant. -/
theorem tableIndex_val {n : ℕ} (bits : Fin n → Bool) :
    (tableIndex n bits).val = ∑ i : Fin n, (if bits i then 1 else 0) * 2 ^ i.val :=
  MagnificationBridge.tableIndex_val bits

/-- The `n`-variable Boolean function represented by a `2 ^ n`-bit truth table `T`. -/
def tableFunction {n : ℕ} (T : Fin (2 ^ n) → Bool) (x : Fin n → Bool) : Bool :=
  T (tableIndex n x)

/-- A circuit `C : DeMorganCircuit (2 ^ n)` decides the `2 ^ n`-bit slice of `MCSP[s]` if for every
truth table `T : Fin (2 ^ n) → Bool`, `C` outputs `true` on `T` if and only if `tableFunction T`
has a De Morgan circuit with at most `s n` gates. -/
def DecidesMCSPSlice {n : ℕ} (C : DeMorganCircuit (2 ^ n)) (s : ℕ → ℕ) : Prop :=
  ∀ T : Fin (2 ^ n) → Bool,
    evalCircuit C T = true ↔ HasCircuitOfSize (tableFunction T) (s n)

/-! ## Uniform and nonuniform complexity classes

`Computation.PolyTime` and `Computation.PolyTimeVerifier` specify total polynomial-time computation
on a single deterministic finite-state binary multi-tape Turing machine; their definitions appear in
the foundations appendix. In contrast, `PPoly` is nonuniform: a separate circuit may be chosen for
each input length `m`, without any machine that constructs the circuit family.
-/

/-- The class `P` of bit-string languages decidable in polynomial time by a deterministic
multi-tape Turing machine. -/
def P : Set (Set (List Bool)) :=
  {A | ∃ f : List Bool → Bool,
    ComplexityTests.Abstracts.Computation.PolyTime f
      ComplexityTests.Abstracts.Encoding.encBits
      ComplexityTests.Abstracts.Encoding.encBool ∧
    ∀ w, w ∈ A ↔ f w = true}

/-- A function `V : List Bool × List Bool → Bool` verifies a bit-string language `A` with
certificate length polynomial `p` if `x ∈ A` holds exactly when there is a binary certificate `w`
of length `p(|x|)` accepted by `V`. -/
def IsVerifier (p : Polynomial ℕ) (V : List Bool × List Bool → Bool)
    (A : Set (List Bool)) : Prop :=
  ∀ x, x ∈ A ↔ ∃ w : List Bool, w.length = p.eval x.length ∧ V (x, w) = true

/-- The class `NP` of bit-string languages with polynomial-length certificates verified in
polynomial time by a deterministic multi-tape Turing machine. -/
def NP : Set (Set (List Bool)) :=
  {A | ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    ComplexityTests.Abstracts.Computation.PolyTimeVerifier
      ComplexityTests.Abstracts.Encoding.encBits V ∧
    IsVerifier p V A}

/-- The nonuniform class `P/poly` of bit-string languages decided at each input length `m` by a
De Morgan circuit whose gate count is bounded by a polynomially bounded function of `m`. -/
def PPoly : Set (Set (List Bool)) :=
  {A | ∃ size : ℕ → ℕ, Cslib.PolynomiallyBounded size ∧ ∀ m,
    ∃ C : DeMorganCircuit m,
      (∀ x : Fin m → Bool, evalCircuit C x = true ↔ List.ofFn x ∈ A) ∧
      C.size ≤ size m}

/-! ## Main results -/

/-- **McKay–Murray–Williams circuit upper bound for `MCSP[s]` under `NP ⊆ P/poly`**
([McKay, Murray, and Williams, Lemma 3.1 and Section 5][McKayMurrayWilliams2019]):
if every `NP` language has polynomial-size circuits (`NP ⊆ PPoly`), then there is a constant `c > 0`
such that for every size schedule `s : ℕ → ℕ` and every arity `n`, some De Morgan circuit of size
at most `2 ^ n * c * (n + s n + 1) ^ c` decides `MCSP[s]` on `2 ^ n`-bit truth tables. -/
theorem mcsp_circuit_of_np_subset_ppoly (hNP : NP ⊆ PPoly) :
    ∃ c > 0, ∀ (s : ℕ → ℕ) (n : ℕ),
      ∃ C : DeMorganCircuit (2 ^ n),
        DecidesMCSPSlice C s ∧ C.size ≤ 2 ^ n * c * (n + s n + 1) ^ c :=
  MagnificationBridge.mcsp_circuit_of_np_subset_ppoly hNP

/-- **McKay–Murray–Williams circuit upper bound for `MCSP[n ^ k]` under `NP ⊆ P/poly`**
([McKay, Murray, and Williams, Section 5][McKayMurrayWilliams2019]):
if `NP ⊆ PPoly`, then for every degree `k`, there is `c > 0` such that for every `n`, some
De Morgan circuit of size at most `2 ^ n * c * (n + 1) ^ c` decides `MCSP[fun m => m ^ k]` on
`2 ^ n`-bit truth tables. -/
theorem mcsp_pow_circuit_of_np_subset_ppoly (hNP : NP ⊆ PPoly) (k : ℕ) :
    ∃ c > 0, ∀ n : ℕ,
      ∃ C : DeMorganCircuit (2 ^ n),
        DecidesMCSPSlice C (fun m => m ^ k) ∧ C.size ≤ 2 ^ n * c * (n + 1) ^ c :=
  MagnificationBridge.mcsp_pow_circuit_of_np_subset_ppoly hNP k

/-- **Theorem (McKay–Murray–Williams, hardness magnification to `¬ (NP ⊆ P/poly)`):**
if for some polynomial threshold degree `k` and every exponent `c > 0`, there is an arity `n` at
which every De Morgan circuit deciding `MCSP[fun m => m ^ k]` on `2 ^ n`-bit truth tables has more
than `2 ^ n * c * (n + 1) ^ c` gates, then `¬ (NP ⊆ P/poly)`. -/
theorem np_not_subset_ppoly_of_mcsp_hard (k : ℕ)
    (h : ∀ c > 0, ∃ n : ℕ, ∀ C : DeMorganCircuit (2 ^ n),
      DecidesMCSPSlice C (fun m => m ^ k) → 2 ^ n * c * (n + 1) ^ c < C.size) :
    ¬ (NP ⊆ PPoly) :=
  MagnificationBridge.np_not_subset_ppoly_of_mcsp_hard k h

/-- **Corollary (McKay–Murray–Williams, hardness magnification to `P ≠ NP`):**
if for some polynomial threshold degree `k` and every exponent `c > 0`, there is an arity `n` at
which every De Morgan circuit deciding `MCSP[fun m => m ^ k]` on `2 ^ n`-bit truth tables has more
than `2 ^ n * c * (n + 1) ^ c` gates, then `P ≠ NP`. -/
theorem p_ne_np_of_mcsp_hard (k : ℕ)
    (h : ∀ c > 0, ∃ n : ℕ, ∀ C : DeMorganCircuit (2 ^ n),
      DecidesMCSPSlice C (fun m => m ^ k) → 2 ^ n * c * (n + 1) ^ c < C.size) :
    P ≠ NP :=
  MagnificationBridge.p_ne_np_of_mcsp_hard k h

/--
info: abstract audit passed for `ComplexityAbstracts.MagnificationAbstract`:
17 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.MagnificationAbstract allowing [
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation
]

end ComplexityAbstracts.MagnificationAbstract
