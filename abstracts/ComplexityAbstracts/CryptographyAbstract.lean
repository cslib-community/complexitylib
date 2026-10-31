/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import ComplexityAbstracts.Randomized
import ComplexityAbstracts.CryptographyBridge

/-! # One-way functions, generators and adaptive pseudorandom functions

A one-way function is easy to compute, but finding any preimage of its output on a random input
is hard for every efficient randomized algorithm. Assuming such a function, the
Håstad–Impagliazzo–Levin–Luby construction produces a generator whose output is one bit longer
than its seed and computationally indistinguishable from uniform bits. The
Goldreich–Goldwasser–Micali construction then produces a keyed function that looks like one
consistently chosen random function even when each query depends on earlier answers.
Existence of a one-way function remains a hypothesis; efficiency and security use uniform
finite-control machines with strict polynomial bounds and independent fair coins. These
conventions, `Randomized.StrictPPT`, `Randomized.Negligible` and `Randomized.Indistinguishable`,
are the shared foundations displayed in the appendix.
The definitions and theorem statements below specify the claim; Lean checks their proofs through
`CryptographyBridge`. Besides the shared foundations, the audit allows only the following eight
foundational program, interpretation and machine modules across the implementation boundary,
without importing a security definition:
* under `Computability.Machines.Turing.MultiTape`: `Machine` (machines whose oracle channels
  have a write-only query buffer and a read-only reply tape), `Machine.Program` (a clocked run as
  a typed program), `Probabilistic` (one fresh fair coin per live instruction) and
  `Probabilistic.Oracle` (fair-coin runs with external oracle calls);
* under `Languages.Probabilistic`: `Basic` (terminating programs with typed calls, whose only
  randomness is uniform choice from a finite range), `Oracle` (private coins beside external
  calls), `Sum` (sums of oracle interfaces) and `Oracle.Interaction` (runs against a stateful
  randomized oracle).

## References

* [J. Håstad, R. Impagliazzo, L. Levin, M. Luby,
  *A Pseudorandom Generator from Any One-Way Function*][HILL1999]
* [T. Holenstein, *Pseudorandom Generators from One-Way Functions*][Holenstein2006], Sections 4–5.
* [S. Arora, B. Barak, *Computational Complexity*][AroraBarak09], Chapter 9.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 3.
* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986]

The typed oracle-program syntax follows VCVio, by Devon Tuma, Quang Dao and collaborators,
as credited in `Complexity.Languages.Probabilistic.Basic`.
-/

namespace ComplexityTests.Abstracts.CryptographyAbstract

/-- A polynomial-time function is one-way if every strict PPT inverter, given unary `n` and
`f(x)` for a uniform `n`-bit `x`, finds any preimage only with negligible probability.
The candidate's length is unrestricted, and recovering the sampled `x` is unnecessary. -/
def OneWay (f : List Bool → List Bool) : Prop :=
  Computation.PolyTime f Encoding.encBits Encoding.encBits ∧
    ∀ inverter : ℕ → List Bool → PMF (List Bool),
      Randomized.StrictPPT (Encoding.encPair Encoding.encUnary Encoding.encBits) Encoding.encBits
        (fun p => inverter p.1 p.2) →
      Randomized.Negligible (fun n => Randomized.probability (do
        let x ← Randomized.uniformBits n
        (inverter n (f x)).map fun candidate => f candidate == f x))

/-- A deterministic polynomial-time generator has exact seed-dependent output length,
strictly expands every length, and its uniform-seed outputs are indistinguishable from the
uniform distribution at that output length. The security parameter in both games is the
seed length. The function need not be injective. -/
def PseudorandomGenerator (g : List Bool → List Bool) (length : ℕ → ℕ) : Prop :=
  Computation.PolyTime g Encoding.encBits Encoding.encBits ∧
    (∀ seed, (g seed).length = length seed.length) ∧ (∀ n, n < length n) ∧
    Randomized.Indistinguishable (fun n => (Randomized.uniformBits n).map g)
      (fun n => Randomized.uniformBits (length n))

/-- **Håstad–Impagliazzo–Levin–Luby:** any uniform one-way function yields a deterministic
uniform polynomial-time generator stretching every `n`-bit seed to `n+1` bits. The proof follows
Holenstein's pseudoentropy route. No entropy estimate or nonuniform advice is an extra hypothesis;
the theorem does not assert optimized seed-length exponents or practical efficiency. -/
theorem hill {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ g : List Bool → List Bool, PseudorandomGenerator g (fun n => n + 1) :=
  CryptographyBridge.hill hf

/-- **Existence equivalence:** uniform one-way functions exist exactly when uniform
pseudorandom generators exist. This is a conditional equivalence, not an existence assertion. -/
theorem existence_equivalence :
    (∃ f : List Bool → List Bool, OneWay f) ↔
      ∃ (g : List Bool → List Bool) (length : ℕ → ℕ), PseudorandomGenerator g length :=
  CryptographyBridge.existence_equivalence

/-- **Polynomial stretch:** a one-bit generator yields any strictly larger output length
computable in polynomial time with unary input and output. The resulting algorithm remains
deterministic polynomial time and secure against the same uniform strict PPT tests. -/
theorem stretch {g : List Bool → List Bool}
    (hg : PseudorandomGenerator g (fun n => n + 1)) (target : ℕ → ℕ)
    (htarget : Computation.PolyTime target Encoding.encUnary Encoding.encUnary)
    (hgreater : ∀ n, n < target n) :
    ∃ g' : List Bool → List Bool, PseudorandomGenerator g' target :=
  CryptographyBridge.stretch hg target htarget hgreater

/-! ## Adaptive oracle tests and pseudorandom functions

A program is a terminating interaction tree. It can return a result, request an independent
uniform sample, or submit a word and branch on the oracle's reply. Its next requests may depend
on earlier replies. Termination alone gives no efficiency: the separate machine certificate
below charges ordinary computation, query writing, reply access and output writing.
-/

/-- Programs with private finite-uniform samples and one word-query channel. A request is
`((), word)` and its reply is a word. Sampling is independent of the external oracle; strict
fair-coin realizability is a separate requirement in `OraclePPT`. -/
abbrev OracleProgram (β : Type) :=
  Cslib.ProbOracleComp (fun _ : Unit × List Bool => List Bool) β

/-- Interpret a program against any shared stateful probabilistic handler. Fresh random draws
are independent of that handler and leave its private state unchanged; external requests can
update it. The result retains both the program's output and the final handler state. -/
noncomputable def execute {State β : Type} (program : OracleProgram β)
    (oracle : Unit × List Bool → StateT State PMF (List Bool)) (s : State) : PMF (β × State) :=
  Cslib.ProbOracleComp.runWith oracle program s

/-- One uniform finite-control oracle machine realizes the entire interaction, at a strict
polynomial clock in the encoded unary parameter and auxiliary input. Equality is required for
every handler and starting state, preserving the final state as well as the output. The
machine cannot return an arbitrarily long reply for free: access and output writing are charged.
Each instruction costs one unit; oracle computation is external. The clocked run returns its
written output on halting or clock exhaustion. The definition does not require the unclocked
machine to halt; this is not a mere bound on the number of oracle queries. -/
def OraclePPT (program : ℕ → List Bool → OracleProgram Bool) : Prop :=
  ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Unit) (c d : ℕ),
    ∀ n aux (State : Type) (oracle : Unit × List Bool → StateT State PMF (List Bool)) s,
      let input := Encoding.encPair Encoding.encUnary Encoding.encBits (n, aux)
      execute (Encoding.encBool <$> program n aux) oracle s =
        execute (machine.runOracle (c * (input.length + 1) ^ d) input) oracle s

/-- Run a program against a fixed deterministic word oracle, with independent private samples.
The handler has no changing state: `Unit` is its single state, discarded from the result. -/
noncomputable def evaluateOracle {β : Type} (program : OracleProgram β)
    (oracle : List Bool → List Bool) : PMF β :=
  (Cslib.ProbOracleComp.runWith
    (fun request => StateT.lift (PMF.pure (oracle request.2))) program ()).map Prod.fst

/-- The real experiment samples one uniform key and consistently answers every valid query
with that key's function. Wrong-length queries return the empty word. The adversary receives
unary `n` and an empty auxiliary input. -/
noncomputable def realPRF (family : List Bool → List Bool → List Bool)
    (adversary : ℕ → List Bool → OracleProgram Bool) (n : ℕ) : PMF Bool := do
  let key ← Randomized.uniformBits n
  evaluateOracle (adversary n [])
    (fun query => if query.length = n then family key query else [])

/-- The ideal experiment samples one entire uniform function from `n` bits to `n` bits and
reuses it across all adaptive calls. This is a probability specification; a lazy cache in the
implementation realizes the same law without constructing its exponential truth table.
Malformed queries are rejected in exactly the same way as in the real experiment. -/
noncomputable def idealPRF (adversary : ℕ → List Bool → OracleProgram Bool) (n : ℕ) : PMF Bool := do
  let table ← Cslib.Probability.PMF.uniformOfFintype ((Fin n → Bool) → Fin n → Bool)
  evaluateOracle (adversary n []) (fun query =>
    if query.length = n then List.ofFn (table fun i => query.getD i.val false) else [])

/-- A uniform adaptive pseudorandom function family has a deterministic polynomial-time keyed
evaluator, `n`-bit answers to valid `n`-bit queries under `n`-bit keys, and negligible advantage
between the preceding games for every one strict uniform adaptive oracle-PPT adversary. -/
def PseudorandomFunction (family : List Bool → List Bool → List Bool) : Prop :=
  Computation.PolyTime (fun p : List Bool × List Bool => family p.1 p.2)
    (Encoding.encPair Encoding.encBits Encoding.encBits) Encoding.encBits ∧
  (∀ key query, query.length = key.length → (family key query).length = key.length) ∧
  ∀ adversary : ℕ → List Bool → OracleProgram Bool, OraclePPT adversary →
    Randomized.Negligible (fun n => nndist (Randomized.probability (realPRF family adversary n))
      (Randomized.probability (idealPRF adversary n)))

/-- **One-way functions imply adaptive pseudorandom functions:** HILL, polynomial stretching
and the Goldreich–Goldwasser–Micali tree construction give an efficient family satisfying the
full adaptive contract above. No fixed query-list restriction or nonuniform advice is assumed. -/
theorem adaptive_functions {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ family : List Bool → List Bool → List Bool, PseudorandomFunction family :=
  CryptographyBridge.adaptive_functions hf

/-! ## Representation details

The binary multitape machine has finite control and one oracle channel with a write-only query
buffer and a read-only reply tape. An ordinary instruction performs an upstream tape action,
appends at most one bit to the query buffer and moves the reply head by at most one cell. A query
instruction submits the buffer, installs the reply, resets the reply head and clears the buffer.
Each live instruction uses one independent fair bit to select between two transitions. The
interpreter starts with blank work and communication tapes. Its clock bounds every run, including
query construction and reply access, while the handler's computation is external.
-/

/-- The underlying response family, retained for clients inspecting the program representation:
`.inl n` requests a fresh uniform `Fin (n+1)`; `.inr ((),word)` requests an external word reply. -/
abbrev OracleResponse : Sum ℕ (Unit × List Bool) → Type :=
  Cslib.probOracleSpec (fun _ : Unit × List Bool => List Bool)

/--
info: abstract audit passed for `ComplexityTests.Abstracts.CryptographyAbstract`: 15 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CryptographyAbstract allowing [
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation, ComplexityAbstracts.Randomized,
  Complexity.Languages.Probabilistic.Basic,
  Complexity.Languages.Probabilistic.Oracle,
  Complexity.Languages.Probabilistic.Sum,
  Complexity.Languages.Probabilistic.Oracle.Interaction,
  Complexity.Computability.Machines.Turing.MultiTape.Machine,
  Complexity.Computability.Machines.Turing.MultiTape.Machine.Program,
  Complexity.Computability.Machines.Turing.MultiTape.Probabilistic,
  Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
]

/--
info: 'ComplexityTests.Abstracts.CryptographyAbstract.hill' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexityTests.Abstracts.CryptographyAbstract.hill

/--
info: 'ComplexityTests.Abstracts.CryptographyAbstract.adaptive_functions' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexityTests.Abstracts.CryptographyAbstract.adaptive_functions

end ComplexityTests.Abstracts.CryptographyAbstract
