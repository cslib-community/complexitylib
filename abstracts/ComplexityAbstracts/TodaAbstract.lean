/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import ComplexityAbstracts.TodaBridge

/-! # Toda's theorem

Counting accepting certificates can be much more powerful than asking whether even one exists.
Toda shows that a deterministic algorithm with an exact counting oracle can decide every problem
specified by a fixed finite alternation of polynomially bounded existential and universal choices.
The proof first expresses these choices through randomized parity tests, then encodes their
majority verdict in a binary digit of a witness count. This gives containment of the polynomial
hierarchy in polynomial time with counting access, without asserting the reverse containment.

The oracle counts certificates accepted by a deterministic verifier in polynomial time and answers
queries about individual binary digits. One native polynomial clock governs the entire stateful
interaction, including constructing queries and reading replies. Correctness holds for every
extension of valid bit answers to words outside the query encoding's image. The decision program
is deterministic. Its resource bound is expressed by exact realization on a clocked fair-coin
machine; the same interaction interface also supports randomized programs.

The definitions and theorem statement below specify the claim. Lean checks the bridge, and
besides the shared foundations the audit permits only the following eight foundational program and
machine modules, with no complexity-class or Toda-theorem allowance:
* under `Computability.Machines.Turing.MultiTape`: `Machine` (machines whose oracle channels
  have a write-only query buffer and a read-only reply tape), `Machine.Program` (a clocked run as
  a typed program), `Probabilistic` (one fresh fair coin per live instruction) and
  `Probabilistic.Oracle` (fair-coin runs with external oracle calls);
* under `Languages.Probabilistic`: `Basic` (terminating programs with typed calls, whose only
  randomness is uniform choice from a finite range), `Oracle` (private coins beside external
  calls), `Sum` (sums of oracle interfaces) and `Oracle.Interaction` (runs against a stateful
  randomized oracle).

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

namespace ComplexityTests.Abstracts.TodaAbstract

/-- Count the accepted binary strings of exactly `n` bits. -/
def acceptCount {α : Type} (V : α × List Bool → Bool) (a : α) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Bool => V (a, List.ofFn w) = true).card

/-- A #P function counts witnesses of a fixed polynomial length accepted by one total
polynomial-time deterministic verifier. Counts are natural numbers in binary. -/
def SharpP {α : Type} (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    Computation.PolyTimeVerifier enc V ∧
    ∀ a, f a = acceptCount V a (p.eval (enc a).length)}

/-- Alternating quantifiers over fixed-length blocks of bits, with an existential first
quantifier when `q=true`. Each subsequent block has the opposite quantifier. -/
def Alternation : Bool → List ℕ → (List Bool → Prop) → Prop
  | _, [], V => V []
  | true, n :: ns, V => ∃ w : List Bool, w.length = n ∧ Alternation false ns (fun v => V (w ++ v))
  | false, n :: ns, V => ∀ w : List Bool, w.length = n → Alternation true ns (fun v => V (w ++ v))

/-- The polynomial hierarchy: a fixed finite number of alternating polynomial-length
certificate blocks followed by a total polynomial-time verifier. The number of alternations
and the length polynomials are fixed for the language, not supplied as part of an instance. -/
def PH {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (ps : List (Polynomial ℕ)) (V : α × List Bool → Bool),
    Computation.PolyTimeVerifier enc V ∧
    ∀ a, a ∈ A ↔ Alternation true (ps.map (fun p => p.eval (enc a).length))
      (fun w => V (a, w) = true)}

/-! The counting oracle is accessed by a deterministic program: it can return an answer or make
a word query, and later queries may depend on earlier replies. The probabilistic interface below
is used only to state its machine resource contract; it adds no random operation to this program.
-/

/-- Deterministic word-query programs; the syntax has queries but no random operation. -/
abbrev QueryProgram (β : Type) := Cslib.OracleComp (fun _ : Unit × List Bool => List Bool) β

/-- A terminating return/request tree. A private request indexed by `n` draws a fresh uniform
`Fin (n+1)`; an external request sends `((), word)` and receives a word. Private draws do not
change the oracle's state. Bare syntax imposes no efficiency or fair-coin implementability:
those are required separately by `StrictOraclePPT`. -/
abbrev InteractiveProgram (β : Type) :=
  Cslib.ProbOracleComp (fun _ : Unit × List Bool => List Bool) β

/-- One fixed finite fair-coin machine and one polynomial clock realize the entire joint law
of the program's encoded result and the oracle's final state, against every stateful oracle.
The clock charges computation, query writing, reply access and output writing. Each instruction
costs one unit; oracle computation is external. The bounded run returns its written output on
halting or clock exhaustion; it does not require the unclocked machine to halt. -/
def StrictOraclePPT {α β : Type} (enc : α ↪ List Bool) (out : β ↪ List Bool)
    (program : α → InteractiveProgram β) : Prop :=
  ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Unit) (c d : ℕ),
    ∀ a (State : Type)
      (oracle : Unit × List Bool → StateT State PMF (List Bool)) s,
      Cslib.ProbOracleComp.runWith oracle (out <$> program a) s =
        Cslib.ProbOracleComp.runWith oracle
          (machine.runOracle (c * ((enc a).length + 1) ^ d) (enc a)) s

/-- An oracle language replies to each requested word with its one-bit membership verdict. -/
noncomputable def languageOracle (B : Set (List Bool)) (q : Unit × List Bool) : List Bool :=
  [@decide (q.2 ∈ B) (Classical.propDecidable _)]

/-- An oracle language answers the bits of `f`: every valid query `(b,i)` returns the `i`th
binary digit. Answers to words outside the encoding image are unrestricted. -/
def AnswersBits {β : Type} (enc : β ↪ List Bool) (f : β → ℕ)
    (B : Set (List Bool)) : Prop :=
  ∀ b i, Encoding.encPair enc Encoding.encNat (b, i) ∈ B ↔ (f b).testBit i

/-- Deterministic polynomial time with a #P oracle, via bit queries. The program must decide
the language against every extension of the valid bit answers to malformed query words.
Its native machine clock is polynomial uniformly over every stateful oracle. Interpreting each
query through `ProbOracleComp.query` embeds the deterministic program into the shared interaction
model without drawing coins. The machine must realize that program's entire joint law exactly. -/
def PWithSharpPOracle {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (β : Type) (b : β ↪ List Bool) (f : β → ℕ), f ∈ SharpP b ∧
    ∃ program : α → QueryProgram Bool,
      StrictOraclePPT enc Encoding.encBool
        (fun a => Cslib.OracleComp.interpret Cslib.ProbOracleComp.query (program a)) ∧
      ∀ B : Set (List Bool), AnswersBits b f B →
        ∀ a, a ∈ A ↔ Cslib.OracleComp.interpret (m := Id) (languageOracle B) (program a) = true}

/-- Every problem in the polynomial hierarchy is decidable by a deterministic polynomial-time
oracle program with bit access to a #P function, with uniform native efficiency. -/
theorem toda {α : Type} (enc : α ↪ List Bool) : PH enc ⊆ PWithSharpPOracle enc := by
  have hgame (q : Bool) (ns : List ℕ) (V : List Bool → Prop) :
      Alternation q ns V ↔ TodaBridge.Alternation q ns V := by
    induction ns generalizing q V with
    | nil => cases q <;> rfl
    | cons n ns ih =>
      cases q
      · exact forall_congr' fun w => imp_congr_right fun _ => ih _ _
      · exact exists_congr fun w => and_congr_right fun _ => ih _ _
  have hclass : PH enc = TodaBridge.PH enc := by
    ext A
    exact exists_congr fun ps => exists_congr fun V => and_congr_right fun _ =>
      forall_congr' fun a => iff_congr Iff.rfl (hgame _ _ _)
  rw [hclass]
  exact TodaBridge.toda enc

/-! ## Representation details

The fair-coin machine uses one independent fair bit at each live instruction to choose between
two transitions. Ordinary instructions perform an upstream tape action, append at most one bit
to a query buffer and move a read-only reply head by at most one cell. A query instruction submits
the buffer, installs the reply, resets the reply head and clears the buffer. Thus constructing a
query and accessing its answer are charged even though the oracle's own computation is external.
The output and final oracle state must agree for every handler, not just for the counting oracle.
-/

/--
info: abstract audit passed for `ComplexityTests.Abstracts.TodaAbstract`:
15 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.TodaAbstract allowing [
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation,
  Complexity.Computability.Machines.Turing.MultiTape.Machine,
  Complexity.Computability.Machines.Turing.MultiTape.Machine.Program,
  Complexity.Computability.Machines.Turing.MultiTape.Probabilistic,
  Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle,
  Complexity.Languages.Probabilistic.Basic,
  Complexity.Languages.Probabilistic.Oracle,
  Complexity.Languages.Probabilistic.Sum,
  Complexity.Languages.Probabilistic.Oracle.Interaction
]

end ComplexityTests.Abstracts.TodaAbstract
