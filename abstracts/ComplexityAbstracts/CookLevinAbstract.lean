/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import ComplexityAbstracts.CookLevinBridge

/-! # Cook–Levin: satisfiability captures efficient verification

A proposed satisfying truth assignment is easy to check. Cook–Levin says that every problem
with short, efficiently checkable witnesses can be
translated into satisfiability in polynomial time. The translation describes a verifier's
computation by Boolean constraints: a satisfying assignment records an accepting computation.
Thus SAT is NP-complete, and its complement UNSAT is coNP-complete.

The definitions below specify CNF formulas, their binary encoding, total polynomial-time
reductions and native finite-state machine bounds. The claims are about asymptotic complexity,
not a fast practical SAT solver. Lean checks the bridge proofs; `#check_abstract` checks that the
statements use the definitions here, the displayed shared foundations, and upstream mathematics.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 2.3.
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94], Theorem 8.2.
-/

namespace ComplexityTests.Abstracts.CookLevinAbstract

/-! ## Propositional CNF formulas and satisfiability

A literal `(v, b)` pairs a natural-number variable index `v : ℕ` with a Boolean
polarity `b : Bool`. A clause is a finite list of literals interpreted as a
disjunction, and a CNF formula is a finite list of clauses interpreted as a
conjunction. Lists are used for finite collections so that algorithms can
process them directly; duplicate literals or clauses do not affect truth values.
-/

/-- A literal `(v, b)`: variable `v` with polarity `b` (`true` for `v`, `false` for `¬v`). -/
abbrev Literal := ℕ × Bool

/-- A clause: the disjunction of its literals. -/
abbrev Clause := List Literal

/-- A CNF formula: the conjunction of its clauses. -/
abbrev Formula := List Clause

/-- A truth assignment `τ : ℕ → Bool` satisfies a CNF formula `φ` if every
clause `c ∈ φ` contains at least one literal `(v, b) ∈ c` with `τ v = b`. -/
def Satisfiable (φ : Formula) : Prop :=
  ∃ τ : ℕ → Bool, ∀ c ∈ φ, ∃ l ∈ c, τ l.1 = l.2

/-- SAT is the set of satisfiable CNF formulas. -/
def SAT : Set Formula := {φ | Satisfiable φ}

/-- UNSAT is the set of unsatisfiable CNF formulas. Because instances are
formulas rather than raw bitstrings, UNSAT is the exact set-theoretic
complement of SAT. -/
def UNSAT : Set Formula := {φ | ¬ Satisfiable φ}

/-- ExactThreeSAT is the set of satisfiable CNF formulas in which every clause
has length 3 (repeated literals within a clause are permitted). -/
def ExactThreeSAT : Set Formula :=
  {φ | (∀ c ∈ φ, c.length = 3) ∧ Satisfiable φ}

/-! ## Representation details

CNF formulas are lists of clauses with binary variable indices. The following fixed encoding
uses the common framing conventions in the appendix.
-/

/-- Encode a CNF formula as a list of clauses, each a list of literals `(v, b)` encoded as the
pair of `Nat.bits v` and the one-bit word `[b]`. -/
def encodeCNF : Formula → List Bool :=
  Encoding.encodeList (Encoding.encodeList (Encoding.encodePair Nat.bits (fun b => [b])))

theorem encodeCNF_injective : Function.Injective encodeCNF :=
  CookLevinBridge.encodeCNF_injective

/-- Injective framed binary encoding of CNF formulas. -/
def encCNF : Formula ↪ List Bool :=
  ⟨encodeCNF, encodeCNF_injective⟩

/-! ## Efficient verification and reductions

`Computation.PolyTimeVerifier enc V` means that one deterministic machine halts on every
instance/certificate pair in polynomial time in their combined bit length. The machine and
polynomial bound are fixed for the problem. We use certificates of exactly `p(|enc a|)` bits;
this is the fixed-length certificate convention. `Computation.PolyTime` is the same total
computation contract for general input and output encodings. Their definitions are in the
foundations appendix.
-/

/-- A function `V : α × List Bool → Bool` verifies a decision problem `A` with
certificate length polynomial `p` if an instance `a` belongs to `A` exactly
when there is a binary certificate `w` of length `p(|enc a|)` accepted by `V`. -/
def IsVerifier {α : Type} (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true

/-- The class NP with respect to instance encoding `enc` consists of decision
problems that have a polynomial-time verifier with polynomially long binary
certificates. -/
def NP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    Computation.PolyTimeVerifier enc V ∧ IsVerifier enc p V A}

/-- The class coNP consists of decision problems whose complements belong to NP. -/
def coNP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | Aᶜ ∈ NP enc}

/-- Problem `A` (with encoding `encA`) many-one reduces in polynomial time to
problem `B` (with encoding `encB`) if a polynomial-time computable map `f`
preserves yes/no membership on every instance. -/
def PolyTimeReducible {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β, Computation.PolyTime f encA encB ∧ ∀ a, a ∈ A ↔ f a ∈ B

/-- A problem `B` is NP-complete if it belongs to NP and every NP problem (over
any instance type `α` and injective binary encoding `encA`) reduces to `B` in
polynomial time. -/
def NPComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  B ∈ NP encB ∧
  ∀ (α : Type) (encA : α ↪ List Bool) (A : Set α),
    A ∈ NP encA → PolyTimeReducible encA encB A B

/-- A problem `B` is coNP-complete if it belongs to coNP and every coNP problem
reduces to `B` in polynomial time. -/
def coNPComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop :=
  B ∈ coNP encB ∧
  ∀ (α : Type) (encA : α ↪ List Bool) (A : Set α),
    A ∈ coNP encA → PolyTimeReducible encA encB A B

/-! ## Main results -/

/-- **Theorem (Cook–Levin):** SAT is NP-complete under polynomial-time many-one
reductions. -/
theorem sat_npComplete : NPComplete encCNF SAT :=
  CookLevinBridge.sat_npComplete

/-- **Corollary:** UNSAT is coNP-complete under polynomial-time many-one
reductions. -/
theorem unsat_coNPComplete : coNPComplete encCNF UNSAT :=
  CookLevinBridge.unsat_coNPComplete

/-- **Theorem (3SAT with exact clause width 3):** Satisfiability of CNF formulas
whose clauses each have 3 literal occurrences (permitting repeated literals) is
NP-complete under polynomial-time many-one reductions. -/
theorem exactThreeSAT_npComplete : NPComplete encCNF ExactThreeSAT :=
  CookLevinBridge.exactThreeSAT_npComplete

/--
info: abstract audit passed for `ComplexityTests.Abstracts.CookLevinAbstract`:
19 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.CookLevinAbstract allowing [
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation
]

end ComplexityTests.Abstracts.CookLevinAbstract
