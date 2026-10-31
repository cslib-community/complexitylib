/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import ComplexityAbstracts.SubsetSumBridge

/-! # A formal abstract of Subset Sum NP-completeness

This file defines the Subset Sum decision problem on finite lists of natural numbers, its binary
encoding, polynomial-time verifiers, the class NP and polynomial-time many-one reductions, and
proves that Subset Sum is NP-complete when numbers are written in binary.

A reader can inspect the definitions and theorem statements here together with the displayed
shared-foundation appendix. `#check_abstract` audits their dependencies on upstream mathematics
and machine models; Lean checks the proofs through `SubsetSumBridge`.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

namespace ComplexityTests.Abstracts.SubsetSumAbstract

/-! ## Subset Sum -/

/-- An instance `(numbers, target) : List ℕ × ℕ` belongs to `SubsetSum` if some
subsequence (`List.Sublist`) of `numbers` sums to `target`. Using lists rather
than sets allows repeated numbers in the input; each occurrence may be chosen at
most once. -/
def SubsetSum : Set (List ℕ × ℕ) :=
  {x | ∃ s : List ℕ, s.Sublist x.1 ∧ s.sum = x.2}

/-! ## Representation details

The input list and target are encoded in binary. Each input occurrence can be selected once;
input size includes every number's binary digits. The fixed pair/list delimiters are given below.
-/

/-- Injective binary encoding of Subset Sum instances: the list of numbers, then the target. -/
def encSubsetSum : List ℕ × ℕ ↪ List Bool :=
  Encoding.encPair (Encoding.encList Encoding.encNat) Encoding.encNat

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

/-! ## Main result -/

/-- **Theorem (Karp):** Subset Sum is NP-complete under polynomial-time many-one
reductions when the input list and target sum are encoded in binary. -/
theorem subsetSum_npComplete : NPComplete encSubsetSum SubsetSum :=
  SubsetSumBridge.subsetSum_npComplete

/--
info: abstract audit passed for `ComplexityTests.Abstracts.SubsetSumAbstract`:
7 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.SubsetSumAbstract allowing [
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation
]

end ComplexityTests.Abstracts.SubsetSumAbstract
