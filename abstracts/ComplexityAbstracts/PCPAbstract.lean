/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import ComplexityAbstracts.PCPBridge

/-! # The PCP theorem

For every problem with certificates checkable in polynomial time, proofs can be presented so that
verification reads only constantly many bits. The verifier chooses those positions using only
logarithmically many random bits. A correct instance has a proof accepted for every random choice;
for an incorrect instance, every purported proof is rejected with probability at least one half.
Dinur's construction repeatedly magnifies the fraction of violated constraints while returning
to a fixed alphabet, so a constant number of local checks can detect global inconsistency.

Queries are nonadaptive: their positions are chosen before any proof bits are read. Native
machine bounds charge the complete construction, the binary query addresses and verification.
The construction is asymptotically polynomial, with enormous fixed constants.

Lean checks the bridge to the complete construction, and `#check_abstract` audits the public
statement's dependency boundary.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

namespace ComplexityTests.Abstracts.PCPAbstract

/-! ## Efficient verification

`Computation.PolyTimeVerifier enc V` is one deterministic verifier that halts on every pair
in polynomial time in `|enc a| + |w|`. Its code and bound are fixed before either input is
chosen. Certificates here have exactly the polynomial length `p(|enc a|)`.
-/

/-- NP consists of problems with a polynomial-time deterministic verifier and binary
certificates of an exact polynomial length. The verifier halts on every input pair. -/
def NP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    Computation.PolyTimeVerifier enc V ∧
    ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true}

/-- Read a finite proof at the queried addresses. Positions beyond its end read as false. -/
def proofAnswers (proof : List Bool) (positions : List ℕ) : List Bool :=
  positions.map (fun i => proof.getD i false)

/-- The number of `n`-bit random strings on which the verifier accepts a fixed proof. -/
def acceptCount {α : Type} (queries : α × List Bool → List ℕ)
    (verdict : (α × List Bool) × List Bool → Bool) (a : α) (proof : List Bool) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun r : Fin n → Bool =>
    verdict ((a, List.ofFn r), proofAnswers proof (queries (a, List.ofFn r))) = true).card

/-! ## Representation details

All three verifier routines run in polynomial time. Query positions are binary integers, so
constructing their addresses is charged; the proof itself is accessed only at those positions.
-/

/-- Native polynomial-time realization of the coin count, query list and verdict. -/
def EfficientVerifier {α : Type} (enc : α ↪ List Bool) (coins : α → ℕ)
    (queries : α × List Bool → List ℕ)
    (verdict : (α × List Bool) × List Bool → Bool) : Prop :=
  Computation.PolyTime coins enc Encoding.encNat ∧
  Computation.PolyTime queries (Encoding.encPair enc Encoding.encBits)
    (Encoding.encList Encoding.encNat) ∧
  Computation.PolyTime verdict
    (Encoding.encPair (Encoding.encPair enc Encoding.encBits) Encoding.encBits) Encoding.encBool

/-! ## Probabilistically checkable proofs

Randomness is a uniformly chosen word of exactly `coins a` bits. Thus the acceptance
probability is `acceptCount / 2^(coins a)`. The final inequality below says it is at most
one half, without division or rounding. `EfficientVerifier` charges coin counting, query selection
and the final verdict.
-/

/-- Nonadaptive probabilistically checkable proofs: one fixed polynomial-time algorithm
computes the number of random bits, the list of binary proof addresses and the final verdict.
For constants `c,d`, it uses at most `c*r(n)` random bits and `d*q(n)` queries. A yes-instance
has a finite proof accepted for every random string; on a no-instance every finite proof is
accepted on at most half of the random strings. -/
def PCP {α : Type} (r q : ℕ → ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (coins : α → ℕ) (queries : α × List Bool → List ℕ)
      (verdict : (α × List Bool) × List Bool → Bool) (c d : ℕ),
    EfficientVerifier enc coins queries verdict ∧
    (∀ a, coins a ≤ c * r (enc a).length) ∧
    (∀ a ρ, ρ.length = coins a → (queries (a, ρ)).length ≤ d * q (enc a).length) ∧
    (∀ a ∈ A, ∃ proof : List Bool, ∀ ρ, ρ.length = coins a →
      verdict ((a, ρ), proofAnswers proof (queries (a, ρ))) = true) ∧
    ∀ a ∉ A, ∀ proof, 2 * acceptCount queries verdict a proof (coins a) ≤ 2 ^ coins a}

/-- NP equals logarithmic-randomness, constant-query PCP, with perfect completeness and
soundness at most one half. Queries are nonadaptive; their binary addresses and all computation
are charged, including the full gap-graph construction. -/
theorem pcp_theorem {α : Type} (enc : α ↪ List Bool) :
    NP enc = PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) enc := by
  unfold PCP EfficientVerifier
  simp only [and_assoc]
  exact PCPBridge.pcp_theorem enc

/--
info: abstract audit passed for `ComplexityTests.Abstracts.PCPAbstract`:
7 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.PCPAbstract allowing [
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation
]

end ComplexityTests.Abstracts.PCPAbstract
