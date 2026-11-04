/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.CommunicationBridge

/-! # Communication: randomness cannot eliminate the need to exchange information

Alice and Bob each hold an `n`-bit string and exchange bits to compute a joint answer.
Disjointness and parity of the intersection both require linearly many communicated bits,
even with shared randomness and error at most one third on every input pair.

Local computation is free. Cost is the worst case over inputs and coins; protocols may be
chosen separately at each input length. Both players learn the answer, so exact deterministic
equality costs `n + 1` bits for `n > 0`: Alice sends her input and Bob replies with the answer.

The only allowlisted model is the binary protocol tree described below. Cost and per-input
error are defined here. Lean checks the bridge proofs; `#check_abstract` audits their statement
dependencies. The disjointness constants are not optimized.

## References

* [B. Kalyanasundaram, G. Schnitger, *The probabilistic communication complexity of set
  intersection*][KalyanasundaramSchnitger1992]
* [A. Razborov, *On the distributional complexity of disjointness*][Razborov1992]
* [E. Kushilevitz, N. Nisan, *Communication Complexity*, Chapters 1–4][KushilevitzNisan1997]
-/

namespace ComplexityAbstracts.CommunicationAbstract

/-- A bit string is a function assigning a Boolean to each of `n` positions. -/
abbrev Input (n : ℕ) := Fin n → Bool

/-- A finite binary tree: `output b` is a leaf announcing `b`; `alice send p₀ p₁` branches
on the bit `send x` of Alice's input, and `bob` branches on Bob's input. The transcript
determines the current node, so messages may depend on all earlier messages. -/
abbrev Protocol (n : ℕ) := Cslib.Communication.Protocol (Input n) (Input n) Bool

/-- Follow the sent bits from the root to a leaf and return its announced answer. -/
def answer {n : ℕ} (p : Protocol n) (x y : Input n) : Bool := p.run x y

/-- Tree depth: leaves cost zero, and sending one bit costs one plus the larger branch cost. -/
def cost {n : ℕ} (p : Protocol n) : ℕ := p.depth

/-- Shared randomness selects a deterministic tree independently of the inputs.
`PMF` is a probability distribution with total mass one. -/
abbrev RandomizedProtocol (n : ℕ) := PMF (Protocol n)

/-- Every tree with positive probability has depth at most `c`, bounding all its branches. -/
def CostAtMost {n : ℕ} (μ : RandomizedProtocol n) (c : ℕ) : Prop :=
  ∀ p ∈ μ.support, cost p ≤ c

/-- On each input pair separately, the probability of a wrong answer is at most `ε`.
The measure sums the probabilities of trees giving a wrong answer; `toReal` returns a real. -/
def ErrorAtMost {n : ℕ} (μ : RandomizedProtocol n)
    (f : Input n → Input n → Bool) (ε : ℝ) : Prop :=
  ∀ x y, (μ.toOuterMeasure {p | answer p x y ≠ f x y}).toReal ≤ ε

/-- The sets of true positions are disjoint exactly when no position is true in both inputs. -/
def disjoint {n : ℕ} (x y : Input n) : Bool :=
  decide (∀ i, (x i && y i) = false)

/-- The inner product modulo two: true when an odd number of positions are true in both
inputs. The sum below uses Boolean multiplication (AND) and addition (XOR). -/
def innerProduct {n : ℕ} (x y : Input n) : Bool := ∑ i, x i * y i

/-- **Exact equality.** A deterministic protocol deciding equality within `c` bits exists
exactly when `n + 1 ≤ c`, for positive input length. At length zero, the constant true
answer costs no communication. -/
theorem equality {n c : ℕ} (hn : 0 < n) :
    (∃ p : Protocol n, (∀ x y, answer p x y = decide (x = y)) ∧ cost p ≤ c) ↔ n + 1 ≤ c :=
  CommunicationBridge.equality hn

/-- **Kalyanasundaram–Schnitger / Razborov.** Even with shared randomness and error at most
one third, disjointness needs linear communication: `n ≤ 65536*c + 4096`.
The proof uses Razborov's corruption method, with a variant of his hard distribution. -/
theorem disjointness_lower_bound {n c : ℕ} (μ : RandomizedProtocol n)
    (hc : CostAtMost μ c) (he : ErrorAtMost μ disjoint (1 / 3)) :
    n ≤ 2 ^ 16 * c + 2 ^ 12 :=
  CommunicationBridge.disjointness μ hc he

/-- **Inner product.** Even with shared randomness and error at most one third,
computing parity of the intersection requires `n ≤ 2*c + 3`. The proof bounds the
discrepancy of the inner-product sign matrix using its orthogonal rows. -/
theorem innerProduct_lower_bound {n c : ℕ} (μ : RandomizedProtocol n)
    (hc : CostAtMost μ c) (he : ErrorAtMost μ innerProduct (1 / 3)) :
    n ≤ 2 * c + 3 :=
  CommunicationBridge.innerProduct μ hc he

/--
info: 'ComplexityAbstracts.CommunicationAbstract.disjointness_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms disjointness_lower_bound

/--
info: 'ComplexityAbstracts.CommunicationAbstract.innerProduct_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms innerProduct_lower_bound

/--
info: abstract audit passed for `ComplexityAbstracts.CommunicationAbstract`: 12 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.CommunicationAbstract allowing [
  Complexity.Computability.Communication.Protocol
]

end ComplexityAbstracts.CommunicationAbstract
