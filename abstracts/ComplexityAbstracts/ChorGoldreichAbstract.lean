/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.ChorGoldreichBridge

/-! # Chor–Goldreich: the inner product extracts a random bit from two weak sources

A weak random source is a distribution on `n`-bit strings in which no outcome is very likely: a
`k`-source gives every string probability at most `2 ^ (-k)`, so it has min-entropy at least `k`.
No fixed function extracts a fair bit from every such source when `k ≤ n - 1`. Two independent
sources suffice: if their min-entropies `k₁` and `k₂` add up to more than `n`, then the inner
product modulo two of independent samples is nearly a fair coin, with bias at most
`2 ^ ((n - k₁ - k₂) / 2) / 2`. The bound holds even on average after the second sample is
revealed. The threshold is sharp: strings supported on complementary sets of positions have
min-entropies adding up to exactly `n` and are always orthogonal.

A reader only needs to inspect the definitions and theorem statements in this file to verify that
they state the intended claims. Lean checks the proofs through `ChorGoldreichBridge`, and
`#check_abstract` audits that every statement depends only on this file and background libraries.
Probabilities are those of Mathlib's discrete distributions `PMF`, read as real numbers with
`toReal`; the experiments are written in `do` notation, sampling independently in sequence.

## References

* [B. Chor and O. Goldreich, *Unbiased bits from sources of weak randomness and probabilistic
  communication complexity*, Theorem 9][ChorGoldreich1988]
* [S. Vadhan, *Pseudorandomness*, Chapter 6][Vadhan2012]
-/

namespace ComplexityAbstracts.ChorGoldreichAbstract

/-- A bit string is a function assigning a Boolean to each of `n` positions. -/
abbrev BitString (n : ℕ) := Fin n → Bool

/-- A **`k`-source**: a distribution on bit strings in which every string has probability at most
`2 ^ (-k)`, that is, of min-entropy at least `k`. The exponent `k` is a real number. -/
def IsSource {n : ℕ} (p : PMF (BitString n)) (k : ℝ) : Prop :=
  ∀ x, (p x).toReal ≤ 2 ^ (-k)

/-- The inner product modulo two: true when an odd number of positions are true in both
inputs. The sum below uses Boolean multiplication (AND) and addition (XOR). -/
def innerProduct {n : ℕ} (x y : BitString n) : Bool := ∑ i, x i * y i

/-- **Chor–Goldreich.** For independent samples of a `k₁`-source and a `k₂`-source of `n`-bit
strings, the probability that their inner product is true differs from one half by at most
`2 ^ ((n - k₁ - k₂) / 2) / 2`. This is the statistical distance of the inner product from a fair
bit. -/
theorem chor_goldreich {n : ℕ} {k₁ k₂ : ℝ} (p q : PMF (BitString n)) (hp : IsSource p k₁)
    (hq : IsSource q k₂) :
    |((do
        let x ← p
        let y ← q
        return innerProduct x y) true).toReal - 1 / 2| ≤
      2 ^ ((n - k₁ - k₂) / 2) / 2 :=
  ChorGoldreichBridge.chorGoldreich p q hp hq

/-- **Chor–Goldreich, strong form.** The same bound holds on average over the second sample `y`:
the probability over the first source that the inner product with `y` is true differs from one
half by at most `2 ^ ((n - k₁ - k₂) / 2) / 2` on average. Equivalently, the second sample paired
with the inner product is that close to the second sample paired with a fair bit. -/
theorem chor_goldreich_strong {n : ℕ} {k₁ k₂ : ℝ} (p q : PMF (BitString n))
    (hp : IsSource p k₁) (hq : IsSource q k₂) :
    ∑ y, (q y).toReal * |((do
        let x ← p
        return innerProduct x y) true).toReal - 1 / 2| ≤
      2 ^ ((n - k₁ - k₂) / 2) / 2 :=
  ChorGoldreichBridge.chorGoldreich_strong p q hp hq

/-- **The threshold is sharp.** For every set `S` of positions, there are an `|S|`-source and an
`(n - |S|)`-source whose independent samples have inner product true with probability zero:
strings vanishing outside `S` are orthogonal to strings vanishing on `S`. -/
theorem orthogonal_sources {n : ℕ} (S : Finset (Fin n)) :
    ∃ p q : PMF (BitString n), IsSource p S.card ∧ IsSource q (n - S.card) ∧
      ((do
        let x ← p
        let y ← q
        return innerProduct x y) true).toReal = 0 :=
  ChorGoldreichBridge.orthogonal_sources S

/--
info: 'ComplexityAbstracts.ChorGoldreichAbstract.chor_goldreich' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chor_goldreich

/--
info: 'ComplexityAbstracts.ChorGoldreichAbstract.chor_goldreich_strong' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms chor_goldreich_strong

/--
info: abstract audit passed for `ComplexityAbstracts.ChorGoldreichAbstract`: 7 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.ChorGoldreichAbstract

end ComplexityAbstracts.ChorGoldreichAbstract
