/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.ThreeSets
public import Complexity.Algorithms.ThreeSum.ArrayPacking
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Sqrt

/-!
# Core Chan–He hashing and recursion data

Direct adaptation of `PaperStatements.lean`, lines 1242–1365, from
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
These are finite mathematical constructions, not a native RAM implementation.

## Main definitions

* `coll`, `heavy`: collision counts and elements sharing a residue class.
* `firstP`, `secondP`, `modulus`: deterministic minimum-prime searches.
* `arrXY`, `arrZ`: light-element convolution arrays with signed padding.
* `nodes`, `reduction`: a finite ternary recursion tree at explicit parameters.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020], Theorem 5.1.
-/

@[expose] public section

namespace Cslib.Algorithms.ThreeSum.ChanHe

open Finset

/-! ### Collisions and heavy elements -/

/-- The number of ordered pairs of distinct elements of `S` that are congruent modulo `M`. -/
def coll (S : Finset ℤ) (M : ℕ) : ℕ := #{p ∈ S.offDiag | (M : ℤ) ∣ p.1 - p.2}

/-- The elements of `S` that share their residue modulo `M` with another element of `S`.  They play
the role of the bad elements of [ChanHe2020]. The elements alone in their residue class modulo
`M` are called light below; they play the role of the good elements of [ChanHe2020]. -/
def heavy (S : Finset ℤ) (M : ℕ) : Finset ℤ := {x ∈ S | ∃ y ∈ S, y ≠ x ∧ (M : ℤ) ∣ x - y}

/-! ### The arrays of one node -/

/-- The elements of `S` with remainder `r` modulo `M`. -/
def bucket (S : Finset ℤ) (M : ℕ) (r : ℤ) : Finset ℤ := {x ∈ S | x % (M : ℤ) = r}

/-- The array of the light elements of `S`.  Cell `i` holds the element of the bucket of `i` if that
bucket has exactly one element, and the padding value `pad` otherwise. -/
def arr (S : Finset ℤ) (M : ℕ) (pad : ℤ) (i : ℕ) : ℤ :=
  if #(bucket S M i) = 1 then ∑ x ∈ bucket S M i, x else pad

/-- The padding value `2U + 1`.  It is too large to take part in a solution among numbers of
absolute value at most `U`. -/
def pad (U : ℕ) : ℤ := 2 * U + 1

/-- The array made from the first or the second set of a node. -/
def arrXY (S : Finset ℤ) (M U : ℕ) : ℕ → ℤ := arr S M (pad U)

/-- The third array of a node.  A light element `c` of `S` is written as `-c` into the two cells `r`
and `r + M`, where `r` is the remainder of `-c`.  All other cells, and all cells from `2M` on, hold
`-pad U`. -/
def arrZ (S : Finset ℤ) (M U : ℕ) (k : ℕ) : ℤ :=
  if k < 2 * M then arr (S.image fun c => -c) M (-pad U) (k % M) else -pad U

/-! ### The choice of the modulus -/

/-- The least element of a finite set of natural numbers, and 1 if the set is empty. -/
def minOrOne (T : Finset ℕ) : ℕ := if h : T.Nonempty then T.min' h else 1

/-- The first prime: the least `p` in `Q` modulo which each of the three sets has at most
`3Λ|S|²/|Q|` colliding pairs.  Here and below, `Q` is the set of candidate primes, and `Λ` bounds
how many of them divide a nonzero difference of two elements.  `reduction` takes the primes up to
`mPar n U` for `Q`, and `labelBits U` for `Λ`. -/
def firstP (Q : Finset ℕ) (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) : ℕ :=
  minOrOne {p ∈ Q | coll S₁ p * #Q ≤ 3 * Λ * #S₁ ^ 2 ∧ coll S₂ p * #Q ≤ 3 * Λ * #S₂ ^ 2 ∧
    coll S₃ p * #Q ≤ 3 * Λ * #S₃ ^ 2}

/-- The second prime, given the first: the least `q` in `Q` such that, in each of the three sets, at
most the fraction `3Λ/|Q|` of the pairs that collide modulo `p` still collide modulo `pq`. -/
def secondP (Q : Finset ℕ) (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) (p : ℕ) : ℕ :=
  minOrOne {q ∈ Q | coll S₁ (p * q) * #Q ≤ 3 * Λ * coll S₁ p ∧
    coll S₂ (p * q) * #Q ≤ 3 * Λ * coll S₂ p ∧ coll S₃ (p * q) * #Q ≤ 3 * Λ * coll S₃ p}

/-- The modulus of a node: the product of the two primes. -/
def modulus (Q : Finset ℕ) (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) : ℕ :=
  firstP Q Λ S₁ S₂ S₃ * secondP Q Λ S₁ S₂ S₃ (firstP Q Λ S₁ S₂ S₃)

/-! ### The recursion tree -/

/-- A node of the recursion tree: three sets and the modulus chosen for them. -/
structure Node where
  /-- The first set. -/
  S₁ : Finset ℤ
  /-- The second set. -/
  S₂ : Finset ℤ
  /-- The third set. -/
  S₃ : Finset ℤ
  /-- The modulus. -/
  M : ℕ
  deriving DecidableEq

/-- The nodes on the first `f` levels of the recursion tree with root `(S₁, S₂, S₃)`; for `f = 0`
there are none.  A triple with an empty set is not a node and has no children.  Any other triple is
a node, and each of its three children replaces one of the sets by its heavy elements. -/
def nodes (Q : Finset ℕ) (Λ : ℕ) : ℕ → Finset ℤ → Finset ℤ → Finset ℤ → List Node
  | 0, _, _, _ => []
  | f + 1, S₁, S₂, S₃ =>
    if S₁ = ∅ ∨ S₂ = ∅ ∨ S₃ = ∅ then [] else
      let M := modulus Q Λ S₁ S₂ S₃
      ⟨S₁, S₂, S₃, M⟩ ::
        (nodes Q Λ f (heavy S₁ M) S₂ S₃ ++ nodes Q Λ f S₁ (heavy S₂ M) S₃ ++
          nodes Q Λ f S₁ S₂ (heavy S₃ M))

/-! ### The parameters -/

/-- `⌈log₂(⌊log₂ n⌋ + 2)⌉`.  In the recursion tree of `reduction n U`, for three sets of at most
`n ≥ 1` elements each, all of absolute value at most `U` (the hypotheses of the library's lemma
`ChanHe.reduction_correct`), a set is empty after this many replacements by its heavy elements. -/
def height (n : ℕ) : ℕ := Nat.clog 2 (Nat.log 2 n + 2)

/-- The number of levels of the recursion tree that are built.  Under the hypotheses named at
`height`, each of the three sets of a node has been replaced at most `height n - 1` times, because
it is not empty.  So a node has at most `3 (height n - 1)` nodes above it. -/
def fuel (n : ℕ) : ℕ := 3 * height n - 2

/-- The number of primes that we want to choose from. -/
def wPar (n U : ℕ) : ℕ := 5 * labelBits U * (Nat.sqrt n + 1)

/-- The bound `m` on the primes.  There are at least `wPar n U` primes up to `m` (the library's
lemma `ChanHe.wPar_le_card_primesLE`). -/
def mPar (n U : ℕ) : ℕ := (wPar n U + 1) * (2 * Nat.log 2 (wPar n U + 1) + 4)

/-! ### The reduction for three sets -/

/-- **The reduction for three sets.**  Here `n` is an upper bound on the sizes of the three sets and
`U` on the absolute values of their elements; both stay fixed through the recursion.  The result is
a list of nodes.  The Convolution-3SUM instance of a node `ν` consists of the arrays
`arrXY ν.S₁ ν.M U`, `arrXY ν.S₂ ν.M U` and `arrZ ν.S₃ ν.M U`, read at any length
`N ≥ 2 * mPar n U ^ 2`. -/
def reduction (n U : ℕ) (S₁ S₂ S₃ : Finset ℤ) : List Node :=
  nodes (Nat.primesLE (mPar n U)) (labelBits U) (fuel n) S₁ S₂ S₃

/-- The three-array convolution instance attached to a recursion node. -/
def Node.Conv (ν : Node) (U N : ℕ) : Prop :=
  HasConvolutionSolution N (arrXY ν.S₁ ν.M U) (arrXY ν.S₂ ν.M U) (arrZ ν.S₃ ν.M U)

end Cslib.Algorithms.ThreeSum.ChanHe
