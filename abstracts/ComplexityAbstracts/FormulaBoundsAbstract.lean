/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.FormulaBoundsBridge

/-! # Formula lower bounds: the cost of copying computation

A circuit may reuse a computed value. A formula is a tree, so using an intermediate result
twice requires copying its computation. This restriction makes strong lower bounds possible:
parity on `n` bits needs at least `n²` input occurrences. Andreev's function asks for a truth-table
entry addressed by block parities, giving a stronger bound for an explicit Boolean function.

The model uses binary AND/OR, unary NOT and constants. Size counts input leaves with
multiplicity; constants cost zero leaves. The statements concern these De Morgan formulas,
not circuits with shared subcomputations or the runtime of constructing a formula. Only the
elementary formula-tree model is allowed from the implementation; its constructors and
semantics are explained below. Lean checks the bridge proofs and `#check_abstract` audits the
statement boundary.

## References

* [P. Spira, *On time-hardware complexity tradeoffs for Boolean functions*][Spira1971]
* [V. Khrapchenko, *Method of determining lower bounds for the complexity of Pi-schemes*]
  [Khrapchenko1971b]
* [S. Yablonskii, *On superpositions of functions of the algebra of logic*][Yablonskii1954]
* [B. Subbotovskaya, *Realizations of linear functions by formulas*][Subbotovskaya1961]
* [A. Andreev, *On a method of obtaining more than quadratic effective lower bounds*][Andreev1987]
* [S. Jukna, *Boolean Function Complexity*][Jukna2012]
-/

namespace ComplexityTests.Abstracts.FormulaBoundsAbstract

/-- A De Morgan expression is a tree of binary AND/OR, unary NOT, constants, and input leaves.
Only the elementary tree datatype/evaluator/costs in the explicitly allowed Formula module are
used; the lower-bound and balancing implementations are not allowed dependencies. -/
abbrev Expression (n : ℕ) := Cslib.Circuits.Formula Cslib.Circuits.Boolean.signature n

/-- The Boolean function computed by an expression under the standard interpretation. -/
def evaluate {n : ℕ} (F : Expression n) : (Fin n → Bool) → Bool :=
  F.eval Cslib.Circuits.Boolean.interpretation

/-- Input occurrences are counted with multiplicity. Constants contribute zero leaves. -/
def leaves {n : ℕ} (F : Expression n) : ℕ := F.leafSize

/-- Count AND/OR gates on the longest path; NOT and constant gates cost zero. -/
def andOrDepth {n : ℕ} (F : Expression n) : ℕ :=
  F.depthWith (fun op : Cslib.Circuits.Boolean.Op =>
    match op with | .and | .or => 1 | .const _ | .not => 0)

/-- The least number of input occurrences in an expression computing `f`. Every Boolean
function has such an expression; this minimum is a size measure, not a search algorithm. -/
noncomputable def minimumLeaves {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {L | ∃ F : Expression n, (∀ x, evaluate F x = f x) ∧ leaves F = L}

/-- Parity is true exactly when an odd number of input bits are true. -/
def parity (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i => x i = true).card % 2 = 1)

/-- The binary number represented by a word, with coordinate zero least significant:
the value is `∑ i, (if bits i then 1 else 0) * 2^i`. -/
def tableIndex (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The address is the ordinary binary value, with bit zero least significant. -/
theorem tableIndex_val {b : ℕ} (bits : Fin b → Bool) :
    (tableIndex b bits).val = ∑ i : Fin b, (if bits i then 1 else 0) * 2 ^ i.val :=
  FormulaBoundsBridge.tableIndex_val bits

/-- The first `2^b` input bits form the truth table, in address order. -/
def tableInput {b m : ℕ} (x : Fin (2 ^ b + b * m) → Bool) : Fin (2 ^ b) → Bool :=
  fun i => x (Fin.castAdd (b * m) i)

/-- The remaining input is `b` consecutive blocks of `m` bits. Block `j`, position `t`, is
input position `2^b + m*j + t`. -/
def blockInput {b m : ℕ} (x : Fin (2 ^ b + b * m) → Bool) (j : Fin b) : Fin m → Bool :=
  fun t => x (Fin.natAdd (2 ^ b) (finProdFinEquiv (j, t)))

/-- Reading block `j` at position `t` reads exactly the indicated flat input coordinate. -/
theorem blockInput_eq {b m : ℕ} (x : Fin (2 ^ b + b * m) → Bool) (j : Fin b) (t : Fin m)
    (i : Fin (2 ^ b + b * m)) (hi : i.val = 2 ^ b + m * j.val + t.val) :
    blockInput x j t = x i :=
  FormulaBoundsBridge.blockInput_eq x j t i hi

/-- Andreev's function reads the truth-table entry addressed by the `b` block parities.
The table is part of the input, not a hardwired oracle. Its bit at address zero is used when
there are no blocks (`b = 0`), or when every block is empty (`m = 0`). -/
def andreev (b m : ℕ) (x : Fin (2 ^ b + b * m) → Bool) : Bool :=
  tableInput x (tableIndex b fun j => parity m (blockInput x j))

/-- **Spira.** Balancing preserves the function and bounds AND/OR depth by four times the
ceiling logarithm of the original leaf count. For a constant expression the bound is zero. -/
theorem spira {n : ℕ} (F : Expression n) :
    ∃ G : Expression n, (∀ x, evaluate G x = evaluate F x) ∧
      andOrDepth G ≤ 4 * Nat.clog 2 (leaves F) :=
  FormulaBoundsBridge.spira F

/-- **Khrapchenko.** If an expression is true on `A` and false on `B`, the square of the
number of Hamming-distance-one pairs between them is at most `leaves * |A| * |B|`. -/
theorem khrapchenko {n : ℕ} (F : Expression n)
    (A B : Finset (Fin n → Bool)) (hA : ∀ x ∈ A, evaluate F x = true)
    (hB : ∀ x ∈ B, evaluate F x = false) :
    ((A ×ˢ B).filter fun p => hammingDist p.1 p.2 = 1).card ^ 2 ≤
      leaves F * A.card * B.card :=
  FormulaBoundsBridge.khrapchenko F A B hA hB

/-- Parity on `n` bits requires at least `n²` input leaves, including `n = 0`. -/
theorem parity_lower_bound {n : ℕ} (F : Expression n)
    (hF : ∀ x, evaluate F x = parity n x) : n ^ 2 ≤ leaves F :=
  FormulaBoundsBridge.parity_lower_bound F hF

/-- The lower bound is attained at every power-of-two arity. -/
theorem parity_exact_at_powers_of_two (k : ℕ) :
    ∃ F : Expression (2 ^ k), (∀ x, evaluate F x = parity (2 ^ k) x) ∧
      leaves F = (2 ^ k) ^ 2 :=
  FormulaBoundsBridge.parity_exact_at_powers_of_two k

/-- **Yablonskii.** Every parity function has an expression within a factor `9/8` of `n²`.
This counts formula leaves, not gates in a circuit that shares intermediate values. -/
theorem yablonskii (n : ℕ) :
    ∃ F : Expression n, (∀ x, evaluate F x = parity n x) ∧ 8 * leaves F ≤ 9 * n ^ 2 :=
  FormulaBoundsBridge.yablonskii n

/-- Free negations still leave a depth lower bound of `ceil(log₂(n²))` for parity. -/
theorem parity_depth_lower_bound {n : ℕ} (F : Expression n)
    (hF : ∀ x, evaluate F x = parity n x) : Nat.clog 2 (n ^ 2) ≤ andOrDepth F :=
  FormulaBoundsBridge.parity_depth_lower_bound F hF

/-- **Subbotovskaya.** Some restriction leaving exactly `k` coordinates free shrinks squared
formula size by at least `(k/n)³`. Fixed coordinates use `some bit`; `none` leaves a coordinate
free. Free coordinates remain in the original `n`-coordinate space and are counted explicitly. -/
theorem subbotovskaya {n : ℕ} (f : (Fin n → Bool) → Bool) {k : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ∃ ρ : Fin n → Option Bool,
      (Finset.univ.filter fun i => ρ i = none).card = k ∧
      minimumLeaves (fun x => f (fun i => (ρ i).getD (x i))) ^ 2 * n ^ 3 ≤
        minimumLeaves f ^ 2 * k ^ 3 :=
  FormulaBoundsBridge.subbotovskaya f hk1 hkn

/-- **Andreev.** Beyond one fixed cutoff in `b`, every `m ≥ floor(log₂ b)+2` gives the
following quantitative formula-size bound. Taking `m = 2^b` yields the familiar
`n^(5/2-o(1))` bound, with `n = (b+1)2^b`. The theorem does not concern general circuits. -/
theorem andreev_lower_bound :
    ∃ B : ℕ, ∀ b ≥ B, ∀ m ≥ Nat.log 2 b + 2,
      2 ^ (2 * b) * m ^ 3 ≤
        144 * b ^ 2 * (Nat.log 2 b + 2) ^ 3 * minimumLeaves (andreev b m) ^ 2 :=
  FormulaBoundsBridge.andreev_lower_bound

/-- info: abstract audit passed for `ComplexityTests.Abstracts.FormulaBoundsAbstract`: 21 root
declarations -/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.FormulaBoundsAbstract allowing [
  Complexity.Computability.Circuit.Formula
]

end ComplexityTests.Abstracts.FormulaBoundsAbstract
