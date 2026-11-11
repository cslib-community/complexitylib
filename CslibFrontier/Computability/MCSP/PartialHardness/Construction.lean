/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CMMSA
public import CslibFrontier.Computability.MCSP.Partial

/-!
# The partial truth table of a CMMSA instance

The table construction of the library's reduction from `GapCMMSA Δ g 1` to partial MCSP
(issue #4362, route B). Hirahara's partial-MCSP hardness [Hirahara2022] fixes the problem shape;
the construction here is the library's own. Each variable `v` of a CMMSA instance `I` gets a
Boolean function `f v` on `ℓ v` inputs, where `2 ^ ℓ v` is about `w v · λ` for the weight `w v`
and a scale `λ`. The partial truth table `FromCMMSA.toInstance I Δ k λ P f` then reads:

* an input: the index `j` of a formula (in `⌈log₂ m⌉` bits), and for each slot `(t, q)` with
  `t, q < Δ`, a mask bit and `k` seeds of `W` bits each, where `W` is the largest `ℓ v`;
* the bit of the slot `(t, q)`: the slot is *occupied* when term `t` of `φ_j` has a literal at
  position `q`, and its bit is the mask plus the sum, over the `k` seeds `z`, of `f v` at the first
  `ℓ v` bits of `z`, for the variable `v` of that literal (`slotBit`);
* the table entry: `b` when `j < m` and the bits of the occupied slots of every term of `φ_j` sum
  to `b` (`termParity`); otherwise `*` (`entry`).

So the masks of a term are an XOR sharing of the output, masked by `k`-fold XORs of the functions
of its variables. Slots outside a term, and seed bits past `ℓ v`, are not read. The size threshold
is `⌊(P + 2) 2 ^ L / (P L)⌋`, where `L = ⌈log₂ (2 θ λ)⌉` is the table length of the Yes circuit
(`sizeThreshold`).

Slots are indexed by term and position within the term, `Δ × Δ` of them, instead of by the at most
`Δ` literal occurrences of a formula: parsing then needs no offsets, and the input length stays
`⌈log₂ m⌉ + Δ² (k W + 1)`.

## Main definitions

* `Cslib.PartialMCSP.FromCMMSA.varLength`, `seedWidth`, `tableLength`, `inputLength`: the
  parameters `ℓ v`, `W`, `L` and the input length.
* `Cslib.PartialMCSP.FromCMMSA.slotBit`, `termParity`, `entry`: the partial truth table.
* `Cslib.PartialMCSP.FromCMMSA.sizeThreshold`: the size threshold.
* `Cslib.PartialMCSP.FromCMMSA.toInstance`: the partial MCSP instance.

## Main results

* `Cslib.PartialMCSP.FromCMMSA.formulaIndex_lt_of_entry_eq_some`,
  `Cslib.PartialMCSP.FromCMMSA.termParity_eq_of_entry_eq_some`: a defined entry has a formula
  index below `m`, and every term of that formula has parity equal to the entry.

## References

* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

@[expose] public section

namespace Cslib.PartialMCSP.FromCMMSA

open Cslib.Complexity Cslib.Logic.PL

variable (I : CMMSAInstance) (Δ k lam P : ℕ)

/-- The input length `ℓ v = ⌈log₂ (w v · λ)⌉` of the function of variable `v`, so that
`w v · λ ≤ 2 ^ ℓ v ≤ 2 w v · λ` for a positive weight and `λ ≥ 1`. -/
def varLength (v : ℕ) : ℕ := Nat.clog 2 (I.weights.getD v 0 * lam)

/-- The seed width `W`: the largest `ℓ v` over the variables `v < n`. -/
def seedWidth : ℕ := (Finset.range I.weights.length).sup (varLength I lam)

/-- The table length `L = ⌈log₂ (2 θ λ)⌉` of the Yes circuit. -/
def tableLength : ℕ := Nat.clog 2 (2 * I.threshold * lam)

/-- The width `⌈log₂ m⌉` of the formula index. -/
def indexWidth : ℕ := Nat.clog 2 I.formulas.length

/-- The width of a slot: `k` seeds and a mask bit. -/
def slotWidth : ℕ := k * seedWidth I lam + 1

/-- The input length `⌈log₂ m⌉ + Δ² (k W + 1)`. -/
def inputLength : ℕ := indexWidth I + Δ * Δ * slotWidth I k lam

/-- The position of bit `i` of the formula index. -/
def indexPos (i : Fin (indexWidth I)) : Fin (inputLength I Δ k lam) :=
  Fin.castAdd _ i

/-- The position of bit `p` of slot `(t, q)`. -/
def slotPos (t q : Fin Δ) (p : Fin (slotWidth I k lam)) : Fin (inputLength I Δ k lam) :=
  Fin.natAdd (indexWidth I) (finProdFinEquiv (finProdFinEquiv (t, q), p))

/-- The position of the mask bit of slot `(t, q)`. -/
def maskPos (t q : Fin Δ) : Fin (inputLength I Δ k lam) :=
  slotPos I Δ k lam t q (Fin.last _)

/-- The position of bit `r` of seed `i` of slot `(t, q)`. -/
def seedPos (t q : Fin Δ) (i : Fin k) (r : Fin (seedWidth I lam)) :
    Fin (inputLength I Δ k lam) :=
  slotPos I Δ k lam t q (Fin.castSucc (finProdFinEquiv (i, r)))

variable {I Δ k lam}

/-- The formula index `j` read from an input. -/
def formulaIndex (x : BitString (inputLength I Δ k lam)) : ℕ :=
  BitString.equivFin _ fun i => x (indexPos I Δ k lam i)

/-- Seed `i` of slot `(t, q)` read from an input. -/
def seed (x : BitString (inputLength I Δ k lam)) (t q : Fin Δ) (i : Fin k) :
    BitString (seedWidth I lam) :=
  fun r => x (seedPos I Δ k lam t q i r)

variable (I) in
/-- Term `t` of formula `j`, empty when there is none. -/
def term (j t : ℕ) : Term ℕ := (I.formulas.getD j []).getD t []

variable (I) in
/-- The variable of the literal at position `q` of term `t` of formula `j`. -/
def var (j t q : ℕ) : ℕ := ((term I j t).getD q (0, true)).1

variable (I lam) in
/-- The functions of the variables: `f v` has `ℓ v` inputs. -/
abbrev VarFunctions : Type :=
  (v : Fin I.weights.length) → BooleanFunction (varLength I lam v)

/-- `f v` at the first `ℓ v` bits of `z`, zero-padded; `false` when `v` is not a variable. -/
def evalVar (f : VarFunctions I lam) (v : ℕ) {d : ℕ} (z : BitString d) : Bool :=
  if hv : v < I.weights.length then f ⟨v, hv⟩ (BitString.zeroExtend z) else false

/-- The bit of slot `(t, q)`: its mask plus `∑_{i < k} f v (z_i)` for the variable `v` of its
literal. -/
def slotBit (f : VarFunctions I lam) (x : BitString (inputLength I Δ k lam)) (t q : Fin Δ) :
    Bool :=
  x (maskPos I Δ k lam t q) +
    ∑ i : Fin k, evalVar f (var I (formulaIndex x) t q) (seed x t q i)

/-- The parity of term `t`: the sum of the bits of its occupied slots. -/
def termParity (f : VarFunctions I lam) (x : BitString (inputLength I Δ k lam)) (t : Fin Δ) :
    Bool :=
  ∑ q : Fin Δ, if (q : ℕ) < (term I (formulaIndex x) t).length then slotBit f x t q else 0

/-- The entry of the partial truth table at `x`: `b` when the formula index `j` is below `m` and
every term of `φ_j` has parity `b`; otherwise undefined. -/
def entry (f : VarFunctions I lam) (x : BitString (inputLength I Δ k lam)) : Option Bool :=
  if formulaIndex x < I.formulas.length then
    if ∀ t : Fin Δ, (t : ℕ) < (I.formulas.getD (formulaIndex x) []).length →
        termParity f x t = true then some true
    else if ∀ t : Fin Δ, (t : ℕ) < (I.formulas.getD (formulaIndex x) []).length →
        termParity f x t = false then some false
    else none
  else none

variable (I lam) in
/-- The size threshold `⌊(P + 2) 2 ^ L / (P L)⌋`. -/
def sizeThreshold : ℕ := (P + 2) * 2 ^ tableLength I lam / (P * tableLength I lam)

variable (I Δ k lam) in
/-- **The partial MCSP instance of a CMMSA instance**, for the functions `f` of its variables. -/
def toInstance (f : VarFunctions I lam) : PartialMCSP.Instance where
  arity := inputLength I Δ k lam
  table i := entry f ((BitString.equivFin _).symm i)
  threshold := sizeThreshold I lam P

/-- A defined entry has a formula index below `m`. -/
theorem formulaIndex_lt_of_entry_eq_some {f : VarFunctions I lam}
    {x : BitString (inputLength I Δ k lam)} {b : Bool} (h : entry f x = some b) :
    formulaIndex x < I.formulas.length := by
  unfold entry at h
  split_ifs at h with hj <;> exact hj

/-- **Support of the table.** At a defined entry `b`, every term of the indexed formula has parity
`b`. -/
theorem termParity_eq_of_entry_eq_some {f : VarFunctions I lam}
    {x : BitString (inputLength I Δ k lam)} {b : Bool} (h : entry f x = some b) (t : Fin Δ)
    (ht : (t : ℕ) < (I.formulas.getD (formulaIndex x) []).length) :
    termParity f x t = b := by
  unfold entry at h
  split_ifs at h with hj h₁ h₂ <;> cases h
  · exact h₁ t ht
  · exact h₂ t ht

end Cslib.PartialMCSP.FromCMMSA
