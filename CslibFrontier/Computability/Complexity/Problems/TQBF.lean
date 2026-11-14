/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Syntax.PrefixParser
public import CslibFrontier.Logics.Propositional.QBF
public import Mathlib.Data.Fintype.Defs
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# The problem of true quantified Boolean formulas

`TQBF` is the set of true closed quantified Boolean formulas over variables numbered by `ℕ`:
formulas without free variables whose value is `true` [Sipser, Section 8.3][Sipser2013]
[Arora and Barak, Section 4.2][AroraBarak09]. A closed formula has the same value under every
assignment (`Cslib.Logic.PL.QBF.eval_eq_of_closed`), so the assignment `fun _ => false` in the
definition is immaterial. Instances are formulas, not words, and every formula is an instance:
formulas with a free variable are simply not in `TQBF`. Formulas are not required to be in prenex
form; the prenex formulas of the textbooks are among them.

A formula is encoded by its tokens in prefix (Polish) order (`Cslib.Logic.PL.QBF.tokens`): the
kind of each node, with its variable for variables and quantifiers and `0` otherwise, as a framed
list of framed pairs of the kind in unary and the variable in binary (`Cslib.Complexity.encQBF`).
The prefix order makes the encoding injective without delimiters
(`Cslib.Logic.PL.QBF.tokens_append_inj`), and every node takes at least three bits, so a formula
with `n` nodes has an encoding of length at least `3 * n`.

Boundary cases: the empty list is the tokens of no formula; the formulas without variables are
built from `top` and `bot`, and `top ∈ TQBF` while `bot ∉ TQBF`; a variable on its own is never
closed, so `var v ∉ TQBF`, while `ex v (var v) ∈ TQBF` and `all v (var v) ∉ TQBF`.

## Main definitions

* `Cslib.Logic.PL.QBF.Kind`, `Cslib.Logic.PL.QBF.tokens`: the tokens of a formula.
* `Cslib.Logic.PL.QBF.Kind.isQuantifier`: whether a kind of nodes is a quantifier.
* `Cslib.Complexity.encQBF`: the encoding of formulas.
* `Cslib.Complexity.TQBF`: the true closed formulas.

## Main results

* `Cslib.Logic.PL.QBF.tokens_append_inj`: tokens in prefix order determine the formula.
* `Cslib.Logic.PL.QBF.length_tokens`: one token for each node.
* `Cslib.Complexity.mem_TQBF`, `Cslib.Complexity.top_mem_TQBF`, `Cslib.Complexity.bot_notMem_TQBF`,
  `Cslib.Complexity.var_notMem_TQBF`: membership and the boundary cases.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL.QBF

/-! ### Tokens -/

/-- The kinds of nodes of a quantified Boolean formula. -/
inductive Kind where
  /-- A variable. -/
  | var
  /-- The constant true. -/
  | top
  /-- The constant false. -/
  | bot
  /-- Negation. -/
  | not
  /-- Conjunction. -/
  | and
  /-- Disjunction. -/
  | or
  /-- Existential quantification. -/
  | ex
  /-- Universal quantification. -/
  | all
  deriving DecidableEq, Inhabited

instance : Fintype Kind :=
  ⟨{.var, .top, .bot, .not, .and, .or, .ex, .all}, fun k => by cases k <;> simp⟩

/-- Whether a kind of nodes is a quantifier. -/
def Kind.isQuantifier : Kind → Bool
  | .ex => true
  | .all => true
  | _ => false

/-- The tokens of a formula in prefix order: the kind of each node, with its variable for
variables and quantifiers, and `0` for the other nodes. -/
def tokens : QBF ℕ → List (Kind × ℕ)
  | .var v => [(.var, v)]
  | .top => [(.top, 0)]
  | .bot => [(.bot, 0)]
  | .not φ => (.not, 0) :: tokens φ
  | .and φ ψ => (.and, 0) :: (tokens φ ++ tokens ψ)
  | .or φ ψ => (.or, 0) :: (tokens φ ++ tokens ψ)
  | .ex v φ => (.ex, v) :: tokens φ
  | .all v φ => (.all, v) :: tokens φ

/-- Interpret an existing formula token as its constructor. Nonzero payloads on constants and
connectives are rejected. Variables and quantifiers retain their binary-encoded variable. -/
def readToken : Kind × ℕ → Option (Cslib.PrefixParser.Step (QBF ℕ))
  | (.var, v) => some (.atom (.var v))
  | (.top, 0) => some (.atom .top)
  | (.bot, 0) => some (.atom .bot)
  | (.not, 0) => some (.unary .not)
  | (.and, 0) => some (.binary .and)
  | (.or, 0) => some (.binary .or)
  | (.ex, v) => some (.unary (.ex v))
  | (.all, v) => some (.unary (.all v))
  | _ => none

/-- Parsing a formula's tokens recovers it and leaves the following suffix untouched. -/
theorem parseFuel_tokens (φ : QBF ℕ) (rest : List (Kind × ℕ)) (fuel : ℕ)
    (hf : φ.tokens.length ≤ fuel) :
    Cslib.PrefixParser.parseFuel readToken fuel (φ.tokens ++ rest) = some (φ, rest) := by
  induction φ generalizing fuel rest with
  | var _ | top | bot =>
    cases fuel <;> simp_all [tokens, Cslib.PrefixParser.parseFuel, readToken]
  | not φ ih | ex _ φ ih | all _ φ ih =>
    cases fuel with
    | zero => simp [tokens] at hf
    | succ fuel =>
      simp only [tokens, List.length_cons] at hf
      simp only [tokens, List.cons_append, Cslib.PrefixParser.parseFuel, readToken]
      rw [ih rest fuel (Nat.le_of_succ_le_succ hf)]
      rfl
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    cases fuel with
    | zero => simp [tokens] at hf
    | succ fuel =>
      simp only [tokens, List.length_cons, List.length_append] at hf
      simp only [tokens, List.cons_append, List.append_assoc,
        Cslib.PrefixParser.parseFuel, readToken]
      rw [ihφ (ψ.tokens ++ rest) fuel
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_succ_le_succ hf))]
      dsimp only [Bind.bind, Option.bind]
      rw [ihψ rest fuel
        (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_succ_le_succ hf))]
      rfl

/-- **Tokens in prefix order determine the formula**, and what follows them. -/
theorem tokens_append_inj {φ ψ : QBF ℕ} {r r' : List (Kind × ℕ)}
    (h : φ.tokens ++ r = ψ.tokens ++ r') : φ = ψ ∧ r = r' :=
  Cslib.PrefixParser.append_injective parseFuel_tokens h

theorem tokens_injective : Function.Injective tokens := fun φ ψ h =>
  (tokens_append_inj (r := []) (r' := []) (by simpa using h)).1

/-- Every formula has a token. -/
theorem tokens_ne_nil (φ : QBF ℕ) : φ.tokens ≠ [] := by
  cases φ <;> simp [tokens]

/-- A formula has one token for each of its nodes. -/
theorem length_tokens (φ : QBF ℕ) : φ.tokens.length = φ.size := by
  induction φ with
  | var v => rfl
  | top => rfl
  | bot => rfl
  | not φ ih => simp only [tokens, size, List.length_cons, ih]
  | and φ ψ ihφ ihψ => simp only [tokens, size, List.length_cons, List.length_append, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp only [tokens, size, List.length_cons, List.length_append, ihφ, ihψ]
  | ex v φ ih => simp only [tokens, size, List.length_cons, ih]
  | all v φ ih => simp only [tokens, size, List.length_cons, ih]

end Cslib.Logic.PL.QBF

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace TQBF

/-- The index of a kind, from `0` for variables to `7` for universal quantifiers. -/
def kindIndex : QBF.Kind → ℕ
  | .var => 0
  | .top => 1
  | .bot => 2
  | .not => 3
  | .and => 4
  | .or => 5
  | .ex => 6
  | .all => 7

theorem kindIndex_injective : Function.Injective kindIndex := by
  intro a b h
  cases a <;> cases b <;> simp_all [kindIndex]

/-- Kinds encoded by their index in unary. -/
def encKind : QBF.Kind ↪ List Bool :=
  ⟨fun k => encUnary (kindIndex k), encUnary.injective.comp kindIndex_injective⟩

/-- Tokens encoded as framed pairs of the kind in unary and the variable in binary. -/
abbrev encToken : QBF.Kind × ℕ ↪ List Bool := encPair encKind encNat

end TQBF

/-- Formulas encoded by their tokens in prefix order (`Cslib.Logic.PL.QBF.tokens`), as a list of
framed tokens. -/
def encQBF : QBF ℕ ↪ List Bool :=
  ⟨fun φ => encList TQBF.encToken φ.tokens,
    fun _ _ h => QBF.tokens_injective ((encList TQBF.encToken).injective h)⟩

/-- A formula is encoded as the list of its framed tokens in prefix order. -/
theorem encQBF_apply (φ : QBF ℕ) : encQBF φ = encList TQBF.encToken φ.tokens := rfl

/-- Every node takes at least three bits. -/
theorem three_mul_length_tokens_le (φ : QBF ℕ) : 3 * φ.tokens.length ≤ (encQBF φ).length := by
  rw [encQBF_apply]
  generalize φ.tokens = l
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [encList_cons, List.length_append, length_frame, List.length_cons, length_encPair]
    omega

/-! ### True closed formulas -/

/-- **The true closed quantified Boolean formulas** over variables numbered by natural numbers
[Sipser, Section 8.3][Sipser2013], [Arora and Barak, Section 4.2][AroraBarak09]. -/
def TQBF : Set (QBF ℕ) := {φ | φ.Closed ∧ φ.eval (fun _ => false) = true}

/-- A formula is in `TQBF` exactly when it is closed and true under the assignment
`fun _ => false`. -/
theorem mem_TQBF {φ : QBF ℕ} : φ ∈ TQBF ↔ φ.Closed ∧ φ.eval (fun _ => false) = true := Iff.rfl

/-- A closed formula is in `TQBF` exactly when it is true under some, equivalently every,
assignment. -/
theorem mem_TQBF_iff_of_closed {φ : QBF ℕ} (hφ : φ.Closed) (σ : ℕ → Bool) :
    φ ∈ TQBF ↔ φ.eval σ = true := by
  rw [mem_TQBF, QBF.eval_eq_of_closed hφ _ σ]
  exact and_iff_right hφ

/-- The constant true is a true closed formula. -/
theorem top_mem_TQBF : QBF.top ∈ TQBF := ⟨rfl, rfl⟩

/-- The constant false is not true. -/
theorem bot_notMem_TQBF : QBF.bot ∉ TQBF := fun h => absurd h.2 (by simp)

/-- A variable on its own is not closed. -/
theorem var_notMem_TQBF (v : ℕ) : QBF.var v ∉ TQBF := fun h =>
  absurd h.1 (by simp [QBF.Closed])

end Cslib.Complexity
