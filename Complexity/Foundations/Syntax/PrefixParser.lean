/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init

/-!
# Parsing constructor tokens in prefix order

A token describes a leaf, a unary constructor, or a binary constructor. `parseFuel` reads one
value and returns the unconsumed suffix, or `none` on an invalid token, missing operand, or
exhausted fuel. No default value or inhabitance assumption is needed. `parse` uses the input
length as fuel, and `decode` additionally rejects trailing tokens.

Syntax-specific round-trip proofs imply `append_injective`: a value's tokens determine both the
value and the following suffix. This avoids comparing every pair of constructors when proving
injectivity of a flat syntax encoding. No machine resource bound is asserted for these parsers.
-/

public section

namespace Cslib.PrefixParser

/-- The constructor represented by a token, with zero, one, or two operands. -/
inductive Step (α : Type*) where
  /-- A leaf value. -/
  | atom (value : α)
  /-- A constructor with one operand. -/
  | unary (make : α → α)
  /-- A constructor with two operands, in input order. -/
  | binary (make : α → α → α)

/-- Read one prefix-coded value, with fuel bounding the depth of recursive parsing. -/
@[expose] def parseFuel {α τ : Type*} (readToken : τ → Option (Step α)) :
    ℕ → List τ → Option (α × List τ)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, token :: rest =>
    match readToken token with
    | none => none
    | some (.atom value) => some (value, rest)
    | some (.unary make) => do
      let (value, rest) ← parseFuel readToken fuel rest
      return (make value, rest)
    | some (.binary make) => do
      let (left, rest) ← parseFuel readToken fuel rest
      let (right, rest) ← parseFuel readToken fuel rest
      return (make left right, rest)

/-- Read a prefix and its remainder, using the number of input tokens as sufficient fuel. -/
@[expose] def parse {α τ : Type*} (readToken : τ → Option (Step α)) (tokens : List τ) :
    Option (α × List τ) :=
  parseFuel readToken tokens.length tokens

/-- Read exactly one value; trailing tokens are rejected. -/
@[expose] def decode {α τ : Type*} (readToken : τ → Option (Step α)) (tokens : List τ) : Option α :=
  match parse readToken tokens with
  | some (value, []) => some value
  | _ => none

/-- A prefix round-trip determines the encoded value and every following token. -/
theorem append_injective {α τ : Type*} {readToken : τ → Option (Step α)}
    {tokens : α → List τ}
    (roundtrip : ∀ value rest fuel, (tokens value).length ≤ fuel →
      parseFuel readToken fuel (tokens value ++ rest) = some (value, rest))
    {left right : α} {rest rest' : List τ}
    (h : tokens left ++ rest = tokens right ++ rest') : left = right ∧ rest = rest' := by
  have hparse := congrArg
    (parseFuel readToken ((tokens left).length + (tokens right).length)) h
  rw [roundtrip _ _ _ (Nat.le_add_right _ _),
    roundtrip _ _ _ (Nat.le_add_left _ _)] at hparse
  have hp := Option.some.inj hparse
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- Parsing an encoded value leaves the supplied suffix unchanged. -/
theorem parse_append {α τ : Type*} {readToken : τ → Option (Step α)}
    {tokens : α → List τ}
    (roundtrip : ∀ value rest fuel, (tokens value).length ≤ fuel →
      parseFuel readToken fuel (tokens value ++ rest) = some (value, rest))
    (value : α) (rest : List τ) : parse readToken (tokens value ++ rest) = some (value, rest) :=
  roundtrip value rest _ (by simp)

/-- A complete encoded value decodes to itself. -/
theorem decode_tokens {α τ : Type*} {readToken : τ → Option (Step α)}
    {tokens : α → List τ}
    (roundtrip : ∀ value rest fuel, (tokens value).length ≤ fuel →
      parseFuel readToken fuel (tokens value ++ rest) = some (value, rest))
    (value : α) : decode readToken (tokens value) = some value := by
  have h := parse_append roundtrip value []
  simp only [List.append_nil] at h
  unfold decode
  rw [h]

end Cslib.PrefixParser
