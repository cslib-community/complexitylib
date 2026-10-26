/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds

/-! # Computational capabilities of pair, option and list encodings

The classes contain proofs of plain computational capabilities, not selected machines or clocks.
Pairing retains independent time and workspace bounds and explicitly charges the output pair.
-/

namespace Turing.MultiTapeTM

universe u

/-! ### Encodings of pairs, options and lists -/

section Classes

variable {α β : Type u}

/-- `enc` encodes pairs compatibly with `enc₁` and `enc₂`. -/
public class PairEncoding (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool)
    (enc : α × β ↪ List Bool) : Prop where
  /-- Pairing is a combinator: functions `f` and `g` computable from a common input within
  common bounds combine into `fun x => (f x, g x)`, within a constant factor of those bounds, plus
  space for the encoded pair. Different bounds are covered by
  `Turing.MultiTapeTM.PairEncoding.pair_mono`. -/
  pair {γ : Type u} {encIn : γ ↪ List Bool} {f : γ → α} {g : γ → β} {t s : γ → ℕ} :
    ComputableInTimeAndSpace f encIn enc₁ t s →
    ComputableInTimeAndSpace g encIn enc₂ t s →
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn enc
      (fun x => c * (t x + 1)) (fun x => c * (s x + (enc (f x, g x)).length + 1))
  /-- The first projection is computable in linear time and space. -/
  fst : ComputableInLinearTimeAndSpace Prod.fst enc enc₁
  /-- The second projection is computable in linear time and space. -/
  snd : ComputableInLinearTimeAndSpace Prod.snd enc enc₂

/-- `enc` encodes options compatibly with `enc₁`: `none` is encoded by the empty word. -/
public class OptionEncoding (enc₁ : α ↪ List Bool) (enc : Option α ↪ List Bool) : Prop where
  /-- `none` is encoded by the empty word. -/
  none_eq : enc none = []
  /-- `some` is computable in linear time and space. -/
  some : ComputableInLinearTimeAndSpace some enc₁ enc
  /-- `Option.getD` is computable in linear time and space. -/
  getD (d : α) : ComputableInLinearTimeAndSpace (fun o => o.getD d) enc enc₁

/-- `enc` encodes lists compatibly with `enc₁`. -/
public class ListEncoding (enc₁ : α ↪ List Bool) (enc : List α ↪ List Bool) : Prop where
  /-- `List.headD` is computable in linear time and space. -/
  headD (d : α) : ComputableInLinearTimeAndSpace (fun l => l.headD d) enc enc₁
  /-- `List.tail` is computable in linear time and space. -/
  tail : ComputableInLinearTimeAndSpace List.tail enc enc
  /-- Testing a list for emptiness is computable in linear time and space. -/
  isEmpty : ComputableInLinearTimeAndSpace List.isEmpty enc encBool

/-- Pairing functions computable within different bounds. -/
public theorem PairEncoding.pair_mono {enc₁ : α ↪ List Bool} {enc₂ : β ↪ List Bool}
    {enc : α × β ↪ List Bool} [h : PairEncoding enc₁ enc₂ enc] {γ : Type u}
    {encIn : γ ↪ List Bool} {f : γ → α} {g : γ → β} {t₁ s₁ t₂ s₂ : γ → ℕ}
    (hf : ComputableInTimeAndSpace f encIn enc₁ t₁ s₁)
    (hg : ComputableInTimeAndSpace g encIn enc₂ t₂ s₂) :
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn enc
      (fun x => c * (t₁ x + t₂ x + 1))
      (fun x => c * (s₁ x + s₂ x + (enc (f x, g x)).length + 1)) :=
  h.pair (hf.mono (fun _ => Nat.le_add_right _ _) (fun _ => Nat.le_add_right _ _))
    (hg.mono (fun _ => Nat.le_add_left _ _) (fun _ => Nat.le_add_left _ _))

end Classes

end Turing.MultiTapeTM
