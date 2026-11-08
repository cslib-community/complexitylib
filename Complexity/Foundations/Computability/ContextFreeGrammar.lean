/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/ContextFreeGrammar.lean`)

public import Complexity.Init
public import Mathlib.Computability.ContextFreeGrammar

/-!
# Derivations from concatenations and from single nonterminals

Mathlib's `ContextFreeGrammar.Derives` is closed under adding context on either side
(`Derives.append_left`, `Derives.append_right`). This file proves the converse decomposition:
a derivation from a concatenation `u ++ v` splits into independent derivations from `u` and
from `v`, the basic fact behind parse trees and the CYK algorithm. It also describes the
derivations from a terminal word (there are none but the trivial one) and from a single
nonterminal (the trivial one, or a first step by a rule).

Splitting lemmas of this kind appear in unmerged Mathlib work: `DerivesIn.append_split`, for
derivations of bounded length, in Loitzl and Dvořák's leanprover-community/mathlib4#19943
(closed), and the private special case `head_tail_split` (for `s :: ss`) in Mündler-Sasahara's
open leanprover-community/mathlib4#33601.

## Main results

* `ContextFreeGrammar.derives_append_iff`: `u ++ v` derives `w` iff `w = x ++ y` with `u`
  deriving `x` and `v` deriving `y`; `Derives.append_split` is the forward direction and
  `Derives.append` the converse.
* `ContextFreeGrammar.derives_map_terminal_iff`: a word of terminals derives only itself.
* `ContextFreeGrammar.produces_nonterminal_iff`, `ContextFreeGrammar.derives_nonterminal_iff`:
  one-step rewrites and derivations from a single nonterminal.
-/

public section

namespace ContextFreeGrammar

variable {T : Type*} {g : ContextFreeGrammar T}

/-- A derivation from a concatenation splits into derivations from the two parts. -/
theorem Derives.append_split {u v w : List (Symbol T g.NT)} (h : g.Derives (u ++ v) w) :
    ∃ x y, g.Derives u x ∧ g.Derives v y ∧ w = x ++ y := by
  induction h with
  | refl => exact ⟨u, v, .refl _, .refl _, rfl⟩
  | tail _ hp ih =>
    obtain ⟨x, y, hx, hy, rfl⟩ := ih
    obtain ⟨r, hr, hrw⟩ := hp
    obtain ⟨p, q, hpq, rfl⟩ := hrw.exists_parts
    rw [List.append_assoc, List.singleton_append, List.append_eq_append_iff] at hpq
    rcases hpq with ⟨c, rfl, rfl⟩ | ⟨c, rfl, hc⟩
    · refine ⟨x, c ++ r.output ++ q, hx, hy.trans_produces ⟨r, hr, ?_⟩, by simp⟩
      simpa using ContextFreeRule.rewrites_of_exists_parts r c q
    · cases c with
      | nil =>
        rw [List.nil_append] at hc
        subst hc
        refine ⟨p, r.output ++ q, by simpa using hx, hy.trans_produces ⟨r, hr, ?_⟩, by simp⟩
        simpa using ContextFreeRule.rewrites_of_exists_parts r [] q
      | cons d c =>
        rw [List.cons_append, List.cons.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        refine ⟨p ++ r.output ++ c, y, hx.trans_produces ⟨r, hr, ?_⟩, hy, by simp⟩
        simpa using ContextFreeRule.rewrites_of_exists_parts r p c

/-- Derivations from two words combine into a derivation from their concatenation. -/
theorem Derives.append {u v x y : List (Symbol T g.NT)} (hu : g.Derives u x)
    (hv : g.Derives v y) : g.Derives (u ++ v) (x ++ y) :=
  (hu.append_right v).trans (hv.append_left x)

/-- `u ++ v` derives `w` exactly when `w` splits into a word derived from `u` followed by a word
derived from `v`. -/
theorem derives_append_iff {u v w : List (Symbol T g.NT)} :
    g.Derives (u ++ v) w ↔ ∃ x y, g.Derives u x ∧ g.Derives v y ∧ w = x ++ y :=
  ⟨Derives.append_split, fun ⟨_, _, hx, hy, h⟩ => h ▸ hx.append hy⟩

/-- A word of terminals derives only itself. -/
theorem derives_map_terminal_iff {w : List T} {v : List (Symbol T g.NT)} :
    g.Derives (w.map Symbol.terminal) v ↔ v = w.map Symbol.terminal := by
  refine ⟨fun h => ?_, fun h => h ▸ .refl _⟩
  rcases h.eq_or_head with h | ⟨u, hu, -⟩
  · exact h.symm
  · obtain ⟨r, -, hr⟩ := hu.exists_nonterminal_input_mem
    simp at hr

/-- A single nonterminal `A` rewrites in one step to `v` exactly when `v` is the output of a rule
with input `A`. -/
theorem produces_nonterminal_iff {A : g.NT} {v : List (Symbol T g.NT)} :
    g.Produces [Symbol.nonterminal A] v ↔ ∃ r ∈ g.rules, r.input = A ∧ v = r.output := by
  constructor
  · rintro ⟨r, hr, hrw⟩
    obtain ⟨p, q, hpq, rfl⟩ := hrw.exists_parts
    have hp : p = [] := by
      cases p with
      | nil => rfl
      | cons _ p => simp at hpq
    subst hp
    simp only [List.nil_append, List.singleton_append, List.cons.injEq, Symbol.nonterminal.injEq]
      at hpq
    obtain ⟨rfl, rfl⟩ := hpq
    exact ⟨r, hr, rfl, by simp⟩
  · rintro ⟨r, hr, rfl, rfl⟩
    exact ⟨r, hr, ContextFreeRule.Rewrites.input_output⟩

/-- A single nonterminal `A` derives `w` exactly when `w = [A]` or some rule with input `A` has an
output deriving `w`. -/
theorem derives_nonterminal_iff {A : g.NT} {w : List (Symbol T g.NT)} :
    g.Derives [Symbol.nonterminal A] w ↔
      w = [Symbol.nonterminal A] ∨ ∃ r ∈ g.rules, r.input = A ∧ g.Derives r.output w := by
  rw [derives_iff_eq_or_head]
  refine or_congr eq_comm ⟨fun ⟨v, hv, hvw⟩ => ?_, fun ⟨r, hr, hA, hw⟩ => ?_⟩
  · obtain ⟨r, hr, hA, rfl⟩ := produces_nonterminal_iff.mp hv
    exact ⟨r, hr, hA, hvw⟩
  · exact ⟨r.output, produces_nonterminal_iff.mpr ⟨r, hr, hA, rfl⟩, hw⟩

end ContextFreeGrammar
