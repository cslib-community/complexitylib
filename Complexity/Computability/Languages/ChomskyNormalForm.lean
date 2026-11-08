/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Computability.ContextFreeGrammar

/-!
# Grammars in Chomsky normal form

A context-free grammar is in Chomsky normal form when every rule has the form `A → B C` or
`A → a`, except that the start symbol `S` may have the rule `S → ε`
[Sipser, Definition 2.8][Sipser2013]. `Cslib.ChomskyNormalFormGrammar` bundles such a grammar:
its rules form a list, so that algorithms can iterate over them, and a Boolean flag records the
rule `S → ε`. When that flag is set, `S` may not occur on the right-hand side of a rule; this is
what keeps `ε` out of the languages of all the other nonterminals. Without the rule `S → ε`, the
start symbol may occur on right-hand sides, as in Hopcroft, Motwani and Ullman's normal form
[Hopcroft2006], which has no `ε`-rule at all. `ChomskyNormalFormGrammar.toCFG` reads the grammar
as a Mathlib `ContextFreeGrammar`, and every statement about derivations and languages is made
through it.

The design (rule constructors `leaf` and `node`, the field names `NT`, `initial` and `rules`, and
the embedding `toCFG`) follows Loitzl and Dvořák's Mathlib pull request
leanprover-community/mathlib4#19943, which was closed unmerged and had no `ε`-rule.

## Main definitions

* `Cslib.ChomskyNormalFormRule`: a rule `A → a` (`leaf`) or `A → B C` (`node`).
* `Cslib.ChomskyNormalFormGrammar`: a grammar in Chomsky normal form, with an optional `S → ε`.
* `Cslib.ChomskyNormalFormGrammar.toCFG`: the grammar as a Mathlib `ContextFreeGrammar`.

## Main results

* `Cslib.ChomskyNormalFormGrammar.derives_nil_iff`: only the start symbol derives `ε`, and only
  with the rule `S → ε`.
* `Cslib.ChomskyNormalFormGrammar.mem_language_nil_iff`: `ε` is in the language iff the grammar
  has the rule `S → ε`.
* `Cslib.ChomskyNormalFormGrammar.derives_iff_of_ne_nil`: a nonterminal `A` derives a nonempty
  word `w` iff `w = a` with a rule `A → a`, or `w = u v` with `u` and `v` nonempty and a rule
  `A → B C` such that `B` derives `u` and `C` derives `v`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages,
  and Computation*][Hopcroft2006]
-/

public section

namespace Cslib

/-- A rule of a grammar in Chomsky normal form, over terminals `T` and nonterminals `N`. -/
inductive ChomskyNormalFormRule (T N : Type*)
  /-- The rule `A → a`. -/
  | leaf (A : N) (a : T)
  /-- The rule `A → B C`. -/
  | node (A B C : N)
deriving DecidableEq, Repr

namespace ChomskyNormalFormRule

variable {T N : Type*}

/-- The left-hand side of a rule. -/
@[expose] def input : ChomskyNormalFormRule T N → N
  | leaf A _ => A
  | node A _ _ => A

/-- The right-hand side of a rule. -/
@[expose] def output : ChomskyNormalFormRule T N → List (Symbol T N)
  | leaf _ a => [.terminal a]
  | node _ B C => [.nonterminal B, .nonterminal C]

/-- A rule in Chomsky normal form as a context-free rule. -/
@[expose] def toContextFreeRule (r : ChomskyNormalFormRule T N) : ContextFreeRule T N :=
  ⟨r.input, r.output⟩

@[simp] theorem input_toContextFreeRule (r : ChomskyNormalFormRule T N) :
    r.toContextFreeRule.input = r.input := rfl

@[simp] theorem output_toContextFreeRule (r : ChomskyNormalFormRule T N) :
    r.toContextFreeRule.output = r.output := rfl

end ChomskyNormalFormRule

/-- A context-free grammar in Chomsky normal form over terminals `T`: rules `A → a` and
`A → B C`, together with the rule `S → ε` for the start symbol `S` when `nilRule` is set. With
that rule, `S` occurs on no right-hand side. -/
structure ChomskyNormalFormGrammar (T : Type*) where
  /-- The type of nonterminals. -/
  NT : Type
  /-- The start symbol. -/
  initial : NT
  /-- The rules `A → a` and `A → B C`. -/
  rules : List (ChomskyNormalFormRule T NT)
  /-- Whether the grammar has the rule `initial → ε`. -/
  nilRule : Bool
  /-- With the rule `initial → ε`, the start symbol occurs on no right-hand side. -/
  initial_notMem_output :
    nilRule = true → ∀ r ∈ rules, Symbol.nonterminal initial ∉ r.output

namespace ChomskyNormalFormGrammar

variable {T : Type*} (G : ChomskyNormalFormGrammar T)

open Classical in
/-- A grammar in Chomsky normal form as a Mathlib `ContextFreeGrammar`. -/
noncomputable abbrev toCFG : ContextFreeGrammar T where
  NT := G.NT
  initial := G.initial
  rules := (G.rules.map ChomskyNormalFormRule.toContextFreeRule).toFinset ∪
    if G.nilRule then {⟨G.initial, []⟩} else ∅

@[simp] theorem toCFG_initial : G.toCFG.initial = G.initial := rfl

/-- The rules of `G.toCFG` are those of `G` and, with `nilRule`, the rule `initial → ε`. -/
theorem mem_toCFG_rules {r : ContextFreeRule T G.NT} :
    r ∈ G.toCFG.rules ↔
      (∃ r' ∈ G.rules, r'.toContextFreeRule = r) ∨ (G.nilRule = true ∧ r = ⟨G.initial, []⟩) := by
  classical
  simp only [toCFG]
  split_ifs with h <;> simp [h, or_comm]

variable {G}

/-- Every symbol of a sentential form deriving `ε` is the start symbol, which then has the rule
`S → ε`. -/
theorem eq_initial_of_derives_nil {u : List (Symbol T G.NT)} (h : G.toCFG.Derives u []) :
    ∀ s ∈ u, s = .nonterminal G.initial ∧ G.nilRule = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => simp
  | head hp _ ih =>
    obtain ⟨r, hr, hrw⟩ := hp
    obtain ⟨p, q, rfl, rfl⟩ := hrw.exists_parts
    intro s hs
    simp only [List.mem_append, List.mem_singleton] at hs ih
    rcases hs with (hs | rfl) | hs
    · exact ih s (Or.inl (Or.inl hs))
    · rcases (G.mem_toCFG_rules).mp hr with ⟨r', hr', rfl⟩ | ⟨hn, rfl⟩
      · obtain ⟨s', hs'⟩ : ∃ s', s' ∈ r'.output := by
          cases r' <;> exact ⟨_, List.mem_cons_self⟩
        obtain ⟨rfl, hn⟩ := ih s' (Or.inl (Or.inr hs'))
        exact absurd hs' (G.initial_notMem_output hn r' hr')
      · exact ⟨rfl, hn⟩
    · exact ih s (Or.inr hs)

/-- A nonterminal derives `ε` exactly when it is the start symbol and the grammar has the rule
`S → ε`. -/
theorem derives_nil_iff {A : G.NT} :
    G.toCFG.Derives [.nonterminal A] [] ↔ G.nilRule = true ∧ A = G.initial := by
  constructor
  · intro h
    obtain ⟨hs, hn⟩ := eq_initial_of_derives_nil h _ List.mem_cons_self
    exact ⟨hn, Symbol.nonterminal.inj hs⟩
  · rintro ⟨hn, rfl⟩
    exact ContextFreeGrammar.Produces.single
      (ContextFreeGrammar.produces_nonterminal_iff.mpr
        ⟨⟨G.initial, []⟩, (G.mem_toCFG_rules).mpr (Or.inr ⟨hn, rfl⟩), rfl, rfl⟩)

/-- The empty word is in the language exactly when the grammar has the rule `S → ε`. -/
theorem mem_language_nil_iff : [] ∈ G.toCFG.language ↔ G.nilRule = true := by
  rw [ContextFreeGrammar.mem_language_iff, List.map_nil]
  exact derives_nil_iff.trans (and_iff_left rfl)

/-- A nonterminal `A` derives a nonempty word `w` exactly when `w` is a letter `a` with a rule
`A → a`, or `w = u ++ v` for nonempty `u` and `v` and a rule `A → B C` such that `B` derives `u`
and `C` derives `v`. -/
theorem derives_iff_of_ne_nil {A : G.NT} {w : List T} (hw : w ≠ []) :
    G.toCFG.Derives [.nonterminal A] (w.map .terminal) ↔
      (∃ a, w = [a] ∧ .leaf A a ∈ G.rules) ∨
      ∃ B C u v, .node A B C ∈ G.rules ∧ u ≠ [] ∧ v ≠ [] ∧ w = u ++ v ∧
        G.toCFG.Derives [.nonterminal B] (u.map .terminal) ∧
        G.toCFG.Derives [.nonterminal C] (v.map .terminal) := by
  rw [ContextFreeGrammar.derives_nonterminal_iff]
  constructor
  · rintro (h | ⟨r, hr, rfl, hd⟩)
    · obtain ⟨a, -, ha⟩ := List.map_eq_singleton_iff.mp h
      exact absurd ha (by simp)
    rcases (G.mem_toCFG_rules).mp hr with ⟨r', hr', rfl⟩ | ⟨-, rfl⟩
    · cases r' with
      | leaf A a =>
        left
        have hw' : w.map Symbol.terminal = [a].map (Symbol.terminal (N := G.NT)) :=
          (ContextFreeGrammar.derives_map_terminal_iff (w := [a])).mp hd
        exact ⟨a, List.map_injective_iff.mpr (fun _ _ h => Symbol.terminal.inj h) hw', hr'⟩
      | node A B C =>
        right
        have hd' : G.toCFG.Derives ([.nonterminal B] ++ [.nonterminal C]) (w.map .terminal) := hd
        obtain ⟨x, y, hx, hy, hxy⟩ := hd'.append_split
        obtain ⟨u, v, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp hxy
        have hnil : ∀ D, Symbol.nonterminal D ∈ (ChomskyNormalFormRule.node A B C).output →
            G.toCFG.Derives [.nonterminal D] [] → False := fun D hD h => by
          obtain ⟨hn, rfl⟩ := derives_nil_iff.mp h
          exact G.initial_notMem_output hn _ hr' hD
        refine ⟨B, C, u, v, hr', ?_, ?_, rfl, hx, hy⟩
        · rintro rfl
          exact hnil B (by simp [ChomskyNormalFormRule.output]) hx
        · rintro rfl
          exact hnil C (by simp [ChomskyNormalFormRule.output]) hy
    · have := (ContextFreeGrammar.derives_map_terminal_iff (g := G.toCFG) (w := [])).mp hd
      exact absurd (List.map_eq_nil_iff.mp this) hw
  · rintro (⟨a, rfl, ha⟩ | ⟨B, C, u, v, hr, -, -, rfl, hu, hv⟩)
    · right
      refine ⟨(ChomskyNormalFormRule.leaf A a).toContextFreeRule,
        (G.mem_toCFG_rules).mpr (Or.inl ⟨_, ha, rfl⟩), rfl, ?_⟩
      exact .refl _
    · right
      refine ⟨(ChomskyNormalFormRule.node A B C).toContextFreeRule,
        (G.mem_toCFG_rules).mpr (Or.inl ⟨_, hr, rfl⟩), rfl, ?_⟩
      rw [List.map_append]
      exact ContextFreeGrammar.Derives.append (u := [.nonterminal B]) (v := [.nonterminal C]) hu hv

end ChomskyNormalFormGrammar

end Cslib
