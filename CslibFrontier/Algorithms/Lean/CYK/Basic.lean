/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TimeM.Loops
public import CslibFrontier.Computability.Languages.ChomskyNormalForm
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Cocke–Younger–Kasami algorithm

Membership in the language of a grammar in Chomsky normal form, decided by dynamic programming
over subwords [Kasami][Kasami1965] [Younger][Younger1967] [Hopcroft, Motwani and Ullman,
Section 7.4.4][Hopcroft2006]. The table holds, for each subword `w[i, i + l)` of the input, the
list of nonterminals deriving it. Cells of length one are read off the rules `A → a`. A cell of
length `l ≥ 2` is filled by trying every split point `k` and every rule `A → B C` with `B` in the
cell of the first `k + 1` letters and `C` in the cell of the remaining `l - k - 1`. The input is
accepted when the start symbol is in the cell of the whole word, or, for the empty word, when the
grammar has the rule `S → ε`.

This is the algorithm in the proof of [Sipser, Theorem 7.16][Sipser2013] that every context-free
language is in P, for a grammar that is already in Chomsky normal form. Conversion of an arbitrary
context-free grammar to Chomsky normal form is not formalized here, and neither is a
machine-level polynomial-time decider; the cost below is in the `TimeM` model.

## Main definitions

* `Cslib.Algorithms.Lean.CYK.table`: the table, filled level by level (by subword length).
* `Cslib.Algorithms.Lean.CYK.cyk`: the membership test.
* `Cslib.Algorithms.Lean.CYK.cykM`: the same algorithm in `TimeM`.

## Main results

* `Cslib.Algorithms.Lean.CYK.mem_table_iff`: a nonterminal is in a table cell iff it derives the
  subword of the cell, in the sense of Mathlib's `ContextFreeGrammar.Derives` for
  `ChomskyNormalFormGrammar.toCFG`.
* `Cslib.Algorithms.Lean.CYK.cyk_eq_true_iff`: CYK accepts exactly the words of the language.
* `Cslib.Algorithms.Lean.CYK.decidableMemLanguage`: membership in the language of a grammar in
  Chomsky normal form is decidable.
* `Cslib.Algorithms.Lean.CYK.nodup_table_and_length_le`: every cell is a list without repetitions
  of at most `|R|` nonterminals.
* `Cslib.Algorithms.Lean.CYK.ret_cykM`: `cykM` returns `cyk`.
* `Cslib.Algorithms.Lean.CYK.time_cykM`: the cost is exactly `(|R| + 1) (n + C(n + 1, 3))` on a
  word of length `n ≥ 1` with `|R|` rules (and `0` on the empty word), so
  `Cslib.Algorithms.Lean.CYK.time_cykM_le` bounds it by `(|R| + 1) (n + 1)³`, that is
  `O(n³ · |G|)`.

## Cost model

`Cslib.Algorithms.Lean.CYK.cykM` charges one unit for each rule examined in each scan of the rule
list. A cell of length one costs one unit to read its letter and one scan. A cell of length
`l ≥ 2` costs, for each of its `l - 1` split points, one unit to read the two subcells and one
scan. Reading and writing a table cell, testing membership of a nonterminal in a cell and adding
a nonterminal to a cell are counted as constant-time steps, as on a random-access machine holding
the table as an array of sets of nonterminals. The cells are lists without repetitions of at most
`|R|` nonterminals (`Cslib.Algorithms.Lean.CYK.nodup_table_and_length_le`), so for a fixed grammar
these operations act on sets of bounded size. The final lookup of the start symbol and the test
for the empty word are not charged.

The pure `Cslib.Algorithms.Lean.CYK.cyk` is a specification of the algorithm, convenient for
proofs and for `decide` on small inputs, not a fast executable: its table is a function built by
a chain of updates, so evaluating a cell recomputes earlier cells. The cost statements are about
`Cslib.Algorithms.Lean.CYK.cykM` in the `TimeM` model above.

## References

* [T. Kasami, *An efficient recognition and syntax-analysis algorithm for context-free
  languages*][Kasami1965]
* [D. H. Younger, *Recognition and parsing of context-free languages in time n³*][Younger1967]
* [J. E. Hopcroft, R. Motwani and J. D. Ullman, *Introduction to Automata Theory, Languages,
  and Computation*][Hopcroft2006]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.Algorithms.Lean.CYK

open ChomskyNormalFormGrammar ChomskyNormalFormRule

variable {T : Type*} [DecidableEq T] (G : ChomskyNormalFormGrammar T) [DecidableEq G.NT]

/-- The left-hand side `A` of a rule `A → a` with `x = some a`. -/
@[expose] def leafMatch (x : Option T) : ChomskyNormalFormRule T G.NT → Option G.NT
  | leaf A a => if x = some a then some A else none
  | node .. => none

/-- The left-hand side `A` of a rule `A → B C` with `B ∈ L` and `C ∈ R`. -/
@[expose] def nodeMatch (L R : List G.NT) : ChomskyNormalFormRule T G.NT → Option G.NT
  | leaf .. => none
  | node A B C => if B ∈ L ∧ C ∈ R then some A else none

/-- Scan the rules once, adding the nonterminal of every match to `acc` unless it is already there
(`List.insert`). -/
@[expose] def scan (f : ChomskyNormalFormRule T G.NT → Option G.NT) (acc : List G.NT) :
    List G.NT :=
  G.rules.foldl (fun acc r => (f r).elim acc (acc.insert ·)) acc

/-- A CYK table: `tbl i l` lists nonterminals for the subword of length `l` starting at `i`. -/
abbrev Table (G : ChomskyNormalFormGrammar T) := ℕ → ℕ → List G.NT

variable (w : List T)

/-- The cell of the letter at position `i`: the nonterminals `A` with a rule `A → w[i]`. -/
@[expose] def leafCell (i : ℕ) : List G.NT := scan G (leafMatch G w[i]?) []

/-- The cell of the subword of length `l ≥ 2` at `i`, from the cells of shorter subwords: the
nonterminals `A` with a rule `A → B C`, `B` in the cell of the first `k + 1` letters and `C` in
the cell of the remaining `l - k - 1`, for some split `k < l - 1`. -/
@[expose] def nodeCell (tbl : Table G) (i l : ℕ) : List G.NT :=
  (List.range (l - 1)).foldl (fun acc k =>
    scan G (nodeMatch G (tbl i (k + 1)) (tbl (i + k + 1) (l - k - 1))) acc) []

/-- The cell of the subword of length `l` at `i`. -/
@[expose] def cell (tbl : Table G) (i l : ℕ) : List G.NT :=
  if l = 1 then leafCell G w i else nodeCell G tbl i l

/-- Overwrite the cell `(i, l)` of a table. -/
@[expose] def setCell (tbl : Table G) (i l : ℕ) (c : List G.NT) : Table G :=
  fun i' l' => if i' = i ∧ l' = l then c else tbl i' l'

/-- Fill the cells of length `l` at every start position `i` with `i + l ≤ |w|`. -/
@[expose] def level (tbl : Table G) (l : ℕ) : Table G :=
  (List.range (w.length + 1 - l)).foldl (fun t i => setCell G t i l (cell G w tbl i l)) tbl

/-- The table with the cells of lengths `1, …, L` filled, in order of length. -/
@[expose] def table : ℕ → Table G
  | 0 => fun _ _ => []
  | L + 1 => level G w (table L) (L + 1)

/-- The CYK membership test: accept the empty word when the grammar has the rule `S → ε`, and a
nonempty word when the start symbol is in the cell of the whole word. -/
@[expose] def cyk : Bool :=
  if w = [] then G.nilRule else G.initial ∈ table G w w.length 0 w.length

/-! ### Correctness -/

variable {G w}

omit [DecidableEq T] [DecidableEq G.NT] in
private theorem mem_foldl_elim {α β : Type*} [DecidableEq β] (f : α → Option β) (l : List α)
    (acc : List β) (b : β) : b ∈ l.foldl (fun acc r => (f r).elim acc (acc.insert ·)) acc ↔
      b ∈ acc ∨ ∃ r ∈ l, f r = some b := by
  induction l generalizing acc with
  | nil => simp
  | cons r l ih =>
    rw [List.foldl_cons, ih]
    cases h : f r with
    | none => simp [h]
    | some c => simp only [Option.elim_some, List.mem_insert_iff]; grind

omit [DecidableEq T] [DecidableEq G.NT] in
private theorem nodup_foldl_elim {α β : Type*} [DecidableEq β] (f : α → Option β) (l : List α)
    {acc : List β} (h : acc.Nodup) :
    (l.foldl (fun acc r => (f r).elim acc (acc.insert ·)) acc).Nodup := by
  induction l generalizing acc with
  | nil => exact h
  | cons r l ih =>
    rw [List.foldl_cons]
    refine ih ?_
    cases f r with
    | none => exact h
    | some c => exact h.insert

omit [DecidableEq T] in
/-- A scan adds exactly the matches of the rules. -/
theorem mem_scan {f : ChomskyNormalFormRule T G.NT → Option G.NT} {acc : List G.NT} {A : G.NT} :
    A ∈ scan G f acc ↔ A ∈ acc ∨ ∃ r ∈ G.rules, f r = some A :=
  mem_foldl_elim f G.rules acc A

omit [DecidableEq T] in
/-- A scan adds no repetitions. -/
theorem nodup_scan {f : ChomskyNormalFormRule T G.NT → Option G.NT} {acc : List G.NT}
    (h : acc.Nodup) : (scan G f acc).Nodup :=
  nodup_foldl_elim f G.rules h

theorem mem_leafCell {i : ℕ} {A : G.NT} :
    A ∈ leafCell G w i ↔ ∃ a, w[i]? = some a ∧ leaf A a ∈ G.rules := by
  rw [leafCell, mem_scan]
  constructor
  · rintro (h | ⟨r, hr, h⟩)
    · simp at h
    · cases r with
      | leaf B a =>
        simp only [leafMatch, Option.ite_none_right_eq_some, Option.some.injEq] at h
        obtain ⟨h, rfl⟩ := h
        exact ⟨a, h, hr⟩
      | node => simp [leafMatch] at h
  · rintro ⟨a, h, hr⟩
    exact Or.inr ⟨leaf A a, hr, by simp [leafMatch, h]⟩

omit [DecidableEq T] in
theorem mem_nodeCell {tbl : Table G} {i l : ℕ} {A : G.NT} :
    A ∈ nodeCell G tbl i l ↔ ∃ k < l - 1, ∃ B C, node A B C ∈ G.rules ∧
      B ∈ tbl i (k + 1) ∧ C ∈ tbl (i + k + 1) (l - k - 1) := by
  have key : ∀ (ks : List ℕ) (acc : List G.NT), A ∈ ks.foldl (fun acc k =>
      scan G (nodeMatch G (tbl i (k + 1)) (tbl (i + k + 1) (l - k - 1))) acc) acc ↔
      A ∈ acc ∨ ∃ k ∈ ks, ∃ B C, node A B C ∈ G.rules ∧
        B ∈ tbl i (k + 1) ∧ C ∈ tbl (i + k + 1) (l - k - 1) := by
    intro ks
    induction ks with
    | nil => simp
    | cons k ks ih =>
      intro acc
      rw [List.foldl_cons, ih, mem_scan]
      constructor
      · rintro ((h | ⟨r, hr, h⟩) | ⟨k', hk', h⟩)
        · exact Or.inl h
        · cases r with
          | leaf => simp [nodeMatch] at h
          | node A' B C =>
            simp only [nodeMatch, Option.ite_none_right_eq_some, Option.some.injEq] at h
            obtain ⟨⟨hB, hC⟩, rfl⟩ := h
            exact Or.inr ⟨k, List.mem_cons_self, B, C, hr, hB, hC⟩
        · exact Or.inr ⟨k', List.mem_cons_of_mem _ hk', h⟩
      · rintro (h | ⟨k', hk', B, C, hr, hB, hC⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hk' with rfl | hk'
          · exact Or.inl (Or.inr ⟨node A B C, hr, by simp [nodeMatch, hB, hC]⟩)
          · exact Or.inr ⟨k', hk', B, C, hr, hB, hC⟩
  rw [nodeCell, key]
  simp

omit [DecidableEq T] [DecidableEq G.NT] in
private theorem foldl_setCell (c : ℕ → List G.NT) (l : ℕ) (is : List ℕ) (tbl : Table G)
    (i' l' : ℕ) : is.foldl (fun t i => setCell G t i l (c i)) tbl i' l' =
      if l' = l ∧ i' ∈ is then c i' else tbl i' l' := by
  induction is generalizing tbl with
  | nil => simp
  | cons i is ih =>
    rw [List.foldl_cons, ih]
    by_cases h₁ : l' = l <;> by_cases h₂ : i' ∈ is <;> by_cases h₃ : i' = i <;>
      simp_all [setCell]

/-- Filling level `l` sets the cells of length `l` that fit in the word, and nothing else. -/
theorem level_apply (tbl : Table G) (l i' l' : ℕ) :
    level G w tbl l i' l' =
      if l' = l ∧ i' + l ≤ w.length then cell G w tbl i' l else tbl i' l' := by
  rw [level, foldl_setCell]
  congr 1
  simp only [List.mem_range]
  apply propext
  constructor <;> rintro ⟨rfl, h⟩ <;> exact ⟨rfl, by omega⟩

omit [DecidableEq T] [DecidableEq G.NT] in
private theorem exists_split_iff {s : List T} {P : List T → List T → Prop} :
    (∃ u v, u ≠ [] ∧ v ≠ [] ∧ s = u ++ v ∧ P u v) ↔
      ∃ k < s.length - 1, P (s.take (k + 1)) (s.drop (k + 1)) := by
  constructor
  · rintro ⟨u, v, hu, hv, rfl, h⟩
    have hu' := List.length_pos_of_ne_nil hu
    have hv' := List.length_pos_of_ne_nil hv
    refine ⟨u.length - 1, by simp only [List.length_append]; omega, ?_⟩
    rw [Nat.sub_add_cancel hu', List.take_left, List.drop_left]
    exact h
  · rintro ⟨k, hk, h⟩
    refine ⟨_, _, ?_, ?_, (List.take_append_drop (k + 1) s).symm, h⟩
    · simp only [ne_eq, List.take_eq_nil_iff, not_or]
      exact ⟨by omega, List.ne_nil_of_length_pos (by omega)⟩
    · simp only [ne_eq, List.drop_eq_nil_iff, not_le]
      omega

/-- The cell of length `L + 1` at `i` lists exactly the nonterminals deriving the subword, given
that the table is correct for all shorter subwords. -/
private theorem mem_cell_iff {tbl : Table G} {L i : ℕ} (hi : i + (L + 1) ≤ w.length)
    (htbl : ∀ i l, 0 < l → l ≤ L → i + l ≤ w.length → ∀ A : G.NT,
      A ∈ tbl i l ↔ G.toCFG.Derives [.nonterminal A] (((w.drop i).take l).map .terminal))
    (A : G.NT) :
    A ∈ cell G w tbl i (L + 1) ↔
      G.toCFG.Derives [.nonterminal A] (((w.drop i).take (L + 1)).map .terminal) := by
  set s := (w.drop i).take (L + 1) with hs
  have hlen : s.length = L + 1 := by grind
  have hne : s ≠ [] := List.ne_nil_of_length_pos (by omega)
  rw [derives_iff_of_ne_nil hne]
  rcases L with _ | L
  · -- a single letter
    have hsi : s = [w[i]] := by
      rw [hs, List.drop_eq_getElem_cons (by omega)]
      rfl
    rw [cell, ite_eq_left rfl, mem_leafCell, List.getElem?_eq_getElem (by omega)]
    constructor
    · rintro ⟨a, ha, hr⟩
      exact Or.inl ⟨a, by rw [hsi, Option.some.inj ha], hr⟩
    · rintro (⟨a, ha, hr⟩ | ⟨B, C, u, v, -, hu, hv, huv, -⟩)
      · rw [hsi, List.singleton_inj] at ha
        exact ⟨a, by rw [ha], hr⟩
      · have := congrArg List.length huv
        rw [hlen, List.length_append] at this
        have := List.length_pos_of_ne_nil hu
        have := List.length_pos_of_ne_nil hv
        omega
  · -- at least two letters
    rw [cell, ite_eq_right (by omega), mem_nodeCell]
    have hleft : ¬ ∃ a, s = [a] ∧ leaf A a ∈ G.rules := by
      rintro ⟨a, ha, -⟩
      rw [ha, List.length_singleton] at hlen
      omega
    rw [or_iff_right hleft]
    have e : (∃ B C u v, node A B C ∈ G.rules ∧ u ≠ [] ∧ v ≠ [] ∧ s = u ++ v ∧
          G.toCFG.Derives [.nonterminal B] (u.map .terminal) ∧
          G.toCFG.Derives [.nonterminal C] (v.map .terminal)) ↔
        ∃ u v, u ≠ [] ∧ v ≠ [] ∧ s = u ++ v ∧ ∃ B C, node A B C ∈ G.rules ∧
          G.toCFG.Derives [.nonterminal B] (u.map .terminal) ∧
          G.toCFG.Derives [.nonterminal C] (v.map .terminal) :=
      ⟨fun ⟨B, C, u, v, hr, hu, hv, he, hB, hC⟩ => ⟨u, v, hu, hv, he, B, C, hr, hB, hC⟩,
        fun ⟨u, v, hu, hv, he, B, C, hr, hB, hC⟩ => ⟨B, C, u, v, hr, hu, hv, he, hB, hC⟩⟩
    rw [e, exists_split_iff, hlen]
    refine exists_congr fun k => and_congr_right fun hk => ?_
    have h1 : s.take (k + 1) = (w.drop i).take (k + 1) := by
      rw [hs, List.take_take]
      congr 1
      omega
    have h2 : s.drop (k + 1) = (w.drop (i + k + 1)).take (L + 1 + 1 - k - 1) := by
      rw [hs, List.drop_take, List.drop_drop, Nat.sub_sub, ← Nat.add_assoc]
    rw [h1, h2]
    refine exists_congr fun B => exists_congr fun C => and_congr_right fun _ => and_congr ?_ ?_
    · exact htbl i (k + 1) (by omega) (by omega) (by omega) B
    · refine htbl (i + k + 1) (L + 1 + 1 - k - 1) ?_ ?_ ?_ C
      all_goals omega

/-- **Correctness of the CYK table**: after filling the levels `1, …, L`, the cell of a subword of
length `l ≤ L` lists exactly the nonterminals deriving it. -/
theorem mem_table_iff {L i l : ℕ} (hl : 0 < l) (hlL : l ≤ L) (hi : i + l ≤ w.length)
    (A : G.NT) :
    A ∈ table G w L i l ↔
      G.toCFG.Derives [.nonterminal A] (((w.drop i).take l).map .terminal) := by
  induction L generalizing i l A with
  | zero => omega
  | succ L ih =>
    rw [table, level_apply]
    split_ifs with h
    · obtain ⟨rfl, -⟩ := h
      exact mem_cell_iff hi (fun i l hl hlL hi A => ih hl hlL hi A) A
    · have : l ≤ L := by
        by_contra h'
        exact h ⟨by omega, by omega⟩
      exact ih hl this hi A

/-- **Correctness of CYK** [Hopcroft, Motwani and Ullman, Section 7.4.4][Hopcroft2006]: the test
accepts exactly the words of the language of the grammar. -/
theorem cyk_eq_true_iff : cyk G w = true ↔ w ∈ G.toCFG.language := by
  rw [cyk]
  split_ifs with hw
  · subst hw
    exact mem_language_nil_iff.symm
  · rw [decide_eq_true_iff, mem_table_iff (List.length_pos_of_ne_nil hw) le_rfl (by simp)]
    simp

/-- Membership in the language of a grammar in Chomsky normal form is decidable, by CYK. -/
instance decidableMemLanguage : DecidablePred (· ∈ G.toCFG.language) :=
  fun w => decidable_of_iff _ (cyk_eq_true_iff (G := G) (w := w))

/-! ### Size of the cells -/

/-- Every nonterminal in a cell is the left-hand side of a rule. -/
theorem exists_rule_of_mem_cell {tbl : Table G} {i l : ℕ} {A : G.NT}
    (h : A ∈ cell G w tbl i l) : ∃ r ∈ G.rules, r.input = A := by
  unfold cell at h
  split_ifs at h
  · obtain ⟨a, -, hr⟩ := mem_leafCell.mp h
    exact ⟨_, hr, rfl⟩
  · obtain ⟨k, -, B, C, hr, -⟩ := mem_nodeCell.mp h
    exact ⟨_, hr, rfl⟩

theorem nodup_cell (tbl : Table G) (i l : ℕ) : (cell G w tbl i l).Nodup := by
  unfold cell nodeCell leafCell
  split_ifs
  · exact nodup_scan List.nodup_nil
  · suffices ∀ (ks : List ℕ) (acc : List G.NT), acc.Nodup → (ks.foldl (fun acc k =>
        scan G (nodeMatch G (tbl i (k + 1)) (tbl (i + k + 1) (l - k - 1))) acc) acc).Nodup from
      this _ _ List.nodup_nil
    intro ks
    induction ks with
    | nil => exact fun _ h => h
    | cons k ks ih => exact fun acc h => ih _ (nodup_scan h)

/-- A cell has at most one entry per rule. -/
theorem length_cell_le (tbl : Table G) (i l : ℕ) : (cell G w tbl i l).length ≤ G.rules.length := by
  have hsub : cell G w tbl i l ⊆ G.rules.map ChomskyNormalFormRule.input := fun A hA => by
    obtain ⟨r, hr, rfl⟩ := exists_rule_of_mem_cell hA
    exact List.mem_map_of_mem hr
  simpa using ((nodup_cell tbl i l).subperm hsub).length_le

/-- Every cell of the table is a list without repetitions of at most `|R|` nonterminals, for a
grammar with `|R|` rules. -/
theorem nodup_table_and_length_le (L i l : ℕ) :
    (table G w L i l).Nodup ∧ (table G w L i l).length ≤ G.rules.length := by
  induction L generalizing i l with
  | zero => simp [table]
  | succ L ih =>
    rw [table, level_apply]
    split_ifs
    · exact ⟨nodup_cell _ _ _, length_cell_le _ _ _⟩
    · exact ih i l

/-! ### Cost -/

open TimeM

variable (G w)

/-- `scan` in `TimeM`, charging one unit per rule examined. -/
@[expose] def scanM (f : ChomskyNormalFormRule T G.NT → Option G.NT) (acc : List G.NT) :
    TimeM ℕ (List G.NT) :=
  G.rules.foldlM (fun acc r => do ✓ return (f r).elim acc (acc.insert ·)) acc

/-- `leafCell` in `TimeM`: one unit to read the letter, and one scan. -/
@[expose] def leafCellM (i : ℕ) : TimeM ℕ (List G.NT) := do
  ✓ scanM G (leafMatch G w[i]?) []

/-- `nodeCell` in `TimeM`: for each split point, one unit to read the two subcells, and one
scan. -/
@[expose] def nodeCellM (tbl : Table G) (i l : ℕ) : TimeM ℕ (List G.NT) :=
  (List.range (l - 1)).foldlM (fun acc k => do
    ✓ scanM G (nodeMatch G (tbl i (k + 1)) (tbl (i + k + 1) (l - k - 1))) acc) []

/-- `cell` in `TimeM`. -/
@[expose] def cellM (tbl : Table G) (i l : ℕ) : TimeM ℕ (List G.NT) :=
  if l = 1 then leafCellM G w i else nodeCellM G tbl i l

/-- `level` in `TimeM`. -/
@[expose] def levelM (tbl : Table G) (l : ℕ) : TimeM ℕ (Table G) :=
  (List.range (w.length + 1 - l)).foldlM (fun t i => do
    let c ← cellM G w tbl i l
    return setCell G t i l c) tbl

/-- `table` in `TimeM`. -/
@[expose] def tableM : ℕ → TimeM ℕ (Table G)
  | 0 => return fun _ _ => []
  | L + 1 => do
    let tbl ← tableM L
    levelM G w tbl (L + 1)

/-- CYK in `TimeM`. -/
@[expose] def cykM : TimeM ℕ Bool :=
  if w = [] then return G.nilRule else do
    let tbl ← tableM G w w.length
    return G.initial ∈ tbl 0 w.length

/-- The charge for one cell of length `l`. -/
def cellCost (l : ℕ) : ℕ :=
  if l = 1 then G.rules.length + 1 else (l - 1) * (G.rules.length + 1)

omit [DecidableEq T] in
@[simp] theorem ret_scanM (f) (acc) : (scanM G f acc).ret = scan G f acc := by
  rw [scanM, ret_foldlM]
  rfl

omit [DecidableEq T] in
@[simp] theorem time_scanM (f) (acc) : (scanM G f acc).time = G.rules.length := by
  rw [scanM, time_foldlM_of_time_eq _ _ _ (c := 1) (fun _ _ => rfl), mul_one]

@[simp] theorem ret_cellM (tbl : Table G) (i l : ℕ) :
    (cellM G w tbl i l).ret = cell G w tbl i l := by
  unfold cellM cell
  split_ifs
  · simp [leafCellM, leafCell]
  · rw [nodeCellM, ret_foldlM]
    simp [nodeCell]

theorem time_cellM (tbl : Table G) (i l : ℕ) : (cellM G w tbl i l).time = cellCost G l := by
  unfold cellM cellCost
  split_ifs
  · simp [leafCellM, Nat.add_comm]
  · rw [nodeCellM, time_foldlM_of_time_eq _ _ _ (c := 1 + G.rules.length)
      (fun _ _ => by simp), List.length_range, Nat.add_comm 1]

@[simp] theorem ret_levelM (tbl : Table G) (l : ℕ) :
    (levelM G w tbl l).ret = level G w tbl l := by
  rw [levelM, ret_foldlM]
  simp [level]

theorem time_levelM (tbl : Table G) (l : ℕ) :
    (levelM G w tbl l).time = (w.length + 1 - l) * cellCost G l := by
  rw [levelM, time_foldlM_of_time_eq _ _ _ (c := cellCost G l)
    (fun _ _ => by simp [time_cellM]), List.length_range]

@[simp] theorem ret_tableM (L : ℕ) : (tableM G w L).ret = table G w L := by
  induction L with
  | zero => rfl
  | succ L ih => simp [tableM, table, ih]

theorem time_tableM (L : ℕ) :
    (tableM G w L).time = ∑ j ∈ Finset.range L, (w.length - j) * cellCost G (j + 1) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [tableM, time_bind, ih, time_levelM, Finset.sum_range_succ, Nat.add_sub_add_right]

/-- `cykM` computes `cyk`. -/
@[simp] theorem ret_cykM : (cykM G w).ret = cyk G w := by
  unfold cykM cyk
  split_ifs <;> simp

private theorem sum_sub_mul (n : ℕ) :
    ∑ j ∈ Finset.range n, (n - j) * j = (n + 1).choose 3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : ∀ j ∈ Finset.range n, (n + 1 - j) * j = (n - j) * j + j := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Nat.sub_add_comm hj.le, Nat.succ_mul]
    have hs : ∑ j ∈ Finset.range n, j + n = (n + 1).choose 2 := by
      rw [Nat.choose_two_right, ← Finset.sum_range_id]
      exact (Finset.sum_range_succ _ _).symm
    rw [Finset.sum_range_succ, Nat.add_sub_cancel_left, one_mul, Finset.sum_congr rfl h,
      Finset.sum_add_distrib, ih, add_assoc, hs, add_comm]
    exact (Nat.choose_succ_succ (n + 1) 2).symm

/-- **Cost of CYK**: exactly `(|R| + 1) (n + C(n + 1, 3))` charged steps on a word of length `n`,
for a grammar with `|R|` rules (`n` cells of length one, and `C(n + 1, 3)` pairs of a longer cell
and a split point). The empty word costs nothing. -/
theorem time_cykM :
    (cykM G w).time = (G.rules.length + 1) * (w.length + (w.length + 1).choose 3) := by
  unfold cykM
  split_ifs with hw
  · subst hw
    rfl
  rw [time_bind, time_tableM, time_pure, add_zero]
  obtain ⟨n, hn⟩ : ∃ n, w.length = n + 1 :=
    Nat.exists_eq_add_one_of_ne_zero (by simpa using hw)
  rw [hn, Finset.sum_range_succ', Nat.sub_zero]
  have h : ∀ j ∈ Finset.range n, (n + 1 - (j + 1)) * cellCost G (j + 1 + 1) =
      (G.rules.length + 1) * ((n - j) * (j + 1)) := by
    intro j _
    rw [cellCost, ite_eq_right (by omega), Nat.add_sub_cancel, Nat.add_sub_add_right]
    ring
  have hsum : ∑ j ∈ Finset.range n, (n - j) * (j + 1) = (n + 1 + 1).choose 3 := by
    rw [← sum_sub_mul (n + 1), Finset.sum_range_succ', mul_zero, add_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_sub_add_right]
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, hsum,
    show cellCost G (0 + 1) = G.rules.length + 1 from rfl]
  ring

/-- **CYK runs in cubic time**: at most `(|R| + 1) (n + 1)³` charged steps on a word of length
`n`, for a grammar with `|R|` rules. -/
theorem time_cykM_le : (cykM G w).time ≤ (G.rules.length + 1) * (w.length + 1) ^ 3 := by
  rw [time_cykM]
  refine Nat.mul_le_mul_left _ ?_
  set n := w.length
  have h : (n + 1).choose 3 ≤ n ^ 3 := by
    rw [← sum_sub_mul]
    calc ∑ j ∈ Finset.range n, (n - j) * j ≤ ∑ _j ∈ Finset.range n, n * n :=
          Finset.sum_le_sum fun j hj => Nat.mul_le_mul (Nat.sub_le _ _)
            (Finset.mem_range.mp hj).le
      _ = n ^ 3 := by rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]; ring
  calc n + (n + 1).choose 3 ≤ n + n ^ 3 := Nat.add_le_add_left h _
    _ ≤ (n + 1) ^ 3 := by nlinarith [Nat.zero_le n]

end Cslib.Algorithms.Lean.CYK
