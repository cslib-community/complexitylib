/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.List.Lex

/-!
# The left set of `SAT`

The *left set* of a problem `A ∈ NP`, for a witness relation of `A`, consists of the pairs
`(x, w)` of an instance `x ∈ A` and a candidate witness `w` that is lexicographically at most the
largest witness of `x` [Arvind, Köbler and Mundhenk, Definition 2.3][ArvindKoblerMundhenk1992].
It is the device of Ogiwara and Watanabe's proof that sparse sets are not `NP`-hard under bounded
truth-table reductions unless `P = NP` [OgiwaraWatanabe1991]: the left-set members among the
candidate prefixes of a level of the search tree are exactly those at most the prefix of the
largest witness, so the boundary of the left set locates that prefix.

For `SAT`, a witness of a formula `φ` lists the values of a satisfying assignment at the literal
occurrences of `φ`, in order (`φ.vars`), as in the self-reduction of
`Complexity/Computability/Complexity/Classes/NP/SelfReduction.lean`. So `(φ, w) ∈ LeftSAT` when
`w` has one bit per occurrence and some satisfying assignment, read along the occurrences, gives
a word lexicographically at least `w` (`Cslib.Complexity.LeftSAT`). Words are compared in Mathlib's
lexicographic order on `List Bool`, with `false < true`.

The clauses `SAT.atLeast a` say that the values of the occurrences fixed by a list of literals `a`
are lexicographically at least the values `a` gives them (`Cslib.Complexity.SAT.eval_atLeast`):
for every position `j` where `a` has `true`, the assignment has `true` there or at an earlier
position where `a` has `false`. Adding them to `φ` reduces the left set to `SAT`
(`Cslib.Complexity.LeftSAT_polyTimeReducible_SAT`), so the left set is in `NP`
(`Cslib.Complexity.LeftSAT_mem_NP`). Conversely `SAT` reduces to its left set, by pairing a
formula with the all-`false` word (`Cslib.Complexity.SAT_polyTimeReducible_LeftSAT`).

The search procedures query the left set at prefixes: a node of the self-reduction tree fixes the
first occurrences of `φ`, and `SAT.atLeast a ++ φ` is satisfiable exactly when the values of the
node `a`, padded with `false`, form a member of the left set
(`Cslib.Complexity.SAT.atLeast_append_mem_SAT_iff_mem_LeftSAT`). For a fixed formula the members
form an initial segment of the words of the right length (`Cslib.Complexity.LeftSAT.mem_of_le`):
the words at most the largest witness. Its largest member is a witness
(`Cslib.Complexity.LeftSAT.exists_eq_map_of_maximal`), so membership queries find a satisfying
assignment, which is the search-to-decision property behind the left-set technique.

## Main definitions

* `Cslib.Complexity.SAT.atLeast`: clauses saying that an assignment is lexicographically at least
  the values of a list of literals.
* `Cslib.Complexity.LeftSAT`: the left set of `SAT`.

## Main results

* `Cslib.Complexity.SAT.eval_atLeast`, `Cslib.Complexity.SAT.atLeast_append_mem_SAT_iff`: the
  meaning of `SAT.atLeast`.
* `Cslib.Complexity.mem_LeftSAT_iff_atLeast`,
  `Cslib.Complexity.SAT.atLeast_append_mem_SAT_iff_mem_LeftSAT`: membership in the left set, of
  words and of prefixes, as satisfiability.
* `Cslib.Complexity.LeftSAT.mem_of_le`, `Cslib.Complexity.LeftSAT.exists_eq_map_of_maximal`: the
  left set of a formula is an initial segment, and its largest member is a witness.
* `Cslib.Complexity.LeftSAT_polyTimeReducible_SAT`, `Cslib.Complexity.LeftSAT_mem_NP`,
  `Cslib.Complexity.SAT_polyTimeReducible_LeftSAT`: the left set and `SAT` reduce to each other,
  and the left set is in `NP`.

## References

* [V. Arvind, J. Köbler, M. Mundhenk, *On Bounded Truth-Table, Conjunctive, and Randomized
  Reductions to Sparse Sets*][ArvindKoblerMundhenk1992]
* [M. Ogiwara, O. Watanabe, *On polynomial-time bounded truth-table reducibility of NP sets to
  sparse sets*][OgiwaraWatanabe1991]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

namespace SAT

/-! ### Lexicographic lower bounds as clauses -/

/-- **The clauses saying that an assignment is lexicographically at least the values of `a`**,
read along the variables of `a`: for each position `j` where `a` has the value `true`, the clause
that one of the variables of `a` at a position before `j` with the value `false`, or the variable
at `j`, is true. -/
def atLeast (a : List (Literal ℕ)) : CNF ℕ :=
  (a.zipIdx.filter fun ((_, b), _) => b).map fun ((v, _), j) =>
    ((a.take j).filter fun (_, b) => !b).map (fun (u, _) => (u, true)) ++ [(v, true)]

@[simp] theorem atLeast_nil : atLeast [] = [] := rfl

/-- A first position with the value `true` adds the unit clause of its variable. -/
theorem atLeast_cons_true (v : ℕ) (a : List (Literal ℕ)) :
    atLeast ((v, true) :: a) = [(v, true)] :: atLeast a := by
  simp only [atLeast, List.zipIdx_cons, List.zipIdx_succ, List.filter_cons, List.filter_map]
  simp [Function.comp_def, List.take_succ_cons]

/-- A first position with the value `false` adds its variable to every clause. -/
theorem atLeast_cons_false (v : ℕ) (a : List (Literal ℕ)) :
    atLeast ((v, false) :: a) = (atLeast a).map ((v, true) :: ·) := by
  simp only [atLeast, List.zipIdx_cons, List.zipIdx_succ, List.filter_cons, List.filter_map,
    List.map_map]
  simp [Function.comp_def, List.take_succ_cons]

/-- **`SAT.atLeast a` holds exactly when the assignment is lexicographically at least `a`**, read
along the variables of `a`. -/
theorem eval_atLeast (σ : ℕ → Bool) (a : List (Literal ℕ)) :
    (atLeast a).eval σ = true ↔ a.map Prod.snd ≤ a.map fun l => σ l.1 := by
  induction a with
  | nil => simp
  | cons l a ih =>
    obtain ⟨v, b⟩ := l
    have h₁ : ¬(true < false) := by decide
    have h₃ : false < true := by decide
    simp only [List.map_cons, List.cons_le_cons_iff']
    cases b with
    | true =>
      rw [atLeast_cons_true, CNF.eval_cons, Bool.and_eq_true, ih]
      rcases hv : σ v <;> simp [hv, h₁]
    | false =>
      rw [atLeast_cons_false, CNF.eval_eq_true_iff]
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        Clause.eval_cons, Literal.eval_mk, Bool.or_eq_true, beq_iff_eq]
      rw [← ih, CNF.eval_eq_true_iff]
      cases σ v <;> simp [h₃]

/-- **Satisfiability with a lexicographic lower bound:** `SAT.atLeast a ++ φ` is satisfiable
exactly when some satisfying assignment of `φ` is lexicographically at least `a`. -/
theorem atLeast_append_mem_SAT_iff {a : List (Literal ℕ)} {φ : CNF ℕ} :
    atLeast a ++ φ ∈ SAT ↔ ∃ σ, φ.eval σ = true ∧ a.map Prod.snd ≤ a.map fun l => σ l.1 := by
  simp only [mem_SAT, CNF.Satisfiable, CNF.eval_append, Bool.and_eq_true, eval_atLeast]
  exact exists_congr fun σ => and_comm

end SAT

/-! ### The left set -/

/-- **The left set of `SAT`** [Arvind, Köbler and Mundhenk, Definition 2.3]
[ArvindKoblerMundhenk1992]: the pairs `(φ, w)` of a formula `φ` and a word `w` with one bit for
each literal occurrence of `φ`, such that the values of some satisfying assignment of `φ` at its
occurrences, read in order, form a word lexicographically at least `w`. The witnesses of `φ` are
these words of values, and `w` is in the left set exactly when it is at most the largest of
them. -/
def LeftSAT : Set (CNF ℕ × List Bool) :=
  {(φ, w) | w.length = φ.vars.length ∧ ∃ σ, φ.eval σ = true ∧ w ≤ φ.vars.map σ}

theorem mem_LeftSAT {φ : CNF ℕ} {w : List Bool} :
    (φ, w) ∈ LeftSAT ↔ w.length = φ.vars.length ∧ ∃ σ, φ.eval σ = true ∧ w ≤ φ.vars.map σ :=
  Iff.rfl

/-- The left set of a formula is an initial segment of the words of the right length. -/
theorem LeftSAT.mem_of_le {φ : CNF ℕ} {w w' : List Bool} (h : (φ, w) ∈ LeftSAT)
    (hlen : w'.length = w.length) (hle : w' ≤ w) : (φ, w') ∈ LeftSAT := by
  obtain ⟨hw, σ, hσ, hwσ⟩ := h
  exact ⟨hlen.trans hw, σ, hσ, hle.trans hwσ⟩

/-- **The largest member of the left set of a formula is a witness**, so searching for it with
membership queries, for example bit by bit, finds a satisfying assignment. -/
theorem LeftSAT.exists_eq_map_of_maximal {φ : CNF ℕ} {w : List Bool} (h : (φ, w) ∈ LeftSAT)
    (hmax : ∀ w' : List Bool, w'.length = w.length → w < w' → (φ, w') ∉ LeftSAT) :
    ∃ σ, φ.eval σ = true ∧ w = φ.vars.map σ := by
  obtain ⟨hw, σ, hσ, hwσ⟩ := h
  refine ⟨σ, hσ, (lt_or_eq_of_le hwσ).resolve_left fun hlt => hmax _ ?_ hlt ⟨?_, σ, hσ, le_rfl⟩⟩
  all_goals simp [hw]

/-- **Membership in the left set as satisfiability:** pair the occurrences of `φ` with the bits of
`w`, and require the assignment to be lexicographically at least them. -/
theorem mem_LeftSAT_iff_atLeast {φ : CNF ℕ} {w : List Bool} :
    (φ, w) ∈ LeftSAT ↔ w.length = φ.vars.length ∧ SAT.atLeast (φ.vars.zip w) ++ φ ∈ SAT := by
  rw [mem_LeftSAT, SAT.atLeast_append_mem_SAT_iff]
  refine and_congr_right fun hw => exists_congr fun σ => and_congr_right fun _ => ?_
  have hsnd : (φ.vars.zip w).map Prod.snd = w := List.map_snd_zip (by omega)
  have hfst : ((φ.vars.zip w).map fun l => σ l.1) = φ.vars.map σ := by
    rw [show (fun l : ℕ × Bool => σ l.1) = σ ∘ Prod.fst from rfl, ← List.map_map,
      List.map_fst_zip (by omega)]
  rw [hsnd, hfst]

/-- The all-`false` word is lexicographically least among the words of its length. -/
private theorem replicate_false_le : ∀ {w : List Bool}, List.replicate w.length false ≤ w
  | [] => le_rfl
  | b :: w => by
    rw [List.length_cons, List.replicate_succ, List.cons_le_cons_iff']
    cases b
    · exact .inr ⟨rfl, replicate_false_le⟩
    · exact .inl rfl

/-- A word padded with `false` is at most a word of the same length exactly when it is at most
the prefix of that word of its own length. -/
private theorem append_replicate_false_le_iff :
    ∀ {y v : List Bool}, y.length ≤ v.length →
      (y ++ List.replicate (v.length - y.length) false ≤ v ↔ y ≤ v.take y.length)
  | [], v, _ => by simpa using replicate_false_le (w := v)
  | b :: y, [], h => by simp at h
  | b :: y, c :: v, h => by
    simp only [List.length_cons, Nat.add_sub_add_right, List.cons_append, List.take_succ_cons,
      List.cons_le_cons_iff']
    rw [append_replicate_false_le_iff (by simpa using h)]

/-- **The search queries the left set at prefixes.** For a node `a` fixing the first occurrences of
`φ`, `SAT.atLeast a ++ φ` is satisfiable exactly when the values of `a`, padded with `false` to one
bit per occurrence, form a member of the left set. -/
theorem SAT.atLeast_append_mem_SAT_iff_mem_LeftSAT {φ : CNF ℕ} {a : List (Literal ℕ)}
    (ha : a.map Prod.fst = φ.vars.take a.length) :
    atLeast a ++ φ ∈ SAT ↔
      (φ, a.map Prod.snd ++ List.replicate (φ.vars.length - a.length) false) ∈ LeftSAT := by
  have hlen : a.length ≤ φ.vars.length := by
    have := congrArg List.length ha
    simp only [List.length_map, List.length_take] at this
    omega
  rw [atLeast_append_mem_SAT_iff, mem_LeftSAT]
  have hlen' : (a.map Prod.snd ++ List.replicate (φ.vars.length - a.length) false).length =
      φ.vars.length := by
    simp only [List.length_append, List.length_map, List.length_replicate]
    omega
  refine ⟨fun ⟨σ, hσ, hle⟩ => ⟨hlen', σ, hσ, ?_⟩, fun ⟨_, σ, hσ, hle⟩ => ⟨σ, hσ, ?_⟩⟩
  all_goals
    have hval : (a.map fun l => σ l.1) = (φ.vars.map σ).take (a.map Prod.snd).length := by
      rw [List.length_map, ← List.map_take, ← ha, List.map_map]
      rfl
  · have := (append_replicate_false_le_iff (y := a.map Prod.snd) (v := φ.vars.map σ)
      (by simpa using hlen)).2 (hval ▸ hle)
    simpa using this
  · rw [hval]
    refine (append_replicate_false_le_iff (by simpa using hlen)).1 ?_
    simpa using hle

/-! ### Reductions -/

/-- `SAT.atLeast` is polynomial-time. -/
@[fun_prop]
theorem SAT.computableInPolyTime_atLeast :
    ComputableInPolyTime atLeast (encList (encPair encNat encBool)) encCNF := by
  unfold atLeast encCNF
  fun_prop

/-- **The left set reduces to `SAT`:** a pair `(φ, w)` with one bit per occurrence goes to
`φ` with the clauses saying that the assignment is at least `w`, and any other pair to the
unsatisfiable formula with an empty clause. -/
theorem LeftSAT_polyTimeReducible_SAT :
    PolyTimeReducible (encPair encCNF encBits) encCNF LeftSAT SAT := by
  refine ⟨fun (φ, w) => if w.length = φ.vars.length then SAT.atLeast (φ.vars.zip w) ++ φ else [[]],
    ?_, fun ⟨φ, w⟩ => ?_⟩
  · have hw : ComputableInPolyTime (fun p : CNF ℕ × List Bool => p.2) (encPair encCNF encBits)
        (encList encBool) := ComputableInPolyTime.bitsToList.comp (ComputableInPolyTime.snd _ _)
    unfold encCNF
    fun_prop
  · rw [mem_LeftSAT_iff_atLeast]
    dsimp only
    split
    · simp_all
    · simp only [false_and, false_iff, *]
      rintro ⟨σ, hσ⟩
      simp at hσ

/-- **The left set of `SAT` is in `NP`.** -/
theorem LeftSAT_mem_NP : LeftSAT ∈ NP (encPair encCNF encBits) :=
  LeftSAT_polyTimeReducible_SAT.mem_NP SAT.mem_NP

/-- **`SAT` reduces to its left set:** pair a formula with the all-`false` word, which is at most
every witness. -/
theorem SAT_polyTimeReducible_LeftSAT :
    PolyTimeReducible encCNF (encPair encCNF encBits) SAT LeftSAT := by
  refine ⟨fun φ => (φ, List.replicate φ.vars.length false), by fun_prop, fun φ => ?_⟩
  rw [mem_LeftSAT]
  refine ⟨fun ⟨σ, hσ⟩ => ⟨List.length_replicate .., σ, hσ, ?_⟩, fun ⟨_, σ, hσ, _⟩ => ⟨σ, hσ⟩⟩
  simpa using replicate_false_le (w := φ.vars.map σ)

end Cslib.Complexity
