/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Sparse.Fortune
public import Complexity.Computability.Complexity.Problems.SAT.LeftSet
public import Complexity.Computability.Complexity.Reduction.TruthTableVariants
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Foundations.Data.List.EraseDupsBy
import Complexity.Foundations.Data.List.Lex
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Sparse sets hard for `NP` under conjunctive truth-table reductions

If `SAT` reduces to a sparse problem by a polynomial-time conjunctive truth-table reduction, then
`P = NP` (`Cslib.Complexity.Conjunctive.P_eq_NP_of_mem_SPARSE`). This is the case `k = 1` of
Arvind, Köbler and Mundhenk's theorem that a problem in `NP` whose left set is bounded truth-table
reducible to a set conjunctively reducible to a sparse set is in `P`
[Arvind, Köbler and Mundhenk, Theorem 3.4][ArvindKoblerMundhenk1992]: with `k = 1` and the
conjunctive set itself, only their procedure `SEARCH-RIGHT` is needed.

The procedure searches the self-reduction tree of a formula `φ` level by level, as Fortune's does.
The nodes of a level fix the same first occurrences of `φ`, and each level is kept in decreasing
lexicographic order of the values of its nodes. A node `a` is in the left set of `φ` when
`SAT.atLeast a ++ φ` is satisfiable, that is, when some satisfying assignment is lexicographically
at least `a` on the occurrences that `a` fixes (`Cslib.Complexity.SAT.atLeast_append_mem_SAT_iff`,
`Cslib.Complexity.SAT.atLeast_append_mem_SAT_iff_mem_LeftSAT`). The conjunctive reduction gives
the node `a` the queries of `SAT.atLeast a ++ φ`; `a` is in the left set exactly when all its
queries are in the target.

Let `c` be the lexicographically largest satisfiable node of a level, if any. The members of the
left set in the level are exactly the nodes at most `c`. Read in increasing order, the level starts
with a run of members ending at `c`, and the node after `c` is not a member. So the queries of the
nodes up to `c` all lie in the sparse target, and the node after `c` has a query outside it.
`SEARCH-RIGHT` (`Cslib.Complexity.Conjunctive.searchRight`) reads the level in increasing order and
keeps a node exactly when the next node has a query that no node up to it has, provided those
nodes have at most `s` distinct queries, where `s` bounds the number of members of the target no
longer than the queries. It also keeps the last node. It keeps `c`, since the queries up to `c` are
distinct members of the target, and keeps at most `s + 2` nodes, since every kept node but the last
raises the number of distinct queries seen, which stays at most `s` while nodes are kept
(`Cslib.Complexity.Conjunctive.length_searchRight_le`).

The largest satisfiable node of the next level is a child of `c`, so the leaves contain the largest
satisfying leaf when `φ` is satisfiable (`Cslib.Complexity.Conjunctive.accepts_iff`), and the search
runs in polynomial time (`Cslib.Complexity.Conjunctive.computableInPolyTime_accepts`).

The source's `SEARCH-RIGHT` stops once more than `s` distinct queries have been collected at the
nodes where it keeps a predecessor; here the test counts the distinct queries of all nodes read
so far, and the scan reads the whole level, so that every level is one fixed computation.

## Main definitions

* `Cslib.Complexity.Conjunctive.hasNewQuery`, `Cslib.Complexity.Conjunctive.searchRight`: the
  pruning rule `SEARCH-RIGHT`, on a level in increasing order.
* `Cslib.Complexity.Conjunctive.prune`, `Cslib.Complexity.Conjunctive.accepts`: the pruning rule
  on a level in decreasing order, and the decision procedure for `SAT`.

## Main results

* `Cslib.Complexity.Conjunctive.searchRight_sublist`,
  `Cslib.Complexity.Conjunctive.length_searchRight_le`,
  `Cslib.Complexity.Conjunctive.mem_searchRight`: `SEARCH-RIGHT` keeps at most `s + 2` nodes of
  its level, among them the last node of every initial run of nodes whose queries lie in a set
  with at most `s` members, when the next node has a query outside it.
* `Cslib.Complexity.Conjunctive.IsLargest`,
  `Cslib.Complexity.Conjunctive.atLeast_append_mem_SAT_of_le`,
  `Cslib.Complexity.Conjunctive.atLeast_append_notMem_SAT_of_lt`,
  `Cslib.Complexity.Conjunctive.exists_isLargest_child`,
  `Cslib.Complexity.Conjunctive.pairwise_expand`: the nodes of a level in the left set are those
  at most its largest satisfiable node, which has a child that is the largest satisfiable node of
  the next level; expanding keeps levels in decreasing order. The bounded truth-table procedure
  reuses them.
* `Cslib.Complexity.Conjunctive.accepts_iff`: the procedure decides satisfiability when the
  queries come from a conjunctive reduction of `SAT` and few queries of bounded length are in the
  target.
* `Cslib.Complexity.Conjunctive.computableInPolyTime_hasNewQuery`,
  `Cslib.Complexity.Conjunctive.computableInPolyTime_searchRight`,
  `Cslib.Complexity.Conjunctive.computableInPolyTime_accepts`: the test, `SEARCH-RIGHT` and the
  procedure are polynomial-time.
* `Cslib.Complexity.Conjunctive.SAT_mem_P`: if `SAT` conjunctively reduces to a sparse problem,
  `SAT ∈ P`.
* `Cslib.Complexity.Conjunctive.P_eq_NP_of_mem_SPARSE`: the resulting collapse `P = NP`.

## References

* [V. Arvind, J. Köbler, M. Mundhenk, *On Bounded Truth-Table, Conjunctive, and Randomized
  Reductions to Sparse Sets*][ArvindKoblerMundhenk1992]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM SAT

namespace Conjunctive

/-! ### `SEARCH-RIGHT` -/

section SearchRight

variable {α κ : Type*} [DecidableEq κ] (Q : α → List κ) (s : ℕ)

/-- The test of `SEARCH-RIGHT` at the node `z` after the nodes `pre`, with the queries `Q` and the
bound `s`: the queries of the nodes `pre` have at most `s` distinct values, and `z` has a query that
is not among them. -/
def hasNewQuery (pre : List α) (z : α) : Bool :=
  decide (((pre.flatMap Q).eraseDupsBy fun u u' => decide (u = u')).length ≤ s) &&
    (Q z).any fun u => decide (u ∉ pre.flatMap Q)

/-- **`SEARCH-RIGHT`** with the queries `Q` and the bound `s`, on a level in increasing order: keep
each node whose successor `z` passes `hasNewQuery` with the nodes up to the node, and keep the
last node. -/
def searchRight (l : List α) : List α :=
  (((l.zip l.tail).zipIdx.filter fun ((_, z), j) => hasNewQuery Q s (l.take (j + 1)) z).map
    fun ((y, _), _) => y) ++ l.drop (l.length - 1)

variable {Q s}

/-- Pairing the nodes of a list with their successors drops the last node. -/
private theorem map_fst_zip_tail : ∀ l : List α, (l.zip l.tail).map Prod.fst = l.dropLast
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    have ih := map_fst_zip_tail (b :: t)
    rw [List.tail_cons] at ih
    rw [List.tail_cons, List.zip_cons_cons, List.map_cons, ih, List.dropLast_cons_cons]

/-- The distinct queries of the nodes `pre` are as many as `hasNewQuery` counts. -/
private theorem length_eraseDupsBy_flatMap (pre : List α) :
    ((pre.flatMap Q).eraseDupsBy fun u u' => decide (u = u')).length =
      (pre.flatMap Q).toFinset.card := by
  rw [← List.toFinset_card_of_nodup (List.nodup_eraseDupsBy_eq _)]
  congr 1
  ext u
  simp only [List.mem_toFinset, List.mem_eraseDupsBy_eq]

/-- `SEARCH-RIGHT` keeps a sublist of its level. -/
theorem searchRight_sublist (l : List α) : (searchRight Q s l).Sublist l := by
  have hmap : ((l.zip l.tail).zipIdx.map fun ((y, _), _) => y) = l.take (l.length - 1) := by
    rw [← List.dropLast_eq_take, ← map_fst_zip_tail]
    conv_rhs => rw [← List.zipIdx_map_fst 0 (l.zip l.tail)]
    rw [List.map_map]
    rfl
  conv_rhs => rw [← List.take_append_drop (l.length - 1) l]
  exact (hmap ▸ List.filter_sublist.map _).append (List.Sublist.refl _)

/-- A node passing the test of `SEARCH-RIGHT` raises the number of distinct queries seen: the nodes
up to any later node have more distinct queries. -/
private theorem card_lt_of_hasNewQuery {l : List α} {j j' : ℕ} {z : α} (hz : l[j + 1]? = some z)
    (hnew : hasNewQuery Q s (l.take (j + 1)) z = true) (hjj' : j < j') :
    ((l.take (j + 1)).flatMap Q).toFinset.card < ((l.take (j' + 1)).flatMap Q).toFinset.card := by
  rw [hasNewQuery, Bool.and_eq_true, List.any_eq_true] at hnew
  obtain ⟨-, u, hu, hnotin⟩ := hnew
  have hnotin : u ∉ (l.take (j + 1)).flatMap Q := of_decide_eq_true hnotin
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.2 ⟨u, ?_, ?_⟩)
  · intro x hx
    simp only [List.mem_toFinset, List.mem_flatMap] at hx ⊢
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨y, (List.take_prefix_take_left (by omega)).subset hy, hxy⟩
  · simp only [List.mem_toFinset, List.mem_flatMap]
    refine ⟨z, List.mem_of_getElem? (i := j + 1) ?_, hu⟩
    rw [List.getElem?_take]
    simpa [show j + 1 < j' + 1 by omega] using hz
  · simpa using hnotin

/-- **`SEARCH-RIGHT` keeps at most `s + 2` nodes**: the last one, and at most `s + 1` others,
since each raises the number of distinct queries seen, which is at most `s` when it is kept. -/
theorem length_searchRight_le (l : List α) : (searchRight Q s l).length ≤ s + 2 := by
  set P := (l.zip l.tail).zipIdx
  set F := P.filter fun ((_, z), j) => hasNewQuery Q s (l.take (j + 1)) z
  /- The distinct queries seen up to the kept nodes, in order. -/
  set c : ℕ → ℕ := fun j => ((l.take (j + 1)).flatMap Q).toFinset.card
  have hP : P.Pairwise fun p q => p.2 < q.2 := by
    have := List.pairwise_lt_range' (s := 0) (n := (l.zip l.tail).length)
    rw [← List.zipIdx_map_snd 0, List.pairwise_map] at this
    exact this
  have hmemF : ∀ p ∈ F,
      l[p.2 + 1]? = some p.1.2 ∧ hasNewQuery Q s (l.take (p.2 + 1)) p.1.2 = true := by
    intro p hp
    obtain ⟨hpP, hnew⟩ := List.mem_filter.1 hp
    refine ⟨?_, hnew⟩
    have := (List.getElem?_zip_eq_some.1 (List.mem_zipIdx_iff_getElem?.1 hpP)).2
    rwa [List.getElem?_tail] at this
  have hsorted : (F.map fun p => c p.2).Pairwise (· < ·) :=
    List.pairwise_map.2 ((hP.sublist List.filter_sublist).imp_of_mem
      fun hp _ hlt => card_lt_of_hasNewQuery (hmemF _ hp).1 (hmemF _ hp).2 hlt)
  have hsub : (F.map fun p => c p.2) ⊆ List.range (s + 1) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hn
    have hnew := (hmemF p hp).2
    rw [hasNewQuery, Bool.and_eq_true, decide_eq_true_iff, length_eraseDupsBy_flatMap] at hnew
    exact List.mem_range.2 (Nat.lt_succ_of_le hnew.1)
  have hF := List.Nodup.length_le_of_subset (hsorted.imp ne_of_lt) hsub
  rw [List.length_map, List.length_range] at hF
  have hdrop : (l.drop (l.length - 1)).length ≤ 1 := by
    rw [List.length_drop]
    omega
  rw [searchRight, List.length_append, List.length_map]
  exact le_trans (Nat.add_le_add hF hdrop) (by omega)

/-- **`SEARCH-RIGHT` keeps the end of a run of nodes whose queries lie in a small set.** If every
query of the nodes `A` and of `y` lies in a set `K` whose finite subsets have at most `s` members,
and the node after `y`, if any, has a query outside `K`, then `SEARCH-RIGHT` keeps `y`. -/
theorem mem_searchRight {K : Set κ} (hc : ∀ T : Finset κ, (∀ u ∈ T, u ∈ K) → T.card ≤ s)
    {A B : List α} {y : α} (hA : ∀ x ∈ A ++ [y], ∀ u ∈ Q x, u ∈ K)
    (hB : ∀ z ∈ B.head?, ∃ u ∈ Q z, u ∉ K) : y ∈ searchRight Q s (A ++ y :: B) := by
  rw [searchRight, List.mem_append]
  cases B with
  | nil =>
    refine .inr ?_
    simp
  | cons z B =>
    refine .inl (List.mem_map.2 ⟨((y, z), A.length), List.mem_filter.2 ⟨?_, ?_⟩, rfl⟩)
    · rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, List.getElem?_tail]
      simp
    · obtain ⟨u, hu, huK⟩ := hB z (by simp)
      have htake : (A ++ y :: z :: B).take (A.length + 1) = A ++ [y] := by
        simp [List.take_append]
      have hW : ∀ u ∈ (A ++ [y]).flatMap Q, u ∈ K := by
        intro u hu
        obtain ⟨x, hx, hux⟩ := List.mem_flatMap.1 hu
        exact hA x hx u hux
      change hasNewQuery Q s ((A ++ y :: z :: B).take (A.length + 1)) z = true
      rw [htake, hasNewQuery, Bool.and_eq_true, decide_eq_true_iff, length_eraseDupsBy_flatMap,
        List.any_eq_true]
      exact ⟨hc _ fun u hu => hW u (List.mem_toFinset.1 hu),
        u, hu, decide_eq_true fun h => huK (hW u h)⟩

end SearchRight

/-! ### The pruning rule and the search -/

section Prune

variable {α κ : Type*} [DecidableEq κ] (Q : α → List κ) (s : ℕ)

/-- **The pruning rule** with the queries `Q` and the bound `s`, on a level in decreasing order:
`SEARCH-RIGHT` on the level in increasing order. -/
def prune (l : List α) : List α := (searchRight Q s l.reverse).reverse

variable {Q s}

theorem prune_sublist (l : List α) : (prune Q s l).Sublist l :=
  List.reverse_sublist.1 (by simpa [prune] using searchRight_sublist (Q := Q) (s := s) l.reverse)

/-- A pruned level has at most `s + 2` nodes. -/
theorem length_prune_le (l : List α) : (prune Q s l).length ≤ s + 2 := by
  rw [prune, List.length_reverse]
  exact length_searchRight_le _

end Prune

/-- **The decision procedure** with the conjunctive reduction `key` and the bound `s`: search the
self-reduction tree of `φ`, giving the node `a` the queries `key (atLeast a ++ φ)`, and accept
when a leaf is satisfied by the values it fixes. -/
def accepts (key : CNF ℕ → List (List Bool)) (s : ℕ) (φ : CNF ℕ) : Bool :=
  Fortune.acceptsWith (prune (fun a => key (atLeast a ++ φ)) s) φ

/-! ### Correctness -/

section Correctness

variable {φ : CNF ℕ}

/-- A node is satisfiable exactly when some satisfying assignment agrees with its values. -/
private theorem units_append_mem_SAT_iff {a : List (Literal ℕ)} :
    units a ++ φ ∈ SAT ↔ ∃ σ, φ.eval σ = true ∧ a.map Prod.snd = a.map fun l => σ l.1 := by
  simp only [mem_SAT, CNF.Satisfiable, CNF.eval_append, Bool.and_eq_true, eval_units]
  refine exists_congr fun σ => ⟨fun ⟨h, hσ⟩ => ⟨hσ, ?_⟩, fun ⟨hσ, h⟩ => ⟨fun l hl => ?_, hσ⟩⟩
  · exact List.map_congr_left fun l hl => (h l hl).symm
  · exact (List.map_inj_left.1 h l hl).symm

/-- `a` is the lexicographically largest satisfiable node fixing its occurrences. -/
def IsLargest (φ : CNF ℕ) (a : List (Literal ℕ)) : Prop :=
  units a ++ φ ∈ SAT ∧ ∀ b : List (Literal ℕ), b.map Prod.fst = a.map Prod.fst →
    units b ++ φ ∈ SAT → b.map Prod.snd ≤ a.map Prod.snd

/-- Nodes fixing the same occurrences with the same values are equal. -/
private theorem eq_of_map_fst_eq_of_map_snd_eq {a b : List (Literal ℕ)}
    (hfst : a.map Prod.fst = b.map Prod.fst) (hsnd : a.map Prod.snd = b.map Prod.snd) : a = b := by
  rw [← List.zip_unzip a, ← List.zip_unzip b, List.unzip_fst, List.unzip_snd, List.unzip_fst,
    List.unzip_snd, hfst, hsnd]

/-- A node at most the largest satisfiable node is in the left set. -/
theorem atLeast_append_mem_SAT_of_le {c x : List (Literal ℕ)} (hc : IsLargest φ c)
    (hfst : x.map Prod.fst = c.map Prod.fst) (hle : x.map Prod.snd ≤ c.map Prod.snd) :
    atLeast x ++ φ ∈ SAT := by
  obtain ⟨σ, hσ, hcσ⟩ := units_append_mem_SAT_iff.1 hc.1
  refine atLeast_append_mem_SAT_iff.2 ⟨σ, hσ, hle.trans ?_⟩
  have hx : (x.map fun l => σ l.1) = (x.map Prod.fst).map σ := by rw [List.map_map]; rfl
  have hc' : (c.map fun l => σ l.1) = (c.map Prod.fst).map σ := by rw [List.map_map]; rfl
  rw [hcσ, hx, hc', hfst]

/-- A node above the largest satisfiable node is not in the left set. -/
theorem atLeast_append_notMem_SAT_of_lt {c z : List (Literal ℕ)} (hc : IsLargest φ c)
    (hfst : z.map Prod.fst = c.map Prod.fst) (hlt : c.map Prod.snd < z.map Prod.snd) :
    atLeast z ++ φ ∉ SAT := by
  rintro hz
  obtain ⟨σ, hσ, hzσ⟩ := atLeast_append_mem_SAT_iff.1 hz
  /- The node with the values of `σ` is satisfiable, so it is at most `c`. -/
  set b := z.map fun l => (l.1, σ l.1)
  have hb : units b ++ φ ∈ SAT := units_append_mem_SAT_iff.2 ⟨σ, hσ, by simp [b]⟩
  have hbfst : b.map Prod.fst = z.map Prod.fst := by simp [b, Function.comp_def]
  have hbc := hc.2 b (hbfst.trans hfst) hb
  have hbz : b.map Prod.snd = z.map fun l => σ l.1 := by simp [b]
  exact absurd (hzσ.trans (hbz ▸ hbc)) (not_le_of_gt hlt)

/-- Some child of the largest satisfiable node of a level is the largest satisfiable node of the
next level. -/
theorem exists_isLargest_child {c : List (Literal ℕ)} (hc : IsLargest φ c) (v : ℕ) :
    ∃ x, IsLargest φ (c ++ [(v, x)]) := by
  /- A satisfiable node fixing the occurrences of `c` and then `v` is a child of `c`, or extends a
  node below `c`. -/
  have hext : ∀ b : List (Literal ℕ), b.map Prod.fst = c.map Prod.fst ++ [v] →
      units b ++ φ ∈ SAT → (∀ y, b.map Prod.snd < c.map Prod.snd ++ [y]) ∨
        ∃ y, b = c ++ [(v, y)] := by
    intro b hfst hb
    rcases List.eq_nil_or_concat b with rfl | ⟨b', l, rfl⟩
    · simp at hfst
    rw [List.concat_eq_append, List.map_append, List.map_singleton] at hfst
    obtain ⟨hfst', hl⟩ := List.append_inj' hfst rfl
    have hb' : units b' ++ φ ∈ SAT := by
      obtain ⟨σ, hσ, h⟩ := units_append_mem_SAT_iff.1 hb
      rw [List.concat_eq_append, List.map_append, List.map_append] at h
      exact units_append_mem_SAT_iff.2 ⟨σ, hσ, (List.append_inj' h (by simp)).1⟩
    have hlen : (b'.map Prod.snd).length = (c.map Prod.snd).length := by
      simpa using congrArg List.length hfst'
    rcases lt_or_eq_of_le (hc.2 b' hfst' hb') with hlt | heq
    · refine .inl fun y => ?_
      simpa using List.append_lt_append_of_lt_of_length_eq hlt hlen [l.2] [y]
    · refine .inr ⟨l.2, ?_⟩
      rw [List.concat_eq_append, eq_of_map_fst_eq_of_map_snd_eq hfst' heq]
      obtain ⟨u, y⟩ := l
      simp only [List.singleton_inj] at hl
      simp [hl]
  have hle_true : ∀ y : Bool, c.map Prod.snd ++ [y] ≤ c.map Prod.snd ++ [true] := by
    intro y
    cases y
    · exact le_of_lt (List.Lex.append_left _ (List.Lex.rel (by decide)) _)
    · exact le_rfl
  by_cases htrue : units (c ++ [(v, true)]) ++ φ ∈ SAT
  · refine ⟨true, htrue, fun b hfst hb => ?_⟩
    rw [List.map_append, List.map_singleton] at hfst
    rcases hext b hfst hb with hlt | ⟨y, rfl⟩
    · simpa using (hlt true).le
    · simpa using hle_true y
  · obtain ⟨y, hy⟩ := Fortune.exists_child_mem_SAT v hc.1
    cases y
    · refine ⟨false, hy, fun b hfst hb => ?_⟩
      rw [List.map_append, List.map_singleton] at hfst
      rcases hext b hfst hb with hlt | ⟨y, rfl⟩
      · simpa using (hlt false).le
      · cases y
        · exact le_rfl
        · exact absurd hb htrue
    · exact absurd hy htrue

/-- Expanding a level in decreasing order gives a level in decreasing order: the `true` child of a
node comes before its `false` child, and the children of a larger node before those of a smaller
one. -/
theorem pairwise_expand {pre : List ℕ} {nodes : List (List (Literal ℕ))} (v : ℕ)
    (hfst : ∀ a ∈ nodes, a.map Prod.fst = pre)
    (h : nodes.Pairwise fun a b => b.map Prod.snd < a.map Prod.snd) :
    (Fortune.expand v nodes).Pairwise fun a b => b.map Prod.snd < a.map Prod.snd := by
  rw [Fortune.expand, List.pairwise_flatMap]
  refine ⟨fun a _ => ?_, h.imp_of_mem fun ha hb hlt => ?_⟩
  · rw [List.pairwise_pair]
    simpa using List.Lex.append_left _ (List.Lex.rel (by decide : false < true)) (a.map Prod.snd)
  · rename_i a b
    have hlen : (b.map Prod.snd).length = (a.map Prod.snd).length := by
      simpa using congrArg List.length ((hfst b hb).trans (hfst a ha).symm)
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simpa using List.append_lt_append_of_lt_of_length_eq hlt hlen _ _

variable {key : CNF ℕ → List (List Bool)} {K : Set (List Bool)} {s M : ℕ}

/-- **Pruning keeps the largest satisfiable node.** In a level in decreasing order, the nodes up to
the largest satisfiable node `c`, in increasing order, are in the left set, so all their queries are
short members of `K`; the node after `c` is not, so one of its queries is outside `K`. -/
private theorem mem_prune_of_isLargest (hkey : ∀ ψ, ψ ∈ SAT ↔ ∀ w ∈ key ψ, w ∈ K)
    (hM : ∀ a : List (Literal ℕ), (∀ l ∈ a, l.1 ∈ φ.vars) → a.length ≤ φ.vars.length →
      ∀ w ∈ key (atLeast a ++ φ), w.length ≤ M)
    (hc : ∀ T : Finset (List Bool), (∀ w ∈ T, w ∈ K ∧ w.length ≤ M) → T.card ≤ s)
    {pre : List ℕ} (hpre : pre.IsPrefix φ.vars) {l : List (List (Literal ℕ))}
    (hfst : ∀ a ∈ l, a.map Prod.fst = pre)
    (hsort : l.Pairwise fun a b => b.map Prod.snd < a.map Prod.snd)
    {c : List (Literal ℕ)} (hcl : c ∈ l) (hlarge : IsLargest φ c) :
    c ∈ prune (fun a => key (atLeast a ++ φ)) s l := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hcl
  have hsort' := List.pairwise_append.1 hsort
  rw [prune, List.mem_reverse, List.reverse_append, List.reverse_cons, List.append_assoc,
    List.singleton_append]
  refine mem_searchRight (K := {w | w ∈ K ∧ w.length ≤ M}) (fun T hT => hc T hT)
    (fun x hx w hw => ?_) fun z hz => ?_
  · have hxl : x ∈ l₁ ++ c :: l₂ := by
      simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · simp [hx]
      · simp
    have hle : x.map Prod.snd ≤ c.map Prod.snd := by
      simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact (List.rel_of_pairwise_cons hsort'.2.1 hx).le
      · exact le_rfl
    have hxfst := hfst x hxl
    have hnode := Fortune.mem_vars_and_length_le_of_map_fst_eq hpre hxfst
    exact ⟨(hkey _).1 (atLeast_append_mem_SAT_of_le hlarge (hxfst.trans (hfst c hcl).symm) hle)
      w hw, hM x hnode.1 hnode.2 w hw⟩
  · have hzl₁ : z ∈ l₁ := List.mem_reverse.1 (List.mem_of_mem_head? hz)
    have hunsat := atLeast_append_notMem_SAT_of_lt hlarge
      ((hfst z (by simp [hzl₁])).trans (hfst c hcl).symm)
      (hsort'.2.2 z hzl₁ c List.mem_cons_self)
    rw [hkey] at hunsat
    push Not at hunsat
    obtain ⟨w, hw, hwK⟩ := hunsat
    exact ⟨w, hw, fun h => hwK h.1⟩

/-- **Correctness of the procedure.** If the queries `key` reduce `SAT` conjunctively to `K`, the
queries of the nodes of the tree of `φ` have length at most `M`, and every finite set of members of
`K` of length at most `M` has at most `s` elements, then the procedure accepts exactly the
satisfiable `φ`. -/
theorem accepts_iff (hkey : ∀ ψ, ψ ∈ SAT ↔ ∀ w ∈ key ψ, w ∈ K)
    (hM : ∀ a : List (Literal ℕ), (∀ l ∈ a, l.1 ∈ φ.vars) → a.length ≤ φ.vars.length →
      ∀ w ∈ key (atLeast a ++ φ), w.length ≤ M)
    (hc : ∀ T : Finset (List Bool), (∀ w ∈ T, w ∈ K ∧ w.length ≤ M) → T.card ≤ s) :
    accepts key s φ = true ↔ φ ∈ SAT := by
  obtain ⟨hfst, -, hlarge⟩ := Fortune.searchWith_induction
    (prune := prune (fun a => key (atLeast a ++ φ)) s) (φ := φ)
    (fun pre nodes => (∀ a ∈ nodes, a.map Prod.fst = pre) ∧
      (nodes.Pairwise fun a b => b.map Prod.snd < a.map Prod.snd) ∧
      (φ ∈ SAT → ∃ a ∈ nodes, IsLargest φ a))
    ⟨by simp, by simp, fun h => ⟨[], by simp, by simpa [units] using h, fun b hb _ => by
      simp only [List.map_nil, List.map_eq_nil_iff] at hb
      simp [hb]⟩⟩
    fun pre v nodes hpre ⟨hfst, hsort, hlarge⟩ => by
      have hexp : ∀ b ∈ Fortune.expand v nodes, b.map Prod.fst = pre ++ [v] :=
        fun b hb => Fortune.map_fst_of_mem_expand hfst hb
      have hsort' := pairwise_expand v hfst hsort
      refine ⟨fun b hb => hexp b ((prune_sublist _).subset hb),
        hsort'.sublist (prune_sublist _), fun hφ => ?_⟩
      obtain ⟨a, ha, halarge⟩ := hlarge hφ
      obtain ⟨x, hx⟩ := exists_isLargest_child halarge v
      refine ⟨_, mem_prune_of_isLargest hkey hM hc hpre hexp hsort' ?_ hx, hx⟩
      simp only [Fortune.expand, List.mem_flatMap]
      exact ⟨a, ha, by cases x <;> simp⟩
  exact Fortune.acceptsWith_iff_of_searchWith hfst fun h =>
    (hlarge h).imp fun _ ⟨ha, hlarge⟩ => ⟨ha, hlarge.1⟩

end Correctness

/-! ### Polynomial time -/

open ComputableInPolyTime

/-- The encoding of the list of nodes at a level of the tree. -/
local notation "encNodes" => encList (encList (encPair encNat encBool))

section PolyTime

variable {γ α κ : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool} {encK : κ ↪ List Bool}
  [DecidableEq κ]

/-- The test of `SEARCH-RIGHT` is polynomial-time. -/
theorem computableInPolyTime_hasNewQuery {Q : γ → α → List κ} {s : γ → ℕ}
    {pre : γ → List α} {z : γ → α}
    (hQ : ComputableInPolyTime (fun p : γ × α => Q p.1 p.2) (encPair encIn encA) (encList encK))
    (hs : ComputableInPolyTime s encIn encUnary)
    (hpre : ComputableInPolyTime pre encIn (encList encA))
    (hz : ComputableInPolyTime z encIn encA) :
    ComputableInPolyTime (fun x => hasNewQuery (Q x) (s x) (pre x) (z x)) encIn encBool := by
  unfold hasNewQuery
  fun_prop

/-- **`SEARCH-RIGHT` is polynomial-time**, for polynomial-time queries, bound and level. -/
theorem computableInPolyTime_searchRight {Q : γ → α → List κ} {s : γ → ℕ} {l : γ → List α}
    (hQ : ComputableInPolyTime (fun p : γ × α => Q p.1 p.2) (encPair encIn encA) (encList encK))
    (hs : ComputableInPolyTime s encIn encUnary)
    (hl : ComputableInPolyTime l encIn (encList encA)) :
    ComputableInPolyTime (fun x => searchRight (Q x) (s x) (l x)) encIn (encList encA) := by
  have htest : ComputableInPolyTime (fun p : γ × ((α × α) × ℕ) =>
      hasNewQuery (Q p.1) (s p.1) ((l p.1).take (p.2.2 + 1)) p.2.1.2)
      (encPair encIn (encPair (encPair encA encA) encUnary)) encBool :=
    computableInPolyTime_hasNewQuery
      (encIn := encPair encIn (encPair (encPair encA encA) encUnary)) (encA := encA)
      (Q := fun p : γ × ((α × α) × ℕ) => Q p.1) (s := fun p => s p.1)
      (pre := fun p => (l p.1).take (p.2.2 + 1)) (z := fun p => p.2.1.2)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold searchRight
  fun_prop

end PolyTime

/-- A level of the search is polynomial-time, uniformly in the formula, the bound, the nodes and the
occurrence. -/
private theorem computableInPolyTime_level {key : CNF ℕ → List (List Bool)}
    (hkey : ComputableInPolyTime key encCNF (encList encBits)) :
    ComputableInPolyTime
      (fun q : ((CNF ℕ × ℕ) × List (List (Literal ℕ))) × ℕ =>
        prune (fun a => key (atLeast a ++ q.1.1.1)) q.1.1.2 (Fortune.expand q.2 q.1.2))
      (encPair (encPair (encPair encCNF encUnary) encNodes) encNat) encNodes := by
  have hsearch := computableInPolyTime_searchRight
    (encIn := encPair (encPair (encPair encCNF encUnary) encNodes) encNat)
    (encA := encList (encPair encNat encBool)) (encK := encBits)
    (Q := fun (q : ((CNF ℕ × ℕ) × List (List (Literal ℕ))) × ℕ) a => key (atLeast a ++ q.1.1.1))
    (s := fun q => q.1.1.2) (l := fun q => (Fortune.expand q.2 q.1.2).reverse)
    (by fun_prop) (by fun_prop) (by unfold Fortune.expand; fun_prop)
  unfold prune
  fun_prop

/-- **The procedure is polynomial-time**, for polynomial-time queries `key` and a bound `s` computed
in unary. Each level keeps at most `s + 2` nodes, each fixing at most as many occurrences as `φ`
has. -/
theorem computableInPolyTime_accepts {key : CNF ℕ → List (List Bool)}
    (hkey : ComputableInPolyTime key encCNF (encList encBits)) {s : CNF ℕ → ℕ}
    (hs : ComputableInPolyTime s encCNF encUnary) :
    ComputableInPolyTime (fun φ => accepts key (s φ) φ) encCNF encBool :=
  Fortune.computableInPolyTime_acceptsWith (par := fun φ => (φ, s φ))
    (prune := fun p => prune (fun a => key (atLeast a ++ p.1)) p.2) (id'.prod hs)
    (computableInPolyTime_level hkey) (fun _ l _ ha => (prune_sublist l).subset ha)
    (hs.polyBounded.add (.const 2)) fun _ _ => length_prune_le _

/-! ### Sparse sets hard under conjunctive reductions -/

/-- **If `SAT` conjunctively reduces to a sparse problem, then `SAT` is in `P`**, decided by the
left-set search [Arvind, Köbler and Mundhenk, Theorem 3.4][ArvindKoblerMundhenk1992]. The queries of
a node are the encoded queries of the reduction on the formula saying that the assignment is at
least the node, and the bound counts the members of the sparse problem whose encodings are at most
as long as the longest query. -/
theorem SAT_mem_P {β : Type} {encB : β ↪ List Bool} {S : Set β} (hS : S ∈ SPARSE encB)
    (h : PolyTimeCTTReducible encCNF encB SAT S) : SAT ∈ P encCNF := by
  obtain ⟨r, q, hr, hq, hL⟩ := h
  have hencB : ComputableInPolyTime (fun b => encB b) encB encBits :=
    of_eq (encIn := encB) (encOut := encBits) (f := fun b => encB b) fun _ => rfl
  set key : CNF ℕ → List (List Bool) := fun ψ => (List.range (r ψ)).map fun i => encB (q (ψ, i))
  have hkey : ComputableInPolyTime key encCNF (encList encBits) := by fun_prop
  have hnode : ComputableInPolyTime (fun p : CNF ℕ × List (Literal ℕ) => key (atLeast p.2 ++ p.1))
      (encPair encCNF (encList (encPair encNat encBool))) (encList encBits) := by
    fun_prop
  obtain ⟨p, hp⟩ := hnode.polyBounded_length.exists_polynomial
  obtain ⟨C, D, hCD⟩ := exists_card_le_of_mem_SPARSE (image_mem_SPARSE_encBits_iff.mpr hS)
  /- Queries have length at most `p (2 L + 1 + L (4 L + 5))`, and at most `Q L` members of the
  sparse problem are that short. -/
  let Q : Polynomial ℕ := Polynomial.C C *
    (p.comp (2 * Polynomial.X + 1 + Polynomial.X * (4 * Polynomial.X + 5)) + 1) ^ D
  have hQ (L : ℕ) : Q.eval L = C * (p.eval (2 * L + 1 + L * (4 * L + 5)) + 1) ^ D := by
    simp [Q]
  refine ⟨fun φ => accepts key (Q.eval (encCNF φ).length) φ,
    computableInPolyTime_accepts hkey ((unary_eval Q).comp (encoding_length encCNF)),
    fun φ => (accepts_iff (K := encB '' S) (M := p.eval (2 * (encCNF φ).length + 1 +
      (encCNF φ).length * (4 * (encCNF φ).length + 5))) (fun ψ => ?_) (fun a ha hlen w hw => ?_)
      (fun T hT => ?_)).symm⟩
  · rw [hL ψ]
    simp only [key, List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, encB.injective.mem_set_image]
  · have hw' := SizedListEncoding.length_elem_le (encA := encBits) (encL := encList encBits) _ w hw
    refine hw'.trans ((hp (φ, a)).trans (Polynomial.eval_mono _ ?_))
    have hnode := Fortune.length_encNode_le ha hlen
    rw [length_encPair]
    dsimp only
    omega
  · rw [hQ]
    exact hCD _ T fun w hw => by simpa using hT w hw

/-- **Sparse sets are not hard for `NP` under conjunctive truth-table reductions unless `P = NP`:**
if `SAT` reduces to a sparse problem by a polynomial-time conjunctive truth-table reduction, then
`P = NP`, for every encoding of instances [Arvind, Köbler and Mundhenk, Theorem 3.4]
[ArvindKoblerMundhenk1992]. -/
theorem P_eq_NP_of_mem_SPARSE {β : Type} {encB : β ↪ List Bool} {S : Set β}
    (h : PolyTimeCTTReducible encCNF encB SAT S) (hS : S ∈ SPARSE encB)
    {α : Type} (enc : α ↪ List Bool) : P enc = NP enc :=
  CookLevin.SAT_npComplete.P_eq_NP_of_mem_P (SAT_mem_P hS h) enc

end Conjunctive

end Cslib.Complexity
