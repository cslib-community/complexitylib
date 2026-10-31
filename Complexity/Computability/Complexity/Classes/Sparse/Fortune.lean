/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP.SelfReduction
public import Complexity.Computability.Complexity.Classes.Sparse
public import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Foundations.Data.List.EraseDupsBy
import Cslib.Foundations.Data.Polynomial.Monotone
import Mathlib.Data.List.GetD

/-!
# Fortune's theorem

If a sparse problem is `coNP`-hard under polynomial-time many-one reductions, then `P = NP`
(`Cslib.Complexity.coNPHard.P_eq_NP_of_mem_SPARSE`) [Fortune1979]. The proof decides `SAT` from
a reduction `f` of `UNSAT` to a sparse problem `S` (`Cslib.Complexity.Fortune.SAT_mem_P`) by
searching the self-reduction tree of a formula `φ` level by level, pruning it on the fly
[Fluet, Hemaspaandra and Homan, Appendix B][FluetHemaspaandraHoman2026].

A node of the tree is a list `a` of literals fixing the values of the literal occurrences of `φ`
considered so far, and stands for the formula `SAT.units a ++ φ`. Its children fix the next
occurrence to `true` and to `false`, and the node is satisfiable exactly when one of its children
is. Each node gets the label `f (SAT.units a ++ φ)`, encoded as a word:

* Nodes with the same label are all satisfiable or all unsatisfiable, since `f` is a reduction, so
  only the first node with each label is kept (`List.eraseDupsBy`).
* The labels of unsatisfiable nodes are members of `S` of polynomially bounded length, so there
  are at most `c` of them for a polynomial `c` in the length of `φ`. If more than `c` nodes, all
  with distinct labels, remain, one of them is satisfiable. So keeping only the first `c + 1`
  of them (`Cslib.Complexity.Fortune.prune`) keeps a satisfiable node whenever there was one.

At the bottom of the tree every occurrence is fixed, and `SAT.verifier` decides whether a leaf
is satisfiable. The source stops and accepts as soon as more than `c` nodes remain; keeping `c + 1`
of them instead makes every level the same loop step, and the leaves still contain a satisfiable
node exactly when `φ` is satisfiable (`Cslib.Complexity.Fortune.accepts_iff`). Every level keeps
at most `c + 1` nodes of polynomial size, so the search runs in polynomial time
(`Cslib.Complexity.Fortune.computableInPolyTime_accepts`).

## Main definitions

* `Cslib.Complexity.Fortune.prune`: Fortune's pruning rule.
* `Cslib.Complexity.Fortune.expand`, `Cslib.Complexity.Fortune.searchWith`,
  `Cslib.Complexity.Fortune.acceptsWith`: the levels of the self-reduction tree, and its search
  and decision procedure with any pruning rule, shared with Mahaney's theorem and its one-query
  and conjunctive extensions.
* `Cslib.Complexity.Fortune.search`, `Cslib.Complexity.Fortune.accepts`: the pruned search and
  the decision procedure for `SAT`.

## Main results

* `Cslib.Complexity.Fortune.exists_child_mem_SAT`,
  `Cslib.Complexity.Fortune.verifier_units_append_iff`: a satisfiable node has a satisfiable
  child, and the verifier decides the leaves.
* `Cslib.Complexity.Fortune.mem_vars_and_length_le_of_map_fst_eq`: the nodes of a level fix
  variables of the formula.
* `Cslib.Complexity.Fortune.searchWith_induction`,
  `Cslib.Complexity.Fortune.acceptsWith_iff_of_searchWith`: induction along a pruned search, and
  its correctness from its leaves.
* `Cslib.Complexity.Fortune.acceptsWith_iff`,
  `Cslib.Complexity.Fortune.computableInPolyTime_acceptsWith`: a pruning rule that keeps a
  satisfiable node of every level decides `SAT`, in polynomial time when a level takes polynomial
  time and keeps polynomially many nodes.
* `Cslib.Complexity.Fortune.accepts_iff`: the procedure decides satisfiability when the labels
  come from a reduction of `UNSAT` and few labels of bounded length are in the target.
* `Cslib.Complexity.Fortune.computableInPolyTime_accepts`: the procedure is polynomial-time.
* `Cslib.Complexity.Fortune.SAT_mem_P`: if `UNSAT` reduces to a sparse problem, `SAT ∈ P`.
* `Cslib.Complexity.coNPHard.P_eq_NP_of_mem_SPARSE`: **Fortune's theorem**.

## References

* [S. Fortune, *A note on sparse complete sets*][Fortune1979]
* [K. Fluet, L. A. Hemaspaandra, C. M. Homan, *Fortune's Bounty: Taming Complexity by Trimming
  Trees*][FluetHemaspaandraHoman2026]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM SAT

namespace Fortune

/-! ### Pruning by labels -/

section Prune

variable {α κ : Type*} [DecidableEq κ] (label : α → κ)

/-- **Fortune's pruning rule:** keep the first entry with each label (`List.eraseDupsBy`), and at
most `c + 1` of these. -/
def prune (c : ℕ) (l : List α) : List α :=
  (l.eraseDupsBy fun a b => decide (label a = label b)).take (c + 1)

variable {label}

theorem prune_sublist (c : ℕ) (l : List α) : (prune label c l).Sublist l :=
  (List.take_sublist _ _).trans (List.eraseDupsBy_sublist l)

theorem length_prune_le (c : ℕ) (l : List α) : (prune label c l).length ≤ c + 1 :=
  List.length_take_le _ _

/-- The entries kept by `prune` have distinct labels. -/
theorem nodup_map_prune (c : ℕ) (l : List α) : ((prune label c l).map label).Nodup := by
  have hpair := List.pairwise_eraseDupsBy (r := fun a b => decide (label a = label b)) l
  have hnodup : ((l.eraseDupsBy fun a b => decide (label a = label b)).map label).Nodup :=
    List.pairwise_map.2 (hpair.imp fun h => by simpa [eq_comm] using h)
  rw [prune, List.map_take]
  exact hnodup.sublist (List.take_sublist _ _)

/-- Every label of `l` is the label of an entry kept by `prune`, unless `prune` keeps `c + 1`
entries. -/
theorem exists_mem_prune_or_length_eq {c : ℕ} {l : List α} {a : α} (ha : a ∈ l) :
    (∃ b ∈ prune label c l, label b = label a) ∨ (prune label c l).length = c + 1 := by
  obtain ⟨b, hb, hab⟩ := List.exists_mem_eraseDupsBy (r := fun a b => decide (label a = label b)) ha
  have hlabel : label b = label a := by
    rcases hab with rfl | hab
    · rfl
    · exact (of_decide_eq_true hab).symm
  by_cases hlen : (l.eraseDupsBy fun a b => decide (label a = label b)).length ≤ c + 1
  · exact .inl ⟨b, by rwa [prune, List.take_of_length_le hlen], hlabel⟩
  · exact .inr (List.length_take_of_le (by omega))

end Prune

/-! ### The self-reduction tree -/

/-- The children of the nodes `nodes` at the literal occurrence `v`: each node with `v` set to
`true`, then with `v` set to `false`. -/
def expand (v : ℕ) (nodes : List (List (Literal ℕ))) : List (List (Literal ℕ)) :=
  nodes.flatMap fun a => [a ++ [(v, true)], a ++ [(v, false)]]

/-- The search of the self-reduction tree of `φ` that prunes every level with the rule `prune`:
one level for each literal occurrence of `φ`. -/
def searchWith (prune : List (List (Literal ℕ)) → List (List (Literal ℕ))) (φ : CNF ℕ) :
    List (List (Literal ℕ)) :=
  φ.vars.foldl (fun nodes v => prune (expand v nodes)) [[]]

/-- Search the self-reduction tree of `φ` with the pruning rule `prune`, and accept when a leaf
is satisfied by the values it fixes. -/
def acceptsWith (prune : List (List (Literal ℕ)) → List (List (Literal ℕ))) (φ : CNF ℕ) : Bool :=
  (searchWith prune φ).any fun a => verifier (units a ++ φ, a.map Prod.snd)

/-- **Fortune's pruned search** of the self-reduction tree of `φ`, with the labels `label` and
the bound `c`: one level for each literal occurrence of `φ`, pruned by `prune`. -/
def search (label : List (Literal ℕ) → List Bool) (c : ℕ) (φ : CNF ℕ) :
    List (List (Literal ℕ)) :=
  searchWith (prune label c) φ

/-- **Fortune's decision procedure** with the reduction `key` and the bound `c`: search the
self-reduction tree of `φ`, labelling the node `a` with `key (units a ++ φ)`, and accept when a
leaf is satisfied by the values it fixes. -/
def accepts (key : CNF ℕ → List Bool) (c : ℕ) (φ : CNF ℕ) : Bool :=
  acceptsWith (prune (fun a => key (units a ++ φ)) c) φ

/-! ### Correctness -/

/-- A formula with unit clauses is satisfiable only if the formula is. -/
theorem mem_SAT_of_units_append {a : List (Literal ℕ)} {φ : CNF ℕ}
    (h : units a ++ φ ∈ SAT) : φ ∈ SAT := by
  obtain ⟨σ, hσ⟩ := h
  rw [CNF.eval_append, Bool.and_eq_true] at hσ
  exact ⟨σ, hσ.2⟩

/-- A satisfiable node has a satisfiable child: fix the next occurrence `v` to its value under a
satisfying assignment. -/
theorem exists_child_mem_SAT {a : List (Literal ℕ)} {φ : CNF ℕ} (v : ℕ)
    (h : units a ++ φ ∈ SAT) : ∃ b, units (a ++ [(v, b)]) ++ φ ∈ SAT := by
  obtain ⟨σ, hσ⟩ := h
  rw [CNF.eval_append, Bool.and_eq_true, eval_units] at hσ
  refine ⟨σ v, σ, ?_⟩
  rw [CNF.eval_append, Bool.and_eq_true, eval_units]
  refine ⟨fun l hl => ?_, hσ.2⟩
  rcases List.mem_append.1 hl with hl | hl
  · exact hσ.1 l hl
  · rw [List.mem_singleton.1 hl]

/-- The children of nodes fixing the occurrences `pre` fix `pre` and then `v`. -/
theorem map_fst_of_mem_expand {v : ℕ} {pre : List ℕ} {nodes : List (List (Literal ℕ))}
    (hfst : ∀ a ∈ nodes, a.map Prod.fst = pre) {b : List (Literal ℕ)} (hb : b ∈ expand v nodes) :
    b.map Prod.fst = pre ++ [v] := by
  simp only [expand, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hb
  obtain ⟨a, ha, rfl | rfl⟩ := hb <;> simp [hfst a ha]

/-- A node fixing a prefix of the occurrences of `φ` fixes only variables of `φ`, and at most as
many occurrences as `φ` has. -/
theorem mem_vars_and_length_le_of_map_fst_eq {φ : CNF ℕ} {pre : List ℕ}
    (hpre : pre.IsPrefix φ.vars) {a : List (Literal ℕ)} (ha : a.map Prod.fst = pre) :
    (∀ l ∈ a, l.1 ∈ φ.vars) ∧ a.length ≤ φ.vars.length :=
  ⟨fun l hl => hpre.subset (ha ▸ List.mem_map_of_mem hl), by simpa [← ha] using hpre.length_le⟩

/-- At a leaf, where every variable of `φ` is fixed, the verifier decides satisfiability with the
values fixed by the leaf as certificate. -/
theorem verifier_units_append_iff {a : List (Literal ℕ)} {φ : CNF ℕ}
    (ha : ∀ v ∈ φ.vars, v ∈ a.map Prod.fst) :
    verifier (units a ++ φ, a.map Prod.snd) = true ↔ units a ++ φ ∈ SAT := by
  refine ⟨fun h => ⟨_, h⟩, fun ⟨τ, hτ⟩ => ?_⟩
  have hτ' := hτ
  rw [CNF.eval_append, Bool.and_eq_true, eval_units] at hτ'
  rw [verifier, CNF.eval_congr fun v hv => ?_]
  · exact hτ
  · have hva : v ∈ a.map Prod.fst := by
      rw [CNF.vars, List.flatten_append, List.map_append, ← CNF.vars, ← CNF.vars,
        vars_units] at hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hv
      · exact ha v hv
    have hlt : (a.map Prod.fst).idxOf v < a.length := by
      simpa using List.idxOf_lt_length_iff.2 hva
    have hfst : (a[(a.map Prod.fst).idxOf v]).1 = v := by
      have := List.getElem_idxOf (List.idxOf_lt_length_iff.2 hva)
      simpa only [List.getElem_map] using this
    rw [assignment, CNF.vars, List.flatten_append, List.map_append, ← CNF.vars, ← CNF.vars,
      vars_units, List.idxOf_append_of_mem hva, List.getD_eq_getElem _ _ (by simpa using hlt),
      List.getElem_map, ← hτ'.1 _ (List.getElem_mem hlt), hfst]

/-! ### Pruned searches

Fortune's and Mahaney's procedures, and the one-query and conjunctive procedures, search the
self-reduction tree level by level, with different pruning rules. A property of the levels that
holds at the root and survives expanding and pruning a level holds at the leaves
(`Cslib.Complexity.Fortune.searchWith_induction`); the search accepts exactly the satisfiable
formulas when the leaves fix every occurrence and include a satisfiable one whenever there is one
(`Cslib.Complexity.Fortune.acceptsWith_iff_of_searchWith`). In particular, a rule that keeps only
nodes of the level it prunes, and keeps a satisfiable node of every level that has one, gives a
decision procedure (`Cslib.Complexity.Fortune.acceptsWith_iff`); it is polynomial-time when a level
is and the pruned levels are polynomially small
(`Cslib.Complexity.Fortune.computableInPolyTime_acceptsWith`). -/

section SearchWith

variable {prune : List (List (Literal ℕ)) → List (List (Literal ℕ))} {φ : CNF ℕ}

/-- **Induction along a pruned search.** A property `P pre nodes` of the levels, where the nodes
`nodes` follow the occurrences `pre`, that holds at the root and is preserved by expanding and
pruning a level holds for the leaves. -/
theorem searchWith_induction (P : List ℕ → List (List (Literal ℕ)) → Prop) (hroot : P [] [[]])
    (hstep : ∀ (pre : List ℕ) (v : ℕ) (nodes : List (List (Literal ℕ))),
      (pre ++ [v]).IsPrefix φ.vars → P pre nodes → P (pre ++ [v]) (prune (expand v nodes))) :
    P φ.vars (searchWith prune φ) := by
  suffices h : ∀ (l pre : List ℕ) (nodes : List (List (Literal ℕ))), (pre ++ l).IsPrefix φ.vars →
      P pre nodes → P (pre ++ l) (l.foldl (fun nodes v => prune (expand v nodes)) nodes) by
    simpa [searchWith] using h φ.vars [] [[]] (by simp) hroot
  intro l
  induction l with
  | nil =>
    intro pre nodes _ h
    simpa using h
  | cons v l ih =>
    intro pre nodes hpre h
    have hpre' : (pre ++ [v] ++ l).IsPrefix φ.vars := by simpa using hpre
    simpa using ih (pre ++ [v]) _ hpre'
      (hstep pre v nodes ((List.prefix_append _ l).trans hpre') h)

/-- **Correctness of a pruned search from its leaves.** If the leaves of the search fix every
occurrence of `φ`, and include a satisfiable one whenever `φ` is satisfiable, then the search
accepts exactly the satisfiable `φ`. -/
theorem acceptsWith_iff_of_searchWith
    (hfst : ∀ a ∈ searchWith prune φ, a.map Prod.fst = φ.vars)
    (hsat : φ ∈ SAT → ∃ a ∈ searchWith prune φ, units a ++ φ ∈ SAT) :
    acceptsWith prune φ = true ↔ φ ∈ SAT := by
  rw [acceptsWith, List.any_eq_true]
  constructor
  · rintro ⟨a, -, ha⟩
    exact mem_SAT_of_units_append ⟨_, ha⟩
  · intro hφ
    obtain ⟨a, ha, hgood⟩ := hsat hφ
    refine ⟨a, ha, (verifier_units_append_iff fun v hv => ?_).2 hgood⟩
    rw [hfst a ha]
    exact hv

/-- **Correctness of a pruned search.** If the rule `prune` keeps only nodes of the level it
prunes, and keeps a satisfiable node of every level of the tree of `φ` that has one, then the
search accepts exactly the satisfiable `φ`. -/
theorem acceptsWith_iff (hsub : ∀ l, ∀ a ∈ prune l, a ∈ l)
    (hkeep : ∀ (pre : List ℕ) (l : List (List (Literal ℕ))), pre.IsPrefix φ.vars →
      (∀ a ∈ l, a.map Prod.fst = pre) → (∃ a ∈ l, units a ++ φ ∈ SAT) →
        ∃ a ∈ prune l, units a ++ φ ∈ SAT) :
    acceptsWith prune φ = true ↔ φ ∈ SAT := by
  obtain ⟨hfst, hsat⟩ := searchWith_induction (prune := prune) (φ := φ)
    (fun pre nodes => (∀ a ∈ nodes, a.map Prod.fst = pre) ∧
      (φ ∈ SAT → ∃ a ∈ nodes, units a ++ φ ∈ SAT))
    ⟨by simp, fun h => ⟨[], by simp, by simpa [units] using h⟩⟩
    fun pre v nodes hpre ⟨hfst, hsat⟩ => by
      have hexp : ∀ b ∈ expand v nodes, b.map Prod.fst = pre ++ [v] :=
        fun b hb => map_fst_of_mem_expand hfst hb
      refine ⟨fun b hb => hexp b (hsub _ b hb), fun hφ => ?_⟩
      obtain ⟨a, ha, hasat⟩ := hsat hφ
      obtain ⟨bv, hb⟩ := exists_child_mem_SAT v hasat
      refine hkeep _ _ hpre hexp ⟨a ++ [(v, bv)], ?_, hb⟩
      simp only [expand, List.mem_flatMap]
      exact ⟨a, ha, by cases bv <;> simp⟩
  exact acceptsWith_iff_of_searchWith hfst hsat

end SearchWith

/-! ### Correctness of Fortune's procedure -/

section Search

variable {key : CNF ℕ → List Bool} {K : Set (List Bool)} {c M : ℕ} {φ : CNF ℕ}

/-- Pruning a level keeps a satisfiable node, if there is one: either one with the label of a
satisfiable node or, among `c + 1` distinct labels, one outside `K`. -/
private theorem exists_mem_prune (hkey : ∀ ψ, ψ ∉ SAT ↔ key ψ ∈ K)
    (hM : ∀ a : List (Literal ℕ), (∀ l ∈ a, l.1 ∈ φ.vars) → a.length ≤ φ.vars.length →
      (key (units a ++ φ)).length ≤ M)
    (hc : ∀ s : Finset (List Bool), (∀ w ∈ s, w ∈ K ∧ w.length ≤ M) → s.card ≤ c)
    {pre : List ℕ} (hpre : pre.IsPrefix φ.vars) {l : List (List (Literal ℕ))}
    (hfst : ∀ a ∈ l, a.map Prod.fst = pre) (h : ∃ a ∈ l, units a ++ φ ∈ SAT) :
    ∃ a ∈ prune (fun a => key (units a ++ φ)) c l, units a ++ φ ∈ SAT := by
  obtain ⟨b₀, hb₀, hb₀sat⟩ := h
  rcases exists_mem_prune_or_length_eq (label := fun a => key (units a ++ φ)) (c := c) hb₀ with
    ⟨b, hbp, hlab⟩ | hlen
  · refine ⟨b, hbp, ?_⟩
    by_contra hbad
    exact (hkey _).2 (hlab ▸ (hkey _).1 hbad) hb₀sat
  · by_contra hnone
    push Not at hnone
    set kept := prune (fun a => key (units a ++ φ)) c l
    have hcard : (kept.map fun a => key (units a ++ φ)).toFinset.card = c + 1 := by
      rw [List.toFinset_card_of_nodup (nodup_map_prune _ _), List.length_map, hlen]
    have hle := hc (kept.map fun a => key (units a ++ φ)).toFinset fun w hw => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hw)
      have hnode :=
        mem_vars_and_length_le_of_map_fst_eq hpre (hfst b ((prune_sublist c l).subset hb))
      exact ⟨(hkey _).1 (hnone b hb), hM b hnode.1 hnode.2⟩
    omega

/-- **Correctness of Fortune's procedure.** If `key` reduces `UNSAT` to `K`, the labels of the
nodes of the tree of `φ` have length at most `M`, and every finite set of members of `K` of length
at most `M` has at most `c` elements, then the procedure accepts exactly the satisfiable `φ`. -/
theorem accepts_iff (hkey : ∀ ψ, ψ ∉ SAT ↔ key ψ ∈ K)
    (hM : ∀ a : List (Literal ℕ), (∀ l ∈ a, l.1 ∈ φ.vars) → a.length ≤ φ.vars.length →
      (key (units a ++ φ)).length ≤ M)
    (hc : ∀ s : Finset (List Bool), (∀ w ∈ s, w ∈ K ∧ w.length ≤ M) → s.card ≤ c) :
    accepts key c φ = true ↔ φ ∈ SAT :=
  acceptsWith_iff (fun l _ ha => (prune_sublist c l).subset ha)
    fun _ _ hpre hfst h => exists_mem_prune hkey hM hc hpre hfst h

end Search

/-! ### Polynomial time -/

open ComputableInPolyTime

/-- The encoding of the list of nodes at a level of the tree. -/
local notation "encNodes" => encList (encList (encPair encNat encBool))

/-- One level of the search is polynomial-time, uniformly in the formula, the bound, the nodes
and the occurrence. -/
private theorem computableInPolyTime_step {key : CNF ℕ → List Bool}
    (hkey : ComputableInPolyTime key encCNF encBits) :
    ComputableInPolyTime
      (fun p : ((CNF ℕ × ℕ) × List (List (Literal ℕ))) × ℕ =>
        prune (fun a => key (units a ++ p.1.1.1)) p.1.1.2 (expand p.2 p.1.2))
      (encPair (encPair (encPair encCNF encUnary) encNodes) encNat) encNodes := by
  unfold prune expand units
  fun_prop

/-- A node fixing at most as many occurrences as `φ` has, all of variables of `φ`, has an encoding
of length at most `L (4 L + 5)`, where `L` is the length of the encoding of `φ`. -/
theorem length_encNode_le {φ : CNF ℕ} {a : List (Literal ℕ)} (ha : ∀ l ∈ a, l.1 ∈ φ.vars)
    (hlen : a.length ≤ φ.vars.length) :
    (encList (encPair encNat encBool) a).length ≤
      (encCNF φ).length * (4 * (encCNF φ).length + 5) := by
  have hlit : ∀ l ∈ a, (encPair encNat encBool l).length ≤ 2 * (encCNF φ).length + 2 := by
    intro l hl
    have := length_encNat_le_of_mem_vars (ha l hl)
    rw [length_encPair, encBool_apply, List.length_singleton]
    omega
  have hlen' : a.length ≤ (encCNF φ).length := hlen.trans (length_vars_le φ)
  calc (encList (encPair encNat encBool) a).length
      ≤ a.length * (2 * (2 * (encCNF φ).length + 2) + 1) := length_encList_le _ _ hlit
    _ ≤ (encCNF φ).length * (4 * (encCNF φ).length + 5) := by
      rw [show 2 * (2 * (encCNF φ).length + 2) + 1 = 4 * (encCNF φ).length + 5 by ring]
      exact Nat.mul_le_mul_right _ hlen'

/-- Checking a leaf with the verifier is polynomial-time. -/
theorem computableInPolyTime_verifier_units_append :
    ComputableInPolyTime
      (fun p : CNF ℕ × List (Literal ℕ) => verifier (units p.2 ++ p.1, p.2.map Prod.snd))
      (encPair encCNF (encList (encPair encNat encBool))) encBool := by
  have hformula : ComputableInPolyTime (fun p : CNF ℕ × List (Literal ℕ) => units p.2 ++ p.1)
      (encPair encCNF (encList (encPair encNat encBool))) encCNF := by
    unfold units encCNF
    fun_prop
  exact computableInPolyTime_verifier.comp
    (hformula.prod (listToBits.comp ((map (snd encNat encBool)).comp (snd _ _))))

/-- **A pruned search is polynomial-time** when one level of it is, uniformly in a parameter
`par φ` computed from the formula, and every pruned level has at most `width φ` nodes for a
polynomially bounded `width`. -/
theorem computableInPolyTime_acceptsWith {π : Type} {encP : π ↪ List Bool} {par : CNF ℕ → π}
    (hpar : ComputableInPolyTime par encCNF encP)
    {prune : π → List (List (Literal ℕ)) → List (List (Literal ℕ))}
    (hprune : ComputableInPolyTime
      (fun q : (π × List (List (Literal ℕ))) × ℕ => prune q.1.1 (expand q.2 q.1.2))
      (encPair (encPair encP encNodes) encNat) encNodes)
    (hsub : ∀ p l, ∀ a ∈ prune p l, a ∈ l) {width : CNF ℕ → ℕ}
    (hwidth : PolyBounded (fun φ => (encCNF φ).length) width)
    (hlen : ∀ φ l, (prune (par φ) l).length ≤ width φ) :
    ComputableInPolyTime (fun φ => acceptsWith (prune (par φ)) φ) encCNF encBool := by
  have hsearch : ComputableInPolyTime (fun φ => searchWith (prune (par φ)) φ) encCNF encNodes :=
    (foldlWith_spec (par := par) (init := fun _ => [[]])
      (step := fun p nodes v => prune p (expand v nodes))
      hpar computableInPolyTime_vars (const _) hprune
      (fun φ pre nodes => pre.IsPrefix φ.vars ∧ (∀ a ∈ nodes, a.map Prod.fst = pre) ∧
        nodes.length ≤ width φ + 1)
      (fun φ => ⟨List.nil_prefix, by simp, by simp⟩)
      (fun φ pre nodes v hpre h => ⟨hpre, fun b hb => map_fst_of_mem_expand h.2.1 (hsub _ _ b hb),
        (hlen φ _).trans (Nat.le_succ _)⟩)
      (size := fun φ => (width φ + 1) *
        (2 * ((encCNF φ).length * (4 * (encCNF φ).length + 5)) + 1))
      ((hwidth.add (.const 1)).mul (((PolyBounded.const 2).mul (PolyBounded.self.mul
        (((PolyBounded.const 4).mul .self).add (.const 5)))).add (.const 1)))
      (fun φ pre nodes _ h => (length_encList_le _ _
        fun a ha => (mem_vars_and_length_le_of_map_fst_eq h.1 (h.2.1 a ha)).elim
          length_encNode_le).trans (Nat.mul_le_mul_right _ h.2.2))).1
  exact anyWithInput hsearch computableInPolyTime_verifier_units_append

/-- **Fortune's procedure is polynomial-time**, for a polynomial-time `key` and a bound `c`
computed in unary. Each level keeps at most `c + 1` nodes, each fixing at most as many
occurrences as `φ` has. -/
theorem computableInPolyTime_accepts {key : CNF ℕ → List Bool}
    (hkey : ComputableInPolyTime key encCNF encBits) {c : CNF ℕ → ℕ}
    (hc : ComputableInPolyTime c encCNF encUnary) :
    ComputableInPolyTime (fun φ => accepts key (c φ) φ) encCNF encBool :=
  computableInPolyTime_acceptsWith (par := fun φ => (φ, c φ))
    (prune := fun p => prune (fun a => key (units a ++ p.1)) p.2) (id'.prod hc)
    (computableInPolyTime_step hkey) (fun _ l _ ha => (prune_sublist _ l).subset ha)
    (hc.polyBounded.add (.const 1)) fun _ _ => length_prune_le _ _

/-! ### Fortune's theorem -/

/-- **If `UNSAT` reduces to a sparse problem, then `SAT` is in `P`**, decided by Fortune's
procedure [Fluet, Hemaspaandra and Homan, Appendix B][FluetHemaspaandraHoman2026]. The labels
are the encoded images of the formulas of the nodes under the reduction, and the bound counts the
members of the sparse problem whose encodings are at most as long as the longest label. -/
theorem SAT_mem_P {β : Type*} {encB : β ↪ List Bool} {S : Set β} (hS : S ∈ SPARSE encB)
    (h : PolyTimeReducible encCNF encB UNSAT S) : SAT ∈ P encCNF := by
  obtain ⟨f, hf, hfS⟩ := h
  have hkey : ComputableInPolyTime (fun ψ => encB (f ψ)) encCNF encBits :=
    (of_eq (encIn := encB) (encOut := encBits) (f := fun b => encB b) fun _ => rfl).comp hf
  obtain ⟨p, hp⟩ := hkey.polyBounded_length.exists_polynomial
  obtain ⟨C, D, hCD⟩ := exists_card_le_of_mem_SPARSE (image_mem_SPARSE_encBits_iff.mpr hS)
  /- Labels have length at most `p (L + L (8 L + 11))`, and at most `q L` members of the
  sparse problem are that short. -/
  let q : Polynomial ℕ := Polynomial.C C *
    (p.comp (Polynomial.X + Polynomial.X * (8 * Polynomial.X + 11)) + 1) ^ D
  have hq (L : ℕ) : q.eval L = C * (p.eval (L + L * (8 * L + 11)) + 1) ^ D := by
    simp [q]
  refine ⟨fun φ => accepts (fun ψ => encB (f ψ)) (q.eval (encCNF φ).length) φ,
    computableInPolyTime_accepts hkey ((unary_eval q).comp (encoding_length encCNF)),
    fun φ => (accepts_iff (K := encB '' S) (M := p.eval ((encCNF φ).length +
      (encCNF φ).length * (8 * (encCNF φ).length + 11))) (fun ψ => ?_) (fun a ha hlen => ?_)
      (fun s hs => ?_)).symm⟩
  · rw [encB.injective.mem_set_image]
    exact hfS ψ
  · refine (hp _).trans (Polynomial.eval_mono _ ?_)
    have hunits := length_encCNF_units_le ha
    have hvars := length_vars_le φ
    rw [length_encCNF_append]
    nlinarith
  · rw [hq]
    exact hCD _ s fun w hw => by simpa using hs w hw

end Fortune

/-- **Fortune's theorem:** if a sparse problem is `coNP`-hard under polynomial-time many-one
reductions, then `P = NP`, for every encoding of instances [Fortune1979]. -/
theorem coNPHard.P_eq_NP_of_mem_SPARSE {β : Type*} {encB : β ↪ List Bool} {S : Set β}
    (hard : coNPHard encB S) (hS : S ∈ SPARSE encB) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  CookLevin.SAT_npComplete.P_eq_NP_of_mem_P
    (Fortune.SAT_mem_P hS (hard encCNF UNSAT UNSAT_mem_coNP)) enc

end Cslib.Complexity
