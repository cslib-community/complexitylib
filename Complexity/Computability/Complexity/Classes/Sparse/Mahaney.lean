/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Sparse.Fortune
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Foundations.Data.List.EraseDupsBy
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Mahaney's theorem

If a sparse problem is `NP`-hard under polynomial-time many-one reductions, then `P = NP`
(`Cslib.Complexity.NPHard.P_eq_NP_of_mem_SPARSE`) [Mahaney1982]. The proof is Agrawal's, as
expounded by Grochow [Grochow, Theorem 2.1][Grochow2016]. It decides `SAT` from a reduction `f` of
`SAT` to a sparse problem (`Cslib.Complexity.Mahaney.SAT_mem_P`) by searching the self-reduction
tree of a formula `φ` level by level, as in Fortune's theorem
(`Complexity/Computability/Complexity/Classes/Sparse/Fortune.lean`), but pruning each level
differently, since the labels of satisfiable rather than unsatisfiable formulas now lie in the
sparse problem.

A level is pruned in stages (`Cslib.Complexity.Mahaney.stage`). A stage takes the first node `a`
and labels every other node `b` with `f (a ∨ b)`, where `a ∨ b` is the formula `Mahaney.disj φ a b`,
satisfiable exactly when `a` or `b` is (`Cslib.Complexity.Mahaney.disj_mem_SAT_iff`).

* Of the other nodes with the same label, only the first is kept (`List.eraseDupsBy`). If `a` is
  satisfiable it is kept anyway; otherwise nodes with the same label are all satisfiable or all
  unsatisfiable.
* If more than `t` other nodes remain, their labels are distinct, so one of them lies outside
  the sparse problem, where `t` bounds its members of the length of the labels. Then `a ∨ b` is
  unsatisfiable for that node `b`, so `a` is unsatisfiable and is dropped.

A stage removes a node or leaves at most `t + 1` of them, so as many stages as there are nodes
leave at most `t + 1` nodes, one of them satisfiable if one was before
(`Cslib.Complexity.Mahaney.accepts_iff`). The source runs the two cases as separate stages,
removing one duplicate at a time; a stage here removes every duplicate at once. Every level keeps
at most `t + 1` nodes of polynomial size, so the search runs in polynomial time
(`Cslib.Complexity.Mahaney.computableInPolyTime_accepts`).

## Main definitions

* `Cslib.Complexity.Mahaney.disj`: the disjunction of two nodes of the self-reduction tree.
* `Cslib.Complexity.Mahaney.stage`, `Cslib.Complexity.Mahaney.prune`: Agrawal's pruning rule.
* `Cslib.Complexity.Mahaney.search`, `Cslib.Complexity.Mahaney.accepts`: the pruned search and the
  decision procedure for `SAT`.

## Main results

* `Cslib.Complexity.Mahaney.disj_mem_SAT_iff`: the disjunction of two nodes is satisfiable
  exactly when one of them is.
* `Cslib.Complexity.Mahaney.length_prune_le`: a pruned level has at most `t + 1` nodes.
* `Cslib.Complexity.Mahaney.accepts_iff`: the procedure decides satisfiability when the labels
  come from a reduction of `SAT` and few labels of bounded length are in the target.
* `Cslib.Complexity.Mahaney.computableInPolyTime_accepts`: the procedure is polynomial-time.
* `Cslib.Complexity.Mahaney.SAT_mem_P`: if `SAT` reduces to a sparse problem, `SAT ∈ P`.
* `Cslib.Complexity.NPHard.P_eq_NP_of_mem_SPARSE`: **Mahaney's theorem**.

## References

* [S. R. Mahaney, *Sparse complete sets for NP: Solution of a conjecture of Berman and
  Hartmanis*][Mahaney1982]
* [J. A. Grochow, *NP-hard sets are not sparse unless P = NP: An exposition of a simple proof of
  Mahaney's Theorem, with applications*][Grochow2016]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM SAT

namespace Mahaney

/-! ### The disjunction of two nodes -/

/-- The disjunction of the nodes `a` and `b` of the tree of `φ`: `φ` together with the clause
`l ∨ m` for each literal `l` of `a` and `m` of `b`. -/
def disj (φ : CNF ℕ) (a b : List (Literal ℕ)) : CNF ℕ :=
  (a.flatMap fun l => b.map fun m => [l, m]) ++ φ

private theorem eval_cross (σ : ℕ → Bool) (a b : List (Literal ℕ)) :
    CNF.eval σ (a.flatMap fun l => b.map fun m => [l, m]) = true ↔
      ∀ l ∈ a, ∀ m ∈ b, σ l.1 = l.2 ∨ σ m.1 = m.2 := by
  simp only [CNF.eval_eq_true_iff, List.mem_flatMap, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h l hl m hm
    have := h _ l hl m hm rfl
    simpa [Clause.eval_cons, Literal.eval_eq_true_iff] using this
  · rintro h c l hl m hm rfl
    simpa [Clause.eval_cons, Literal.eval_eq_true_iff] using h l hl m hm

/-- **The disjunction of two nodes is satisfiable exactly when one of them is.** -/
theorem disj_mem_SAT_iff {φ : CNF ℕ} {a b : List (Literal ℕ)} :
    disj φ a b ∈ SAT ↔ units a ++ φ ∈ SAT ∨ units b ++ φ ∈ SAT := by
  constructor
  · rintro ⟨σ, hσ⟩
    rw [disj, CNF.eval_append, Bool.and_eq_true, eval_cross] at hσ
    by_cases ha : ∀ l ∈ a, σ l.1 = l.2
    · exact .inl ⟨σ, by rw [CNF.eval_append, Bool.and_eq_true, eval_units]; exact ⟨ha, hσ.2⟩⟩
    · push Not at ha
      obtain ⟨l, hl, hne⟩ := ha
      refine .inr ⟨σ, ?_⟩
      rw [CNF.eval_append, Bool.and_eq_true, eval_units]
      exact ⟨fun m hm => (hσ.1 l hl m hm).resolve_left hne, hσ.2⟩
  · rintro (⟨σ, hσ⟩ | ⟨σ, hσ⟩) <;>
      rw [CNF.eval_append, Bool.and_eq_true, eval_units] at hσ <;>
      refine ⟨σ, ?_⟩ <;>
      rw [disj, CNF.eval_append, Bool.and_eq_true, eval_cross]
    · exact ⟨fun l hl m _ => .inl (hσ.1 l hl), hσ.2⟩
    · exact ⟨fun l _ m hm => .inr (hσ.1 m hm), hσ.2⟩

/-! ### Agrawal's pruning rule -/

section Prune

variable {α κ : Type*} [DecidableEq κ] (label : α → α → κ) (t : ℕ)

/-- **One stage of Agrawal's pruning rule** with the labels `label a b` of pairs of nodes and the
bound `t`: of the nodes after the first node `a`, keep the first with each label `label a b`, and
drop `a` if more than `t` of them remain. -/
def stage : List α → List α
  | [] => []
  | a :: rest =>
    if t < (rest.eraseDupsBy fun b b' => decide (label a b = label a b')).length then
      rest.eraseDupsBy fun b b' => decide (label a b = label a b')
    else a :: rest.eraseDupsBy fun b b' => decide (label a b = label a b')

/-- **Agrawal's pruning rule:** as many stages as there are nodes. -/
def prune (l : List α) : List α := (stage label t)^[l.length] l

variable {label t}

theorem stage_sublist : ∀ l : List α, (stage label t l).Sublist l
  | [] => List.Sublist.slnil
  | a :: rest => by
    have h := List.eraseDupsBy_sublist (r := fun b b' => decide (label a b = label a b')) rest
    rw [stage]
    split
    · exact h.cons a
    · exact h.cons_cons a

theorem length_stage_le : ∀ l : List α, (stage label t l).length ≤ max (t + 1) (l.length - 1)
  | [] => Nat.zero_le _
  | a :: rest => by
    have h := (List.eraseDupsBy_sublist
      (r := fun b b' => decide (label a b = label a b')) rest).length_le
    rw [stage]
    split
    · simp only [List.length_cons, Nat.add_sub_cancel]
      omega
    · rw [List.length_cons]
      omega

theorem iterate_stage_sublist (i : ℕ) (l : List α) : ((stage label t)^[i] l).Sublist l := by
  induction i with
  | zero => exact List.Sublist.refl l
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (stage_sublist _).trans ih

theorem length_iterate_stage_le (i : ℕ) (l : List α) :
    ((stage label t)^[i] l).length ≤ max (t + 1) (l.length - i) := by
  induction i with
  | zero => exact le_max_right _ _
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    refine (length_stage_le _).trans ?_
    omega

theorem prune_sublist (l : List α) : (prune label t l).Sublist l := iterate_stage_sublist _ l

/-- A pruned level has at most `t + 1` nodes. -/
theorem length_prune_le (l : List α) : (prune label t l).length ≤ t + 1 := by
  have := length_iterate_stage_le (label := label) (t := t) l.length l
  rw [Nat.sub_self] at this
  exact this.trans (by omega)

end Prune

/-! ### The search -/

/-- **Agrawal's pruned search** of the self-reduction tree of `φ`, with the labels `label` and the
bound `t`: one level for each literal occurrence of `φ`, pruned by `prune`. -/
def search (label : List (Literal ℕ) → List (Literal ℕ) → List Bool) (t : ℕ) (φ : CNF ℕ) :
    List (List (Literal ℕ)) :=
  Fortune.searchWith (prune label t) φ

/-- **The decision procedure for Mahaney's theorem** with the reduction `key` and the bound `t`:
search the self-reduction tree of `φ`, labelling the pair of nodes `a`, `b` with
`key (disj φ a b)`, and accept when a leaf is satisfied by the values it fixes. -/
def accepts (key : CNF ℕ → List Bool) (t : ℕ) (φ : CNF ℕ) : Bool :=
  Fortune.acceptsWith (prune (fun a b => key (disj φ a b)) t) φ

/-! ### Correctness -/

section Correctness

variable {key : CNF ℕ → List Bool} {K : Set (List Bool)} {t M : ℕ} {φ : CNF ℕ}

/-- A stage keeps a satisfiable node, if there is one: when the first node is dropped, more than
`t` distinct labels remain, so the first node is unsatisfiable. -/
private theorem exists_mem_stage (hkey : ∀ ψ, ψ ∈ SAT ↔ key ψ ∈ K)
    (hc : ∀ s : Finset (List Bool), (∀ w ∈ s, w ∈ K ∧ w.length ≤ M) → s.card ≤ t)
    {l : List (List (Literal ℕ))} (hM : ∀ a ∈ l, ∀ b ∈ l, (key (disj φ a b)).length ≤ M)
    (h : ∃ a ∈ l, units a ++ φ ∈ SAT) :
    ∃ a ∈ stage (fun a b => key (disj φ a b)) t l, units a ++ φ ∈ SAT := by
  obtain ⟨x, hx, hxsat⟩ := h
  match l, hx, hM with
  | a :: rest, hx, hM =>
    rw [stage]
    set kept := rest.eraseDupsBy fun b b' => decide (key (disj φ a b) = key (disj φ a b'))
    /- A satisfiable node after `a`, when `a` is unsatisfiable, has a satisfiable representative
    among the kept nodes. -/
    have hrep : ∀ b ∈ rest, units b ++ φ ∈ SAT → units a ++ φ ∉ SAT →
        ∃ b' ∈ kept, units b' ++ φ ∈ SAT := by
      intro b hb hbsat hanot
      obtain ⟨b', hb', hbb'⟩ := List.exists_mem_eraseDupsBy
        (r := fun b b' => decide (key (disj φ a b) = key (disj φ a b'))) hb
      refine ⟨b', hb', ?_⟩
      rcases hbb' with rfl | hlab
      · exact hbsat
      · have hdisj : disj φ a b' ∈ SAT := by
          rw [hkey, ← of_decide_eq_true hlab, ← hkey]
          exact disj_mem_SAT_iff.2 (.inr hbsat)
        exact (disj_mem_SAT_iff.1 hdisj).resolve_left hanot
    have hcases : units a ++ φ ∈ SAT ∨ ∃ b' ∈ kept, units b' ++ φ ∈ SAT := by
      by_cases hasat : units a ++ φ ∈ SAT
      · exact .inl hasat
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd hxsat hasat
        · exact .inr (hrep x hx hxsat hasat)
    split
    · rename_i hlen
      by_cases hasat : units a ++ φ ∈ SAT
      · /- If `a` were satisfiable, every kept label would lie in `K`. -/
        exfalso
        have hnodup : (kept.map fun b => key (disj φ a b)).Nodup :=
          List.pairwise_map.2 ((List.pairwise_eraseDupsBy _).imp fun h => by
            simpa [eq_comm] using h)
        have hsub := (List.eraseDupsBy_sublist
          (r := fun b b' => decide (key (disj φ a b) = key (disj φ a b'))) rest).subset
        have hle := hc (kept.map fun b => key (disj φ a b)).toFinset fun w hw => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hw)
          exact ⟨(hkey _).1 (disj_mem_SAT_iff.2 (.inl hasat)),
            hM a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ (hsub hb))⟩
        rw [List.toFinset_card_of_nodup hnodup, List.length_map] at hle
        omega
      · exact (hcases.resolve_left hasat)
    · rcases hcases with hasat | ⟨b', hb', hb'sat⟩
      · exact ⟨a, List.mem_cons_self .., hasat⟩
      · exact ⟨b', List.mem_cons_of_mem _ hb', hb'sat⟩

/-- Pruning keeps a satisfiable node, if there is one. -/
private theorem exists_mem_prune (hkey : ∀ ψ, ψ ∈ SAT ↔ key ψ ∈ K)
    (hc : ∀ s : Finset (List Bool), (∀ w ∈ s, w ∈ K ∧ w.length ≤ M) → s.card ≤ t)
    {l : List (List (Literal ℕ))} (hM : ∀ a ∈ l, ∀ b ∈ l, (key (disj φ a b)).length ≤ M)
    (h : ∃ a ∈ l, units a ++ φ ∈ SAT) :
    ∃ a ∈ prune (fun a b => key (disj φ a b)) t l, units a ++ φ ∈ SAT := by
  suffices ∀ i, ∃ a ∈ (stage (fun a b => key (disj φ a b)) t)^[i] l, units a ++ φ ∈ SAT from
    this _
  intro i
  induction i with
  | zero => exact h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have hsub := (iterate_stage_sublist (label := fun a b => key (disj φ a b)) (t := t) i l).subset
    exact exists_mem_stage hkey hc (fun a ha b hb => hM a (hsub ha) b (hsub hb)) ih

/-- **Correctness of the procedure.** If `key` reduces `SAT` to `K`, the labels of the pairs of
nodes of the tree of `φ` have length at most `M`, and every finite set of members of `K` of length
at most `M` has at most `t` elements, then the procedure accepts exactly the satisfiable `φ`. -/
theorem accepts_iff (hkey : ∀ ψ, ψ ∈ SAT ↔ key ψ ∈ K)
    (hM : ∀ a b : List (Literal ℕ), (∀ l ∈ a, l.1 ∈ φ.vars) → (∀ l ∈ b, l.1 ∈ φ.vars) →
      a.length ≤ φ.vars.length → b.length ≤ φ.vars.length → (key (disj φ a b)).length ≤ M)
    (hc : ∀ s : Finset (List Bool), (∀ w ∈ s, w ∈ K ∧ w.length ≤ M) → s.card ≤ t) :
    accepts key t φ = true ↔ φ ∈ SAT := by
  refine Fortune.acceptsWith_iff (fun l _ ha => (prune_sublist l).subset ha)
    fun pre l hpre hfst h => exists_mem_prune hkey hc (fun a ha b hb => ?_) h
  have ha' := Fortune.mem_vars_and_length_le_of_map_fst_eq hpre (hfst a ha)
  have hb' := Fortune.mem_vars_and_length_le_of_map_fst_eq hpre (hfst b hb)
  exact hM a b ha'.1 hb'.1 ha'.2 hb'.2

end Correctness

/-! ### Polynomial time -/

open ComputableInPolyTime

/-- The encoding of the list of nodes at a level of the tree. -/
local notation "encNodes" => encList (encList (encPair encNat encBool))

/-- A stage in terms of list operations. -/
private theorem stage_eq (label : List (Literal ℕ) → List (Literal ℕ) → List Bool) (t : ℕ)
    (l : List (List (Literal ℕ))) :
    stage label t l = if l.isEmpty then [] else
      if t < (l.tail.eraseDupsBy fun b b' =>
          decide (label (l.headD []) b = label (l.headD []) b')).length then
        l.tail.eraseDupsBy fun b b' => decide (label (l.headD []) b = label (l.headD []) b')
      else l.headD [] ::
        l.tail.eraseDupsBy fun b b' => decide (label (l.headD []) b = label (l.headD []) b') := by
  cases l <;> rfl

/-- A stage is polynomial-time, uniformly in the formula, the bound and the nodes. -/
private theorem computableInPolyTime_stage {key : CNF ℕ → List Bool}
    (hkey : ComputableInPolyTime key encCNF encBits) :
    ComputableInPolyTime
      (fun r : (CNF ℕ × ℕ) × List (List (Literal ℕ)) =>
        stage (fun a b => key (disj r.1.1 a b)) r.1.2 r.2)
      (encPair (encPair encCNF encUnary) encNodes) encNodes := by
  simp only [stage_eq]
  unfold disj
  fun_prop

/-- A level of the search is polynomial-time, uniformly in the formula, the bound, the nodes and
the occurrence: every stage keeps a sublist of the expanded level. -/
private theorem computableInPolyTime_level {key : CNF ℕ → List Bool}
    (hkey : ComputableInPolyTime key encCNF encBits) :
    ComputableInPolyTime
      (fun q : ((CNF ℕ × ℕ) × List (List (Literal ℕ))) × ℕ =>
        prune (fun a b => key (disj q.1.1.1 a b)) q.1.1.2 (Fortune.expand q.2 q.1.2))
      (encPair (encPair (encPair encCNF encUnary) encNodes) encNat) encNodes := by
  have hexpand : ComputableInPolyTime
      (fun q : ((CNF ℕ × ℕ) × List (List (Literal ℕ))) × ℕ => Fortune.expand q.2 q.1.2)
      (encPair (encPair (encPair encCNF encUnary) encNodes) encNat) encNodes := by
    unfold Fortune.expand
    fun_prop
  have hcount : ComputableInPolyTime
      (fun q : ((CNF ℕ × ℕ) × List (List (Literal ℕ))) × ℕ => (Fortune.expand q.2 q.1.2).length)
      (encPair (encPair (encPair encCNF encUnary) encNodes) encNat) encUnary := by
    fun_prop
  unfold prune
  exact iterateWith (par := fun q => q.1.1) (init := fun q => Fortune.expand q.2 q.1.2)
    (step := fun r l => stage (fun a b => key (disj r.1 a b)) r.2 l)
    (fst _ _).fst' hcount hexpand (computableInPolyTime_stage hkey)
    hexpand.polyBounded_length
    (fun q i _ => length_encList_sublist _ (iterate_stage_sublist i _))

/-- **The procedure is polynomial-time**, for a polynomial-time `key` and a bound `t` computed in
unary. Each level keeps at most `t + 1` nodes, each fixing at most as many occurrences as `φ`
has. -/
theorem computableInPolyTime_accepts {key : CNF ℕ → List Bool}
    (hkey : ComputableInPolyTime key encCNF encBits) {t : CNF ℕ → ℕ}
    (ht : ComputableInPolyTime t encCNF encUnary) :
    ComputableInPolyTime (fun φ => accepts key (t φ) φ) encCNF encBool :=
  Fortune.computableInPolyTime_acceptsWith (par := fun φ => (φ, t φ))
    (prune := fun p => prune (fun a b => key (disj p.1 a b)) p.2) (id'.prod ht)
    (computableInPolyTime_level hkey) (fun _ l _ ha => (prune_sublist l).subset ha)
    (ht.polyBounded.add (.const 1)) fun _ _ => length_prune_le _

/-! ### Mahaney's theorem -/

/-- The disjunction of two nodes fixing variables of `φ` has an encoding of length at most
`|a| |b| (16 L + 21) + L`, where `L` is the length of the encoding of `φ`. -/
theorem length_encCNF_disj_le {φ : CNF ℕ} {a b : List (Literal ℕ)} (ha : ∀ l ∈ a, l.1 ∈ φ.vars)
    (hb : ∀ l ∈ b, l.1 ∈ φ.vars) :
    (encCNF (disj φ a b)).length ≤
      a.length * b.length * (16 * (encCNF φ).length + 21) + (encCNF φ).length := by
  have hclause : ∀ c ∈ a.flatMap (fun l => b.map fun m => [l, m]),
      (encList (encPair encNat encBool) c).length ≤ 8 * (encCNF φ).length + 10 := by
    intro c hc
    simp only [List.mem_flatMap, List.mem_map] at hc
    obtain ⟨l, hl, m, hm, rfl⟩ := hc
    have h₁ := length_encNat_le_of_mem_vars (ha l hl)
    have h₂ := length_encNat_le_of_mem_vars (hb m hm)
    simp only [encList_cons, encList_nil, List.append_nil, List.length_append, length_frame,
      length_encPair, encBool_apply, List.length_singleton]
    omega
  have hcross := length_encList_le _ _ hclause
  have hlen : (a.flatMap fun l => b.map fun m => [l, m]).length = a.length * b.length := by
    simp [List.length_flatMap, List.sum_replicate, List.map_const']
  rw [hlen] at hcross
  have hcross' : (encCNF (a.flatMap fun l => b.map fun m => [l, m])).length ≤
      a.length * b.length * (16 * (encCNF φ).length + 21) := by
    have e : a.length * b.length * (2 * (8 * (encCNF φ).length + 10) + 1) =
        a.length * b.length * (16 * (encCNF φ).length + 21) := by ring
    exact e ▸ hcross
  rw [disj, length_encCNF_append]
  omega

/-- **If `SAT` reduces to a sparse problem, then `SAT` is in `P`**, decided by Agrawal's
procedure [Grochow, Theorem 2.1][Grochow2016]. The labels are the encoded images of the
disjunctions of pairs of nodes under the reduction, and the bound counts the members of the
sparse problem whose encodings are at most as long as the longest label. -/
theorem SAT_mem_P {β : Type*} {encB : β ↪ List Bool} {S : Set β} (hS : S ∈ SPARSE encB)
    (h : PolyTimeReducible encCNF encB SAT S) : SAT ∈ P encCNF := by
  obtain ⟨f, hf, hfS⟩ := h
  have hkey : ComputableInPolyTime (fun ψ => encB (f ψ)) encCNF encBits :=
    (of_eq (encIn := encB) (encOut := encBits) (f := fun b => encB b) fun _ => rfl).comp hf
  obtain ⟨p, hp⟩ := hkey.polyBounded_length.exists_polynomial
  obtain ⟨C, D, hCD⟩ := exists_card_le_of_mem_SPARSE (image_mem_SPARSE_encBits_iff.mpr hS)
  /- Labels have length at most `p (L L (16 L + 21) + L)`, and at most `q L` members of the
  sparse problem are that short. -/
  let q : Polynomial ℕ := Polynomial.C C * (p.comp (Polynomial.X * Polynomial.X *
    (16 * Polynomial.X + 21) + Polynomial.X) + 1) ^ D
  have hq (L : ℕ) : q.eval L = C * (p.eval (L * L * (16 * L + 21) + L) + 1) ^ D := by
    simp [q]
  refine ⟨fun φ => accepts (fun ψ => encB (f ψ)) (q.eval (encCNF φ).length) φ,
    computableInPolyTime_accepts hkey ((unary_eval q).comp (encoding_length encCNF)),
    fun φ => (accepts_iff (K := encB '' S) (M := p.eval ((encCNF φ).length *
      (encCNF φ).length * (16 * (encCNF φ).length + 21) + (encCNF φ).length))
      (fun ψ => ?_) (fun a b ha hb hla hlb => ?_) (fun s hs => ?_)).symm⟩
  · rw [encB.injective.mem_set_image]
    exact hfS ψ
  · refine (hp _).trans (Polynomial.eval_mono _ ?_)
    have hvars := length_vars_le φ
    have hla' : a.length ≤ (encCNF φ).length := hla.trans hvars
    have hlb' : b.length ≤ (encCNF φ).length := hlb.trans hvars
    refine (length_encCNF_disj_le ha hb).trans ?_
    gcongr
  · rw [hq]
    exact hCD _ s fun w hw => by simpa using hs w hw

end Mahaney

/-- **Mahaney's theorem:** if a sparse problem is `NP`-hard under polynomial-time many-one
reductions, then `P = NP`, for every encoding of instances [Mahaney1982]. -/
theorem NPHard.P_eq_NP_of_mem_SPARSE {β : Type*} {encB : β ↪ List Bool} {S : Set β}
    (hard : NPHard encB S) (hS : S ∈ SPARSE encB) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  CookLevin.SAT_npComplete.P_eq_NP_of_mem_P
    (Mahaney.SAT_mem_P hS (hard encCNF SAT SAT.mem_NP)) enc

end Cslib.Complexity
