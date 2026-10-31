/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Sparse.Mahaney
public import Complexity.Computability.Complexity.Reduction.TruthTableVariants
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
# Sparse sets hard for `NP` under one-query reductions

If `SAT` reduces to a sparse problem by a polynomial-time truth-table reduction making at most one
query, then `P = NP` (`Cslib.Complexity.OneQuery.P_eq_NP_of_mem_SPARSE`). This generalizes
Mahaney's theorem (`Complexity/Computability/Complexity/Classes/Sparse/Mahaney.lean`) and, since
the answer may be negated, Fortune's theorem. The proof is Grochow's variant of Agrawal's proof
[Grochow, Question 3.2][Grochow2016].

A one-query reduction gives each formula `ψ` a *signed label* `(w, s)`, a word `w` and a sign
`s`, such that `ψ` is satisfiable exactly when `w` lies in a sparse problem `K` if `s` is `true`,
and exactly when `w` lies outside `K` if `s` is `false`. For a reduction to `S`, `K` consists of
the encodings of the members of `S` marked by a leading `true`
(`Cslib.Complexity.OneQuery.mem_SAT_iff_signedKey`). The source labels a formula with the query
and whether its answer is negated; here a formula whose result does not depend on the answer gets
the empty word, which lies outside `K`, with the sign that gives its result.

The decision procedure searches the self-reduction tree of a formula `φ` as Mahaney's does,
pruning each level in stages (`Cslib.Complexity.OneQuery.stage`). A stage takes the first node `a`
and labels every other node `b` with the signed label of `a ∨ b` (`Cslib.Complexity.Mahaney.disj`).

* Of the other nodes with the same label, only the first is kept. If `a` is satisfiable it is
  kept anyway; otherwise nodes with the same label are all satisfiable or all unsatisfiable.
* If more than `t` of the remaining nodes have the sign `true`, then `a` is unsatisfiable, since
  their labels are distinct members of `K` when `a` is satisfiable. Then `a` is dropped.
* Otherwise `a` is kept, with the first `2 t + 1` other nodes. If `a` is unsatisfiable and a
  satisfiable node is dropped, then at least `t + 1` of the kept nodes have the sign `false`;
  their labels would all lie in `K` if they were all unsatisfiable, so one of them is satisfiable.

Here `t` bounds the number of members of `K` no longer than the labels. A stage removes a node or
leaves at most `2 t + 2` of them, so as many stages as there are nodes leave at most `2 t + 2`
nodes, the source's bound of `2 (t + 1)`, one of them satisfiable if one was before
(`Cslib.Complexity.OneQuery.accepts_iff`). The source stops and accepts in two cases where a
satisfiable node is certain to exist: more than `t` distinct labels with the sign `false`, or one
word with both signs. Here a stage keeps the first node and the first `2 t + 1` others instead, so
that every stage is the same step.

## Main definitions

* `Cslib.Complexity.OneQuery.stage`, `Cslib.Complexity.OneQuery.prune`: the pruning rule for
  signed labels.
* `Cslib.Complexity.OneQuery.accepts`: the decision procedure for `SAT`.
* `Cslib.Complexity.OneQuery.signedKey`: the signed label of a formula under a one-query
  reduction.

## Main results

* `Cslib.Complexity.OneQuery.length_prune_le`: a pruned level has at most `2 t + 2` nodes.
* `Cslib.Complexity.OneQuery.accepts_iff`: the procedure decides satisfiability when the signed
  labels come from a reduction of `SAT` and few labels of bounded length are in the target.
* `Cslib.Complexity.OneQuery.computableInPolyTime_accepts`: the procedure is polynomial-time.
* `Cslib.Complexity.OneQuery.mem_SAT_iff_signedKey`: a one-query reduction of `SAT` gives signed
  labels.
* `Cslib.Complexity.OneQuery.SAT_mem_P`: if `SAT` reduces to a sparse problem with one query,
  `SAT ∈ P`.
* `Cslib.Complexity.OneQuery.P_eq_NP_of_mem_SPARSE`: the resulting collapse `P = NP`.

## References

* [J. A. Grochow, *NP-hard sets are not sparse unless P = NP: An exposition of a simple proof of
  Mahaney's Theorem, with applications*][Grochow2016]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM SAT

namespace OneQuery

/-! ### The pruning rule for signed labels -/

section Prune

variable {α κ : Type*} [DecidableEq κ] (label : α → α → κ × Bool) (t : ℕ)

/-- The nodes `rest` after the node `a`, keeping the first with each label `label a b`. -/
def reps (a : α) (rest : List α) : List α :=
  rest.eraseDupsBy fun b b' => decide (label a b = label a b')

/-- **One stage of the pruning rule** with the signed labels `label a b` of pairs of nodes and the
bound `t`: of the nodes after the first node `a`, keep the first with each label; drop `a` if more
than `t` of them have the sign `true`, and otherwise keep `a` and the first `2 t + 1` of them. -/
def stage : List α → List α
  | [] => []
  | a :: rest =>
    if t < ((reps label a rest).filter fun b => (label a b).2).length then reps label a rest
    else a :: (reps label a rest).take (2 * t + 1)

/-- **The pruning rule:** as many stages as there are nodes. -/
def prune (l : List α) : List α := (stage label t)^[l.length] l

variable {label t}

theorem reps_sublist (a : α) (rest : List α) : (reps label a rest).Sublist rest :=
  List.eraseDupsBy_sublist rest

theorem stage_sublist : ∀ l : List α, (stage label t l).Sublist l
  | [] => List.Sublist.slnil
  | a :: rest => by
    rw [stage]
    split
    · exact (reps_sublist a rest).cons a
    · exact ((List.take_sublist _ _).trans (reps_sublist a rest)).cons_cons a

theorem length_stage_le : ∀ l : List α, (stage label t l).length ≤ max (2 * t + 2) (l.length - 1)
  | [] => Nat.zero_le _
  | a :: rest => by
    have h := (reps_sublist (label := label) a rest).length_le
    rw [stage]
    split
    · simp only [List.length_cons, Nat.add_sub_cancel]
      omega
    · have := List.length_take_le (2 * t + 1) (reps label a rest)
      rw [List.length_cons]
      omega

theorem iterate_stage_sublist (i : ℕ) (l : List α) : ((stage label t)^[i] l).Sublist l := by
  induction i with
  | zero => exact List.Sublist.refl l
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (stage_sublist _).trans ih

theorem length_iterate_stage_le (i : ℕ) (l : List α) :
    ((stage label t)^[i] l).length ≤ max (2 * t + 2) (l.length - i) := by
  induction i with
  | zero => exact le_max_right _ _
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    refine (length_stage_le _).trans ?_
    omega

theorem prune_sublist (l : List α) : (prune label t l).Sublist l := iterate_stage_sublist _ l

/-- A pruned level has at most `2 t + 2` nodes. -/
theorem length_prune_le (l : List α) : (prune label t l).length ≤ 2 * t + 2 := by
  have := length_iterate_stage_le (label := label) (t := t) l.length l
  rw [Nat.sub_self] at this
  exact this.trans (by omega)

end Prune

/-! ### The search -/

/-- **The decision procedure** with the signed reduction `key` and the bound `t`: search the
self-reduction tree of `φ`, labelling the pair of nodes `a`, `b` with `key (disj φ a b)`, and
accept when a leaf is satisfied by the values it fixes. -/
def accepts (key : CNF ℕ → List Bool × Bool) (t : ℕ) (φ : CNF ℕ) : Bool :=
  Fortune.acceptsWith (prune (fun a b => key (Mahaney.disj φ a b)) t) φ

/-! ### Correctness -/

section Correctness

variable {key : CNF ℕ → List Bool × Bool} {K : Set (List Bool)} {t M : ℕ} {φ : CNF ℕ}

/-- Distinct signed labels with the same sign, whose words are members of `K` of length at most
`M`, number at most `t`. -/
private theorem length_le_of_nodup
    (hc : ∀ s : Finset (List Bool), (∀ w ∈ s, w ∈ K ∧ w.length ≤ M) → s.card ≤ t)
    {β : Type*} {lab : β → List Bool × Bool} {T : List β} (hnd : (T.map lab).Nodup) {s₀ : Bool}
    (hsign : ∀ b ∈ T, (lab b).2 = s₀) (hK : ∀ b ∈ T, (lab b).1 ∈ K ∧ (lab b).1.length ≤ M) :
    T.length ≤ t := by
  have hnd' : ((T.map lab).map Prod.fst).Nodup := by
    refine hnd.map_on fun x hx y hy hxy => ?_
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hy
    exact Prod.ext hxy (by rw [hsign b hb, hsign b' hb'])
  have hle := hc ((T.map lab).map Prod.fst).toFinset fun w hw => by
    simp only [List.mem_toFinset, List.map_map, List.mem_map, Function.comp_apply] at hw
    obtain ⟨b, hb, rfl⟩ := hw
    exact hK b hb
  rwa [List.toFinset_card_of_nodup hnd', List.length_map, List.length_map] at hle

/-- A stage keeps a satisfiable node, if there is one. -/
private theorem exists_mem_stage (hkey : ∀ ψ, ψ ∈ SAT ↔ ((key ψ).1 ∈ K ↔ (key ψ).2 = true))
    (hc : ∀ s : Finset (List Bool), (∀ w ∈ s, w ∈ K ∧ w.length ≤ M) → s.card ≤ t)
    {l : List (List (Literal ℕ))}
    (hM : ∀ a ∈ l, ∀ b ∈ l, (key (Mahaney.disj φ a b)).1.length ≤ M)
    (h : ∃ a ∈ l, units a ++ φ ∈ SAT) :
    ∃ a ∈ stage (fun a b => key (Mahaney.disj φ a b)) t l, units a ++ φ ∈ SAT := by
  obtain ⟨x, hx, hxsat⟩ := h
  match l, hx, hM with
  | a :: rest, hx, hM =>
    rw [stage]
    set kept := reps (fun a b => key (Mahaney.disj φ a b)) a rest
    have hnodup : (kept.map fun b => key (Mahaney.disj φ a b)).Nodup :=
      List.pairwise_map.2 ((List.pairwise_eraseDupsBy _).imp fun h => by
        simpa [eq_comm] using h)
    have hlen : ∀ b ∈ kept, (key (Mahaney.disj φ a b)).1.length ≤ M := fun b hb =>
      hM a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ ((reps_sublist a rest).subset hb))
    /- A satisfiable node after `a`, when `a` is unsatisfiable, has a satisfiable representative
    among the kept nodes. -/
    have hrep : ∀ b ∈ rest, units b ++ φ ∈ SAT → units a ++ φ ∉ SAT →
        ∃ b' ∈ kept, units b' ++ φ ∈ SAT := by
      intro b hb hbsat hanot
      obtain ⟨b', hb', hbb'⟩ := List.exists_mem_eraseDupsBy
        (r := fun b b' => decide (key (Mahaney.disj φ a b) = key (Mahaney.disj φ a b'))) hb
      refine ⟨b', hb', ?_⟩
      rcases hbb' with rfl | hlab
      · exact hbsat
      · have hdisj : Mahaney.disj φ a b' ∈ SAT := by
          rw [hkey, ← of_decide_eq_true hlab, ← hkey]
          exact Mahaney.disj_mem_SAT_iff.2 (.inr hbsat)
        exact (Mahaney.disj_mem_SAT_iff.1 hdisj).resolve_left hanot
    have hcases : units a ++ φ ∈ SAT ∨ ∃ b' ∈ kept, units b' ++ φ ∈ SAT := by
      by_cases hasat : units a ++ φ ∈ SAT
      · exact .inl hasat
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd hxsat hasat
        · exact .inr (hrep x hx hxsat hasat)
    split
    · rename_i hpos
      by_cases hasat : units a ++ φ ∈ SAT
      · /- If `a` were satisfiable, every kept label with the sign `true` would lie in `K`. -/
        exfalso
        have hle := length_le_of_nodup hc (lab := fun b => key (Mahaney.disj φ a b))
          (T := kept.filter fun b => (key (Mahaney.disj φ a b)).2) (s₀ := true)
          (hnodup.sublist ((List.filter_sublist).map _))
          (fun b hb => by simpa using (List.mem_filter.1 hb).2) fun b hb => by
            have hsign : (key (Mahaney.disj φ a b)).2 = true := by
              simpa using (List.mem_filter.1 hb).2
            refine ⟨?_, hlen b (List.mem_filter.1 hb).1⟩
            have := (hkey (Mahaney.disj φ a b)).1 (Mahaney.disj_mem_SAT_iff.2 (.inl hasat))
            rwa [hsign, iff_true_right rfl] at this
        omega
      · exact hcases.resolve_left hasat
    · rename_i hpos
      by_contra hnone
      push Not at hnone
      have hasat : units a ++ φ ∉ SAT := hnone a (List.mem_cons_self ..)
      obtain ⟨b', hb', hb'sat⟩ := hcases.resolve_left hasat
      by_cases hshort : kept.length ≤ 2 * t + 1
      · exact hnone b' (List.mem_cons_of_mem _ (by rwa [List.take_of_length_le hshort])) hb'sat
      · /- Otherwise at least `t + 1` of the first `2 t + 1` kept nodes have the sign `false`,
        and their labels would all lie in `K`. -/
        set T := kept.take (2 * t + 1)
        have hT : T.length = 2 * t + 1 := List.length_take_of_le (by omega)
        have hTpos : (T.filter fun b => (key (Mahaney.disj φ a b)).2).length ≤ t :=
          (((List.take_sublist _ _).filter _).length_le).trans (not_lt.1 hpos)
        have hTneg := length_le_of_nodup hc (lab := fun b => key (Mahaney.disj φ a b))
          (T := T.filter fun b => !(key (Mahaney.disj φ a b)).2) (s₀ := false)
          (hnodup.sublist (((List.filter_sublist).trans (List.take_sublist _ _)).map _))
          (fun b hb => by simpa using (List.mem_filter.1 hb).2) fun b hb => by
            have hbT := (List.mem_filter.1 hb).1
            have hsign : (key (Mahaney.disj φ a b)).2 = false := by
              simpa using (List.mem_filter.1 hb).2
            refine ⟨?_, hlen b ((List.take_sublist _ _).subset hbT)⟩
            have hdisj : Mahaney.disj φ a b ∉ SAT := fun h =>
              (Mahaney.disj_mem_SAT_iff.1 h).elim hasat (hnone b (List.mem_cons_of_mem _ hbT))
            rw [hkey, hsign] at hdisj
            simpa using hdisj
        have := List.length_eq_length_filter_add
          (l := T) fun b => (key (Mahaney.disj φ a b)).2
        omega

/-- Pruning keeps a satisfiable node, if there is one. -/
private theorem exists_mem_prune (hkey : ∀ ψ, ψ ∈ SAT ↔ ((key ψ).1 ∈ K ↔ (key ψ).2 = true))
    (hc : ∀ s : Finset (List Bool), (∀ w ∈ s, w ∈ K ∧ w.length ≤ M) → s.card ≤ t)
    {l : List (List (Literal ℕ))}
    (hM : ∀ a ∈ l, ∀ b ∈ l, (key (Mahaney.disj φ a b)).1.length ≤ M)
    (h : ∃ a ∈ l, units a ++ φ ∈ SAT) :
    ∃ a ∈ prune (fun a b => key (Mahaney.disj φ a b)) t l, units a ++ φ ∈ SAT := by
  suffices ∀ i, ∃ a ∈ (stage (fun a b => key (Mahaney.disj φ a b)) t)^[i] l,
      units a ++ φ ∈ SAT from this _
  intro i
  induction i with
  | zero => exact h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have hsub := (iterate_stage_sublist
      (label := fun a b => key (Mahaney.disj φ a b)) (t := t) i l).subset
    exact exists_mem_stage hkey hc (fun a ha b hb => hM a (hsub ha) b (hsub hb)) ih

/-- **Correctness of the procedure.** If the signed labels `key` reduce `SAT` to `K`, the words of
the labels of the pairs of nodes of the tree of `φ` have length at most `M`, and every finite set
of members of `K` of length at most `M` has at most `t` elements, then the procedure accepts
exactly the satisfiable `φ`. -/
theorem accepts_iff (hkey : ∀ ψ, ψ ∈ SAT ↔ ((key ψ).1 ∈ K ↔ (key ψ).2 = true))
    (hM : ∀ a b : List (Literal ℕ), (∀ l ∈ a, l.1 ∈ φ.vars) → (∀ l ∈ b, l.1 ∈ φ.vars) →
      a.length ≤ φ.vars.length → b.length ≤ φ.vars.length →
        (key (Mahaney.disj φ a b)).1.length ≤ M)
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
private theorem stage_eq (label : List (Literal ℕ) → List (Literal ℕ) → List Bool × Bool)
    (t : ℕ) (l : List (List (Literal ℕ))) :
    stage label t l = if l.isEmpty then [] else
      if t < ((l.tail.eraseDupsBy fun b b' =>
          decide (label (l.headD []) b = label (l.headD []) b')).filter
            fun b => (label (l.headD []) b).2).length then
        l.tail.eraseDupsBy fun b b' => decide (label (l.headD []) b = label (l.headD []) b')
      else l.headD [] :: (l.tail.eraseDupsBy fun b b' =>
        decide (label (l.headD []) b = label (l.headD []) b')).take (2 * t + 1) := by
  cases l <;> rfl

/-- A stage is polynomial-time, uniformly in the formula, the bound and the nodes. -/
private theorem computableInPolyTime_stage {key : CNF ℕ → List Bool × Bool}
    (hkey : ComputableInPolyTime key encCNF (encPair encBits encBool)) :
    ComputableInPolyTime
      (fun r : (CNF ℕ × ℕ) × List (List (Literal ℕ)) =>
        stage (fun a b => key (Mahaney.disj r.1.1 a b)) r.1.2 r.2)
      (encPair (encPair encCNF encUnary) encNodes) encNodes := by
  simp only [stage_eq]
  unfold Mahaney.disj
  fun_prop

/-- A level of the search is polynomial-time, uniformly in the formula, the bound, the nodes and
the occurrence: every stage keeps a sublist of the expanded level. -/
private theorem computableInPolyTime_level {key : CNF ℕ → List Bool × Bool}
    (hkey : ComputableInPolyTime key encCNF (encPair encBits encBool)) :
    ComputableInPolyTime
      (fun q : ((CNF ℕ × ℕ) × List (List (Literal ℕ))) × ℕ =>
        prune (fun a b => key (Mahaney.disj q.1.1.1 a b)) q.1.1.2 (Fortune.expand q.2 q.1.2))
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
  exact iterateWith (par := fun q => q.1.1)
    (step := fun r l => stage (fun a b => key (Mahaney.disj r.1 a b)) r.2 l)
    (fst _ _).fst' hcount hexpand (computableInPolyTime_stage hkey)
    hexpand.polyBounded_length
    (fun q i _ => length_encList_sublist _ (iterate_stage_sublist i _))

/-- **The procedure is polynomial-time**, for a polynomial-time signed reduction `key` and a
bound `t` computed in unary. Each level keeps at most `2 t + 2` nodes, each fixing at most as
many occurrences as `φ` has. -/
theorem computableInPolyTime_accepts {key : CNF ℕ → List Bool × Bool}
    (hkey : ComputableInPolyTime key encCNF (encPair encBits encBool)) {t : CNF ℕ → ℕ}
    (ht : ComputableInPolyTime t encCNF encUnary) :
    ComputableInPolyTime (fun φ => accepts key (t φ) φ) encCNF encBool :=
  Fortune.computableInPolyTime_acceptsWith (par := fun φ => (φ, t φ))
    (prune := fun p => prune (fun a b => key (Mahaney.disj p.1 a b)) p.2) (id'.prod ht)
    (computableInPolyTime_level hkey) (fun _ l _ ha => (prune_sublist l).subset ha)
    (((PolyBounded.const 2).mul ht.polyBounded).add (.const 2)) fun _ _ => length_prune_le _

/-! ### Signed labels from a one-query reduction -/

section SignedKey

variable {β : Type} {encB : β ↪ List Bool}

/-- **The signed label of `ψ`** under a truth-table reduction `(r, q, d)` to a problem over `β`
making at most one query. When the combiner `d` gives the same result `b` for both answers, the
label is `([], !b)`; otherwise it is the encoded query, marked by a leading `true`, with the sign
`true` if the combiner accepts the answer `true` and `false` if it accepts the answer `false`. -/
def signedKey (encB : β ↪ List Bool) (r : CNF ℕ → ℕ) (q : CNF ℕ × ℕ → β)
    (d : CNF ℕ × List Bool → Bool) (ψ : CNF ℕ) : List Bool × Bool :=
  if d (ψ, List.replicate (r ψ) false) = d (ψ, List.replicate (r ψ) true) then
    ([], !d (ψ, List.replicate (r ψ) false))
  else (true :: encB (q (ψ, 0)), d (ψ, List.replicate (r ψ) true))

/-- **Signed labels of a one-query reduction.** If `(r, q, d)` reduces `SAT` to `S` with at most
one query, then a formula is satisfiable exactly when the word of its signed label lies in the
words `true :: encB s` for `s ∈ S` if the sign is `true`, and outside them if it is `false`. -/
theorem mem_SAT_iff_signedKey {S : Set β} {r : CNF ℕ → ℕ} {q : CNF ℕ × ℕ → β}
    {d : CNF ℕ × List Bool → Bool} (hr : ∀ ψ, r ψ ≤ 1)
    (hL : ∀ ψ, ψ ∈ SAT ↔ d (ψ, truthTableAnswers (q ⁻¹' S) r ψ) = true) (ψ : CNF ℕ) :
    ψ ∈ SAT ↔ ((signedKey encB r q d ψ).1 ∈ List.cons true '' (encB '' S) ↔
      (signedKey encB r q d ψ).2 = true) := by
  classical
  have hcons : ∀ w : List Bool, true :: w ∈ List.cons true '' (encB '' S) ↔ w ∈ encB '' S :=
    fun w => (List.cons_injective).mem_set_image
  have hnil : ([] : List Bool) ∉ List.cons true '' (encB '' S) := by
    rintro ⟨w, -, hw⟩
    exact List.cons_ne_nil _ _ hw
  rw [hL, signedKey]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hr ψ) with h0 | h1
  · have hans : truthTableAnswers (q ⁻¹' S) r ψ = [] := by
      rw [← List.length_eq_zero_iff, length_truthTableAnswers, h0]
    simp only [h0, List.replicate_zero, ite_true, hans]
    simp [hnil]
  · have hans : truthTableAnswers (q ⁻¹' S) r ψ = [decide (q (ψ, 0) ∈ S)] := by
      rw [truthTableAnswers_eq_map_range, h1]
      simp
    simp only [h1, List.replicate_one, hans]
    split
    · rename_i heq
      cases hq : decide (q (ψ, 0) ∈ S) <;> simp [heq, hnil]
    · rename_i hne
      rw [hcons, encB.injective.mem_set_image]
      by_cases hqS : q (ψ, 0) ∈ S
      · simp [hqS]
      · have hfalse : d (ψ, [false]) = !d (ψ, [true]) := by
          cases hf : d (ψ, [false]) <;> cases ht : d (ψ, [true]) <;> simp_all
        simp [hqS, hfalse]

/-- Signed labels are polynomial-time when the reduction is. -/
theorem computableInPolyTime_signedKey {r : CNF ℕ → ℕ} {q : CNF ℕ × ℕ → β}
    {d : CNF ℕ × List Bool → Bool} (hr : ComputableInPolyTime r encCNF encUnary)
    (hq : ComputableInPolyTime q (encPair encCNF encUnary) encB)
    (hd : ComputableInPolyTime d (encPair encCNF encBits) encBool) :
    ComputableInPolyTime (signedKey encB r q d) encCNF (encPair encBits encBool) := by
  have hencB : ComputableInPolyTime (fun b => encB b) encB encBits :=
    of_eq (encIn := encB) (encOut := encBits) (f := fun b => encB b) fun _ => rfl
  unfold signedKey
  fun_prop

end SignedKey

/-! ### Sparse sets hard under one-query reductions -/

/-- **If `SAT` reduces to a sparse problem by a one-query truth-table reduction, then `SAT` is in
`P`**, decided by Grochow's variant of Agrawal's procedure [Grochow, Question 3.2][Grochow2016].
The labels are the signed labels of the disjunctions of pairs of nodes, and the bound counts the
members of the sparse problem whose encodings are at most as long as the longest label. -/
theorem SAT_mem_P {β : Type} {encB : β ↪ List Bool} {S : Set β} (hS : S ∈ SPARSE encB)
    (h : PolyTimeKTruthTableReducible 1 encCNF encB SAT S) : SAT ∈ P encCNF := by
  obtain ⟨r, q, d, hr, hq, hd, hr1, hL⟩ := h
  have hkey := computableInPolyTime_signedKey hr hq hd
  have hword : ComputableInPolyTime (fun ψ => (signedKey encB r q d ψ).1) encCNF encBits :=
    (fst encBits encBool).comp hkey
  obtain ⟨p, hp⟩ := hword.polyBounded_length.exists_polynomial
  obtain ⟨C, D, hCD⟩ := exists_card_le_of_mem_SPARSE (image_mem_SPARSE_encBits_iff.mpr hS)
  /- The words of the labels have length at most `p (L L (16 L + 21) + L)`, and at most `q L` of
  them are marked encodings of members of the sparse problem. -/
  let Q : Polynomial ℕ := Polynomial.C C * (p.comp (Polynomial.X * Polynomial.X *
    (16 * Polynomial.X + 21) + Polynomial.X) + 1) ^ D
  have hQ (L : ℕ) : Q.eval L = C * (p.eval (L * L * (16 * L + 21) + L) + 1) ^ D := by
    simp [Q]
  refine ⟨fun φ => accepts (signedKey encB r q d) (Q.eval (encCNF φ).length) φ,
    computableInPolyTime_accepts hkey ((unary_eval Q).comp (encoding_length encCNF)),
    fun φ => (accepts_iff (K := List.cons true '' (encB '' S)) (M := p.eval ((encCNF φ).length *
      (encCNF φ).length * (16 * (encCNF φ).length + 21) + (encCNF φ).length))
      (mem_SAT_iff_signedKey hr1 hL) (fun a b ha hb hla hlb => ?_) (fun s hs => ?_)).symm⟩
  · refine (hp _).trans (Polynomial.eval_mono _ ?_)
    have hvars := length_vars_le φ
    have hla' : a.length ≤ (encCNF φ).length := hla.trans hvars
    have hlb' : b.length ≤ (encCNF φ).length := hlb.trans hvars
    refine (Mahaney.length_encCNF_disj_le ha hb).trans ?_
    gcongr
  · /- Dropping the leading `true` is injective on `s`, and gives members of the sparse problem
    no longer than the words in `s`. -/
    rw [hQ]
    have hinj : Set.InjOn List.tail (s : Set (List Bool)) := by
      intro w hw w' hw' hww'
      obtain ⟨u, -, rfl⟩ := (hs w hw).1
      obtain ⟨u', -, rfl⟩ := (hs w' hw').1
      simpa using hww'
    rw [← Finset.card_image_of_injOn hinj]
    refine hCD _ _ fun v hv => ?_
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨⟨u, hu, rfl⟩, hlen⟩ := hs w hw
    exact ⟨hu, by simpa using (Nat.le_succ _).trans hlen⟩

/-- **Sparse sets are not hard for `NP` under one-query reductions unless `P = NP`:** if `SAT`
reduces to a sparse problem by a polynomial-time truth-table reduction making at most one query,
then `P = NP`, for every encoding of instances [Grochow, Question 3.2][Grochow2016]. -/
theorem P_eq_NP_of_mem_SPARSE {β : Type} {encB : β ↪ List Bool} {S : Set β}
    (h : PolyTimeKTruthTableReducible 1 encCNF encB SAT S) (hS : S ∈ SPARSE encB)
    {α : Type} (enc : α ↪ List Bool) : P enc = NP enc :=
  CookLevin.SAT_npComplete.P_eq_NP_of_mem_P (SAT_mem_P hS h) enc

end OneQuery

end Cslib.Complexity
