/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Sparse.Hausdorff
public import Complexity.Computability.Complexity.Classes.Sparse.Prune
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Sparse sets hard for `NP` under bounded truth-table reductions

If `SAT` reduces to a sparse problem by a polynomial-time bounded truth-table reduction, then
`P = NP` (`Cslib.Complexity.BTT.P_eq_NP_of_mem_SPARSE`), a theorem of Ogiwara and Watanabe
[Arvind, Köbler and Mundhenk, Section 1][ArvindKoblerMundhenk1992]. More generally, the reduction
may go to a problem that reduces conjunctively to a sparse problem
(`Cslib.Complexity.BTT.P_eq_NP_of_polyTimeCTTReducible`). This is Arvind, Köbler and Mundhenk's
theorem that a problem in `NP` whose left set is in `R_btt(R_ctt(SPARSE))` is in `P`
[Arvind, Köbler and Mundhenk, Theorem 3.4][ArvindKoblerMundhenk1992], for `SAT`, whose left set
reduces to `SAT` itself (`Cslib.Complexity.LeftSAT_polyTimeReducible_SAT`); the hypothesis here is
on `SAT` rather than on its left set.

The procedure searches the self-reduction tree of a formula `φ` level by level, as the conjunctive
procedure does (`Cslib.Complexity.Conjunctive.accepts`). A node `a` is in the left set of `φ` when
`SAT.atLeast a ++ φ` is satisfiable, and the members of the left set in a level, read in increasing
order, are the nodes up to the largest satisfiable node. The bounded truth-table reduction gives
`SAT` a Hausdorff decomposition `⋃ d < D, C (2 d) \ C (2 d + 1)` with decreasing sets `C j`
(`Cslib.Complexity.BTT.eq_true_iff_exists_hausdorff`), each with a conjunctive reduction to a
tally problem (`Cslib.Complexity.BTT.exists_polyTimeCTTReducible_hausdorff`). The node `a` asks the
queries of `SAT.atLeast a ++ φ` for each `C j`, and `PRUNE`
(`Cslib.Complexity.BTT.prune`) keeps the largest satisfiable node
(`Cslib.Complexity.BTT.getElem_mem_prune`) and polynomially many nodes: the queries are unary
numbers bounded by a polynomial `M` in the length of `φ`, so at most `M + 1` of them lie in a
target.

## Main definitions

* `Cslib.Complexity.BTT.accepts`: the decision procedure for `SAT`.

## Main results

* `Cslib.Complexity.BTT.accepts_iff`: the procedure decides satisfiability when the queries come
  from conjunctive reductions of the sets of a Hausdorff decomposition of `SAT`, with bounded
  values.
* `Cslib.Complexity.BTT.computableInPolyTime_accepts`: the procedure is polynomial-time.
* `Cslib.Complexity.BTT.SAT_mem_P_of_polyTimeCTTReducible`, `Cslib.Complexity.BTT.SAT_mem_P`: if
  `SAT` reduces by a bounded truth-table reduction to a problem with a conjunctive reduction to a
  sparse problem, or to a sparse problem, then `SAT ∈ P`.
* `Cslib.Complexity.BTT.P_eq_NP_of_polyTimeCTTReducible`,
  `Cslib.Complexity.BTT.P_eq_NP_of_mem_SPARSE`: the resulting collapses `P = NP`.

## References

* [V. Arvind, J. Köbler, M. Mundhenk, *On Bounded Truth-Table, Conjunctive, and Randomized
  Reductions to Sparse Sets*][ArvindKoblerMundhenk1992]
-/

@[expose] public section

namespace Cslib.Complexity.BTT

open Cslib.Logic.PL Turing.MultiTapeTM SAT Conjunctive

/-- **The decision procedure** with the queries `key`, the bound `s` and `D` depths: search the
self-reduction tree of `φ`, keeping the levels in decreasing order and pruning each with `PRUNE` on
the level in increasing order, where the node `a` asks the queries `key j (atLeast a ++ φ)` for the
`j`-th set; accept when a leaf is satisfied by the values it fixes. -/
def accepts (key : ℕ → CNF ℕ → List ℕ) (D s : ℕ) (φ : CNF ℕ) : Bool :=
  Fortune.acceptsWith (fun l => (prune (fun j a => key j (atLeast a ++ φ)) s D l.reverse).reverse) φ

/-! ### Correctness -/

section Correctness

variable {φ : CNF ℕ} {C : ℕ → CNF ℕ → Prop} {key : ℕ → CNF ℕ → List ℕ} {A : ℕ → Set ℕ}
  {D M s : ℕ}

/-- **Pruning keeps the largest satisfiable node.** On a level in decreasing order, read in
increasing order, the members of the left set are the nodes up to the largest satisfiable node
`c`, and the left set has the Hausdorff decomposition given by the sets `C j`. -/
private theorem mem_prune_of_isLargest (hnest : ∀ j ψ, C (j + 1) ψ → C j ψ)
    (hsat : ∀ ψ, ψ ∈ SAT ↔ ∃ d < D, C (2 * d) ψ ∧ ¬C (2 * d + 1) ψ)
    (hkey : ∀ j < 2 * D, ∀ ψ, C j ψ ↔ ∀ w ∈ key j ψ, w ∈ A j)
    (hM : ∀ j < 2 * D, ∀ a : List (Literal ℕ), (∀ l ∈ a, l.1 ∈ φ.vars) →
      a.length ≤ φ.vars.length → ∀ w ∈ key j (atLeast a ++ φ), w ≤ M)
    (hs : M + 1 ≤ s) {pre : List ℕ} (hpre : pre.IsPrefix φ.vars) {l : List (List (Literal ℕ))}
    (hfst : ∀ a ∈ l, a.map Prod.fst = pre)
    (hsort : l.Pairwise fun a b => b.map Prod.snd < a.map Prod.snd)
    {c : List (Literal ℕ)} (hcl : c ∈ l) (hlarge : IsLargest φ c) :
    c ∈ (prune (fun j a => key j (atLeast a ++ φ)) s D l.reverse).reverse := by
  set N := l.reverse
  have hsortN : N.Pairwise fun a b => a.map Prod.snd < b.map Prod.snd :=
    List.pairwise_reverse.2 hsort
  have hfstN : ∀ a ∈ N, a.map Prod.fst = pre := fun a ha => hfst a (List.mem_reverse.1 ha)
  obtain ⟨h, hh, hNh⟩ := List.getElem_of_mem (List.mem_reverse.2 hcl : c ∈ N)
  rw [List.mem_reverse, ← hNh]
  refine getElem_mem_prune (C := fun j a => C j (atLeast a ++ φ))
    (K := fun j => {w | w ∈ A j ∧ w ≤ M}) hh (fun j _ _ => hnest j _) (fun i hi => ?_)
    (fun j hj y hy => ?_) (fun j _ T hT => ?_)
  · /- The node at position `i` is in the left set exactly when it is at most `c`. -/
    rw [← hsat]
    have hfst' : N[i].map Prod.fst = c.map Prod.fst :=
      (hfstN _ (List.getElem_mem hi)).trans (hfstN c (hNh ▸ List.getElem_mem hh)).symm
    constructor
    · intro hih
      refine atLeast_append_mem_SAT_of_le hlarge hfst' ?_
      rcases Nat.lt_or_eq_of_le hih with hlt | rfl
      · exact hNh ▸ (List.pairwise_iff_getElem.1 hsortN i h hi hh hlt).le
      · exact hNh ▸ le_rfl
    · intro hmem
      by_contra hhi
      exact atLeast_append_notMem_SAT_of_lt hlarge hfst'
        (hNh ▸ List.pairwise_iff_getElem.1 hsortN h i hh hi (by omega)) hmem
  · /- The queries of the nodes of the tree are at most `M`. -/
    have hnode := Fortune.mem_vars_and_length_le_of_map_fst_eq hpre (hfstN y hy)
    have hbound := hM j hj y hnode.1 hnode.2
    exact (hkey j hj _).trans ⟨fun h w hw => ⟨h w hw, hbound w hw⟩, fun h w hw => (h w hw).1⟩
  · /- At most `M + 1` queries are at most `M`. -/
    have hsub : T ⊆ Finset.range (M + 1) := fun w hw =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (hT w hw).2)
    exact (Finset.card_le_card hsub).trans (by simpa using hs)

/-- **Correctness of the procedure.** Let the sets `C j` decrease and give `SAT` the Hausdorff
decomposition `⋃ d < D, C (2 d) \ C (2 d + 1)`. If, for each `j < 2 D`, the queries `key j` reduce
`C j` conjunctively to a set `A j` of natural numbers, the queries of the nodes of the tree of `φ`
are at most `M`, and `s ≥ M + 1`, then the procedure accepts exactly the satisfiable `φ`. -/
theorem accepts_iff (hnest : ∀ j ψ, C (j + 1) ψ → C j ψ)
    (hsat : ∀ ψ, ψ ∈ SAT ↔ ∃ d < D, C (2 * d) ψ ∧ ¬C (2 * d + 1) ψ)
    (hkey : ∀ j < 2 * D, ∀ ψ, C j ψ ↔ ∀ w ∈ key j ψ, w ∈ A j)
    (hM : ∀ j < 2 * D, ∀ a : List (Literal ℕ), (∀ l ∈ a, l.1 ∈ φ.vars) →
      a.length ≤ φ.vars.length → ∀ w ∈ key j (atLeast a ++ φ), w ≤ M)
    (hs : M + 1 ≤ s) :
    accepts key D s φ = true ↔ φ ∈ SAT := by
  have hsub : ∀ l : List (List (Literal ℕ)),
      (((prune (fun j a => key j (atLeast a ++ φ)) s D l.reverse).reverse).Sublist l) :=
    fun l => by simpa using (prune_sublist (Q := fun j a => key j (atLeast a ++ φ)) (s := s)
      (D := D) (N := l.reverse)).reverse
  obtain ⟨hfst, -, hlarge⟩ := Fortune.searchWith_induction
    (prune := fun l => (prune (fun j a => key j (atLeast a ++ φ)) s D l.reverse).reverse) (φ := φ)
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
      refine ⟨fun b hb => hexp b ((hsub _).subset hb), hsort'.sublist (hsub _), fun hφ => ?_⟩
      obtain ⟨a, ha, halarge⟩ := hlarge hφ
      obtain ⟨x, hx⟩ := exists_isLargest_child halarge v
      refine ⟨_, mem_prune_of_isLargest hnest hsat hkey hM hs hpre hexp hsort' ?_ hx, hx⟩
      simp only [Fortune.expand, List.mem_flatMap]
      exact ⟨a, ha, by cases x <;> simp⟩
  exact Fortune.acceptsWith_iff_of_searchWith hfst fun h =>
    (hlarge h).imp fun _ ⟨ha, hlarge⟩ => ⟨ha, hlarge.1⟩

end Correctness

/-! ### Polynomial time -/

open ComputableInPolyTime

/-- The encoding of the list of nodes at a level of the tree. -/
local notation "encNodes" => encList (encList (encPair encNat encBool))

/-- **The procedure is polynomial-time**, for polynomial-time queries `key j`, a fixed number `D`
of depths and a bound `s` computed in unary. Each level keeps at most `2 D (s + 2) ^ (2 D)`
nodes. -/
theorem computableInPolyTime_accepts {key : ℕ → CNF ℕ → List ℕ}
    (hkey : ∀ j, ComputableInPolyTime (key j) encCNF (encList encUnary)) (D : ℕ)
    {s : CNF ℕ → ℕ} (hs : ComputableInPolyTime s encCNF encUnary) :
    ComputableInPolyTime (fun φ => accepts key D (s φ) φ) encCNF encBool := by
  have hlevel : ComputableInPolyTime
      (fun q : ((CNF ℕ × ℕ) × List (List (Literal ℕ))) × ℕ =>
        (prune (fun j a => key j (atLeast a ++ q.1.1.1)) q.1.1.2 D
          (Fortune.expand q.2 q.1.2).reverse).reverse)
      (encPair (encPair (encPair encCNF encUnary) encNodes) encNat) encNodes := by
    have hprune := computableInPolyTime_prune
      (encIn := encPair (encPair (encPair encCNF encUnary) encNodes) encNat)
      (encA := encList (encPair encNat encBool)) (encK := encUnary)
      (Q := fun (q : ((CNF ℕ × ℕ) × List (List (Literal ℕ))) × ℕ) j a =>
        key j (atLeast a ++ q.1.1.1))
      (s := fun q => q.1.1.2) (N := fun q => (Fortune.expand q.2 q.1.2).reverse) D
      (fun j => by have := hkey j; fun_prop) (by fun_prop) (by unfold Fortune.expand; fun_prop)
    fun_prop
  refine Fortune.computableInPolyTime_acceptsWith (par := fun φ => (φ, s φ))
    (prune := fun p l => (prune (fun j a => key j (atLeast a ++ p.1)) p.2 D l.reverse).reverse)
    (id'.prod hs) hlevel (fun _ l a ha => ?_)
    (width := fun φ => 2 * D * (s φ + 2) ^ (2 * D))
    ((PolyBounded.const _).mul ((hs.polyBounded.add (.const 2)).pow _)) fun _ _ => ?_
  · exact List.mem_reverse.1 ((prune_sublist).subset (List.mem_reverse.1 ha))
  · rw [List.length_reverse]
    exact length_prune_le

/-! ### Sparse sets hard under bounded truth-table reductions -/

/-- **If `SAT` reduces by a bounded truth-table reduction to a problem with a conjunctive reduction
to a sparse problem, then `SAT` is in `P`**, decided by the left-set search with `PRUNE`
[Arvind, Köbler and Mundhenk, Theorem 3.4][ArvindKoblerMundhenk1992]. The queries of a node for the
`j`-th Hausdorff set are those of a conjunctive reduction of that set to a tally problem, on the
formula saying that the assignment is at least the node. -/
theorem SAT_mem_P_of_polyTimeCTTReducible {β γ : Type} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {B : Set β} {S : Set γ} (hS : S ∈ SPARSE encC)
    (hB : PolyTimeCTTReducible encB encC B S) (h : PolyTimeBTTReducible encCNF encB SAT B) :
    SAT ∈ P encCNF := by
  obtain ⟨k, r, q, d, hr, hq, hd, hk, hL⟩ := h
  obtain ⟨AS, hAS⟩ := exists_polyTimeCTTReducible_encUnary_of_mem_SPARSE hS
  have hred := fun j => exists_polyTimeCTTReducible_hausdorff (j := j) ⟨AS, hB.trans hAS⟩
    hr hq hd hk
  choose A rj qj hrj hqj hA using hred
  set C : ℕ → CNF ℕ → Prop :=
    fun j ψ => Hausdorff (fun v => d (ψ, v)) (truthTableAnswers (q ⁻¹' B) r ψ) j
  set D := k / 2 + 1
  set key : ℕ → CNF ℕ → List ℕ := fun j ψ => (List.range (rj j ψ)).map fun i => qj j (ψ, i)
  have hkey (j : ℕ) : ComputableInPolyTime (key j) encCNF (encList encUnary) := by
    have := hrj j
    have := hqj j
    fun_prop
  have hnode (j : ℕ) : ComputableInPolyTime
      (fun p : CNF ℕ × List (Literal ℕ) => key j (atLeast p.2 ++ p.1))
      (encPair encCNF (encList (encPair encNat encBool))) (encList encUnary) := by
    have := hkey j
    fun_prop
  choose p hp using fun j => (hnode j).polyBounded_length.exists_polynomial
  /- The queries of the nodes are at most `M (L)`, where `L` is the length of the formula. -/
  let M : Polynomial ℕ := ∑ j ∈ Finset.range (2 * D),
    (p j).comp (2 * Polynomial.X + 1 + Polynomial.X * (4 * Polynomial.X + 5))
  have hM (L : ℕ) :
      M.eval L = ∑ j ∈ Finset.range (2 * D), (p j).eval (2 * L + 1 + L * (4 * L + 5)) := by
    simp [M, Polynomial.eval_finsetSum]
  refine ⟨fun φ => accepts key D ((M + 1).eval (encCNF φ).length) φ,
    computableInPolyTime_accepts hkey D ((unary_eval (M + 1)).comp (encoding_length encCNF)),
    fun φ => (accepts_iff (C := C) (A := A) (M := M.eval (encCNF φ).length)
      (fun j ψ hψ => hψ.of_succ) (fun ψ => ?_) (fun j _ ψ => ?_) (fun j hj a ha hlen w hw => ?_)
      (by simp)).symm⟩
  · rw [hL ψ]
    refine eq_true_iff_exists_hausdorff (f := fun v => d (ψ, v))
      (b := truthTableAnswers (q ⁻¹' B) r ψ) ?_
    rw [length_truthTableAnswers]
    have := hk ψ
    omega
  · simpa [key] using hA j ψ
  · have hw' :=
      SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary) _ w hw
    rw [encUnary_apply, List.length_replicate] at hw'
    refine hw'.trans ((hp j (φ, a)).trans ?_)
    rw [hM]
    refine le_trans (Polynomial.eval_mono _ ?_)
      (Finset.single_le_sum (f := fun j => (p j).eval _) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 hj))
    have hnode := Fortune.length_encNode_le ha hlen
    rw [length_encPair]
    dsimp only
    omega

/-- **If `SAT` reduces to a sparse problem by a bounded truth-table reduction, then `SAT` is in
`P`**, a theorem of Ogiwara and Watanabe [Arvind, Köbler and Mundhenk, Section 1]
[ArvindKoblerMundhenk1992]: [Arvind, Köbler and Mundhenk, Theorem 3.4][ArvindKoblerMundhenk1992]
with the sparse problem itself as conjunctive target. -/
theorem SAT_mem_P {β : Type} {encB : β ↪ List Bool} {S : Set β} (hS : S ∈ SPARSE encB)
    (h : PolyTimeBTTReducible encCNF encB SAT S) : SAT ∈ P encCNF :=
  SAT_mem_P_of_polyTimeCTTReducible hS (.refl encB S) h

/-- **`NP ⊆ R_btt(R_ctt(SPARSE))` implies `P = NP`:** if `SAT` reduces by a bounded truth-table
reduction to a problem with a conjunctive reduction to a sparse problem, then `P = NP`, for every
encoding of instances [Arvind, Köbler and Mundhenk, Theorem 3.4][ArvindKoblerMundhenk1992]. -/
theorem P_eq_NP_of_polyTimeCTTReducible {β γ : Type} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {B : Set β} {S : Set γ} (h : PolyTimeBTTReducible encCNF encB SAT B)
    (hB : PolyTimeCTTReducible encB encC B S) (hS : S ∈ SPARSE encC) {α : Type}
    (enc : α ↪ List Bool) : P enc = NP enc :=
  CookLevin.SAT_npComplete.P_eq_NP_of_mem_P (SAT_mem_P_of_polyTimeCTTReducible hS hB h) enc

/-- **Sparse sets are not hard for `NP` under bounded truth-table reductions unless `P = NP`**
(Ogiwara and Watanabe; [Arvind, Köbler and Mundhenk, Section 1][ArvindKoblerMundhenk1992]): if
`SAT` reduces to a sparse problem by a polynomial-time bounded truth-table reduction, then
`P = NP`, for every encoding of instances. -/
theorem P_eq_NP_of_mem_SPARSE {β : Type} {encB : β ↪ List Bool} {S : Set β}
    (h : PolyTimeBTTReducible encCNF encB SAT S) (hS : S ∈ SPARSE encB) {α : Type}
    (enc : α ↪ List Bool) : P enc = NP enc :=
  CookLevin.SAT_npComplete.P_eq_NP_of_mem_P (SAT_mem_P hS h) enc

end Cslib.Complexity.BTT
