/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Approximation.MaxCSP
public import Complexity.Computability.Complexity.Problems.ThreeSAT
public import Complexity.Logics.Propositional.CNF.UnsatVal
import Complexity.Computability.PCP.Encoded.Count
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Foundations.Data.List.Filter

/-!
# MAX-3SAT is NP-hard to approximate

The **unsatisfiability value** `CNF.unsatVal φ` of a formula is the least proportion of its clauses
that an assignment falsifies (`Complexity.Logics.Propositional.CNF.UnsatVal`), and
`1 - CNF.unsatVal φ` is its value as an instance of MAX-SAT. `GapThreeSAT s` is the gap problem of
MAX-3SAT with perfect completeness: its instances are formulas whose clauses have at most three
literals, its yes-instances are the satisfiable ones (`ThreeSAT`) and its no-instances those in
which every assignment satisfies at most the proportion `s` of the clauses.

A binary constraint on labels written in `k` bits is a conjunction of clauses of width `2 k`, one
excluding each pair of labels the constraint forbids [Arora and Barak, Chapter 11][AroraBarak09].
`Graph.toCNF` writes a constraint graph this way, and splitting the clauses to width three
(`Cslib.Complexity.toThreeSAT`) gives a gap-preserving reduction from MAX-2CSP to MAX-3SAT: every
violated edge leaves a falsified clause, and each edge produces at most `|α| ^ 2 * (2 k - 2)`
clauses.
From the gap of Dinur's construction (`Cslib.Complexity.GapTwoCSP_npHard`) over `128 = 2 ^ 7`
symbols, MAX-3SAT is NP-hard to approximate within `1 - 1 / (3 * 2 ^ 77)`: the loss is the factor
`128 ^ 2 * 12 = 3 * 2 ^ 16`. That MAX-3SAT is NP-hard to approximate within some constant is due to
Arora, Lund, Motwani, Sudan and Szegedy [AroraLundMotwaniSudanSzegedy1998].

## Main definitions

* `Cslib.PCP.Encoded.Graph.toCNF`: a constraint graph written as a formula.
* `Cslib.Complexity.GapThreeSAT`: the gap problem of MAX-3SAT with perfect completeness.

## Main results

* `Cslib.PCP.Encoded.Graph.div_le_unsatVal_toThreeSAT_toCNF`: the gap-preserving bound.
* `Cslib.Complexity.polyTimeReducible_GapTwoCSP_GapThreeSAT`: MAX-2CSP reduces to MAX-3SAT in
  polynomial time, preserving a gap.
* `Cslib.Complexity.GapThreeSAT_npHard`: distinguishing satisfiable 3CNF formulas from those in
  which every assignment satisfies at most the proportion `1 - 1 / (3 * 2 ^ 77)` of the clauses is
  NP-hard.

## References

* [S. Arora, C. Lund, R. Motwani, M. Sudan, M. Szegedy, *Proof verification and the hardness of
  approximation problems*][AroraLundMotwaniSudanSzegedy1998]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 11][AroraBarak09]
* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Cslib.Logic.PL Cslib.Complexity Finset Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {k : ℕ}

/-! ### Constraint graphs as formulas -/

/-- The clause excluding the label `p.1` at the vertex `u` and the label `p.2` at `v`. The label
of a vertex `u` is written in `k` bits, in the variables `Nat.pair u i` for `i < k`, along `e`. -/
def excludeClause (e : α ≃ (Fin k → Bool)) (u v : ℕ) (p : α × α) : Clause ℕ :=
  (List.finRange k).map (fun i : Fin k => (Nat.pair u i, !e p.1 i)) ++
    (List.finRange k).map (fun i : Fin k => (Nat.pair v i, !e p.2 i))

/-- One clause for each pair in the list `pairs` violating the constraint of the edge. -/
def edgeCNF (e : α ≃ (Fin k → Bool)) (pairs : List (α × α)) (d : Edge (α → α → Bool)) :
    CNF ℕ :=
  (pairs.filter fun p => !d.constraint p.1 p.2).map (excludeClause e d.src d.dst)

/-- A constraint graph written as a formula: one clause of width `2 k` for each edge and each pair
of labels, listed in `pairs`, that its constraint forbids. -/
def toCNF (e : α ≃ (Fin k → Bool)) (pairs : List (α × α)) (g : Graph (α → α → Bool)) : CNF ℕ :=
  g.edges.flatMap (edgeCNF e pairs)

/-- The label of the vertex `u` written by an assignment. -/
def readLabel (e : α ≃ (Fin k → Bool)) (τ : ℕ → Bool) (u : ℕ) : α :=
  e.symm fun i => τ (Nat.pair u i)

variable (e : α ≃ (Fin k → Bool)) (pairs : List (α × α))

private theorem exists_eq_not_iff {τ : ℕ → Bool} {u : ℕ} {a : α} :
    (∃ i : Fin k, τ (Nat.pair u i) = !e a i) ↔ readLabel e τ u ≠ a := by
  rw [readLabel, ne_eq, Equiv.symm_apply_eq, funext_iff]
  simp only [not_forall]
  exact exists_congr fun i => by cases τ (Nat.pair u i) <;> cases e a i <;> simp

/-- An assignment satisfies `excludeClause e u v p` exactly when it does not write the labels `p`
at `u` and `v`. -/
theorem eval_excludeClause_eq_true_iff (τ : ℕ → Bool) (u v : ℕ) (p : α × α) :
    (excludeClause e u v p).eval τ = true ↔ readLabel e τ u ≠ p.1 ∨ readLabel e τ v ≠ p.2 := by
  simp only [excludeClause, Clause.eval_eq_true_iff, List.mem_append, List.mem_map,
    List.mem_finRange, true_and]
  rw [← exists_eq_not_iff, ← exists_eq_not_iff]
  constructor
  · rintro ⟨l, (⟨i, rfl⟩ | ⟨i, rfl⟩), hl⟩
    exacts [Or.inl ⟨i, hl⟩, Or.inr ⟨i, hl⟩]
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    exacts [⟨_, Or.inl ⟨i, rfl⟩, hi⟩, ⟨_, Or.inr ⟨i, rfl⟩, hi⟩]

/-- Every clause of `toCNF` has width `2 k`. -/
private theorem length_of_mem_toCNF {g : Graph (α → α → Bool)} {c : Clause ℕ}
    (hc : c ∈ toCNF e pairs g) :
    c.length = 2 * k := by
  obtain ⟨d, -, hc⟩ := List.mem_flatMap.1 hc
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hc
  simp only [excludeClause, List.length_append, List.length_map, List.length_finRange]
  omega

/-- Each edge produces at most `pairs.length` clauses. -/
private theorem length_toCNF_le (g : Graph (α → α → Bool)) :
    (toCNF e pairs g).length ≤ g.edges.length * pairs.length := by
  rw [toCNF, List.length_flatMap]
  refine (List.sum_le_length_nsmul _ pairs.length fun n hn => ?_).trans (by simp)
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hn
  exact (List.length_map _).trans_le (List.length_filter_le _ _)

/-- A labelling satisfying the constraint graph, written in bits, satisfies its formula. -/
theorem satisfiable_toCNF {g : Graph (α → α → Bool)} (h : (g.toGraph id).Satisfiable) :
    (toCNF e pairs g).Satisfiable := by
  obtain ⟨σ, hσ⟩ := h
  let τ : ℕ → Bool := fun n =>
    if hn : n.unpair.2 < k then e (σ n.unpair.1) ⟨n.unpair.2, hn⟩ else false
  have hτ (u : ℕ) : readLabel e τ u = σ u := by
    rw [readLabel, Equiv.symm_apply_eq]
    funext i
    simp [τ, Nat.unpair_pair]
  refine ⟨τ, (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
  obtain ⟨d, hd, hc⟩ := List.mem_flatMap.1 hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  obtain ⟨i, rfl⟩ := List.get_of_mem hd
  have hsat : (g.edges.get i).constraint (σ (g.edges.get i).src) (σ (g.edges.get i).dst) = true :=
    hσ i
  have hp' : (g.edges.get i).constraint p.1 p.2 = false := by simpa using (List.mem_filter.1 hp).2
  rw [eval_excludeClause_eq_true_iff, hτ, hτ, ← not_and_or]
  rintro ⟨h₁, h₂⟩
  rw [h₁, h₂, hp'] at hsat
  exact Bool.false_ne_true hsat

/-- **Every violated edge leaves a falsified clause**: an assignment falsifies at least as many
clauses of the formula as the labelling it writes violates edges, when `pairs` lists all pairs of
labels. -/
private theorem card_unsatEdges_le_countUnsat (hpairs : ∀ p, p ∈ pairs) (g : Graph (α → α → Bool))
    (τ : ℕ → Bool) :
    #((g.toGraph id).unsatEdges (readLabel e τ)) ≤ (toCNF e pairs g).countUnsat τ := by
  rw [card_unsatEdges_toGraph, CNF.countUnsat, toCNF, List.countP_flatMap]
  simp only [id_eq]
  refine List.countP_le_sum_map fun d _ hd => List.countP_pos_iff.2
    ⟨excludeClause e d.src d.dst (readLabel e τ d.src, readLabel e τ d.dst),
      List.mem_map.2 ⟨_, List.mem_filter.2 ⟨hpairs _, hd⟩, rfl⟩, ?_⟩
  rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, eval_excludeClause_eq_true_iff]
  simp

/-- Splitting the clauses of `toCNF`, all of width `2 k`, gives `2 k - 2` clauses for each, and at
least one. -/
private theorem length_toThreeSAT_toCNF (g : Graph (α → α → Bool)) :
    (toThreeSAT (toCNF e pairs g)).length = (toCNF e pairs g).length * max 1 (2 * k - 2) := by
  rw [toThreeSAT, CNF.relabel, List.length_map, CNF.length_to3CNF,
    List.map_congr_left fun c hc => by rw [length_of_mem_toCNF e pairs hc], List.map_const',
    List.sum_replicate, smul_eq_mul]

/-- **MAX-2CSP reduces to MAX-3SAT, preserving the gap**: if every labelling of the constraint graph
violates the proportion `ε` of its edges, every assignment falsifies the proportion
`ε / (pairs.length * max 1 (2 k - 2))` of the clauses of its formula, split to width three. Labels
are written in `k` bits, along `e`, and `pairs` lists every pair of labels. -/
theorem div_le_unsatVal_toThreeSAT_toCNF (hpairs : ∀ p, p ∈ pairs) (g : Graph (α → α → Bool)) :
    (g.toGraph id).unsatVal / (pairs.length * max 1 (2 * k - 2) : ℕ) ≤
      (toThreeSAT (toCNF e pairs g)).unsatVal := by
  rw [CNF.le_unsatVal_iff]
  intro τ
  set φ := toCNF e pairs g
  set σ := readLabel e (τ ∘ splitVarToNat ∘ Sum.inl)
  set m := max 1 (2 * k - 2)
  have hcount : #((g.toGraph id).unsatEdges σ) ≤ (toThreeSAT φ).countUnsat τ :=
    (card_unsatEdges_le_countUnsat e pairs hpairs g _).trans <| by
      rw [toThreeSAT, CNF.countUnsat_relabel]
      exact CNF.countUnsat_comp_inl_le_countUnsat_to3CNF φ (τ ∘ splitVarToNat)
  have hval : (g.toGraph id).unsatVal ≤ #((g.toGraph id).unsatEdges σ) / g.edges.length := by
    simpa [ConstraintGraph.unsatFrac] using (g.toGraph id).unsatVal_le σ
  have hlen := length_toThreeSAT_toCNF e pairs g
  rcases Nat.eq_zero_or_pos (toThreeSAT φ).length with hL | hL
  · have hC : (toThreeSAT φ).countUnsat τ = 0 :=
      Nat.le_zero.1 (hL ▸ CNF.countUnsat_le_length _ _)
    have hU : #((g.toGraph id).unsatEdges σ) = 0 := Nat.le_zero.1 (hC ▸ hcount)
    have hnonpos : (g.toGraph id).unsatVal ≤ 0 := by simpa [hU] using hval
    rw [hL, Nat.cast_zero, div_zero]
    exact div_nonpos_of_nonpos_of_nonneg hnonpos (Nat.cast_nonneg _)
  · have hm : 0 < m := lt_max_of_lt_left Nat.one_pos
    have hφ : 0 < φ.length := by
      rw [hlen] at hL
      exact Nat.pos_of_mul_pos_right hL
    have hφle : φ.length ≤ g.edges.length * pairs.length := length_toCNF_le e pairs g
    have hn : 0 < g.edges.length := Nat.pos_of_mul_pos_right (hφ.trans_le hφle)
    have hp : 0 < pairs.length := Nat.pos_of_mul_pos_left (hφ.trans_le hφle)
    have hLle : ((toThreeSAT φ).length : ℝ) ≤ g.edges.length * (pairs.length * m : ℕ) := by
      rw [hlen, ← Nat.cast_mul, Nat.cast_le, ← Nat.mul_assoc]
      exact Nat.mul_le_mul_right m hφle
    calc (g.toGraph id).unsatVal / (pairs.length * m : ℕ)
        ≤ #((g.toGraph id).unsatEdges σ) / g.edges.length / (pairs.length * m : ℕ) :=
          div_le_div_of_nonneg_right hval (Nat.cast_nonneg _)
      _ = #((g.toGraph id).unsatEdges σ) / (g.edges.length * (pairs.length * m : ℕ)) := by
          rw [div_div]
      _ ≤ (toThreeSAT φ).countUnsat τ / (g.edges.length * (pairs.length * m : ℕ)) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hcount) (by positivity)
      _ ≤ (toThreeSAT φ).countUnsat τ / (toThreeSAT φ).length :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast hL) hLle

/-! ### Polynomial time -/

variable [Fintype α]

/-- Writing a constraint graph as a formula is polynomial-time: for each edge, every pair in the
fixed list `pairs` is tested against its constraint table. -/
@[fun_prop]
theorem isPolyTime_toCNF :
    ComputableInPolyTime (toCNF e pairs) (encoding (encPi (encPi encBool))) encCNF := by
  have hpair : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
    have hleft : ComputableInPolyTime (fun p : ℕ × ℕ => p.2 * p.2 + p.1)
        (encPair encUnary encUnary) encUnary := by fun_prop
    have hright : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.1 + p.1 + p.2)
        (encPair encUnary encUnary) encUnary := by fun_prop
    simpa [Nat.pair] using unary_lt.ite hleft hright
  have hclause (p : α × α) : ComputableInPolyTime
      (fun d : Edge (α → α → Bool) => excludeClause e d.src d.dst p)
      (Edge.encoding (encPi (encPi encBool))) (encList (encPair encNat encBool)) := by
    unfold excludeClause
    fun_prop
  have htest (p : α × α) : ComputableInPolyTime
      (fun d : Edge (α → α → Bool) => !d.constraint p.1 p.2)
      (Edge.encoding (encPi (encPi encBool))) encBool := by
    fun_prop
  have hmapFilter (l : List (α × α)) : ComputableInPolyTime
      (fun d : Edge (α → α → Bool) =>
        (l.filter fun p => !d.constraint p.1 p.2).map (excludeClause e d.src d.dst))
      (Edge.encoding (encPi (encPi encBool))) encCNF := by
    induction l with
    | nil => exact const []
    | cons p l ih =>
      simp only [List.filter_cons, List.map_cons, apply_ite]
      exact (htest p).ite ((hclause p).cons' ih) ih
  exact flatMapWithInput (isPolyTime_edges id') ((hmapFilter pairs).comp (snd _ _))

end Cslib.PCP.Encoded.Graph

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

/-- The gap problem of **MAX-3SAT** with perfect completeness and soundness `s`. The instances are
the formulas whose clauses have at most three literals; their value is the largest proportion of
the clauses, counted with multiplicity, that an assignment satisfies. The yes-instances have value
one, the no-instances value at most `s`. -/
noncomputable def GapThreeSAT (s : ℝ) : PromiseProblem (CNF ℕ) :=
  (PromiseProblem.gapMax (fun φ => 1 - φ.unsatVal) (fun _ => 1) (fun _ => s)).restrict
    {φ | ∀ c ∈ φ, c.length ≤ 3}

variable {s : ℝ} {φ : CNF ℕ}

/-- The yes-instances of `GapThreeSAT` are the members of `ThreeSAT`. -/
theorem yes_GapThreeSAT : (GapThreeSAT s).yes = ThreeSAT := by
  ext φ
  simp only [GapThreeSAT, PromiseProblem.yes_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_yes_gapMax, Set.mem_ofPred_eq, ThreeSAT, ← CNF.unsatVal_eq_zero_iff]
  have := φ.unsatVal_nonneg
  constructor
  · rintro ⟨h, h3⟩
    exact ⟨h3, by linarith⟩
  · rintro ⟨h3, h⟩
    exact ⟨by linarith, h3⟩

/-- For `s < 1`, the no-instances of `GapThreeSAT` are the formulas of width at most three in
which every assignment falsifies at least the proportion `1 - s` of the clauses. -/
theorem mem_no_GapThreeSAT (hs : s < 1) :
    φ ∈ (GapThreeSAT s).no ↔ (∀ c ∈ φ, c.length ≤ 3) ∧ 1 - s ≤ φ.unsatVal := by
  simp only [GapThreeSAT, PromiseProblem.no_restrict, Set.mem_inter_iff,
    PromiseProblem.mem_no_gapMax_of_lt (c := fun _ => (1 : ℝ)) (s := fun _ => s) hs,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h, h3⟩
    exact ⟨h3, by linarith⟩
  · rintro ⟨h3, h⟩
    exact ⟨by linarith, h3⟩

/-- **MAX-2CSP reduces to MAX-3SAT**: for labels written in `k` bits along an equivalence `e`, the
gap problem of MAX-2CSP with soundness `s < 1` reduces in polynomial time to that of MAX-3SAT with
soundness `1 - (1 - s) / (|α| ^ 2 * (2 k - 2))`, through `Cslib.PCP.Encoded.Graph.toCNF` and
splitting to width three. -/
theorem polyTimeReducible_GapTwoCSP_GapThreeSAT {α : Type} [Fintype α] {k : ℕ}
    (e : α ≃ (Fin k → Bool)) (hs : s < 1) :
    PromiseProblem.PolyTimeReducible (Graph.encoding (encPi (encPi encBool))) encCNF
      (GapTwoCSP α s)
      (GapThreeSAT (1 - (1 - s) / (Fintype.card α ^ 2 * max 1 (2 * k - 2) : ℕ))) := by
  have : Nonempty α := ⟨e.symm fun _ => false⟩
  let pairs := (Finset.univ : Finset (α × α)).toList
  have hpairs : ∀ p, p ∈ pairs := fun p => Finset.mem_toList.2 (Finset.mem_univ p)
  have hlen : pairs.length = Fintype.card α ^ 2 := by
    simp [pairs, Fintype.card_prod, sq]
  refine ⟨fun g => toThreeSAT (Graph.toCNF e pairs g),
    computableInPolyTime_toThreeSAT.comp (Graph.isPolyTime_toCNF e pairs),
    fun g hg => ?_, fun g hg => ?_⟩
  · rw [yes_GapThreeSAT, mem_ThreeSAT_toThreeSAT_iff]
    exact Graph.satisfiable_toCNF e pairs (mem_yes_GapTwoCSP.1 hg)
  · have hK : (0 : ℝ) < (Fintype.card α ^ 2 * max 1 (2 * k - 2) : ℕ) := by
      have := Fintype.card_pos (α := α)
      positivity
    refine (mem_no_GapThreeSAT ?_).2 ⟨fun c hc => ?_, ?_⟩
    · have : 0 < 1 - s := by linarith
      linarith [div_pos this hK]
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      simpa using CNF.length_le_three_of_mem_to3CNF hd
    · rw [sub_sub_cancel, ← hlen]
      exact ((div_le_div_of_nonneg_right ((mem_no_GapTwoCSP hs).1 hg) (by rw [hlen]; positivity)))
        |>.trans (Graph.div_le_unsatVal_toThreeSAT_toCNF e pairs hpairs g)

/-- **MAX-3SAT is NP-hard to approximate** [AroraLundMotwaniSudanSzegedy1998], [Arora and Barak,
Chapter 11][AroraBarak09]: distinguishing satisfiable formulas with at most three literals per
clause from those in which every assignment satisfies at most the proportion
`1 - 1 / (3 * 2 ^ 77)` of the clauses is NP-hard. The constant comes from Dinur's gap `2 ^ (-61)`
over `128 = 2 ^ 7` symbols (`GapTwoCSP_npHard`), divided by `128 ^ 2 * 12 = 3 * 2 ^ 16` clauses per
edge. -/
theorem GapThreeSAT_npHard : PromiseProblem.NPHard encCNF (GapThreeSAT (1 - 1 / (3 * 2 ^ 77))) := by
  have hcard : Fintype.card (Bool × (Fin 6 → Bool)) = 128 := by
    simp [Fintype.card_prod, Fintype.card_bool]
  have hs : 1 - (1 - (1 - 1 / 2 ^ 61 : ℝ)) /
      (Fintype.card (Bool × (Fin 6 → Bool)) ^ 2 * max 1 (2 * (6 + 1) - 2) : ℕ) =
      1 - 1 / (3 * 2 ^ 77) := by
    rw [hcard]
    norm_num
  have hred := polyTimeReducible_GapTwoCSP_GapThreeSAT (Fin.consEquiv fun _ : Fin 7 => Bool)
    (by norm_num : (1 - 1 / 2 ^ 61 : ℝ) < 1)
  rw [hs] at hred
  intro _ enc A hA
  exact (GapTwoCSP_npHard enc A hA).trans hred

/-- Unless `P = NP`, no polynomial-time algorithm distinguishes satisfiable 3CNF formulas from
those in which every assignment satisfies at most the proportion `1 - 1 / (3 * 2 ^ 77)` of the
clauses. -/
theorem GapThreeSAT_notMem_PromiseP {β : Type} {enc : β ↪ List Bool} (h : P enc ≠ NP enc) :
    GapThreeSAT (1 - 1 / (3 * 2 ^ 77)) ∉ PromiseP encCNF :=
  GapThreeSAT_npHard.notMem_PromiseP h

end Cslib.Complexity
