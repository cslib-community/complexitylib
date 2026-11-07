/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Approximation.LabelCover
public import Complexity.Computability.PCP.Approximation.MaxCSP
import Complexity.Computability.PCP.Encoded.Count
import Complexity.Foundations.Data.List.Filter
import Complexity.Foundations.Data.BitString.Enumeration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Incidence projections from binary CSP to Label Cover

Each edge occurrence becomes a left vertex carrying a pair of symbols, and two total projection
edges check the two endpoint labels. Invalid pair labels retract to a satisfying pair, using a
fixed exhaustive list. A relation with no satisfying pair instead produces a fixed contradictory
projection instance. Loops and parallel edges retain their occurrence identities.

The construction and factor-two gap bound are original library adaptations to the existing
executable graph and total-projection APIs. The source hardness theorem is the already-proved
`Cslib.Complexity.GapTwoCSP_npHard`. This is a constant-gap prerequisite for small-soundness Label
Cover; parallel repetition is not established here.

## Main definitions

* `Cslib.PCP.Encoded.LabelCoverIncidence.repair`: retract pair labels to satisfying pairs.
* `Cslib.PCP.Encoded.LabelCoverIncidence.incidence`: the two projections per edge occurrence.
* `Cslib.PCP.Encoded.LabelCoverIncidence.reduce`: handle empty relations explicitly.

## Main results

* `Cslib.PCP.Encoded.LabelCoverIncidence.satisfiable_reduce`: perfect completeness.
* `Cslib.PCP.Encoded.LabelCoverIncidence.half_unsatVal_le_reduce`: the factor-two gap bound.
* `Cslib.PCP.Encoded.LabelCoverIncidence.isPolyTime_reduce`: native polynomial-time compilation
  under the existing framed graph/table encodings, for a fixed finite alphabet.
* `Cslib.Complexity.GapLabelCover_npHard`: constant-gap hardness with `128²` left labels and
  `128` right labels, at soundness `1 - 2⁻⁶²`.
-/

@[expose] public section

namespace Cslib.PCP.Encoded.LabelCoverIncidence

open Cslib.Complexity Finset Turing.MultiTapeTM

variable {α : Type}

/-- Keep satisfying pairs; repair any other pair using the first satisfying pair in `pairs`.
The fallback is read only when no such pair exists. -/
def repair (pairs : List (α × α)) (fallback : α × α) (R : α → α → Bool) (p : α × α) : α × α :=
  if R p.1 p.2 then p else (pairs.find? fun q => R q.1 q.2).getD fallback

/-- Repair fixes every pair that already satisfies the relation. -/
theorem repair_eq (pairs : List (α × α)) (fallback : α × α) {R : α → α → Bool}
    {p : α × α} (hp : R p.1 p.2 = true) : repair pairs fallback R p = p := by
  simp [repair, hp]

/-- A nonempty relation makes every repaired pair satisfying. -/
theorem satisfies_repair (pairs : List (α × α)) (fallback : α × α) {R : α → α → Bool}
    (hR : pairs.any (fun p => R p.1 p.2) = true) (p : α × α) :
    R (repair pairs fallback R p).1 (repair pairs fallback R p).2 = true := by
  unfold repair
  split
  · assumption
  · cases hfind : pairs.find? (fun q => R q.1 q.2) with
    | none =>
      obtain ⟨q, hq, hRq⟩ := List.any_eq_true.mp hR
      exact False.elim ((List.find?_eq_none.mp hfind q hq) hRq)
    | some q =>
      simpa only [Option.getD_some] using
        (List.find?_some (p := fun q : α × α => R q.1 q.2) hfind)

/-- The two incidence projections associated to source edge occurrence `i`. -/
def block (pairs : List (α × α)) (fallback : α × α) (d : Edge (α → α → Bool))
    (i : ℕ) : List (Edge (α × α → α)) :=
  [⟨i, d.src, fun p => (repair pairs fallback d.constraint p).1⟩,
   ⟨i, d.dst, fun p => (repair pairs fallback d.constraint p).2⟩]

/-- The occurrence-indexed incidence graph. Left and right vertex numbers are separate, as in
`GapLabelCover`; an original loop still yields two distinct incidence edge occurrences. -/
def incidence (pairs : List (α × α)) (fallback : α × α)
    (g : Graph (α → α → Bool)) : Graph (α × α → α) :=
  ⟨g.vertices + g.edges.length, g.edges.zipIdx.flatMap fun p => block pairs fallback p.1 p.2⟩

/-- Each input edge occurrence contributes two projection edges. -/
theorem length_edges_incidence (pairs : List (α × α)) (fallback : α × α)
    (g : Graph (α → α → Bool)) :
    (incidence pairs fallback g).edges.length = 2 * g.edges.length := by
  simp [incidence, List.length_flatMap, block, List.map_const', List.sum_replicate,
    Nat.mul_comm]

/-- Two constant projections to distinct symbols cannot both be satisfied. -/
def contradiction (a b : α) : Graph (α × α → α) :=
  ⟨1, [⟨0, 0, fun _ => a⟩, ⟨0, 0, fun _ => b⟩]⟩

/-- Send an empty relation to the contradictory instance; otherwise take incidence projections. -/
def reduce (pairs : List (α × α)) (a b : α) (g : Graph (α → α → Bool)) :
    Graph (α × α → α) :=
  if g.edges.any (fun d => !(pairs.any fun p => d.constraint p.1 p.2)) then
    contradiction a b
  else incidence pairs (a, a) g

variable [DecidableEq α]

/-- The fixed contradictory instance has unsatisfied value exactly one half. -/
theorem unsatVal_contradiction (a b : α) (hab : a ≠ b) :
    ((contradiction a b).toGraph projectionEval).unsatVal = 1 / 2 := by
  let : Nonempty α := ⟨a⟩
  have hcount (τ : ℕ → (α × α) × α) :
      1 ≤ (contradiction a b).edges.countP
        (fun d => !projectionEval d.constraint (τ d.src) (τ d.dst)) := by
    have hnot : ¬(a = (τ 0).2 ∧ b = (τ 0).2) := fun h => hab (h.1.trans h.2.symm)
    by_cases ha : a = (τ 0).2 <;> by_cases hb : b = (τ 0).2 <;>
      simp [contradiction, projectionEval, ha, hb] at *
  refine le_antisymm ?_ ((ConstraintGraph.le_unsatVal_iff _).2 fun τ => ?_)
  · have h := ((contradiction a b).toGraph projectionEval).unsatVal_le
      (fun _ => ((a, a), a))
    rw [Graph.unsatFrac_toGraph] at h
    simpa [contradiction, projectionEval, hab, Ne.symm hab] using h
  · rw [Graph.unsatFrac_toGraph]
    have h := hcount τ
    have hlen : (contradiction a b).edges.length = 2 := rfl
    rw [hlen]
    exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 (by exact_mod_cast h)

private theorem count_violations_le_incidence (pairs : List (α × α)) (fallback : α × α)
    (g : Graph (α → α → Bool))
    (hR : ∀ d ∈ g.edges, pairs.any (fun p => d.constraint p.1 p.2) = true)
    (τ : ℕ → (α × α) × α) :
    g.edges.countP (fun d => !d.constraint (τ d.src).2 (τ d.dst).2) ≤
      (incidence pairs fallback g).edges.countP
        (fun d => !projectionEval d.constraint (τ d.src) (τ d.dst)) := by
  have hmap : g.edges.countP (fun d => !d.constraint (τ d.src).2 (τ d.dst).2) =
      g.edges.zipIdx.countP (fun p => !p.1.constraint (τ p.1.src).2 (τ p.1.dst).2) := by
    change _ = g.edges.zipIdx.countP
      ((fun d : Edge (α → α → Bool) => !d.constraint (τ d.src).2 (τ d.dst).2) ∘ Prod.fst)
    rw [← List.countP_map, List.zipIdx_map_fst]
  rw [hmap, incidence, List.countP_flatMap]
  refine List.countP_le_sum_map fun ⟨d, i⟩ hdi hbad => ?_
  have hgood := satisfies_repair pairs fallback (hR d (List.fst_mem_of_mem_zipIdx hdi))
    ((τ i).1)
  have hnotboth : ¬((repair pairs fallback d.constraint (τ i).1).1 = (τ d.src).2 ∧
      (repair pairs fallback d.constraint (τ i).1).2 = (τ d.dst).2) := by
    rintro ⟨h₁, h₂⟩
    rw [h₁, h₂] at hgood
    have hfalse : d.constraint (τ d.src).2 (τ d.dst).2 = false := by
      simpa using hbad
    exact Bool.noConfusion (hgood.symm.trans hfalse)
  by_cases h₁ : (repair pairs fallback d.constraint (τ i).1).1 = (τ d.src).2 <;>
    by_cases h₂ : (repair pairs fallback d.constraint (τ i).1).2 = (τ d.dst).2 <;>
    simp [block, projectionEval, h₁, h₂] at *

/-- Every labelling of the incidence graph decodes to a source labelling with at most twice its
violated fraction. The label of each source vertex is the right component of the target label. -/
theorem half_unsatVal_le_incidence (pairs : List (α × α)) (fallback : α × α)
    (g : Graph (α → α → Bool))
    (hR : ∀ d ∈ g.edges, pairs.any (fun p => d.constraint p.1 p.2) = true) :
    (g.toGraph id).unsatVal / 2 ≤
      ((incidence pairs fallback g).toGraph projectionEval).unsatVal := by
  let : Nonempty α := ⟨fallback.1⟩
  apply (ConstraintGraph.le_unsatVal_iff _).2
  intro τ
  have hval := (g.toGraph id).unsatVal_le (fun v => (τ v).2)
  rw [Graph.unsatFrac_toGraph] at hval
  rw [Graph.unsatFrac_toGraph, length_edges_incidence]
  have hcount := count_violations_le_incidence pairs fallback g hR τ
  have hcount' : (g.edges.countP (fun d => !d.constraint (τ d.src).2 (τ d.dst).2) : ℝ) ≤
      ((incidence pairs fallback g).edges.countP
        (fun d => !projectionEval d.constraint (τ d.src) (τ d.dst)) : ℝ) := by
    exact_mod_cast hcount
  calc (g.toGraph id).unsatVal / 2 ≤
        (g.edges.countP (fun d => !d.constraint (τ d.src).2 (τ d.dst).2) : ℝ) /
          g.edges.length / 2 := div_le_div_of_nonneg_right hval (by norm_num)
    _ ≤ ((incidence pairs fallback g).edges.countP
        (fun d => !projectionEval d.constraint (τ d.src) (τ d.dst)) : ℝ) /
          g.edges.length / 2 := by gcongr
    _ = _ := by push_cast; ring

/-- Source satisfiability gives a satisfying pair at every edge occurrence and hence a satisfying
labelling of the incidence projections. -/
theorem satisfiable_incidence (pairs : List (α × α)) (fallback : α × α)
    {g : Graph (α → α → Bool)} (hg : (g.toGraph id).Satisfiable) :
    ((incidence pairs fallback g).toGraph projectionEval).Satisfiable := by
  obtain ⟨σ, hσ⟩ := hg
  let edge (i : ℕ) := g.edges.getD i ⟨0, 0, fun _ _ => false⟩
  apply (satisfiable_toGraph_projectionEval_iff _).2
  refine ⟨fun i => (σ (edge i).src, σ (edge i).dst), σ, ?_⟩
  intro e he
  obtain ⟨⟨d, i⟩, hdi, he⟩ := List.mem_flatMap.mp he
  have hget : edge i = d := by
    unfold edge
    rw [List.getD_eq_getElem?_getD, List.mk_mem_zipIdx_iff_getElem?.mp hdi]
    rfl
  have hd := List.fst_mem_of_mem_zipIdx hdi
  obtain ⟨j, rfl⟩ := List.get_of_mem hd
  have hsat : (g.edges.get j).constraint (σ (g.edges.get j).src) (σ (g.edges.get j).dst) = true :=
    hσ j
  have hrepair := repair_eq pairs fallback (R := (g.edges.get j).constraint)
    (p := (σ (g.edges.get j).src, σ (g.edges.get j).dst)) hsat
  simp only [block, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> simp only [hget, hrepair]

/-- The reduction retains at least half the source unsatisfied value, including an empty relation
or an empty edge list. -/
theorem half_unsatVal_le_reduce (pairs : List (α × α)) (a b : α) (hab : a ≠ b)
    (g : Graph (α → α → Bool)) :
    (g.toGraph id).unsatVal / 2 ≤ ((reduce pairs a b g).toGraph projectionEval).unsatVal := by
  by_cases hnone : g.edges.any (fun d => !(pairs.any fun p => d.constraint p.1 p.2)) = true
  · rw [reduce, ite_eq_left hnone, unsatVal_contradiction a b hab]
    let : Nonempty α := ⟨a⟩
    exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
      (g.toGraph id).unsatVal_le_one
  · rw [reduce, ite_eq_right hnone]
    apply half_unsatVal_le_incidence
    intro d hd
    have hnone' : g.edges.any (fun d => !(pairs.any fun p => d.constraint p.1 p.2)) = false :=
      Bool.eq_false_iff.mpr hnone
    have h := (List.any_eq_false.mp hnone') d hd
    simpa using h

/-- An exhaustive pair list ensures that satisfiable source instances never enter the empty
relation branch. -/
theorem satisfiable_reduce (pairs : List (α × α)) (hpairs : ∀ p, p ∈ pairs) (a b : α)
    {g : Graph (α → α → Bool)} (hg : (g.toGraph id).Satisfiable) :
    ((reduce pairs a b g).toGraph projectionEval).Satisfiable := by
  have hnone : g.edges.any (fun d => !(pairs.any fun p => d.constraint p.1 p.2)) = false := by
    rw [List.any_eq_false]
    intro d hd
    obtain ⟨σ, hσ⟩ := hg
    obtain ⟨i, rfl⟩ := List.get_of_mem hd
    have hsat : (g.edges.get i).constraint (σ (g.edges.get i).src) (σ (g.edges.get i).dst) = true :=
      hσ i
    simpa using
      ((List.any_eq_true (l := pairs)
        (p := fun p => (g.edges.get i).constraint p.1 p.2)).mpr
        ⟨(σ (g.edges.get i).src, σ (g.edges.get i).dst), hpairs _, hsat⟩)
  rw [reduce, hnone]
  exact satisfiable_incidence pairs (a, a) hg

section Runtime

variable [Fintype α]

omit [DecidableEq α] in
private theorem isPolyTime_block (pairs : List (α × α)) (fallback : α × α)
    (encA : α ↪ List Bool) :
    ComputableInPolyTime
      (fun p : Edge (α → α → Bool) × ℕ => block pairs fallback p.1 p.2)
      (encPair (Edge.encoding (encPi (encPi encBool))) encUnary)
      (encList (Edge.encoding (encPi encA))) := by
  have hproj₁ : ComputableInPolyTime
      (fun R : α → α → Bool => fun p : α × α => (repair pairs fallback R p).1)
      (encPi (encPi encBool)) (encPi encA) := .of_finite _
  have hproj₂ : ComputableInPolyTime
      (fun R : α → α → Bool => fun p : α × α => (repair pairs fallback R p).2)
      (encPi (encPi encBool)) (encPi encA) := .of_finite _
  have hleft : ComputableInPolyTime
      (fun p : Edge (α → α → Bool) × ℕ => p.1)
      (encPair (Edge.encoding (encPi (encPi encBool))) encUnary)
      (Edge.encoding (encPi (encPi encBool))) := .fst _ _
  have hidx : ComputableInPolyTime
      (fun p : Edge (α → α → Bool) × ℕ => p.2)
      (encPair (Edge.encoding (encPi (encPi encBool))) encUnary) encUnary := .snd _ _
  have hb : ComputableInPolyTime
      (fun p : Edge (α → α → Bool) × ℕ => block pairs fallback p.1 p.2)
      (encPair (Edge.encoding (encPi (encPi encBool))) encUnary)
      (encList (Edge.encoding (encPi encA))) := by
    unfold block
    exact (Edge.isPolyTime_mk hidx (Edge.isPolyTime_src hleft)
      (hproj₁.comp (Edge.isPolyTime_constraint hleft))).cons'
        ((Edge.isPolyTime_mk hidx (Edge.isPolyTime_dst hleft)
          (hproj₂.comp (Edge.isPolyTime_constraint hleft))).cons' (.const []))
  exact hb

omit [DecidableEq α] [Fintype α] in
private theorem zipIdx_edges_eq (g : Graph (α → α → Bool)) : g.edges.zipIdx =
    (List.range g.edges.length).map fun i =>
      (g.edges.getD i ⟨0, 0, fun _ _ => false⟩, i) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hi'' : i < g.edges.length := by simpa only [List.length_zipIdx] using hi
  simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'', Option.getD_some, Nat.zero_add]

omit [DecidableEq α] in
private theorem isPolyTime_incidence (pairs : List (α × α)) (fallback : α × α)
    (encA : α ↪ List Bool) :
    ComputableInPolyTime (incidence pairs fallback)
      (Graph.encoding (encPi (encPi encBool))) (Graph.encoding (encPi encA)) := by
  have hb := isPolyTime_block pairs fallback encA
  have hget : ComputableInPolyTime
      (fun p : Graph (α → α → Bool) × ℕ =>
        p.1.edges.getD p.2 ⟨0, 0, fun _ _ => false⟩)
      (encPair (Graph.encoding (encPi (encPi encBool))) encUnary)
      (Edge.encoding (encPi (encPi encBool))) :=
    Graph.isPolyTime_edgeAt (.fst _ _) (.snd _ _) (fun _ _ => false)
  have hlen : ComputableInPolyTime
      (fun g : Graph (α → α → Bool) => g.edges.length)
      (Graph.encoding (encPi (encPi encBool))) encUnary :=
    (ComputableInPolyTime.length_list (Edge.encoding (encPi (encPi encBool)))).comp
      (Graph.isPolyTime_edges ComputableInPolyTime.id')
  have hrange := ComputableInPolyTime.range.comp hlen
  have hindex : ComputableInPolyTime
      (fun p : Graph (α → α → Bool) × ℕ => p.2)
      (encPair (Graph.encoding (encPi (encPi encBool))) encUnary) encUnary := .snd _ _
  have hcomp := hb.comp (hget.prod hindex)
  have hcall : ComputableInPolyTime
      (fun p : Graph (α → α → Bool) × ℕ =>
        block pairs fallback (p.1.edges.getD p.2 ⟨0, 0, fun _ _ => false⟩) p.2)
      (encPair (Graph.encoding (encPi (encPi encBool))) encUnary)
      (encList (Edge.encoding (encPi encA))) := by
    simpa only [Function.comp_def] using hcomp
  have hedges := ComputableInPolyTime.flatMapWithInput
    (f := fun (g : Graph (α → α → Bool)) i =>
      block pairs fallback (g.edges.getD i ⟨0, 0, fun _ _ => false⟩) i) hrange hcall
  have hvertices : ComputableInPolyTime
      (fun g : Graph (α → α → Bool) => g.vertices + g.edges.length)
      (Graph.encoding (encPi (encPi encBool))) encUnary :=
    ComputableInPolyTime.unary_add'
      (Graph.isPolyTime_vertices (ComputableInPolyTime.id'
        (encIn := Graph.encoding (encPi (encPi encBool))))) hlen
  unfold incidence
  simp_rw [zipIdx_edges_eq, List.flatMap_map]
  exact Graph.isPolyTime_mk hvertices hedges

omit [DecidableEq α] in
/-- The incidence reduction is polynomial-time for every fixed finite alphabet and fixed pair
list. Unary endpoints, the input edge list and the complete finite projection tables are
charged under the existing graph encodings. -/
@[fun_prop]
theorem isPolyTime_reduce (pairs : List (α × α)) (a b : α) (encA : α ↪ List Bool) :
    ComputableInPolyTime (reduce pairs a b)
      (Graph.encoding (encPi (encPi encBool))) (Graph.encoding (encPi encA)) := by
  have htest : ComputableInPolyTime
      (fun R : α → α → Bool => !(pairs.any fun p => R p.1 p.2))
      (encPi (encPi encBool)) encBool := .of_finite _
  have hinc := isPolyTime_incidence pairs (a, a) encA
  unfold reduce
  fun_prop

end Runtime

end Cslib.PCP.Encoded.LabelCoverIncidence

namespace Cslib.Complexity

open Cslib.PCP Cslib.PCP.Encoded Turing.MultiTapeTM

/-- Constant-gap binary CSP reduces to total-projection Label Cover, preserving perfect
completeness and losing a factor of at most two in unsatisfied fraction. -/
theorem polyTimeReducible_GapTwoCSP_GapLabelCover {α : Type} [Fintype α] [DecidableEq α]
    (pairs : List (α × α)) (hpairs : ∀ p, p ∈ pairs) (a b : α) (hab : a ≠ b)
    (encA : α ↪ List Bool) (s : ℝ) :
    PromiseProblem.PolyTimeReducible (Graph.encoding (encPi (encPi encBool)))
      (Graph.encoding (encPi encA)) (GapTwoCSP α s)
      (GapLabelCover (α × α) α 1 ((1 + s) / 2)) := by
  let : Nonempty α := ⟨a⟩
  refine ⟨LabelCoverIncidence.reduce pairs a b,
    LabelCoverIncidence.isPolyTime_reduce pairs a b encA, ?_, ?_⟩
  · intro g hg
    have hs := LabelCoverIncidence.satisfiable_reduce pairs hpairs a b
      (mem_yes_GapTwoCSP.mp hg)
    rw [GapLabelCover, PromiseProblem.mem_yes_gapMax,
      (ConstraintGraph.unsatVal_eq_zero_iff _).mpr hs]
    norm_num
  · intro g hg
    simp only [GapTwoCSP, PromiseProblem.mem_no_gapMax] at hg
    simp only [GapLabelCover, PromiseProblem.mem_no_gapMax]
    have hgap := LabelCoverIncidence.half_unsatVal_le_reduce pairs a b hab g
    constructor <;> linarith [hg.1, hg.2]

private def dinurAlphabet : List (Bool × (Fin 6 → Bool)) :=
  (Cslib.BitString.enum 6).flatMap fun w => [(false, w), (true, w)]

private theorem mem_dinurAlphabet (p : Bool × (Fin 6 → Bool)) : p ∈ dinurAlphabet := by
  rcases p with ⟨b, w⟩
  cases b <;> simp [dinurAlphabet]

private def dinurPairs : List ((Bool × (Fin 6 → Bool)) × (Bool × (Fin 6 → Bool))) :=
  dinurAlphabet.flatMap fun a => dinurAlphabet.map fun b => (a, b)

private theorem mem_dinurPairs (p : (Bool × (Fin 6 → Bool)) × (Bool × (Fin 6 → Bool))) :
    p ∈ dinurPairs := by
  exact List.mem_flatMap.mpr ⟨p.1, mem_dinurAlphabet _, List.mem_map.mpr
    ⟨p.2, mem_dinurAlphabet _, rfl⟩⟩

/-- Label Cover with left alphabet of `128²` symbols and right alphabet of `128` symbols is
NP-hard at the constant soundness `1 - 2⁻⁶²`. Arbitrarily small soundness still needs repetition. -/
theorem GapLabelCover_npHard :
    PromiseProblem.NPHard
      (Graph.encoding (encPi (encPair encBool (encPi encBool))))
      (GapLabelCover ((Bool × (Fin 6 → Bool)) × (Bool × (Fin 6 → Bool)))
        (Bool × (Fin 6 → Bool)) 1 (1 - 1 / 2 ^ 62)) := by
  have hred := polyTimeReducible_GapTwoCSP_GapLabelCover dinurPairs mem_dinurPairs
    (false, fun _ : Fin 6 => false) (true, fun _ : Fin 6 => false) (by decide)
    (encPair encBool (encPi encBool)) (1 - 1 / 2 ^ 61)
  have hconst : (1 + (1 - 1 / 2 ^ 61) : ℝ) / 2 = 1 - 1 / 2 ^ 62 := by norm_num
  rw [hconst] at hred
  exact GapTwoCSP_npHard.trans hred

end Cslib.Complexity
