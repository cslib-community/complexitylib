/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.IndependentDomination
import all CslibFrontier.Computability.PolyTime.CNF.IndependentDomination
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.PerfectMatchingCut

/-!
# Actual encoded perfect matching cut construction

Enumerate distinct neighbor pairs for the upper constraints and write both signed neighborhood
conditions at every original vertex. This is [ChenJiangZhu2027], Proposition D.2 (PDF p. 34).
No cut, matching, auxiliary assignment or constructor/runtime conclusion is supplied as advice.

## Main definitions

* `upper`: actual opposite-neighbor upper clauses, with binary literal references.
* `conditions`: the two actual singleton-term neighborhood predicates at each vertex.
* `build`: original matrix to the generic DNF input.
* `run`: direct empty rejection, otherwise execution of the constructed input.

## Main results

* `build_polytime`: actual encoded construction, including all lookups and writes.
* `finite_semantics`: exact conventional perfect-matching-cut correspondence on nonempty graphs.
* `query_count`, `query_budget`: two actual width-three queries with the source cubic budget.
* `plan_count`: exact nonempty labeled-cut count; `run` rejects empty inputs directly.
-/

public section

namespace Cslib.Logic.PL.PerfectMatchingCut

open Turing.MultiTapeTM IndependentDomination

/-- Distinct neighbor pairs write both source clauses; duplicates across pair order are safe. -/
@[expose] def upper (x : Input) : CNF ℕ :=
  (List.range (order x)).flatMap fun u => (List.range (order x)).flatMap fun a =>
    (List.range (order x)).flatMap fun b =>
      if decide (a ≠ b) && adjacent x u a && adjacent x u b then
        [[(u, true), (a, false), (b, false)], [(u, false), (a, true), (b, true)]] else []

/-- Both signed neighborhood tests; the canonical input graph is undirected. -/
@[expose] def conditions (x : Input) : List (DNF ℕ) :=
  (List.range (order x)).flatMap fun u =>
    let ns := (List.range (order x)).filter (adjacent x u)
    [[[(u, true)]] ++ ns.map (fun v => [(v, true)]),
      [[(u, false)]] ++ ns.map (fun v => [(v, false)])]

/-- The actual original-matrix to generic DNF constructor, with no auxiliary variables. -/
@[expose] def build (x : Input) : TwoBoundary.BinaryFrontend.Input :=
  (order x, upper x, conditions x)

/-- Actual empty-graph test, before writing graph constraints or invoking the counter. -/
@[expose] def isEmpty (x : Input) : Bool := decide (order x = 0)

/-- Empty graphs have no partition into two nonempty sides and return zero directly. -/
@[expose] def run (counter : TwoBoundary.BinaryFrontend.Input → ℕ) (x : Input) : ℕ :=
  if isEmpty x then 0 else counter (build x)

private theorem upper_polytime : ComputableInPolyTime upper encInput VCOne.encSignedCNF := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  unfold upper VCOne.encSignedCNF
  apply ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hn)
  apply ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.range.comp (hn.comp (ComputableInPolyTime.fst _ _)))
  apply ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.range.comp (hn.comp ((ComputableInPolyTime.fst _ _).comp
      (ComputableInPolyTime.fst _ _))))
  let ei := encPair (encPair (encPair encInput encUnary) encUnary) encUnary
  have hau := IndependentDomination.adjacent_polytime.comp (show ComputableInPolyTime
    (fun p : ((Input × ℕ) × ℕ) × ℕ => (p.1.1.1, p.1.1.2, p.1.2)) ei
    (encPair encInput (encPair encUnary encUnary)) from by unfold ei; fun_prop)
  have hbu := IndependentDomination.adjacent_polytime.comp (show ComputableInPolyTime
    (fun p : ((Input × ℕ) × ℕ) × ℕ => (p.1.1.1, p.1.1.2, p.2)) ei
    (encPair encInput (encPair encUnary encUnary)) from by unfold ei; fun_prop)
  have hne : ComputableInPolyTime (fun p : ((Input × ℕ) × ℕ) × ℕ => decide (p.1.2 ≠ p.2))
      ei encBool := by unfold ei; fun_prop
  have hu : ComputableInPolyTime (fun p : ((Input × ℕ) × ℕ) × ℕ => p.1.1.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have ha : ComputableInPolyTime (fun p : ((Input × ℕ) × ℕ) × ℕ => p.1.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have hb : ComputableInPolyTime (fun p : ((Input × ℕ) × ℕ) × ℕ => p.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have htest : ComputableInPolyTime
      (fun p : ((Input × ℕ) × ℕ) × ℕ => decide (p.1.2 ≠ p.2) &&
        adjacent p.1.1.1 p.1.1.2 p.1.2 && adjacent p.1.1.1 p.1.1.2 p.2) ei encBool := by fun_prop
  have hbody : ComputableInPolyTime (fun p : ((Input × ℕ) × ℕ) × ℕ =>
      [[(p.1.1.2, true), (p.1.2, false), (p.2, false)],
        [(p.1.1.2, false), (p.1.2, true), (p.2, true)]]) ei
      (encList (encList (encPair encNat encBool))) := by fun_prop
  exact (htest.ite' hbody (.const [])).of_enc_eq fun _ => rfl

private theorem conditions_polytime : ComputableInPolyTime conditions encInput
    (encList VCOne.encSignedCNF) := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  let ei := encPair encInput encUnary
  have hns : ComputableInPolyTime (fun p : Input × ℕ =>
      (List.range (order p.1)).filter (adjacent p.1 p.2)) ei (encList encUnary) := by
    apply ComputableInPolyTime.filterWithInput
      (ComputableInPolyTime.range.comp (hn.comp (ComputableInPolyTime.fst _ _)))
    exact IndependentDomination.adjacent_polytime.comp (show ComputableInPolyTime
      (fun p : (Input × ℕ) × ℕ => (p.1.1, p.1.2, p.2))
        (encPair ei encUnary) (encPair encInput (encPair encUnary encUnary)) from by
          unfold ei; fun_prop)
  have hlit (β : Bool) : ComputableInPolyTime (fun v : ℕ => [(v, β)]) encUnary
      (encList (encPair encNat encBool)) := by
    have h := ComputableInPolyTime.unary_to_binary
    fun_prop
  have hpos : ComputableInPolyTime (fun p : Input × ℕ =>
      [[(p.2, true)]] ++ ((List.range (order p.1)).filter (adjacent p.1 p.2)).map
        (fun v => [(v, true)])) ei VCOne.encSignedCNF := by
    apply ComputableInPolyTime.listAppend' ?_ ((hlit true).map.comp hns)
    have hu : ComputableInPolyTime (fun p : Input × ℕ => p.2) ei encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
    fun_prop
  have hneg : ComputableInPolyTime (fun p : Input × ℕ =>
      [[(p.2, false)]] ++ ((List.range (order p.1)).filter (adjacent p.1 p.2)).map
        (fun v => [(v, false)])) ei VCOne.encSignedCNF := by
    apply ComputableInPolyTime.listAppend' ?_ ((hlit false).map.comp hns)
    have hu : ComputableInPolyTime (fun p : Input × ℕ => p.2) ei encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
    fun_prop
  have hu : ComputableInPolyTime (fun p : Input × ℕ => p.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold ei; fun_prop)
  have hbody : ComputableInPolyTime (fun p : Input × ℕ =>
      [[[(p.2, true)]] ++ ((List.range (order p.1)).filter (adjacent p.1 p.2)).map
        (fun v => [(v, true)]),
      [[(p.2, false)]] ++ ((List.range (order p.1)).filter (adjacent p.1 p.2)).map
        (fun v => [(v, false)])]) ei (encList (encList (encList (encPair encNat encBool)))) :=
    ComputableInPolyTime.cons' hpos (ComputableInPolyTime.cons' hneg (.const []))
  exact ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hn) hbody

/-- Actual matrix tests, triple loops, binary indices and output writes are polynomial time. -/
@[fun_prop] theorem build_polytime : ComputableInPolyTime build encInput
    TwoBoundary.BinaryFrontend.encInput := by
  have hn : ComputableInPolyTime order encInput encUnary := by unfold order encInput; fun_prop
  exact hn.prod (upper_polytime.prod conditions_polytime)

/-- The actual empty dispatch test has polynomial binary resources. -/
@[fun_prop] theorem isEmpty_polytime : ComputableInPolyTime isEmpty encInput encBool := by
  unfold isEmpty order encInput
  fun_prop

/-- Finite original-column presentation of the actual upper clauses. -/
@[expose] def finiteUpper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : CNF (Fin n) :=
  (List.finRange n).flatMap fun u => (List.finRange n).flatMap fun a =>
    (List.finRange n).flatMap fun b =>
      if a ≠ b ∧ G.Adj u a ∧ G.Adj u b then
        [[(u, true), (a, false), (b, false)], [(u, false), (a, true), (b, true)]] else []

/-- The two finite signed-neighborhood conditions at every original vertex. -/
@[expose] def finiteConditions {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    List (DNF (Fin n)) :=
  (List.finRange n).flatMap fun u =>
    let ns := (List.finRange n).filter (fun v => decide (G.Adj u v))
    [[[(u, true)]] ++ ns.map (fun v => [(v, true)]),
      [[(u, false)]] ++ ns.map (fun v => [(v, false)])]

/-- The actual encoded writer agrees with the finite original-side formulas. -/
theorem build_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    build (ofGraph G) =
      TwoBoundary.BinaryFrontend.ofFinite (finiteUpper G) (finiteConditions G) := by
  have hn : order (ofGraph G) = n := rfl
  simp only [build, upper, conditions, hn, ← List.map_coe_finRange_eq_range,
    List.flatMap_map, TwoBoundary.BinaryFrontend.ofFinite,
    CNF.relabel, finiteUpper, finiteConditions, List.map_flatMap]
  apply congrArg (fun z : CNF ℕ × List (DNF ℕ) => (n, z))
  apply Prod.ext <;> dsimp only
  · congr 1
    funext u
    congr 1
    funext a
    congr 1
    funext b
    simp only [IndependentDomination.adjacent_ofGraph, Bool.and_eq_true, decide_eq_true_eq,
      ne_eq, Fin.val_inj, and_assoc]
    split_ifs <;> simp [Clause.relabel]
  · congr 1
    funext u
    simp only [CNF.relabel, List.filter_map, List.map_map, Function.comp_def,
      IndependentDomination.adjacent_ofGraph, List.map_cons, List.map_nil, List.map_append,
      Clause.relabel]
    rfl

private theorem upper_pair_eval {V : Type*} (σ : V → Bool) (u a b : V) :
    CNF.eval σ [[(u, true), (a, false), (b, false)],
      [(u, false), (a, true), (b, true)]] = true ↔ ¬(σ u ≠ σ a ∧ σ u ≠ σ b) := by
  cases hu : σ u <;> cases ha : σ a <;> cases hb : σ b <;>
    simp [CNF.eval, Clause.eval, Literal.eval, hu, ha, hb]

/-- The actual upper constraints allow at most one opposite-side neighbor at every vertex. -/
theorem finiteUpper_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) :
    (finiteUpper G).eval σ = true ↔
      ∀ u a b, a ≠ b → G.Adj u a → G.Adj u b → ¬(σ u ≠ σ a ∧ σ u ≠ σ b) := by
  have he (u a b : Fin n) :
      CNF.eval σ (if a ≠ b ∧ G.Adj u a ∧ G.Adj u b then
        [[(u, true), (a, false), (b, false)], [(u, false), (a, true), (b, true)]] else []) = true ↔
        (a ≠ b → G.Adj u a → G.Adj u b → ¬(σ u ≠ σ a ∧ σ u ≠ σ b)) := by
    split_ifs with h
    · rw [upper_pair_eval]
      tauto
    · simp only [CNF.eval_nil, true_iff]
      intro ha hu hv
      exact False.elim (h ⟨ha, hu, hv⟩)
  simp only [finiteUpper, CNF.eval_flatMap_eq_true_iff, List.mem_finRange, forall_true_left, he]

private theorem neighborhood_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) (u : Fin n) (β : Bool) :
    DNF.eval σ ([[(u, β)]] ++ ((List.finRange n).filter (fun v => decide (G.Adj u v))).map
      (fun v => [(v, β)])) = true ↔ σ u = β ∨ ∃ v, G.Adj u v ∧ σ v = β := by
  cases β <;> simp [DNF.eval_eq_true_iff, Term.eval, Literal.eval]

/-- The two actual neighborhood predicates force an opposite-side neighbor, for either side bit. -/
theorem finiteConditions_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Fin n → Bool) :
    (∀ p ∈ finiteConditions G, DNF.eval σ p = true) ↔
      ∀ u, (σ u = true ∨ ∃ v, G.Adj u v ∧ σ v = true) ∧
        (σ u = false ∨ ∃ v, G.Adj u v ∧ σ v = false) := by
  constructor
  · intro h u
    have ht := h _ (List.mem_flatMap.mpr ⟨u, List.mem_finRange u, List.mem_cons_self⟩)
    have hf := h _ (List.mem_flatMap.mpr ⟨u, List.mem_finRange u,
      List.mem_cons_of_mem _ (List.mem_cons_self)⟩)
    exact ⟨(neighborhood_eval G σ u true).mp ht, (neighborhood_eval G σ u false).mp hf⟩
  · intro h p hp
    obtain ⟨u, _, hp⟩ := List.mem_flatMap.mp hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (neighborhood_eval G σ u true).mpr (h u).1
    · have he := List.mem_singleton.mp hp
      subst p
      exact (neighborhood_eval G σ u false).mpr (h u).2

/-- On nonempty graphs the actual formulas count exactly the labeled perfect matching cuts.
The conventional perfect matching is the entire crossing subgraph, not an arbitrary submatching. -/
theorem finite_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 0 < n) (σ : Fin n → Bool) :
    (finiteUpper G).eval σ = true ∧ (∀ p ∈ finiteConditions G, DNF.eval σ p = true) ↔
      G.IsPerfectMatchingCut σ := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [SimpleGraph.isPerfectMatchingCut_iff, finiteUpper_eval, finiteConditions_eval]
  constructor
  · rintro ⟨hu, hl⟩ u
    have hex : ∃ v, G.Adj u v ∧ σ u ≠ σ v := by
      cases hx : σ u with
      | false =>
        rcases (hl u).1 with h | ⟨v, ha, hv⟩
        · simp_all
        · exact ⟨v, ha, by simp [hv]⟩
      | true =>
        rcases (hl u).2 with h | ⟨v, ha, hv⟩
        · simp_all
        · exact ⟨v, ha, by simp [hv]⟩
    obtain ⟨v, ha, hv⟩ := hex
    refine ⟨v, ⟨ha, hv⟩, fun w hw => ?_⟩
    by_contra hne
    exact hu u w v hne hw.1 ha ⟨hw.2, hv⟩
  · intro h
    constructor
    · intro u a b hab hua hub hop
      exact hab ((h u).unique ⟨hua, hop.1⟩ ⟨hub, hop.2⟩)
    · intro u
      obtain ⟨v, ha, hv⟩ := h u
      constructor
      · cases hx : σ u with
        | true => exact Or.inl rfl
        | false =>
          refine Or.inr ⟨v, ha.1, ?_⟩
          cases hy : σ v <;> simp_all
      · cases hx : σ u with
        | false => exact Or.inl rfl
        | true =>
          refine Or.inr ⟨v, ha.1, ?_⟩
          cases hy : σ v <;> simp_all

/-- Width three in the bounded part and singleton terms in every coverage condition. -/
theorem widths {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∀ c ∈ finiteUpper G, c.length ≤ 3) ∧
      (∀ p ∈ finiteConditions G, ∀ t ∈ p, t.length ≤ 1) := by
  constructor
  · intro c hc
    obtain ⟨u, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨a, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨b, _, hc⟩ := List.mem_flatMap.mp hc
    split_ifs at hc
    · rcases List.mem_cons.mp hc with rfl | hc
      · simp
      · have he := List.mem_singleton.mp hc
        subst c
        simp
    · simp at hc
  · have ht (u : Fin n) (β : Bool) (t : Term (Fin n))
        (ht : t ∈ [[(u, β)]] ++ ((List.finRange n).filter (fun v => decide (G.Adj u v))).map
          (fun v => [(v, β)])) : t.length ≤ 1 := by
      rcases List.mem_append.mp ht with ht | ht
      · have he := List.mem_singleton.mp ht
        subst t
        simp
      · obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
        simp
    intro p hp t hmem
    obtain ⟨u, _, hp⟩ := List.mem_flatMap.mp hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ht u true t hmem
    · have he := List.mem_singleton.mp hp
      subst p
      exact ht u false t hmem

/-- There are exactly two signed conditions per original vertex. -/
theorem finiteConditions_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (finiteConditions G).length = 2 * n := by
  simp [finiteConditions, List.length_flatMap, List.finRange, List.map_ofFn,
    List.sum_ofFn, Nat.mul_comm]

/-- Ordered-pair enumeration has cubic clause volume and quadratic total neighborhood volume. -/
theorem volumes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (finiteUpper G).length ≤ 2 * n ^ 3 ∧
      ((finiteConditions G).map List.length).sum ≤ 2 * n * (n + 1) := by
  constructor
  · simp only [finiteUpper, List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn]
    calc
      _ ≤ ∑ _u : Fin n, ∑ _a : Fin n, ∑ _b : Fin n, 2 := by
        apply Finset.sum_le_sum
        intro u _
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        dsimp only [Function.comp_def]
        split_ifs <;> simp
      _ = _ := by simp; ring
  · simp only [finiteConditions, List.flatMap_def, List.map_flatten, List.sum_flatten,
      Function.comp_def, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_append, List.length_cons, List.length_nil, List.length_map, Nat.add_zero,
      List.finRange, List.map_ofFn, List.sum_ofFn]
    calc
      _ ≤ ∑ _u : Fin n, 2 * (n + 1) := by
        apply Finset.sum_le_sum
        intro u _
        have hl := List.length_filter_le (fun v => decide (G.Adj u v))
          (List.ofFn (fun i : Fin n => i))
        simp only [List.length_ofFn] at hl
        omega
      _ = _ := by simp; ring

/-- Nonempty graphs actually emit two ordinary boundary queries. Empty inputs bypass this writer. -/
theorem query_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 1 ≤ n) :
    (TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G)))).length = 2 := by
  rw [TwoBoundary.BinaryFrontend.compile_query_count, build_ofGraph]
  have hl := finiteConditions_length G
  have he : (finiteConditions G).isEmpty ≠ true := by
    intro h
    have hz := List.isEmpty_iff_length_eq_zero.mp h
    omega
  simp only [TwoBoundary.BinaryFrontend.conditions, TwoBoundary.BinaryFrontend.ofFinite,
    List.isEmpty_map, he, Bool.false_eq_true, ↓reduceIte]

/-- Positive-vertex queries have the source's `3v-1` variables, width three and cubic size. -/
theorem query_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 1 ≤ n)
    (N : ℕ) (q : CNF ℕ) (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G)))) :
    N = 3 * n - 1 ∧ q.length ≤ 10 * n ^ 3 ∧
      ∀ c ∈ q, c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < N := by
  rw [build_ofGraph] at hq
  obtain ⟨hb, hp⟩ := widths G
  obtain ⟨hv, hm, hw⟩ := TwoBoundary.BinaryFrontend.compile_budget
    (finiteUpper G) (finiteConditions G) hb hp N q hq
  obtain ⟨hside, hterms⟩ := volumes G
  have hl := finiteConditions_length G
  have hn2 : n ≤ n ^ 2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right n hn
  have hn3 : n ^ 2 ≤ n ^ 3 := by
    calc n ^ 2 ≤ n ^ 2 * n := Nat.le_mul_of_pos_right _ hn
      _ = n ^ 3 := by ring
  refine ⟨?_, by nlinarith, by simpa using hw⟩
  split_ifs at hv with he
  · have hz := List.isEmpty_iff_length_eq_zero.mp he
    omega
  · omega

open Classical in
/-- Exact labeled perfect-matching-cut count of the constructed plan, on nonempty graphs. -/
theorem plan_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 0 < n) :
    TwoBoundary.BinaryFrontend.value (TwoBoundary.BinaryFrontend.compile (build (ofGraph G))) =
      Fintype.card {side : Fin n → Bool // G.IsPerfectMatchingCut side} := by
  rw [build_ofGraph, TwoBoundary.BinaryFrontend.compile_count]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (finite_semantics G hn))

end Cslib.Logic.PL.PerfectMatchingCut
