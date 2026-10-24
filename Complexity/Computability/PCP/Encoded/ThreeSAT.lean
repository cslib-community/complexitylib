/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Basic
public import Complexity.Computability.PCP.ThreeSAT
public import Complexity.Logics.Propositional.CNF.Compact
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Tactic.PolyTime

/-!
# Executable constraint graphs for 3-SAT

First-occurrence renaming bounds every variable index by the number of literal occurrences.
Variable vertices use even numbers and clause vertices use odd numbers. Each clause contributes
three ordered edges, including the self-loops for missing literal positions. Constraints are
complete Boolean tables on the eight-symbol alphabet `Fin 3 → Bool`.

## Main definitions

* `Cslib.PCP.Encoded.Graph.ofCNF`: construct a graph from a compactly numbered formula.
* `Cslib.PCP.Encoded.Graph.ofCompactCNF`: compact arbitrary variable names and construct the graph.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_ofCompactCNF`: charge renaming, enumeration, and truth tables.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 22][AroraBarak09]
* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Cslib.Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- Check the first three literal positions against a clause label. -/
def clauseHolds (κ : Clause ℕ) (a : Fin 3 → Bool) : Bool :=
  (List.finRange 3).any fun q => κ[q.val]?.elim false (fun l => a q == l.2)

/-- The Boolean test agrees with the existing mathematical clause predicate. -/
private theorem clauseHolds_eq_true (κ : Clause ℕ) (a : Fin 3 → Bool) :
    clauseHolds κ a = true ↔ ConstraintGraph.ClauseHolds κ a := by
  simp only [clauseHolds, List.any_eq_true, List.mem_finRange, true_and,
    ConstraintGraph.ClauseHolds]
  apply exists_congr
  intro q
  cases κ[q.val]? <;> simp

/-- Construct one edge, computing its entire fixed-alphabet relation. -/
def cnfEdge (φ : CNF ℕ) (p : ℕ × Fin 3) :
    Edge ((Fin 3 → Bool) → (Fin 3 → Bool) → Bool) :=
  let κ := φ.getD p.1 []
  ⟨2 * p.1 + 1, κ[p.2.val]?.elim (2 * p.1 + 1) (fun l => 2 * l.1),
    fun a b => clauseHolds κ a && κ[p.2.val]?.elim true (fun _ => a p.2 == b 0)⟩

/-- Construct three edges per clause. `variableCount` bounds compact variable names;
it is used only for the declared vertex count, and correctness does not inspect a bound proof. -/
def ofCNF (variableCount : ℕ) (φ : CNF ℕ) :
    Graph ((Fin 3 → Bool) → (Fin 3 → Bool) → Bool) :=
  ⟨2 * (variableCount + φ.length),
    ((List.range φ.length).product (List.finRange 3)).map (cnfEdge φ)⟩

/-- Compact the original variable names before producing unary graph indices. -/
def ofCompactCNF {V : Type} [DecidableEq V] (φ : CNF V) :
    Graph ((Fin 3 → Bool) → (Fin 3 → Bool) → Bool) :=
  ofCNF φ.vars.length φ.compact

/-- Checking a clause label includes lookup of the literals at its three positions. -/
@[fun_prop]
theorem isPolyTime_clauseHolds :
    ComputableInPolyTime (fun p : Clause ℕ × (Fin 3 → Bool) => clauseHolds p.1 p.2)
      (encPair (encList (encPair encUnary encBool)) (encPi encBool)) encBool := by
  refine .of_tidy ?_
  unfold clauseHolds
  apply anyWithInput (encA := encFinEnum (Fin 3)) (by fun_prop)
  apply finite_cases (branch := fun (i : Fin 3) (p : (Clause ℕ × (Fin 3 → Bool)) × Fin 3) =>
    p.1.1[i.val]?.elim false (fun l => p.1.2 i == l.2)) (snd _ _)
  intro i
  apply optionElimWithInput (encB := encPair encUnary encBool) <;> fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- The per-edge program charges clause lookup, endpoints, and all 64 entries of its relation. -/
@[fun_prop]
theorem isPolyTime_cnfEdge :
    ComputableInPolyTime (fun p : CNF ℕ × (ℕ × Fin 3) => cnfEdge p.1 p.2)
      (encPair (encList (encList (encPair encUnary encBool)))
        (encPair encUnary (encFinEnum (Fin 3))))
      (Edge.encoding (encPi (encPi encBool))) := by
  refine .of_tidy ?_
  have hindex : ComputableTidilyInPolyTime (Fin.val (n := 3))
      (encFinEnum (Fin 3)) encUnary := .of_finite _
  have hclause : ComputableTidilyInPolyTime
      (fun p : CNF ℕ × (ℕ × Fin 3) => p.1.getD p.2.1 [])
      (encPair (encList (encList (encPair encUnary encBool)))
        (encPair encUnary (encFinEnum (Fin 3)))) (encList (encPair encUnary encBool)) := by
    fun_prop
  have hliteral := ComputableTidilyInPolyTime.getElem? (encA := encPair encUnary encBool)
    hclause (hindex.comp ((snd _ _).snd'))
  unfold cnfEdge
  refine ComputableInPolyTime.tidy
    (Edge.isPolyTime_mk (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)) (.of_tidy ?_))
  refine pi fun a => pi fun b => ?_
  have ha : ComputableTidilyInPolyTime a (encFinEnum (Fin 3)) encBool := .of_finite _
  fun_prop

/-- Constructing all edges and copying their constraints is polynomial-time. -/
@[fun_prop]
theorem isPolyTime_ofCNF :
    ComputableInPolyTime (fun p : ℕ × CNF ℕ => ofCNF p.1 p.2)
      (encPair encUnary (encList (encList (encPair encUnary encBool))))
      (encoding (encPi (encPi encBool))) := by
  have hdarts : ComputableInPolyTime
      (fun p : ℕ × CNF ℕ => (List.range p.2.length).product (List.finRange 3))
      (encPair encUnary (encList (encList (encPair encUnary encBool))))
      (encList (encPair encUnary (encFinEnum (Fin 3)))) := by
    unfold List.product
    fun_prop
  unfold ofCNF
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- The complete construction accepts any variable encoding and charges compact renaming. -/
@[fun_prop]
theorem isPolyTime_ofCompactCNF {V Input : Type} [DecidableEq V]
    {enc : V ↪ List Bool} {input : Input ↪ List Bool} {formula : Input → CNF V}
    (hformula : ComputableInPolyTime formula input
      (encList (encList (encPair enc encBool)))) :
    ComputableInPolyTime (fun x => ofCompactCNF (formula x))
      input (encoding (encPi (encPi encBool))) := by
  unfold ofCompactCNF
  polytime

/-- Even numbers name variables; odd numbers name clause positions. -/
def cnfVertexNumber {m : ℕ} : ℕ ⊕ Fin m → ℕ
  | .inl x => 2 * x
  | .inr j => 2 * j.val + 1

/-- The numbering separates all variable vertices and clause vertices. -/
theorem cnfVertexNumber_injective (m : ℕ) :
    Function.Injective (cnfVertexNumber (m := m)) := by
  intro v w h
  cases v with
  | inl x =>
    cases w with
    | inl y => simp only [cnfVertexNumber] at h; congr 1; lia
    | inr j => simp only [cnfVertexNumber] at h; lia
  | inr j =>
    cases w with
    | inl y => simp only [cnfVertexNumber] at h; lia
    | inr k => simp only [cnfVertexNumber] at h; congr 1; apply Fin.ext; lia

/-- Every clause contributes exactly three edges, including missing-position self-loops. -/
@[simp]
theorem length_edges_ofCNF (variableCount : ℕ) (φ : CNF ℕ) :
    (ofCNF variableCount φ).edges.length = φ.length * 3 := by
  simp [ofCNF, List.product, List.length_flatMap, List.sum_replicate]

/-- The concrete edge occurrences are indexed by clause and literal position. -/
def ofCNFEnumeration (variableCount : ℕ) (φ : CNF ℕ) :
    List.Enumeration (ofCNF variableCount φ).edges
      (fun p : Fin φ.length × Fin 3 => cnfEdge φ (p.1.val, p.2)) :=
  ((List.Enumeration.range φ.length).prod
    (List.Enumeration.ofNodup (List.finRange 3) (List.nodup_finRange 3)
      (fun _ => List.mem_finRange _))).map (cnfEdge φ)

/-- The executable graph is exactly the existing mathematical graph with concrete numbering. -/
theorem toGraph_ofCNF (variableCount : ℕ) (φ : CNF ℕ) :
    (ofCNF variableCount φ).toGraph id =
      ((ConstraintGraph.ofCNF φ).map cnfVertexNumber).comap
        (ofCNFEnumeration variableCount φ).equiv := by
  apply toGraph_eq_comap _ _ (ofCNFEnumeration variableCount φ)
  · intro p
    simp only [cnfEdge, ConstraintGraph.ofCNF, cnfVertexNumber]
  · intro p
    simp only [cnfEdge, ConstraintGraph.ofCNF]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Fin.isLt _), Option.getD_some]
    cases φ[p.1][p.2.val]? <;> rfl
  · intro p a b
    simp only [cnfEdge, ConstraintGraph.ofCNF, id_eq, Bool.and_eq_true, clauseHolds_eq_true]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Fin.isLt _), Option.getD_some]
    apply and_congr_right
    intro _
    cases φ[p.1][p.2.val]? <;> simp

/-- The exact graph interpretation retains the mathematical unsatisfied value. -/
theorem unsatVal_ofCNF (variableCount : ℕ) (φ : CNF ℕ) :
    ((ofCNF variableCount φ).toGraph id).unsatVal = (ConstraintGraph.ofCNF φ).unsatVal := by
  rw [toGraph_ofCNF, ConstraintGraph.unsatVal_comap_map_of_injective _
    (cnfVertexNumber_injective _)]

/-- For clauses of length at most three, the executable construction preserves satisfiability. -/
theorem satisfiable_ofCNF_iff (variableCount : ℕ) (φ : CNF ℕ)
    (h3 : ∀ c ∈ φ, c.length ≤ 3) :
    ((ofCNF variableCount φ).toGraph id).Satisfiable ↔ φ.Satisfiable := by
  rw [toGraph_ofCNF, ConstraintGraph.satisfiable_comap_map_iff _
    (cnfVertexNumber_injective _) (Equiv.surjective _)]
  exact ConstraintGraph.satisfiable_ofCNF_iff φ h3

/-- Bounded variable names ensure every generated endpoint lies in the declared vertex range. -/
private theorem wellFormed_ofCNF (variableCount : ℕ) (φ : CNF ℕ)
    (hvars : ∀ v ∈ φ.vars, v < variableCount) : (ofCNF variableCount φ).WellFormed := by
  intro e he
  obtain ⟨⟨j, q⟩, hp, rfl⟩ := List.mem_map.mp he
  have hj := List.mem_range.mp (List.mem_product.mp hp).1
  have hget : φ.getD j [] = φ[j] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  change 2 * j + 1 < 2 * (variableCount + φ.length) ∧
    ((φ.getD j [])[q.val]?.elim (2 * j + 1) (fun l => 2 * l.1)) <
      2 * (variableCount + φ.length)
  rw [hget]
  constructor
  · lia
  · cases hl : φ[j][q.val]? with
    | none => simp only [Option.elim_none]; lia
    | some l =>
      have hlt := hvars l.1
        (List.mem_map.mpr ⟨l, List.mem_flatten.mpr
          ⟨φ[j], List.getElem_mem _, List.mem_of_getElem? hl⟩, rfl⟩)
      simp only [Option.elim_some]
      lia

/-- The complete construction always produces well-formed numbered graphs. -/
theorem wellFormed_ofCompactCNF {V : Type} [DecidableEq V] (φ : CNF V) :
    (ofCompactCNF φ).WellFormed :=
  wellFormed_ofCNF φ.vars.length φ.compact (fun _ => CNF.mem_vars_compact_lt φ)

/-- There are two declared vertex slots per literal occurrence or clause position. -/
@[simp]
theorem vertices_ofCompactCNF {V : Type} [DecidableEq V] (φ : CNF V) :
    (ofCompactCNF φ).vertices = 2 * (φ.vars.length + φ.length) := by
  simp [ofCompactCNF, ofCNF]

/-- Compaction does not change the three edges contributed by each original clause. -/
@[simp]
theorem length_edges_ofCompactCNF {V : Type} [DecidableEq V] (φ : CNF V) :
    (ofCompactCNF φ).edges.length = φ.length * 3 := by
  simp [ofCompactCNF]

/-- The full construction accepts exactly the satisfiable formulas with at most three literals
per clause, including repeated variables and missing literal positions. -/
theorem satisfiable_ofCompactCNF_iff {V : Type} [DecidableEq V] (φ : CNF V)
    (h3 : ∀ c ∈ φ, c.length ≤ 3) :
    ((ofCompactCNF φ).toGraph id).Satisfiable ↔ φ.Satisfiable := by
  rw [ofCompactCNF, satisfiable_ofCNF_iff, CNF.satisfiable_compact]
  intro c hc
  obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hc
  exact (Clause.length_relabel _ κ).trans_le (h3 κ hκ)

/-- An unsatisfiable input supplies the inverse-polynomial starting gap for amplification. -/
theorem inv_edges_le_unsatVal_ofCompactCNF {V : Type} [DecidableEq V] (φ : CNF V)
    (h3 : ∀ c ∈ φ, c.length ≤ 3) (hφ : ¬ φ.Satisfiable) :
    (φ.length * 3 : ℝ)⁻¹ ≤ ((ofCompactCNF φ).toGraph id).unsatVal := by
  have h := ((ofCompactCNF φ).toGraph id).inv_card_le_unsatVal
    (fun hs => hφ ((satisfiable_ofCompactCNF_iff φ h3).mp hs))
  simpa only [Fintype.card_fin, length_edges_ofCompactCNF, Nat.cast_mul, Nat.cast_ofNat] using h

end Cslib.PCP.Encoded.Graph
