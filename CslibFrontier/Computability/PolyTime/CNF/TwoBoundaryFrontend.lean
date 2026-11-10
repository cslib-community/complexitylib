/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.WeightedQuery
public import CslibFrontier.Logics.Propositional.CNF.VCOneElimination
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Executable generic bounded-term DNF frontend

Theorem 1.1 of [ChenJiangZhu2027], PDF pp. 4–5, accepts arbitrary explicit term lists.
No VC-one promise or table expansion is needed or implied. The actual writer uses binary literal
labels and a unary declaration, and substitutes path endpoints while writing clauses. With no
conditions it emits one ordinary query; otherwise it emits the two boundary queries.
-/

public section

namespace Cslib.Logic.PL.TwoBoundary.BinaryFrontend

open Turing.MultiTapeTM
open WeightedRow
open VCOne

/-- Original unary declaration, ordinary side formula, and explicit list of DNF conditions. -/
abbrev Input := ℕ × CNF ℕ × List (DNF ℕ)
/-- Access the original declaration without exposing tuple-layout details in clients. -/
@[expose] def declared : Input → ℕ | (n, _, _) => n
/-- Access the original side formula. -/
@[expose] def side : Input → CNF ℕ | (_, B, _) => B
/-- Access the original explicit DNF conditions. -/
@[expose] def conditions : Input → List (DNF ℕ) | (_, _, P) => P
/-- Literal labels are binary; list framing is explicit and the declaration is unary. -/
@[expose] def encInput : Input ↪ List Bool :=
  encPair encUnary (encPair encSignedCNF (encList encSignedCNF))
/-- One ordinary declared query or two ordinary queries sharing their declared variables. -/
abbrev Output := (ℕ × CNF ℕ) ⊕ (ℕ × CNF ℕ × CNF ℕ)
/-- Binary clauses and sum tags, with unary output declarations. -/
@[expose] def encOutput : Output ↪ List Bool :=
  encSum (encPair encUnary encSignedCNF)
    (encPair encUnary (encPair encSignedCNF encSignedCNF))

/-- Actual endpoint-substituted writing from the original term lists. Repeated/contradictory
literals and empty terms/conditions are preserved; there is no cube or powerset enumeration. -/
@[expose] def query (x : Input) (β : Bool) : CNF ℕ :=
  side x ++ (List.range (conditions x).length).flatMap fun j =>
    ((conditions x).getD j []).flatMap
      (BinaryQuery.termClauses (declared x) ((conditions x).length - 1) β j)

/-- Compute the source's one-query/no-condition or two-boundary branch from original data. -/
@[expose] def compile (x : Input) : Output :=
  if (conditions x).isEmpty then .inl (declared x, side x)
  else .inr (declared x + (conditions x).length - 1, query x false, query x true)

private theorem term_polytime {α : Type} {enc : α ↪ List Bool}
    {n h j : α → ℕ} {β : α → Bool} {t : α → Term ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hh : ComputableInPolyTime h enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary) (hβ : ComputableInPolyTime β enc encBool)
    (ht : ComputableInPolyTime t enc (encList (encPair encNat encBool))) :
    ComputableInPolyTime (fun x => BinaryQuery.termClauses
      (n x) (h x) (β x) (j x) (t x)) enc encSignedCNF := by
  have hnB := ComputableInPolyTime.unary_to_binary.comp hn
  have ha : ComputableInPolyTime (fun x => n x + j x - 1) enc encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hnext : ComputableInPolyTime (fun x => n x + j x) enc encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hneg : ComputableInPolyTime
      (fun x => (t x).map fun (i, s) => (i, !s)) enc
      (encList (encPair encNat encBool)) := by fun_prop
  have hz : ComputableInPolyTime (fun x => decide (j x = 0)) enc encBool := by fun_prop
  have hh0 : ComputableInPolyTime (fun x => decide (h x = 0)) enc encBool := by fun_prop
  have heq : ComputableInPolyTime (fun x => decide (j x = h x)) enc encBool := by fun_prop
  have hfirst : ComputableInPolyTime
      (fun x => [(t x).map (fun (i, s) => (i, !s)) ++ [(n x, false)]]) enc encSignedCNF := by
    unfold encSignedCNF; fun_prop
  have hlast : ComputableInPolyTime
      (fun x => [(t x).map (fun (i, s) => (i, !s)) ++ [(n x + j x - 1, β x)]])
      enc encSignedCNF := by unfold encSignedCNF; fun_prop
  have hinner : ComputableInPolyTime (fun x =>
      [(t x).map (fun (i, s) => (i, !s)) ++ [(n x + j x - 1, false), (n x + j x, true)],
        (t x).map (fun (i, s) => (i, !s)) ++ [(n x + j x - 1, true), (n x + j x, false)]])
      enc encSignedCNF := by unfold encSignedCNF; fun_prop
  have hone : ComputableInPolyTime
      (fun x => [(t x).map fun (i, s) => (i, !s)]) enc encSignedCNF := by
    unfold encSignedCNF; fun_prop
  simpa only [BinaryQuery.termClauses, decide_eq_true_eq] using
    hz.ite' (hh0.ite' (hβ.ite' hone (.const [])) hfirst) (heq.ite' hlast hinner)

/-- Polynomial binary construction time for every raw side/term list, charging all writes. -/
@[fun_prop] theorem query_polytime (β : Bool) :
    ComputableInPolyTime (fun x => query x β) encInput encSignedCNF := by
  have hn : ComputableInPolyTime declared encInput encUnary := by
    unfold declared encInput; fun_prop
  have hB : ComputableInPolyTime side encInput encSignedCNF := by
    unfold side encInput; fun_prop
  have hP : ComputableInPolyTime conditions encInput (encList encSignedCNF) := by
    unfold conditions encInput; fun_prop
  have hl := (ComputableInPolyTime.length_list encSignedCNF).comp hP
  have hm := ComputableInPolyTime.unary_sub.comp (hl.prod (.const 1))
  let ei := encPair encInput encUnary
  have hp := ComputableInPolyTime.fst encInput encUnary
  have hj := ComputableInPolyTime.snd encInput encUnary
  have ht : ComputableInPolyTime
      (fun p : Input × ℕ => (conditions p.1).getD p.2 []) ei encSignedCNF :=
    ComputableInPolyTime.listGetDWithInput (hP.comp hp) hj []
  have hpar := ComputableInPolyTime.fst ei (encList (encPair encNat encBool))
  have hctx := hp.comp hpar
  have hw := term_polytime (hn.comp hctx) (hm.comp hctx) (hj.comp hpar) (.const β)
    (ComputableInPolyTime.snd ei (encList (encPair encNat encBool)))
  unfold query
  exact ComputableInPolyTime.listAppend' hB
    (ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hl)
      (ComputableInPolyTime.flatMapWithInput ht hw))

/-- The entire actual one/two-query dispatch has polynomial binary resources. -/
@[fun_prop] theorem compile_polytime : ComputableInPolyTime compile encInput encOutput := by
  have hn : ComputableInPolyTime declared encInput encUnary := by
    unfold declared encInput; fun_prop
  have hB : ComputableInPolyTime side encInput encSignedCNF := by
    unfold side encInput; fun_prop
  have hP : ComputableInPolyTime conditions encInput (encList encSignedCNF) := by
    unfold conditions encInput; fun_prop
  have hlen := (ComputableInPolyTime.length_list encSignedCNF).comp hP
  have hN := ComputableInPolyTime.unary_sub.comp
    ((ComputableInPolyTime.unary_add.comp (hn.prod hlen)).prod (.const 1))
  have hs := (ComputableInPolyTime.sumInl (encPair encUnary encSignedCNF)
    (encPair encUnary (encPair encSignedCNF encSignedCNF))).comp (hn.prod hB)
  have hq := (ComputableInPolyTime.sumInr (encPair encUnary encSignedCNF)
    (encPair encUnary (encPair encSignedCNF encSignedCNF))).comp
      (hN.prod ((query_polytime false).prod (query_polytime true)))
  have hz : ComputableInPolyTime (fun x => (conditions x).isEmpty) encInput encBool := by
    unfold conditions encInput; fun_prop
  exact (hz.ite' hs hq).of_enc_eq fun _ => rfl

end Cslib.Logic.PL.TwoBoundary.BinaryFrontend
