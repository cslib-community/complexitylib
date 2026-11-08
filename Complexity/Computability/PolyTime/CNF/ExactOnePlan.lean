/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.WeightedPlan
public import Complexity.Logics.Propositional.CNF.VCOneElimination
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Binary all-cases dispatch for signed exact-one rows with a side CNF

The original declaration, side formula and explicit signed equations determine every branch.
The declaration is unary; all literal labels, matrix integers and direct counts are binary.
No basis, candidate, query or runtime is supplied. Enumeration of assignments is confined to
zero/one declared bits. This is the dispatcher needed by [ChenJiangZhu2027], Theorem 6.3,
PDF pp. 20–21, and the signed/side-CNF form of Theorem 1.2 / Corollary 5.3.
-/

public section

namespace Cslib.Logic.PL.ExactOne.BinaryPlan

open Turing.MultiTapeTM
open Cslib.LinearSystem
open VCOne WeightedRow

/-- Original declaration, ordinary side CNF and occurrence-sensitive signed equations. -/
abbrev Input := ℕ × (CNF ℕ × CNF ℕ)
/-- Unary declaration and binary literal labels in both explicit formulas. -/
@[expose] def encInput : Input ↪ List Bool :=
  encPair encUnary (encPair encSignedCNF encSignedCNF)
/-- Reuse the tagged direct/two-query output type. -/
abbrev Output := WeightedRow.BinaryPlan.Output
/-- Output tags/declarations/counts and both queries are actually written, with binary labels. -/
@[expose] def encOutput : Output ↪ List Bool := encPlanPayload

/-- Binary finite-assignment evaluation of an ordinary side formula. -/
@[expose] def eval (B : CNF ℕ) (bits : List Bool) : Bool :=
  B.all fun c => c.any fun l => bits.getD l.1 false == l.2

/-- Binary finite-assignment evaluation of all original exact-one rows. -/
@[expose] def test (B E : CNF ℕ) (bits : List Bool) : Bool :=
  eval B bits && E.all fun c => c.countP (fun l => bits.getD l.1 false == l.2) == 1

/-- Scan the two constant assignments only when the declaration has at most one bit. -/
@[expose] def small (n : ℕ) (B E : CNF ℕ) : ℕ :=
  (if test B E (List.replicate n false) then 1 else 0) +
    if n = 0 then 0 else if test B E (List.replicate n true) then 1 else 0

/-- Read the computed common-denominator certificate as candidate bits, using integer equality. -/
@[expose] def candidate (n : ℕ) (E : CNF ℕ) : List Bool :=
  let (den, nums) := rectangularCertificate n (payloadRows n E) (payloadRhs E)
  nums.map fun z => z == den

/-- Compute pair exclusions by original suffixes, charging only a quadratic occurrence scan. -/
@[expose] def pairs (c : Clause ℕ) : CNF ℕ :=
  (List.range c.length).flatMap fun i => (c.drop (i + 1)).map fun l =>
    let first := c.getD i (0, false)
    [(first.1, !first.2), (l.1, !l.2)]

/-- The indexed scan is precisely the standard occurrence-sensitive at-most-one encoding. -/
theorem pairs_eq (c : Clause ℕ) : pairs c = c.atMostOneOccurrences := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [pairs, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map, List.drop_zero, List.getD_cons_zero, List.drop_succ_cons,
      List.getD_cons_succ, Clause.atMostOneOccurrences] at ih ⊢
    rw [ih]
    rfl

/-- Selected-row coverage clauses use one path edge per computed original equation. -/
@[expose] def query (n : ℕ) (B E : CNF ℕ) (β : Bool) : CNF ℕ :=
  (B ++ E.flatMap pairs).dedup ++ (List.range E.length).flatMap fun j =>
    (E.getD j []).flatMap fun l =>
      BinaryQuery.termClauses n (E.length - 1) β j [l]

/-- The whole dispatcher consumes only original data; every rank and candidate is computed. -/
@[expose] def compile (x : Input) : Output :=
  let (n, B, E) := x
  if n ≤ 1 then .inl (small n B E)
  else if B.isEmpty && E.isEmpty then .inl (2 ^ n)
  else if [] ∈ B then .inl 0
  else
    let A := payloadRows n E
    let b := payloadRhs E
    if rectangularConsistent n A b then
      let ids := gramRowBasis n A
      if ids.length = n then .inl (if test B E (candidate n E) then 1 else 0)
      else if ids.isEmpty then .inr (n, (B.dedup, [[]]))
      else
        let selected := ids.map fun i => E.getD i []
        .inr (n + ids.length - 1, (query n B selected false, query n B selected true))
    else .inl 0

private theorem read_polytime : ComputableInPolyTime
    (fun p : List Bool × ℕ => p.1.getD p.2 false) (encPair encBits encNat) encBool :=
  .of_tidy (ComputableTidilyInPolyTime.listGetD_binary false (by fun_prop) (by fun_prop))

attribute [local fun_prop] read_polytime

private theorem eval_polytime : ComputableInPolyTime
    (fun p : CNF ℕ × List Bool => eval p.1 p.2)
    (encPair encSignedCNF encBits) encBool := by
  unfold eval encSignedCNF
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  apply ComputableInPolyTime.anyWithInput (by fun_prop)
  fun_prop

private theorem test_polytime : ComputableInPolyTime
    (fun p : (CNF ℕ × CNF ℕ) × List Bool => test p.1.1 p.1.2 p.2)
    (encPair (encPair encSignedCNF encSignedCNF) encBits) encBool := by
  have he := eval_polytime.comp (show ComputableInPolyTime
    (fun p : (CNF ℕ × CNF ℕ) × List Bool => (p.1.1, p.2))
    (encPair (encPair encSignedCNF encSignedCNF) encBits)
    (encPair encSignedCNF encBits) from by fun_prop)
  unfold test encSignedCNF
  apply ComputableInPolyTime.bool_and' he
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  fun_prop

private theorem small_polytime : ComputableInPolyTime
    (fun x : Input => small x.1 x.2.1 x.2.2) encInput encNat := by
  have ht (b : Bool) := test_polytime.comp (show ComputableInPolyTime
    (fun x : Input => (x.2, List.replicate x.1 b)) encInput
    (encPair (encPair encSignedCNF encSignedCNF) encBits) from by
      have hn : ComputableTidilyInPolyTime (fun x : Input => x.1) encInput encUnary := by
        unfold encInput; fun_prop
      have hb := (ComputableTidilyInPolyTime.listToBits.comp
        (ComputableTidilyInPolyTime.replicate hn (.const b)))
      exact (show ComputableInPolyTime (fun x : Input => x.2) _ _ from
        by unfold encInput; fun_prop).prod (.of_tidy hb))
  unfold small
  have hz : ComputableInPolyTime (fun x : Input => decide (x.1 = 0)) encInput encBool := by
    unfold encInput; fun_prop
  apply (ComputableInPolyTime.binary_add.comp
    (((ht false).ite' (.const 1) (.const 0)).prod
      (hz.ite' (.const 0) ((ht true).ite' (.const 1) (.const 0))))).of_enc_eq
  intro x
  simp only [Function.comp_def, decide_eq_true_eq]

private theorem candidate_polytime : ComputableInPolyTime
    (fun p : ℕ × CNF ℕ => candidate p.1 p.2)
    (encPair encUnary encSignedCNF) encBits := by
  have hn : ComputableInPolyTime (fun p : ℕ × CNF ℕ => p.1)
      (encPair encUnary encSignedCNF) encUnary := by fun_prop
  have hb := payloadRhs_polytime.comp (ComputableInPolyTime.snd encUnary encSignedCNF)
  have hc := rectangularCertificate_polytime.comp ((hn.prod payloadRows_polytime).prod hb)
  have hm : ComputableInPolyTime (fun p : ℤ × List ℤ => p.2.map fun z => z == p.1)
      (encPair encIntBin (encList encIntBin)) (encList encBool) := by
    apply ComputableInPolyTime.mapWithInput (by fun_prop)
    fun_prop
  exact ((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.listToBits).comp
    (hm.comp hc)).of_enc_eq fun _ => rfl

private theorem pairs_polytime : ComputableInPolyTime pairs
    (encList (encPair encNat encBool)) encSignedCNF := by
  unfold pairs encSignedCNF
  apply ComputableInPolyTime.flatMapWithInput (by fun_prop)
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  fun_prop

private theorem term_polytime {α : Type} {enc : α ↪ List Bool}
    {n h j : α → ℕ} {β : α → Bool} {l : α → Literal ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hh : ComputableInPolyTime h enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary) (hb : ComputableInPolyTime β enc encBool)
    (hl : ComputableInPolyTime l enc (encPair encNat encBool)) :
    ComputableInPolyTime
      (fun x => BinaryQuery.termClauses (n x) (h x) (β x) (j x) [l x]) enc encSignedCNF := by
  have hnB := ComputableInPolyTime.unary_to_binary.comp hn
  have ha : ComputableInPolyTime (fun x => n x + j x - 1) enc encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hz : ComputableInPolyTime (fun x => decide (j x = 0)) enc encBool := by fun_prop
  have hh0 : ComputableInPolyTime (fun x => decide (h x = 0)) enc encBool := by fun_prop
  have heq : ComputableInPolyTime (fun x => decide (j x = h x)) enc encBool := by fun_prop
  have hnext : ComputableInPolyTime (fun x => n x + j x) enc encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hfirst : ComputableInPolyTime
      (fun x => [[((l x).1, !(l x).2), (n x, false)]]) enc encSignedCNF := by
    unfold encSignedCNF; fun_prop
  have hlast : ComputableInPolyTime
      (fun x => [[((l x).1, !(l x).2), (n x + j x - 1, β x)]]) enc encSignedCNF := by
    unfold encSignedCNF; fun_prop
  have hinner : ComputableInPolyTime (fun x =>
      [[((l x).1, !(l x).2), (n x + j x - 1, false), (n x + j x, true)],
        [((l x).1, !(l x).2), (n x + j x - 1, true), (n x + j x, false)]])
      enc encSignedCNF := by unfold encSignedCNF; fun_prop
  have hone : ComputableInPolyTime
      (fun x => [[((l x).1, !(l x).2)]]) enc encSignedCNF := by
    unfold encSignedCNF; fun_prop
  simpa only [BinaryQuery.termClauses, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append,
    decide_eq_true_eq] using
    hz.ite' (hh0.ite' (hb.ite' hone (.const [])) hfirst) (heq.ite' hlast hinner)

/-- Actual exclusion/coverage/path writing, including global side/exclusion deduplication. -/
@[fun_prop] theorem query_polytime : ComputableInPolyTime
    (fun p : (Input × CNF ℕ) × Bool => query p.1.1.1 p.1.1.2.1 p.1.2 p.2)
    (encPair (encPair encInput encSignedCNF) encBool) encSignedCNF := by
  let ei := encPair (encPair encInput encSignedCNF) encBool
  have hn : ComputableInPolyTime (fun p : (Input × CNF ℕ) × Bool => p.1.1.1)
      ei encUnary := by unfold ei encInput; fun_prop
  have hB : ComputableInPolyTime (fun p : (Input × CNF ℕ) × Bool => p.1.1.2.1)
      ei encSignedCNF := by unfold ei encInput; fun_prop
  have hE : ComputableInPolyTime (fun p : (Input × CNF ℕ) × Bool => p.1.2)
      ei encSignedCNF := by unfold ei; fun_prop
  have hpairs : ComputableInPolyTime
      (fun p : (Input × CNF ℕ) × Bool => p.1.2.flatMap pairs) ei encSignedCNF := by
    unfold encSignedCNF at hE ⊢
    apply ComputableInPolyTime.flatMapWithInput hE
    exact (pairs_polytime.comp
      (ComputableInPolyTime.snd ei (encList (encPair encNat encBool)))).of_enc_eq fun _ => rfl
  have hbase := (Cslib.dedup_polytime (encList (encPair encNat encBool)) []).comp
    (ComputableInPolyTime.listAppend' hB hpairs)
  have hp : ComputableInPolyTime (fun p : ((Input × CNF ℕ) × Bool) × ℕ =>
      p.1.1.2.getD p.2 []) (encPair ei encUnary) (encList (encPair encNat encBool)) := by
    unfold ei encSignedCNF; fun_prop
  have hlen := (ComputableInPolyTime.length_list (encList (encPair encNat encBool))).comp hE
  have hH := ComputableInPolyTime.unary_sub.comp (hlen.prod (ComputableInPolyTime.const 1))
  have hβ : ComputableInPolyTime (fun p : (Input × CNF ℕ) × Bool => p.2) ei encBool :=
    ComputableInPolyTime.snd _ _
  have hclauses : ComputableInPolyTime (fun p : (Input × CNF ℕ) × Bool =>
      (List.range p.1.2.length).flatMap fun j =>
        (p.1.2.getD j []).flatMap fun l =>
          BinaryQuery.termClauses p.1.1.1 (p.1.2.length - 1) p.2 j [l]) ei encSignedCNF := by
    unfold encSignedCNF
    apply ComputableInPolyTime.flatMapWithInput (by unfold ei; fun_prop)
    apply ComputableInPolyTime.flatMapWithInput hp
    let outer := ComputableInPolyTime.fst (encPair ei encUnary) (encPair encNat encBool)
    let parent := (ComputableInPolyTime.fst ei encUnary).comp outer
    exact (term_polytime (hn.comp parent) (hH.comp parent)
      ((ComputableInPolyTime.snd ei encUnary).comp outer) (hβ.comp parent)
      (ComputableInPolyTime.snd _ _)).of_enc_eq fun _ => rfl
  exact ComputableInPolyTime.listAppend' hbase hclauses

/-- Complete binary branch dispatch and output writing is polynomial time/space on every raw
payload. Semantic correctness below restricts rows to the declared signed-scope convention. -/
@[fun_prop] theorem compile_polytime : ComputableInPolyTime compile encInput encOutput := by
  have hn : ComputableInPolyTime (fun x : Input => x.1) encInput encUnary := by
    unfold encInput; fun_prop
  have hB : ComputableInPolyTime (fun x : Input => x.2.1) encInput encSignedCNF := by
    unfold encInput; fun_prop
  have hE : ComputableInPolyTime (fun x : Input => x.2.2) encInput encSignedCNF := by
    unfold encInput; fun_prop
  have hA := payloadRows_polytime.comp (hn.prod hE)
  have hrhs := payloadRhs_polytime.comp hE
  have hsys := (hn.prod hA).prod hrhs
  have hc := rectangularConsistent_polytime.comp hsys
  have hi := gramRowBasis_polytime.comp (hn.prod hA)
  have hs : ComputableInPolyTime (fun x : Input =>
      (gramRowBasis x.1 (payloadRows x.1 x.2.2)).map fun i => x.2.2.getD i [])
      encInput encSignedCNF := by
    unfold encSignedCNF at hE ⊢
    exact ComputableInPolyTime.mapWithInput hi (by unfold encInput encSignedCNF; fun_prop)
  have hq (b : Bool) := query_polytime.comp
    ((ComputableInPolyTime.id'.prod hs).prod (ComputableInPolyTime.const b))
  have hN : ComputableInPolyTime
      (fun x : Input => x.1 + (gramRowBasis x.1 (payloadRows x.1 x.2.2)).length - 1)
      encInput encUnary := by fun_prop
  have htag := ComputableInPolyTime.sumInr encNat
    (encPair encUnary (encPair encSignedCNF encSignedCNF))
  have hquery := htag.comp (hN.prod ((hq false).prod (hq true)))
  have hnone := htag.comp
    (hn.prod (((Cslib.dedup_polytime (encList (encPair encNat encBool)) []).comp hB).prod
      (ComputableInPolyTime.const ([[]] : CNF ℕ))))
  have hbits := candidate_polytime.comp (hn.prod hE)
  have ht := test_polytime.comp ((hB.prod hE).prod hbits)
  have hdir := (ComputableInPolyTime.sumInl encNat
    (encPair encUnary (encPair encSignedCNF encSignedCNF))).comp
      (ht.ite' (.const 1) (.const 0))
  have hsmall := (ComputableInPolyTime.sumInl encNat
    (encPair encUnary (encPair encSignedCNF encSignedCNF))).comp small_polytime
  have hbare : ComputableInPolyTime (fun x : Input => x.2.1.isEmpty && x.2.2.isEmpty)
      encInput encBool := by unfold encInput encSignedCNF; fun_prop
  have hpow := (ComputableInPolyTime.sumInl encNat
    (encPair encUnary (encPair encSignedCNF encSignedCNF))).comp
      ((ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_pow).comp
        ((ComputableInPolyTime.const 2).prod hn))
  have hzero : ComputableInPolyTime (fun _ : Input => (Sum.inl 0 : Output)) encInput encOutput :=
    .const _
  have hsm : ComputableInPolyTime (fun x : Input => decide (x.1 ≤ 1)) encInput encBool := by
    fun_prop
  have hempty := ComputableInPolyTime.decide_mem hB
    (ComputableInPolyTime.const ([] : Clause ℕ))
  have hfull : ComputableInPolyTime (fun x : Input =>
      decide ((gramRowBasis x.1 (payloadRows x.1 x.2.2)).length = x.1)) encInput encBool := by
    fun_prop
  have hno : ComputableInPolyTime (fun x : Input =>
      (gramRowBasis x.1 (payloadRows x.1 x.2.2)).isEmpty) encInput encBool := by fun_prop
  exact (hsm.ite' hsmall (hbare.ite' hpow (hempty.ite' hzero
    (hc.ite' (hfull.ite' hdir (hno.ite' hnone hquery)) hzero)))).of_enc_eq fun x => by
      simp only [compile, decide_eq_true_eq, Function.comp_def]
      rfl

end Cslib.Logic.PL.ExactOne.BinaryPlan
