/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.WeightedComparison.Frontend
import all CslibFrontier.Computability.Circuit.Boolean.PopulationCount.ThresholdPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# Binary resources of actual weighted-comparison generation

Certify the original-input radix grouping, literal extraction, population counting, arithmetic,
code composition and full functional CNF writes of [ChenJiangZhu2027], Lemma A.1 (PDF pp.28–29).
Coefficients and targets remain binary; only original counts, derived widths and loop positions
are unary. All code and index intermediates are charged by the existing binary calculus.

## Main results

* `radix_polytime`, `sumCode_polytime`: actual binary group arithmetic and complete gate lists.
* `testCode_polytime`, `build_polytime`: original-input comparison and full CNF writing.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum.BinaryFrontend

open Turing.MultiTapeTM ComputableInPolyTime

/-- Actual square-root-scale radix, including its unary materialization. -/
@[fun_prop] theorem radix_polytime :
    ComputableInPolyTime (fun x : Input => radix (declared x)) encInput encUnary := by
  have hn : ComputableInPolyTime declared encInput encUnary := by
    unfold declared encInput; fun_prop
  have hl := (unary_clog_const 2).comp
    (show ComputableInPolyTime (fun x => declared x + 1) encInput encUnary from by fun_prop)
  have hh : ComputableInPolyTime (fun x => height (declared x)) encInput encUnary := by
    unfold height
    have hd := ComputableInPolyTime.unary_div.comp (hl.prod (.const 2))
    fun_prop
  refine binary_to_unary_bounded (binary_two_pow.comp hh)
    (show ComputableInPolyTime (fun x => 4 * (declared x + 1)) encInput encUnary from by
      fun_prop) ?_
  intro x
  have he : height (declared x) ≤ Nat.clog 2 (declared x + 1) + 1 := by unfold height; omega
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) he
  have hc := Nat.pow_clog_le_mul Nat.one_lt_two (Nat.succ_ne_zero (declared x))
  rw [pow_succ] at hp
  change 2 ^ height (declared x) ≤ _
  nlinarith

/-- A group request contains the original frame and actual unary digit/value loop positions. -/
abbrev Request := Input × (ℕ × ℕ)
/-- The original frame, without circuit or budget advice. -/
@[expose] def original (r : Request) : Input := r.1
/-- Actual digit position. -/
@[expose] def position (r : Request) : ℕ := let (_, (a, _)) := r; a
/-- Actual digit value. -/
@[expose] def digitValue (r : Request) : ℕ := let (_, (_, q)) := r; q
/-- Original binary frame plus unary loop positions. -/
abbrev encRequest := encPair encInput (encPair encUnary encUnary)

/-- Actual natural-index traversal of a radix group, without a finite-subset oracle. -/
@[expose] def indices (r : Request) : List ℕ :=
  let x := original r
  (List.range (declared x)).filter fun i =>
    decide (digit (radix (declared x)) (position r) (entry x i).1 = digitValue r)

private theorem indices_eq (r : Request) : indices r =
    (group (weight (original r)) (radix (declared (original r)))
      (position r) (digitValue r)).map Fin.val := by
  dsimp only [indices, group]
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  rfl

/-- Charge coefficient lookup, radix powers, binary division/modulus and group-index writes. -/
@[fun_prop] theorem indices_polytime :
    ComputableInPolyTime indices encRequest (encList encUnary) := by
  have hx : ComputableInPolyTime original encRequest encInput := by
    unfold original encRequest; fun_prop
  have hn : ComputableInPolyTime (fun r => declared (original r)) encRequest encUnary := by
    unfold declared; fun_prop
  have hp := unary_to_binary.comp (radix_polytime.comp hx)
  have ha : ComputableInPolyTime position encRequest encUnary := by
    unfold position encRequest; fun_prop
  have hq : ComputableInPolyTime digitValue encRequest encNat := by
    apply unary_to_binary.comp
    unfold encRequest
    fun_prop
  have hpow := binary_pow' hp ha
  have he : ComputableInPolyTime
      (fun p : Request × ℕ => entry (original p.1) p.2)
      (encPair encRequest encUnary) (encPair encNat encBool) := by
    unfold entry entries original encRequest encInput
    fun_prop
  have htest : ComputableInPolyTime
      (fun p : Request × ℕ => decide (digit (radix (declared (original p.1)))
        (position p.1) (entry (original p.1) p.2).1 = digitValue p.1))
      (encPair encRequest encUnary) encBool := by
    have hget := he.fst'
    have hpp := hpow.comp (fst encRequest encUnary)
    have hp' := hp.comp (fst encRequest encUnary)
    have hq' := hq.comp (fst encRequest encUnary)
    have hd := binary_div.comp (hget.prod hpp)
    have hm := binary_mod.comp (hd.prod hp')
    exact .of_tidy ((ComputableTidilyInPolyTime.decide_eq encNat).comp (hm.tidy.prod hq'.tidy))
  exact filterWithInput (range.comp hn) htest

/-- Actual literal code generation on the raw group indices. -/
@[expose] def groupLiterals (r : Request) : List (Op × List ℕ) × List ℕ :=
  let x := original r
  appendCodes (declared x) ((indices r).map fun i =>
    literalCode (declared x) i (entry x i).2)

private theorem groupLiterals_eq (r : Request) : groupLiterals r =
    literalsCode (positive (original r)) (group (weight (original r))
      (radix (declared (original r))) (position r) (digitValue r)) := by
  simp only [groupLiterals, indices_eq, List.map_map, literalsCode, Function.comp_def, positive]

/-- Literal signs, complete NOT gates and output references are computed from original entries. -/
@[fun_prop] theorem groupLiterals_polytime :
    ComputableInPolyTime groupLiterals encRequest encCode := by
  have hn : ComputableInPolyTime (fun r => declared (original r)) encRequest encNat := by
    unfold declared original encRequest encInput; fun_prop
  have he : ComputableInPolyTime
      (fun p : Request × ℕ => (entry (original p.1) p.2).2)
      (encPair encRequest encUnary) encBool := by
    unfold entry entries original encRequest encInput
    fun_prop
  have hb : ComputableInPolyTime
      (fun p : Request × ℕ => literalCode (declared (original p.1)) p.2
        (entry (original p.1) p.2).2)
      (encPair encRequest encUnary) encCode := by
    have hn' := hn.comp (fst encRequest encUnary)
    have hi := unary_to_binary.comp (snd encRequest encUnary)
    unfold literalCode
    fun_prop
  exact computableInPolyTime_appendCodes hn (mapWithInput indices_polytime hb)

/-- Actual population-count stage, with derived group length and binary code throughout. -/
@[expose] def countCode (c : ℕ) (r : Request) : List (Op × List ℕ) × List ℕ :=
  let n := declared (original r)
  let u := (indices r).length
  compCode n (PopulationCount.pad (Nat.clog 2 (u + 1) + 1) (width n c)).code
    (compCode n (populationCountCircuit u).code (groupLiterals r))

private theorem countCode_eq (c : ℕ) (r : Request) : countCode c r =
    groupCountCode (weight (original r)) (positive (original r))
      (radix (declared (original r))) (position r) (digitValue r)
      (width (declared (original r)) c) := by
  have hl : (indices r).length = (group (weight (original r))
      (radix (declared (original r))) (position r) (digitValue r)).length := by
    simpa only [List.length_map] using congrArg List.length (indices_eq r)
  dsimp only [countCode, groupCountCode]
  rw [hl, groupLiterals_eq]

/-- Polynomial bit time for complete signed-literal counting and zero widening. -/
@[fun_prop] theorem countCode_polytime (c : ℕ) :
    ComputableInPolyTime (countCode c) encRequest encCode := by
  have hx : ComputableInPolyTime original encRequest encInput := by
    unfold original encRequest; fun_prop
  have hn : ComputableInPolyTime (fun r => declared (original r)) encRequest encNat := by
    unfold declared; fun_prop
  have hu := (length_list encUnary).comp indices_polytime
  have hw := (width_polytime c).comp hx
  have hgw : ComputableInPolyTime
      (fun r => Nat.clog 2 ((indices r).length + 1) + 1) encRequest encUnary := by
    have hlog := (unary_clog_const 2).comp
      (show ComputableInPolyTime (fun r => (indices r).length + 1) encRequest encUnary from by
        fun_prop)
    fun_prop
  have hpad := PopulationCount.computableInPolyTime_pad.comp (hgw.prod hw)
  have hpop := computableInPolyTime_populationCountCircuit.comp hu
  exact computableInPolyTime_compCode hn hpad
    (computableInPolyTime_compCode hn hpop groupLiterals_polytime)

/-- Generate each actual weighted group contribution, including its full multiplier code. -/
@[fun_prop] theorem contribution_polytime (c : ℕ) : ComputableInPolyTime
    (fun r : Request => contributionCode (weight (original r)) (positive (original r))
      (radix (declared (original r))) (position r) (digitValue r)
      (width (declared (original r)) c)) encRequest encCode := by
  have hx : ComputableInPolyTime original encRequest encInput := by
    unfold original encRequest; fun_prop
  have hn : ComputableInPolyTime (fun r => declared (original r)) encRequest encNat := by
    unfold declared; fun_prop
  have hw := (width_polytime c).comp hx
  have hP := unary_to_binary.comp (radix_polytime.comp hx)
  have ha : ComputableInPolyTime position encRequest encUnary := by
    unfold position encRequest; fun_prop
  have hq : ComputableInPolyTime digitValue encRequest encNat := by
    apply unary_to_binary.comp
    unfold encRequest
    fun_prop
  have hpow := binary_pow' hP ha
  have hcoeff := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.binary_mul.comp (hpow.tidy.prod hq.tidy))
  have hnum := PopulationCount.numeralCode_polyTime hn hw hcoeff
  have hmul : ComputableInPolyTime
      (fun r : Request => Modular.multiplyCode (width (declared (original r)) c))
      encRequest encCode := by
    simpa only [Modular.multiplyCode_eq_code, Function.comp_def] using
      Modular.computableInPolyTime_multiply.comp hw
  have hcount : ComputableInPolyTime
      (fun r : Request => groupCountCode (weight (original r)) (positive (original r))
        (radix (declared (original r))) (position r) (digitValue r)
        (width (declared (original r)) c)) encRequest encCode := by
    convert countCode_polytime c using 1
    funext r
    exact (countCode_eq c r).symm
  unfold contributionCode
  exact computableInPolyTime_compCode hn hmul
    (computableInPolyTime_appendCode hn hcount hnum)

/-- Actual original-input weighted sum generation, including both group loops and reduction. -/
@[fun_prop] theorem sumCode_polytime (c : ℕ) : ComputableInPolyTime
    (fun x : Input => sumCode (weight x) (positive x) (radix (declared x)) (positions c)
      (width (declared x) c)) encInput encCode := by
  have hn : ComputableInPolyTime declared encInput encNat := by
    apply unary_to_binary.comp
    unfold encInput
    fun_prop
  have hw := width_polytime c
  let eA := encPair encInput encUnary
  let eQ := encPair eA encUnary
  have hm : ComputableInPolyTime
      (fun p : (Input × ℕ) × ℕ => (p.1.1, (p.1.2, p.2))) eQ encRequest := by
    unfold eQ eA encRequest
    fun_prop
  have hcon := (contribution_polytime c).comp hm
  have hnq : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ => declared p.1.1)
      eQ encNat := by
    exact hn.comp ((fst eA encUnary).fst')
  have hwq : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ => width (declared p.1.1) c)
      eQ encUnary := by
    exact hw.comp ((fst eA encUnary).fst')
  have hpair := computableInPolyTime_pairWithZeroCode hnq hwq hcon
  have hqs : ComputableInPolyTime
      (fun p : Input × ℕ => List.range (radix (declared p.1))) eA (encList encUnary) :=
    range.comp (radix_polytime.comp (fst encInput encUnary))
  have ha := mapWithInput
    (f := fun (p : Input × ℕ) (q : ℕ) => pairWithZeroCode (declared p.1)
      (width (declared p.1) c) (contributionCode (weight p.1) (positive p.1)
        (radix (declared p.1)) p.2 q (width (declared p.1) c))) hqs
    (by simpa only [Function.comp_def, original, position, digitValue] using hpair)
  have hleaves := flatMapWithInput
    (f := fun (x : Input) (a : ℕ) => (List.range (radix (declared x))).map fun q =>
      pairWithZeroCode (declared x) (width (declared x) c)
        (contributionCode (weight x) (positive x) (radix (declared x)) a q (width (declared x) c)))
    (const (encOut := encList encUnary) (List.range (positions c))) ha
  have h := computableInPolyTime_sumPairsCode hn hw hleaves
  convert h using 1
  funext x
  unfold sumCode
  congr 1
  simp_rw [← List.map_coe_finRange_eq_range (n := radix (declared x))]
  simp only [List.map_map, Function.comp_def]

/-- Actual upper-comparison code generation has polynomial binary time, including huge targets. -/
@[fun_prop] theorem upperCode_polytime (c : ℕ) : ComputableInPolyTime
    (fun x : Input => upperCode c (weight x) (positive x) (target x)) encInput encCode := by
  have hn : ComputableInPolyTime declared encInput encUnary := by
    unfold declared encInput; fun_prop
  have hb := unary_to_binary.comp hn
  have hw := width_polytime c
  have ht : ComputableInPolyTime target encInput encIntBin := by
    unfold target encInput; fun_prop
  have hnat := ComputableInPolyTime.intBin_toNat.comp ht
  have hfit : ComputableInPolyTime
      (fun x : Input => decide ((target x).toNat < 2 ^ width (declared x) c))
      encInput encBool := by
    have hp := binary_two_pow.comp hw
    exact binary_lt.comp (hnat.prod hp)
  have hneg : ComputableInPolyTime (fun x : Input => decide (target x < 0))
      encInput encBool := .of_tidy (ComputableTidilyInPolyTime.intBin_lt.comp
        (ht.tidy.prod (.const 0)))
  have hnum := PopulationCount.numeralCode_polyTime hb hw hnat
  have hle := computableInPolyTime_leCircuit.comp hw
  have hbody := computableInPolyTime_compCode hb hle
    (computableInPolyTime_appendCode hb (sumCode_polytime c) hnum)
  have hfalse : ComputableInPolyTime (fun x : Input => ([(Op.const false, [])], [declared x]))
      encInput encCode := by fun_prop
  have htrue : ComputableInPolyTime (fun x : Input => ([(Op.const true, [])], [declared x]))
      encInput encCode := by fun_prop
  unfold upperCode
  simpa only [decide_eq_true_eq, Function.comp_def] using
    hneg.ite' hfalse (hfit.ite' hbody htrue)

/-- Shift a signed binary target by one without changing its original records/declaration. -/
@[expose] def predecessor (x : Input) : Input :=
  (declared x, (entries x, target x - 1))

private theorem predecessor_polytime :
    ComputableInPolyTime predecessor encInput encInput := by
  unfold predecessor declared entries target encInput
  fun_prop

/-- Every ordinary comparison, including strict shifts and equality's two sums, is generated
in polynomial binary time from its actual original frame. -/
@[fun_prop] theorem testCode_polytime (op : Comparison) (c : ℕ) : ComputableInPolyTime
    (fun x : Input => testCode op c (weight x) (positive x) (target x)) encInput encCode := by
  have hn : ComputableInPolyTime declared encInput encNat := by
    apply unary_to_binary.comp
    unfold encInput
    fun_prop
  have hu := upperCode_polytime c
  have hs : ComputableInPolyTime
      (fun x : Input => upperCode c (weight x) (positive x) (target x - 1)) encInput encCode := by
    convert hu.comp predecessor_polytime using 1
    funext x
    rfl
  have hn0 := computableInPolyTime_compCode hn
    (const (encOut := encCode) ([(Op.not, [0])], [1])) hu
  have hn1 := computableInPolyTime_compCode hn
    (const (encOut := encCode) ([(Op.not, [0])], [1])) hs
  have heq := computableInPolyTime_compCode hn
    (const (encOut := encCode) ([(Op.and, [0, 1])], [2]))
    (computableInPolyTime_appendCode hn hu hn1)
  cases op with
  | le => exact hu
  | ge => exact hn1
  | eq => exact heq
  | lt => exact hs
  | gt => exact hn0

/-- Complete actual original-input functional 3-CNF writing, charging every gate/literal/delimiter.
This is a machine-time proof, not an inference from the independent linear gate/output bounds. -/
@[fun_prop] theorem build_polytime (op : Comparison) (c : ℕ) :
    ComputableInPolyTime (build op c) encInput
      (encList (encList (encPair encNat encBool))) := by
  have hn : ComputableInPolyTime declared encInput encUnary := by
    unfold declared encInput; fun_prop
  have hf : ComputableInPolyTime
      (fun x : Input => (declared x, testCode op c (weight x) (positive x) (target x), [true]))
      encInput FunctionalCNF.encInput :=
    hn.prod ((testCode_polytime op c).prod (.const [true]))
  exact FunctionalCNF.write_polytime.comp hf

end Cslib.Circuits.Boolean.WeightedSum.BinaryFrontend
