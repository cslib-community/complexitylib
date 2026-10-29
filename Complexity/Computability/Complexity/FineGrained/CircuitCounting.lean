/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Encoding
public import Complexity.Computability.Circuit.Frontier.Compiler.CNF
public import Complexity.Computability.Complexity.FineGrained.CountingCSP
public import Complexity.Computability.Complexity.FineGrained.CountingNativeModelCount
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
import Complexity.Computability.Circuit.Program
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Subexponential `#Circuit-SAT` and circuit satisfiability over bounded-arity Boolean signatures

Combines the frontier CSP/CNF reduction (`Cslib.Circuits.Frontier.Compiler.toCSP`,
`Compiler.toCNF`, `Compiler.freeShift`,
`Compiler.acceptCount_eq_two_pow_freeShift_mul_modelCount`) with bounded-arity Boolean `#CSP`
compilation (`Cslib.Complexity.CSP.computableInPolyTime_toCNFBounded_of_finite`) and the shifted
bounded-width `#SAT` wrapper (`CountingNativeEndpoint.exists_shiftedCounter_of_polyTime_toCNF`) to
obtain deterministic subexponential-time, polynomial-space exact counting and decision for
bounded-fan-in Boolean circuits.

### Source relation and library extensions

* **Appendix C.1 of [OpenAI2026ETH] (p. 51):** states the **decision** consequence for linear-size
  De Morgan (`AND`/`OR`/`NOT`) circuits (`DecidableInSubexpTime` on `c.2.size ≤ C * n + C` in
  `decidableInSubexpTime_linearSizeCircuitSAT`), proved there by introducing one variable per gate
  (`O(n + s)` variables and 3-CNF clauses).
* **Original library extensions:** exact counting (`acceptCount` and `satCount`), arbitrary finite
  Boolean signatures `σ` with bounded fan-in, reachable-wire pruning through
  `Cslib.Circuits.Frontier.Compiler` with the `2 ^ freeShift` multiplicity factor so the variable
  bound `k * c.2.size + m` depends only on gate count `c.2.size` (independent of unread inputs),
  and the single-machine `interpolationScale` counting bounds (`exists_circuitAcceptCounter`,
  `exists_circuitSatCounter`, `exists_booleanCircuitSatCounter`,
  `exists_linearSizeCircuitSatCounter`, `exists_linearSizeBooleanCircuitSatCounter`).
* **Runtime scale and per-`δ` decision:** the single-machine counters run at the §§3–6
  `interpolationScale` rate (Proposition 6.4, pp. 43–44), whereas the `DecidableInSubexpTime`
  corollaries express the library's weaker per-`δ > 0` decision notion (`∀ δ > 0`, some decider runs
  in `O(2 ^ (δ * μ c) * poly(|c|))`).

## Main definitions

* `Cslib.Complexity.CircuitCounting.encCircuitRel`: binary encoding of
  `Compiler.CircuitRel σ m = σ.Op ⊕ Fin m`.

## Main results

* `Cslib.Complexity.CircuitCounting.computableInPolyTime_toCSP`,
  `Cslib.Complexity.CircuitCounting.computableInPolyTime_toCNF`,
  `Cslib.Complexity.CircuitCounting.computableInPolyTime_freeShift`,
  `Cslib.Complexity.CircuitCounting.computableInPolyTime_toSatCNF`,
  `Cslib.Complexity.CircuitCounting.computableInPolyTime_satFreeShift`:
  polynomial-time compilation of circuits into reachable-wire CSP and CNF with exact multiplicity
  shift.
* `Cslib.Complexity.CircuitCounting.exists_circuitAcceptCounter`,
  `Cslib.Complexity.CircuitCounting.exists_circuitSatCounter`,
  `Cslib.Complexity.CircuitCounting.exists_booleanCircuitSatCounter`,
  `Cslib.Complexity.CircuitCounting.exists_linearSizeCircuitSatCounter`,
  `Cslib.Complexity.CircuitCounting.exists_linearSizeBooleanCircuitSatCounter`:
  exact subexponential-time, polynomial-space counters at the `interpolationScale` rate.
* `Cslib.Complexity.CircuitCounting.decidableInSubexpTime_fanInSignatureCircuitSAT_size`,
  `Cslib.Complexity.CircuitCounting.decidableInSubexpTime_signatureCircuitSAT_size`,
  `Cslib.Complexity.CircuitCounting.decidableInSubexpTime_CircuitSAT_size`,
  `Cslib.Complexity.CircuitCounting.decidableInSubexpTime_linearSizeSignatureCircuitSAT`,
  `Cslib.Complexity.CircuitCounting.decidableInSubexpTime_linearSizeCircuitSAT`:
  per-`δ > 0` subexponential-time decision corollaries.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Proposition 6.4 (pp. 43–44)
  and Appendix C.1 (p. 51).
-/

namespace Cslib.Complexity.CircuitCounting

open Cslib.Circuits Cslib.Circuits.Frontier Cslib.Logic.PL Turing.MultiTapeTM SubexponentialSAT

/-- Binary encoding of the circuit constraint relation alphabet `Compiler.CircuitRel σ m`. -/
public abbrev encCircuitRel {σ : Signature} (encOp : σ.Op ↪ List Bool) (m : ℕ) :
    Compiler.CircuitRel σ m ↪ List Bool :=
  encSum encOp (encFinEnum (Fin m))

/-! ### Syntactic fan-in and linear-size checks on serialized circuits -/

private def fanInCheck {σ : Signature} {m : ℕ} (k : ℕ) (c : Σ n, Circuit σ n m) : Bool :=
  c.2.code.1.all fun g => decide (g.2.length ≤ k)

private theorem fanInCheck_eq_true_iff {σ : Signature} {m k : ℕ} (c : Σ n, Circuit σ n m) :
    fanInCheck k c = true ↔ c.2.FanInAtMost k := by
  have hcode : c.2.code.1 = List.ofFn fun j : Fin c.2.size => (c.2.program.lines j).code :=
    Program.code_eq_ofFn_lines c.2.program
  rw [fanInCheck, hcode, List.all_eq_true, Circuit.FanInAtMost, Program.fanInAtMost_iff]
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, decide_eq_true_eq,
    Line.length_code_snd]

private def linearSizeCheck {σ : Signature} {m : ℕ} (C : ℕ) (c : Σ n, Circuit σ n m) : Bool :=
  decide (c.2.code.1.length ≤ C * c.1 + C)

private theorem linearSizeCheck_eq_true_iff {σ : Signature} {m C : ℕ} (c : Σ n, Circuit σ n m) :
    linearSizeCheck C c = true ↔ c.2.size ≤ C * c.1 + C := by
  simp only [linearSizeCheck, Circuit.length_code_fst, decide_eq_true_eq]

/-! ### Polynomial-time certificates for `Compiler.toCSP`, `Compiler.toCNF`, and `freeShift` -/

section PolyTimeCompiler

open ComputableInPolyTime

variable {σ : Signature}

private theorem computableInPolyTime_sumInl {α β : Type}
    (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInPolyTime (Sum.inl (α := α) (β := β)) left (encSum left right) :=
  ((const false).bitsCons
    (of_eq (f := left) (encIn := left) (encOut := encBits) fun _ => rfl)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_zipIdx {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun list : List α => list.zipIdx)
      (encList enc) (encList (encPair enc encUnary)) := by
  rcases isEmpty_or_nonempty α with h | h
  · exact of_finite _
  · obtain ⟨fallback⟩ := h
    have heq (list : List α) : list.zipIdx =
        (List.range list.length).map (fun i => (list.getD i fallback, i)) := by
      apply List.ext_getElem (by simp)
      intro i hi hi'
      simp only [List.length_zipIdx] at hi
      simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, Nat.zero_add]
    simp_rw [heq]
    fun_prop

private theorem computableInPolyTime_mapConst {α ι γ : Type} {encIn : α ↪ List Bool}
    {encC : γ ↪ List Bool} (items : List ι) {f : α → ι → γ}
    (hf : ∀ i ∈ items, ComputableInPolyTime (fun a => f a i) encIn encC) :
    ComputableInPolyTime (fun a => items.map (f a)) encIn (encList encC) := by
  induction items with
  | nil => exact const []
  | cons item rest ih =>
    exact cons' (hf item List.mem_cons_self)
      (ih fun i hi => hf i (List.mem_cons_of_mem _ hi))

private abbrev RawCode (σ : Signature) := ℕ × (List (σ.Op × List ℕ) × List ℕ)

private abbrev encRaw (encOp : σ.Op ↪ List Bool) : RawCode σ ↪ List Bool :=
  encPair encUnary (Circuit.encCode encOp)

private theorem computableInPolyTime_toRaw (encOp : σ.Op ↪ List Bool) (m : ℕ) :
    ComputableInPolyTime (fun c : Σ n, Circuit σ n m => (c.1, c.2.code))
      (Circuit.encCircuit encOp m) (encRaw encOp) :=
  of_eq fun _ => rfl

private theorem computableInPolyTime_fanInCheck (encOp : σ.Op ↪ List Bool) (m k : ℕ) :
    ComputableInPolyTime (fanInCheck (σ := σ) (m := m) k)
      (Circuit.encCircuit encOp m) encBool := by
  have hgates : ComputableInPolyTime (fun c : Σ n, Circuit σ n m => c.2.code.1)
      (Circuit.encCircuit encOp m) (encList (Circuit.encGate encOp)) :=
    (fst (encList (Circuit.encGate encOp)) (encList encNat)).comp
      ((snd encUnary (Circuit.encCode encOp)).comp (computableInPolyTime_toRaw encOp m))
  have htest : ComputableInPolyTime
      (fun p : (Σ n, Circuit σ n m) × (σ.Op × List ℕ) => decide (p.2.2.length ≤ k))
      (encPair (Circuit.encCircuit encOp m) (Circuit.encGate encOp)) encBool := by
    have hlen : ComputableInPolyTime
        (fun p : (Σ n, Circuit σ n m) × (σ.Op × List ℕ) => p.2.2.length)
        (encPair (Circuit.encCircuit encOp m) (Circuit.encGate encOp)) encUnary :=
      (length_list encNat).comp
        ((snd encOp (encList encNat)).comp
          (snd (Circuit.encCircuit encOp m) (Circuit.encGate encOp)))
    exact unary_le' hlen (const k)
  exact allWithInput hgates htest

private theorem computableInPolyTime_linearSizeCheck (encOp : σ.Op ↪ List Bool) (m C : ℕ) :
    ComputableInPolyTime (linearSizeCheck (σ := σ) (m := m) C)
      (Circuit.encCircuit encOp m) encBool := by
  have hraw := computableInPolyTime_toRaw encOp m
  have hn : ComputableInPolyTime (fun c : Σ n, Circuit σ n m => c.1)
      (Circuit.encCircuit encOp m) encUnary :=
    (fst encUnary (Circuit.encCode encOp)).comp hraw
  have hsize : ComputableInPolyTime (fun c : Σ n, Circuit σ n m => c.2.code.1.length)
      (Circuit.encCircuit encOp m) encUnary :=
    (length_list (Circuit.encGate encOp)).comp
      ((fst (encList (Circuit.encGate encOp)) (encList encNat)).comp
        ((snd encUnary (Circuit.encCode encOp)).comp hraw))
  have hrhs : ComputableInPolyTime (fun c : Σ n, Circuit σ n m => C * c.1 + C)
      (Circuit.encCircuit encOp m) encUnary :=
    unary_add.comp ((unary_mul.comp ((const C).prod hn)).prod (const C))
  exact unary_le' hsize hrhs

private theorem computableInPolyTime_reachStep (encOp : σ.Op ↪ List Bool) :
    ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × ((σ.Op × List ℕ) × ℕ) =>
        Compiler.reachStep p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encList encNat)) (encPair (Circuit.encGate encOp) encUnary))
      (encList encNat) := by
  let encS :=
    encPair (encPair encUnary (encList encNat)) (encPair (Circuit.encGate encOp) encUnary)
  have hseen : ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × ((σ.Op × List ℕ) × ℕ) => p.1.2) encS (encList encNat) :=
    (fst (encPair encUnary (encList encNat)) (encPair (Circuit.encGate encOp) encUnary)).snd'
  have htarget : ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × ((σ.Op × List ℕ) × ℕ) => p.1.1 + p.2.2) encS encNat := by
    have hn :=
      (fst (encPair encUnary (encList encNat)) (encPair (Circuit.encGate encOp) encUnary)).fst'
    have hj :=
      (snd (encPair encUnary (encList encNat)) (encPair (Circuit.encGate encOp) encUnary)).snd'
    exact unary_to_binary.comp (unary_add.comp (hn.prod hj))
  have hany : ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × ((σ.Op × List ℕ) × ℕ) => p.1.2.any (· == p.1.1 + p.2.2))
      encS encBool :=
    anyWithInput hseen ((snd encS encNat).beq (htarget.comp (fst encS encNat)))
  have hargs : ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × ((σ.Op × List ℕ) × ℕ) => p.2.1.2) encS (encList encNat) :=
    (snd encOp (encList encNat)).comp
      (snd (encPair encUnary (encList encNat)) (encPair (Circuit.encGate encOp) encUnary)).fst'
  exact hany.ite (listAppend' hargs hseen) hseen

private theorem computableInPolyTime_reachWiresRaw (encOp : σ.Op ↪ List Bool) :
    ComputableInPolyTime (fun r : RawCode σ => Compiler.reachWiresCode r.1 r.2)
      (encRaw encOp) (encList encNat) := by
  have hn : ComputableInPolyTime (fun r : RawCode σ => r.1) (encRaw encOp) encUnary :=
    fst encUnary (Circuit.encCode encOp)
  have hgates : ComputableInPolyTime (fun r : RawCode σ => r.2.1)
      (encRaw encOp) (encList (Circuit.encGate encOp)) :=
    (fst (encList (Circuit.encGate encOp)) (encList encNat)).comp
      (snd encUnary (Circuit.encCode encOp))
  have houts : ComputableInPolyTime (fun r : RawCode σ => r.2.2)
      (encRaw encOp) (encList encNat) :=
    (snd (encList (Circuit.encGate encOp)) (encList encNat)).comp
      (snd encUnary (Circuit.encCode encOp))
  have hlist : ComputableInPolyTime (fun r : RawCode σ => r.2.1.zipIdx.reverse)
      (encRaw encOp) (encList (encPair (Circuit.encGate encOp) encUnary)) :=
    listReverseWithInput ((computableInPolyTime_zipIdx (Circuit.encGate encOp)).comp hgates)
  refine foldlWith_of_bounded_growth hn hlist houts (computableInPolyTime_reachStep encOp)
    (growth := fun r => (encList (Circuit.encGate encOp) r.2.1).length)
    hgates.polyBounded_length fun r seen gj hmem => ?_
  unfold Compiler.reachStep
  split_ifs
  · rw [encList_append, List.length_append]
    have hmem_zip : gj ∈ r.2.1.zipIdx := List.mem_reverse.mp hmem
    rw [List.mem_zipIdx_iff_getElem?] at hmem_zip
    have hmem_g : gj.1 ∈ r.2.1 := List.mem_of_getElem? hmem_zip
    have hg_le := length_le_encList_of_mem (Circuit.encGate encOp) hmem_g
    have harg_le : (encList encNat gj.1.2).length ≤ (Circuit.encGate encOp gj.1).length := by
      rw [Circuit.encGate, length_encPair]
      omega
    omega
  · omega

private theorem computableInPolyTime_toCSPRaw (encOp : σ.Op ↪ List Bool) (m : ℕ) :
    ComputableInPolyTime (fun r : RawCode σ => Compiler.toCSPCode m r.1 r.2)
      (encRaw encOp) (encCSP (encCircuitRel encOp m) encNat) := by
  have hreach := computableInPolyTime_reachWiresRaw encOp
  have hgates : ComputableInPolyTime (fun r : RawCode σ => r.2.1.zipIdx)
      (encRaw encOp) (encList (encPair (Circuit.encGate encOp) encUnary)) :=
    (computableInPolyTime_zipIdx (Circuit.encGate encOp)).comp
      ((fst (encList (Circuit.encGate encOp)) (encList encNat)).comp
        (snd encUnary (Circuit.encCode encOp)))
  let encGJ := encPair (Circuit.encGate encOp) encUnary
  let encRG := encPair (encRaw encOp) encGJ
  have hwireNat : ComputableInPolyTime
      (fun p : RawCode σ × ((σ.Op × List ℕ) × ℕ) => p.1.1 + p.2.2) encRG encNat :=
    unary_to_binary.comp (unary_add.comp
      (((fst encUnary (Circuit.encCode encOp)).comp (fst (encRaw encOp) encGJ)).prod
        ((snd (Circuit.encGate encOp) encUnary).comp (snd (encRaw encOp) encGJ))))
  have hreachP : ComputableInPolyTime
      (fun p : RawCode σ × ((σ.Op × List ℕ) × ℕ) => Compiler.reachWiresCode p.1.1 p.1.2)
      encRG (encList encNat) :=
    hreach.comp (fst (encRaw encOp) encGJ)
  have hpred : ComputableInPolyTime
      (fun p : RawCode σ × ((σ.Op × List ℕ) × ℕ) =>
        (Compiler.reachWiresCode p.1.1 p.1.2).any (· == p.1.1 + p.2.2))
      encRG encBool :=
    anyWithInput hreachP ((snd encRG encNat).beq (hwireNat.comp (fst encRG encNat)))
  have hfilt := filterWithInput
    (test := fun (r : RawCode σ) gj => (Compiler.reachWiresCode r.1 r.2).any (· == r.1 + gj.2))
    hgates hpred
  have hgCons : ComputableInPolyTime
      (fun r : RawCode σ =>
        (r.2.1.zipIdx.filter fun gj =>
          (Compiler.reachWiresCode r.1 r.2).any (· == r.1 + gj.2)).map
          fun gj => ((Sum.inl gj.1.1 : Compiler.CircuitRel σ m), (r.1 + gj.2) :: gj.1.2))
      (encRaw encOp) (encCSP (encCircuitRel encOp m) encNat) := by
    refine mapWithInput hfilt ?_
    have hop : ComputableInPolyTime
        (fun p : RawCode σ × ((σ.Op × List ℕ) × ℕ) =>
          (Sum.inl p.2.1.1 : Compiler.CircuitRel σ m))
        encRG (encCircuitRel encOp m) :=
      (computableInPolyTime_sumInl encOp (encFinEnum (Fin m))).comp
        ((fst encOp (encList encNat)).comp
          ((fst (Circuit.encGate encOp) encUnary).comp (snd (encRaw encOp) encGJ)))
    have hargs : ComputableInPolyTime
        (fun p : RawCode σ × ((σ.Op × List ℕ) × ℕ) => p.2.1.2)
        encRG (encList encNat) :=
      (snd encOp (encList encNat)).comp
        ((fst (Circuit.encGate encOp) encUnary).comp (snd (encRaw encOp) encGJ))
    exact hop.prod (hwireNat.cons' hargs)
  have houtCons : ComputableInPolyTime
      (fun r : RawCode σ =>
        (List.finRange m).map fun o =>
          ((Sum.inr o : Compiler.CircuitRel σ m), [r.2.2.getD o.val 0]))
      (encRaw encOp) (encCSP (encCircuitRel encOp m) encNat) := by
    have houts : ComputableInPolyTime (fun r : RawCode σ => r.2.2)
        (encRaw encOp) (encList encNat) :=
      (snd (encList (Circuit.encGate encOp)) (encList encNat)).comp
        (snd encUnary (Circuit.encCode encOp))
    refine computableInPolyTime_mapConst (List.finRange m) fun o _ => ?_
    have hw : ComputableInPolyTime (fun r : RawCode σ => r.2.2.getD o.val 0)
        (encRaw encOp) encNat :=
      (listGetD 0).comp (houts.prod (const o.val))
    exact (const (Sum.inr o : Compiler.CircuitRel σ m)).prod (hw.cons' (const []))
  exact listAppend' hgCons houtCons

private theorem computableInPolyTime_reachGateCountRaw (encOp : σ.Op ↪ List Bool) :
    ComputableInPolyTime (fun r : RawCode σ => Compiler.reachGateCountCode r.1 r.2)
      (encRaw encOp) encUnary := by
  have hreach := computableInPolyTime_reachWiresRaw encOp
  have hgates : ComputableInPolyTime (fun r : RawCode σ => r.2.1.zipIdx)
      (encRaw encOp) (encList (encPair (Circuit.encGate encOp) encUnary)) :=
    (computableInPolyTime_zipIdx (Circuit.encGate encOp)).comp
      ((fst (encList (Circuit.encGate encOp)) (encList encNat)).comp
        (snd encUnary (Circuit.encCode encOp)))
  let encGJ := encPair (Circuit.encGate encOp) encUnary
  let encRG := encPair (encRaw encOp) encGJ
  have hwireNat : ComputableInPolyTime
      (fun p : RawCode σ × ((σ.Op × List ℕ) × ℕ) => p.1.1 + p.2.2) encRG encNat :=
    unary_to_binary.comp (unary_add.comp
      (((fst encUnary (Circuit.encCode encOp)).comp (fst (encRaw encOp) encGJ)).prod
        ((snd (Circuit.encGate encOp) encUnary).comp (snd (encRaw encOp) encGJ))))
  have hreachP : ComputableInPolyTime
      (fun p : RawCode σ × ((σ.Op × List ℕ) × ℕ) => Compiler.reachWiresCode p.1.1 p.1.2)
      encRG (encList encNat) :=
    hreach.comp (fst (encRaw encOp) encGJ)
  have hpred : ComputableInPolyTime
      (fun p : RawCode σ × ((σ.Op × List ℕ) × ℕ) =>
        (Compiler.reachWiresCode p.1.1 p.1.2).any (· == p.1.1 + p.2.2))
      encRG encBool :=
    anyWithInput hreachP ((snd encRG encNat).beq (hwireNat.comp (fst encRG encNat)))
  exact countPWithInput hgates hpred

/-- Compiling a circuit over `σ` to its reachable-wire Boolean CSP `Compiler.toCSP c.2` takes
polynomial time. -/
public theorem computableInPolyTime_toCSP (encOp : σ.Op ↪ List Bool) (m : ℕ) :
    ComputableInPolyTime (fun c : Σ n, Circuit σ n m => Compiler.toCSP c.2)
      (Circuit.encCircuit encOp m) (encCSP (encCircuitRel encOp m) encNat) :=
  (computableInPolyTime_toCSPRaw encOp m).comp (computableInPolyTime_toRaw encOp m)

/-- Compiling a circuit over a finite Boolean signature to its exact-multiplicity frontier CNF
formula `Compiler.toCNF c.2 I acc` takes polynomial time, obtained by composing
`computableInPolyTime_toCSP` with `CSP.computableInPolyTime_toCNFBounded_of_finite`. -/
public theorem computableInPolyTime_toCNF [Finite σ.Op] (encOp : σ.Op ↪ List Bool)
    (I : Interpretation σ Bool) {m : ℕ} (acc : Fin m → Bool → Bool) :
    ComputableInPolyTime (fun c : Σ n, Circuit σ n m => Compiler.toCNF c.2 I acc)
      (Circuit.encCircuit encOp m) encCNF := by
  let _ : Fintype σ.Op := Fintype.ofFinite σ.Op
  let K : ℕ := Finset.univ.sup σ.Arity
  have hbounded : ComputableInPolyTime
      (fun c : Σ n, Circuit σ n m =>
        (Compiler.toCSP c.2).toCNFBounded (K + 1) (Compiler.circuitSem I acc))
      (Circuit.encCircuit encOp m) encCNF :=
    (CSP.computableInPolyTime_toCNFBounded_of_finite
      (encCircuitRel encOp m) encNat (K + 1) (Compiler.circuitSem I acc)).comp
      (computableInPolyTime_toCSP encOp m)
  refine hbounded.of_enc_eq fun c => congrArg encCNF ?_
  have hfan : c.2.FanInAtMost K :=
    Program.fanInAtMost_iff.mpr fun j => Finset.le_sup (Finset.mem_univ _)
  exact (CSP.toCNFBounded_eq_toCNF fun _ hcon =>
    Compiler.length_scope_le_of_mem_toCSP hfan hcon).symm

/-- Computing the unread-input / unconstrained-wire shift `Compiler.freeShift c.2 I acc` in unary
takes polynomial time. -/
public theorem computableInPolyTime_freeShift [Finite σ.Op] (encOp : σ.Op ↪ List Bool)
    (I : Interpretation σ Bool) {m : ℕ} (acc : Fin m → Bool → Bool) :
    ComputableInPolyTime (fun c : Σ n, Circuit σ n m => Compiler.freeShift c.2 I acc)
      (Circuit.encCircuit encOp m) encUnary := by
  have hraw := computableInPolyTime_toRaw encOp m
  have hn : ComputableInPolyTime (fun c : Σ n, Circuit σ n m => c.1)
      (Circuit.encCircuit encOp m) encUnary :=
    (fst encUnary (Circuit.encCode encOp)).comp hraw
  have hrg : ComputableInPolyTime
      (fun c : Σ n, Circuit σ n m => Compiler.reachGateCountCode c.1 c.2.code)
      (Circuit.encCircuit encOp m) encUnary :=
    (computableInPolyTime_reachGateCountRaw encOp).comp hraw
  have hnum : ComputableInPolyTime
      (fun c : Σ n, Circuit σ n m => (Compiler.toCNF c.2 I acc).numVars)
      (Circuit.encCircuit encOp m) encUnary :=
    SAT.computableInPolyTime_numVars.comp (computableInPolyTime_toCNF encOp I acc)
  exact unary_sub.comp ((unary_add.comp (hn.prod hrg)).prod hnum)

/-- Compiling a 1-output circuit over a finite Boolean signature to `Compiler.toSatCNF c.2 I` takes
polynomial time. -/
public theorem computableInPolyTime_toSatCNF [Finite σ.Op] (encOp : σ.Op ↪ List Bool)
    (I : Interpretation σ Bool) :
    ComputableInPolyTime (fun c : Σ n, Circuit σ n 1 => Compiler.toSatCNF c.2 I)
      (Circuit.encCircuit encOp 1) encCNF :=
  computableInPolyTime_toCNF encOp I (fun _ b => b)

/-- Computing `Compiler.satFreeShift c.2 I` in unary takes polynomial time. -/
public theorem computableInPolyTime_satFreeShift [Finite σ.Op] (encOp : σ.Op ↪ List Bool)
    (I : Interpretation σ Bool) :
    ComputableInPolyTime (fun c : Σ n, Circuit σ n 1 => Compiler.satFreeShift c.2 I)
      (Circuit.encCircuit encOp 1) encUnary :=
  computableInPolyTime_freeShift encOp I (fun _ b => b)

end PolyTimeCompiler

/-! ### Exact `#Circuit-SAT` counting at `interpolationScale` -/

section ExactCounters

open ComputableInPolyTime

private theorem exists_guardedCircuitAcceptCounter {σ : Signature} [Finite σ.Op]
    (encOp : σ.Op ↪ List Bool) (I : Interpretation σ Bool) {m : ℕ}
    (acc : Fin m → Bool → Bool) (k : ℕ)
    {guard : (Σ n, Circuit σ n m) → Bool}
    (hguard : ComputableInPolyTime guard (Circuit.encCircuit encOp m) encBool)
    (μ : (Σ n, Circuit σ n m) → ℕ) (C D : ℕ)
    (hspec_guard : ∀ c : Σ n, Circuit σ n m, guard c = true →
      c.2.FanInAtMost k ∧ (Compiler.toCNF c.2 I acc).numVars ≤ C * μ c + D) :
    ∃ (count : (Σ n, Circuit σ n m) → ℕ) (A e b : ℕ),
      (∀ c : Σ n, Circuit σ n m, guard c = true → count c = c.2.acceptCount I acc) ∧
      ComputableInO count (Circuit.encCircuit encOp m) encNat
        (fun c => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale (μ c))⌉₊ *
          ((Circuit.encCircuit encOp m c).length + 1) ^ e)
        (fun c => ((Circuit.encCircuit encOp m c).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hspec, hinO⟩ :=
    CountingNativeEndpoint.exists_shiftedCounter_of_polyTime_toCNF (k + 1)
      (computableInPolyTime_toCNF encOp I acc)
      (computableInPolyTime_freeShift encOp I acc)
      hguard μ C D fun c hgc =>
        ⟨fun _ hcl => Compiler.length_le_of_mem_toCNF I acc (hspec_guard c hgc).1 hcl,
          (hspec_guard c hgc).2⟩
  refine ⟨count, A, e, b, fun c hgc => ?_, hinO⟩
  simp only [hspec c, hgc, ↓reduceIte, ← Compiler.acceptCount_eq_two_pow_freeShift_mul_modelCount]

/-- **Subexponential acceptance counting for bounded-fan-in circuits over any finite Boolean
signature.** For every finite signature `σ`, operation encoding `encOp`, Boolean interpretation `I`,
output predicate `acc : Fin m → Bool → Bool`, and fan-in bound `k`, a single native machine
computes `c.2.acceptCount I acc` on every circuit `c` with `c.2.FanInAtMost k`, running in time
`2 ^ (A * interpolationScale c.2.size)` times a polynomial in the encoded circuit length and in
polynomial space. -/
public theorem exists_circuitAcceptCounter {σ : Signature} [Finite σ.Op]
    (encOp : σ.Op ↪ List Bool) (I : Interpretation σ Bool) {m : ℕ}
    (acc : Fin m → Bool → Bool) (k : ℕ) :
    ∃ (count : (Σ n, Circuit σ n m) → ℕ) (A e b : ℕ),
      (∀ c : Σ n, Circuit σ n m, c.2.FanInAtMost k → count c = c.2.acceptCount I acc) ∧
      ComputableInO count (Circuit.encCircuit encOp m) encNat
        (fun c => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale c.2.size)⌉₊ *
          ((Circuit.encCircuit encOp m c).length + 1) ^ e)
        (fun c => ((Circuit.encCircuit encOp m c).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hspec, hinO⟩ := exists_guardedCircuitAcceptCounter encOp I acc k
    (computableInPolyTime_fanInCheck encOp m k) (fun c => c.2.size) k m fun c hgc => by
      have hfan := (fanInCheck_eq_true_iff c).mp hgc
      exact ⟨hfan, Compiler.numVars_toCNF_le I acc hfan⟩
  exact ⟨count, A, e, b, fun c hfan => hspec c ((fanInCheck_eq_true_iff c).mpr hfan), hinO⟩

/-- **Subexponential `#Circuit-SAT` over any finite Boolean signature of bounded arity.** For every
finite signature `σ`, operation encoding `encOp`, Boolean interpretation `I`, and fan-in bound `k`,
one native machine computes the exact number of satisfying inputs `c.2.satCount I` of every
circuit `c : Σ n, Circuit σ n 1` with `c.2.FanInAtMost k`, in time
`2 ^ (A * interpolationScale c.2.size)` times a polynomial in the encoding length and in
polynomial space. -/
public theorem exists_circuitSatCounter {σ : Signature} [Finite σ.Op]
    (encOp : σ.Op ↪ List Bool) (I : Interpretation σ Bool) (k : ℕ) :
    ∃ (count : (Σ n, Circuit σ n 1) → ℕ) (A e b : ℕ),
      (∀ c : Σ n, Circuit σ n 1, c.2.FanInAtMost k → count c = c.2.satCount I) ∧
      ComputableInO count (Circuit.encCircuit encOp 1) encNat
        (fun c => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale c.2.size)⌉₊ *
          ((Circuit.encCircuit encOp 1 c).length + 1) ^ e)
        (fun c => ((Circuit.encCircuit encOp 1 c).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hspec, hinO⟩ :=
    exists_circuitAcceptCounter encOp I (m := 1) (fun _ b => b) k
  refine ⟨count, A, e, b, fun c hfan => ?_, hinO⟩
  rw [c.2.satCount_eq_acceptCount I]
  exact hspec c hfan

/-- **Unconditional subexponential De Morgan `#Circuit-SAT`.** One native machine computes the exact
number of satisfying inputs `c.2.satCount Boolean.interpretation` of every De Morgan circuit `c`
(encoded via `Boolean.encCircuit 1`) in time `2 ^ (A * interpolationScale c.2.size)` times a
polynomial in the encoding length and in polynomial space. -/
public theorem exists_booleanCircuitSatCounter :
    ∃ (count : (Σ n, Circuit Boolean.signature n 1) → ℕ) (A e b : ℕ),
      (∀ c : Σ n, Circuit Boolean.signature n 1,
        count c = c.2.satCount Boolean.interpretation) ∧
      ComputableInO count (Boolean.encCircuit 1) encNat
        (fun c => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale c.2.size)⌉₊ *
          ((Boolean.encCircuit 1 c).length + 1) ^ e)
        (fun c => ((Boolean.encCircuit 1 c).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hspec, hinO⟩ :=
    exists_circuitSatCounter Boolean.encOp Boolean.interpretation 2
  exact ⟨count, A, e, b, fun c => hspec c c.2.fanInAtMost_two, hinO⟩

/-- **Exact-counting extension of Appendix C.1 of [OpenAI2026ETH] (general bounded-arity
signatures).** Whereas Appendix C.1 (p. 51) states only decision for linear-size De Morgan circuits,
this theorem strengthens the result to exact `#Circuit-SAT` over any finite signature `σ`: for every
fan-in bound `k` and size constant `C`, one native machine computes `c.2.satCount I` on every
circuit `c` with `c.2.FanInAtMost k` and `c.2.size ≤ C * c.1 + C`, in time
`2 ^ (A * interpolationScale c.1)` times a polynomial in the encoding length and in polynomial
space. -/
public theorem exists_linearSizeCircuitSatCounter {σ : Signature} [Finite σ.Op]
    (encOp : σ.Op ↪ List Bool) (I : Interpretation σ Bool) (k C : ℕ) :
    ∃ (count : (Σ n, Circuit σ n 1) → ℕ) (A e b : ℕ),
      (∀ c : Σ n, Circuit σ n 1, c.2.FanInAtMost k → c.2.size ≤ C * c.1 + C →
        count c = c.2.satCount I) ∧
      ComputableInO count (Circuit.encCircuit encOp 1) encNat
        (fun c => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale c.1)⌉₊ *
          ((Circuit.encCircuit encOp 1 c).length + 1) ^ e)
        (fun c => ((Circuit.encCircuit encOp 1 c).length + 1) ^ b) := by
  have hguard : ComputableInPolyTime
      (fun c : Σ n, Circuit σ n 1 => fanInCheck k c && linearSizeCheck C c)
      (Circuit.encCircuit encOp 1) encBool :=
    bool_and' (computableInPolyTime_fanInCheck encOp 1 k)
      (computableInPolyTime_linearSizeCheck encOp 1 C)
  obtain ⟨count, A, e, b, hspec, hinO⟩ := exists_guardedCircuitAcceptCounter encOp I
    (m := 1) (fun _ b => b) k hguard Sigma.fst (k * C) (k * C + 1) fun c hgc => by
      simp only [Bool.and_eq_true, fanInCheck_eq_true_iff, linearSizeCheck_eq_true_iff] at hgc
      refine ⟨hgc.1, ?_⟩
      have hnum := Compiler.numVars_toCNF_le I (m := 1) (fun _ b => b) hgc.1
      have hmul := Nat.mul_le_mul_left k hgc.2
      nlinarith
  refine ⟨count, A, e, b, fun c hfan hsize => ?_, hinO⟩
  rw [c.2.satCount_eq_acceptCount I]
  refine hspec c ?_
  simp only [Bool.and_eq_true, fanInCheck_eq_true_iff, linearSizeCheck_eq_true_iff]
  exact ⟨hfan, hsize⟩

/-- **Exact-counting analogue of Appendix C.1 of [OpenAI2026ETH] on linear-size De Morgan circuits**
(`c.2.size ≤ C * c.1 + C`), running in time `2 ^ (A * interpolationScale c.1)` times a polynomial in
the encoding length and in polynomial space. -/
public theorem exists_linearSizeBooleanCircuitSatCounter (C : ℕ) :
    ∃ (count : (Σ n, Circuit Boolean.signature n 1) → ℕ) (A e b : ℕ),
      (∀ c : Σ n, Circuit Boolean.signature n 1, c.2.size ≤ C * c.1 + C →
        count c = c.2.satCount Boolean.interpretation) ∧
      ComputableInO count (Boolean.encCircuit 1) encNat
        (fun c => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale c.1)⌉₊ *
          ((Boolean.encCircuit 1 c).length + 1) ^ e)
        (fun c => ((Boolean.encCircuit 1 c).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hspec, hinO⟩ :=
    exists_linearSizeCircuitSatCounter Boolean.encOp Boolean.interpretation 2 C
  exact ⟨count, A, e, b, fun c hsize => hspec c c.2.fanInAtMost_two hsize, hinO⟩

end ExactCounters

/-! ### Subexponential-time decision corollaries -/

section SubexpDecision

open ComputableInPolyTime

/-- Bounded-fan-in `SignatureCircuitSAT I` over any finite Boolean signature `σ` satisfies
`DecidableInSubexpTime` with respect to gate count `c.2.size` (for every `δ > 0`, some decider runs
in time `O(2 ^ (δ * c.2.size) * (|c| + 1) ^ e)`; see `exists_circuitSatCounter` for a single
machine at the `interpolationScale` rate). -/
public theorem decidableInSubexpTime_fanInSignatureCircuitSAT_size {σ : Signature} [Finite σ.Op]
    (encOp : σ.Op ↪ List Bool) (I : Interpretation σ Bool) (k : ℕ) :
    DecidableInSubexpTime
      {c : Σ n, Circuit σ n 1 | c.2.FanInAtMost k ∧ c ∈ SignatureCircuitSAT I}
      (Circuit.encCircuit encOp 1) (fun c => c.2.size) := by
  set red : (Σ n, Circuit σ n 1) → CNF ℕ :=
    fun c => if fanInCheck k c then Compiler.toSatCNF c.2 I else [[]]
  have hred : ComputableInPolyTime red (Circuit.encCircuit encOp 1) encCNF :=
    (computableInPolyTime_fanInCheck encOp 1 k).ite
      (computableInPolyTime_toSatCNF encOp I) (const [[]])
  refine (CountingNativeEndpoint.decidableInSubexpTime_KSAT (k + 1)).of_reduction hred
    (fun ⟨n, c⟩ => ?_) (c := k + 1) fun c => ?_
  · dsimp only [red]
    by_cases hfan : c.FanInAtMost k
    · have hfc : fanInCheck k ⟨n, c⟩ = true := (fanInCheck_eq_true_iff ⟨n, c⟩).mpr hfan
      simp only [hfc, ↓reduceIte, KSAT, Set.mem_ofPred_eq, hfan, true_and,
        Compiler.satisfiable_toSatCNF_iff]
      exact ⟨fun h => ⟨fun cl hcl => Compiler.length_le_of_mem_toCNF I _ hfan hcl, h⟩,
        fun h => h.2⟩
    · have hfc : fanInCheck k ⟨n, c⟩ = false :=
        Bool.eq_false_iff.mpr fun h => hfan ((fanInCheck_eq_true_iff ⟨n, c⟩).mp h)
      simp only [hfc, Bool.false_eq_true, ↓reduceIte, KSAT, Set.mem_ofPred_eq, hfan, false_and]
      exact ⟨False.elim, fun ⟨_, τ, hτ⟩ => by simp at hτ⟩
  · dsimp only [red]
    split_ifs with hfc
    · have hfan := (fanInCheck_eq_true_iff c).mp hfc
      have hnum := Compiler.numVars_toCNF_le I (fun _ b => b) hfan
      change (Compiler.toCNF c.2 I (fun _ b => b)).numVars ≤ (k + 1) * c.2.size + (k + 1)
      nlinarith
    · simp only [CNF.numVars, CNF.vars, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.map_nil, List.toFinset_nil, Finset.card_empty, Nat.zero_le]

/-- When every operation in a finite signature `σ` has arity at most `k`, full
`SignatureCircuitSAT I` satisfies `DecidableInSubexpTime` with respect to `c.2.size` (for every
`δ > 0`, some decider runs in `O(2 ^ (δ * c.2.size) * (|c| + 1) ^ e)`). -/
public theorem decidableInSubexpTime_signatureCircuitSAT_size {σ : Signature} [Finite σ.Op]
    (encOp : σ.Op ↪ List Bool) (I : Interpretation σ Bool) {k : ℕ}
    (harity : ∀ op : σ.Op, σ.Arity op ≤ k) :
    DecidableInSubexpTime (SignatureCircuitSAT I)
      (Circuit.encCircuit encOp 1) (fun c => c.2.size) := by
  have hall_fan (c : Σ n, Circuit σ n 1) : c.2.FanInAtMost k :=
    Program.fanInAtMost_iff.mpr fun j => harity (c.2.program.lines j).op
  have heq : {c : Σ n, Circuit σ n 1 | c.2.FanInAtMost k ∧ c ∈ SignatureCircuitSAT I} =
      SignatureCircuitSAT I := by
    ext c
    exact ⟨fun h => h.2, fun h => ⟨hall_fan c, h⟩⟩
  rw [← heq]
  exact decidableInSubexpTime_fanInSignatureCircuitSAT_size encOp I k

/-- De Morgan `CircuitSAT` satisfies `DecidableInSubexpTime` with respect to gate count `c.2.size`
(for every `δ > 0`, some decider runs in `O(2 ^ (δ * c.2.size) * (|c| + 1) ^ e)`; see
`exists_booleanCircuitSatCounter` for a single machine at the `interpolationScale` rate). -/
public theorem decidableInSubexpTime_CircuitSAT_size :
    DecidableInSubexpTime CircuitSAT (Boolean.encCircuit 1) (fun c => c.2.size) := by
  refine decidableInSubexpTime_signatureCircuitSAT_size (σ := Boolean.signature)
    Boolean.encOp Boolean.interpretation (k := 2) fun op => ?_
  cases op with
  | const b => cases b <;> decide
  | _ => decide

/-- General-signature extension of Appendix C.1 of [OpenAI2026ETH] (p. 51): satisfiability of
linear-size circuits (`c.2.size ≤ C * n + C`) of fan-in at most `k` over any finite Boolean
signature `σ` satisfies `DecidableInSubexpTime` in the input count `n = c.1` (for every `δ > 0`,
some decider runs in `O(2 ^ (δ * n) * (|c| + 1) ^ e)`; see `exists_linearSizeCircuitSatCounter` for
a single machine at the `interpolationScale` rate). -/
public theorem decidableInSubexpTime_linearSizeSignatureCircuitSAT {σ : Signature} [Finite σ.Op]
    (encOp : σ.Op ↪ List Bool) (I : Interpretation σ Bool) (k C : ℕ) :
    DecidableInSubexpTime
      {c : Σ n, Circuit σ n 1 |
        c.2.FanInAtMost k ∧ c.2.size ≤ C * c.1 + C ∧ c ∈ SignatureCircuitSAT I}
      (Circuit.encCircuit encOp 1) Sigma.fst := by
  set red : (Σ n, Circuit σ n 1) → CNF ℕ :=
    fun c => if fanInCheck k c && linearSizeCheck C c then Compiler.toSatCNF c.2 I else [[]]
  have hguard : ComputableInPolyTime
      (fun c : Σ n, Circuit σ n 1 => fanInCheck k c && linearSizeCheck C c)
      (Circuit.encCircuit encOp 1) encBool :=
    bool_and' (computableInPolyTime_fanInCheck encOp 1 k)
      (computableInPolyTime_linearSizeCheck encOp 1 C)
  have hred : ComputableInPolyTime red (Circuit.encCircuit encOp 1) encCNF :=
    hguard.ite (computableInPolyTime_toSatCNF encOp I) (const [[]])
  refine (CountingNativeEndpoint.decidableInSubexpTime_KSAT (k + 1)).of_reduction hred
    (fun ⟨n, c⟩ => ?_) (c := k * C + k + 1) fun c => ?_
  · dsimp only [red]
    by_cases hcond : c.FanInAtMost k ∧ c.size ≤ C * n + C
    · have hgc : (fanInCheck k ⟨n, c⟩ && linearSizeCheck C ⟨n, c⟩) = true := by
        simp only [Bool.and_eq_true, fanInCheck_eq_true_iff, linearSizeCheck_eq_true_iff]
        exact hcond
      simp only [hgc, ↓reduceIte, KSAT, Set.mem_ofPred_eq, hcond.1, hcond.2, true_and,
        Compiler.satisfiable_toSatCNF_iff]
      exact ⟨fun h => ⟨fun cl hcl => Compiler.length_le_of_mem_toCNF I _ hcond.1 hcl, h⟩,
        fun h => h.2⟩
    · have hgc : (fanInCheck k ⟨n, c⟩ && linearSizeCheck C ⟨n, c⟩) = false := by
        rw [Bool.eq_false_iff]
        intro h
        simp only [Bool.and_eq_true, fanInCheck_eq_true_iff, linearSizeCheck_eq_true_iff] at h
        exact hcond h
      simp only [hgc, Bool.false_eq_true, ↓reduceIte, KSAT, Set.mem_ofPred_eq]
      exact ⟨fun h => absurd ⟨h.1, h.2.1⟩ hcond, fun ⟨_, τ, hτ⟩ => by simp at hτ⟩
  · dsimp only [red]
    split_ifs with hgc
    · simp only [Bool.and_eq_true, fanInCheck_eq_true_iff, linearSizeCheck_eq_true_iff] at hgc
      have hnum := Compiler.numVars_toCNF_le I (fun _ b => b) hgc.1
      have hmul := Nat.mul_le_mul_left k hgc.2
      change (Compiler.toCNF c.2 I (fun _ b => b)).numVars ≤
        (k * C + k + 1) * c.1 + (k * C + k + 1)
      nlinarith
    · simp only [CNF.numVars, CNF.vars, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.map_nil, List.toFinset_nil, Finset.card_empty, Nat.zero_le]

/-- **Appendix C.1 of [OpenAI2026ETH] (p. 51):** satisfiability of linear-size De Morgan circuits
(`c.2.size ≤ C * n + C`) satisfies `DecidableInSubexpTime` in the input count `n = c.1` (for every
`δ > 0`, some decider runs in `O(2 ^ (δ * n) * (|c| + 1) ^ e)`; see
`exists_linearSizeBooleanCircuitSatCounter` for a single machine at the `interpolationScale`
rate). -/
public theorem decidableInSubexpTime_linearSizeCircuitSAT (C : ℕ) :
    DecidableInSubexpTime
      {c : Σ n, Circuit Boolean.signature n 1 | c.2.size ≤ C * c.1 + C ∧ c ∈ CircuitSAT}
      (Boolean.encCircuit 1) Sigma.fst := by
  have heq : {c : Σ n, Circuit Boolean.signature n 1 |
      c.2.FanInAtMost 2 ∧ c.2.size ≤ C * c.1 + C ∧
        c ∈ SignatureCircuitSAT Boolean.interpretation} =
      {c : Σ n, Circuit Boolean.signature n 1 | c.2.size ≤ C * c.1 + C ∧ c ∈ CircuitSAT} := by
    ext c
    simp only [Set.mem_ofPred_eq, signatureCircuitSAT_boolean]
    exact ⟨fun h => h.2, fun h => ⟨c.2.fanInAtMost_two, h⟩⟩
  have h0 := decidableInSubexpTime_linearSizeSignatureCircuitSAT (σ := Boolean.signature)
    Boolean.encOp Boolean.interpretation 2 C
  exact Eq.ndrec (motive := fun s => DecidableInSubexpTime s (Boolean.encCircuit 1) Sigma.fst)
    h0 heq

end SubexpDecision

end Cslib.Complexity.CircuitCounting
