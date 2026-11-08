/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Tseitin
import all Complexity.Computability.Circuit.Boolean.Tseitin
public import Complexity.Computability.Circuit.Boolean.CodeComposition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Actual functional circuit-to-CNF writing

Write the full truth-table constraints of every De Morgan gate and prescribed output bits.
The underlying Tseitin semantics are reused; no reachability deletion or existential-only gate
encoding introduces free auxiliaries. This supplies the binary writing stage for functional
cardinality tests in [ChenJiangZhu2027], Lemma 3.3 and Appendix A.1 (PDF pp. 11, 28).

## Main definitions

* `write`: actual binary gate traversal and full truth-table/output clause writing.
* `wireValues`: the existing circuit trace on its declared input/gate wires.

## Main results

* `write_polytime`: polynomial binary construction, including every literal write.
* `count_extensions`: a unique trace preserves counts with arbitrary original-input predicates.
-/

public section

namespace Cslib.Circuits.Boolean.FunctionalCNF

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Explicit gate/output code, in the existing binary-wire circuit encoding. -/
abbrev Code := List (Op × List ℕ) × List ℕ
/-- Original declaration, circuit code and requested output bits. -/
abbrev Input := ℕ × Code × List Bool
/-- Original input-wire declaration. -/
@[expose] def inputs : Input → ℕ | (n, _, _) => n
/-- Explicit original gate list. -/
@[expose] def gates : Input → List (Op × List ℕ) | (_, (gs, _), _) => gs
/-- Explicit output-wire list. -/
@[expose] def outputs : Input → List ℕ | (_, (_, os), _) => os
/-- Requested output bits. -/
@[expose] def wanted : Input → List Bool | (_, _, bs) => bs
/-- Unary declaration, binary gate/output references and framed output bits. -/
@[expose] def encInput : Input ↪ List Bool :=
  encPair encUnary (encPair encCode (encList encBool))

/-- Three actual clauses for one gate, preserving the reviewed Tseitin ordering. -/
@[expose] def gate (op : Op) (w a b : ℕ) : CNF ℕ :=
  if op = .const false then List.replicate 3 (unitClause (w, false))
  else if op = .const true then List.replicate 3 (unitClause (w, true))
  else if op = .not then
    [[(w, true), (a, true), (a, true)], [(w, false), (a, false), (a, false)],
      [(w, true), (a, true), (a, true)]]
  else if op = .and then
    [[(w, false), (a, true), (a, true)], [(w, false), (b, true), (b, true)],
      [(w, true), (a, false), (b, false)]]
  else
    [[(w, true), (a, false), (a, false)], [(w, true), (b, false), (b, false)],
      [(w, false), (a, true), (b, true)]]

/-- The writer is precisely the existing truth-table encoding. -/
theorem gate_eq (op : Op) (w a b : ℕ) :
    gate op w a b = List.ofFn (tseitinClause op w a b) := by
  cases op with
  | const v => cases v <;> rfl
  | not => rfl
  | and => rfl
  | or => rfl

/-- Actual gate traversal and output-unit writing, without a supplied variable assignment. -/
@[expose] def write (x : Input) : CNF ℕ :=
  ((outputs x).zip (wanted x)).map unitClause ++
    (List.range (gates x).length).flatMap fun j =>
      let (op, args) := (gates x).getD j (.const false, [])
      gate op (inputs x + j) (args.getD 0 0) (args.getD 1 0)

/-- Raw binary writing agrees with the reviewed full Tseitin formula plus prescribed outputs. -/
theorem write_eq (x : Input) : write x =
    ((outputs x).zip (wanted x)).map unitClause ++ tseitinCNF (inputs x) (gates x) := by
  unfold write tseitinCNF
  congr 1
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map]
  congr 1
  funext j
  rw [List.getD_eq_getElem _ _ j.isLt]
  exact gate_eq _ _ _ _

private theorem gate_polytime : ComputableInPolyTime
    (fun p : Op × ℕ × ℕ × ℕ => let (op, w, a, b) := p; gate op w a b)
    (encPair encOp (encPair encNat (encPair encNat encNat)))
    (encList (encList (encPair encNat encBool))) := by
  unfold gate unitClause
  have hrep (v : Bool) : ComputableInPolyTime
      (fun p : Op × ℕ × ℕ × ℕ => List.replicate 3 [(p.2.1, v), (p.2.1, v), (p.2.1, v)])
      (encPair encOp (encPair encNat (encPair encNat encNat)))
      (encList (encList (encPair encNat encBool))) := by fun_prop
  fun_prop

/-- Every binary gate, index lookup and literal write has a polynomial-time machine certificate. -/
@[fun_prop] theorem write_polytime : ComputableInPolyTime write encInput
    (encList (encList (encPair encNat encBool))) := by
  have hn : ComputableInPolyTime inputs encInput encUnary := by unfold inputs encInput; fun_prop
  have hg : ComputableInPolyTime gates encInput (encList encGate) := by
    unfold gates encInput encCode Circuit.encCode; fun_prop
  have ho : ComputableInPolyTime outputs encInput (encList encNat) := by
    unfold outputs encInput encCode Circuit.encCode; fun_prop
  have hw : ComputableInPolyTime wanted encInput (encList encBool) := by
    unfold wanted encInput; fun_prop
  have hu : ComputableInPolyTime
      (fun p : ℕ × Bool => unitClause p) (encPair encNat encBool)
      (encList (encPair encNat encBool)) := by unfold unitClause; fun_prop
  have hz := (ComputableInPolyTime.zip encNat encBool).comp (ho.prod hw)
  have hout := hu.map.comp hz
  have hl := (ComputableInPolyTime.length_list encGate).comp hg
  let ei := encPair encInput encUnary
  have hp := ComputableInPolyTime.fst encInput encUnary
  have hj := ComputableInPolyTime.snd encInput encUnary
  have hget := ComputableInPolyTime.listGetDWithInput (hg.comp hp) hj (.const false, [])
  have hindex : ComputableInPolyTime (fun p : Input × ℕ => inputs p.1 + p.2) ei encNat :=
    ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.unary_add.comp
      ((hn.comp hp).prod hj))
  have hargs0 := ComputableInPolyTime.listGetDWithInput hget.snd' (.const 0) 0
  have hargs1 := ComputableInPolyTime.listGetDWithInput hget.snd' (.const 1) 0
  have hbody := gate_polytime.comp (hget.fst'.prod (hindex.prod (hargs0.prod hargs1)))
  exact (ComputableInPolyTime.listAppend' hout
    (ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hl) hbody)).of_enc_eq
      fun _ => rfl

/-- The actual raw payload obtained from a circuit and its prescribed output bits. -/
@[expose] def ofCircuit {n m : ℕ} (c : Circuit signature n m) (bs : Fin m → Bool) : Input :=
  (n, c.code, List.ofFn bs)

/-- The existing circuit trace restricted to declared input/gate wires, omitting output copies. -/
@[expose] def wireValues {n m : ℕ} (c : Circuit signature n m) (x : Fin n → Bool) :
    Fin (n + c.size) → Bool := c.trace interpretation x ∘ Fin.castAdd m

private theorem trace_code {n m : ℕ} (c : Circuit signature n m) (x : Fin n → Bool) :
    List.ofFn (wireValues c x) = evalCode interpretation false (List.ofFn x) c.code.1 := by
  have he : wireValues c x = Fin.append x (c.program.eval interpretation x) := by
    funext j
    simp only [wireValues, Circuit.trace, Function.comp_def, Fin.addCases_left]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.addCases_left, Fin.append_left]
    · simp only [Fin.addCases_right, Fin.append_right]
  rw [he, Circuit.code, Program.evalCode_code, ← List.ofFn_fin_append]

private theorem trace_output {n m : ℕ} (c : Circuit signature n m)
    (x : Fin n → Bool) (j : Fin m) :
    wireValues c x ⟨(c.outputs j).toNat, (c.outputs j).toNat_lt⟩ = c.eval interpretation x j := by
  rw [Circuit.eval_eq_getD c interpretation false x j, ← trace_code]
  exact (List.getD_ofFn (wireValues c x) ⟨(c.outputs j).toNat, (c.outputs j).toNat_lt⟩ false).symm

private theorem output_units {n m : ℕ} (c : Circuit signature n m) (bs : Fin m → Bool)
    (σ : ℕ → Bool) :
    CNF.eval σ (((outputs (ofCircuit c bs)).zip (wanted (ofCircuit c bs))).map unitClause) =
      true ↔ ∀ j, σ (c.outputs j).toNat = bs j := by
  have hz : ((List.ofFn fun j => (c.outputs j).toNat).zip (List.ofFn bs)) =
      List.ofFn (fun j => ((c.outputs j).toNat, bs j)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_zip, List.getElem_ofFn]
  simp only [outputs, wanted, ofCircuit, Circuit.code, hz, CNF.eval_eq_true_iff,
    List.mem_map, List.mem_ofFn, forall_exists_index, and_imp, forall_apply_eq_imp_iff,
    eval_unitClause, Literal.eval_eq_true_iff]

/-- Full truth-table constraints are functional on all declared wires. Every accepted original
input has exactly its circuit trace, and the prescribed outputs hold precisely on that trace. -/
theorem eval_write_iff {n m : ℕ} (c : Circuit signature n m) (bs : Fin m → Bool)
    (x : Fin n → Bool) (σ : ℕ → Bool) (hin : ∀ i : Fin n, σ i.val = x i) :
    (write (ofCircuit c bs)).eval σ = true ↔
      (∀ j : Fin (n + c.size), σ j.val = wireValues c x j) ∧ c.eval interpretation x = bs := by
  have hc : Program.IsCodeFrom signature n 0 c.code.1 :=
    Program.isSome_ofCode_iff.mp (by rw [Circuit.code, Program.ofCode_code]; rfl)
  have hx : (List.ofFn fun i : Fin n => σ i) = List.ofFn x := by
    congr 1
    funext i
    exact hin i
  have ht : (tseitinCNF n c.code.1).eval σ = true ↔
      ∀ j : Fin (n + c.size), σ j.val = wireValues c x j := by
    rw [eval_tseitinCNF_eq_true_iff_evalCode hc, hx, ← trace_code,
      Circuit.length_code_fst]
    constructor
    · intro h j
      simpa only [List.getD_ofFn] using h j.val j.isLt
    · intro h j hj
      exact (h ⟨j, hj⟩).trans (List.getD_ofFn (wireValues c x) ⟨j, hj⟩ false).symm
  rw [write_eq, CNF.eval_append, Bool.and_eq_true, output_units]
  change (∀ j, σ (c.outputs j).toNat = bs j) ∧ (tseitinCNF n c.code.1).eval σ = true ↔ _
  rw [ht]
  constructor
  · rintro ⟨ho, htrace⟩
    refine ⟨htrace, ?_⟩
    funext j
    rw [← ho j, htrace ⟨(c.outputs j).toNat, (c.outputs j).toNat_lt⟩, trace_output]
  · rintro ⟨htrace, ho⟩
    refine ⟨fun j => ?_, htrace⟩
    rw [htrace ⟨(c.outputs j).toNat, (c.outputs j).toNat_lt⟩, trace_output, ho]

/-- The declared input prefix of the existing full wire trace is the original assignment. -/
theorem wireValues_input {n m : ℕ} (c : Circuit signature n m) (x : Fin n → Bool)
    (i : Fin n) : wireValues c x (Fin.castAdd c.size i) = x i := by
  simp only [wireValues, Circuit.trace, Function.comp_def, Fin.addCases_left]

open Classical in
/-- Full functional CNF extensions preserve an arbitrary predicate on the original inputs.
This counts finite input/gate assignments, without supplied satisfying gate values. -/
theorem count_extensions {n m : ℕ} (c : Circuit signature n m) (bs : Fin m → Bool)
    (P : (Fin n → Bool) → Prop) :
    Fintype.card {y : Fin (n + c.size) → Bool //
      (write (ofCircuit c bs)).eval
        (Function.extend Fin.val y (fun _ => false)) = true ∧
        P (fun i => y (Fin.castAdd c.size i))} =
      Fintype.card {x : Fin n → Bool // c.eval interpretation x = bs ∧ P x} := by
  let restrict (y : Fin (n + c.size) → Bool) : Fin n → Bool :=
    fun i => y (Fin.castAdd c.size i)
  have he (y : Fin (n + c.size) → Bool) (j : Fin (n + c.size)) :
      Function.extend Fin.val y (fun _ => false) j.val = y j :=
    Fin.val_injective.extend_apply _ _ _
  have hf (y : Fin (n + c.size) → Bool) := eval_write_iff c bs (restrict y)
    (Function.extend Fin.val y (fun _ => false)) (fun i =>
      he y (Fin.castAdd c.size i))
  have hr (x : Fin n → Bool) : restrict (wireValues c x) = x := by
    funext i
    exact wireValues_input c x i
  let f : {y : Fin (n + c.size) → Bool //
      (write (ofCircuit c bs)).eval
        (Function.extend Fin.val y (fun _ => false)) = true ∧
        P (restrict y)} →
      {x : Fin n → Bool // c.eval interpretation x = bs ∧ P x} :=
    fun y => ⟨restrict y.val, (hf y.val).mp y.property.1 |>.2, y.property.2⟩
  let g : {x : Fin n → Bool // c.eval interpretation x = bs ∧ P x} →
      {y : Fin (n + c.size) → Bool //
        (write (ofCircuit c bs)).eval
        (Function.extend Fin.val y (fun _ => false)) = true ∧
          P (restrict y)} := fun x => ⟨wireValues c x.val, by
            apply (hf _).mpr
            rw [hr]
            exact ⟨fun j => he _ j, x.property.1⟩, by rw [hr]; exact x.property.2⟩
  apply Fintype.card_congr
  refine ⟨f, g, ?_, ?_⟩
  · intro y
    apply Subtype.ext
    funext j
    exact ((he y.val j).symm.trans (((hf y.val).mp y.property.1).1 j)).symm
  · intro x
    apply Subtype.ext
    exact hr x.val

/-- Actual CNF size is linear in all gates and prescribed outputs. -/
theorem write_length {n m : ℕ} (c : Circuit signature n m) (bs : Fin m → Bool) :
    (write (ofCircuit c bs)).length = m + 3 * c.size := by
  rw [write_eq]
  simp only [ofCircuit, outputs, wanted, gates, inputs, Circuit.code, List.length_append,
    List.length_map, List.length_zip, List.length_ofFn, min_self, tseitinCNF,
    List.length_flatMap, gateClauses, List.length_ofFn, List.map_const', List.sum_replicate,
    List.length_finRange, smul_eq_mul]
  have hlen : c.program.code.length = c.size := Program.length_code c.program
  omega

/-- Every actual emitted literal has width three and a declared input/gate-wire label. -/
theorem write_bounds {n m : ℕ} (c : Circuit signature n m) (bs : Fin m → Bool)
    (a : Clause ℕ) (ha : a ∈ write (ofCircuit c bs)) :
    a.length = 3 ∧ ∀ l ∈ a, l.1 < n + c.size := by
  have hc : Program.IsCodeFrom signature n 0 c.code.1 :=
    Program.isSome_ofCode_iff.mp (by rw [Circuit.code, Program.ofCode_code]; rfl)
  rw [write_eq] at ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    have ho := (List.of_mem_zip hl).1
    simp only [ofCircuit, outputs, Circuit.code, List.mem_ofFn] at ho
    obtain ⟨j, hj⟩ := ho
    refine ⟨rfl, ?_⟩
    intro v hv
    have hv' : v = l := by simpa only [unitClause, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false, or_self] using hv
    rw [hv', ← hj]
    exact (c.outputs j).toNat_lt
  · change a ∈ tseitinCNF n c.code.1 at ha
    simp only [tseitinCNF, List.mem_flatMap, List.mem_finRange, true_and,
      gateClauses, List.mem_ofFn] at ha
    obtain ⟨j, k, rfl⟩ := ha
    refine ⟨length_tseitinClause _ _ _ _ _, ?_⟩
    have hargs := getD_lt_of_isCodeFrom hc j.isLt
    have hw : n + j.val < n + c.size := by
      have hj := j.isLt
      have hlen := Circuit.length_code_fst c
      omega
    intro l hl
    generalize hop : c.code.1[j.val] = op at hargs hl
    rcases op with ⟨op, args⟩
    cases op <;> fin_cases k <;>
      simp only [tseitinClause, List.mem_cons, List.not_mem_nil,
        or_false] at hl <;>
      rcases hl with rfl | rfl | rfl
    all_goals first
    | exact hw
    | exact (hargs.1 (by dsimp only [signature]; omega)).trans (by omega)
    |
      exact (hargs.2 (by dsimp only [signature]; omega)).trans (by omega)

end Cslib.Circuits.Boolean.FunctionalCNF
