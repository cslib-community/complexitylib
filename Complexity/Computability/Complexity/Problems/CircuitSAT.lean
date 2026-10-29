/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.EvaluationTime
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Circuit satisfiability

`CircuitSAT` is the set of De Morgan circuits with one output that output true on some input
[Arora and Barak, Section 6.1][AroraBarak09]. Circuits are encoded by
`Cslib.Circuits.Boolean.encCircuit`: the number `n` of inputs in unary, then the gates in program
order with wire numbers in binary, then the output wire. Since `n` is written in unary, the
encoding is at least `n` bits long, and an assignment to the inputs fits in a certificate as long
as the encoding.

`CircuitSAT` is `NP`-complete (`Cslib.Complexity.CircuitSAT_npComplete`). It is in `NP`: the
verifier evaluates the circuit on the first `n` bits of the certificate. It is `NP`-hard because
`SAT` reduces to it (`Cslib.Complexity.SAT.polyTimeReducible_CircuitSAT`) and `SAT` is
`NP`-complete by the Cook–Levin theorem. The circuit of a formula (`Cslib.Complexity.SAT.toCircuit`)
has one input for each literal occurrence; a variable is read at the input of its first
occurrence, as for the certificates of `SAT.verifier`. Its gates come in blocks of three, one block
for each literal and one for the end of each clause, which keep the disjunction of the current
clause and the conjunction of the finished clauses at fixed offsets from the end.

## Main definitions

* `Cslib.Complexity.SignatureCircuitSAT`: the satisfiable single-output circuits over an arbitrary
  Boolean signature and interpretation.
* `Cslib.Complexity.CircuitSAT`: the satisfiable De Morgan circuits with one output.
* `Cslib.Complexity.CircuitSAT.verifier`: evaluation on the first bits of a certificate.
* `Cslib.Complexity.SAT.toCircuit`: the circuit of a formula in conjunctive normal form.

## Main results

* `Cslib.Complexity.signatureCircuitSAT_boolean`: specializing `SignatureCircuitSAT` to the De
  Morgan basis recovers `CircuitSAT`.
* `Cslib.Complexity.CircuitSAT.mem_NP`: circuit satisfiability is in `NP`.
* `Cslib.Complexity.SAT.toCircuit_mem_CircuitSAT_iff`: the circuit of a formula is satisfiable
  exactly when the formula is.
* `Cslib.Complexity.SAT.polyTimeReducible_CircuitSAT`: `SAT` reduces to `CircuitSAT` in
  polynomial time.
* `Cslib.Complexity.CircuitSAT_npHard`, `Cslib.Complexity.CircuitSAT_npComplete`: circuit
  satisfiability is `NP`-hard and `NP`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM Cslib.Logic.PL

/-- **Circuit satisfiability over an arbitrary Boolean signature**: the single-output circuits
over `σ` that output `true` under `I` on some input. -/
def SignatureCircuitSAT {σ : Signature} (I : Interpretation σ Bool) :
    Set (Σ n, Circuit σ n 1) :=
  {c | ∃ x : BitString c.1, c.2.eval I x 0 = true}

/-- Membership in `SignatureCircuitSAT I`. -/
theorem mem_SignatureCircuitSAT {σ : Signature} {I : Interpretation σ Bool}
    {c : Σ n, Circuit σ n 1} :
    c ∈ SignatureCircuitSAT I ↔ ∃ x : BitString c.1, c.2.eval I x 0 = true :=
  Iff.rfl

/-- **Circuit satisfiability**: the De Morgan circuits with one output that output true on some
input [Arora and Barak, Section 6.1][AroraBarak09]. -/
def CircuitSAT : Set (Σ n, Circuit signature n 1) :=
  {c | ∃ x : BitString c.1, c.2.eval interpretation x 0 = true}

/-- Specializing `SignatureCircuitSAT` to the De Morgan basis recovers `CircuitSAT`. -/
@[simp]
theorem signatureCircuitSAT_boolean :
    SignatureCircuitSAT interpretation = CircuitSAT := rfl

theorem mem_CircuitSAT {c : Σ n, Circuit signature n 1} :
    c ∈ CircuitSAT ↔ ∃ x : BitString c.1, c.2.eval interpretation x 0 = true :=
  Iff.rfl

namespace CircuitSAT

/-! ### Membership in `NP` -/

/-- The verifier for `CircuitSAT`: evaluate the circuit on the first bits of the certificate,
reading missing bits as `false`. -/
def verifier (p : (Σ n, Circuit signature n 1) × List Bool) : Bool :=
  p.1.2.eval interpretation (fun i => p.2.getD i false) 0

/-- `CircuitSAT.verifier` verifies `CircuitSAT` with certificates as long as the encoded
circuit. -/
theorem isVerifier : IsVerifier (encCircuit 1) Polynomial.X verifier CircuitSAT := by
  refine IsVerifier.of_padding (fun c w _ hw => ⟨_, hw⟩) fun c ⟨x, hx⟩ => ?_
  refine ⟨List.ofFn x, by simpa using le_length_encCircuit c, fun k => ?_⟩
  rw [verifier]
  convert hx using 3 with i
  rw [List.getD_append _ _ _ _ (by simp), List.getD_ofFn]

/-- The verifier evaluates the code of the circuit on the first bits of the certificate. -/
private theorem verifier_eq_evalOutput (p : (Σ n, Circuit signature n 1) × List Bool) :
    verifier p = evalOutput ((List.range p.1.1).map fun i => p.2.getD i false) p.1.2.code.1
      (p.1.2.code.2.headD 0) := by
  have h : List.ofFn (fun i : Fin p.1.1 => p.2.getD i false) =
      (List.range p.1.1).map fun i => p.2.getD i false :=
    List.ext_getElem (by simp) fun _ _ _ => by simp
  rw [verifier, Circuit.eval_eq_evalOutput, h]
  rfl

/-- The `CircuitSAT` verifier is polynomial-time, on certificates of arbitrary length. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair (encCircuit 1) encBits) encBool := by
  have hraw : ComputableInPolyTime
      (fun p : (Σ n, Circuit signature n 1) × List Bool => ((p.1.1, p.1.2.code), p.2))
      (encPair (encCircuit 1) encBits) (encPair (encPair encUnary encCode) encBits) :=
    .of_eq fun _ => rfl
  have hout : ComputableInPolyTime
      (fun r : (ℕ × (List (Op × List ℕ) × List ℕ)) × List Bool =>
        evalOutput ((List.range r.1.1).map fun i => r.2.getD i false) r.1.2.1 (r.1.2.2.headD 0))
      (encPair (encPair encUnary encCode) encBits) encBool := by
    apply computableInPolyTime_evalOutput <;> fun_prop
  rw [funext verifier_eq_evalOutput]
  exact hout.comp hraw

/-- **Circuit satisfiability is in `NP`**, with certificates as long as the encoded circuit. -/
theorem mem_NP : CircuitSAT ∈ NP (encCircuit 1) :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end CircuitSAT

/-! ### The circuit of a formula -/

namespace SAT

/-- The instructions building the circuit of a formula: each literal of each clause, flagged
`false`, and after each clause an end marker flagged `true` (with a placeholder literal). -/
def circuitSteps (φ : CNF ℕ) : List (Literal ℕ × Bool) :=
  φ.flatMap fun c => c.map (·, false) ++ [((0, false), true)]

/-- The three gates of one instruction, when the three gates before it are the wires `p`, `p + 1`
and `p + 2`, the last two holding the disjunction of the current clause so far and the
conjunction of the finished clauses. For the literal `(v, b)` read at input `i`, the gates compute
the literal, add it to the clause and copy the conjunction. At the end of a clause they compute
the conjunction with the clause, restart the clause at `false` and copy the conjunction. -/
def circuitBlock (p i : ℕ) (b e : Bool) : List (Op × List ℕ) :=
  if e then [(.and, [p + 2, p + 1]), (.const false, []), (.or, [p + 3, p + 3])]
  else [if b then (.or, [i, i]) else (.not, [i]), (.or, [p + 1, p + 3]), (.and, [p + 2, p + 2])]

/-- The gates of the circuit of a formula with `n` literal occurrences: three constant gates
starting the clause at `false` and the conjunction at `true`, then the block of each instruction.
The block of instruction `t` follows the gates `3 t`, `3 t + 1`, `3 t + 2`, which are the wires
`n + 3 t`, `n + 3 t + 1` and `n + 3 t + 2`. -/
def circuitGates (φ : CNF ℕ) : List (Op × List ℕ) :=
  [(.const false, []), (.const false, []), (.const true, [])] ++
    (circuitSteps φ).zipIdx.flatMap fun s =>
      circuitBlock (φ.vars.length + 3 * s.2) (φ.vars.idxOf s.1.1.1) s.1.1.2 s.1.2

/-- The code of the circuit of a formula: its gates and, as output, the last conjunction. -/
def circuitCode (φ : CNF ℕ) : List (Op × List ℕ) × List ℕ :=
  (circuitGates φ, [φ.vars.length + 3 * (circuitSteps φ).length + 2])

private theorem length_circuitBlock (p i : ℕ) (b e : Bool) : (circuitBlock p i b e).length = 3 := by
  unfold circuitBlock
  split <;> rfl

/-- The circuit of a formula has three gates for each instruction, and three more. -/
private theorem length_circuitGates (φ : CNF ℕ) :
    (circuitGates φ).length = 3 * (circuitSteps φ).length + 3 := by
  rw [circuitGates, List.length_append, List.length_flatMap]
  simp only [length_circuitBlock, List.map_const', List.sum_replicate, List.length_zipIdx,
    smul_eq_mul]
  simp only [List.length_cons, List.length_nil]
  omega

private theorem isCodeFrom_circuitBlock {n k i : ℕ} (b e : Bool) (hi : e = false → i < n) :
    Program.IsCodeFrom signature n (3 * k + 3) (circuitBlock (n + 3 * k) i b e) := by
  cases e
  · have hi := hi rfl
    cases b <;>
      refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      (intro _ h; simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil,
        or_false, or_self] at h;
        rcases h with rfl | rfl <;> omega)
  · refine ⟨⟨rfl, ?_⟩, ⟨rfl, nofun⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
      (intro _ h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h;
        rcases h with rfl | rfl <;> omega)

private theorem isCodeFrom_circuitBlocks (φ : CNF ℕ) (steps : List (Literal ℕ × Bool)) (k : ℕ)
    (h : ∀ s ∈ steps, s.2 = false → s.1.1 ∈ φ.vars) :
    Program.IsCodeFrom signature φ.vars.length (3 * k + 3) ((steps.zipIdx k).flatMap fun s =>
      circuitBlock (φ.vars.length + 3 * s.2) (φ.vars.idxOf s.1.1.1) s.1.1.2 s.1.2) := by
  induction steps generalizing k with
  | nil => simp [Program.IsCodeFrom]
  | cons s steps ih =>
    rw [List.zipIdx_cons, List.flatMap_cons, Program.isCodeFrom_append]
    refine ⟨isCodeFrom_circuitBlock _ _ fun he =>
      List.idxOf_lt_length_iff.2 (h s (List.mem_cons_self ..) he), ?_⟩
    have := ih (k + 1) fun s' hs' => h s' (List.mem_cons_of_mem _ hs')
    simp only [circuitBlock] at this ⊢
    split_ifs <;> simpa [Nat.mul_add, Nat.add_assoc] using this

/-- Every literal instruction reads a variable of the formula. -/
private theorem mem_vars_of_mem_circuitSteps {φ : CNF ℕ} {s : Literal ℕ × Bool}
    (hs : s ∈ circuitSteps φ) (he : s.2 = false) : s.1.1 ∈ φ.vars := by
  obtain ⟨c, hc, hs⟩ := List.mem_flatMap.1 hs
  rcases List.mem_append.1 hs with hs | hs
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hs
    exact List.mem_map.2 ⟨l, List.mem_flatten.2 ⟨c, hc, hl⟩, rfl⟩
  · simp [List.mem_singleton.1 hs] at he

/-- The circuit code of a formula is the code of a circuit with one output. -/
theorem isSome_ofCode_circuitCode (φ : CNF ℕ) :
    (Circuit.ofCode φ.vars.length 1 (circuitCode φ) : Option (Circuit signature _ 1)).isSome := by
  rw [Circuit.isSome_ofCode_iff]
  refine ⟨?_, rfl, ?_⟩
  · rw [circuitCode, circuitGates, Program.isCodeFrom_append]
    refine ⟨by simp [Program.IsCodeFrom], ?_⟩
    simpa using isCodeFrom_circuitBlocks φ (circuitSteps φ) 0 fun s hs =>
      mem_vars_of_mem_circuitSteps hs
  · simp only [circuitCode, length_circuitGates, List.mem_singleton, forall_eq]
    omega

/-- **The circuit of a formula**: one input for each literal occurrence, and the gates of
`circuitCode`. -/
def toCircuit (φ : CNF ℕ) : Σ n, Circuit signature n 1 :=
  ⟨φ.vars.length, (Circuit.ofCode _ 1 (circuitCode φ)).get (isSome_ofCode_circuitCode φ)⟩

private theorem code_toCircuit (φ : CNF ℕ) : (toCircuit φ).2.code = circuitCode φ :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

/-! ### Correctness of the circuit of a formula -/

/-- The values of the last two gates after an instruction: the disjunction of the current clause
so far and the conjunction of the finished clauses. -/
private def circuitState (τ : ℕ → Bool) (s : Bool × Bool) (t : Literal ℕ × Bool) : Bool × Bool :=
  if t.2 then (false, s.2 && s.1) else (s.1 || t.1.eval τ, s.2)

private theorem evalCode_circuitBlock (V : List Bool) (p i : ℕ) (b e : Bool)
    (hV : V.length = p + 3) (hi : e = false → i < p) :
    evalCode interpretation false V (circuitBlock p i b e) = V ++ (if e then
      [V.getD (p + 2) false && V.getD (p + 1) false, false,
        V.getD (p + 2) false && V.getD (p + 1) false]
      else [V.getD i false == b, V.getD (p + 1) false || (V.getD i false == b),
        V.getD (p + 2) false]) := by
  cases e
  · have hi := hi rfl
    cases b <;>
    simp [circuitBlock, evalCode, interpretation, hV, show i < p + 3 by omega,
      show p + 1 < p + 3 by omega, show p + 2 < p + 3 by omega]
  · simp [circuitBlock, evalCode, interpretation, hV]

/-- The blocks of instructions `k, k + 1, …` keep the state of `circuitState`: after them, the
last gate holds the conjunction computed from the state before them. -/
private theorem evalCode_flatMap (φ : CNF ℕ) (x : List Bool) (hx : x.length = φ.vars.length)
    (steps : List (Literal ℕ × Bool)) (hsteps : ∀ t ∈ steps, t.2 = false → t.1.1 ∈ φ.vars)
    (k : ℕ) (V : List Bool) (s : Bool × Bool) (hV : V.length = φ.vars.length + 3 * k + 3)
    (hx' : x <+: V) (h₁ : V.getD (φ.vars.length + 3 * k + 1) false = s.1)
    (h₂ : V.getD (φ.vars.length + 3 * k + 2) false = s.2) :
    (evalCode interpretation false V ((steps.zipIdx k).flatMap fun s =>
      circuitBlock (φ.vars.length + 3 * s.2) (φ.vars.idxOf s.1.1.1) s.1.1.2 s.1.2)).getD
      (φ.vars.length + 3 * (k + steps.length) + 2) false =
      (steps.foldl (circuitState (assignment φ x)) s).2 := by
  induction steps generalizing k V s with
  | nil =>
    rw [List.zipIdx_nil, List.flatMap_nil, evalCode_nil]
    simpa using h₂
  | cons t steps ih =>
    obtain ⟨⟨v, b⟩, e⟩ := t
    have hsteps' := fun t ht => hsteps t (List.mem_cons_of_mem _ ht)
    have hv : e = false → φ.vars.idxOf v < φ.vars.length := fun he =>
      List.idxOf_lt_length_iff.2 (hsteps _ (List.mem_cons_self ..) he)
    rw [List.zipIdx_cons, List.flatMap_cons, evalCode_append, List.foldl_cons, List.length_cons,
      evalCode_circuitBlock V (φ.vars.length + 3 * k) (φ.vars.idxOf v) b e hV
        fun he => by have := hv he; omega,
      show k + (steps.length + 1) = k + 1 + steps.length by ring]
    have hread : e = false → V.getD (φ.vars.idxOf v) false = assignment φ x v := fun he => by
      have h := hv he
      rw [assignment, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
        hx'.getElem]
    refine ih hsteps' (k + 1) _ _ ?_ (hx'.trans (List.prefix_append _ _)) ?_ ?_
    · cases e <;> simp [hV] <;> omega
    · rw [show φ.vars.length + 3 * (k + 1) + 1 = V.length + 1 by omega,
        List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, h₁]
      cases e
      · have h := hread rfl
        rw [List.getD_eq_getElem?_getD] at h
        simp [circuitState, h]
      · simp [circuitState]
    · rw [show φ.vars.length + 3 * (k + 1) + 2 = V.length + 2 by omega,
        List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left, h₁, h₂]
      cases e <;> simp [circuitState]

private theorem foldl_circuitState_clause (τ : ℕ → Bool) (c : Clause ℕ) (a g : Bool) :
    (c.map (·, false)).foldl (circuitState τ) (a, g) = (a || c.eval τ, g) := by
  induction c generalizing a with
  | nil => simp
  | cons l c ih => simp [circuitState, ih, Bool.or_assoc]

private theorem foldl_circuitState (τ : ℕ → Bool) (φ : CNF ℕ) (g : Bool) :
    (circuitSteps φ).foldl (circuitState τ) (false, g) = (false, g && φ.eval τ) := by
  induction φ generalizing g with
  | nil => simp [circuitSteps]
  | cons c φ ih =>
    simp only [circuitSteps, List.flatMap_cons, List.foldl_append, foldl_circuitState_clause,
      Bool.false_or] at ih ⊢
    simp [circuitState, ih, Bool.and_assoc]

/-- **The circuit of a formula evaluates it**: on input `x`, it outputs the value of the formula
under the assignment giving each variable the input bit at its first occurrence
(`SAT.assignment`). -/
theorem eval_toCircuit (φ : CNF ℕ) (x : BitString (toCircuit φ).1) :
    (toCircuit φ).2.eval interpretation x 0 = φ.eval (assignment φ (List.ofFn x)) := by
  rw [Circuit.eval_eq_evalOutput]
  have hcode := code_toCircuit φ
  have hout : ((toCircuit φ).2.outputs 0).toNat =
      φ.vars.length + 3 * (circuitSteps φ).length + 2 := by
    have := congrArg (fun c => c.2.headD 0) hcode
    simpa [Circuit.code, circuitCode] using this
  rw [hout, show (toCircuit φ).2.code.1 = circuitGates φ by rw [hcode]; rfl, evalOutput,
    circuitGates, evalCode_append]
  have hinit : evalCode interpretation false (List.ofFn x)
      [(Op.const false, []), (Op.const false, []), (Op.const true, [])] =
      List.ofFn x ++ [false, false, true] := by
    simp [evalCode, interpretation]
  rw [hinit]
  have hn : (List.ofFn x).length = φ.vars.length := List.length_ofFn
  have := evalCode_flatMap φ (List.ofFn x) hn (circuitSteps φ)
    (fun t ht => mem_vars_of_mem_circuitSteps ht) 0 (List.ofFn x ++ [false, false, true])
    (false, true) (by simp only [List.length_append, hn]; rfl) (List.prefix_append _ _)
    (by rw [← hn, List.getD_append_right _ _ _ _ (by omega)]; simp)
    (by rw [← hn, List.getD_append_right _ _ _ _ (by omega)]; simp)
  rw [foldl_circuitState, Bool.true_and] at this
  simpa using this

/-- The circuit of a formula is satisfiable exactly when the formula is. -/
theorem toCircuit_mem_CircuitSAT_iff (φ : CNF ℕ) : toCircuit φ ∈ CircuitSAT ↔ φ ∈ SAT := by
  rw [mem_CircuitSAT, mem_SAT]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, (eval_toCircuit φ x).symm.trans hx⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨fun i => τ (φ.vars[i.val]'i.isLt), ?_⟩
    rw [eval_toCircuit, CNF.eval_congr fun v hv => ?_]
    · exact hτ
    · have hlt : φ.vars.idxOf v < φ.vars.length := List.idxOf_lt_length_iff.2 hv
      rw [assignment]
      exact (List.getD_ofFn_of_lt _ hlt _).trans (congrArg τ (List.getElem_idxOf hlt))

/-! ### The reduction is polynomial-time -/

open ComputableInPolyTime

/-- Listing the instructions of the circuit of a formula is polynomial-time. -/
@[local fun_prop]
private theorem computableInPolyTime_circuitSteps
    : ComputableInPolyTime circuitSteps encCNF
    (encList (encPair (encPair encNat encBool) encBool)) := by
  unfold circuitSteps encCNF
  fun_prop

/-- Writing the block of an instruction is polynomial-time, from the position `p` and the input
`i` in unary; the gates use their binary numbers. -/
private theorem computableInPolyTime_circuitBlock :
    ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × Bool) × Bool => circuitBlock q.1.1.1 q.1.1.2 q.1.2 q.2)
      (encPair (encPair (encPair encUnary encUnary) encBool) encBool) (encList encGate) := by
  have hp (c : ℕ) : ComputableInPolyTime (fun q : ((ℕ × ℕ) × Bool) × Bool => q.1.1.1 + c)
      (encPair (encPair (encPair encUnary encUnary) encBool) encBool) encNat :=
    unary_to_binary.comp (unary_add.comp ((fst _ _).fst'.fst'.prod (const c)))
  have hi : ComputableInPolyTime (fun q : ((ℕ × ℕ) × Bool) × Bool => q.1.1.2)
      (encPair (encPair (encPair encUnary encUnary) encBool) encBool) encNat :=
    unary_to_binary.comp (fst _ _).fst'.snd'
  have hgate (op : Op) {args : ((ℕ × ℕ) × Bool) × Bool → List ℕ}
      (h : ComputableInPolyTime args
        (encPair (encPair (encPair encUnary encUnary) encBool) encBool) (encList encNat)) :
      ComputableInPolyTime (fun q => (op, args q))
        (encPair (encPair (encPair encUnary encUnary) encBool) encBool) encGate :=
    (const op).prod h
  have hnil {β : Type} (enc : β ↪ List Bool) : ComputableInPolyTime
      (fun _ : ((ℕ × ℕ) × Bool) × Bool => ([] : List β))
      (encPair (encPair (encPair encUnary encUnary) encBool) encBool) (encList enc) := const []
  unfold circuitBlock
  refine ite' (snd _ _) ?_ ?_
  · exact cons' (hgate .and (cons' (hp 2) (cons' (hp 1) (hnil _))))
      (cons' (hgate (.const false) (hnil _))
        (cons' (hgate .or (cons' (hp 3) (cons' (hp 3) (hnil _)))) (hnil _)))
  · exact cons' (ite' (fst _ _).snd' (hgate .or (cons' hi (cons' hi (hnil _))))
        (hgate .not (cons' hi (hnil _))))
      (cons' (hgate .or (cons' (hp 1) (cons' (hp 3) (hnil _))))
        (cons' (hgate .and (cons' (hp 2) (cons' (hp 2) (hnil _)))) (hnil _)))

/-- Writing the gates of the circuit of a formula is polynomial-time. -/
private theorem computableInPolyTime_circuitGates :
    ComputableInPolyTime circuitGates encCNF (encList encGate) := by
  have hvars := SAT.computableInPolyTime_vars
  have hzip : ComputableInPolyTime (fun φ => (circuitSteps φ).zipIdx) encCNF
      (encList (encPair (encPair (encPair encNat encBool) encBool) encUnary)) := by
    fun_prop
  have hargs : ComputableInPolyTime (fun p : CNF ℕ × ((Literal ℕ × Bool) × ℕ) =>
      (((p.1.vars.length + 3 * p.2.2, p.1.vars.idxOf p.2.1.1.1), p.2.1.1.2), p.2.1.2))
      (encPair encCNF (encPair (encPair (encPair encNat encBool) encBool) encUnary))
      (encPair (encPair (encPair encUnary encUnary) encBool) encBool) := by
    fun_prop
  unfold circuitGates
  exact listAppend' (const _) (flatMapWithInput hzip
    (computableInPolyTime_circuitBlock.comp hargs))

/-- Building the circuit of a formula is polynomial-time, from the encoding `encCNF` of formulas
to the binary encoding `encCircuit 1` of circuits. -/
private theorem computableInPolyTime_toCircuit :
    ComputableInPolyTime toCircuit encCNF (encCircuit 1) := by
  have hg := computableInPolyTime_circuitGates
  have hvars := SAT.computableInPolyTime_vars
  have hn : ComputableInPolyTime (fun φ : CNF ℕ => φ.vars.length) encCNF encUnary := by
    fun_prop
  have hout : ComputableInPolyTime
      (fun φ : CNF ℕ => φ.vars.length + 3 * (circuitSteps φ).length + 2) encCNF encNat :=
    unary_to_binary.comp (by fun_prop)
  have h : ComputableInPolyTime (fun φ : CNF ℕ => (φ.vars.length, circuitCode φ)) encCNF
      (encPair encUnary encCode) :=
    hn.prod (hg.prod (cons' hout (const [])))
  exact h.of_enc_eq fun φ => by rw [encCircuit_apply, code_toCircuit]; rfl

/-- **`SAT` reduces to `CircuitSAT`** in polynomial time. -/
theorem polyTimeReducible_CircuitSAT : PolyTimeReducible encCNF (encCircuit 1) SAT CircuitSAT :=
  ⟨toCircuit, computableInPolyTime_toCircuit,
    fun φ => (toCircuit_mem_CircuitSAT_iff φ).symm⟩

end SAT

/-- Circuit satisfiability is `NP`-hard. -/
theorem CircuitSAT_npHard : NPHard (encCircuit 1) CircuitSAT :=
  CookLevin.SAT_npHard.trans SAT.polyTimeReducible_CircuitSAT

/-- **Circuit satisfiability is `NP`-complete**, for the binary encoding of circuits
`encCircuit 1` [Arora and Barak, Section 6.1][AroraBarak09]. -/
theorem CircuitSAT_npComplete : NPComplete (encCircuit 1) CircuitSAT :=
  ⟨CircuitSAT.mem_NP, CircuitSAT_npHard⟩

end Cslib.Complexity
