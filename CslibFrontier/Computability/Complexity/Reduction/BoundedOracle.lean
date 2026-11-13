/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.BoundedQuery
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Space
public import CslibFrontier.Computability.Complexity.FineGrained
public import CslibFrontier.Computability.Complexity.FineGrained.DisjointInstances
public import CslibFrontier.Computability.Complexity.FineGrained.SearchStep
public import CslibFrontier.Computability.Complexity.Reduction.Turing
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.QueryBounds

/-!
# Oracle reductions with explicit query and answer lengths

`Cslib.Complexity.PolyTimeTuringReducible`
(`CslibFrontier/Computability/Complexity/Reduction/Turing.lean`) and
`Cslib.Complexity.ComputableInPolyTimeWithOracle`
(`CslibFrontier/Computability/Complexity/Classes/Oracle.lean`) quantify over adaptive
deterministic `WordQueryComp` programs certified by `IsOraclePPTOn` against one-bit language
oracles. Fine-grained and exact exponential complexity require explicit quantitative accounting of
the oracle interaction across both decision and multi-bit function oracles:

* `Cslib.Complexity.OracleCallBound`: an `enc_structure`-backed record tracking four explicit
  quantities on each input `a`:
  * `qcount`: number of oracle queries issued along the run;
  * `qlen`: maximum bit-length of any single query word issued along the run;
  * `totalQlen`: total bit-length `∑ q, |q|` summed across all queries issued along the run;
  * `alen`: maximum bit-length of any oracle answer returned along the run.
* `Cslib.Complexity.BoundedOracleProgram`: a `#4391` `structure` packaging a deterministic adaptive
  `WordQueryComp` program, its `IsOraclePPTOn` certificate, an explicit `OracleCallBound` profile
  respected against `oracle : List Bool → List Bool`, and a polynomial-time unary answer-length
  allowance `alenCap` enabling open handler substitution.
* `Cslib.Complexity.BoundedOracleReduction`: the specialization to typed decision problems
  `(A, encA)` and `(B, encB)` against `languageOracle (encB '' B)` (`alen ≤ 1`).

In addition to identity, zero-query polynomial-time lifts, single-query many-one/function lifts,
and bridges to `PolyTimeTuringReducible` and `PWithOracleQueries`, this module extends
`Turing.MultiTapePTM` simulation from one-bit `receiveBit` to arbitrary word replies `receiveWord`,
proving:

1. **Composition (`BoundedOracleProgram.comp`, `BoundedOracleReduction.trans`):** explicit
   worst-case composition via `wordMax` and sharper linear `totalQlen` composition when the inner
   total query length is affine in the outer query length.
2. **Polynomial-time and polynomial-space multi-bit oracle transfer
   (`BoundedOracleProgram.computableInPolyTime`,
   `BoundedOracleProgram.exists_computableInO_polySpace`):**
   simulator workspace is bounded in terms of input length, clock, answer-length cap, and simulated
   oracle workspace — never as a polynomial in simulated oracle running time.
3. **Parameterized exponential and subexponential time transfer
   (`BoundedOracleReduction.decidableInExpTime`, `BoundedOracleReduction.decidableInSubexpTime`):**
   guarding oracle calls by a polynomial-time validity/length predicate that holds along
   `queriesWith` transfers `2 ^ (δ * μB)` deciders to `2 ^ (scale * δ * μA)` with polynomial
   overhead absorbing query count and construction cost.

## Main definitions

* `Cslib.Complexity.OracleCallBound`, `Cslib.Complexity.OracleCallBound.Respects`: explicit
  `(qcount, qlen, totalQlen, alen)` call budget and run satisfaction predicate.
* `Turing.MultiTapePTM.receiveWord`: multi-bit reply installation on `FiniteConfig`.
* `Cslib.Complexity.BoundedOracleProgram`: multi-bit functional oracle program with explicit query
  and answer length accounting.
* `Cslib.Complexity.BoundedOracleReduction`: language oracle reduction with explicit query and
  answer length accounting.

## Main results

* `Turing.MultiTapePTM.computableInPolyTime_run_word`,
  `Turing.MultiTapePTM.exists_computableInO_run_word`: multi-bit clocked oracle machine simulation
  in polynomial time and in polynomial workspace.
* `Cslib.Complexity.BoundedOracleProgram.id`, `.ofPolyTime`, `.ofSingleQuery`, `.comp`,
  `.compAffine`, `.totalQueryLength_comp_affine`, `.computableInPolyTime`,
  `.exists_computableInO_polySpace`, `.computableInPolySpace`.
* `Cslib.Complexity.BoundedOracleReduction.refl`, `.ofPolyTime`, `.ofSizeSensitive`,
  `.transDecoded`, `.trans`, `.polyTimeTuringReducible`, `.mem_PWithOracleQueries`,
  `.ofPWithOracleQueries`, `.mem_P`, `.mem_PSPACE`, `.decidableInExpTime`,
  `.decidableInSubexpTime`.

## References

* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4
* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
-/

public section

/-! ### Multi-bit oracle simulation on `Turing.MultiTapePTM` -/

namespace Turing.MultiTapePTM

open Cslib Cslib.Complexity MultiTapeMachine MultiTapeTM

variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]
  (machine : MultiTapePTM k Bool Control Operation)

/-- Install a multi-bit word reply to the pending query on `p.1`; leave `p.1` unchanged when no
query is pending. -/
@[expose]
def receiveWord (p : FiniteConfig k Bool Control Operation × List Bool) :
    FiniteConfig k Bool Control Operation :=
  match machine.pendingQuery p.1 with
  | some (op, next) => p.1.receive op next p.2
  | none => p.1

/-- Against any word oracle `oracle : List Bool → List Bool`, one `answerStep` either installs
`oracle (machine.pendingRequest cfg)` via `receiveWord` or executes `localStep`. -/
theorem answerStep_word (oracle : List Bool → List Bool)
    (cfg : FiniteConfig k Bool Control Operation) :
    machine.answerStep (fun q => oracle q.2) cfg =
      if (machine.pendingQuery cfg).isSome then
        machine.receiveWord (cfg, oracle (machine.pendingRequest cfg))
      else machine.localStep cfg := by
  unfold answerStep receiveWord pendingRequest localStep pendingQuery
  cases cfg.tapes.state with
  | none => rfl
  | some control =>
    simp only [Option.map_some]
    cases machine.tr control cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols
      false <;> rfl

/-- When every reply to a request of length at most `steps` has length at most `answerSize`, one
`answerStep` advances `FiniteConfig.SpaceBound` from `steps` to `steps + 1` with the same
`answerSize`. -/
theorem spaceBound_answerStep_word (oracle : List Bool → List Bool)
    {inputSize steps answerSize : ℕ} {cfg : FiniteConfig k Bool Control Operation}
    (h : FiniteConfig.SpaceBound inputSize steps answerSize cfg)
    (hans : ∀ w, w.length ≤ steps → (oracle w).length ≤ answerSize) :
    FiniteConfig.SpaceBound inputSize (steps + 1) answerSize
      (machine.answerStep (fun q => oracle q.2) cfg) := by
  unfold answerStep
  split
  · exact h.mono le_rfl (Nat.le_succ _) le_rfl
  · split
    · exact h.step _ _ _
    · exact h.receive _ _ _ (hans _ (h.query _))

section FiniteControl

variable [Finite Control] [Fintype Operation]

theorem receiveWord_pt : ComputableInPolyTime machine.receiveWord
    (encPair encFiniteConfig encBits) encFiniteConfig := by
  refine .of_tidy <| ComputableTidilyInPolyTime.finite_cases
    (tag := fun p : FiniteConfig k Bool Control Operation × List Bool => machine.pendingQuery p.1)
    (branch := fun q (p : FiniteConfig k Bool Control Operation × List Bool) => match q with
      | some (op, next) => p.1.receive op next p.2
      | none => p.1)
    (machine.pendingQuery_pt.tidy.comp
      (ComputableTidilyInPolyTime.fst encFiniteConfig encBits)) ?_
  rintro (_ | ⟨op, next⟩)
  · exact ComputableTidilyInPolyTime.fst _ _
  · exact ComputableTidilyInPolyTime.finiteConfig_receive
      (ComputableTidilyInPolyTime.fst encFiniteConfig encBits)
      (ComputableTidilyInPolyTime.snd encFiniteConfig encBits) op next

/-- **Independent time and space of one multi-bit oracle instruction.**
Charges `Tg` and `Sg` only when `(machine.pendingQuery cfg).isSome = true`. -/
theorem answerStep_word_inO {oracle : List Bool → List Bool} {Tg Sg : List Bool → ℕ}
    (horacle : ComputableInO oracle encBits encBits Tg Sg) :
    ∃ d : ℕ, ComputableInO (machine.answerStep fun q => oracle q.2)
      encFiniteConfig encFiniteConfig
      (fun cfg => ((encFiniteConfig cfg).length + 1) ^ d +
        if (machine.pendingQuery cfg).isSome = true then
          Tg (machine.pendingRequest cfg) +
            ((encFiniteConfig cfg).length +
              (oracle (machine.pendingRequest cfg)).length + 1) ^ d
        else 0)
      (fun cfg => ((encFiniteConfig cfg).length + 1) ^ d +
        if (machine.pendingQuery cfg).isSome = true then
          Sg (machine.pendingRequest cfg) +
            ((encFiniteConfig cfg).length +
              (oracle (machine.pendingRequest cfg)).length + 1) ^ d
        else 0) := by
  have hdone : ComputableInPolyTime (fun _ : FiniteConfig k Bool Control Operation => false)
      encFiniteConfig encBool := .const false
  have hleaf : ComputableInPolyTime (fun cfg => (machine.pendingQuery cfg).isSome)
      encFiniteConfig encBool :=
    (ComputableInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt
  obtain ⟨d, h⟩ := exists_computableInO_searchStep hdone hleaf machine.pendingRequest_pt
    machine.localStep_pt machine.receiveWord_pt horacle
  refine ⟨d, (h.mono_le (fun cfg => ?_) (fun cfg => ?_)).of_enc_eq fun cfg => ?_⟩
  · simp only [true_and, encBits_apply]
    exact le_rfl
  · simp only [true_and, encBits_apply]
    exact le_rfl
  · simp only [Bool.false_eq_true, ite_false]
    rw [machine.answerStep_word]

theorem computableInPolyTime_answerStep_word {oracle : List Bool → List Bool}
    (horacle : ComputableInPolyTime oracle encBits encBits) :
    ComputableInPolyTime (machine.answerStep fun q => oracle q.2)
      encFiniteConfig encFiniteConfig := by
  have hcond : ComputableTidilyInPolyTime (fun cfg => (machine.pendingQuery cfg).isSome)
      encFiniteConfig encBool :=
    (ComputableTidilyInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt.tidy
  have h := ComputableTidilyInPolyTime.cond hcond
    (machine.receiveWord_pt.tidy.comp
      (ComputableTidilyInPolyTime.id'.prod (horacle.tidy.comp machine.pendingRequest_pt.tidy)))
    machine.localStep_pt.tidy
  exact (h.of_enc_eq fun cfg => by rw [machine.answerStep_word]; rfl).computableInPolyTime

omit [Fintype Operation] in
/-- **A clocked multi-bit oracle run against a polynomial-time word oracle is polynomial-time.** -/
theorem computableInPolyTime_run_word [Finite Operation] {α : Type} {input : α ↪ List Bool}
    {oracle : List Bool → List Bool} (horacle : ComputableInPolyTime oracle encBits encBits)
    (c d : ℕ) :
    ComputableInPolyTime (fun a => OracleComp.interpret (m := Id) (fun q => oracle q.2)
      (machine.run (pure false) (fun op word => OracleComp.query (op, word))
        (c * ((input a).length + 1) ^ d) (input a))) input encBits := by
  refine .of_tidy ?_
  classical
  let _ := Fintype.ofFinite Operation
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  obtain ⟨co, do', ho_len⟩ := horacle.polyBounded_length.exists_le
  let clk (a : α) : ℕ := c * ((input a).length + 1) ^ d
  let ansMax (a : α) : ℕ := co * (clk a + 1) ^ do'
  have hcount : ComputableTidilyInPolyTime clk input encUnary :=
    ((ComputableTidilyInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableTidilyInPolyTime.encoding_length input)).of_enc_eq fun _ => by simp [clk]
  have hinit : ComputableTidilyInPolyTime
      (fun a => FiniteConfig.init (k := k) (Oracle := Operation) machine.initial (input a))
      input encFiniteConfig :=
    ComputableTidilyInPolyTime.finiteConfig_init (by fun_prop) _
  have hspace (a : α) {i : ℕ} (hi : i ≤ clk a) :
      FiniteConfig.SpaceBound (input a).length i (ansMax a)
        ((machine.answerStep fun q => oracle q.2)^[i]
          (FiniteConfig.init machine.initial (input a))) := by
    induction i with
    | zero => exact (FiniteConfig.spaceBound_init _ _ 0).mono le_rfl le_rfl (Nat.zero_le _)
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      refine machine.spaceBound_answerStep_word oracle (ih (Nat.le_of_succ_le hi)) fun w hw => ?_
      have hw' : w.length ≤ clk a := hw.trans (Nat.le_of_succ_le hi)
      exact (ho_len w).trans (Nat.mul_le_mul_left co
        (Nat.pow_le_pow_left (Nat.add_le_add_right hw' 1) do'))
  have hbound : PolyBounded (fun a => (input a).length)
      (fun a => cf * ((input a).length + clk a + ansMax a + 1)) := by
    dsimp only [clk, ansMax]
    growth_poly
  have hit := ComputableTidilyInPolyTime.iterate hcount hinit
    (machine.computableInPolyTime_answerStep_word horacle).tidy hbound fun a i hi =>
      (hcf _ _ _ _ (hspace a hi)).trans (Nat.mul_le_mul_left cf (by omega))
  have hout : ComputableTidilyInPolyTime
      (fun cfg : FiniteConfig k Bool Control Operation => cfg.tapes.output)
      encFiniteConfig encBits := by fun_prop
  exact (hout.comp hit).of_enc_eq fun a => by rw [machine.interpret_run_pure_false]; rfl

omit [Fintype Operation] in
/-- **A clocked multi-bit oracle run against a polynomial-space word oracle runs in polynomial
workspace**, with explicit time `O(poly(|a|) + (clock a + 1) * (poly(|a|) + wordMax Tg (clock a)))`
charging `Tg` only up to the clock and bounding space solely by input, simulated space, and
counters (never by simulated time `Tg`). -/
theorem exists_computableInO_run_word [Finite Operation] {α : Type} {input : α ↪ List Bool}
    {oracle : List Bool → List Bool} {Tg Sg : List Bool → ℕ}
    (horacle : ComputableInO oracle encBits encBits Tg Sg)
    (hSg : PolyBounded List.length Sg) (c d : ℕ) :
    ∃ (c₀ e₀ : ℕ) (S : α → ℕ),
      PolyBounded (fun a => (input a).length) S ∧
      ComputableInO (fun a => OracleComp.interpret (m := Id) (fun q => oracle q.2)
        (machine.run (pure false) (fun op word => OracleComp.query (op, word))
          (c * ((input a).length + 1) ^ d) (input a))) input encBits
        (fun a => c₀ * ((input a).length + 1) ^ e₀ +
          (c * ((input a).length + 1) ^ d + 1) *
            (c₀ * ((input a).length + 1) ^ e₀ + wordMax Tg (c * ((input a).length + 1) ^ d)))
        S := by
  classical
  let _ := Fintype.ofFinite Operation
  let _ : Inhabited (FiniteConfig k Bool Control Operation) :=
    ⟨FiniteConfig.init machine.initial []⟩
  obtain ⟨e, hstep⟩ := machine.answerStep_word_inO horacle
  obtain ⟨cg, dg, hSg_le⟩ := hSg.exists_le
  obtain ⟨kg, ho_len⟩ := horacle.length_le
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Control) (Oracle := Operation)
  let clk (a : α) : ℕ := c * ((input a).length + 1) ^ d
  let sgMax (a : α) : ℕ := cg * (clk a + 1) ^ dg
  let ansMax (a : α) : ℕ := kg * (sgMax a + 1)
  have hans_le (a : α) {w : List Bool} (hw : w.length ≤ clk a) :
      (oracle w).length ≤ ansMax a := by
    have hsg : Sg w ≤ sgMax a :=
      (hSg_le w).trans (Nat.mul_le_mul_left cg
        (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) dg))
    exact (ho_len w).trans (Nat.mul_le_mul_left kg (Nat.add_le_add_right hsg 1))
  have hn : ComputableTidilyInPolyTime clk input encNat := by
    have hlen : ComputableTidilyInPolyTime (fun a => (input a).length) input encUnary := by
      fun_prop
    exact (ComputableTidilyInPolyTime.unary_to_binary.comp
      ((ComputableTidilyInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
        hlen)).of_enc_eq fun _ => by simp [clk]
  obtain ⟨dn, _, hn⟩ := hn.exists_degree
  have hinit : ComputableTidilyInPolyTime
      (fun a => FiniteConfig.init (k := k) (Oracle := Operation) machine.initial (input a))
      input encFiniteConfig :=
    ComputableTidilyInPolyTime.finiteConfig_init (by fun_prop) _
  obtain ⟨di, _, hinit⟩ := hinit.exists_degree
  have hout : ComputableTidilyInPolyTime
      (fun cfg : FiniteConfig k Bool Control Operation => cfg.tapes.output)
      encFiniteConfig encBits := by fun_prop
  obtain ⟨do', _, hout⟩ := hout.exists_degree
  let step := machine.answerStep fun q => oracle q.2
  have hspace (a : α) {i : ℕ} (hi : i ≤ clk a) :
      FiniteConfig.SpaceBound (input a).length i (ansMax a)
        (step^[i] (FiniteConfig.init machine.initial (input a))) := by
    induction i with
    | zero => exact (FiniteConfig.spaceBound_init _ _ 0).mono le_rfl le_rfl (Nat.zero_le _)
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact machine.spaceBound_answerStep_word oracle (ih (Nat.le_of_succ_le hi))
        fun w hw => hans_le a (hw.trans (Nat.le_of_succ_le hi))
  let B (a : α) : ℕ := cf * ((input a).length + clk a + ansMax a + 1)
  have hlen (a : α) {i : ℕ} (hi : i ≤ clk a) :
      (encFiniteConfig (step^[i] (FiniteConfig.init machine.initial (input a)))).length ≤ B a :=
    (hcf _ _ _ _ (hspace a hi)).trans (Nat.mul_le_mul_left cf (by omega))
  have hreq (a : α) {i : ℕ} (hi : i ≤ clk a) :
      (machine.pendingRequest (step^[i] (FiniteConfig.init machine.initial (input a)))).length ≤
        clk a :=
    (machine.length_pendingRequest_le (hspace a hi)).trans hi
  let stepPoly (a : α) : ℕ := (B a + 1) ^ e + (B a + ansMax a + 1) ^ e
  have hit := ComputableInO.iterate hn.inO.computableInO hinit.inO.computableInO hstep
    (R := fun a => stepPoly a + wordMax Tg (clk a))
    (Q := fun a => stepPoly a + sgMax a) (B := B)
    (fun a i hi => by
      have hl := hlen a hi
      have hr := hreq a hi
      have hp1 := Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) e
      split_ifs
      · have ha := hans_le a hr
        have hp2 := Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add hl ha) 1) e
        have htm := le_wordMax Tg hr
        dsimp only [step, stepPoly] at hl hr hp1 ha hp2 htm ⊢
        omega
      · dsimp only [step, stepPoly] at hl hr hp1 ⊢
        omega)
    (fun a i hi => by
      have hl := hlen a hi
      have hr := hreq a hi
      have hp1 := Nat.pow_le_pow_left (Nat.add_le_add_right hl 1) e
      split_ifs
      · have ha := hans_le a hr
        have hp2 := Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add hl ha) 1) e
        have hsm : Sg (machine.pendingRequest
            (step^[i] (FiniteConfig.init machine.initial (input a)))) ≤ sgMax a :=
          (hSg_le _).trans (Nat.mul_le_mul_left cg
            (Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) dg))
        dsimp only [step, stepPoly] at hl hr hp1 ha hp2 hsm ⊢
        omega
      · dsimp only [step, stepPoly] at hl hr hp1 ⊢
        omega)
    (fun a _ hi => hlen a hi)
  have hwhole := (hout.inO.computableInO.comp hit).of_enc_eq
    (g := fun a => OracleComp.interpret (m := Id) (fun q => oracle q.2)
      (machine.run (pure false) (fun op word => OracleComp.query (op, word))
        (clk a) (input a)))
    fun a => by rw [machine.interpret_run_pure_false]; rfl
  let clockLen (a : α) : ℕ := (encNat (clk a)).length
  have hclkLen (a : α) : clockLen a ≤ clk a + 1 := by
    dsimp only [clockLen]
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_succ _)
  have hOverhead : PolyBounded (fun a => (input a).length)
      (fun a => ((input a).length + 1) ^ dn + ((input a).length + 1) ^ di +
        (B a + 1) ^ do' + stepPoly a + sgMax a + B a + (clk a + 1 + 1) ^ 2 + (clk a + 1)) := by
    dsimp only [stepPoly, B, ansMax, sgMax, clk]
    growth_poly
  obtain ⟨c₀, e₀, hc₀⟩ := hOverhead.exists_le
  let S (a : α) : ℕ := c₀ * ((input a).length + 1) ^ e₀
  have hSPoly : PolyBounded (fun a => (input a).length) S := by
    dsimp only [S]
    growth_poly
  refine ⟨c₀, e₀, S, hSPoly, hwhole.mono_le (fun a => ?_) (fun a => ?_)⟩
  · have hfin := Nat.pow_le_pow_left (Nat.add_le_add_right (hlen a le_rfl) 1) do'
    have hcl2 := Nat.pow_le_pow_left (Nat.add_le_add_right (hclkLen a) 1) 2
    have h₁ := hc₀ a
    dsimp only [step, clk, clockLen] at hfin hcl2 h₁ ⊢
    rw [Nat.add_right_comm]
    exact Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ (by omega))
  · have hfin := Nat.pow_le_pow_left (Nat.add_le_add_right (hlen a le_rfl) 1) do'
    have hcl := hclkLen a
    have h₁ := hc₀ a
    dsimp only [step, S, clk, clockLen] at hfin hcl h₁ ⊢
    omega

end FiniteControl

end Turing.MultiTapePTM

/-! ### `OracleCallBound`, `BoundedOracleProgram`, and `BoundedOracleReduction` -/

namespace Cslib.Complexity

open Probability _root_.Turing _root_.Turing.MultiTapeTM

@[expose] section
/-- Explicit quantitative profile of an oracle call budget on a single input:
`qcount` queries, each of bit-length at most `qlen`, with total bit-length at most `totalQlen`,
and each answer of bit-length at most `alen`. -/
@[ext]
structure OracleCallBound where
  /-- Maximum number of oracle queries issued along the run. -/
  qcount : ℕ
  /-- Maximum bit-length of any single query word issued along the run. -/
  qlen : ℕ
  /-- Maximum sum of bit-lengths of all query words issued along the run. -/
  totalQlen : ℕ
  /-- Maximum bit-length of any oracle answer read along the run. -/
  alen : ℕ
  deriving DecidableEq, Repr
end

/-- Framed binary encoding of `OracleCallBound`. -/
enc_structure encOracleCallBound : OracleCallBound where
  qcount : encNat, qlen : encNat, totalQlen : encNat, alen : encNat

namespace OracleCallBound

/-- Zero-query profile `(0, 0, 0, 0)`. -/
@[expose] def zero : OracleCallBound := ⟨0, 0, 0, 0⟩

/-- Single-query profile `(1, ql, ql, al)` for a query of length `≤ ql` and reply of length `≤ al`.
-/
@[expose] def single (ql al : ℕ) : OracleCallBound := ⟨1, ql, ql, al⟩

/-- Coordinatewise dominance between `OracleCallBound` profiles. -/
@[expose] def Le (b₁ b₂ : OracleCallBound) : Prop :=
  b₁.qcount ≤ b₂.qcount ∧ b₁.qlen ≤ b₂.qlen ∧ b₁.totalQlen ≤ b₂.totalQlen ∧ b₁.alen ≤ b₂.alen

/-- `prog` **respects** `b` against the word oracle `oracle : List Bool → List Bool`: along the
deterministic run `queriesWith (fun q => oracle q.2) prog`, query count is `≤ b.qcount`, each query
has length `≤ b.qlen`, total query length is `≤ b.totalQlen`, and each reply has length `≤ b.alen`.
-/
@[expose]
def Respects {β : Type} (oracle : List Bool → List Bool) (prog : WordQueryComp Unit β)
    (b : OracleCallBound) : Prop :=
  let qs := OracleComp.queriesWith (fun q => oracle q.2) prog
  qs.length ≤ b.qcount ∧
  (∀ q ∈ qs, q.2.length ≤ b.qlen) ∧
  (qs.map fun q => q.2.length).sum ≤ b.totalQlen ∧
  (∀ q ∈ qs, (oracle q.2).length ≤ b.alen)

theorem Respects.mono {β : Type} {oracle : List Bool → List Bool} {prog : WordQueryComp Unit β}
    {b₁ b₂ : OracleCallBound} (h : Respects oracle prog b₁) (hle : b₁.Le b₂) :
    Respects oracle prog b₂ := by
  rcases h with ⟨hqc, hql, htql, hal⟩
  rcases hle with ⟨hlqc, hlql, hltql, hlal⟩
  exact ⟨hqc.trans hlqc, fun q hq => (hql q hq).trans hlql,
    htql.trans hltql, fun q hq => (hal q hq).trans hlal⟩

theorem respects_pure {β : Type} (oracle : List Bool → List Bool) (x : β) (b : OracleCallBound) :
    Respects oracle (pure x) b := by
  simp [Respects]

theorem respects_map {β γ : Type} (oracle : List Bool → List Bool) (f : β → γ)
    (prog : WordQueryComp Unit β) (b : OracleCallBound) :
    Respects oracle (f <$> prog) b ↔ Respects oracle prog b := by
  simp [Respects, OracleComp.queriesWith_map]

/-- Composed call bound when an outer run with bound `b₁` answers each query `w` (`|w| ≤ b₁.qlen`)
using an inner oracle program with profile `b₂ w`. -/
@[expose]
noncomputable def comp (b₁ : OracleCallBound) (b₂ : List Bool → OracleCallBound) :
    OracleCallBound where
  qcount := b₁.qcount * wordMax (fun w => (b₂ w).qcount) b₁.qlen
  qlen := wordMax (fun w => (b₂ w).qlen) b₁.qlen
  totalQlen := b₁.qcount * wordMax (fun w => (b₂ w).totalQlen) b₁.qlen
  alen := wordMax (fun w => (b₂ w).alen) b₁.qlen

end OracleCallBound

/-- Auxiliary structural lemma for substituting a deterministic word-query handler `G` into an
outer `WordQueryComp` program `prog`. -/
private theorem interpret_and_queriesWith_subst {β : Type}
    (oracle₁ oracle₂ : List Bool → List Bool)
    (G : Unit × List Bool → WordQueryComp Unit (List Bool))
    (prog : WordQueryComp Unit β)
    (hG : ∀ q ∈ OracleComp.queriesWith (fun q => oracle₁ q.2) prog,
      OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2) (G q) = oracle₁ q.2) :
    OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2) (OracleComp.interpret G prog) =
      OracleComp.interpret (m := Id) (fun q => oracle₁ q.2) prog ∧
    OracleComp.queriesWith (fun q' => oracle₂ q'.2) (OracleComp.interpret G prog) =
      (OracleComp.queriesWith (fun q => oracle₁ q.2) prog).flatMap fun q =>
        OracleComp.queriesWith (fun q' => oracle₂ q'.2) (G q) := by
  induction prog using PFunctor.FreeM.induction with
  | pure x => exact ⟨rfl, rfl⟩
  | lift_bind q cont ih =>
    change OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2)
        (OracleComp.interpret G (OracleComp.query q >>= cont)) =
      OracleComp.interpret (m := Id) (fun q => oracle₁ q.2) (OracleComp.query q >>= cont) ∧
      OracleComp.queriesWith (fun q' => oracle₂ q'.2)
        (OracleComp.interpret G (OracleComp.query q >>= cont)) =
      (OracleComp.queriesWith (fun q => oracle₁ q.2) (OracleComp.query q >>= cont)).flatMap _
    rw [OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_bind,
      OracleComp.queriesWith_bind, OracleComp.queriesWith_query_bind, List.flatMap_cons]
    have hq : OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2) (G q) = oracle₁ q.2 :=
      hG q (List.mem_cons_self ..)
    rw [hq]
    obtain ⟨heval, hqs⟩ := ih (oracle₁ q.2) fun q' hq' => hG q' (List.mem_cons_of_mem _ hq')
    exact ⟨heval, congrArg (_ ++ ·) hqs⟩

private theorem forall_queriesWith_of_probQueriesSatisfy {β : Type}
    {p : Unit × List Bool → Prop} (answer : Unit × List Bool → List Bool)
    (prog : WordQueryComp Unit β)
    (h : (OracleComp.interpret ProbOracleComp.query prog).QueriesSatisfy p) :
    ∀ q ∈ OracleComp.queriesWith answer prog, p q := by
  induction prog using PFunctor.FreeM.induction with
  | pure _ => simp
  | lift_bind q cont ih =>
    change (OracleComp.interpret ProbOracleComp.query
      (OracleComp.query q >>= cont)).QueriesSatisfy p at h
    rw [OracleComp.interpret_bind, OracleComp.interpret_query, ProbOracleComp.query] at h
    obtain ⟨hpq, hcont⟩ := OracleComp.QueriesSatisfy.liftBind_iff.mp h
    intro q' hq'
    change q' ∈ OracleComp.queriesWith answer (OracleComp.query q >>= cont) at hq'
    rw [OracleComp.queriesWith_query_bind, List.mem_cons] at hq'
    rcases hq' with rfl | hq'
    · exact hpq
    · exact ih (answer q) (hcont (answer q)) q' hq'

/-- **Deterministic adaptive oracle program with explicit query and answer length bounds.**
Packages a `WordQueryComp` program computing `f : α → β` relative to `oracle : List Bool → List
Bool`, certified by `IsOraclePPTOn`, together with an explicit `OracleCallBound` profile `bound a`
and a polynomial-time unary reply-length allowance `alenCap a` (`(bound a).alen ≤ alenCap a`) used
when composing open oracle handlers. -/
structure BoundedOracleProgram {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (oracle : List Bool → List Bool) (f : α → β) where
  /-- Deterministic adaptive word-query program. -/
  program : α → WordQueryComp Unit β
  /-- Explicit `(qcount, qlen, totalQlen, alen)` profile on each input. -/
  bound : α → OracleCallBound
  /-- Polynomial-time unary upper allowance on reply lengths along the run. -/
  alenCap : α → ℕ
  /-- Strict oracle-PPT machine realization across all stateful handlers. -/
  isOraclePPTOn :
    IsOraclePPTOn encA encB (fun a => OracleComp.interpret ProbOracleComp.query (program a))
  /-- Polynomial-time certificate for `alenCap` in unary. -/
  computableInPolyTime_alenCap : ComputableInPolyTime alenCap encA encUnary
  /-- Functional correctness against `oracle`. -/
  eval_eq : ∀ a, OracleComp.interpret (m := Id) (fun q => oracle q.2) (program a) = f a
  /-- Every run respects `bound a`. -/
  respects_bound : ∀ a, OracleCallBound.Respects oracle (program a) (bound a)
  /-- `alenCap a` dominates `(bound a).alen`. -/
  alen_le_alenCap : ∀ a, (bound a).alen ≤ alenCap a

namespace BoundedOracleProgram

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}

/-- Number of queries budgeted on `a`. -/
@[expose] def qcount {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f) (a : α) : ℕ := (R.bound a).qcount

/-- Per-query length budgeted on `a`. -/
@[expose] def qlen {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f) (a : α) : ℕ := (R.bound a).qlen

/-- Total query length budgeted on `a`. -/
@[expose] def totalQlen {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f) (a : α) : ℕ := (R.bound a).totalQlen

/-- Per-answer length budgeted on `a`. -/
@[expose] def alen {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f) (a : α) : ℕ := (R.bound a).alen

/-- Weaken the `OracleCallBound` profile of `R` to any coordinatewise larger `bound'`. -/
@[expose]
def mono {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f)
    {bound' : α → OracleCallBound} {alenCap' : α → ℕ}
    (hbound : ∀ a, (R.bound a).Le (bound' a))
    (hcap_pt : ComputableInPolyTime alenCap' encA encUnary)
    (hcap_le : ∀ a, (bound' a).alen ≤ alenCap' a) :
    BoundedOracleProgram encA encB oracle f where
  program := R.program
  bound := bound'
  alenCap := alenCap'
  isOraclePPTOn := R.isOraclePPTOn
  computableInPolyTime_alenCap := hcap_pt
  eval_eq := R.eval_eq
  respects_bound a := (R.respects_bound a).mono (hbound a)
  alen_le_alenCap := hcap_le

/-- A plain polynomial-time function `f : α → β` lifts to a `0`-query `BoundedOracleProgram` with
`OracleCallBound.zero` relative to every word oracle. -/
@[expose]
def ofPolyTime {f : α → β} (hf : ComputableInPolyTime f encA encB)
    (oracle : List Bool → List Bool) :
    BoundedOracleProgram encA encB oracle f where
  program a := pure (f a)
  bound _ := OracleCallBound.zero
  alenCap _ := 0
  isOraclePPTOn := hf.isOraclePPTOn
  computableInPolyTime_alenCap := .const 0
  eval_eq _ := rfl
  respects_bound _ := OracleCallBound.respects_pure oracle _ _
  alen_le_alenCap _ := le_rfl

/-- Polynomial-time postprocessing `g : β → γ` preserves `bound` and `alenCap`. -/
@[expose]
def map {oracle : List Bool → List Bool} {f : α → β} {g : β → γ}
    (R : BoundedOracleProgram encA encB oracle f)
    (hg : ComputableInPolyTime g encB encC) :
    BoundedOracleProgram encA encC oracle (g ∘ f) where
  program a := g <$> R.program a
  bound := R.bound
  alenCap := R.alenCap
  isOraclePPTOn := by
    simpa only [OracleComp.interpret_map] using R.isOraclePPTOn.map' hg
  computableInPolyTime_alenCap := R.computableInPolyTime_alenCap
  eval_eq a := by
    rw [OracleComp.interpret_map, R.eval_eq a]
    rfl
  respects_bound a := (OracleCallBound.respects_map oracle g (R.program a) (R.bound a)).mpr
    (R.respects_bound a)
  alen_le_alenCap := R.alen_le_alenCap

/-- Polynomial-time preprocessing `p : γ → α` pulls back `bound` and `alenCap` along `p`. -/
@[expose]
def preprocess {oracle : List Bool → List Bool} {f : α → β} {p : γ → α}
    (R : BoundedOracleProgram encA encB oracle f)
    (hp : ComputableInPolyTime p encC encA) :
    BoundedOracleProgram encC encB oracle (f ∘ p) where
  program c := R.program (p c)
  bound c := R.bound (p c)
  alenCap c := R.alenCap (p c)
  isOraclePPTOn := R.isOraclePPTOn.preprocess' hp
  computableInPolyTime_alenCap := R.computableInPolyTime_alenCap.comp hp
  eval_eq c := R.eval_eq (p c)
  respects_bound c := R.respects_bound (p c)
  alen_le_alenCap c := R.alen_le_alenCap (p c)

/-- **Single-query oracle call** with explicit request generator `req : α → List Bool`, unary
answer-length cap `alenCap : α → ℕ`, and polynomial-time reply decoder `decode : α × List Bool →
β`. Issues `1` query of length `(req a).length` and reads at most `alenCap a` reply bits. -/
@[expose]
def ofSingleQuery {oracle : List Bool → List Bool} {req : α → List Bool} {alenCap : α → ℕ}
    {decode : α × List Bool → β}
    (hreq : ComputableInPolyTime req encA encBits)
    (halen : ComputableInPolyTime alenCap encA encUnary)
    (hdec : ComputableInPolyTime decode (encPair encA encBits) encB)
    (hle : ∀ a, (oracle (req a)).length ≤ alenCap a) :
    BoundedOracleProgram encA encB oracle (fun a => decode (a, oracle (req a))) where
  program a := (fun reply => decode (a, reply)) <$>
    (List.take (alenCap a) <$> OracleComp.query ((), req a))
  bound a := OracleCallBound.single (req a).length (oracle (req a)).length
  alenCap := alenCap
  isOraclePPTOn := by
    have hq := IsOraclePPTOn.query_take' () hreq halen
    simpa only [OracleComp.interpret_map, OracleComp.interpret_query, Functor.map_map] using
      hq.map_with' (f := fun a reply => decode (a, reply)) hdec
  computableInPolyTime_alenCap := halen
  eval_eq a := by
    simp only [OracleComp.interpret_map, Functor.map_map]
    change decode (a, (oracle (req a)).take (alenCap a)) = decode (a, oracle (req a))
    rw [List.take_of_length_le (hle a)]
  respects_bound a := by
    simp [OracleCallBound.Respects, OracleCallBound.single, OracleComp.queriesWith_map]
  alen_le_alenCap a := hle a

/-- **Identity word-oracle program** on `List Bool` given a polynomial-time unary bound `alenCap`
on `(oracle w).length`: makes `1` query `w` of length `w.length` and returns `oracle w`. -/
@[expose]
def id {oracle : List Bool → List Bool} {alenCap : List Bool → ℕ}
    (halen : ComputableInPolyTime alenCap encBits encUnary)
    (hle : ∀ w, (oracle w).length ≤ alenCap w) :
    BoundedOracleProgram encBits encBits oracle oracle :=
  ofSingleQuery (req := _root_.id) (alenCap := alenCap) (decode := Prod.snd)
    .id' halen (.snd encBits encBits) hle

private theorem list_sum_affine_le {ι : Type} (f g : ι → ℕ) (scale offset : ℕ) :
    ∀ (l : List ι), (∀ x ∈ l, f x ≤ scale * g x + offset) →
      (l.map f).sum ≤ scale * (l.map g).sum + offset * l.length
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have hxs := list_sum_affine_le f g scale offset xs
      fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Polynomial reply-length allowance for `BoundedOracleProgram.comp`. -/
noncomputable def compCapPoly {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) : Polynomial ℕ :=
  let hqb := IsOraclePPTOn.query_bounds R₁.isOraclePPTOn
  let c₁ := Classical.choose hqb
  let d₁ := Classical.choose (Classical.choose_spec hqb)
  let hcap₂ : PolyBounded List.length R₂.alenCap := by
    simpa only [encUnary_apply, List.length_replicate, encBits_apply] using
      R₂.computableInPolyTime_alenCap.polyBounded_length
  let hex₂ := hcap₂.exists_le
  let c₂ := Classical.choose hex₂
  let d₂ := Classical.choose (Classical.choose_spec hex₂)
  Polynomial.C c₂ * (Polynomial.C c₁ * (Polynomial.X + 1) ^ d₁ + 1) ^ d₂

/-- **Composition of `BoundedOracleProgram`s with explicit query and answer length accounting.**
Substitutes `R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁` for each query of
`R₁ : BoundedOracleProgram encA encB oracle₁ f`, truncating replies to `R₁.alenCap a` so open
machine realization (`IsOraclePPTOn.interpret_preprocess_open'`) holds against every stateful
external oracle while `OracleCallBound.comp` records the composed `(qcount, qlen, totalQlen, alen)`
budget (with `alen` additionally capped by the polynomial machine reply bound). -/
@[expose]
noncomputable def comp {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) :
    BoundedOracleProgram encA encB oracle₂ f where
  program a := OracleComp.interpret
    (fun q : Unit × List Bool => List.take (R₁.alenCap a) <$> R₂.program q.2) (R₁.program a)
  bound a :=
    let bc := (R₁.bound a).comp R₂.bound
    { bc with alen := min bc.alen ((compCapPoly R₁ R₂).eval (encA a).length) }
  alenCap a := (compCapPoly R₁ R₂).eval (encA a).length
  isOraclePPTOn := by
    let G (a : α) (q : Unit × List Bool) : WordQueryComp Unit (List Bool) :=
      List.take (R₁.alenCap a) <$> R₂.program q.2
    let EIn := encPair encA (encPair (encFinEnum Unit) encBits)
    have hR₂_lift : IsOraclePPTOn EIn encBits
        (fun ⟨_, _, w⟩ => OracleComp.interpret ProbOracleComp.query (R₂.program w)) :=
      R₂.isOraclePPTOn.preprocess' (input := EIn)
        (prepare := fun ⟨_, _, w⟩ => w) (by dsimp only [EIn]; fun_prop)
    have htake_pt : ComputableInPolyTime
        (fun ⟨⟨a, _, _⟩, reply⟩ => reply.take (R₁.alenCap a))
        (encPair EIn encBits) encBits := by
      have hfstE : ComputableInPolyTime
          (fun ⟨⟨a, _, _⟩, _⟩ => a) (encPair EIn encBits) encA := by
        dsimp only [EIn]; fun_prop
      have hsndB : ComputableInPolyTime
          (fun ⟨_, reply⟩ => reply) (encPair EIn encBits) encBits :=
        ComputableInPolyTime.snd EIn encBits
      exact (ComputableTidilyInPolyTime.bitsTake.comp
        (hsndB.tidy.prod (R₁.computableInPolyTime_alenCap.comp hfstE).tidy)).computableInPolyTime
    have hhandler : IsOraclePPTOn EIn encBits
        (fun p : α × (Unit × List Bool) =>
          OracleComp.interpret ProbOracleComp.query (G p.1 p.2)) := by
      simpa only [G, OracleComp.interpret_map] using
        hR₂_lift.map_with' (f := fun ⟨a, _⟩ reply => reply.take (R₁.alenCap a)) htake_pt
    have hresources : ComputableInPolyTime (fun p : α × List Bool => R₁.alenCap p.1)
        (encPair encA encBits) encUnary :=
      R₁.computableInPolyTime_alenCap.comp (ComputableInPolyTime.fst encA encBits)
    have hsub := R₁.isOraclePPTOn.interpret_preprocess_open'
      (operationEncoding := encFinEnum Unit)
      (handler := fun a q => OracleComp.interpret ProbOracleComp.query (G a q))
      (prepare := _root_.id) (resources := fun a _ => R₁.alenCap a)
      .id' hhandler hresources fun a q reply hreply => by
        dsimp only [G] at hreply
        rw [OracleComp.interpret_map] at hreply
        obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
        exact List.length_take_le _ _
    convert hsub using 1
    funext a
    rw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
    congr 1
    funext q
    simp only [ProbOracleComp.interpret_query]
    rfl
  computableInPolyTime_alenCap := by
    exact ((ComputableInPolyTime.unary_eval (compCapPoly R₁ R₂)).comp
      (ComputableInPolyTime.encoding_length encA)).of_enc_eq fun _ => rfl
  eval_eq a := by
    let G (q : Unit × List Bool) : WordQueryComp Unit (List Bool) :=
      List.take (R₁.alenCap a) <$> R₂.program q.2
    rcases R₁.respects_bound a with ⟨_, _, _, hal₁⟩
    have hG (q : Unit × List Bool)
        (hq : q ∈ OracleComp.queriesWith (fun q => oracle₁ q.2) (R₁.program a)) :
        OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2) (G q) = oracle₁ q.2 := by
      dsimp only [G]
      rw [OracleComp.interpret_map, R₂.eval_eq q.2]
      exact List.take_of_length_le ((hal₁ q hq).trans (R₁.alen_le_alenCap a))
    exact (interpret_and_queriesWith_subst oracle₁ oracle₂ G (R₁.program a) hG).1.trans
      (R₁.eval_eq a)
  respects_bound a := by
    let hqb := IsOraclePPTOn.query_bounds R₁.isOraclePPTOn
    let c₁ := Classical.choose hqb
    let hc₁ := Classical.choose_spec hqb
    let d₁ := Classical.choose hc₁
    have hqb₁ : ∀ x, (OracleComp.interpret ProbOracleComp.query (R₁.program x)).IsQueryBounded
          (c₁ * ((encA x).length + 1) ^ d₁) ∧
        (OracleComp.interpret ProbOracleComp.query (R₁.program x)).QueriesSatisfy
          (fun request => request.2.length ≤ c₁ * ((encA x).length + 1) ^ d₁) :=
      Classical.choose_spec hc₁
    have hcap₂_poly : PolyBounded List.length R₂.alenCap := by
      simpa only [encUnary_apply, List.length_replicate, encBits_apply] using
        R₂.computableInPolyTime_alenCap.polyBounded_length
    let hex₂ := hcap₂_poly.exists_le
    let c₂ := Classical.choose hex₂
    let hc₂ := Classical.choose_spec hex₂
    let d₂ := Classical.choose hc₂
    have hcap₂_le : ∀ w : List Bool, R₂.alenCap w ≤ c₂ * (w.length + 1) ^ d₂ :=
      Classical.choose_spec hc₂
    let G (q : Unit × List Bool) : WordQueryComp Unit (List Bool) :=
      List.take (R₁.alenCap a) <$> R₂.program q.2
    rcases R₁.respects_bound a with ⟨hqc₁, hql₁, _, hal₁⟩
    have hG (q : Unit × List Bool)
        (hq : q ∈ OracleComp.queriesWith (fun q => oracle₁ q.2) (R₁.program a)) :
        OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2) (G q) = oracle₁ q.2 := by
      dsimp only [G]
      rw [OracleComp.interpret_map, R₂.eval_eq q.2]
      exact List.take_of_length_le ((hal₁ q hq).trans (R₁.alen_le_alenCap a))
    have hqs := (interpret_and_queriesWith_subst oracle₁ oracle₂ G (R₁.program a) hG).2
    dsimp only [OracleCallBound.Respects, OracleCallBound.comp]
    change (OracleComp.queriesWith (fun q' => oracle₂ q'.2)
        (OracleComp.interpret G (R₁.program a))).length ≤ _ ∧ _
    rw [hqs]
    set qs₁ := OracleComp.queriesWith (fun q => oracle₁ q.2) (R₁.program a)
    have hinner_qs (q : Unit × List Bool) :
        OracleComp.queriesWith (fun q' => oracle₂ q'.2) (G q) =
          OracleComp.queriesWith (fun q' => oracle₂ q'.2) (R₂.program q.2) := by
      dsimp only [G]
      exact OracleComp.queriesWith_map _ _ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.length_flatMap]
      have hsum_le : (qs₁.map fun q =>
          (OracleComp.queriesWith (fun q' => oracle₂ q'.2) (G q)).length).sum ≤
          qs₁.length * wordMax (fun w => (R₂.bound w).qcount) (R₁.bound a).qlen := by
        have hmem : ∀ x ∈ qs₁.map (fun q =>
            (OracleComp.queriesWith (fun q' => oracle₂ q'.2) (G q)).length),
            x ≤ wordMax (fun w => (R₂.bound w).qcount) (R₁.bound a).qlen := by
          intro x hx
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
          rw [hinner_qs]
          rcases R₂.respects_bound q.2 with ⟨hqc₂, _, _, _⟩
          exact hqc₂.trans (le_wordMax (fun w => (R₂.bound w).qcount) (hql₁ q hq))
        simpa only [List.length_map, smul_eq_mul] using List.sum_le_length_nsmul _ _ hmem
      exact hsum_le.trans (Nat.mul_le_mul_right _ hqc₁)
    · intro q' hq'
      obtain ⟨q, hq, hq'_mem⟩ := List.mem_flatMap.mp hq'
      rw [hinner_qs] at hq'_mem
      rcases R₂.respects_bound q.2 with ⟨_, hql₂, _, _⟩
      exact (hql₂ q' hq'_mem).trans
        (le_wordMax (fun w => (R₂.bound w).qlen) (hql₁ q hq))
    · rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
      have hsum_le : (qs₁.map
          ((fun l : List ℕ => l.sum) ∘ fun q =>
            (OracleComp.queriesWith (fun q' => oracle₂ q'.2) (G q)).map
              (fun q' => q'.2.length))).sum ≤
          qs₁.length * wordMax (fun w => (R₂.bound w).totalQlen) (R₁.bound a).qlen := by
        have hmem : ∀ x ∈ qs₁.map
            ((fun l : List ℕ => l.sum) ∘ fun q =>
              (OracleComp.queriesWith (fun q' => oracle₂ q'.2) (G q)).map
                (fun q' => q'.2.length)),
            x ≤ wordMax (fun w => (R₂.bound w).totalQlen) (R₁.bound a).qlen := by
          intro x hx
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
          simp only [Function.comp_apply, hinner_qs]
          rcases R₂.respects_bound q.2 with ⟨_, _, htql₂, _⟩
          exact htql₂.trans (le_wordMax (fun w => (R₂.bound w).totalQlen) (hql₁ q hq))
        simpa only [List.length_map, smul_eq_mul] using List.sum_le_length_nsmul _ _ hmem
      exact hsum_le.trans (Nat.mul_le_mul_right _ hqc₁)
    · intro q' hq'
      obtain ⟨q, hq, hq'_mem⟩ := List.mem_flatMap.mp hq'
      rw [hinner_qs] at hq'_mem
      rcases R₂.respects_bound q.2 with ⟨_, _, _, hal₂⟩
      refine le_min
        ((hal₂ q' hq'_mem).trans (le_wordMax (fun w => (R₂.bound w).alen) (hql₁ q hq))) ?_
      have hq_clk : q.2.length ≤ c₁ * ((encA a).length + 1) ^ d₁ :=
        forall_queriesWith_of_probQueriesSatisfy (fun q => oracle₁ q.2) (R₁.program a)
          (hqb₁ a).2 q hq
      have hcap_eval : (compCapPoly R₁ R₂).eval (encA a).length =
          c₂ * (c₁ * ((encA a).length + 1) ^ d₁ + 1) ^ d₂ := by
        dsimp only [compCapPoly, c₁, d₁, c₂, d₂, hc₁, hc₂, hqb, hex₂]
        simp
      rw [hcap_eval]
      exact ((hal₂ q' hq'_mem).trans (R₂.alen_le_alenCap q.2)).trans
        ((hcap₂_le q.2).trans
          (Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left (Nat.add_le_add_right hq_clk 1) d₂)))
  alen_le_alenCap _ := Nat.min_le_right _ _

@[simp]
theorem qcount_comp {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) (a : α) :
    (R₁.comp R₂).qcount a = R₁.qcount a * wordMax R₂.qcount (R₁.qlen a) := rfl

@[simp]
theorem qlen_comp {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) (a : α) :
    (R₁.comp R₂).qlen a = wordMax R₂.qlen (R₁.qlen a) := rfl

@[simp]
theorem totalQlen_comp {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) (a : α) :
    (R₁.comp R₂).totalQlen a = R₁.qcount a * wordMax R₂.totalQlen (R₁.qlen a) := rfl

theorem alen_comp_le {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁) (a : α) :
    (R₁.comp R₂).alen a ≤ wordMax R₂.alen (R₁.qlen a) :=
  Nat.min_le_left _ _

/-- **Sharper affine `totalQlen` bound under composition:** when `R₂.totalQlen w ≤ scale * |w| +
offset`, the actual sum of inner query lengths along `(R₁.comp R₂).program a` is bounded by
`scale * R₁.totalQlen a + offset * R₁.qcount a`, preserving total-query-length sparsity rather than
multiplying `qcount * qlen`. -/
theorem totalQueryLength_comp_affine {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁)
    {scale offset : ℕ} (haff : ∀ w, R₂.totalQlen w ≤ scale * w.length + offset) (a : α) :
    ((OracleComp.queriesWith (fun q' => oracle₂ q'.2) ((R₁.comp R₂).program a)).map
        fun q' => q'.2.length).sum ≤
      scale * R₁.totalQlen a + offset * R₁.qcount a := by
  rcases R₁.respects_bound a with ⟨hqc₁, _, htql₁, hal₁⟩
  let G (q : Unit × List Bool) : WordQueryComp Unit (List Bool) :=
    List.take (R₁.alenCap a) <$> R₂.program q.2
  have hG (q : Unit × List Bool)
      (hq : q ∈ OracleComp.queriesWith (fun q => oracle₁ q.2) (R₁.program a)) :
      OracleComp.interpret (m := Id) (fun q' => oracle₂ q'.2) (G q) = oracle₁ q.2 := by
    dsimp only [G]
    rw [OracleComp.interpret_map, R₂.eval_eq q.2]
    exact List.take_of_length_le ((hal₁ q hq).trans (R₁.alen_le_alenCap a))
  have hqs : OracleComp.queriesWith (fun q' => oracle₂ q'.2) ((R₁.comp R₂).program a) =
      (OracleComp.queriesWith (fun q => oracle₁ q.2) (R₁.program a)).flatMap fun q =>
        OracleComp.queriesWith (fun q' => oracle₂ q'.2) (G q) :=
    (interpret_and_queriesWith_subst oracle₁ oracle₂ G (R₁.program a) hG).2
  rw [hqs, List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
  set qs₁ := OracleComp.queriesWith (fun q => oracle₁ q.2) (R₁.program a)
  have hstep := list_sum_affine_le
    (fun q : Unit × List Bool =>
      ((OracleComp.queriesWith (fun q' => oracle₂ q'.2) (G q)).map fun q' => q'.2.length).sum)
    (fun q => q.2.length) scale offset qs₁ fun q _ => by
      dsimp only [G]
      rw [OracleComp.queriesWith_map]
      rcases R₂.respects_bound q.2 with ⟨_, _, htql₂, _⟩
      exact htql₂.trans (haff q.2)
  have hmul₁ : scale * (qs₁.map fun q => q.2.length).sum ≤ scale * R₁.totalQlen a :=
    Nat.mul_le_mul_left scale htql₁
  have hmul₂ : offset * qs₁.length ≤ offset * R₁.qcount a :=
    Nat.mul_le_mul_left offset hqc₁
  simpa only [Function.comp_def] using hstep.trans (Nat.add_le_add hmul₁ hmul₂)

/-- Composed `BoundedOracleProgram` refining `comp` with the sharper linear `totalQlen` budget
`scale * R₁.totalQlen a + offset * R₁.qcount a` when `R₂.totalQlen` is affine in query length. -/
@[expose]
noncomputable def compAffine {oracle₁ oracle₂ : List Bool → List Bool} {f : α → β}
    (R₁ : BoundedOracleProgram encA encB oracle₁ f)
    (R₂ : BoundedOracleProgram encBits encBits oracle₂ oracle₁)
    {scale offset : ℕ} (haff : ∀ w, R₂.totalQlen w ≤ scale * w.length + offset) :
    BoundedOracleProgram encA encB oracle₂ f := by
  let C := R₁.comp R₂
  exact
    { program := C.program
      bound := fun a =>
        { C.bound a with totalQlen := scale * R₁.totalQlen a + offset * R₁.qcount a }
      alenCap := C.alenCap
      isOraclePPTOn := C.isOraclePPTOn
      computableInPolyTime_alenCap := C.computableInPolyTime_alenCap
      eval_eq := C.eval_eq
      respects_bound := fun a => by
        rcases C.respects_bound a with ⟨hqc, hql, _, hal⟩
        exact ⟨hqc, hql, totalQueryLength_comp_affine R₁ R₂ haff a, hal⟩
      alen_le_alenCap := C.alen_le_alenCap }

/-- **Polynomial-time transfer for multi-bit word oracles:** if `oracle : List Bool → List Bool` is
computable in polynomial time, any `BoundedOracleProgram` relative to `oracle` is computable in
polynomial time. -/
theorem computableInPolyTime {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f)
    (horacle : ComputableInPolyTime oracle encBits encBits) :
    ComputableInPolyTime f encA encB := by
  obtain ⟨_, _, machine, c, d, hrun⟩ := R.isOraclePPTOn.exists_fin_run_pure_false
  refine (machine.computableInPolyTime_run_word (input := encA) horacle c d).of_enc_eq fun a => ?_
  rw [← R.eval_eq a, ← hrun a (fun q => oracle q.2)]
  rfl

/-- **Explicit `ComputableInO` transfer in polynomial workspace for multi-bit word oracles:**
simulating `R` against `ComputableInO oracle encBits encBits Tg Sg` uses **polynomial workspace**
(depending only on input length, machine clock, answer-length growth, and `Sg` — never on `Tg`)
and charges `Tg` at most once per step up to the polynomial clock. -/
theorem exists_computableInO_polySpace {oracle : List Bool → List Bool} {f : α → β}
    {Tg Sg : List Bool → ℕ}
    (R : BoundedOracleProgram encA encB oracle f)
    (horacle : ComputableInO oracle encBits encBits Tg Sg)
    (hSg : PolyBounded List.length Sg) :
    ∃ (c₀ e₀ : ℕ) (S : α → ℕ), PolyBounded (fun a => (encA a).length) S ∧
      ∃ c₁ d₁ : ℕ,
        ComputableInO f encA encB
          (fun a => c₀ * ((encA a).length + 1) ^ e₀ +
            (c₁ * ((encA a).length + 1) ^ d₁ + 1) *
              (c₀ * ((encA a).length + 1) ^ e₀ +
                wordMax Tg (c₁ * ((encA a).length + 1) ^ d₁)))
          S := by
  obtain ⟨_, _, machine, c₁, d₁, hrun⟩ := R.isOraclePPTOn.exists_fin_run_pure_false
  obtain ⟨c₀, e₀, S, hSPoly, hcomp⟩ :=
    machine.exists_computableInO_run_word (input := encA) horacle hSg c₁ d₁
  refine ⟨c₀, e₀, S, hSPoly, c₁, d₁, hcomp.of_enc_eq fun a => ?_⟩
  rw [← R.eval_eq a, ← hrun a (fun q => oracle q.2)]
  rfl

/-- **Polynomial-space transfer for multi-bit word oracles:** if `oracle : List Bool → List Bool` is
computable in polynomial space, any `BoundedOracleProgram` relative to `oracle` is computable in
polynomial space. -/
theorem computableInPolySpace {oracle : List Bool → List Bool} {f : α → β}
    (R : BoundedOracleProgram encA encB oracle f)
    (horacle : ComputableInPolySpace oracle encBits encBits) :
    ComputableInPolySpace f encA encB := by
  obtain ⟨t, s, hs, hc, hl⟩ := horacle
  have hO : ComputableInO oracle encBits encBits t (fun w => s w.length) :=
    (hc.computableTidilyInO hl).computableInO
  have hsPoly : PolyBounded List.length (fun w : List Bool => s w.length) :=
    .of_polynomiallyBounded List.length hs
  obtain ⟨_, _, S, hSPoly, _, _, c, htm, hout⟩ := R.exists_computableInO_polySpace hO hsPoly
  exact ComputableInPolySpace.of_inSpace hSPoly ⟨_, c, htm, hout⟩

end BoundedOracleProgram

/-! ### `BoundedOracleReduction`: language oracle reductions with explicit call profiles -/

/-- Word-oracle adapter for a typed decision problem `(B, encB)`: maps `w : List Bool` to
`[decide (w ∈ encB '' B)]`, matching `languageOracle (encB '' B) ((), w)`. -/
@[expose]
noncomputable def encodedDecisionOracle {β : Type} (encB : β ↪ List Bool) (B : Set β)
    (w : List Bool) : List Bool :=
  languageOracle (encB '' B) ((), w)

@[simp]
theorem length_encodedDecisionOracle {β : Type} (encB : β ↪ List Bool) (B : Set β)
    (w : List Bool) : (encodedDecisionOracle encB B w).length = 1 := by
  simp [encodedDecisionOracle, languageOracle]

/-- **Deterministic adaptive oracle reduction between decision problems `(A, encA)` and `(B, encB)`
with explicit `(qcount, qlen, totalQlen, alen)` call accounting.** -/
structure BoundedOracleReduction {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) where
  /-- Deterministic adaptive word-query decider program. -/
  program : α → WordQueryComp Unit Bool
  /-- Explicit `(qcount, qlen, totalQlen, alen)` call profile on each input. -/
  bound : α → OracleCallBound
  /-- Strict oracle-PPT machine realization across all stateful handlers. -/
  isOraclePPTOn :
    IsOraclePPTOn encA encBool (fun a => OracleComp.interpret ProbOracleComp.query (program a))
  /-- Decision correctness relative to `encB '' B`. -/
  decides : ∀ a,
    a ∈ A ↔ OracleComp.interpret (m := Id) (languageOracle (encB '' B)) (program a) = true
  /-- Every run against `encB '' B` respects `bound a`. -/
  respects_bound : ∀ a,
    OracleCallBound.Respects (encodedDecisionOracle encB B) (program a) (bound a)

namespace BoundedOracleReduction

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}

/-- Number of oracle queries budgeted on `a`. -/
@[expose] def qcount {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) (a : α) : ℕ := (R.bound a).qcount

/-- Per-query length budgeted on `a`. -/
@[expose] def qlen {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) (a : α) : ℕ := (R.bound a).qlen

/-- Total query length budgeted on `a`. -/
@[expose] def totalQlen {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) (a : α) : ℕ := (R.bound a).totalQlen

/-- Per-answer length budgeted on `a`. -/
@[expose] def alen {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) (a : α) : ℕ := (R.bound a).alen

/-- Weaken the call bound of a `BoundedOracleReduction` to any coordinatewise larger profile. -/
@[expose]
def mono {A : Set α} {B : Set β} (R : BoundedOracleReduction encA encB A B)
    {bound' : α → OracleCallBound} (h : ∀ a, (R.bound a).Le (bound' a)) :
    BoundedOracleReduction encA encB A B where
  program := R.program
  bound := bound'
  isOraclePPTOn := R.isOraclePPTOn
  decides := R.decides
  respects_bound a := (R.respects_bound a).mono (h a)

/-- Build a `BoundedOracleReduction` from a `BoundedOracleProgram` computing a decider `f` for `A`
against `encodedDecisionOracle encB B`. -/
@[expose]
def ofProgram {A : Set α} {B : Set β} {f : α → Bool}
    (P : BoundedOracleProgram encA encBool (encodedDecisionOracle encB B) f)
    (hf : ∀ a, a ∈ A ↔ f a = true) :
    BoundedOracleReduction encA encB A B where
  program := P.program
  bound := P.bound
  isOraclePPTOn := P.isOraclePPTOn
  decides a := by
    rw [hf a]
    have heq : (fun q : Unit × List Bool => encodedDecisionOracle encB B q.2) =
        languageOracle (encB '' B) := rfl
    rw [← P.eval_eq a, heq]
  respects_bound := P.respects_bound

open Classical in
/-- View a `BoundedOracleReduction` as a `BoundedOracleProgram` computing `fun a => decide (a ∈ A)`
with unary answer-length cap `1`. -/
@[expose]
noncomputable def toProgram {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) :
    BoundedOracleProgram encA encBool (encodedDecisionOracle encB B)
      (fun a => decide (a ∈ A)) where
  program := R.program
  bound a := { R.bound a with alen := min (R.bound a).alen 1 }
  alenCap _ := 1
  isOraclePPTOn := R.isOraclePPTOn
  computableInPolyTime_alenCap := .const 1
  eval_eq a := by
    have heq : (fun q : Unit × List Bool => encodedDecisionOracle encB B q.2) =
        languageOracle (encB '' B) := rfl
    rw [heq]
    exact Bool.eq_iff_iff.mpr ⟨fun h => decide_eq_true ((R.decides a).mpr h),
      fun h => (R.decides a).mp (of_decide_eq_true h)⟩
  respects_bound a := by
    rcases R.respects_bound a with ⟨hqc, hql, htql, hal⟩
    refine ⟨hqc, hql, htql, fun q hq => le_min (hal q hq) ?_⟩
    simp only [length_encodedDecisionOracle, le_refl]
  alen_le_alenCap _ := Nat.min_le_right _ _

/-- A problem in `P` has a `0`-query `BoundedOracleReduction` to every problem `B`. -/
@[expose]
noncomputable def ofPolyTime {A : Set α} (B : Set β) {f : α → Bool}
    (hf : ComputableInPolyTime f encA encBool) (hA : ∀ a, a ∈ A ↔ f a = true) :
    BoundedOracleReduction encA encB A B :=
  ofProgram (BoundedOracleProgram.ofPolyTime hf (encodedDecisionOracle encB B)) hA

/-- **Single-query lift from `SizeSensitiveReduction`:** a many-one `SizeSensitiveReduction` lifts
to a `1`-query `BoundedOracleReduction` with `qlen = totalQlen = |encB (R.toFun a)|` and `alen = 1`.
-/
@[expose]
noncomputable def ofSizeSensitive {A : Set α} {B : Set β} {μA : α → ℕ} {μB : β → ℕ}
    (R : SizeSensitiveReduction encA encB μA μB)
    (hAB : ∀ a, a ∈ A ↔ R.toFun a ∈ B) :
    BoundedOracleReduction encA encB A B := by
  let req (a : α) : List Bool := encB (R.toFun a)
  have hreq : ComputableInPolyTime req encA encBits :=
    R.computableInPolyTime_toFun.of_enc_eq fun _ => rfl
  have hdec : ComputableInPolyTime
      (fun p : α × List Bool => p.2.headD false) (encPair encA encBits) encBool :=
    Decoder.bool.computableInPolyTime.comp (ComputableInPolyTime.snd encA encBits)
  let P := BoundedOracleProgram.ofSingleQuery (oracle := encodedDecisionOracle encB B)
    (req := req) (alenCap := fun _ => 1) (decode := fun p => p.2.headD false)
    hreq (.const 1) hdec (fun a => by simp only [length_encodedDecisionOracle, le_refl])
  refine ofProgram P fun a => ?_
  dsimp only [req, encodedDecisionOracle, languageOracle]
  simp only [List.headD_cons, decide_eq_true_eq, encB.injective.mem_set_image]
  exact hAB a

/-- **Identity / reflexivity (`refl`)** of `BoundedOracleReduction`: `1` query of length `|encA a|`
and `1`-bit reply. -/
@[expose]
noncomputable def refl (encA : α ↪ List Bool) (A : Set α) :
    BoundedOracleReduction encA encA A A :=
  ofSizeSensitive (SizeSensitiveReduction.refl encA (fun _ => 0)) (fun _ => Iff.rfl)

/-- Complement the source language `Aᶜ` without changing the `OracleCallBound` profile. -/
@[expose]
def complLeft {A : Set α} {B : Set β} (R : BoundedOracleReduction encA encB A B) :
    BoundedOracleReduction encA encB Aᶜ B where
  program a := Bool.not <$> R.program a
  bound := R.bound
  isOraclePPTOn := by
    have hnot : ComputableInPolyTime Bool.not encBool encBool :=
      ComputableTidilyInPolyTime.bool_not.computableInPolyTime
    simpa only [OracleComp.interpret_map] using R.isOraclePPTOn.map' hnot
  decides a := by
    rw [Set.mem_compl_iff, R.decides a, OracleComp.interpret_map]
    change ¬(_ = true) ↔ (!(OracleComp.interpret (m := Id) _ (R.program a))) = true
    cases OracleComp.interpret (m := Id) (languageOracle (encB '' B)) (R.program a) <;> simp
  respects_bound a :=
    (OracleCallBound.respects_map (encodedDecisionOracle encB B) Bool.not (R.program a)
      (R.bound a)).mpr (R.respects_bound a)

/-- Every language's complement reduces to the language itself via `1` query (`Aᶜ ≤ B` for `B = A`).
-/
@[expose]
noncomputable def complSelf (encA : α ↪ List Bool) (A : Set α) :
    BoundedOracleReduction encA encA Aᶜ A :=
  (refl encA A).complLeft

/-- Lift a typed `BoundedOracleReduction encB encC B C` to a word-level `BoundedOracleProgram`
answering `encodedDecisionOracle encB B` via a total polynomial-time `D : Decoder encB`:
non-canonical words (`encB (D.decode w) ≠ w`) are rejected in `0` queries, while canonical
encodings run `R₂`. -/
@[expose]
noncomputable def toDecodedWordProgram {B : Set β} {C : Set γ}
    (D : Decoder encB) (R₂ : BoundedOracleReduction encB encC B C) :
    BoundedOracleProgram encBits encBits
      (encodedDecisionOracle encC C) (encodedDecisionOracle encB B) := by
  classical
  let isCan (w : List Bool) : Bool := decide (encB (D.decode w) = w)
  have hreenc : ComputableInPolyTime (fun b : β => (encB b : List Bool)) encB encBits :=
    ComputableInPolyTime.id'.of_enc_eq fun _ => rfl
  have hisCan : ComputableInPolyTime isCan encBits encBool :=
    ((hreenc.comp D.computableInPolyTime).tidy.decide_eq' .id').computableInPolyTime
  have hsingleton : ComputableInPolyTime (fun b : Bool => [b]) encBool encBits :=
    ComputableInPolyTime.id'.of_enc_eq fun b => (encBool_apply b).symm
  let yesProg (w : List Bool) : WordQueryComp Unit (List Bool) :=
    (fun b => [b]) <$> R₂.program (D.decode w)
  have hyes_ppt : IsOraclePPTOn encBits encBits
      (fun w => OracleComp.interpret ProbOracleComp.query (yesProg w)) := by
    have hpre := R₂.isOraclePPTOn.preprocess' D.computableInPolyTime
    simpa only [yesProg, OracleComp.interpret_map] using hpre.map' hsingleton
  have hno_ppt : IsOraclePPTOn encBits encBits
      (fun _ : List Bool =>
        OracleComp.interpret (spec := fun _ : Unit × List Bool => List Bool)
          ProbOracleComp.query (pure [false])) := by
    simpa only [OracleComp.interpret_pure] using
      (ComputableInPolyTime.const (encIn := encBits) (encOut := encBits) [false]).isOraclePPTOn
  refine
    { program := fun w => if isCan w then yesProg w else pure [false]
      bound := fun w =>
        if isCan w then { R₂.bound (D.decode w) with alen := 1 } else OracleCallBound.zero
      alenCap := fun _ => 1
      isOraclePPTOn := by
        refine (IsOraclePPTOn.cond' hisCan hyes_ppt hno_ppt).congr fun w _ _ _ => ?_
        by_cases hc : isCan w = true <;> simp [hc]
      computableInPolyTime_alenCap := .const 1
      eval_eq := fun w => ?_
      respects_bound := fun w => ?_
      alen_le_alenCap := fun w => by split_ifs <;> simp [OracleCallBound.zero] }
  · by_cases hc : isCan w = true
    · simp only [hc, ↓reduceIte, yesProg, OracleComp.interpret_map, encodedDecisionOracle]
      have hcan : encB (D.decode w) = w := of_decide_eq_true hc
      have hmem : w ∈ encB '' B ↔ D.decode w ∈ B := by
        conv_lhs => rw [← hcan]
        exact encB.injective.mem_set_image
      have heq : (fun q : Unit × List Bool => languageOracle (encC '' C) ((), q.2)) =
          languageOracle (encC '' C) := rfl
      rw [heq]
      change [OracleComp.interpret (m := Id) (languageOracle (encC '' C))
        (R₂.program (D.decode w))] = [decide (w ∈ encB '' B)]
      congr 1
      exact Bool.eq_iff_iff.mpr ⟨fun h => decide_eq_true (hmem.mpr ((R₂.decides _).mpr h)),
        fun h => (R₂.decides _).mp (hmem.mp (of_decide_eq_true h))⟩
    · have hnc : isCan w = false := Bool.eq_false_iff.mpr hc
      simp only [hnc, Bool.false_eq_true, ↓reduceIte, encodedDecisionOracle, languageOracle]
      have hnotmem : w ∉ encB '' B := by
        rintro ⟨b, _, rfl⟩
        have : isCan (encB b) = true := by simp [isCan, D.decode_enc]
        rw [this] at hnc
        exact Bool.noConfusion hnc
      simp only [OracleComp.interpret_pure, hnotmem, decide_false]
      rfl
  · by_cases hc : isCan w = true
    · simp only [hc, ↓reduceIte]
      have hresp : OracleCallBound.Respects (encodedDecisionOracle encC C) (yesProg w)
          (R₂.bound (D.decode w)) :=
        (OracleCallBound.respects_map (encodedDecisionOracle encC C) (fun b => [b])
          (R₂.program (D.decode w)) (R₂.bound (D.decode w))).mpr
          (R₂.respects_bound (D.decode w))
      rcases hresp with ⟨hqc, hql, htql, _⟩
      refine ⟨hqc, hql, htql, fun q _ => ?_⟩
      simp only [length_encodedDecisionOracle, le_refl]
    · have hnc : isCan w = false := Bool.eq_false_iff.mpr hc
      simp only [hnc, Bool.false_eq_true, ↓reduceIte]
      exact OracleCallBound.respects_pure _ _ _

/-- **Transitivity (`transDecoded`) across any typed intermediate language `(B, encB)` equipped
with `D : Decoder encB`,** tracking explicit `(qcount, qlen, totalQlen, alen)` composition. -/
@[expose]
noncomputable def transDecoded {A : Set α} {B : Set β} {C : Set γ}
    (D : Decoder encB)
    (R₁ : BoundedOracleReduction encA encB A B)
    (R₂ : BoundedOracleReduction encB encC B C) :
    BoundedOracleReduction encA encC A C :=
  ofProgram (R₁.toProgram.comp (R₂.toDecodedWordProgram D)) (fun _ => by simp)

/-- **Transitivity (`trans`) across word-encoded intermediate languages `(B, encBits)`.** -/
@[expose]
noncomputable def trans {A : Set α} {B : Set (List Bool)} {C : Set γ}
    (R₁ : BoundedOracleReduction encA encBits A B)
    (R₂ : BoundedOracleReduction encBits encC B C) :
    BoundedOracleReduction encA encC A C :=
  R₁.transDecoded Decoder.bits R₂

/-! ### Bridges to `PolyTimeTuringReducible`, `PWithOracleQueries`, `P`, and `PSPACE` -/

/-- Every `BoundedOracleReduction` witnesses `PolyTimeTuringReducible` (`A ≤ᵖ_T B`). -/
theorem polyTimeTuringReducible {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) :
    PolyTimeTuringReducible encA encB A B := by
  classical
  exact ⟨fun a => decide (a ∈ A),
    ⟨R.program, R.isOraclePPTOn, fun a => R.toProgram.eval_eq a⟩,
    fun _ => by simp⟩

/-- If `R.qcount a ≤ r (encA a).length` for all `a`, then `R` places `A` in
`PWithOracleQueries (encB '' B) r encA`. -/
theorem mem_PWithOracleQueries {A : Set α} {B : Set β}
    (R : BoundedOracleReduction encA encB A B) {r : ℕ → ℕ}
    (hr : ∀ a, R.qcount a ≤ r (encA a).length) :
    A ∈ PWithOracleQueries (encB '' B) r encA := by
  classical
  refine ⟨fun a => decide (a ∈ A), ⟨R.program, R.isOraclePPTOn, fun a => ⟨?_, ?_⟩⟩,
    fun _ => by simp⟩
  · exact R.toProgram.eval_eq a
  · rcases R.respects_bound a with ⟨hqc, _, _, _⟩
    have heq : (fun q : Unit × List Bool => encodedDecisionOracle encB B q.2) =
        languageOracle (encB '' B) := rfl
    rw [← heq]
    exact hqc.trans (hr a)

/-- Conversely, any membership witness `A ∈ PWithOracleQueries (encB '' B) r encA` yields a
`BoundedOracleReduction encA encB A B` with `qcount a = r |encA a|`, polynomial `qlen`,
`totalQlen = qcount * qlen`, and `alen = 1`. -/
noncomputable def ofPWithOracleQueries {A : Set α} {B : Set β} {r : ℕ → ℕ}
    (h : A ∈ PWithOracleQueries (encB '' B) r encA) :
    BoundedOracleReduction encA encB A B := by
  classical
  let f := Classical.choose h
  have hf_spec := Classical.choose_spec h
  let prog := Classical.choose hf_spec.1
  have hprog := Classical.choose_spec hf_spec.1
  let hqb_ex := IsOraclePPTOn.query_bounds hprog.1
  let c := Classical.choose hqb_ex
  let hc := Classical.choose_spec hqb_ex
  let d := Classical.choose hc
  have hqb : ∀ a, (OracleComp.interpret ProbOracleComp.query (prog a)).IsQueryBounded
        (c * ((encA a).length + 1) ^ d) ∧
      (OracleComp.interpret ProbOracleComp.query (prog a)).QueriesSatisfy
        (fun request => request.2.length ≤ c * ((encA a).length + 1) ^ d) :=
    Classical.choose_spec hc
  let ql (a : α) : ℕ := c * ((encA a).length + 1) ^ d
  refine
    { program := prog
      bound := fun a =>
        { qcount := r (encA a).length
          qlen := ql a
          totalQlen := r (encA a).length * ql a
          alen := 1 }
      isOraclePPTOn := hprog.1
      decides := fun a => by rw [hf_spec.2 a, (hprog.2 a).1]
      respects_bound := fun a => ?_ }
  have heq : (fun q : Unit × List Bool => encodedDecisionOracle encB B q.2) =
      languageOracle (encB '' B) := rfl
  dsimp only [OracleCallBound.Respects]
  have hqc : (OracleComp.queriesWith (fun q => encodedDecisionOracle encB B q.2)
      (prog a)).length ≤ r (encA a).length := by
    rw [heq]
    exact (hprog.2 a).2
  have hql : ∀ q ∈ OracleComp.queriesWith (fun q => encodedDecisionOracle encB B q.2) (prog a),
      q.2.length ≤ ql a :=
    forall_queriesWith_of_probQueriesSatisfy _ (prog a) (hqb a).2
  refine ⟨hqc, hql, ?_, fun q _ => by simp only [length_encodedDecisionOracle, le_refl]⟩
  set qs := OracleComp.queriesWith (fun q => encodedDecisionOracle encB B q.2) (prog a)
  have hsum : (qs.map fun q => q.2.length).sum ≤ qs.length * ql a := by
    have hmem : ∀ x ∈ qs.map (fun q => q.2.length), x ≤ ql a := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact hql q hq
    simpa only [List.length_map, smul_eq_mul] using List.sum_le_length_nsmul _ _ hmem
  exact hsum.trans (Nat.mul_le_mul_right (ql a) hqc)

/-- **Polynomial-time transfer (`mem_P`)** across `BoundedOracleReduction` when `D : Decoder encB`
and `B ∈ P encB`. -/
theorem mem_P {A : Set α} {B : Set β} (D : Decoder encB)
    (R : BoundedOracleReduction encA encB A B) (hB : B ∈ P encB) :
    A ∈ P encA := by
  classical
  obtain ⟨g, hg, hgB⟩ := hB
  let R_P : BoundedOracleReduction encB encBits B ∅ := ofPolyTime ∅ hg hgB
  let R_comp := R.transDecoded D R_P
  have horacle : ComputableInPolyTime (encodedDecisionOracle encBits ∅) encBits encBits :=
    (ComputableInPolyTime.const (encIn := encBits) (encOut := encBits) [false]).of_enc_eq
      fun w => by simp [encodedDecisionOracle, languageOracle]
  exact ⟨_, R_comp.toProgram.computableInPolyTime horacle, fun _ => by simp⟩

/-- **Polynomial-space transfer (`mem_PSPACE`)** across `BoundedOracleReduction` when
`D : Decoder encB` and `B ∈ PSPACE encB`. -/
theorem mem_PSPACE {A : Set α} {B : Set β} (D : Decoder encB)
    (R : BoundedOracleReduction encA encB A B) (hB : B ∈ PSPACE encB) :
    A ∈ PSPACE encA := by
  classical
  obtain ⟨T, S, hS, g, hg, hgB⟩ := exists_computableInO_of_mem_PSPACE hB
  let isCan (w : List Bool) : Bool := decide (encB (D.decode w) = w)
  have hreenc : ComputableInPolyTime (fun b : β => (encB b : List Bool)) encB encBits :=
    ComputableInPolyTime.id'.of_enc_eq fun _ => rfl
  have hisCan : ComputableInPolyTime isCan encBits encBool :=
    ((hreenc.comp D.computableInPolyTime).tidy.decide_eq' .id').computableInPolyTime
  have hg_ps : ComputableInPolySpace g encB encBool := by
    obtain ⟨c, htm, hout⟩ := hg
    exact ComputableInPolySpace.of_inSpace hS ⟨_, c, htm, hout⟩
  have hdecB_ps : ComputableInPolySpace (fun w : List Bool =>
      if isCan w then g (D.decode w) else false) encBits encBool :=
    ComputableInPolySpace.ite (ComputableInPolySpace.of_polyTime hisCan)
      (hg_ps.comp (ComputableInPolySpace.of_polyTime D.computableInPolyTime))
      (ComputableInPolySpace.of_polyTime (.const false))
  have hsingleton : ComputableInPolySpace (fun b : Bool => [b]) encBool encBits :=
    ComputableInPolySpace.of_polyTime (ComputableInPolyTime.id'.of_enc_eq fun b =>
      (encBool_apply b).symm)
  have horacle_eq : encodedDecisionOracle encB B =
      fun w => [if isCan w then g (D.decode w) else false] := by
    funext w
    simp only [encodedDecisionOracle, languageOracle]
    congr 1
    by_cases hc : isCan w = true
    · simp only [hc, ↓reduceIte]
      have hcan : encB (D.decode w) = w := of_decide_eq_true hc
      have hmem : w ∈ encB '' B ↔ D.decode w ∈ B := by
        conv_lhs => rw [← hcan]
        exact encB.injective.mem_set_image
      exact Bool.eq_iff_iff.mpr ⟨fun h => (hgB _).mp (hmem.mp (of_decide_eq_true h)),
        fun h => decide_eq_true (hmem.mpr ((hgB _).mpr h))⟩
    · have hnc : isCan w = false := Bool.eq_false_iff.mpr hc
      simp only [hnc, Bool.false_eq_true, ↓reduceIte]
      have hnotmem : w ∉ encB '' B := by
        rintro ⟨b, _, rfl⟩
        have : isCan (encB b) = true := by simp [isCan, D.decode_enc]
        rw [this] at hnc
        exact Bool.noConfusion hnc
      simp [hnotmem]
  have horacle : ComputableInPolySpace (encodedDecisionOracle encB B) encBits encBits := by
    rw [horacle_eq]
    exact hsingleton.comp hdecB_ps
  have hf_ps := R.toProgram.computableInPolySpace horacle
  exact ⟨_, hf_ps, fun _ => by simp⟩

/-! ### Parameterized exponential and subexponential oracle transfer -/

/-- Internal simulator state pairing a fixed parameter budget `budget = scale * μA a + offset`
with the live `FiniteConfig` of the deterministic oracle machine. -/
private structure GuardedOracleState (k m : ℕ) where
  budget : ℕ
  cfg : Turing.MultiTapeMachine.FiniteConfig k Bool (Fin m) Unit

private noncomputable def encGuardedOracleState {k m : ℕ} :
    GuardedOracleState k m ↪ List Bool where
  toFun s := encPair encNat encFiniteConfig (s.budget, s.cfg)
  inj' s₁ s₂ h := by
    have hp := (encPair encNat encFiniteConfig).injective h
    cases s₁; cases s₂
    cases hp
    rfl

@[simp]
private theorem encGuardedOracleState_apply {k m : ℕ} (s : GuardedOracleState k m) :
    encGuardedOracleState s = encPair encNat encFiniteConfig (s.budget, s.cfg) := rfl

private theorem guardedOracleState_parts {k m : ℕ} :
    ComputableInPolyTime (fun s : GuardedOracleState k m => (s.budget, s.cfg))
      encGuardedOracleState (encPair encNat encFiniteConfig) :=
  (ComputableInPolyTime.id' (encIn := encGuardedOracleState)).of_enc_eq fun _ => rfl

private theorem computableInPolyTime_guardedBudget {k m : ℕ} :
    ComputableInPolyTime (GuardedOracleState.budget (k := k) (m := m))
      encGuardedOracleState encNat :=
  guardedOracleState_parts.fst'

private theorem computableInPolyTime_guardedCfg {k m : ℕ} :
    ComputableInPolyTime (GuardedOracleState.cfg (k := k) (m := m))
      encGuardedOracleState encFiniteConfig :=
  guardedOracleState_parts.snd'

private theorem computableInPolyTime_guardedMk {k m : ℕ} {ι : Type} {encI : ι ↪ List Bool}
    {fb : ι → ℕ} {fc : ι → Turing.MultiTapeMachine.FiniteConfig k Bool (Fin m) Unit}
    (hb : ComputableInPolyTime fb encI encNat)
    (hc : ComputableInPolyTime fc encI encFiniteConfig) :
    ComputableInPolyTime (fun x => GuardedOracleState.mk (fb x) (fc x))
      encI encGuardedOracleState :=
  (hb.prod hc).of_enc_eq fun _ => rfl

/-- **Parameterized exponential-time transfer across `BoundedOracleReduction`:**
when `D : Decoder encB` decodes canonical `encB`-words in polynomial time, `μA` and `μB` are
polynomial-time computable, and every query `q` issued by `R.program a` against `encB '' B`
with `encB b = q.2` satisfies `μB b ≤ scale * μA a + offset`, any `2 ^ (δ * μB b) * poly(|b|)`
decider for `B` transfers to a `2 ^ ((scale * δ) * μA a) * poly(|a|)` decider for `A` — with
polynomial overhead absorbing both query count and query construction cost. -/
theorem decidableInExpTime {A : Set α} {B : Set β} {μA : α → ℕ} {μB : β → ℕ}
    (D : Decoder encB)
    (R : BoundedOracleReduction encA encB A B)
    {scale offset : ℕ}
    (hμA : ComputableInPolyTime μA encA encNat)
    (hμB : ComputableInPolyTime μB encB encNat)
    (hparam : ∀ a q,
      q ∈ OracleComp.queriesWith (languageOracle (encB '' B)) (R.program a) →
        ∀ b, encB b = q.2 → μB b ≤ scale * μA a + offset)
    {δ : ℝ} (hδ : 0 ≤ δ) (hB : DecidableInExpTime B encB μB δ) :
    DecidableInExpTime A encA μA (scale * δ) := by
  classical
  obtain ⟨e, h⟩ := hB
  obtain ⟨g, t, k_cost, hg, hgB, ht⟩ := h.exists_computableInO
  obtain ⟨k_tm, m_tm, machine, c_clk, d_clk, hrun⟩ := R.isOraclePPTOn.exists_fin_run_pure_false
  let _ : Inhabited β := ⟨D.decode []⟩
  let _ : Inhabited (GuardedOracleState k_tm m_tm) :=
    ⟨⟨0, Turing.MultiTapeMachine.FiniteConfig.init machine.initial []⟩⟩
  let isCan (w : List Bool) : Bool := decide (encB (D.decode w) = w)
  have hreenc : ComputableInPolyTime (fun b : β => (encB b : List Bool)) encB encBits :=
    ComputableInPolyTime.id'.of_enc_eq fun _ => rfl
  have hisCan : ComputableInPolyTime isCan encBits encBool :=
    ((hreenc.comp D.computableInPolyTime).tidy.decide_eq' .id').computableInPolyTime
  let guardAns (K : ℕ) (w : List Bool) : Bool :=
    if isCan w && decide (μB (D.decode w) ≤ K) then g (D.decode w) else false
  let stepGuard (s : GuardedOracleState k_tm m_tm) : GuardedOracleState k_tm m_tm :=
    ⟨s.budget, machine.answerStep (fun q => [guardAns s.budget q.2]) s.cfg⟩
  let isActive (s : GuardedOracleState k_tm m_tm) : Bool :=
    (machine.pendingQuery s.cfg).isSome &&
      (isCan (machine.pendingRequest s.cfg) &&
        decide (μB (D.decode (machine.pendingRequest s.cfg)) ≤ s.budget))
  let subinst (s : GuardedOracleState k_tm m_tm) : β :=
    D.decode (machine.pendingRequest s.cfg)
  let localStep (s : GuardedOracleState k_tm m_tm) : GuardedOracleState k_tm m_tm :=
    ⟨s.budget, machine.answerStep (fun _ => [false]) s.cfg⟩
  let combine (p : GuardedOracleState k_tm m_tm × Bool) : GuardedOracleState k_tm m_tm :=
    ⟨p.1.budget, machine.receiveWord (p.1.cfg, [p.2])⟩
  have hstep_eq (s : GuardedOracleState k_tm m_tm) :
      stepGuard s =
        (if false then s else if isActive s then combine (s, g (subinst s)) else localStep s) := by
    rcases s with ⟨K, cfg⟩
    dsimp only [stepGuard, isActive, subinst, combine, localStep]
    rw [machine.answerStep_word (fun w => [guardAns K w]) cfg,
      machine.answerStep_word (fun _ => [false]) cfg]
    by_cases hpq : (machine.pendingQuery cfg).isSome = true
    · simp only [hpq, ↓reduceIte, Bool.true_and, Bool.false_eq_true, guardAns]
      by_cases hc : (isCan (machine.pendingRequest cfg) &&
          decide (μB (D.decode (machine.pendingRequest cfg)) ≤ K)) = true
      · simp only [hc, ↓reduceIte]
      · have hnc : (isCan (machine.pendingRequest cfg) &&
            decide (μB (D.decode (machine.pendingRequest cfg)) ≤ K)) = false :=
          Bool.eq_false_iff.mpr hc
        simp only [hnc, Bool.false_eq_true, ↓reduceIte]
    · have hnpq : (machine.pendingQuery cfg).isSome = false := Bool.eq_false_iff.mpr hpq
      simp only [hnpq, Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  -- Polynomial-time certificates for all local pieces of `stepGuard`.
  have hcfg_pt := computableInPolyTime_guardedCfg (k := k_tm) (m := m_tm)
  have hbud_pt := computableInPolyTime_guardedBudget (k := k_tm) (m := m_tm)
  have hpend_pt : ComputableInPolyTime
      (fun s : GuardedOracleState k_tm m_tm => machine.pendingRequest s.cfg)
      encGuardedOracleState encBits :=
    machine.pendingRequest_pt.comp hcfg_pt
  have hsubinst_pt : ComputableInPolyTime subinst encGuardedOracleState encB :=
    D.computableInPolyTime.comp hpend_pt
  have hisSome_pt : ComputableInPolyTime
      (fun s : GuardedOracleState k_tm m_tm => (machine.pendingQuery s.cfg).isSome)
      encGuardedOracleState encBool :=
    ((ComputableInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt).comp hcfg_pt
  have hle_pt : ComputableInPolyTime
      (fun s : GuardedOracleState k_tm m_tm => decide (μB (subinst s) ≤ s.budget))
      encGuardedOracleState encBool :=
    ((hμB.comp hsubinst_pt).tidy.binary_le' hbud_pt.tidy).computableInPolyTime
  have hisActive_pt : ComputableInPolyTime isActive encGuardedOracleState encBool := by
    have hand2 := ComputableTidilyInPolyTime.bool_and.comp
      (((hisCan.comp hpend_pt).tidy).prod hle_pt.tidy)
    exact (ComputableTidilyInPolyTime.bool_and.comp
      (hisSome_pt.tidy.prod hand2)).computableInPolyTime
  have hlocal_pt : ComputableInPolyTime localStep encGuardedOracleState encGuardedOracleState :=
    computableInPolyTime_guardedMk hbud_pt
      ((machine.computableInPolyTime_answerStep_word (.const [false])).comp hcfg_pt)
  have hcombine_pt : ComputableInPolyTime combine
      (encPair encGuardedOracleState encBool) encGuardedOracleState := by
    have hp1 : ComputableInPolyTime (fun p : GuardedOracleState k_tm m_tm × Bool => p.1)
        (encPair encGuardedOracleState encBool) encGuardedOracleState := .fst _ _
    have hp2_word : ComputableInPolyTime (fun p : GuardedOracleState k_tm m_tm × Bool => [p.2])
        (encPair encGuardedOracleState encBool) encBits :=
      (ComputableInPolyTime.snd encGuardedOracleState encBool).of_enc_eq (encD := encBits)
        fun p => (encBool_apply p.2).symm
    exact computableInPolyTime_guardedMk (hbud_pt.comp hp1)
      (machine.receiveWord_pt.comp ((hcfg_pt.comp hp1).prod hp2_word))
  obtain ⟨d_step, hstep_inO⟩ := exists_computableInO_searchStep
    (done := fun _ : GuardedOracleState k_tm m_tm => false)
    (.const false) hisActive_pt hsubinst_pt hlocal_pt hcombine_pt hg
  have hstep : ComputableInO stepGuard encGuardedOracleState encGuardedOracleState
      (fun s => ((encGuardedOracleState s).length + 1) ^ d_step +
        if isActive s then
          t (subinst s) +
            ((encGuardedOracleState s).length + (encBool (g (subinst s))).length + 1) ^ d_step
        else 0)
      (fun s => ((encGuardedOracleState s).length + 1) ^ d_step +
        if isActive s then
          t (subinst s) +
            ((encGuardedOracleState s).length + (encBool (g (subinst s))).length + 1) ^ d_step
        else 0) := by
    refine (hstep_inO.mono_le (fun _ => ?_) (fun _ => ?_)).of_enc_eq fun s => ?_
    · simp only [true_and]
      exact le_rfl
    · simp only [true_and]
      exact le_rfl
    · rw [hstep_eq s]
  -- Initial state, iteration count, and final decision bit.
  let K (a : α) : ℕ := scale * μA a + offset
  let clk (a : α) : ℕ := c_clk * ((encA a).length + 1) ^ d_clk
  let initSt (a : α) : GuardedOracleState k_tm m_tm :=
    ⟨K a, Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a)⟩
  have hK_pt : ComputableInPolyTime K encA encNat := by
    have hsc : ComputableTidilyInPolyTime (fun _ : α => scale) encA encNat := .const scale
    have hof : ComputableTidilyInPolyTime (fun _ : α => offset) encA encNat := .const offset
    exact ((hsc.binary_mul' hμA.tidy).binary_add' hof).computableInPolyTime
  have hinit_cfg_pt : ComputableInPolyTime
      (fun a : α =>
        Turing.MultiTapeMachine.FiniteConfig.init (k := k_tm) (Oracle := Unit)
          machine.initial (encA a))
      encA encFiniteConfig :=
    (ComputableTidilyInPolyTime.finiteConfig_init (by fun_prop) _).computableInPolyTime
  have hinit_pt : ComputableInPolyTime initSt encA encGuardedOracleState :=
    computableInPolyTime_guardedMk hK_pt hinit_cfg_pt
  let pClk : Polynomial ℕ := Polynomial.C c_clk * (Polynomial.X + 1) ^ d_clk
  have hclk_pt : ComputableInPolyTime clk encA encNat :=
    ComputableTidilyInPolyTime.computableInPolyTime <|
      ((ComputableTidilyInPolyTime.unary_to_binary.comp
        ((ComputableTidilyInPolyTime.unary_eval pClk).comp
          (ComputableTidilyInPolyTime.encoding_length encA)))).of_enc_eq
        fun a => by simp [clk, pClk]
  have hout_raw : ComputableTidilyInPolyTime
      (fun cfg : Turing.MultiTapeMachine.FiniteConfig k_tm Bool (Fin m_tm) Unit =>
        cfg.tapes.output)
      encFiniteConfig encBits := by fun_prop
  have hout_pt : ComputableInPolyTime
      (fun s : GuardedOracleState k_tm m_tm => s.cfg.tapes.output.headD false)
      encGuardedOracleState encBool :=
    Decoder.bool.computableInPolyTime.comp (hout_raw.computableInPolyTime.comp hcfg_pt)
  -- Track `stepGuard^[i] (initSt a)` and its `FiniteConfig.SpaceBound`.
  have hiter_eq (a : α) (i : ℕ) :
      stepGuard^[i] (initSt a) =
        ⟨K a, (machine.answerStep (fun q => [guardAns (K a) q.2]))^[i]
          (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a))⟩ := by
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
  have hspace (a : α) {i : ℕ} (hi : i ≤ clk a) :
      Turing.MultiTapeMachine.FiniteConfig.SpaceBound (encA a).length i 1
        ((machine.answerStep (fun q => [guardAns (K a) q.2]))^[i]
          (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a))) := by
    induction i with
    | zero =>
      exact (Turing.MultiTapeMachine.FiniteConfig.spaceBound_init _ _ 0).mono
        le_rfl le_rfl (Nat.zero_le _)
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact machine.spaceBound_answerStep_word (fun w => [guardAns (K a) w])
        (ih (Nat.le_of_succ_le hi)) fun _ _ => le_rfl
  obtain ⟨cf, hcf⟩ :=
    length_encFiniteConfig_le (k := k_tm) (State := Fin m_tm) (Oracle := Unit)
  obtain ⟨cK, dK, hK_len⟩ := hK_pt.polyBounded_length.exists_le
  let stateBound (a : α) : ℕ :=
    2 * (cK * ((encA a).length + 1) ^ dK) + 1 +
      cf * ((encA a).length + clk a + 2)
  have hstate (a : α) (i : ℕ) (hi : i ≤ clk a) :
      (encGuardedOracleState (stepGuard^[i] (initSt a))).length ≤ stateBound a := by
    rw [hiter_eq]
    have hcfg_len : (encFiniteConfig
        ((machine.answerStep (fun q => [guardAns (K a) q.2]))^[i]
          (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a)))).length ≤
        cf * ((encA a).length + clk a + 2) :=
      (hcf _ _ _ _ (hspace a hi)).trans (Nat.mul_le_mul_left cf (by omega))
    have hk_len := hK_len a
    simp only [encGuardedOracleState_apply, length_encPair]
    dsimp only [stateBound]
    omega
  -- Bound `t (subinst st)` on every active step using `isCan` and `μB ≤ K a`.
  let leafMax (a : α) : ℕ :=
    ⌈(k_cost : ℝ) * (2 ^ (δ * (K a : ℝ)) * ((clk a : ℝ) + 1) ^ e) + k_cost⌉₊
  have htime (a : α) (i : ℕ) (hi : i ≤ clk a) :
      isActive (stepGuard^[i] (initSt a)) = true →
        t (subinst (stepGuard^[i] (initSt a))) ≤ leafMax a := by
    intro hact
    set st := stepGuard^[i] (initSt a)
    have hst_eq : st = ⟨K a, (machine.answerStep (fun q => [guardAns (K a) q.2]))^[i]
        (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a))⟩ := hiter_eq a i
    dsimp only [isActive] at hact
    rcases Bool.and_eq_true_iff.mp hact with ⟨_, hrest⟩
    rcases Bool.and_eq_true_iff.mp hrest with ⟨hcan_b, hle_b⟩
    have hcan : encB (subinst st) = machine.pendingRequest st.cfg := of_decide_eq_true hcan_b
    have hμ_le : μB (subinst st) ≤ K a := by
      have hle' : μB (subinst st) ≤ st.budget := of_decide_eq_true hle_b
      simpa only [hst_eq] using hle'
    have hreq_len : (encB (subinst st)).length ≤ clk a := by
      rw [hcan, hst_eq]
      exact (machine.length_pendingRequest_le (hspace a hi)).trans hi
    have hexp : (2 : ℝ) ^ (δ * μB (subinst st)) ≤ 2 ^ (δ * (K a : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hμ_le) hδ)
    have hpow : (((encB (subinst st)).length : ℝ) + 1) ^ e ≤ ((clk a : ℝ) + 1) ^ e := by gcongr
    refine Nat.cast_le.mp ((ht (subinst st)).trans ((?_ : _ ≤ _).trans (Nat.le_ceil _)))
    gcongr
  -- Assemble the `ComputableInO.iterate` decider and absorb polynomial overhead.
  obtain ⟨dn, _, hn⟩ := hclk_pt.exists_degree
  obtain ⟨di, _, hi_deg⟩ := hinit_pt.exists_degree
  obtain ⟨da, _, ha_deg⟩ := hout_pt.exists_degree
  let stepPoly (a : α) : ℕ := (stateBound a + 1) ^ d_step + (stateBound a + 2) ^ d_step
  have hround (a : α) (i : ℕ) (hi : i ≤ clk a) :
      ((encGuardedOracleState (stepGuard^[i] (initSt a))).length + 1) ^ d_step +
        (if isActive (stepGuard^[i] (initSt a)) then
          t (subinst (stepGuard^[i] (initSt a))) +
            ((encGuardedOracleState (stepGuard^[i] (initSt a))).length +
              (encBool (g (subinst (stepGuard^[i] (initSt a))))).length + 1) ^ d_step
        else 0) ≤ stepPoly a + leafMax a := by
    set st := stepGuard^[i] (initSt a)
    have hst : (encGuardedOracleState st).length ≤ stateBound a := hstate a i hi
    have hp1 := Nat.pow_le_pow_left (Nat.add_le_add_right hst 1) d_step
    split_ifs with hact
    · have ht_le : t (subinst st) ≤ leafMax a := htime a i hi hact
      have hp2 : ((encGuardedOracleState st).length +
          (encBool (g (subinst st))).length + 1) ^ d_step ≤
          (stateBound a + 2) ^ d_step := by
        simp only [encBool_apply, List.length_singleton]
        exact Nat.pow_le_pow_left (by omega) d_step
      dsimp only [stepPoly]
      omega
    · dsimp only [stepPoly]
      omega
  have hloop := ha_deg.inO.comp (ComputableInO.iterate hn.inO hi_deg.inO hstep hround hround
    fun a i hi => hstate a i hi)
  have hdecides_loop (a : α) :
      a ∈ A ↔ (stepGuard^[clk a] (initSt a)).cfg.tapes.output.headD false = true := by
    let ans_a : Unit × List Bool → List Bool := fun q => [guardAns (K a) q.2]
    have hcongr : OracleComp.interpret (m := Id) ans_a (R.program a) =
        OracleComp.interpret (m := Id) (languageOracle (encB '' B)) (R.program a) := by
      refine (OracleComp.interpret_id_congr (languageOracle (encB '' B)) ans_a
        (R.program a) ?_).1
      intro q hq
      dsimp only [ans_a, languageOracle]
      congr 1
      by_cases hmem : q.2 ∈ encB '' B
      · rcases hmem with ⟨b, hbB, hb_eq⟩
        have hdec_b : D.decode q.2 = b := by rw [← hb_eq, D.decode_enc]
        have hcan_q : isCan q.2 = true := by simp [isCan, hdec_b, hb_eq]
        have hμ_q : μB b ≤ K a := hparam a q hq b hb_eq
        have hle_q : decide (μB b ≤ K a) = true := decide_eq_true hμ_q
        simp only [guardAns, hcan_q, hdec_b, hle_q, Bool.and_self, ↓reduceIte]
        have hmem' : q.2 ∈ encB '' B := ⟨b, hbB, hb_eq⟩
        simp only [hmem', decide_true]
        exact (hgB b).mp hbB
      · simp only [hmem, decide_false]
        by_cases hcond : (isCan q.2 && decide (μB (D.decode q.2) ≤ K a)) = true
        · simp only [guardAns, hcond, ↓reduceIte]
          rcases Bool.and_eq_true_iff.mp hcond with ⟨hcan_q, _⟩
          have hcan_eq : encB (D.decode q.2) = q.2 := of_decide_eq_true hcan_q
          have hnotB : D.decode q.2 ∉ B := fun hb => hmem ⟨D.decode q.2, hb, hcan_eq⟩
          exact Bool.eq_false_iff.mpr fun hgb => hnotB ((hgB _).mpr hgb)
        · have hnc : (isCan q.2 && decide (μB (D.decode q.2) ≤ K a)) = false :=
            Bool.eq_false_iff.mpr hcond
          simp only [guardAns, hnc, Bool.false_eq_true, ↓reduceIte]
    have hm_out : ((machine.answerStep ans_a)^[clk a]
        (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a))).tapes.output =
        encBool (OracleComp.interpret (m := Id) (languageOracle (encB '' B)) (R.program a)) := by
      rw [← hcongr, ← hrun a ans_a, ← machine.interpret_run_pure_false]
    rw [hiter_eq a (clk a)]
    dsimp only
    change a ∈ A ↔ (((machine.answerStep ans_a)^[clk a]
      (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a))).tapes.output).headD
        false = true
    rw [hm_out, encBool_apply, List.headD_cons]
    exact R.decides a
  let clockLen (a : α) : ℕ := (encNat (clk a)).length
  have hclkLen (a : α) : clockLen a ≤ clk a + 1 := by
    dsimp only [clockLen]
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.le_succ _)
  have hpoly : PolyBounded (fun a => (encA a).length)
      (fun a => ((encA a).length + 1) ^ dn + ((encA a).length + 1) ^ di +
        (stateBound a + 1) ^ da +
        (clk a + 1) * (stepPoly a + stateBound a + (clk a + 1 + 1) ^ 2 +
          (clk a + 1) ^ e + 1)) := by
    dsimp only [stepPoly, stateBound, clk]
    growth_poly
  obtain ⟨Cp, E, hCp⟩ := hpoly.exists_le
  set C_big : ℝ := Cp + Cp * (k_cost * 2 ^ (δ * offset) + (k_cost + 1))
  refine DecidableInExpTime.of_computableInO hloop hdecides_loop ⌈C_big⌉₊ E fun a => ?_
  have hCp_a := hCp a
  have hfin_da : ((encGuardedOracleState (stepGuard^[clk a] (initSt a))).length + 1) ^ da ≤
      (stateBound a + 1) ^ da :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (hstate a (clk a) le_rfl) 1) da
  have hcl2 := Nat.pow_le_pow_left (Nat.add_le_add_right (hclkLen a) 1) 2
  set P : ℝ := (((encA a).length : ℝ) + 1) ^ E
  set Y : ℝ := (2 : ℝ) ^ ((scale * δ) * μA a)
  have hP1 : 1 ≤ P := one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hY1 : 1 ≤ Y := Real.one_le_rpow (by norm_num) (by positivity)
  have hleaf_bound : (leafMax a : ℝ) ≤
      (k_cost * 2 ^ (δ * offset)) * Y * (((clk a : ℝ) + 1) ^ e) + (k_cost + 1) := by
    have hceil : (leafMax a : ℝ) <
        (k_cost : ℝ) * (2 ^ (δ * (K a : ℝ)) * ((clk a : ℝ) + 1) ^ e) + k_cost + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hexp_split : (2 : ℝ) ^ (δ * (K a : ℝ)) = 2 ^ (δ * offset) * Y := by
      dsimp only [K, Y]
      push_cast
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    rw [hexp_split] at hceil
    linarith
  have hbase_le : (((encA a).length + 1) ^ dn + ((encA a).length + 1) ^ di +
      ((encGuardedOracleState (stepGuard^[clk a] (initSt a))).length + 1) ^ da +
      (clk a + 1) * (stepPoly a + stateBound a + (clockLen a + 1) ^ 2) : ℝ) ≤ Cp * P := by
    have hnat : ((encA a).length + 1) ^ dn + ((encA a).length + 1) ^ di +
        ((encGuardedOracleState (stepGuard^[clk a] (initSt a))).length + 1) ^ da +
        (clk a + 1) * (stepPoly a + stateBound a + (clockLen a + 1) ^ 2) ≤
        Cp * ((encA a).length + 1) ^ E := by
      have hmul_le : (clk a + 1) * (stepPoly a + stateBound a + (clockLen a + 1) ^ 2) ≤
          (clk a + 1) * (stepPoly a + stateBound a + (clk a + 1 + 1) ^ 2 +
            (clk a + 1) ^ e + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    dsimp only [P]
    exact_mod_cast hnat
  have hclk_pow_le : ((clk a : ℝ) + 1) * (((clk a : ℝ) + 1) ^ e) ≤ Cp * P := by
    have hnat : (clk a + 1) * ((clk a + 1) ^ e) ≤ Cp * ((encA a).length + 1) ^ E := by
      have hmul_le : (clk a + 1) * ((clk a + 1) ^ e) ≤
          (clk a + 1) * (stepPoly a + stateBound a + (clk a + 1 + 1) ^ 2 +
            (clk a + 1) ^ e + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    dsimp only [P]
    exact_mod_cast hnat
  have hclk_le : ((clk a : ℝ) + 1) ≤ Cp * P := by
    have hnat : clk a + 1 ≤ Cp * ((encA a).length + 1) ^ E := by
      have hmul_le : (clk a + 1) * 1 ≤
          (clk a + 1) * (stepPoly a + stateBound a + (clk a + 1 + 1) ^ 2 +
            (clk a + 1) ^ e + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    dsimp only [P]
    exact_mod_cast hnat
  have htot : (((((encA a).length + 1) ^ dn + ((encA a).length + 1) ^ di +
      (clk a + 1) * (stepPoly a + leafMax a + stateBound a + (clockLen a + 1) ^ 2) +
      ((encGuardedOracleState (stepGuard^[clk a] (initSt a))).length + 1) ^ da : ℕ) : ℝ)) ≤
      C_big * (Y * P) := by
    have hmul_leaf : ((clk a : ℝ) + 1) * (leafMax a : ℝ) ≤
        Cp * (k_cost * 2 ^ (δ * offset)) * (Y * P) + Cp * (k_cost + 1) * P := by
      have h1 : ((clk a : ℝ) + 1) * (leafMax a : ℝ) ≤
          ((clk a : ℝ) + 1) *
            ((k_cost * 2 ^ (δ * offset)) * Y * (((clk a : ℝ) + 1) ^ e) + (k_cost + 1)) :=
        mul_le_mul_of_nonneg_left hleaf_bound (by positivity)
      have h2 : (k_cost * 2 ^ (δ * offset)) * Y * (((clk a : ℝ) + 1) * (((clk a : ℝ) + 1) ^ e)) ≤
          (k_cost * 2 ^ (δ * offset)) * Y * (Cp * P) :=
        mul_le_mul_of_nonneg_left hclk_pow_le (by positivity)
      have h3 : (k_cost + 1 : ℝ) * ((clk a : ℝ) + 1) ≤ (k_cost + 1 : ℝ) * (Cp * P) :=
        mul_le_mul_of_nonneg_left hclk_le (by positivity)
      linarith
    have hYP : P ≤ Y * P := le_mul_of_one_le_left (by positivity) hY1
    have hbase_YP : (Cp : ℝ) * P ≤ Cp * (Y * P) := mul_le_mul_of_nonneg_left hYP (by positivity)
    have hk_YP : Cp * (k_cost + 1 : ℝ) * P ≤ Cp * (k_cost + 1 : ℝ) * (Y * P) :=
      mul_le_mul_of_nonneg_left hYP (by positivity)
    dsimp only [C_big, clockLen] at hbase_le hmul_leaf ⊢
    push_cast at hbase_le ⊢
    linarith
  exact htot.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C_big) (by positivity))

/-- **Parameterized subexponential-time transfer across `BoundedOracleReduction`.** -/
theorem decidableInSubexpTime {A : Set α} {B : Set β} {μA : α → ℕ} {μB : β → ℕ}
    (D : Decoder encB)
    (R : BoundedOracleReduction encA encB A B)
    {scale offset : ℕ}
    (hμA : ComputableInPolyTime μA encA encNat)
    (hμB : ComputableInPolyTime μB encB encNat)
    (hparam : ∀ a q,
      q ∈ OracleComp.queriesWith (languageOracle (encB '' B)) (R.program a) →
        ∀ b, encB b = q.2 → μB b ≤ scale * μA a + offset)
    (hB : DecidableInSubexpTime B encB μB) :
    DecidableInSubexpTime A encA μA := by
  intro ε hε
  set δ : ℝ := ε / (scale + 1)
  have hδ : 0 < δ := by positivity
  refine (R.decidableInExpTime D hμA hμB hparam hδ.le (hB δ hδ)).mono ?_
  dsimp only [δ]
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

end BoundedOracleReduction

end Cslib.Complexity
