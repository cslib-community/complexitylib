/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Oracle.Composition

/-!
# Oracle substitution for polynomial-time oracle classes

If an oracle language `O₁` belongs to `P^{O₂}`, a polynomial-time computation relative to `O₁`
becomes one relative to `O₂`: each query to `O₁` is answered by running the polynomial-time
`O₂`-oracle program deciding `O₁`. The simulation runs a finite oracle machine for the outer
computation and replaces each of its oracle steps by a call to the inner program; the outer clock
bounds both the number and the length of the queries, so the composite stays polynomial.

The special case where `O₁` many-one reduces to `O₂` is
`Cslib.Complexity.PolyTimeReducible.PWithOracle_subset` in
`CslibFrontier.Computability.Complexity.Classes.Oracle.Monotone`, which also covers non-Boolean
outputs.

## Main results

* `Cslib.Complexity.ComputableInPolyTimeWithOracle.of_mem_PWithOracle`: a Boolean function
  computable in polynomial time relative to `O₁ ∈ P^{O₂}` is computable in polynomial time
  relative to `O₂`.
* `Cslib.Complexity.PWithOracle_subset_of_mem_PWithOracle`,
  `Cslib.Complexity.NPWithOracle_subset_of_mem_PWithOracle`: if `O₁ ∈ P^{O₂}`, then
  `P^{O₁} ⊆ P^{O₂}` and `NP^{O₁} ⊆ NP^{O₂}`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {encA : α ↪ List Bool}

/-- One simulated instruction of a finite oracle machine `machine` when each query to its oracle is
answered by running the deterministic oracle program `prog`. -/
private def oracleAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (prog : List Bool → WordQueryComp Unit Bool)
    (cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    WordQueryComp Unit (Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :=
  if (machine.pendingQuery cfg).isSome then
    (fun b => machine.receiveBit (cfg, b)) <$> prog (machine.pendingRequest cfg)
  else
    pure (machine.localStep cfg)

private theorem interpret_oracleAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (prog : List Bool → WordQueryComp Unit Bool)
    (cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    OracleComp.interpret ProbOracleComp.query (oracleAnswerStep machine prog cfg) =
      if (machine.pendingQuery cfg).isSome then
        (fun b => machine.receiveBit (cfg, b)) <$>
          OracleComp.interpret ProbOracleComp.query (prog (machine.pendingRequest cfg))
      else
        pure (machine.localStep cfg) := by
  unfold oracleAnswerStep
  split <;> simp [OracleComp.interpret_map]

private theorem isOraclePPTOn_oracleAnswerStep {k : ℕ} {Control : Type} [Finite Control]
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    {prog : List Bool → WordQueryComp Unit Bool}
    (hprog : Probability.IsOraclePPTOn encBits encBool
      (fun w => OracleComp.interpret ProbOracleComp.query (prog w))) :
    Probability.IsOraclePPTOn encFiniteConfig encFiniteConfig
      (fun cfg =>
        OracleComp.interpret ProbOracleComp.query (oracleAnswerStep machine prog cfg)) := by
  simp only [interpret_oracleAnswerStep]
  exact Probability.IsOraclePPTOn.cond'
    ((ComputableInPolyTime.of_finite Option.isSome).comp machine.pendingQuery_pt)
    ((hprog.preprocess' machine.pendingRequest_pt).map_with'
      (f := fun cfg b => machine.receiveBit (cfg, b)) machine.receiveBit_pt)
    machine.localStep_pt.isOraclePPTOn

private theorem spaceBound_of_mem_support_oracleAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    (prog : List Bool → WordQueryComp Unit Bool)
    {inputSize steps : ℕ}
    {cfg next : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit}
    (hcfg : Turing.MultiTapeMachine.FiniteConfig.SpaceBound inputSize steps 1 cfg)
    (hnext : next ∈ OracleComp.support
      (OracleComp.interpret ProbOracleComp.query (oracleAnswerStep machine prog cfg))) :
    Turing.MultiTapeMachine.FiniteConfig.SpaceBound inputSize (steps + 1) 1 next := by
  rw [interpret_oracleAnswerStep] at hnext
  split_ifs at hnext with hq
  · obtain ⟨b, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    have hstep := machine.spaceBound_answerStep (fun _ => b) hcfg
    rw [machine.answerStep_bit (fun _ => b)] at hstep
    simpa [hq] using hstep
  · rw [OracleComp.eq_of_mem_supportWith_pure hnext]
    have hstep := machine.spaceBound_answerStep (fun _ => false) hcfg
    rw [machine.answerStep_bit (fun _ => false)] at hstep
    simpa [hq] using hstep

private theorem interpret_id_oracleAnswerStep {k : ℕ} {Control : Type}
    (machine : Turing.MultiTapePTM k Bool Control Unit)
    {prog : List Bool → WordQueryComp Unit Bool} {O : Set (List Bool)} {g : List Bool → Bool}
    (hg : ∀ w, OracleComp.interpret (m := Id) (languageOracle O) (prog w) = g w)
    (cfg : Turing.MultiTapeMachine.FiniteConfig k Bool Control Unit) :
    OracleComp.interpret (m := Id) (languageOracle O) (oracleAnswerStep machine prog cfg) =
      machine.answerStep (fun q => [g q.2]) cfg := by
  rw [machine.answerStep_bit]
  unfold oracleAnswerStep
  split_ifs with hq
  · rw [OracleComp.interpret_map, hg]
    rfl
  · rfl

open Classical in
/-- **Oracle substitution for polynomial-time Boolean computations**: if an oracle language `O₁`
belongs to `P^{O₂}` and `f : α → Bool` is computable in polynomial time relative to `O₁`, then
`f` is computable in polynomial time relative to `O₂`. -/
theorem ComputableInPolyTimeWithOracle.of_mem_PWithOracle {O₁ O₂ : Set (List Bool)} {f : α → Bool}
    (hO₁ : O₁ ∈ PWithOracle O₂ encBits)
    (hf : ComputableInPolyTimeWithOracle O₁ f encA encBool) :
    ComputableInPolyTimeWithOracle O₂ f encA encBool := by
  obtain ⟨g, ⟨prog, hprog, hg⟩, hgO₁⟩ := hO₁
  have hg' : g = fun w => decide (w ∈ O₁) := funext fun w =>
    Bool.eq_iff_iff.mpr ⟨fun h => decide_eq_true ((hgO₁ w).mpr h),
      fun h => (hgO₁ w).mp (of_decide_eq_true h)⟩
  subst hg'
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  obtain ⟨cf, hcf⟩ := length_encFiniteConfig_le (k := k) (State := Fin m) (Oracle := Unit)
  have hcount : ComputableInPolyTime (fun a => c * ((encA a).length + 1) ^ d) encA
      encUnary :=
    ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      (ComputableInPolyTime.encoding_length encA)).of_enc_eq fun a => by simp
  have hinit : ComputableInPolyTime
      (fun a => Turing.MultiTapeMachine.FiniteConfig.init (k := k) (Oracle := Unit)
        machine.initial (encA a))
      encA encFiniteConfig := by
    refine (((ComputableInPolyTime.of_eq fun _ => rfl :
        ComputableInPolyTime encA encA encBits).prod
      (ComputableInPolyTime.const (encOut :=
        encPair (encFinite (Option (Fin m)))
          (encPair encUnary (encPair (encPi (Index := Fin k) (encBiTape encBool)) encBits)))
        (some machine.initial, 1, fun _ => Cslib.Turing.BiTape.nil, []))).prod
      (ComputableInPolyTime.const
        (encOut := encPi (Index := Unit) (encPair encBits (encBiTape encBool)))
        fun _ : Unit => ([], Cslib.Turing.BiTape.nil))).of_enc_eq fun a => ?_
    simp [Turing.MultiTapeMachine.FiniteConfig.init, Turing.FiniteCfg.init]
  have hbound : PolyBounded (fun a => (encA a).length)
      (fun a => cf * ((encA a).length + c * ((encA a).length + 1) ^ d + 1 + 1)) := by growth_poly
  have hit := (Probability.IsOraclePPTOn.iterate_spec' hcount hinit
    (isOraclePPTOn_oracleAnswerStep machine hprog)
    (fun a i cfg => Turing.MultiTapeMachine.FiniteConfig.SpaceBound (encA a).length i 1 cfg)
    (fun _ => Turing.MultiTapeMachine.FiniteConfig.spaceBound_init _ _ _)
    (fun _ _ _ _ hinv _ hnext =>
      spaceBound_of_mem_support_oracleAnswerStep machine prog hinv hnext)
    hbound
    (fun _ _ _ hi hinv => (hcf _ _ _ _ hinv).trans (Nat.mul_le_mul_left cf (by omega)))).1
  refine ⟨fun a => (fun cfg => cfg.tapes.output.headD false) <$>
    OracleComp.iterate (c * ((encA a).length + 1) ^ d) (oracleAnswerStep machine prog)
      (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a)), ?_, fun a => ?_⟩
  · simp only [OracleComp.interpret_map, OracleComp.interpret_iterate]
    exact hit.map' (by fun_prop)
  · rw [OracleComp.interpret_map, OracleComp.interpret_id_iterate]
    simp only [interpret_id_oracleAnswerStep machine hg]
    change ((machine.answerStep (languageOracle O₁))^[c * ((encA a).length + 1) ^ d]
      (Turing.MultiTapeMachine.FiniteConfig.init machine.initial (encA a))).tapes.output.headD
        false = f a
    rw [← machine.interpret_run_pure_false, hrun a (languageOracle O₁), ← hprogram a]
    simp

/-- If `O₁ ∈ P^{O₂}`, then `P^{O₁} ⊆ P^{O₂}`. -/
theorem PWithOracle_subset_of_mem_PWithOracle {O₁ O₂ : Set (List Bool)}
    (hO₁ : O₁ ∈ PWithOracle O₂ encBits) (enc : α ↪ List Bool) :
    PWithOracle O₁ enc ⊆ PWithOracle O₂ enc :=
  fun _ ⟨f, hf, hL⟩ => ⟨f, hf.of_mem_PWithOracle hO₁, hL⟩

/-- If `O₁ ∈ P^{O₂}`, then `NP^{O₁} ⊆ NP^{O₂}`. -/
theorem NPWithOracle_subset_of_mem_PWithOracle {O₁ O₂ : Set (List Bool)}
    (hO₁ : O₁ ∈ PWithOracle O₂ encBits) (enc : α ↪ List Bool) :
    NPWithOracle O₁ enc ⊆ NPWithOracle O₂ enc :=
  fun _ ⟨p, V, hV, hL⟩ => ⟨p, V, hV.of_mem_PWithOracle hO₁, hL⟩

end Cslib.Complexity
