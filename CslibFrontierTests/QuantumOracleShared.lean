/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Signature
public import CslibFrontier.Probability.Product.Split
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.List.GetD

/-! Original finite-oracle clients: a native family at different input lengths shares one table.
Independent redraws lose the resulting correlation. Complete-table sampling is ideal semantics,
not a PPT sampler. -/

public section

namespace CslibFrontierTests.QuantumOracleShared

open Cslib Cslib.Quantum Turing.MultiTapeTM
open scoped ENNReal

abbrev queryDescription (a b n ℓ : ℕ) : OracleCircuitDescription where
  width := 2 * n + 1 + ℓ + (a + b)
  queryWidth := a
  responseWidth := b
  quantumInputWidth := 0
  outputWidth := a + b
  instructions := [.query]

private theorem polyTime_queryDescription (a b : ℕ) : ComputableInPolyTime
    (fun s : OracleInputSize => queryDescription a b s.securityParameter s.classicalInputLength)
    encOracleInputSize encOracleCircuitDescription := by
  dsimp only [queryDescription]
  fun_prop

private theorem wellFormed_queryDescription (a b n ℓ : ℕ) :
    (queryDescription a b n ℓ).WellFormed ⟨n, ℓ⟩ := by
  refine ⟨by dsimp only [queryDescription]; omega, by dsimp only [queryDescription]; omega,
    by dsimp only [queryDescription]; omega, ?_⟩
  intro g hg
  simp only [List.mem_singleton] at hg
  subst g
  change a + b ≤ 2 * n + 1 + ℓ + (a + b)
  omega

/-- One native generator, with growing workspace and one query at every input length. -/
abbrev queryFamily (a b : ℕ) : UniformOracleCircuitFamily :=
  ⟨queryDescription a b, by exact polyTime_queryDescription a b,
    by exact wellFormed_queryDescription a b⟩

/-- The input-length cap is independent of the fixed oracle signature. -/
theorem querySignature (a b : ℕ) (L : ℕ → ℕ) :
    (queryFamily a b).HasOracleSignature (fun _ => a) (fun _ => b) L :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

example (a b : ℕ) (L : ℕ → ℕ) : PolynomiallyBounded (fun _ : ℕ => a + b) :=
  (querySignature a b L).polynomiallyBounded_widths

-- A different argument width is rejected, even when only the empty input is permitted.
example : ¬(queryFamily 1 1).HasOracleSignature (fun _ => 0) (fun _ => 1) (fun _ => 0) := by
  intro h
  exact Nat.one_ne_zero (h.queryWidth_eq 0 0 le_rfl)

private theorem querySignature_oracle (a b : ℕ) (L : ℕ → ℕ) (n ℓ : ℕ) (hℓ : ℓ ≤ L n)
    (H : (Fin a → Bool) → Fin b → Bool) : (querySignature a b L).oracle n ℓ hℓ H = H := by
  ext q j
  rw [UniformOracleCircuitFamily.HasOracleSignature.oracle_apply]
  rfl

-- Existing uniform transport applies directly; there is no second function sampler.
example (a b : ℕ) (L : ℕ → ℕ) (n ℓ : ℕ) (hℓ : ℓ ≤ L n) :
    (Probability.PMF.uniformOfFintype ((Fin a → Bool) → Fin b → Bool)).map
      ((querySignature a b L).oracle n ℓ hℓ) =
      Probability.PMF.uniformOfFintype
        ((Fin ((queryFamily a b).description n ℓ).queryWidth → Bool) →
          Fin ((queryFamily a b).description n ℓ).responseWidth → Bool) :=
  Probability.PMF.uniformOfFintype_map_equiv _

-- Existing finite-product restriction applies to a subset of addresses, without resampling.
example {S : Type} [Fintype S] [DecidableEq S] (a b : ℕ) (e : S ↪ (Fin a → Bool)) :
    (Probability.PMF.uniformOfFintype ((Fin a → Bool) → Fin b → Bool)).map
      (fun H s => H (e s)) = Probability.PMF.uniformOfFintype (S → Fin b → Bool) :=
  Probability.PMF.uniformOfFintype_map_comp_dep e.injective

private theorem initial_queryFamily (a b ℓ : ℕ) :
    (queryFamily a b).initialState 0 (List.replicate ℓ false) (ket (fun _ => false)) =
      ket (fun _ => false) := by
  rw [UniformOracleCircuitFamily.initialState_ket]
  congr 1
  ext j
  simp [inputState, encPair_apply, encUnary_apply, encBits_apply, List.getD_eq_getElem?_getD,
    ← List.replicate_succ]

private theorem queryFamily_toCircuit (a b n ℓ : ℕ)
    (H : (Fin a → Bool) → Fin b → Bool) :
    OracleCircuit.toCircuit (2 * n + 1 + ℓ + (a + b)) H [.query] =
      [xorQuery H (Fin.castLEEmb (by omega))] := by
  simp [OracleCircuit.toCircuit, OracleGateCode.toPlacedGate?,
    show a + b ≤ 2 * n + 1 + ℓ + (a + b) by omega]

/-- At security parameter zero, a zero word initializes the query and response to zero.
The returned prefix contains the all-zero query followed by its oracle answer. -/
theorem output_queryFamily (a b ℓ : ℕ) (H : (Fin a → Bool) → Fin b → Bool) :
    (queryFamily a b).output 0 (List.replicate ℓ false) H (ket (fun _ => false)) (norm_ket _) =
      PMF.pure (List.replicate a false ++ List.ofFn (H (fun _ => false))) := by
  let A : Fin (a + b) ↪ Fin ((queryFamily a b).description 0
      (List.replicate ℓ false).length).width := Fin.castLEEmb (by
    change a + b ≤ 2 * 0 + 1 + (List.replicate ℓ false).length + (a + b)
    omega)
  let z := (queryRegisters A).symm ((fun _ => false), H (fun _ => false), (fun _ => false))
  have hz : (queryRegisters A).symm ((fun _ => false), (fun _ => false), (fun _ => false)) =
      (fun _ => false) := by
    apply (queryRegisters A).injective
    simp
  have hrun : (queryFamily a b).run 0 (List.replicate ℓ false) H (ket (fun _ => false)) =
      ket z := by
    rw [UniformOracleCircuitFamily.run_apply, initial_queryFamily]
    change Circuit.eval (OracleCircuit.toCircuit
      (2 * 0 + 1 + (List.replicate ℓ false).length + (a + b)) H [.query]) _ = _
    rw [queryFamily_toCircuit, Circuit.eval_cons, Circuit.eval_nil]
    change (xorQuery H A).eval (ket (fun _ => false)) = ket z
    rw [← hz, xorQuery_eval_ket]
    change ket ((queryRegisters A).symm ((fun _ => false), 0 + H (fun _ => false),
      (fun _ => false))) = ket z
    rw [zero_add]
  rw [UniformOracleCircuitFamily.output_eq]
  trans measureOut (ket z) (norm_ket z) (fun y => List.ofFn fun i => y (A i))
  · congr 1
  rw [measureOut_ket]
  congr 1
  trans List.ofFn (Fin.append (fun _ : Fin a => false) (H (fun _ => false)))
  · apply congrArg List.ofFn
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change (queryRegisters A).symm _ (A (Fin.castAdd b j)) = _
      rw [queryRegisters_symm_query, Fin.append_left]
    · change (queryRegisters A).symm _ (A (Fin.natAdd a j)) = _
      rw [queryRegisters_symm_response, Fin.append_right]
  · simp [List.ofFn_fin_append]

private noncomputable def readOutput (ℓ : ℕ) (hℓ : ℓ ≤ 1)
    (H : (Fin 1 → Bool) → Fin 1 → Bool) : PMF (List Bool) :=
  (queryFamily 1 1).output 0 (List.replicate ℓ false)
    ((querySignature 1 1 (fun _ => 1)).oracle 0 ℓ hℓ H)
    (ket (fun _ => false)) (norm_ket _)

private theorem readOutput_eq (ℓ : ℕ) (hℓ : ℓ ≤ 1)
    (H : (Fin 1 → Bool) → Fin 1 → Bool) :
    readOutput ℓ hℓ H = PMF.pure [false, H (fun _ => false) 0] := by
  rw [readOutput, querySignature_oracle, output_queryFamily]
  simp

/-- The one sampled table is visibly outside both executions, at input lengths zero and one. -/
noncomputable def sharedExperiment : PMF Bool := do
  let H ← Probability.PMF.uniformOfFintype ((Fin 1 → Bool) → Fin 1 → Bool)
  let first ← readOutput 0 (by decide) H
  let second ← readOutput 1 le_rfl H
  pure (decide (first = second))

/-- Both runs make the same query, so their outputs always agree. -/
theorem sharedExperiment_eq : sharedExperiment = PMF.pure true := by
  simp [sharedExperiment, readOutput_eq]

/-- Redrawing between executions gives two independent tables instead of one shared table. -/
noncomputable def redrawnExperiment : PMF Bool := do
  let H₀ ← Probability.PMF.uniformOfFintype ((Fin 1 → Bool) → Fin 1 → Bool)
  let first ← readOutput 0 (by decide) H₀
  let H₁ ← Probability.PMF.uniformOfFintype ((Fin 1 → Bool) → Fin 1 → Bool)
  let second ← readOutput 1 le_rfl H₁
  pure (decide (first = second))

private theorem uniform_answer (q : Fin 1 → Bool) :
    (Probability.PMF.uniformOfFintype ((Fin 1 → Bool) → Fin 1 → Bool)).map
      (fun H => H q 0) = Probability.PMF.uniformOfFintype Bool := by
  rw [show (fun H : (Fin 1 → Bool) → Fin 1 → Bool => H q 0) =
    (fun r : Fin 1 → Bool => r 0) ∘ (fun H => H q) from rfl,
    ← PMF.map_comp, ← Probability.PMF.pi_uniformOfFintype,
    Probability.PMF.pi_map_eval, ← Probability.PMF.pi_uniformOfFintype,
    Probability.PMF.pi_map_eval]

/-- Independent redraws agree with probability one half, unlike the shared-table experiment. -/
theorem redrawnExperiment_eq : redrawnExperiment = Probability.PMF.uniformOfFintype Bool := by
  have h : ((Probability.PMF.uniformOfFintype ((Fin 1 → Bool) → Fin 1 → Bool)).map
      (fun H => H (fun _ => false) 0)).bind (fun b =>
        ((Probability.PMF.uniformOfFintype ((Fin 1 → Bool) → Fin 1 → Bool)).map
          (fun H => H (fun _ => false) 0)).map (fun c => decide (b = c))) =
      Probability.PMF.uniformOfFintype Bool := by
    rw [uniform_answer]
    ext b
    cases b <;> norm_num [PMF.bind_apply, PMF.map_apply, Probability.PMF.uniformOfFintype_apply,
      tsum_fintype, Fintype.sum_bool]
    all_goals simp only [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), one_mul]
  simpa only [redrawnExperiment, readOutput_eq, Probability.PMF.monad_bind_eq_bind, PMF.pure_bind,
    Probability.PMF.monad_pure_eq_pure, List.cons.injEq, true_and, and_true, PMF.bind_map,
    PMF.map_comp, Function.comp_def, PMF.map, PMF.bind_bind] using h

example : sharedExperiment true = 1 ∧ redrawnExperiment true = 1 / 2 := by
  rw [sharedExperiment_eq, redrawnExperiment_eq]
  norm_num [Probability.PMF.uniformOfFintype_apply]

-- Empty response registers have one possible answer and produce no output response bits.
example (a ℓ : ℕ) (H : (Fin a → Bool) → Fin 0 → Bool) :
    (queryFamily a 0).output 0 (List.replicate ℓ false) H
      (ket (fun _ => false)) (norm_ket _) = PMF.pure (List.replicate a false) := by
  simpa using output_queryFamily a 0 ℓ H

-- An empty argument register still has one address; its response can be nonempty.
example (H : (Fin 0 → Bool) → Fin 1 → Bool) :
    (queryFamily 0 1).output 0 [] H (ket (fun _ => false)) (norm_ket _) =
      PMF.pure [H (fun _ => false) 0] := by
  simpa using output_queryFamily 0 1 0 H

example :
    (queryFamily 0 0).output 0 [] (fun _ _ => false) (ket (fun _ => false)) (norm_ket _) =
      PMF.pure [] := by
  simpa using output_queryFamily 0 0 0 (fun _ _ => false)

end CslibFrontierTests.QuantumOracleShared
