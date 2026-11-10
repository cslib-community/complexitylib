/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.FunctionalCNF
public import CslibFrontier.Computability.Circuit.Boolean.PopulationCount.ThresholdPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Actual functional cardinality intervals with binary bounds

Use the existing linear-size population-count/threshold circuits to test an input lower and upper
bound simultaneously. Each original assignment has exactly one full gate trace, accepted precisely
inside the interval. Upper/lower/equality tests are specializations. Binary cutoffs are capped
before unary generation; huge targets do not trigger a loop of target length.
This is [ChenJiangZhu2027], Lemma 3.3 and Appendix A.1, PDF pp. 11, 28.

## Main definitions

* `generate`: actual capped binary-threshold circuit code.
* `formula`: full functional 3-CNF for both inclusive input bounds.

## Main results

* `formula_polytime`: binary construction costs with input bounds.
* `functional`: exactly the original-weight interval with a unique full gate trace.
* `formula_bounds`: linear auxiliary/clause budgets and width three.
-/

public section

namespace Cslib.Logic.PL.CardinalityInterval

open Turing.MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean

/-- Original unary declaration and binary lower/upper bounds on the selected count. -/
abbrev Input := ℕ × ℕ × ℕ
/-- Original declared bit count. -/
@[expose] def declared : Input → ℕ | (n, _, _) => n
/-- Inclusive input lower bound. -/
@[expose] def lower : Input → ℕ | (_, lo, _) => lo
/-- Inclusive input upper bound. -/
@[expose] def upper : Input → ℕ | (_, _, hi) => hi
/-- Framed unary declaration and binary bounds. -/
@[expose] def encInput : Input ↪ List Bool := encPair encUnary (encPair encNat encNat)

/-- Actual safe generator: the cutoff is capped at one more than the unary declaration. -/
@[expose] def thresholdCode (n q : ℕ) : FunctionalCNF.Code :=
  (linearThresholdCircuit n (min q (n + 1))).code

private theorem threshold_cap (n q : ℕ) :
    linearThresholdCircuit n (min q (n + 1)) = linearThresholdCircuit n q := by
  by_cases hq : q ≤ n
  · rw [Nat.min_eq_left (by omega)]
  · have hc : min q (n + 1) = n + 1 := Nat.min_eq_right (by omega)
    simp only [hc, linearThresholdCircuit, hq, not_le.mpr (Nat.lt_succ_self n), ↓reduceDIte]

/-- Capping changes no threshold semantics, including out-of-range cutoffs. -/
theorem thresholdCode_eq (n q : ℕ) : thresholdCode n q = (linearThresholdCircuit n q).code := by
  rw [thresholdCode, threshold_cap]

private theorem thresholdCode_polytime : ComputableInPolyTime
    (fun p : ℕ × ℕ => thresholdCode p.1 p.2) (encPair encUnary encNat) encCode := by
  have hn := ComputableInPolyTime.fst encUnary encNat
  have hq := ComputableInPolyTime.snd encUnary encNat
  have hbound : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + 1)
      (encPair encUnary encNat) encUnary := by fun_prop
  have hcap : ComputableInPolyTime (fun p : ℕ × ℕ => min p.2 (p.1 + 1))
      (encPair encUnary encNat) encUnary :=
    (ComputableInPolyTime.binary_min_unary' hbound hq).of_enc_eq fun _ => by rw [Nat.min_comm]
  have h := computableInPolyTime_linearThresholdCircuit.comp (hn.prod hcap)
  exact h.of_enc_eq fun _ => rfl

/-- The two standard circuits whose full traces enforce the inclusive interval. -/
@[expose] def circuit (n lo hi : ℕ) : Circuit signature n 2 :=
  (linearThresholdCircuit n lo).append (linearThresholdCircuit n (hi + 1))

/-- Actual binary gate-and-output construction, sharing the original input wires. -/
@[expose] def generate (x : Input) : FunctionalCNF.Code :=
  appendCode (declared x) (thresholdCode (declared x) (lower x))
    (thresholdCode (declared x) (upper x + 1))

/-- The actual code is the reviewed linear circuit, with no circuit or size supplied. -/
theorem generate_eq (n lo hi : ℕ) : generate (n, lo, hi) = (circuit n lo hi).code := by
  simp only [generate, declared, lower, upper, thresholdCode_eq, appendCode_code, circuit]

/-- Every binary comparison, cap, generation and reference relocation is polynomial time. -/
@[fun_prop] theorem generate_polytime : ComputableInPolyTime generate encInput encCode := by
  have hn : ComputableInPolyTime declared encInput encUnary := by unfold declared encInput; fun_prop
  have hlo : ComputableInPolyTime lower encInput encNat := by unfold lower encInput; fun_prop
  have hhi : ComputableInPolyTime (fun x => upper x + 1) encInput encNat := by
    unfold upper encInput; fun_prop
  have hl := thresholdCode_polytime.comp (hn.prod hlo)
  have hh := thresholdCode_polytime.comp (hn.prod hhi)
  have h := computableInPolyTime_appendCode (ComputableInPolyTime.unary_to_binary.comp hn) hl hh
  exact h.of_enc_eq fun _ => rfl

/-- The required output vector: lower threshold true, strict upper threshold false. -/
@[expose] def wanted : Fin 2 → Bool := fun i => decide (i.val = 0)
/-- Actual cardinality-test payload in the shared full-gate CNF writer. -/
@[expose] def payload (x : Input) : FunctionalCNF.Input :=
  (declared x, generate x, [true, false])
/-- Full ordinary 3-CNF cardinality test, with every gate constrained functionally. -/
@[expose] def formula (x : Input) : CNF ℕ := FunctionalCNF.write (payload x)

/-- The whole original-bound-to-CNF computation has binary polynomial resources. -/
@[fun_prop] theorem formula_polytime : ComputableInPolyTime formula encInput
    (encList (encList (encPair encNat encBool))) := by
  have hn : ComputableInPolyTime declared encInput encUnary := by unfold declared encInput; fun_prop
  exact FunctionalCNF.write_polytime.comp (hn.prod (generate_polytime.prod (.const [true, false])))

/-- Actual cardinality payload is exactly the typed circuit with prescribed outputs. -/
theorem payload_eq (n lo hi : ℕ) : payload (n, lo, hi) =
    FunctionalCNF.ofCircuit (circuit n lo hi) wanted := by
  rw [payload, generate_eq]
  rfl

/-- Original count comparisons are the precise semantics of the computed output bits. -/
theorem circuit_accepts (n lo hi : ℕ) (x : Fin n → Bool) :
    (circuit n lo hi).eval interpretation x = wanted ↔
      lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi := by
  rw [funext_iff]
  simp only [circuit, Circuit.eval_append]
  have hh : (∀ i : Fin 2, Fin.append
      ((linearThresholdCircuit n lo).eval interpretation x)
      ((linearThresholdCircuit n (hi + 1)).eval interpretation x) i = wanted i) ↔
      (linearThresholdCircuit n lo).eval interpretation x 0 = true ∧
        (linearThresholdCircuit n (hi + 1)).eval interpretation x 0 = false := by
    rw [Fin.forall_fin_two]
    rfl
  rw [hh, eval_linearThresholdCircuit, eval_linearThresholdCircuit]
  simp [single, Cslib.threshold]

/-- The circuit introduces linearly many gate variables, uniformly over binary bounds. -/
theorem size_circuit (n lo hi : ℕ) : (circuit n lo hi).size ≤ 952 * (n + 1) := by
  have hl := size_linearThresholdCircuit_le n lo
  have hh := size_linearThresholdCircuit_le n (hi + 1)
  simp only [circuit, Circuit.size_append]
  omega

/-- Every accepted original assignment has exactly the full existing circuit trace. -/
theorem functional (n lo hi : ℕ) (x : Fin n → Bool) (σ : ℕ → Bool)
    (hin : ∀ i : Fin n, σ i.val = x i) :
    (formula (n, lo, hi)).eval σ = true ↔
      (∀ j : Fin (n + (circuit n lo hi).size),
        σ j.val = FunctionalCNF.wireValues (circuit n lo hi) x j) ∧
      lo ≤ Cslib.BitString.weight x ∧ Cslib.BitString.weight x ≤ hi := by
  rw [formula, payload_eq, FunctionalCNF.eval_write_iff _ _ _ _ hin, circuit_accepts]

/-- Actual cardinality clauses have width three and a linear clause/auxiliary budget. -/
theorem formula_bounds (n lo hi : ℕ) :
    (formula (n, lo, hi)).length ≤ 2 + 2856 * (n + 1) ∧
      ∀ c ∈ formula (n, lo, hi), c.length = 3 ∧
        ∀ l ∈ c, l.1 < n + (circuit n lo hi).size := by
  have hl := FunctionalCNF.write_length (circuit n lo hi) wanted
  have hs := size_circuit n lo hi
  rw [formula, payload_eq]
  refine ⟨by omega, fun c hc => FunctionalCNF.write_bounds _ _ c hc⟩

end Cslib.Logic.PL.CardinalityInterval
