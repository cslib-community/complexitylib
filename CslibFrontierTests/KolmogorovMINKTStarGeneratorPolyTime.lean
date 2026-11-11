/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Kolmogorov.MINKTStar.Generator.PolyTime
import CslibFrontier.Computability.MCSP.PartialHardness.EvaluatorPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Tests for the polynomial time of the `MINKT*` generator -/

public section

namespace CslibFrontierTests.KolmogorovMINKTStarGeneratorPolyTime

open Cslib Cslib.Complexity Cslib.Kolmogorov Cslib.Kolmogorov.MINKTStar Cslib.PartialMCSP.FromCMMSA
  Turing.MultiTapeTM

/-- The printed table is polynomial-time in the encoded witness: the hypothesis of
`exists_timeBounded_of_computableInPolyTime`. -/
example (Δ k : ℕ) :
    ComputableInPolyTime (GenWitness.generate Δ k) GenWitness.enc encBits :=
  GenWitness.computableInPolyTime_generate Δ k ComputableInPolyTime.id'

/-- `fun_prop` composes the generator with a polynomial-time witness map. -/
example (Δ k : ℕ) {γ : Type} {enc : γ ↪ List Bool} {w : γ → GenWitness}
    (hw : ComputableInPolyTime w enc GenWitness.enc) :
    ComputableInPolyTime (fun a => GenWitness.generate Δ k (w a)) enc encBits := by
  fun_prop

/-- The step budget `pG (sizeBound Δ I λ + c)` of `exists_toMINKTStar_mem` is polynomial-time in
unary, from the instance and `λ` in unary: the shape a reduction to `MINKT*` needs for the budget
field. -/
example (Δ c : ℕ) (pG : Polynomial ℕ) {γ : Type} {enc : γ ↪ List Bool} {I : γ → CMMSAInstance}
    {lam : γ → ℕ} (hI : ComputableInPolyTime I enc CMMSAInstance.encoding)
    (hlam : ComputableInPolyTime lam enc encUnary) :
    ComputableInPolyTime (fun a => pG.eval (GenWitness.sizeBound Δ (I a) (lam a) + c)) enc
      encUnary :=
  (ComputableInPolyTime.unary_eval pG).comp (ComputableInPolyTime.unary_add'
    (GenWitness.computableInPolyTime_sizeBound Δ hI hlam) (ComputableInPolyTime.const c))

/-- With every variable function constantly `false`, the empty list has the table of every
variable, so the `MINKT*` instance with the budget and threshold of `exists_toMINKTStar_mem` is
polynomial-time in the CMMSA instance alone. -/
example (Δ k c : ℕ) (pG : Polynomial ℕ) :
    ComputableInPolyTime (fun I : CMMSAInstance =>
        toMINKTStar I Δ k 1 (fun _ _ => false) (pG.eval (GenWitness.sizeBound Δ I 1 + c))
          (GenWitness.sizeBound Δ I 1 + c))
      CMMSAInstance.encoding MINKTStar.enc := by
  have hs := ComputableInPolyTime.unary_add' (GenWitness.computableInPolyTime_sizeBound Δ
    ComputableInPolyTime.id' (ComputableInPolyTime.const 1)) (ComputableInPolyTime.const c)
  exact computableInPolyTime_toMINKTStar (T := fun _ => []) Δ k ComputableInPolyTime.id'
    (ComputableInPolyTime.const 1) (ComputableInPolyTime.const []) (fun _ v y => by simp [evalVar])
    ((ComputableInPolyTime.unary_eval pG).comp hs) hs

/-- **Yes completeness, as a reduction uses it.** For a Yes instance, `λ ≥ 1` and every choice of
the functions, the `MINKT*` instance is a yes-instance, and stays one for any larger budget and
threshold. -/
example (Δ k : ℕ) : ∃ (pG : Polynomial ℕ) (c : ℕ), ∀ {g σ : ℝ} {I : CMMSAInstance},
    I ∈ (GapCMMSA Δ g σ).yes → ∀ {lam}, 1 ≤ lam → ∀ (f : VarFunctions I lam) (t s : ℕ),
      pG.eval (GenWitness.sizeBound Δ I lam + c) ≤ t → GenWitness.sizeBound Δ I lam + c ≤ s →
        toMINKTStar I Δ k lam f t s ∈ MINKTStar := by
  obtain ⟨pG, c, -, h⟩ := exists_toMINKTStar_mem Δ k
  exact ⟨pG, c, fun hI lam hlam f t s ht hs =>
    mem_of_size_le (mem_of_time_le (h _ _ _ hI lam hlam f) ht) hs⟩

/-- The pattern of `toMINKTStar` has one entry per input of the CMMSA table. -/
example (I : CMMSAInstance) (Δ k lam : ℕ) (f : VarFunctions I lam) (t s : ℕ) :
    (toMINKTStar I Δ k lam f t s).pattern.length = 2 ^ inputLength I Δ k lam := by
  simp [toMINKTStar]

end CslibFrontierTests.KolmogorovMINKTStarGeneratorPolyTime
