/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.CertificateCircuit
public import Complexity.Computability.Circuit.Fusion.Conondeterministic
public import Complexity.Computability.Circuit.Boolean.Conondeterministic

/-!
# Universal verifiers from semi-ultrafilter covers

A cover of length `t` yields a native universal verifier with `3t` auxiliary bits and exactly
`5t` binary AND gates. The verifier rejects precisely valid, pair-preserving certificates.
True primary inputs have no such certificate by the cover property; false inputs supply their
point-membership certificate. The construction includes empty covers and constant functions.

## Main results

* `Cslib.Circuits.Fusion.PairCover.exists_forallGuess`: the universal verifier with exact cost.
* `Cslib.Circuits.Fusion.conondeterministicAndComplexity_bounds`: minimum universal-verifier
  AND complexity lies between semi-ultrafilter cover complexity and five times that measure.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], Theorem 45, credited there to Karchmer. The explicit factor five
  follows from the grouped certificate construction formalized here.
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

open Cslib Boolean PairCertificate

private theorem exists_primary_literal_formula {n a : ℕ} (l : Fin (n + n)) :
    ∃ F : Formula Monotone.signature ((n + a) + (n + a)),
      (∀ z : BitString (n + a), F.eval Monotone.interpretation (AltFormula.literals z) = true ↔
        AltFormula.literals (fun i => z (Fin.castAdd a i)) l = true) ∧
      F.cost Monotone.andCost = 0 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · exact ⟨.input (Fin.castAdd _ (Fin.castAdd a i)),
      fun _ => by simp only [Formula.eval_input, AltFormula.literals, Fin.append_left], rfl⟩
  · exact ⟨.input (Fin.natAdd _ (Fin.castAdd a i)),
      fun _ => by simp only [Formula.eval_input, AltFormula.literals, Fin.append_right], rfl⟩

private theorem exists_auxiliary_literal_formula {n a : ℕ} (i : Fin a) (b : Bool) :
    ∃ F : Formula Monotone.signature ((n + a) + (n + a)),
      (∀ z : BitString (n + a), F.eval Monotone.interpretation (AltFormula.literals z) = true ↔
        z (Fin.natAdd n i) = b) ∧ F.cost Monotone.andCost = 0 := by
  cases b
  · exact ⟨.input (Fin.natAdd _ (Fin.natAdd n i)),
      fun _ => by simp only [Formula.eval_input, AltFormula.literals, Fin.append_right,
        Bool.not_eq_true_eq_eq_false], rfl⟩
  · exact ⟨.input (Fin.castAdd _ (Fin.natAdd n i)),
      fun _ => by simp only [Formula.eval_input, AltFormula.literals, Fin.append_left], rfl⟩

/-- A cover of length `t` yields a verifier with `3t` auxiliary bits and exactly `5t` AND gates.
Constants, OR gates and supplied positive/negative literals are free. No nonempty-target,
nonempty-complement or positive-length assumption is imposed. -/
theorem PairCover.exists_forallGuess {n : ℕ} (f : BooleanFunction n)
    (cover : PairCover {x | f x = true} (fun i => {x | AltFormula.literals x i = true})
      Semifilter.IsUltra) :
    ∃ g : BooleanFunction (n + size cover.pairs),
      ∃ c : Circuit Monotone.signature
        ((n + size cover.pairs) + (n + size cover.pairs)) 1,
        forallGuess g = f ∧ c.ComputesFrom Monotone.interpretation (single g)
          AltFormula.literals ∧ c.program.cost Monotone.andCost = 5 * cover.pairs.length := by
  classical
  let sources : Fin (n + n) → Set ↥({x | f x = true}ᶜ) :=
    fun i => Subtype.val ⁻¹' {x : BitString n | AltFormula.literals x i = true}
  obtain ⟨F, hF, cF⟩ := PairCertificate.exists_formula cover.pairs sources AltFormula.literals
    (fun z : BitString (n + size cover.pairs) =>
      AltFormula.literals (fun i => z (Fin.castAdd _ i)))
    (fun z i => z (Fin.natAdd n i)) exists_primary_literal_formula
    exists_auxiliary_literal_formula
  let g : BooleanFunction (n + size cover.pairs) :=
    fun z => F.eval Monotone.interpretation (AltFormula.literals z)
  have hspec (x : BitString n) (y : BitString (size cover.pairs)) :
      g (Fin.append x y) = true ↔
        Invalid cover.pairs sources (AltFormula.literals x) y ∨ BreaksPair cover.pairs y := by
    simpa only [g, Fin.append_left, Fin.append_right] using hF (Fin.append x y)
  refine ⟨g, F.toCircuit, ?_, ?_, by simpa only [Formula.cost_toCircuit] using cF⟩
  · funext x
    apply Bool.eq_iff_iff.mpr
    simp only [forallGuess, decide_eq_true_eq]
    constructor
    · intro h
      by_contra hx
      let u : ↥({x | f x = true}ᶜ) := ⟨x, hx⟩
      have hvalid := not_invalid_pointLabels cover.pairs sources (AltFormula.literals x) u
        (fun _ h => h)
      have hpreserve := not_breaksPair_pointLabels cover.pairs u
      exact (hspec x (pointLabels cover.pairs u)).mp (h _) |>.elim hvalid hpreserve
    · intro hx y
      apply (hspec x y).mpr
      simpa only [Set.mem_ofPred_eq, Bool.decide_eq_true] using
        cover.invalid_or_breaksPair ⟨x, hx⟩ y
  · intro z
    funext i
    exact Formula.eval_toCircuit _ _ _ _

/-- The semi-ultrafilter bound applies after minimizing over all auxiliary counts and verifiers. -/
private theorem pairCoverComplexity_le_econondeterministicAndComplexity {n : ℕ}
    (f : BooleanFunction n) :
    pairCoverComplexity {x | f x = true} (fun i => {x | AltFormula.literals x i = true})
      Semifilter.IsUltra ≤ econondeterministicAndComplexity f := by
  apply le_econondeterministicAndComplexity_iff.mpr
  intro a g hg c hc
  subst f
  exact pairCoverComplexity_forallGuess_le_cost g c hc

/-- A semi-ultrafilter cover gives a universal verifier at most five times as costly. -/
private theorem econondeterministicAndComplexity_le_pairCoverComplexity {n : ℕ}
    (f : BooleanFunction n) :
    econondeterministicAndComplexity f ≤
      5 * pairCoverComplexity {x | f x = true}
        (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra := by
  rw [pairCoverComplexity, ENat.mul_iInf_of_ne (by decide : (5 : ℕ∞) ≠ 0)]
  apply le_iInf
  intro cover
  obtain ⟨g, c, hg, hc, hcost⟩ := cover.exists_forallGuess f
  simpa only [hcost, Nat.cast_mul, Nat.cast_ofNat] using
    econondeterministicAndComplexity_le_cost g hg c hc

/-- **Linear semi-ultrafilter characterization of conondeterministic AND complexity**,
with explicit factors one and five and unrestricted finite auxiliary input counts. -/
theorem conondeterministicAndComplexity_bounds {n : ℕ} (f : BooleanFunction n) :
    let ρ := pairCoverComplexity {x | f x = true}
      (fun i => {x | AltFormula.literals x i = true}) Semifilter.IsUltra
    ρ ≤ econondeterministicAndComplexity f ∧ econondeterministicAndComplexity f ≤ 5 * ρ :=
  ⟨pairCoverComplexity_le_econondeterministicAndComplexity f,
    econondeterministicAndComplexity_le_pairCoverComplexity f⟩

end Cslib.Circuits.Fusion
