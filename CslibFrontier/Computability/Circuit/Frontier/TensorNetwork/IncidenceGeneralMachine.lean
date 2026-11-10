/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceGeneralResources
import CslibFrontier.Computability.GenericRAM.Native.MachineBounds
import CslibFrontier.Computability.Complexity.Problems.SAT.SizeBound

/-!
# A finite binary machine for the sharp unrestricted-density CNF counter

Expose the machine already realized by the actual sparsification/parity/contraction counter,
with all multiplicative and additive constants absorbed. Fixed width is the only problem
parameter: no count, decomposition, clock or realizing machine is supplied by the caller.
The declaration is unary and literal indices are binary. Unused declared variables are retained.

The shared `encCounter` encoding is defined in `IncidenceGeneralResources`.

## Main results

* `exists_countGeneralParity_machine`: total native realization and polynomial output storage.
* `exists_countGeneralParity_source_machine`: the source polynomial in variables plus clauses,
  real single-loglog time, polynomial bit workspace and exact original declared counts.

## References

[ChenJiangZhu2027], Section 3 and Lemma 3.2 (PDF pp.10–11), using
[OpenAI2026ETH], Appendix D.3 (PDF p.57).
-/

public section
namespace Cslib.Circuits.Frontier.IncidenceNetwork
open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Complexity Turing.MultiTapeTM

/-- One finite binary machine executes the actual general-density counter on every declared
input. Invalid width/indices return zero; no density bound or resource premise is required. -/
theorem exists_countGeneralParity_machine (K : ℕ) (hK : 2 ≤ K) :
    ∃ (β N₀ Ncut C e A tapes : ℕ) (State : Type) (_ : Finite State)
      (tm : Turing.MultiTapeTM tapes Bool State),
      (∀ x, tm.ComputesInTimeAndSpace (encCounter x)
        (encNat (countGeneralParity K β N₀ Ncut x))
        (C * ((encCounter x).length + 1) ^ e * 2 ^ (A * Nat.logLogSqrtLogScale x.1))
        (C * ((encCounter x).length + 1) ^ e)) ∧
      (∀ x, (encNat (countGeneralParity K β N₀ Ncut x)).length ≤
        C * ((encCounter x).length + 1) ^ e) ∧
      (∀ x, countGeneralParity K β N₀ Ncut x =
        if validDeclaredInput K x.1 x.2 then x.2.modelCountOn (Finset.range x.1) else 0) := by
  obtain ⟨β, N₀, Ncut, cs, D, hresource, hcorrect⟩ :=
    exists_countGeneralParity_sharp_certificate K hK
  obtain ⟨C, tapes, State, hfinite, tm, ht, hl⟩ := cs.exists_sharp_machine D D D
    (fun x => Nat.logLogSqrtLogScale x.1) (fun x => (hresource x).2)
    (fun x => (hresource x).1)
  exact ⟨β, N₀, Ncut, C, D, D, tapes, State, hfinite, tm, ht, hl, hcorrect⟩

/-- Lemma 3.2 in transition-level semantics: for fixed K≥2 a single machine counts every
K-CNF on every declared N≥20, regardless of clause density, with the source clock and bit space.
Encoded output is bounded independently; all constants precede N and the formula. -/
theorem exists_countGeneralParity_source_machine (K : ℕ) (hK : 2 ≤ K) :
    ∃ (β N₀ Ncut C e A tapes : ℕ) (State : Type) (_ : Finite State)
      (tm : Turing.MultiTapeTM tapes Bool State),
      (∀ x, countGeneralParity K β N₀ Ncut x =
        if validDeclaredInput K x.1 x.2 then x.2.modelCountOn (Finset.range x.1) else 0) ∧
      ∀ N, 20 ≤ N → ∀ φ : CNF ℕ, validDeclaredInput K N φ = true →
        ∃ t, tm.ComputesInTimeAndSpace (encCounter (N, φ))
          (encNat (countGeneralParity K β N₀ Ncut (N, φ))) t
          (C * (N + φ.length + 1) ^ e) ∧
          (t : ℝ) ≤ (C : ℝ) * (N + φ.length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale N) ∧
          (encNat (countGeneralParity K β N₀ Ncut (N, φ))).length ≤
            C * (N + φ.length + 1) ^ e := by
  obtain ⟨β, N₀, Ncut, B, f, A, tapes, State, hfinite, tm, ht, hl, hc⟩ :=
    exists_countGeneralParity_machine K hK
  let C := B * (20 * K + 4) ^ f
  let e := 2 * f
  refine ⟨β, N₀, Ncut, C, e, 6 * A, tapes, State, hfinite, tm, hc, ?_⟩
  intro N hN φ hv
  have hpoly : B * ((encCounter (N, φ)).length + 1) ^ f ≤
      C * (N + φ.length + 1) ^ e := by
    calc _ ≤ B * ((20 * K + 4) * (N + φ.length + 1) ^ 2) ^ f :=
          Nat.mul_le_mul_left B (Nat.pow_le_pow_left (SAT.length_declaredInput_le hv) f)
      _ = _ := by dsimp only [C, e]; rw [mul_pow, ← pow_mul]; ring
  refine ⟨_, ⟨(ht (N, φ)).1, (ht (N, φ)).2.1,
    ((ht (N, φ)).2.2).mono hpoly⟩, ?_, (hl (N, φ)).trans hpoly⟩
  have hclock : ((B * ((encCounter (N, φ)).length + 1) ^ f *
      2 ^ (A * Nat.logLogSqrtLogScale N) : ℕ) : ℝ) ≤ (C : ℝ) *
      (N + φ.length + 1 : ℕ) ^ e * (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale N) := by
    exact_mod_cast Nat.mul_le_mul_right (2 ^ (A * Nat.logLogSqrtLogScale N)) hpoly
  exact hclock.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A (by omega)) (by positivity))

end Cslib.Circuits.Frontier.IncidenceNetwork
