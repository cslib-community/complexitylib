/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Sequential

/-!
# Bundling a family of reductions

A family of reductions `R θ` that share their rounds and their challenge samplers is one
reduction on the statements `⟨θ, x⟩`, which runs `R θ` on `x` and tags its output with `θ`
(`Cslib.Interactive.Reduction.bundle`). The parameter `θ` is part of the statement, so the
protocol may depend on the statement through it: for example, sumcheck on a polynomial chosen by an
earlier claim, as in the GKR protocol. Completeness and round-by-round soundness carry over with
the same errors (`Cslib.Interactive.Reduction.Complete.bundle`,
`Cslib.Interactive.Verifier.RbrSound.bundle`).

## Main definitions

* `Cslib.Interactive.Verifier.bundle`, `Cslib.Interactive.Reduction.bundle`.

## Main results

* `Cslib.Interactive.Verifier.outputOn_bundle`: the bundled verifier's output.
* `Cslib.Interactive.Reduction.Complete.bundle`, `Cslib.Interactive.Verifier.RbrSound.bundle`.
-/

@[expose] public section

namespace Cslib.Interactive

open scoped ENNReal
open Spec

variable {ιP ιV : Type} {oP : OracleSpec ιP} {oV : OracleSpec ιV} {s : Spec} {Θ : Type}
  {S₁ S₂ : Θ → Type} {W₁ W₂ : Type}

/-- The verifiers `V θ` as one verifier on the statements `⟨θ, x⟩`, with challenges drawn from
`smp`. -/
def Verifier.bundle (smp : PerChallenge ProbComp s) (V : (θ : Θ) → Verifier oV s (S₁ θ) (S₂ θ)) :
    Verifier oV s (Σ θ, S₁ θ) (Σ θ, S₂ θ) where
  samplers := smp
  decide x c := (fun o => o.map (Sigma.mk x.1)) <$> (V x.1).decide x.2 c

/-- The reductions `R θ` as one reduction on the statements `⟨θ, x⟩`, with challenges drawn from
`smp`. -/
def Reduction.bundle (smp : PerChallenge ProbComp s)
    (R : (θ : Θ) → Reduction oP oV s (S₁ θ) W₁ (S₂ θ) W₂) :
    Reduction oP oV s (Σ θ, S₁ θ) W₁ (Σ θ, S₂ θ) W₂ where
  prover x w := do
    let st ← (R x.1).prover x.2 w
    ProverStrategy.bindLeaf s st fun _ yw => pure (⟨x.1, yw.1⟩, yw.2)
  verifier := Verifier.bundle smp fun θ => (R θ).verifier

/-- The bundled verifier outputs what `V θ` outputs, tagged with `θ`. -/
theorem Verifier.outputOn_bundle (smp : PerChallenge ProbComp s)
    (V : (θ : Θ) → Verifier OracleSpec.empty s (S₁ θ) (S₂ θ)) (x : Σ θ, S₁ θ)
    (τ : Transcript s) :
    (Verifier.bundle smp V).outputOn x τ = ((V x.1).outputOn x.2 τ).map (Sigma.mk x.1) := by
  simp only [Verifier.outputOn, Verifier.bundle]
  exact OracleComp.interpret_map (m := Id) _ _ _

/-- **Round-by-round soundness of a bundle**, with the common per-round errors. -/
theorem Verifier.RbrSound.bundle {smp : PerChallenge ProbComp s}
    {V : (θ : Θ) → Verifier OracleSpec.empty s (S₁ θ) (S₂ θ)} (hsmp : ∀ θ, (V θ).samplers = smp)
    {L₁ : (θ : Θ) → Set (S₁ θ)} {L₂ : (θ : Θ) → Set (S₂ θ)}
    {ε : PerChallenge (fun _ => ℝ≥0∞) s} (h : ∀ θ, (V θ).RbrSound (L₁ θ) (L₂ θ) ε) :
    (Verifier.bundle smp V).RbrSound {x | x.2 ∈ L₁ x.1} {y | y.2 ∈ L₂ y.1} ε := by
  choose T hT hR using h
  refine ⟨fun x => T x.1 x.2, fun x hx => hT x.1 x.2 hx, fun x => ?_⟩
  have h := hR x.1 x.2
  rw [hsmp] at h
  refine RbrFrom.congr (fun _ => Iff.rfl) (fun τ => ?_) h
  rw [Verifier.outputOn_bundle]
  constructor
  · rintro ⟨y, hy, hout⟩
    exact ⟨⟨x.1, y⟩, hy, by rw [hout]; rfl⟩
  · rintro ⟨⟨θ, y⟩, hy, hout⟩
    cases hτ : (V x.1).outputOn x.2 τ with
    | none => rw [hτ] at hout; cases hout
    | some y' =>
      rw [hτ] at hout
      cases hout
      exact ⟨y', hy, rfl⟩

/-- The honest run of a bundle on `⟨θ, x⟩` is the honest run of `R θ` on `x`, with the output
statement tagged by `θ`. -/
theorem Reduction.plainLaw_run_bundle {smp : PerChallenge ProbComp s}
    {R : (θ : Θ) → Reduction OracleSpec.empty OracleSpec.empty s (S₁ θ) W₁ (S₂ θ) W₂}
    (hsmp : ∀ θ, (R θ).verifier.samplers = smp) (x : Σ θ, S₁ θ) (w : W₁) :
    plainLaw ((Reduction.bundle smp R).prover x w >>=
        runStrategy s (Reduction.bundle smp R).verifier.samplers) =
      (plainLaw ((R x.1).prover x.2 w >>= runStrategy s (R x.1).verifier.samplers)).map
        fun r => (r.1, Prod.map (Sigma.mk x.1) _root_.id r.2) := by
  rw [hsmp]
  simp only [Reduction.bundle, Verifier.bundle, bind_assoc, plainLaw_bind]
  rw [PMF.map_bind]
  congr 1 with st : 1
  rw [← plainLaw_bind]
  exact plainLaw_bindLeaf_pure_run _ _ _ _

/-- **Completeness of a bundle**, with the common error. -/
theorem Reduction.Complete.bundle {smp : PerChallenge ProbComp s}
    {R : (θ : Θ) → Reduction OracleSpec.empty OracleSpec.empty s (S₁ θ) W₁ (S₂ θ) W₂}
    (hsmp : ∀ θ, (R θ).verifier.samplers = smp) {rel₁ : (θ : Θ) → S₁ θ → W₁ → Prop}
    {rel₂ : (θ : Θ) → S₂ θ → W₂ → Prop} {ε : ℝ≥0∞}
    (h : ∀ θ, (R θ).Complete World.plain (rel₁ θ) (rel₂ θ) ε) :
    (Reduction.bundle smp R).Complete World.plain (fun x w => rel₁ x.1 x.2 w)
      (fun y w => rel₂ y.1 y.2 w) ε := by
  intro x w hxw
  have hl := h x.1 x.2 w hxw
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hl ⊢
  rw [Reduction.plainLaw_run_bundle hsmp, PMF.toOuterMeasure_map_apply]
  refine le_of_eq_of_le (congrArg _ ?_) hl
  ext r
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [show (Reduction.bundle smp R).verifier = Verifier.bundle smp fun θ => (R θ).verifier from rfl,
    Verifier.outputOn_bundle]
  refine not_congr (and_congr_left fun _ => ?_)
  cases (R x.1).verifier.outputOn x.2 r.1 <;> simp

end Cslib.Interactive
