/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.TM2.ConfigBound
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain

/-!
# Mathlib stack-machine computations within polynomial space

The simulation stores one encoded source configuration and a binary clock. Its space bound
depends on the sizes of the intermediate configurations, independently of the number of rounds.
All source stacks count towards space, including the initial input and final output.
The terminating-computation theorem derives an exponential clock from the polynomial stack
bound; it does not require a runtime certificate. The simulation gives polynomial space overhead,
rather than an assertion of a linear space bound.
`TM2.Reverse.Transfer` supplies the converse comparison and PSPACE decision equivalence under
the original binary encodings. Its target counts input and output storage, so it does not
preserve sublinear native work-space bounds.

## Main definitions

* `Turing.TM2Computable.StacksBounded`: a uniform bound on all reachable stack lengths.

## Main results

* `Turing.TM2.run_polySpace`: a polynomial-time binary clock and polynomially bounded source
  stacks give a polynomial-space simulation.
* `Turing.TM2Computable.computableInPolySpace_encList`: transfer termination and a polynomial
  source-stack bound to polynomial-space computation.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.1][Sipser2013]
-/

@[expose] public section

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin
  Turing.FinTM2.Γk₀Fin

namespace Turing.TM2

open MultiTapeTM

/-- Iterate a source machine using a binary clock. The source input may be computed from a
typed input; only its actual intermediate stacks need to obey the supplied space bound. -/
theorem run_polySpace (tm : FinTM2) [∀ k, Finite (tm.Γ k)]
    {α : Type} {encIn : α ↪ List Bool} {input : α → List (tm.Γ tm.k₀)}
    {clock space : α → ℕ}
    (hinput : ComputableInPolyTime input encIn (encList (encFinite (tm.Γ tm.k₀))))
    (hclock : ComputableInPolyTime clock encIn encNat)
    (hspace : PolyBounded (fun a => (encIn a).length) space)
    (hstacks : ∀ a i, i ≤ clock a → ∀ k,
      (((stepTotal tm.m)^[i] (initList tm (input a))).stk k).length ≤ space a) :
    ComputableInPolySpace
      (fun a => (stepTotal tm.m)^[clock a] (initList tm (input a))) encIn encCfg := by
  let : Inhabited (Cfg tm.Γ tm.Λ tm.σ) := ⟨initList tm []⟩
  obtain ⟨C, hC⟩ := length_encCfg_le (Γ := tm.Γ) (Λ := tm.Λ) (σ := tm.σ)
  apply ComputableInPolySpace.iterate hclock
    (.of_polyTime ((initList_polyTime tm).comp hinput))
    (.of_polyTime (stepTotal_polyTime tm.m))
    ((PolyBounded.const C).mul (hspace.add (.const 1)))
  intro a i hi
  exact hC _ _ (hstacks a i hi)

end Turing.TM2

namespace Turing.TM2Computable

open MultiTapeTM MultiTapeTM.ComputableInPolyTime

/-- Every stack of every configuration reached from the encoded input `a` has length at most
`space a`. Since `Turing.TM2.stepTotal` fixes halted configurations, this bounds the initial,
intermediate and final stacks of the computation. -/
def StacksBounded {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : TM2Computable ea eb f) (space : α → ℕ) : Prop :=
  ∀ a i stack,
    (((TM2.stepTotal h.tm.m)^[i]
      (initList h.tm (List.map h.inputAlphabet.symm (ea a)))).stk stack).length ≤ space a

/-- A terminating Mathlib computation with polynomially bounded source stacks is computable
within polynomial space. No source runtime bound or computable space bound is needed.
The bound includes the input and output stacks at initialization, during execution and at
halting. -/
theorem computableInPolySpace_encList {α β αΓ βΓ : Type} [Finite αΓ]
    {encA : αΓ ↪ List Bool} {encB : βΓ ↪ List Bool}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : TM2Computable ea eb f) [∀ k, Finite (h.tm.Γ k)]
    (ha : Function.Injective ea) (hb : Function.Injective eb)
    {space : α → ℕ} (hspace : PolyBounded (fun a => (ea a).length) space)
    (hstacks : h.StacksBounded space) :
    ComputableInPolySpace f
      ((⟨ea, ha⟩ : α ↪ List αΓ).trans (encList encA))
      ((⟨eb, hb⟩ : β ↪ List βΓ).trans (encList encB)) := by
  have hinput : ComputableInPolyTime ea
      ((⟨ea, ha⟩ : α ↪ List αΓ).trans (encList encA))
      (encList encA) := of_eq fun _ => rfl
  have hmap := (map (of_finite h.inputAlphabet.symm
    (encOut := encFinite (h.tm.Γ h.tm.k₀)))).comp hinput
  have hlength := (length_list encA).comp hinput
  obtain ⟨p, hp⟩ := hspace.exists_polynomial
  have hpBound := ((unary_eval p).comp hlength).polyBounded
  obtain ⟨C, hC⟩ := TM2.exists_exponential_clock h.tm
  let q : Polynomial ℕ := Polynomial.C C * (p + 1) + 1
  have hclock : ComputableInPolyTime
      (fun a => 2 ^ (C * (p.eval (ea a).length + 1) + 1))
      ((⟨ea, ha⟩ : α ↪ List αΓ).trans (encList encA)) encNat := by
    simpa only [Function.comp_def, q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_one] using binary_two_pow.comp ((unary_eval q).comp hlength)
  have hrun := TM2.run_polySpace h.tm hmap hclock hpBound
    (fun a i _ k => (hstacks a i k).trans (hp a))
  have hstacks' := (ComputableInPolySpace.of_polyTime TM2.cfg_stacks).comp hrun
  have hout := (ComputableInPolySpace.of_polyTime
    (dpi_apply (fun k => encList (encFinite (h.tm.Γ k))) h.tm.k₁)).comp hstacks'
  have hword := (ComputableInPolySpace.of_polyTime
    (map (of_finite h.outputAlphabet (encOut := encB)))).comp hout
  obtain ⟨S, hS, hword⟩ := hword.exists_inSpace
  refine ComputableInPolySpace.of_inSpace hS (ComputableInSpace.of_enc_eq hword ?_)
  intro a
  have heval := hC _ _ (p.eval (ea a).length) (h.outputsFun a)
    (fun i k => (hstacks a i k).trans (hp a))
  have houtput := congrArg (fun cfg : TM2.Cfg h.tm.Γ h.tm.Λ h.tm.σ =>
    List.map h.outputAlphabet (cfg.stk h.tm.k₁)) heval
  have hresult : List.map h.outputAlphabet
      (((TM2.stepTotal h.tm.m)^[2 ^ (C * (p.eval (ea a).length + 1) + 1)]
        (initList h.tm (List.map h.inputAlphabet.symm (ea a)))).stk h.tm.k₁) = eb (f a) := by
    simpa [haltList] using houtput
  exact congrArg (encList encB) hresult.symm

end Turing.TM2Computable
