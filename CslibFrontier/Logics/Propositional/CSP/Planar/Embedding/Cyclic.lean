/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Probe
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.ScopeReindex
import CslibFrontier.Foundations.Data.List.OfFnPositions

/-!
# Cyclic transport of actual ordered boundaries

The structural probe is reindexed by the opposite cyclic shift, preserving the original
clockwise argument rotations. The source and target actual bodies are identical. Numerical
genus and complete target certificate acceptance follow internally from occurrence transport
and probe removal. The distinct-boundary guard is explicit; closed components and nullaries
remain present, including at arity zero. These are original finite structural constructions.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V]

private noncomputable def reindexOfFn {F : CSP Rel V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hn : (List.ofFn v).Nodup)
    (p q : Equiv.Perm (Fin n))
    (hq : ∀ j, q (finRotate n j) = finRotate n (q j))
    (hrev : ∀ j, (q j).rev = p j.rev) : Witness F (List.ofFn (v ∘ p)) := by
  let B := F.map (fun c => (some c.1, c.2))
  let scope : Fin n → V := fun j => v j.rev
  have hs : verifyRotationCertificate (B ++ [(none, List.ofFn scope)]) w.certificate = true := by
    simpa only [B, scope, probeBody, List.reverse_ofFn] using w.probe_accepted
  have he := (verifyRotationCertificate_eq_true_iff _ _).mp hs
  have hrot := he.choose
  let certificate := reindexLastScopeCertificate B none scope q w.certificate hrot
  have ht := verifyRotationCertificate_reindexLastScopeCertificate B none scope q hq
    w.certificate hrot hs
  have hscope : scope ∘ q = fun j => v (p j.rev) := by
    funext j
    exact congrArg v (hrev j)
  have hout : verifyRotationCertificate (probeBody F (List.ofFn (v ∘ p)))
      certificate = true := by
    simpa only [B, hscope, probeBody, List.reverse_ofFn, Function.comp_apply] using ht
  have hv : Function.Injective v := List.nodup_ofFn.mp hn
  have hn' : (List.ofFn (v ∘ p)).Nodup := List.nodup_ofFn.mpr (hv.comp p.injective)
  exact Witness.ofProbe hn' certificate hout

/-- Cyclically shift a distinct named boundary one step forwards, retaining the literal
body. The probe uses the opposite directed shift, not a reflected argument rotation. -/
noncomputable def Witness.rotateOfFn {F : CSP Rel V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hn : (List.ofFn v).Nodup) :
    Witness F (List.ofFn (v ∘ finRotate n)) :=
  reindexOfFn w hn (finRotate n) (finRotate n).symm (by
    intro j
    simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]) (by
      intro j
      have := j.neZero
      rw [finRotate_symm_apply, Fin.rev_sub, finRotate_apply])

/-- Cyclically shift a distinct named boundary one step backwards. Arity zero and one,
unused ports, arbitrary body degree and closed components need no separate provider. -/
noncomputable def Witness.unrotateOfFn {F : CSP Rel V} {n : ℕ} {v : Fin n → V}
    (w : Witness F (List.ofFn v)) (hn : (List.ofFn v).Nodup) :
    Witness F (List.ofFn (v ∘ (finRotate n).symm)) :=
  reindexOfFn w hn (finRotate n).symm (finRotate n) (by intro j; rfl) (by
    intro j
    have := j.neZero
    rw [finRotate_apply, Fin.rev_add, finRotate_symm_apply])

end Cslib.Complexity.CSP.OrderedBoundary
