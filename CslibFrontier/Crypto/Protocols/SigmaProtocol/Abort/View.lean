/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Abort
import CslibFrontier.Probability.PMF.Option

/-!
# Recovering complete aborting transcript laws

Erased-abort equality alone does not determine a full transcript. Equality of the commitment
marginal supplies the missing information. Equality at each fixed challenge then also applies
to a common public randomized challenge/state kernel chosen from the commitment, including
deterministic commitment-dependent challenges.

## Main results

* `SigmaProtocol.transcript_eq_of_acceptedTranscript_eq`: recover full optional-response laws.
* `SigmaProtocol.bind_respond_challenge_eq_of_transcript_eq`: public randomized challenges/state.
* `SigmaProtocol.map_respond_challenge_eq_of_transcript_eq`: choose challenges from commitments.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability

universe u

/-- Equal commitment marginals and erased-abort laws determine the full transcript, including
the commitment when the response is `none`. -/
theorem transcript_eq_of_acceptedTranscript_eq {X Y T C Z : Type u}
    (P : SigmaProtocol X Y T C (Option Z)) {x x' : X} {y : Y} {c : C}
    (hcommit : (P.commit x y).map Prod.fst = (P.commit x' y).map Prod.fst)
    (haccept : P.acceptedTranscript x y c = P.acceptedTranscript x' y c) :
    P.transcript x y c = P.transcript x' y c := by
  apply PMF.ext_prod_option
  · simpa only [transcript, PMF.map_comp, Function.comp_def] using hcommit
  · exact haccept

/-- Equal full fixed-challenge laws remain equal under a common public randomized challenge
and state kernel. The kernel sees the commitment but not the witness or private prover state. -/
theorem bind_respond_challenge_eq_of_transcript_eq {X Y T C Z : Type u} {R : Type*}
    (P : SigmaProtocol X Y T C Z) {x x' : X} {y : Y}
    (h : ∀ c, P.transcript x y c = P.transcript x' y c) (kernel : T → PMF (C × R)) :
    ((P.commit x y).bind fun ts => (kernel ts.1).map fun cr =>
      (ts.1, cr.1, P.respond x y ts.2 cr.1, cr.2)) =
    (P.commit x' y).bind fun ts => (kernel ts.1).map fun cr =>
      (ts.1, cr.1, P.respond x' y ts.2 cr.1, cr.2) := by
  classical
  have hmass (w : T) (c : C) (z : Z) (r : R) (x : X) :
      ((P.commit x y).bind fun ts => (kernel ts.1).map fun cr =>
        (ts.1, cr.1, P.respond x y ts.2 cr.1, cr.2)) (w, c, z, r) =
        kernel w (c, r) * P.transcript x y c (w, z) := by
    rw [PMF.bind_apply, transcript, PMF.map_apply, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro ts
    rw [PMF.map_apply, tsum_eq_single (c, r)]
    · by_cases hw : w = ts.1 <;> by_cases hz : z = P.respond x y ts.2 c <;>
        simp [Prod.mk.injEq, hw, hz, mul_comm]
    · rintro ⟨c', r'⟩ hne
      have hn : (w, c, z, r) ≠ (ts.1, c', P.respond x y ts.2 c', r') := by
        intro heq
        exact hne (congrArg (fun view : T × C × Z × R => (view.2.1, view.2.2.2)) heq).symm
      simp [hn]
  ext ⟨w, c, z, r⟩
  rw [hmass, hmass, h]

/-- Equality of full transcripts at every fixed challenge gives equality when the same
challenge function is applied to the observed commitment. This is an equality of laws, not a
coupling that reuses the prover's private coins in two runs. -/
theorem map_respond_challenge_eq_of_transcript_eq {X Y T C Z : Type u}
    (P : SigmaProtocol X Y T C Z) {x x' : X} {y : Y}
    (h : ∀ c, P.transcript x y c = P.transcript x' y c) (challenge : T → C) :
    ((P.commit x y).map fun ts => (ts.1, P.respond x y ts.2 (challenge ts.1))) =
      (P.commit x' y).map fun ts => (ts.1, P.respond x' y ts.2 (challenge ts.1)) := by
  have hk := bind_respond_challenge_eq_of_transcript_eq P h
    (fun w => PMF.pure (challenge w, ()))
  simpa only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def] using
    congrArg (PMF.map fun view => (view.1, view.2.2.1)) hk

end Cslib.Crypto.Protocols.SigmaProtocol
