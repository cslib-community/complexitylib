/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SigmaProtocol.Abort
import Complexity.Probability.PMF.Option

/-!
# Recovering complete aborting transcript laws

Erased-abort equality alone does not determine a full transcript. Equality of the commitment
marginal supplies the missing information. Equality at each fixed challenge then also applies
to a common deterministic challenge chosen from the commitment.

## Main results

* `SigmaProtocol.transcript_eq_of_acceptedTranscript_eq`: recover full optional-response laws.
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

/-- Equality of full transcripts at every fixed challenge gives equality when the same
challenge function is applied to the observed commitment. This is an equality of laws, not a
coupling that reuses the prover's private coins in two runs. -/
theorem map_respond_challenge_eq_of_transcript_eq {X Y T C Z : Type u}
    (P : SigmaProtocol X Y T C Z) {x x' : X} {y : Y}
    (h : ∀ c, P.transcript x y c = P.transcript x' y c) (challenge : T → C) :
    ((P.commit x y).map fun ts => (ts.1, P.respond x y ts.2 (challenge ts.1))) =
      (P.commit x' y).map fun ts => (ts.1, P.respond x' y ts.2 (challenge ts.1)) := by
  classical
  have hmass (w : T) (z : Z) (x : X) :
      ((P.commit x y).map fun ts => (ts.1, P.respond x y ts.2 (challenge ts.1))) (w, z) =
        P.transcript x y (challenge w) (w, z) := by
    simp only [transcript, PMF.map_apply]
    apply tsum_congr
    intro ts
    by_cases hw : ts.1 = w
    · simp only [hw]
    · simp [Prod.mk.injEq, Ne.symm hw]
  ext ⟨w, z⟩
  rw [hmass, hmass, h]

end Cslib.Crypto.Protocols.SigmaProtocol
