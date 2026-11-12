/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Transport
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateLookup
import Mathlib.Data.List.GetD

/-!
# Exact certificates under positional dart transport

A dart equivalence retaining each binary edge/end index keeps the generated successor list
literally unchanged. Vertex names and declared isolated points need not coincide. These
original list identities connect dense incidence-name transport to computed certificate
programs, without replacing either table by an existential certificate.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- Position-preserving transport retains every literal successor-table lookup. -/
theorem getD_ofRotation_transport {G H : Graph} (r : RotationSystem G) (e : Dart G ≃ Dart H)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
    (hi : ∀ a, (e a).index = a.index) (d : Dart G) :
    (RotationCertificate.ofRotation (r.transport e hv)).successor.getD d.index 0 =
      (r.rotate d).index := by
  rw [← hi d, RotationCertificate.getD_ofRotation]
  simp only [transport, Equiv.permCongr_apply, Equiv.symm_apply_apply, hi]

/-- The complete generated certificate is unchanged by actual edge/end position transport. -/
theorem ofRotation_transport {G H : Graph} (r : RotationSystem G) (e : Dart G ≃ Dart H)
    (hv : ∀ a b, (e a).vertex = (e b).vertex ↔ a.vertex = b.vertex)
    (hi : ∀ a, (e a).index = a.index) :
    RotationCertificate.ofRotation (r.transport e hv) = RotationCertificate.ofRotation r := by
  have hn := Fintype.card_congr e
  rw [Dart.card, Dart.card] at hn
  symm
  refine (RotationCertificate.ofRotation_eq_iff r _).mpr ⟨?_, ?_⟩
  · rw [RotationCertificate.length_ofRotation]
    omega
  · exact getD_ofRotation_transport r e hv hi

end Cslib.Complexity.Graph.RotationSystem

namespace Cslib.Complexity.Graph.RotationCertificate

/-- Decoding an accepted raw table and encoding its actual rotation returns that very
table, including empty tables. Acceptance supplies the exact list length internally. -/
theorem ofRotation_decode {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) : ofRotation (decode G c h) = c := by
  exact (ofRotation_eq_iff (decode G c h) c).mpr
    ⟨length_of_verifyRotation h, fun d => (index_decode_rotate h d).symm⟩

end Cslib.Complexity.Graph.RotationCertificate
