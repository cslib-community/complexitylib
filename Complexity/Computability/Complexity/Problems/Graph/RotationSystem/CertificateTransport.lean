/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Transport
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
  apply congrArg RotationCertificate.mk
  refine List.ext_getElem (by
    change (RotationCertificate.ofRotation (r.transport e hv)).successor.length =
      (RotationCertificate.ofRotation r).successor.length
    rw [RotationCertificate.length_ofRotation, RotationCertificate.length_ofRotation]
    omega) ?_
  intro i hH hG
  change i < (RotationCertificate.ofRotation (r.transport e hv)).successor.length at hH
  change i < (RotationCertificate.ofRotation r).successor.length at hG
  change (RotationCertificate.ofRotation (r.transport e hv)).successor[i] =
    (RotationCertificate.ofRotation r).successor[i]
  rw [← List.getD_eq_getElem (RotationCertificate.ofRotation (r.transport e hv)).successor 0 hH,
    ← List.getD_eq_getElem (RotationCertificate.ofRotation r).successor 0 hG]
  have hb : i < 2 * G.2.length := by rwa [RotationCertificate.length_ofRotation] at hG
  let d := (Dart.indexEquiv G).symm ⟨i, hb⟩
  have hd : d.index = i := congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply ⟨i, hb⟩)
  rw [← hd, getD_ofRotation_transport r e hv hi, RotationCertificate.getD_ofRotation]

end Cslib.Complexity.Graph.RotationSystem

namespace Cslib.Complexity.Graph.RotationCertificate

/-- Decoding an accepted raw table and encoding its actual rotation returns that very
table, including empty tables. Acceptance supplies the exact list length internally. -/
theorem ofRotation_decode {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) : ofRotation (decode G c h) = c := by
  apply congrArg RotationCertificate.mk
  refine List.ext_getElem (by
    change (ofRotation (decode G c h)).successor.length = c.successor.length
    rw [length_ofRotation, length_of_verifyRotation h]) ?_
  intro i hi hj
  change i < (ofRotation (decode G c h)).successor.length at hi
  change (ofRotation (decode G c h)).successor[i] = c.successor[i]
  rw [← List.getD_eq_getElem (ofRotation (decode G c h)).successor 0 hi,
    ← List.getD_eq_getElem c.successor 0 hj]
  have hb : i < 2 * G.2.length := by rwa [length_ofRotation] at hi
  let d := (Dart.indexEquiv G).symm ⟨i, hb⟩
  have hd : d.index = i := congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply ⟨i, hb⟩)
  rw [← hd, getD_ofRotation, index_decode_rotate]

end Cslib.Complexity.Graph.RotationCertificate
