/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ConcreteSupplier
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitialVectorCorrect
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi

/-!
# Explicit uniform storage for concrete evaluator suppliers

The bounds use binary metadata at the supplied horizon and the actual field-point dimensions.
The point and assignment capacity are charged with constant coefficients, independent of the
number of coordinates and the schedule horizon. Replay uses the existing linear local replay
allowance, with binary origins bounded by the horizon and a fixed finite head-row allowance.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ConcreteSupplier

open MultiTapeTM Cslib.TreeEval.Ary Cslib.TreeEval.Ary.Packed
open QueryReplay
open MultiTapeNTM.ChoiceTable

/-- Point-free binary metadata at the horizon and largest requested output coordinate. -/
@[expose] noncomputable def metadataSpace
    (N b σ q m alphabet limit p d r : ℕ) : ℕ :=
  (QueryGate.encParams Interpolation.encContext
    ((N, b, σ, q, m, r, r * m), (p, alphabet, d * r), [], limit)).length

/-- Uniform replay allowance: origins are binary horizon counts and the head family is fixed. -/
@[expose] noncomputable def replaySpace (k s : ℕ) (Q : Type)
    (N b q m r : ℕ) : ℕ :=
  2 * (SupplierChunk.encContext (m, r)).length + 1 + (Encoding.width k s b + 1) +
    (2 * (4 * (encNat q).length +
      Fintype.card (Option (Fin k)) * (2 * Nat.card SignType + 1) + 2) + 2 +
      1024 * (k + 1) * (b + Nat.log2 N + Nat.card (Option Q) + Nat.card OutputTrack + 1))

/-- Concrete gate storage, without multiplying the point or assignment limit by the horizon. -/
@[expose] noncomputable def gateSpace (k s : ℕ) (Q : Type)
    (N b σ q m alphabet limit p d r : ℕ) : ℕ :=
  let cell := 2 * (encNat p).length + 1
  48 * (metadataSpace N b σ q m alphabet limit p d r + 2 * (d * r * cell) + 1) +
    16 * (encNat r).length + 2 * r * cell + replaySpace k s Q N b q m r + 5

private theorem normalized_point_encoding_le {p d r : ℕ} (point : List ℕ)
    (hp : 0 < p) (hlen : point.length ≤ d * r) :
    (encList encNat (NormalizePoint.normalize p point)).length ≤
      d * r * (2 * (encNat p).length + 1) := by
  have h := length_encList_le encNat (NormalizePoint.normalize p point)
    (b := (encNat p).length) (by
      intro value hvalue
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hvalue
      exact length_encNat_mono (Nat.mod_lt v hp).le)
  rw [NormalizePoint.length_normalize] at h
  exact h.trans (Nat.mul_le_mul_right _ hlen)

/-- The replay's two origin counters never exceed the supplied horizon. -/
theorem calleeSpace_le_replaySpace {k s : ℕ} {Q : Type}
    (N b σ q m r i : ℕ) (hi : i ≤ q) :
    Interpolation.calleeSpace k s Q (N, b, σ, i, m, r, r * m) ≤
      replaySpace k s Q N b q m r := by
  have hp := length_encNat_mono ((ScheduleRead.iterate_snd_le k 0 2 σ i).trans hi)
  have hn := length_encNat_mono ((ScheduleRead.iterate_snd_le k 0 0 σ i).trans hi)
  have hrow := length_encPi_le (encFinite SignType) (ScheduleRead.fullrow k (σ, i))
    (bound := Nat.card SignType) (fun _ => (length_encFinite_lt _).le)
  change (encNat (ScheduleRead.read k 0 2 (σ, i))).length ≤ (encNat q).length at hp
  change (encNat (ScheduleRead.read k 0 0 (σ, i))).length ≤ (encNat q).length at hn
  simp only [Interpolation.calleeSpace, ScheduleRead.origin, Gate.encContext,
    length_encPair, replaySpace]
  omega

private theorem interpolation_params_encoding_le
    (N b σ q m alphabet limit p d r i chunk : ℕ) (point : List ℕ)
    (hi : i ≤ q) (hc : chunk ≤ r)
    (hpoint : (encList encNat point).length ≤ d * r * (2 * (encNat p).length + 1)) :
    (QueryGate.encParams Interpolation.encContext
      ((N, b, σ, i, m, chunk, r * m), (p, alphabet, d * r), point, limit)).length ≤
        metadataSpace N b σ q m alphabet limit p d r +
          2 * (d * r * (2 * (encNat p).length + 1)) := by
  have hi' := length_encNat_mono hi
  have hc' := length_encNat_mono hc
  simp only [metadataSpace, QueryGate.encParams, Interpolation.encContext, encNat3,
    length_encPair]
  have hempty : (encList encNat []).length = 0 := rfl
  rw [hempty]
  omega

/-- Every stored request point of the stated dimensions has one explicit uniform gate bound.
No validity or typed-path premise is needed: navigation is bounded even on malformed paths. -/
theorem allowance_le {k s : ℕ} {Q : Type}
    (N b σ q m alphabet limit p d r tag chunk : ℕ) (path point : List ℕ)
    (hp : 0 < p) (hlen : point.length ≤ d * r) :
    GateReply.allowance k s Q
      (gateArgs ((N, b, σ, q, m, alphabet, limit), (p, d, r), (tag, path, point, chunk))) ≤
        gateSpace k s Q N b σ q m alphabet limit p d r := by
  let i := ImplicitPath.walk k (σ, q, path) - 1
  have hi : i ≤ q := (Nat.sub_le _ _).trans (ImplicitPath.walk_le k σ q path)
  have hpoint := normalized_point_encoding_le point hp hlen
  have hparams := interpolation_params_encoding_le N b σ q m alphabet limit p d r i 0
    (NormalizePoint.normalize p point) hi (Nat.zero_le r) hpoint
  have hmax := interpolation_params_encoding_le N b σ q m alphabet limit p d r i r
    (NormalizePoint.normalize p point) hi le_rfl hpoint
  have hcallee := calleeSpace_le_replaySpace (k := k) (s := s) (Q := Q)
    N b σ q m r i hi
  change 2 * GateVector.callerSpace
      (((N, b, σ, i, m, 0, r * m), (p, alphabet, d * r),
        NormalizePoint.normalize p point, limit), r) +
      16 * ((QueryGate.encParams Interpolation.encContext
        ((N, b, σ, i, m, r, r * m), (p, alphabet, d * r),
          NormalizePoint.normalize p point, limit)).length + 1) +
      Interpolation.calleeSpace k s Q (N, b, σ, i, m, r, r * m) + 5 ≤ _
  simp only [GateVector.callerSpace, GateVector.encParams, length_encPair, gateSpace]
    at hparams hmax ⊢
  simp only [Nat.mul_assoc] at hparams hmax ⊢
  omega

/-- Actual modulus-padded field points satisfy the uniform dimension bound directly. -/
theorem allowance_le_padded {k s : ℕ} {Q : Type}
    (N b σ q m alphabet limit p d r tag chunk : ℕ) (path : List ℕ)
    (x : Fin (d * r) → ZMod p) (hp : 0 < p) :
    GateReply.allowance k s Q
      (gateArgs ((N, b, σ, q, m, alphabet, limit), (p, d, r),
        (tag, path, List.ofFn (fun j => p + (x j).val), chunk))) ≤
      gateSpace k s Q N b σ q m alphabet limit p d r :=
  allowance_le N b σ q m alphabet limit p d r tag chunk path _ hp
    (by simp only [List.length_ofFn, le_refl])

/-- Immediate node replies pay only for one field vector and a fixed reply tag. -/
theorem node_reply_encoding_le {k s p r m : ℕ} {Q : Type}
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (limit b σ q : ℕ) [NeZero b]
    (path : List ℕ) (hcapacity : r ≤ limit.size)
    (hb : Encoding.width k s b ≤ r * m) (hsp : 2 ^ m ≤ p) :
    (RawController.encReply (NodeReply.reply M e ((σ, q, path), (limit, m, r)))).length ≤
      r * (2 * (encNat p).length + 1) + 8 := by
  have hvalues := length_encList_le encNat (InitialVector.values M e (limit, m, r))
    (b := (encNat p).length) (by
      intro value hvalue
      rw [InitialVector.values_eq_packBits M e limit b hcapacity hb] at hvalue
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hvalue
      exact length_encNat_mono ((Fin.isLt _).trans_le hsp).le)
  have hlength : (InitialVector.values M e (limit, m, r)).length = r := by
    rw [InitialVector.length_values, Nat.min_eq_left hcapacity]
  rw [hlength] at hvalues
  have htag : ImplicitNode.classify k (σ, q, path) ≤ 2 := by
    simp only [ImplicitNode.classify]
    split <;> (try split) <;> omega
  have htaglen := length_encNat_mono htag
  have htwo : (encNat 2).length = 2 := rfl
  have hone : (encNat 1).length = 1 := rfl
  simp only [NodeReply.reply, hcapacity, ↓reduceIte]
  split
  · simp only [RawController.encReply, length_encPair]
    omega
  · simp only [RawController.encReply, length_encPair]
    have hempty : (encList encNat []).length = 0 := rfl
    rw [hempty]
    omega

end Turing.MultiTapePTM.BlockComputation.ConcreteSupplier
