/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists
import Complexity.Computability.GenericRAM.Native.Certificate
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Polynomially many queries with a common running-time factor

A polynomial-time procedure produces a list of queries. The answer procedure may take
superpolynomial time, but its time on each query is a common factor `T x` times a polynomial in
the encoded query, and its workspace is polynomial. Computing all answers costs only a
polynomial factor beyond `T x` and still uses polynomial space, including the full answer list.

The theorem uses the plain native list-mapping machine. In particular, it does not assume an
oracle for the answers or charge a superpolynomial answer procedure as a polynomial-time step.

## Main results

* `Turing.MultiTapeTM.ComputableInO.polynomial_queries`: polynomially many queries preserve a
  common running-time factor and polynomial workspace.
* `Turing.MultiTapeTM.ComputableInO.polynomial_postprocessing`: polynomial postprocessing has
  the same preservation property when the producer uses polynomial space.
-/

public section

namespace Turing.MultiTapeTM.ComputableInO

open Cslib.GenericRAM

variable {α β γ : Type} {ei : α ↪ List Bool} {eq : β ↪ List Bool} {eo : γ ↪ List Bool}

/-- Compute a polynomial-size list of answers while preserving the common running-time factor.
The constants `e`, `b`, and the resulting `d` are fixed before the input `x`. -/
theorem polynomial_queries {answer : α × β → γ} {queries : α → List β}
    {T : α → ℕ} {e b : ℕ}
    (ha : ComputableInO answer (encPair ei eq) eo
      (fun p => T p.1 * ((encPair ei eq p).length + 1) ^ e)
      (fun p => ((encPair ei eq p).length + 1) ^ b))
    (hq : ComputableInPolyTime queries ei (encList eq)) (hT : ∀ x, 1 ≤ T x) :
    ∃ d : ℕ, ComputableInO (fun x => (queries x).map fun q => answer (x, q))
      ei (encList eo) (fun x => T x * ((ei x).length + 1) ^ d)
      (fun x => ((ei x).length + 1) ^ d) := by
  let cq := NativeCertificate.ofPolyTime hq
  have hcq := NativeCertificate.ofPolyTime_isPolynomial hq
  let L := fun x => (ei x).length
  let Q := fun x => (encList eq (queries x)).length
  let B := fun x => 2 * L x + Q x + 2
  let O := fun x => (encList eo ((queries x).map fun q => answer (x, q))).length
  have hL : PolyBounded L L := .self
  have hQ : PolyBounded L Q := hq.polyBounded_length
  have hB : PolyBounded L B :=
    (((PolyBounded.const 2).mul hL).add hQ).add (PolyBounded.const 2)
  have hquery (x : α) (q : β) (h : q ∈ queries x) :
      (encPair ei eq (x, q)).length + 1 ≤ B x := by
    have := length_le_encList_of_mem eq h
    simp only [length_encPair]
    dsimp [B, L, Q]
    omega
  obtain ⟨c, hc⟩ := ha.length_le
  have hO : PolyBounded L O := by
    refine (hQ.mul (((PolyBounded.const 2).mul ((PolyBounded.const c).mul
      ((hB.pow b).add (PolyBounded.const 1)))).add (PolyBounded.const 1))).mono fun x => ?_
    have hlen := length_encList_le eo ((queries x).map fun q => answer (x, q))
      (b := c * (B x ^ b + 1)) fun a ha => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        exact (hc (x, q)).trans (Nat.mul_le_mul_left c (Nat.add_le_add_right
          (Nat.pow_le_pow_left (hquery x q hq) b) 1))
    rw [List.length_map] at hlen
    exact hlen.trans (Nat.mul_le_mul_right _ (length_le_length_encList eq (queries x)))
  let U := fun x => L x + L x + cq.time x +
    (Q x + 1) * (L x + Q x + O x + B x ^ e)
  let V := fun x => L x + L x + cq.space x + L x + Q x + O x + B x ^ b
  have hU : PolyBounded L U :=
    ((hL.add hL).add hcq.1).add
      ((hQ.add (PolyBounded.const 1)).mul (((hL.add hQ).add hO).add (hB.pow e)))
  have hV : PolyBounded L V :=
    (((((hL.add hL).add hcq.2).add hL).add hQ).add hO).add (hB.pow b)
  obtain ⟨k, d, hk⟩ := (hU.add hV).exists_le
  have hmap := ha.mapWith
    (ComputableInO.of_eq (encIn := ei) (encMid := ei) fun _ => rfl) cq.computes
  refine ⟨d, hmap.mono k (fun x => ?_) (fun x => ?_)⟩
  · have hmax : listMax (fun q => T x * ((encPair ei eq (x, q)).length + 1) ^ e)
        (queries x) ≤ T x * B x ^ e :=
      listMax_le fun q hq => Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (hquery x q hq) e)
    have hlen : (queries x).length ≤ Q x := length_le_length_encList eq (queries x)
    have hfirst : L x + L x + cq.time x ≤ T x * (L x + L x + cq.time x) :=
      Nat.le_mul_of_pos_left _ (hT x)
    have hbody : L x + Q x + O x + T x * B x ^ e ≤
        T x * (L x + Q x + O x + B x ^ e) := by
      have := Nat.le_mul_of_pos_left (L x + Q x + O x) (hT x)
      nlinarith
    have hbound : L x + L x + cq.time x + ((queries x).length + 1) *
        (L x + Q x + O x + listMax
          (fun q => T x * ((encPair ei eq (x, q)).length + 1) ^ e) (queries x)) ≤
        T x * U x := by
      calc _ ≤ L x + L x + cq.time x +
            (Q x + 1) * (L x + Q x + O x + T x * B x ^ e) := by
              exact Nat.add_le_add_left (Nat.mul_le_mul (by omega)
                (Nat.add_le_add_left hmax _)) _
        _ ≤ T x * (L x + L x + cq.time x) +
            (Q x + 1) * (T x * (L x + Q x + O x + B x ^ e)) :=
              Nat.add_le_add hfirst (Nat.mul_le_mul_left _ hbody)
        _ = T x * U x := by dsimp [U]; ring
    have hpoly : U x ≤ k * (L x + 1) ^ d := (Nat.le_add_right _ _).trans (hk x)
    have h := hbound.trans (Nat.mul_le_mul_left (T x) hpoly)
    dsimp [L, Q, O] at h
    nlinarith
  · have hmax : listMax (fun q => ((encPair ei eq (x, q)).length + 1) ^ b)
        (queries x) ≤ B x ^ b :=
      listMax_le fun q hq => Nat.pow_le_pow_left (hquery x q hq) b
    have hpoly : V x ≤ k * (L x + 1) ^ d := (Nat.le_add_left _ _).trans (hk x)
    dsimp [V, L, Q, O] at hpoly
    nlinarith

/-- Polynomial postprocessing of a polynomial-space result preserves the common time factor.
The producer itself need not run in polynomial time. -/
theorem polynomial_postprocessing {f : α → β} {g : β → γ} {T : α → ℕ} {e b : ℕ}
    (hf : ComputableInO f ei eq (fun x => T x * ((ei x).length + 1) ^ e)
      (fun x => ((ei x).length + 1) ^ b))
    (hg : ComputableInPolyTime g eq eo) (hT : ∀ x, 1 ≤ T x) :
    ∃ d : ℕ, ComputableInO (g ∘ f) ei eo (fun x => T x * ((ei x).length + 1) ^ d)
      (fun x => ((ei x).length + 1) ^ d) := by
  let cg := NativeCertificate.ofPolyTime hg
  have hcg := NativeCertificate.ofPolyTime_isPolynomial hg
  let L := fun x => (ei x).length
  have hL : PolyBounded L L := .self
  have hLp : PolyBounded L (fun x => (L x + 1)) := hL.add (PolyBounded.const 1)
  have hlen : PolyBounded L (fun x => (eq (f x)).length) := by
    obtain ⟨c, hc⟩ := hf.length_le
    exact ((PolyBounded.const c).mul ((hLp.pow b).add (PolyBounded.const 1))).mono hc
  have htime : PolyBounded L (fun x => cg.time (f x)) := hcg.1.comp hlen
  have hspace : PolyBounded L (fun x => cg.space (f x)) := hcg.2.comp hlen
  let P := fun x => (L x + 1) ^ e + cg.time (f x) + (L x + 1) ^ b + cg.space (f x)
  have hP : PolyBounded L P := (((hLp.pow e).add htime).add (hLp.pow b)).add hspace
  obtain ⟨k, d, hk⟩ := hP.exists_le
  refine ⟨d, (cg.computes.comp hf).mono k (fun x => ?_) (fun x => ?_)⟩
  · have hscale := Nat.le_mul_of_pos_left (cg.time (f x)) (hT x)
    have hp : (L x + 1) ^ e + cg.time (f x) ≤ P x := by dsimp [P]; omega
    calc T x * (L x + 1) ^ e + cg.time (f x)
        ≤ T x * ((L x + 1) ^ e + cg.time (f x)) := by
          rw [Nat.mul_add]
          exact Nat.add_le_add_left hscale _
      _ ≤ T x * P x := Nat.mul_le_mul_left _ hp
      _ ≤ T x * (k * (L x + 1) ^ d) := Nat.mul_le_mul_left _ (hk x)
      _ = k * (T x * (L x + 1) ^ d) := by ring
      _ ≤ k * (T x * (L x + 1) ^ d + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
  · have hp : (L x + 1) ^ b + cg.space (f x) ≤ P x := by dsimp [P]; omega
    exact (hp.trans (hk x)).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))

end Turing.MultiTapeTM.ComputableInO
