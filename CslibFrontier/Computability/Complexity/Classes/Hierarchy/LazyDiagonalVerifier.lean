/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.LazyDiagonal
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Tactic.Ring

/-!
# Resource certificates for lazy-diagonal verifiers

Assemble the common input decoding, simulation, negated exhaustive search and conditional
branches of a lazy-diagonal verifier. Clock construction and its estimates belong to callers:
the polynomial and exponential hierarchies use different clocks. The resulting time bound
charges only the branch taken; the space witness is independent of that time bound.

## Main results

* `Cslib.Complexity.Diagonal.exists_computableInO_lazyVerifier`: assemble a verifier from
  certificates for its tests, acceptance simulation and exhaustive search.
-/

public section

namespace Cslib.Complexity.Diagonal

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Compose the lazy verifier without replacing branch costs by their worst case.
The caller supplies three tests at cost `C`, an acceptance simulation at cost `B`, and
exhaustive search at cost `R`. Test space bounds may differ from each other and from time. -/
theorem exists_computableInO_lazyVerifier
    {β : List Bool → List Bool → ℕ} {L H : ℕ → ℕ}
    {C S₀ S₁ S₂ : List Bool × List Bool → ℕ}
    {B SB : List Bool × List Bool × List Bool → ℕ}
    {R SR : List Bool × List Bool → ℕ}
    (hacc : ComputableInO (fun q : List Bool × List Bool × List Bool =>
      lazyAccepts β q.1 q.2.1 q.2.2) (encPair encBits (encPair encBits encBits)) encBool B SB)
    (hbrute : ComputableInO (fun q : List Bool × List Bool =>
      (Cslib.BitString.enumList (L q.2.length)).any (lazyAccepts β q.1 q.2))
      (encPair encBits encBits) encBool R SR)
    (hc₀ : ComputableInO (fun p : List Bool × List Bool => shortDesc (unframe p.1))
      (encPair encBits encBits) encBool C S₀)
    (hc₁' : ComputableInO (fun p : List Bool × List Bool =>
      decide (Nat.size (p.1.length + 1) ≤ H (2 * (unframe p.1).length + 1)))
      (encPair encBits encBits) encBool C S₁)
    (hc₂' : ComputableInO (fun p : List Bool × List Bool =>
      decide (Nat.size p.1.length ≤ H (2 * (unframe p.1).length + 1)))
      (encPair encBits encBits) encBool C S₂)
    (hC : ∀ p, (encPair encBits encBits p).length + 1 ≤ C p) :
    ∃ S, ComputableInO (lazyVerifier β L H) (encPair encBits encBits) encBool
      (fun p => C p + if shortDesc (unframe p.1) then
        (C p + if Nat.size (p.1.length + 1) ≤ H (2 * (unframe p.1).length + 1) then
          C p + B (unframe (unframe p.1), p.1 ++ [false], p.2)
        else (C p + if Nat.size p.1.length ≤ H (2 * (unframe p.1).length + 1) then
          C p + R (unframe (unframe p.1), frame (unframe p.1))
          else C p))
        else C p) S := by
  have hx := ComputableInO.fst encBits encBits
  have hun : ComputableInO unframe encBits encBits (fun z => z.length) (fun z => z.length) :=
    ComputableInO.of_linear (.of_unframe fun _ => rfl)
  have hfr : ComputableInO frame encBits encBits (fun z => z.length) (fun z => z.length) :=
    ComputableInO.of_linear (.of_frame fun _ => rfl)
  have hw := hun.comp hx
  have hcode := hun.comp hw
  have hbase := hfr.comp hw
  have hsnoc : ComputableInO (fun p : List Bool × List Bool => p.1 ++ [false])
      (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length + (encPair encBits encBits p).length)
      (fun p => (encPair encBits encBits p).length + (encPair encBits encBits p).length) :=
    hx.append (ComputableInO.const (encMid := encBits) [false]) fun _ => rfl
  have hf₁ := ComputableInO.mono_time
      (hacc.comp (hcode.prod (hsnoc.prod (ComputableInO.snd encBits encBits))))
      (T' := fun p => C p + B (unframe (unframe p.1), p.1 ++ [false], p.2)) 7
      fun p => by
    have h₁ := hC p
    simp only [Function.comp_apply] at ⊢
    have : 7 * (C p + B (unframe (unframe p.1), p.1 ++ [false], p.2) + 1) =
        7 * C p + 7 * B (unframe (unframe p.1), p.1 ++ [false], p.2) + 7 := by ring
    omega
  have hf₂ := ComputableInO.mono_time ((ComputableInDegree.of_finite (encIn := encBool)
    (encMid := encBool) (fun b : Bool => !b)).inO_one.comp (hbrute.comp (hcode.prod hbase)))
      (T' := fun p => C p + R (unframe (unframe p.1), frame (unframe p.1))) 7
      fun p => by
    have h₁ := hC p
    have hb : (encBool ((Cslib.BitString.enumList (L (frame (unframe p.1)).length)).any
        (Diagonal.lazyAccepts β (unframe (unframe p.1)) (frame (unframe p.1))))).length = 1 := rfl
    simp only [Function.comp_apply, hb] at ⊢
    set cost := R (unframe (unframe p.1), frame (unframe p.1))
    have : 7 * (C p + cost + 1) = 7 * C p + 7 * cost + 7 := by ring
    omega
  have hfalse := ComputableInO.mono_time (ComputableInO.const (encIn := encPair encBits encBits)
    (encMid := encBool) false) (T' := C) 1 fun p => by
    have h₁ := hC p; omega
  have h := hc₀.ite (hc₁'.ite hf₁ (hc₂'.ite hf₂ hfalse)) hfalse
  refine ⟨_, (h.of_enc_eq fun p => ?_).mono_le (fun p => le_of_eq ?_) fun p => le_rfl⟩
  · congr 1
    simp only [Diagonal.lazyVerifier, Function.comp_apply, decide_eq_true_eq,
      length_frame]
  · simp only [Function.comp_apply, decide_eq_true_eq]

end Cslib.Complexity.Diagonal
