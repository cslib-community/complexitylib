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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.BitLength
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.LazyDiagonalBounds
import CslibFrontier.Computability.Complexity.Classes.Time.BoundedExists
import Mathlib.Tactic.Ring
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame

/-!
# Resource certificates for lazy-diagonal verifiers

Assemble the common input decoding, simulation, negated exhaustive search and conditional
branches of a lazy-diagonal verifier. Clock construction and its estimates belong to callers:
the polynomial and exponential hierarchies use different clocks. The resulting time bound
charges only the branch taken; the space witness is independent of that time bound.

## Main results

* `Cslib.Complexity.Diagonal.exists_computableInO_lazyAccepts`: construct acceptance from a binary clock.
* `Cslib.Complexity.Diagonal.exists_computableInO_lazyBrute`: search with polynomial-time
  acceptance and parameter selection, including a separately supplied unary length.
* `Cslib.Complexity.Diagonal.exists_computableInO_sizeLength_le`: construct a horizon comparison
  from an independently bounded unary clock.
* `Cslib.Complexity.Diagonal.exists_computableInO_lazyTests`: construct the three tests together.
* `Cslib.Complexity.Diagonal.exists_computableInO_lazyVerifier`: assemble a verifier from
  certificates for its tests, acceptance simulation and exhaustive search.
-/

public section

namespace Cslib.Complexity.Diagonal

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Description, input and certificate encoding for lazy acceptance simulation.
The word is `frame description ++ frame input ++ certificate`. -/
abbrev encLazyAcceptsInput : (List Bool × List Bool × List Bool) ↪ List Bool :=
  encPair encBits (encPair encBits encBits)

/-- Construct the acceptance simulation with an arbitrary binary clock. Its time and space
budgets include input access; positivity and a linear binary-length bound suffice for the
shared universal-simulation estimate. The clock may depend on both input and certificate. -/
theorem exists_computableInO_lazyAccepts
    (β : List Bool → List Bool → ℕ) (a : ℕ)
    (hclock : ComputableInO (fun q : List Bool × List Bool × List Bool => β q.2.1 q.2.2)
      (encLazyAcceptsInput) encNat
      (fun q => (encLazyAcceptsInput q).length + β q.2.1 q.2.2)
      (fun q => (encLazyAcceptsInput q).length + β q.2.1 q.2.2))
    (hlen : ∀ y v, (encNat (β y v)).length ≤ (a + 4) * (y.length + v.length + 1))
    (hpos : ∀ y v, 1 ≤ β y v) :
    ∃ D, ComputableInO (fun q : List Bool × List Bool × List Bool => lazyAccepts β q.1 q.2.1 q.2.2)
      (encLazyAcceptsInput) encBool
      (fun q => ((q.1.length + 1) ^ D + q.2.1.length + q.2.2.length + 1) ^ 4 * (β q.2.1 q.2.2) ^ 2)
      (fun q => ((q.1.length + 1) ^ D + q.2.1.length + q.2.2.length + 1) ^ 4 * (β q.2.1 q.2.2) ^ 2) := by
  obtain ⟨dd, ed, hdec⟩ := exists_computableInDegree_decodeDesc
  set enc := encLazyAcceptsInput
  have hdesc := hdec.inO.comp (ComputableInO.fst encBits (encPair encBits encBits))
  have hword : ComputableInO (fun q : List Bool × List Bool × List Bool => frame q.2.1 ++ q.2.2)
      enc encBits (fun q => (enc q).length) (fun q => (enc q).length) :=
    (ComputableInO.snd encBits (encPair encBits encBits)).of_enc_eq fun _ => rfl
  have hsym := Universal.computableInO_map_eBit.comp hword
  have hU := computableInO_universal.comp (hdesc.prod (hsym.prod hclock))
  have hv := Diagonal.computableInO_verdict.comp hU
  have hnot := (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
    (fun b : Bool => !b)).inO_one.comp hv
  obtain ⟨cD, hcD⟩ := hdesc.length_le
  obtain ⟨cO, hcO⟩ := hU.length_le
  obtain ⟨K, hK⟩ := LazyDiagonal.accBound_aux a cD cO
  have hbounds (q : List Bool × List Bool × List Bool) := by
    have hD := hcD q
    have hE := hcO q
    have hNl := length_encList_map_eBit_le (frame q.2.1 ++ q.2.2)
    have hc : q.1.length + 1 ≤ (q.1.length + 1) ^ (dd + 1) :=
      Nat.le_self_pow (Nat.succ_ne_zero _) _
    have hA : (q.1.length + 1) ^ dd ≤ (q.1.length + 1) ^ (dd + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _)
    simp only [Function.comp_apply, encBits_apply, enc, length_encPair, List.length_append,
      length_frame] at hD hE hNl ⊢
    exact hK (X := (q.1.length + 1) ^ (dd + 1) + q.2.1.length + q.2.2.length + 1)
      (by omega) (by omega) (by omega) hD hNl
      ((hlen q.2.1 q.2.2).trans (Nat.mul_le_mul_left (a + 4) (by omega)))
      (by omega) (hpos q.2.1 q.2.2) hE
  have hb (b : Bool) : (encBool b).length = 1 := rfl
  refine ⟨dd + 1, (hnot.mono K (fun q => ?_) fun q => ?_).of_enc_eq fun q => rfl⟩
  all_goals
    refine le_trans ?_ (Nat.mul_le_mul_left K (Nat.le_succ _))
    have ⟨h₁, h₂⟩ := hbounds q
    simp only [Function.comp_apply, encBits_apply, enc, length_encPair, List.length_append,
      length_frame, hb] at h₁ h₂ ⊢
    omega

/-- Exhaustive acceptance search after polynomial-time parameter selection. The parameter
may include a unary certificate length, so the same construction covers both directly
constructible lengths and lengths supplied by a separate, more expensive preprocessing step.
The bound charges the entire encoded parameter, preserving that preprocessing interface. -/
theorem exists_computableInO_lazyBrute
    {α : Type} {encA : α ↪ List Bool} {β : List Bool → List Bool → ℕ}
    {param : α → List Bool × List Bool} {ℓ : α → ℕ}
    (hacc : ComputableInPolyTime (fun q : List Bool × List Bool × List Bool =>
      lazyAccepts β q.1 q.2.1 q.2.2) (encLazyAcceptsInput) encBool)
    (hparam : ComputableInPolyTime param encA (encPair encBits encBits))
    (hℓ : ComputableInPolyTime ℓ encA encUnary) :
    ∃ K, ComputableInO (fun x => (Cslib.BitString.enumList (ℓ x)).any
      (lazyAccepts β (param x).1 (param x).2)) encA encBool
      (fun x => 2 ^ (K * ((encA x).length + ℓ x)))
      (fun x => 2 ^ (K * ((encA x).length + ℓ x))) := by
  have hp := hparam.comp (ComputableInPolyTime.fst encA encBits)
  have hre := hp.fst'.prod (hp.snd'.prod (ComputableInPolyTime.snd encA encBits))
  obtain ⟨T, S, hT, hS, hf⟩ := (hacc.comp hre).exists_computableInO
  exact exists_computableInO_any_enumList hf hT hS hℓ

/-- Construct a horizon comparison from a unary clock certificate. The tested word may
be the input or its one-bit extension. Only its time and length bounds are needed; its
space bound and the clock's space bound remain independent. -/
theorem exists_computableInO_sizeLength_le
    {z : List Bool × List Bool → List Bool} {E C T S Sz : List Bool × List Bool → ℕ}
    {M K : ℕ}
    (hz : ComputableInO z (encPair encBits encBits) encBits
      (fun p => 2 * (encPair encBits encBits p).length) Sz)
    (hE : ComputableInO E (encPair encBits encBits) encUnary T S)
    (hzlen : ∀ p, (z p).length ≤ p.1.length + 1)
    (hC : ∀ p, (encPair encBits encBits p).length + 1 ≤ C p)
    (hQ : ∀ p, (2 * (encPair encBits encBits p).length + 4 + E p) ^ 2 ≤ M * C p)
    (hT : ∀ p, T p ≤ K * C p) :
    ∃ S', ComputableInO (fun p => decide (Nat.size (z p).length ≤ E p))
      (encPair encBits encBits) encBool C S' := by
  have hsz : ComputableInO (fun z : List Bool => Nat.size z.length) encBits encUnary
      (fun z => (z.length + 1) ^ 2 + (encNat z.length).length)
      (fun z => z.length + 1 + (encNat z.length).length) :=
    (ComputableInO.lengthUnary.comp ((ComputableInO.lengthNat.mono 1
      (T' := fun z : List Bool => (z.length + 1) ^ 2) (S' := fun z => z.length + 1)
      (fun z => by nlinarith) fun z => by omega).of_enc_eq (encC := encBits)
      (g := fun z : List Bool => encNat z.length) fun _ => rfl)).of_enc_eq fun z => by
        simp [encNat_apply, Nat.size_eq_bits_len]
  have h := ComputableInO.unaryLe.comp ((hsz.comp hz).prod hE)
  refine ⟨_, h.mono_time (T' := C) (8 + 4 * M + K) (fun p => ?_)⟩
  have hn : p.1.length ≤ (encPair encBits encBits p).length := by
    simp only [length_encPair, encBits_apply]
    omega
  have hl := hzlen p
  have hc := hC p
  have hq := hQ p
  have ht := hT p
  have hs := Nat.size_le.mpr (Nat.lt_two_pow_self (n := (z p).length))
  have he := Universal.length_encNat_le (z p).length
  have hsquare : ((z p).length + 1) ^ 2 ≤
      (2 * (encPair encBits encBits p).length + 4 + E p) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hcompare : (2 * Nat.size (z p).length + 1 + E p + 1) ^ 2 ≤
      (2 * (encPair encBits encBits p).length + 4 + E p) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  simp only [Function.comp_apply, length_encPair (enc₁ := encUnary) (enc₂ := encUnary),
    encUnary_apply, List.length_replicate] at ⊢
  have hscale : (8 + 4 * M + K) * (C p + 1) =
      8 * C p + 4 * (M * C p) + K * C p + (8 + 4 * M + K) := by ring
  omega

/-- Construct all three lazy-verifier tests from a unary horizon certificate. The common
time budget covers input access and the comparison square; each test keeps its own space
witness, independently of the clock's space budget. -/
theorem exists_computableInO_lazyTests
    {H : ℕ → ℕ} {C SE : List Bool × List Bool → ℕ} {M : ℕ}
    (hE : ComputableInO (fun p : List Bool × List Bool =>
      H (2 * (unframe p.1).length + 1)) (encPair encBits encBits) encUnary C SE)
    (hC : ∀ p, (encPair encBits encBits p).length + 1 ≤ C p)
    (hQ : ∀ p, (2 * (encPair encBits encBits p).length + 4 +
      H (2 * (unframe p.1).length + 1)) ^ 2 ≤ M * C p) :
    ∃ S₀ S₁ S₂,
      ComputableInO (fun p : List Bool × List Bool => shortDesc (unframe p.1))
        (encPair encBits encBits) encBool C S₀ ∧
      ComputableInO (fun p : List Bool × List Bool =>
        decide (Nat.size (p.1.length + 1) ≤ H (2 * (unframe p.1).length + 1)))
        (encPair encBits encBits) encBool C S₁ ∧
      ComputableInO (fun p : List Bool × List Bool =>
        decide (Nat.size p.1.length ≤ H (2 * (unframe p.1).length + 1)))
        (encPair encBits encBits) encBool C S₂ := by
  have hx := ComputableInO.fst encBits encBits
  have hun : ComputableInO unframe encBits encBits (fun z => z.length) (fun z => z.length) :=
    ComputableInO.of_linear (.of_unframe fun _ => rfl)
  have hsnoc : ComputableInO (fun p : List Bool × List Bool => p.1 ++ [false])
      (encPair encBits encBits) encBits
      (fun p => (encPair encBits encBits p).length + (encPair encBits encBits p).length)
      (fun p => (encPair encBits encBits p).length + (encPair encBits encBits p).length) :=
    hx.append (ComputableInO.const (encMid := encBits) [false]) fun _ => rfl
  have hc₀ := (computableInO_shortDesc.comp (hun.comp hx)).mono_time (T' := C) 3 fun p => by
    have hu := length_unframe_le p.1
    have hn : p.1.length ≤ (encPair encBits encBits p).length := by enc_len
    have hc := hC p
    simp only [Function.comp_apply]
    omega
  obtain ⟨S₁, hc₁⟩ := exists_computableInO_sizeLength_le
    (hsnoc.mono_le (fun p => by omega) (fun p => le_rfl)) hE
    (fun p => by simp) hC hQ (K := 1) (fun p => by omega)
  obtain ⟨S₂, hc₂⟩ := exists_computableInO_sizeLength_le
    (hx.mono_le (fun p => by omega) (fun p => le_rfl)) hE
    (fun p => by omega) hC hQ (K := 1) (fun p => by omega)
  refine ⟨_, S₁, S₂, hc₀, ?_, ?_⟩
  · simpa only [List.length_append, List.length_singleton] using hc₁
  · simpa only [Function.comp_apply] using hc₂

/-- Compose the lazy verifier without replacing branch costs by their worst case.
The caller supplies three tests at cost `C`, an acceptance simulation at cost `B`, and
exhaustive search at cost `R`. Test space bounds may differ from each other and from time. -/
theorem exists_computableInO_lazyVerifier
    {β : List Bool → List Bool → ℕ} {L H : ℕ → ℕ}
    {C S₀ S₁ S₂ : List Bool × List Bool → ℕ}
    {B SB : List Bool × List Bool × List Bool → ℕ}
    {R SR : List Bool × List Bool → ℕ}
    (hacc : ComputableInO (fun q : List Bool × List Bool × List Bool =>
      lazyAccepts β q.1 q.2.1 q.2.2) (encLazyAcceptsInput) encBool B SB)
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
    have hu := length_unframe_le p.1
    have hp : p.1.length ≤ (encPair encBits encBits p).length := by
      simpa only [encBits_apply] using length_le_encPair_left encBits encBits p
    simp only [Function.comp_apply] at ⊢
    have : 7 * (C p + B (unframe (unframe p.1), p.1 ++ [false], p.2) + 1) =
        7 * C p + 7 * B (unframe (unframe p.1), p.1 ++ [false], p.2) + 7 := by ring
    omega
  have hf₂ := ComputableInO.mono_time ((ComputableInDegree.of_finite (encIn := encBool)
    (encMid := encBool) (fun b : Bool => !b)).inO_one.comp (hbrute.comp (hcode.prod hbase)))
      (T' := fun p => C p + R (unframe (unframe p.1), frame (unframe p.1))) 7
      fun p => by
    have h₁ := hC p
    have hu := length_unframe_le p.1
    have hp : p.1.length ≤ (encPair encBits encBits p).length := by
      simpa only [encBits_apply] using length_le_encPair_left encBits encBits p
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
  · simp only [decide_eq_true_eq]

end Cslib.Complexity.Diagonal
