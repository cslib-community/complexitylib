/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundarySolver
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Source-input checked recovery with original-prefix output

Compose a certified actual constructor with the proved checked native solver and write only the
original prefix. The resource calculus charges the constructor, whole solver, retained encodings
and final option/prefix output. A proved linear bound on formula wires plus predicates absorbs
auxiliary variables into the original source parameter without adding a loglog factor.
The concrete graph applications instantiate every construction and bound.

## Main results

* `exists_source_solver_sharp_certificate`: complete original-input resource composition.
-/

public section

namespace Cslib.Logic.PL.TwoBoundary.BinaryFrontend.Witness

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Keep the original-variable prefix of a checked full word; preserve failure. -/
@[expose] def keepPrefix (p : ℕ × Output) : Output :=
  let (n, result) := p
  result.map (fun bits => bits.take n)
/-- Unary original count, framed, followed by the standard optional raw-word encoding. -/
abbrev encPrefix : (ℕ × Output) ↪ List Bool := encPair encUnary encOutput

private theorem prefix_polytime : ComputableInPolyTime keepPrefix encPrefix encOutput := by
  unfold keepPrefix encPrefix encOutput
  apply ComputableInPolyTime.optionMapWithInput (by fun_prop)
  fun_prop

open Classical in
/-- Complete checked solver for a supplied *proved polynomial constructor*. No solver/runtime
contract is a premise: the native solver is instantiated here. Concrete clients must discharge
finite erasure, widths and linear wire/predicate bounds for their actual constructor. -/
theorem exists_source_solver_sharp_certificate {α : Type} (enc : α ↪ List Bool)
    (construct : α → Input) (sourceSize : α → ℕ)
    (hg : ComputableInPolyTime construct enc encInput)
    (hn : ComputableInPolyTime sourceSize enc encUnary) (b d c : ℕ) (hb0 : 1 ≤ b) :
    ∃ solver : α → Output, ∃ cs : NativeCertificate solver enc encOutput, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((enc x).length + 1) ^ e) ∧
      ∀ (x : α) {N : ℕ} (B : CNF (Fin N)) (P : List (DNF (Fin N)))
        (_hbuild : construct x = ofFinite B P) (_hb : ∀ q ∈ B, q.length ≤ b)
        (_hp : ∀ q ∈ P, ∀ t ∈ q, t.length ≤ d)
        (_hN : sourceSize x ≤ N) (_hdim : N + P.length ≤ c * (sourceSize x + 1)),
        ((solver x).isSome = true ↔
          ∃ σ : Fin N → Bool, B.eval σ = true ∧ ∀ q ∈ P, DNF.eval σ q = true) ∧
        (∀ bits, solver x = some bits → bits.length = sourceSize x ∧
          ∃ full : List Bool, full.length = N ∧
            B.eval (fun i => full.getD i.val false) = true ∧
            (∀ q ∈ P, DNF.eval (fun i => full.getD i.val false) q = true) ∧
            bits = full.take (sourceSize x)) ∧
        cs.time x ≤ C * ((enc x).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale (sourceSize x)) := by
  obtain ⟨recover, cp, D, f, A, hs, h⟩ := exists_solver_sharp_certificate b d hb0
  let cg := NativeCertificate.ofPolyTime hg
  let cn := NativeCertificate.ofPolyTime hn
  have hcg := NativeCertificate.ofPolyTime_isPolynomial hg
  have hcn := NativeCertificate.ofPolyTime_isPolynomial hn
  let raw := cp.comp cg
  have hrawS := SparseCNFLeafCounter.polyBounded_comp_space cp cg
    (PolyBounded.of_forall_le D f hs) hcg.2
  let pair := cn.prod raw
  have hpairS : PolyBounded (fun x => (enc x).length) pair.space := hcn.2.add hrawS
  have hpairL := SparseCNFLeafCounter.polyBounded_output_of_space pair hpairS
  let cf := NativeCertificate.ofPolyTime prefix_polytime
  have hcf := NativeCertificate.ofPolyTime_isPolynomial prefix_polytime
  let cs := cf.comp pair
  have hcsS : PolyBounded (fun x => (enc x).length) cs.space :=
    hpairS.add (hcf.2.comp hpairL)
  let W (x : α) := cn.time x + cg.time x + cf.time (sourceSize x, recover (construct x)) +
    D * ((encInput (construct x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (enc x).length) W :=
    (((hcn.1.add hcg.1).add (hcf.1.comp hpairL)).add ((PolyBounded.const D).mul
      ((hg.polyBounded_length.add (.const 1)).pow f))).add hcsS
  let L := 2 * c + 4
  let H := max 4 L
  let T := L * (H + 1)
  let K := 2 ^ (A * (5 * Nat.logLogSqrtLogScale T))
  obtain ⟨C, e, hCe⟩ := ((PolyBounded.const K).mul hW).exists_le
  have hK : 0 < K := Nat.two_pow_pos _
  refine ⟨fun x => keepPrefix (sourceSize x, recover (construct x)), cs, C, e, (20 * L) * A,
    fun x => (show cs.space x ≤ W x from Nat.le_add_left _ _).trans
      ((Nat.le_mul_of_pos_left _ hK).trans (hCe x)), ?_⟩
  intro x N B P hbuild hb hp hN hdim
  obtain ⟨hyes, hword, ht⟩ := h B P hb hp
  rw [← hbuild] at hyes hword ht
  have hscale : Nat.logLogSqrtLogScale (N + P.length) ≤
      20 * L * Nat.logLogSqrtLogScale (sourceSize x) + 5 * Nat.logLogSqrtLogScale T := by
    by_cases hbig : H ≤ sourceSize x
    · have hlarge : 4 ≤ L * sourceSize x := by
        have hL : 4 ≤ L := by dsimp only [L]; omega
        have hn1 : 1 ≤ sourceSize x := by have := le_max_left 4 L; omega
        nlinarith
      have hbound : N + P.length ≤ L * sourceSize x := by
        dsimp only [L]
        have hn1 : 1 ≤ sourceSize x := by have := le_max_left 4 L; omega
        nlinarith
      have hm := Nat.logLogSqrtLogScale_le_of_le hbound hlarge
      have hl := Nat.logLogSqrtLogScale_mul_le L hbig
      nlinarith
    · have hsmall : sourceSize x ≤ H := by omega
      have hbnd : N + P.length ≤ T := by dsimp only [T, L, H] at *; nlinarith
      have ht4 : 4 ≤ T := by dsimp only [T, L]; have := le_max_left 4 L; nlinarith
      have hm := Nat.logLogSqrtLogScale_le_of_le hbnd ht4
      omega
  let E := 2 ^ (((20 * L) * A) * Nat.logLogSqrtLogScale (sourceSize x))
  have hE : 0 < E := Nat.two_pow_pos _
  have hpow : 2 ^ (A * Nat.logLogSqrtLogScale (N + P.length)) ≤ K * E := by
    calc _ ≤ 2 ^ (A * (20 * L * Nat.logLogSqrtLogScale (sourceSize x) +
          5 * Nat.logLogSqrtLogScale T)) := Nat.pow_le_pow_right (by decide)
            (Nat.mul_le_mul_left A hscale)
      _ = _ := by dsimp only [K, E]; rw [Nat.mul_add, pow_add, mul_comm]; congr 1; ring
  refine ⟨?_, ?_, ?_⟩
  · simpa [keepPrefix] using hyes
  · intro bits heq
    obtain ⟨full, hf, hbts⟩ := Option.map_eq_some_iff.mp heq
    obtain ⟨hlen, hB, hP⟩ := hword full hf
    refine ⟨?_, full, hlen, hB, hP, hbts.symm⟩
    rw [← hbts, List.length_take, hlen, Nat.min_eq_left hN]
  · have htime := ht.trans (Nat.mul_le_mul_left _ hpow)
    have hT : cs.time x = cn.time x + (cg.time x + cp.time (construct x)) +
        cf.time (sourceSize x, recover (construct x)) := rfl
    rw [hT]
    have hpre : cn.time x + cg.time x + cf.time (sourceSize x, recover (construct x)) ≤
        (cn.time x + cg.time x + cf.time (sourceSize x, recover (construct x))) * (K * E) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE)
    calc _ ≤ (cn.time x + cg.time x + cf.time (sourceSize x, recover (construct x)) +
          D * ((encInput (construct x)).length + 1) ^ f) * (K * E) := by
            rw [Nat.add_mul]
            omega
      _ ≤ W x * (K * E) := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ = K * W x * E := by ring
      _ ≤ _ := Nat.mul_le_mul_right E (hCe x)

end Cslib.Logic.PL.TwoBoundary.BinaryFrontend.Witness
