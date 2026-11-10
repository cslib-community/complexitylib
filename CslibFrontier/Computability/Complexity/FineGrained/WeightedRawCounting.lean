/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.WeightedRaggedResources
import CslibFrontier.Computability.GenericRAM.Native.MachineBounds
import CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Total-decoder admission and a finite-machine weighted counting endpoint

Unlike the canonical parser, this alternative interprets every word by the existing total decoder,
then checks the decoded declaration, positive weights and normalized demands. It accepts decoder
aliases; it does not assert that malformed frames are canonical encodings. Both policies agree on
canonical encodings. Original declared but unused variables are counted in either policy.
The declaration remains explicit unary, and no succinct-declaration transfer is asserted.

## Main definitions

* `runDecoded`: decode before the actual structural/demand-admitting counter.

## Main results

* `exists_countDecoded_sharp_certificate`: actual total-decoder counter and charged resources.
* `exists_countDecoded_machine`: one finite binary Turing machine, exact decoded counts, sharp
  transition time, polynomial work-tape space and polynomial encoded-output length.
* `exists_countDecoded_machine_realEta`: the same machine with the source real clock.

## References

[ChenJiangZhu2027], Section 3 conventions (PDF p.10), Theorem 7.1 (PDF pp.23–24).
-/

public section
namespace Cslib.Logic.PL.WeightedRow.BinaryRagged
open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Every word denotes its total decoding; admission is performed by the supplied counter. -/
@[expose] def runDecoded (counter : Input → ℕ) (w : List Bool) : ℕ :=
  counter (decoder.decode w)

/-- Compose the actual decoder and admitting counter, without a canonicality or runtime premise. -/
theorem exists_countDecoded_sharp_certificate (d : ℕ) :
    ∃ count : List Bool → ℕ, ∃ cs : NativeCertificate count encBits encNat, ∃ C e A : ℕ,
      (∀ w, cs.space w ≤ C * (w.length + 1) ^ e) ∧
      (∀ w, cs.time w ≤ C * (w.length + 1) ^ e *
        2 ^ (A * Nat.logLogSqrtLogScale (decoder.decode w).1)) ∧
      (∀ w, count w = if admit d (decoder.decode w) then
        Fintype.card {σ // Holds (decoder.decode w) σ} else 0) ∧
      (∀ x, admit d x = true → count (encInput x) = Fintype.card {σ // Holds x σ}) := by
  obtain ⟨counter, cp, C, e, A, hs, ht, hc, hz⟩ := exists_count_sharp_certificate d
  let pre := NativeCertificate.ofPolyTime decoder.computableInPolyTime
  have hp := NativeCertificate.ofPolyTime_isPolynomial decoder.computableInPolyTime
  let cs := cp.comp pre
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp pre
    (PolyBounded.of_forall_le C e hs) hp.2
  let W (w : List Bool) := pre.time w +
    C * ((encInput (decoder.decode w)).length + 1) ^ e + cs.space w
  have hW : PolyBounded List.length W :=
    (hp.1.add ((PolyBounded.const C).mul
      ((decoder.computableInPolyTime.polyBounded_length.add (.const 1)).pow e))).add hcsS
  obtain ⟨B, f, hBf⟩ := hW.exists_le
  refine ⟨runDecoded counter, cs, B, f, A,
    fun w => (Nat.le_add_left _ _).trans (hBf w), ?_, ?_, ?_⟩
  · intro w
    let E := 2 ^ (A * Nat.logLogSqrtLogScale (decoder.decode w).1)
    have hE : 0 < E := Nat.two_pow_pos _
    have ht' : cp.time (decoder.decode w) ≤
        C * ((encInput (decoder.decode w)).length + 1) ^ e * E := ht _
    change pre.time w + cp.time (decoder.decode w) ≤ _
    calc _ ≤ (pre.time w + C * ((encInput (decoder.decode w)).length + 1) ^ e) * E := by
          have := Nat.le_mul_of_pos_right (pre.time w) hE
          nlinarith only [ht', this]
      _ ≤ W w * E := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hBf w)
  · intro w
    by_cases hw : admit d (decoder.decode w) = true
    · simpa only [runDecoded, hw, ↓reduceIte] using hc _ hw
    · simpa only [runDecoded, hw, Bool.false_eq_true, ↓reduceIte] using
        hz _ (Bool.eq_false_iff.mpr hw)
  · intro x hx
    simpa only [runDecoded, decoder.decode_enc] using hc x hx

/-- Unpack the actual certificate into transition-level finite-machine semantics. Constants absorb
only fixed multiplicative/additive factors; neither clock nor machine is advice. -/
theorem exists_countDecoded_machine (d : ℕ) :
    ∃ (count : List Bool → ℕ) (C e A k : ℕ) (State : Type) (_ : Finite State)
      (tm : Turing.MultiTapeTM k Bool State),
      (∀ w, tm.ComputesInTimeAndSpace (encBits w) (encNat (count w))
        (C * (w.length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale (decoder.decode w).1))
        (C * (w.length + 1) ^ e)) ∧
      (∀ w, (encNat (count w)).length ≤ C * (w.length + 1) ^ e) ∧
      (∀ w, count w = if admit d (decoder.decode w) then
        Fintype.card {σ // Holds (decoder.decode w) σ} else 0) := by
  obtain ⟨count, cs, C, e, A, hs, ht, hc, _⟩ := exists_countDecoded_sharp_certificate d
  obtain ⟨B, k, State, hfinite, tm, hm, hl⟩ := cs.exists_sharp_machine C e A
    (fun w => Nat.logLogSqrtLogScale (decoder.decode w).1) hs ht
  exact ⟨count, B, e, A, k, State, hfinite, tm, hm, hl, hc⟩

/-- The same finite machine has the source real eta time, retaining global polynomial workspace
and output length even below the real-clock cutoff. -/
theorem exists_countDecoded_machine_realEta (d : ℕ) :
    ∃ (count : List Bool → ℕ) (C e A k : ℕ) (State : Type) (_ : Finite State)
      (tm : Turing.MultiTapeTM k Bool State),
      (∀ w, ∃ t, tm.ComputesInTimeAndSpace (encBits w) (encNat (count w)) t
        (C * (w.length + 1) ^ e) ∧
        (16 ≤ (decoder.decode w).1 → (t : ℝ) ≤ (C : ℝ) * (w.length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale (decoder.decode w).1))) ∧
      (∀ w, (encNat (count w)).length ≤ C * (w.length + 1) ^ e) ∧
      (∀ w, count w = if admit d (decoder.decode w) then
        Fintype.card {σ // Holds (decoder.decode w) σ} else 0) := by
  obtain ⟨count, C, e, A, k, State, hfinite, tm, ht, hl, hc⟩ := exists_countDecoded_machine d
  refine ⟨count, C, e, 6 * A, k, State, hfinite, tm, ?_, hl, hc⟩
  intro w
  refine ⟨_, ht w, fun hn => ?_⟩
  have h := Nat.two_pow_mul_logLogSqrtLogScale_le A hn
  push_cast at h ⊢
  exact mul_le_mul_of_nonneg_left h (by positivity)

end Cslib.Logic.PL.WeightedRow.BinaryRagged
