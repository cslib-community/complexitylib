/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CNF.WeightedRagged
public import Complexity.Computability.Complexity.FineGrained.WeightedCountingResources
import all Complexity.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Actual counting resources for admitted ragged weighted equations

Compose binary structural/demand admission and safe index conversion with the actual weighted
constructor and general-density counter. Every row keeps its own length, including zero. The
algorithm returns zero on rejected inputs. The declaration is unary; indices, coefficients and
signed targets are binary. Time includes admission, conversion, counting and binary output;
workspace is polynomial on all inputs. This is the counting/reduction portion of
[ChenJiangZhu2027], Section 7.1, Theorem 7.1 (PDF pp. 23–24), for the explicit nonsuccinct
encoding below, with constants depending on fixed demand bound `d`. It is not a table or graph
frontend. Rounded time covers all declared sizes; real eta is stated from size 16.
-/

public section

namespace Cslib.Logic.PL.WeightedRow.BinaryRagged

open Cslib.Complexity Cslib.GenericRAM Turing.MultiTapeTM

/-- Guard the actual counter using computed admission, before invoking its unary-index backend. -/
@[expose] def run (counter : Input → ℕ) (d : ℕ) (x : Input) : ℕ :=
  if admit d x then counter (recode x) else 0

/-- A single actual ragged-input algorithm, with exact original assignment count, sharp rounded
eta time and global polynomial workspace. All certificates and constants are constructed. -/
theorem exists_count_sharp_certificate (d : ℕ) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat,
    ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      (∀ x, cs.time x ≤ C * ((encInput x).length + 1) ^ e *
        2 ^ (A * Nat.logLogSqrtLogScale x.1)) ∧
      (∀ x, admit d x = true → count x = Fintype.card {σ // Holds x σ}) ∧
      (∀ x, admit d x = false → count x = 0) := by
  obtain ⟨counter, cp, D, f, A, hspace, hcounter⟩ :=
    BinaryPlan.exists_count_sharp_certificate d
  let hr := recode_polytime
  let cr := NativeCertificate.ofPolyTime hr
  have hcr := NativeCertificate.ofPolyTime_isPolynomial hr
  let ca := NativeCertificate.ofPolyTime (admit_polytime d)
  have hca := NativeCertificate.ofPolyTime_isPolynomial (admit_polytime d)
  let hz : ComputableInPolyTime (fun _ : Input => (0 : ℕ)) encInput encNat := .const 0
  let cz := NativeCertificate.ofPolyTime hz
  have hcz := NativeCertificate.ofPolyTime_isPolynomial hz
  let cc := cp.comp cr
  let cs : NativeCertificate (run counter d) encInput encNat :=
    NativeCertificate.branch ca cc cz
  have hcp : PolyBounded (fun x => (encLegacy x).length) cp.space :=
    PolyBounded.of_forall_le D f hspace
  have hcc := SparseCNFLeafCounter.polyBounded_comp_space cp cr hcp hcr.2
  have hs : PolyBounded (fun x => (encInput x).length) cs.space :=
    ((hca.2.add hcc).add hcz.2).mono fun x => by
      change ca.space x + (if admit d x then cc.space x else cz.space x) ≤
        ca.space x + cc.space x + cz.space x
      split_ifs <;> omega
  let B (x : Input) := D * ((encLegacy (recode x)).length + 1) ^ f
  have hB : PolyBounded (fun x => (encInput x).length) B :=
    (PolyBounded.const D).mul ((hr.polyBounded_length.add (.const 1)).pow f)
  let W (x : Input) := ca.time x + cr.time x + cz.time x + B x + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (((hca.1.add hcr.1).add hcz.1).add hB).add hs
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  have hcorrect {x : Input} (hx : admit d x = true) :
      counter (recode x) = Fintype.card {σ // Holds x σ} ∧
      cp.time (recode x) ≤ B x * 2 ^ (A * Nat.logLogSqrtLogScale x.1) := by
    obtain ⟨t, m, R, hrows, hd, hsem⟩ := admitted_refinement hx
    have ha : shape x = true ∧ bounded d (recode x) = true := by
      simpa only [admit, Bool.and_eq_true] using hx
    have heq : (x.1, (List.finRange t).map fun j => BinaryNormalization.ofOccurrences (R j)) =
        recode x := by
      rw [recode_eq ((shape_iff x).mp ha.1)]
      exact Prod.ext rfl hrows.symm
    have hc := hcounter R hd
    rw [heq] at hc
    refine ⟨hc.1.trans ?_, hc.2⟩
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun σ => (hsem σ).symm)
  refine ⟨run counter d, cs, C, e, A, fun x => ?_, fun x => ?_, ?_, ?_⟩
  · exact (by dsimp only [W]; omega : cs.space x ≤ W x).trans (hCe x)
  · let E := 2 ^ (A * Nat.logLogSqrtLogScale x.1)
    have hE : 0 < E := Nat.two_pow_pos _
    have ht : cs.time x ≤ W x * E := by
      change ca.time x + (if admit d x then cr.time x + cp.time (recode x)
        else cz.time x) ≤ _
      by_cases hx : admit d x = true
      · simp only [hx, ↓reduceIte]
        have hc := (hcorrect hx).2
        have hw : ca.time x + cr.time x + B x ≤ W x := by dsimp only [W]; omega
        have hmul := Nat.mul_le_mul_right E hw
        have hpoly := Nat.le_mul_of_pos_right (ca.time x + cr.time x) hE
        dsimp only [E] at hmul hpoly ⊢
        nlinarith
      · simp only [hx, Bool.false_eq_true, ↓reduceIte]
        exact (by dsimp only [W]; omega : ca.time x + cz.time x ≤ W x).trans
          (Nat.le_mul_of_pos_right _ hE)
    exact ht.trans (Nat.mul_le_mul_right E (hCe x))
  · intro x hx
    simpa only [run, hx, ↓reduceIte] using (hcorrect hx).1
  · intro x hx
    simp [run, hx]

/-- Canonical binary words are parsed and admitted before counting; malformed words return zero. -/
@[expose] def runWords (counter : Input → ℕ) (w : List Bool) : ℕ :=
  if canonical w then counter (decoder.decode w) else 0

/-- Complete framed-word algorithm, charging parsing, canonicality, admission, normalization,
construction, native counting and output. Its rounded eta depends on the decoded declaration;
canonical encodings retain exactly the original declaration and equations. -/
theorem exists_countWords_sharp_certificate (d : ℕ) :
    ∃ count : List Bool → ℕ, ∃ cs : NativeCertificate count encBits encNat,
    ∃ C e A : ℕ,
      (∀ w, cs.space w ≤ C * (w.length + 1) ^ e) ∧
      (∀ w, cs.time w ≤ C * (w.length + 1) ^ e *
        2 ^ (A * Nat.logLogSqrtLogScale (decoder.decode w).1)) ∧
      (∀ x, admit d x = true → count (encInput x) = Fintype.card {σ // Holds x σ}) ∧
      (∀ w, canonical w = false → count w = 0) ∧
      (∀ x, admit d x = false → count (encInput x) = 0) := by
  obtain ⟨counter, cp, D, f, A, hspace, htime, hcorrect, hreject⟩ :=
    exists_count_sharp_certificate d
  let hr := decoder.computableInPolyTime
  let cr := NativeCertificate.ofPolyTime hr
  have hcr := NativeCertificate.ofPolyTime_isPolynomial hr
  let ca := NativeCertificate.ofPolyTime canonical_polytime
  have hca := NativeCertificate.ofPolyTime_isPolynomial canonical_polytime
  let hz : ComputableInPolyTime (fun _ : List Bool => (0 : ℕ)) encBits encNat := .const 0
  let cz := NativeCertificate.ofPolyTime hz
  have hcz := NativeCertificate.ofPolyTime_isPolynomial hz
  let cc := cp.comp cr
  let cs : NativeCertificate (runWords counter) encBits encNat :=
    NativeCertificate.branch ca cc cz
  have hcp : PolyBounded (fun x => (encInput x).length) cp.space :=
    PolyBounded.of_forall_le D f hspace
  have hcc := SparseCNFLeafCounter.polyBounded_comp_space cp cr hcp hcr.2
  have hs : PolyBounded (fun w : List Bool => w.length) cs.space :=
    ((hca.2.add hcc).add hcz.2).mono fun w => by
      change ca.space w + (if canonical w then cc.space w else cz.space w) ≤
        ca.space w + cc.space w + cz.space w
      split_ifs <;> omega
  let B (w : List Bool) := D * ((encInput (decoder.decode w)).length + 1) ^ f
  have hB : PolyBounded (fun w : List Bool => w.length) B :=
    (PolyBounded.const D).mul ((hr.polyBounded_length.add (.const 1)).pow f)
  let W (w : List Bool) := ca.time w + cr.time w + cz.time w + B w + cs.space w
  have hW : PolyBounded (fun w : List Bool => w.length) W :=
    (((hca.1.add hcr.1).add hcz.1).add hB).add hs
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨runWords counter, cs, C, e, A, fun w => ?_, fun w => ?_, ?_, ?_, ?_⟩
  · exact (by dsimp only [W]; omega : cs.space w ≤ W w).trans (hCe w)
  · let E := 2 ^ (A * Nat.logLogSqrtLogScale (decoder.decode w).1)
    have hE : 0 < E := Nat.two_pow_pos _
    have ht : cs.time w ≤ W w * E := by
      change ca.time w + (if canonical w then cr.time w + cp.time (decoder.decode w)
        else cz.time w) ≤ _
      by_cases hw : canonical w = true
      · simp only [hw, ↓reduceIte]
        have hc := htime (decoder.decode w)
        have hb : ca.time w + cr.time w + B w ≤ W w := by dsimp only [W]; omega
        have hmul := Nat.mul_le_mul_right E hb
        have hpoly := Nat.le_mul_of_pos_right (ca.time w + cr.time w) hE
        dsimp only [B, E] at hmul hpoly ⊢
        nlinarith
      · simp only [hw, Bool.false_eq_true, ↓reduceIte]
        exact (by dsimp only [W]; omega : ca.time w + cz.time w ≤ W w).trans
          (Nat.le_mul_of_pos_right _ hE)
    exact ht.trans (Nat.mul_le_mul_right E (hCe w))
  · intro x hx
    simpa only [runWords, canonical, decoder.decode_enc, decide_true, ↓reduceIte] using
      hcorrect x hx
  · intro w hw
    simp [runWords, hw]
  · intro x hx
    simpa only [runWords, canonical, decoder.decode_enc, decide_true, ↓reduceIte] using
      hreject x hx

/-- Source eta (natural real logarithms) for the actual original-word algorithm, with polynomial
workspace at every size. The cutoff only avoids the singular small arguments of real eta. -/
theorem exists_countWords_real_sharp_certificate (d : ℕ) :
    ∃ count : List Bool → ℕ, ∃ cs : NativeCertificate count encBits encNat,
    ∃ C e A : ℕ,
      (∀ w, cs.space w ≤ C * (w.length + 1) ^ e) ∧
      ∀ x, admit d x = true →
        count (encInput x) = Fintype.card {σ // Holds x σ} ∧
        (16 ≤ x.1 → (cs.time (encInput x) : ℝ) ≤
          (C : ℝ) * ((encInput x).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale x.1)) := by
  obtain ⟨count, cs, C, e, A, hs, ht, hc, _⟩ := exists_countWords_sharp_certificate d
  refine ⟨count, cs, C, e, 6 * A, hs, fun x hx => ⟨hc x hx, fun hn => ?_⟩⟩
  have h := ht (encInput x)
  rw [decoder.decode_enc] at h
  have htR : (cs.time (encInput x) : ℝ) ≤
      (C : ℝ) * ((encInput x).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale x.1) := by exact_mod_cast h
  exact htR.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.WeightedRow.BinaryRagged
