/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.ExactCover
public import CslibFrontier.Computability.Complexity.FineGrained.ExactOneCountingResources
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Native exact counting for indexed Exact Cover

Compose actual incidence-list transposition with the proved exact-one all-cases counter,
including binary result reconstruction. The exponential parameter is the number of original
indexed candidates, with no bound on universe size or incidence density. Polynomial peak
workspace includes actual input/transposed/query/result encodings. The source is
[ChenJiangZhu2027], Corollary 5.4, PDF p.18.

## Main results

* `exists_count_sharp_certificate`: actual original covers, native sharp time and global space.
* `exists_count_realEta_certificate`: unshifted real source exponent with binary count bounds.
* `exists_decision_sharp_certificate`, `exists_decision_realEta_certificate`: actual positivity
  decision with the same rounded and real source bounds.
-/

public section

namespace Cslib.Logic.PL.ExactCover

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity

/-- Every encoded original cover count has at most s+1 bits, including optional empty candidates. -/
theorem count_le_two_pow (x : Input) : count x ≤ 2 ^ size x := by
  unfold count
  calc _ ≤ Nat.card (Fin (size x) → Bool) := Nat.card_le_card_of_injective
          (fun σ => σ.val) Subtype.val_injective
    _ = _ := by simp [Nat.card_eq_fintype_card]

/-- Actual binary output size is linear in candidate count; this is separate from machine time. -/
theorem count_bits_le (x : Input) : (encNat (count x)).length ≤ size x + 1 := by
  have h := Nat.size_le_size (count_le_two_pow x)
  simpa only [encNat_apply, Nat.size_eq_bits_len, Nat.size_pow] using h

/-- The complete actual original-input counter has sharp single-loglog time and global
polynomial peak workspace. No transposed equations, rank, count or resource advice is input. -/
theorem exists_count_sharp_certificate :
    ∃ counter : Input → ℕ, ∃ cs : NativeCertificate counter encInput encNat, ∃ C e A : ℕ,
      (∀ x, counter x = count x) ∧
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ x, cs.time x ≤ C * ((encInput x).length + 1) ^ e *
        2 ^ (A * Nat.logLogSqrtLogScale (size x)) := by
  obtain ⟨counter, cp, pC, f, A, hs, h⟩ := ExactOne.BinaryPlan.exists_count_sharp_certificate
  let cg := NativeCertificate.ofPolyTime backend_polytime
  have hg := NativeCertificate.ofPolyTime_isPolynomial backend_polytime
  let cs := cp.comp cg
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp cg
    (PolyBounded.of_forall_le pC f hs) hg.2
  let W (x : Input) := cg.time x +
    pC * ((ExactOne.BinaryPlan.encInput (backend x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hg.1.add ((PolyBounded.const pC).mul
      ((backend_polytime.polyBounded_length.add (.const 1)).pow f))).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  have hpoint (x : Input) := h ([] : CNF (Fin (size x))) (finiteRows x)
    (by simp) (finiteRows_width x) (scopes x) (fun _ _ => true) (finiteRows_perm x)
  have hcount (x : Input) : counter (backend x) = count x := by
    have hc := (hpoint x).1
    rw [← backend_eq x] at hc
    exact hc.trans (sourceCount_eq_count x)
  have htime (x : Input) : cp.time (backend x) ≤
      pC * ((ExactOne.BinaryPlan.encInput (backend x)).length + 1) ^ f *
        2 ^ (A * Nat.logLogSqrtLogScale (size x)) := by
    have ht := (hpoint x).2
    simpa only [← backend_eq x] using ht
  refine ⟨counter ∘ backend, cs, C, e, A, hcount, fun x => ?_, fun x => ?_⟩
  · exact (show cs.space x ≤ W x from Nat.le_add_left _ _).trans (hCe x)
  · have hE : 1 ≤ 2 ^ (A * Nat.logLogSqrtLogScale (size x)) := Nat.one_le_two_pow
    have hT : cs.time x = cg.time x + cp.time (backend x) := rfl
    rw [hT]
    have hgT : cg.time x ≤ cg.time x * 2 ^ (A * Nat.logLogSqrtLogScale (size x)) :=
      Nat.le_mul_of_pos_right _ (by positivity)
    calc _ ≤ (cg.time x + pC * ((ExactOne.BinaryPlan.encInput (backend x)).length + 1) ^ f) *
          2 ^ (A * Nat.logLogSqrtLogScale (size x)) := by nlinarith [htime x]
      _ ≤ W x * 2 ^ (A * Nat.logLogSqrtLogScale (size x)) := by
        exact Nat.mul_le_mul_right _ (show _ ≤ W x from Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hCe x)

/-- Corollary 5.4 with the exact unshifted real eta(s), beyond s>=16. Correct counts and
polynomial space hold at every size, including no candidates and an empty universe. -/
theorem exists_count_realEta_certificate :
    ∃ counter : Input → ℕ, ∃ cs : NativeCertificate counter encInput encNat, ∃ C e A : ℕ,
      (∀ x, counter x = count x) ∧
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      (∀ x, (encNat (counter x)).length ≤ size x + 1) ∧
      ∀ x, 16 ≤ size x → (cs.time x : ℝ) ≤
        (C : ℝ) * ((encInput x).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale (size x)) := by
  obtain ⟨counter, cs, C, e, A, hc, hs, ht⟩ := exists_count_sharp_certificate
  refine ⟨counter, cs, C, e, 6 * A, hc, hs, ?_, ?_⟩
  · intro x
    rw [hc]
    exact count_bits_le x
  · intro x hn
    have hR : (cs.time x : ℝ) ≤
        (C : ℝ) * ((encInput x).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale (size x)) := by exact_mod_cast ht x
    exact hR.trans (mul_le_mul_of_nonneg_left
      (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

/-- Positive original count is exactly existence of an original indexed cover. -/
theorem count_pos_iff (x : Input) : 0 < count x ↔ ∃ σ, IsCover x σ := by
  unfold count
  rw [Nat.card_pos_iff]
  constructor
  · rintro ⟨h, _⟩
    exact nonempty_subtype.mp h
  · intro h
    exact ⟨nonempty_subtype.mpr h, inferInstance⟩

/-- The actual positivity test is composed with the proved counter, retaining polynomial
workspace and the candidate-parameter sharp clock; no decision/count oracle is assumed. -/
theorem exists_decision_sharp_certificate :
    ∃ decideCover : Input → Bool, ∃ cs : NativeCertificate decideCover encInput encBool,
      ∃ C e A : ℕ,
        (∀ x, decideCover x = true ↔ ∃ σ, IsCover x σ) ∧
        (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
        ∀ x, cs.time x ≤ C * ((encInput x).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale (size x)) := by
  obtain ⟨counter, cp, pC, f, A, hc, hs, ht⟩ := exists_count_sharp_certificate
  have hp : ComputableInPolyTime (fun n : ℕ => decide (0 < n)) encNat encBool := by
    exact .of_tidy (ComputableTidilyInPolyTime.binary_lt.comp
      ((ComputableTidilyInPolyTime.const 0).prod
        (ComputableTidilyInPolyTime.id' (encIn := encNat))))
  let cz := NativeCertificate.ofPolyTime hp
  have hz := NativeCertificate.ofPolyTime_isPolynomial hp
  let cs := cz.comp cp
  have hcpS : PolyBounded (fun x => (encInput x).length) cp.space :=
    PolyBounded.of_forall_le pC f hs
  have hlen := SparseCNFLeafCounter.polyBounded_output_of_space cp hcpS
  have hcsS : PolyBounded (fun x => (encInput x).length) cs.space :=
    hcpS.add (hz.2.comp hlen)
  let W (x : Input) := pC * ((encInput x).length + 1) ^ f + cz.time (counter x) + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    ((PolyBounded.const pC).mul ((PolyBounded.self.add (.const 1)).pow f)).add
      (hz.1.comp hlen) |>.add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨(fun x => decide (0 < counter x)), cs, C, e, A, ?_, ?_, ?_⟩
  · intro x
    simp only [decide_eq_true_eq, hc, count_pos_iff]
  · intro x
    exact (Nat.le_add_left _ _).trans (hCe x)
  · intro x
    have hT : cs.time x = cp.time x + cz.time (counter x) := rfl
    rw [hT]
    have hE : 1 ≤ 2 ^ (A * Nat.logLogSqrtLogScale (size x)) := Nat.one_le_two_pow
    calc _ ≤ W x * 2 ^ (A * Nat.logLogSqrtLogScale (size x)) := by
            dsimp only [W]
            nlinarith [ht x]
      _ ≤ _ := Nat.mul_le_mul_right _ (hCe x)

/-- The original decision endpoint with the same unshifted real source exponent eta(s). -/
theorem exists_decision_realEta_certificate :
    ∃ decideCover : Input → Bool, ∃ cs : NativeCertificate decideCover encInput encBool,
      ∃ C e A : ℕ,
        (∀ x, decideCover x = true ↔ ∃ σ, IsCover x σ) ∧
        (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
        ∀ x, 16 ≤ size x → (cs.time x : ℝ) ≤
          (C : ℝ) * ((encInput x).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale (size x)) := by
  obtain ⟨decision, cs, C, e, A, hc, hs, ht⟩ := exists_decision_sharp_certificate
  refine ⟨decision, cs, C, e, 6 * A, hc, hs, ?_⟩
  intro x hn
  have hR : (cs.time x : ℝ) ≤ (C : ℝ) * ((encInput x).length + 1 : ℕ) ^ e *
      (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale (size x)) := by exact_mod_cast ht x
  exact hR.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.ExactCover
