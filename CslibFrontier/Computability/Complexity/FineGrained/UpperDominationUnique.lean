/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.UpperDominationUnique
public import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Exact original-set upper-domination counting with sharp native resources

Instantiate the actual width-four CNF counter in the augmented unique-mark writer. Every minimal
dominating set of the required signed input size has exactly one mark/gate extension. This is the
exact-count clause of [ChenJiangZhu2027], Proposition 7.6 / Appendix D.3 (PDF pp.27,35), not the
previous nonunique marking count or the separate width-three path-marker refinement.

## Main results

* `exists_count_sharp_certificate`: complete exact original-set counter with rounded sharp time.
* `exists_count_realEta_certificate`: the real source eta bound and global polynomial workspace.
-/

public section

namespace Cslib.Logic.PL.UpperDomination.Unique

open Turing.MultiTapeTM Cslib.Complexity Cslib.GenericRAM

open Classical in
/-- One actual augmented unique-mark graph counter has global polynomial workspace and sharp
rounded time in original vertices, uniformly over the signed binary input threshold. -/
theorem exists_count_sharp_certificate :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
        count (ofGraph G k) =
          Fintype.card {S : Set (Fin n) // Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)} ∧
        cs.time (ofGraph G k) ≤ C * ((encInput (ofGraph G k)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨counter, cp, D, f, A, hs, h⟩ :=
    TwoBoundary.BinaryFrontend.exists_count_sharp_certificate 3 2
  let cc := NativeCertificate.ofPolyTime build_polytime
  have hcc := NativeCertificate.ofPolyTime_isPolynomial build_polytime
  let cs := cp.comp cc
  have hcpS : PolyBounded
      (fun x => (TwoBoundary.BinaryFrontend.encInput x).length) cp.space :=
    PolyBounded.of_forall_le D f hs
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp cc hcpS hcc.2
  let W (x : Input) := cc.time x +
    D * ((TwoBoundary.BinaryFrontend.encInput (build x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encInput x).length) W :=
    (hcc.1.add ((PolyBounded.const D).mul
      ((build_polytime.polyBounded_length.add (.const 1)).pow f))).add hcsS
  let K := 2 ^ (A * (5 * Nat.logLogSqrtLogScale 2097152))
  obtain ⟨C, e, hCe⟩ := ((PolyBounded.const K).mul hW).exists_le
  have hK : 0 < K := Nat.two_pow_pos _
  refine ⟨counter ∘ build, cs, C, e, 38120 * A, fun x => ?_, ?_⟩
  · exact (show cs.space x ≤ W x from Nat.le_add_left _ _).trans
      ((Nat.le_mul_of_pos_left _ hK).trans (hCe x))
  intro n G _ k
  obtain ⟨B, P, hbuild, hb, hp, hplen, hcount⟩ := representation G k
  obtain ⟨hc, ht⟩ := h B P hb hp
  let a := (CardinalityInterval.circuit n k.toNat n).size
  have ha : a ≤ 952 * (n + 1) := CardinalityInterval.size_circuit n k.toNat n
  have htime : cp.time (build (ofGraph G k)) ≤
      D * ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G k))).length + 1) ^ f *
        2 ^ (A * Nat.logLogSqrtLogScale (5 * n + a)) := by
    rw [← hbuild, hplen] at ht
    have hh : (n + (CardinalityInterval.circuit n k.toNat n).size + n) + 3 * n =
        5 * n + a := by dsimp only [a]; omega
    simpa only [hh] using ht
  have hscale : Nat.logLogSqrtLogScale (5 * n + a) ≤
      38120 * Nat.logLogSqrtLogScale n + 5 * Nat.logLogSqrtLogScale 2097152 := by
    by_cases hn : 1906 ≤ n
    · have hdim : 5 * n + a ≤ 1906 * n := by omega
      have hm := Nat.logLogSqrtLogScale_le_of_le hdim (by omega : 4 ≤ 1906 * n)
      have hl := Nat.logLogSqrtLogScale_mul_le 1906 (by omega : max 4 1906 ≤ n)
      omega
    · have hm := Nat.logLogSqrtLogScale_le_of_le
        (by omega : 5 * n + a ≤ 2097152) (by decide : 4 ≤ 2097152)
      omega
  let E := 2 ^ ((38120 * A) * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have hpow : 2 ^ (A * Nat.logLogSqrtLogScale (5 * n + a)) ≤ K * E := by
    calc _ ≤ 2 ^ (A * (38120 * Nat.logLogSqrtLogScale n +
        5 * Nat.logLogSqrtLogScale 2097152)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left A hscale)
      _ = _ := by dsimp only [K, E]; rw [Nat.mul_add, pow_add, mul_comm]; congr 1; ring
  constructor
  · change counter (build (ofGraph G k)) = _
    rw [hbuild, hc, hcount]
  · change cc.time (ofGraph G k) + cp.time (build (ofGraph G k)) ≤ _
    calc
      _ ≤ (cc.time (ofGraph G k) +
          D * ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G k))).length + 1) ^ f) *
            (K * E) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add
          (Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE))
          (htime.trans (Nat.mul_le_mul_left _ hpow))
      _ ≤ K * W (ofGraph G k) * E := by
        have hm := Nat.mul_le_mul_right (K * E)
          (show cc.time (ofGraph G k) + D *
            ((TwoBoundary.BinaryFrontend.encInput (build (ofGraph G k))).length + 1) ^ f ≤
              W (ofGraph G k) from Nat.le_add_right _ _)
        nlinarith
      _ ≤ _ := Nat.mul_le_mul_right E (hCe _)

open Classical in
/-- The real single-log-log source exponent, including actual binary-bound construction and
count reconstruction. Rounded bounds cover all smaller graphs and degenerate intervals. -/
theorem exists_count_realEta_certificate :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
        count (ofGraph G k) =
          Fintype.card {S : Set (Fin n) // Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)} ∧
        (16 ≤ n → (cs.time (ofGraph G k) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G k)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_sharp_certificate
  refine ⟨count, cs, C, e, 6 * A, hs, ?_⟩
  intro n G _ k
  refine ⟨(h G k).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G k) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G k)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G k).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

end Cslib.Logic.PL.UpperDomination.Unique
