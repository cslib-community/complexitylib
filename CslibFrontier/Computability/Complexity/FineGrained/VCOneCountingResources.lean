/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.VCOneDispatch
public import CslibFrontier.Computability.Complexity.FineGrained.ExactOneCountingResources
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Complete binary resource composition for VC-one table counting

The actual original table payload determines closure, separators, aligned equations, binary
elimination, direct candidates, query writing, sequential native counting and binary reconstruction.
The declaration and widths are unary, literal table rows are explicit, and scope columns are binary.
Individual scopes are injective and local tables have VC dimension at most one; global scopes may
arbitrarily overlap. The global space bound covers malformed inputs too, while correctness/time
use this precise source promise. This proves the table endpoint of [ChenJiangZhu2027], Theorem 6.3
(PDF pp. 20–21), with `L` the complete framed input bit length. Graph applications remain separate.
-/

public section

namespace Cslib.Logic.PL.VCOne.BinaryFrontend

open Cslib.Complexity Cslib.GenericRAM Turing.MultiTapeTM

open Classical in
/-- An actual original-input table counter has exact declared counts, polynomial global workspace
and single-log-log rounded exponential time. No constructor/counter/resource advice is assumed. -/
theorem exists_count_sharp_certificate :
    ∃ count : (ℕ × List Table) → ℕ,
    ∃ cs : NativeCertificate count encTablePayload encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encTablePayload x).length + 1) ^ e) ∧
      ∀ {r m : ℕ} (w : Fin m → ℕ) (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
        (R : (i : Fin m) → Finset (Fin (w i) → Bool)) (_hR : ∀ i, DimensionOne (R i)),
        let x := tablePayload w scope R
        count x = Fintype.card {σ : Fin r → Bool // Satisfies w scope R σ} ∧
          cs.time x ≤ C * ((encTablePayload x).length + 1) ^ e *
            2 ^ (A * Nat.logLogSqrtLogScale r) := by
  classical
  obtain ⟨counter, cp, D, f, A, hspace, hcounter⟩ :=
    ExactOne.BinaryPlan.exists_count_sharp_certificate
  let arg (x : ℕ × List Table) : ExactOne.BinaryPlan.Input := (x.1, payload x)
  have harg : ComputableInPolyTime arg encTablePayload ExactOne.BinaryPlan.encInput := by
    have hn : ComputableInPolyTime (fun x : ℕ × List Table => x.1)
        encTablePayload encUnary := by unfold encTablePayload; fun_prop
    exact hn.prod payload_polytime
  let cc := NativeCertificate.ofPolyTime harg
  have hcc := NativeCertificate.ofPolyTime_isPolynomial harg
  let cs := cp.comp cc
  have hcpS : PolyBounded (fun x => (ExactOne.BinaryPlan.encInput x).length) cp.space :=
    PolyBounded.of_forall_le D f hspace
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space cp cc hcpS hcc.2
  let W (x : ℕ × List Table) := cc.time x +
    D * ((ExactOne.BinaryPlan.encInput (arg x)).length + 1) ^ f + cs.space x
  have hW : PolyBounded (fun x => (encTablePayload x).length) W :=
    (hcc.1.add ((PolyBounded.const D).mul
      ((harg.polyBounded_length.add (.const 1)).pow f))).add hcsS
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨counter ∘ arg, cs, C, e, A, fun x => (by
    dsimp only [W] at hCe
    exact (Nat.le_add_left _ _).trans (hCe x)), ?_⟩
  intro r m w scope R hR
  obtain ⟨E, hE, S, p, hp⟩ := payload_presentation w scope R hR
  let B : CNF (Fin r) := (listedSide w scope R).dedup
  have hB : B.relabel Fin.val = (payload (tablePayload w scope R)).1 :=
    (payload_side w scope R).symm
  have hb : ∀ c ∈ B, c.length ≤ 2 := by
    intro c hc
    obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hc)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    simpa only [Clause.relabel, List.length_map] using binary_width (R i) a ha
  have he : ∀ c ∈ E, c.length ≤ r := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.get_of_mem hc
    rw [(hp i).length_eq]
    simpa only [ExactOne.signedClause, List.length_map, Finset.length_sort,
      Fintype.card_fin] using (S i).card_le_univ
  let x := tablePayload w scope R
  have hpair : arg x = (r, (B.relabel Fin.val, E.relabel Fin.val)) := by
    dsimp only [arg, x]
    change (r, payload (tablePayload w scope R)) = _
    rw [hB, hE]
  obtain ⟨hc, ht⟩ := hcounter B E hb he S p hp
  constructor
  · change counter (arg x) = _
    rw [hpair, hc, ← ExactOne.BinaryPlan.compile_count_of_perm B E S p hp]
    have ht := compile_count w scope R hR
    change WeightedRow.BinaryPlan.Output.count
      (ExactOne.BinaryPlan.compile (arg x)) = _ at ht
    rwa [hpair] at ht
  · change cc.time x + cp.time (arg x) ≤ _
    have htime : cp.time (arg x) ≤
        D * ((ExactOne.BinaryPlan.encInput (arg x)).length + 1) ^ f *
          2 ^ (A * Nat.logLogSqrtLogScale r) := by simpa only [hpair] using ht
    have hpos : 0 < 2 ^ (A * Nat.logLogSqrtLogScale r) := Nat.two_pow_pos _
    calc
      _ ≤ (cc.time x + D * ((ExactOne.BinaryPlan.encInput (arg x)).length + 1) ^ f) *
          2 ^ (A * Nat.logLogSqrtLogScale r) := by
        rw [Nat.add_mul]
        exact Nat.add_le_add (Nat.le_mul_of_pos_right _ hpos) htime
      _ ≤ W x * 2 ^ (A * Nat.logLogSqrtLogScale r) :=
        Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      _ ≤ _ := Nat.mul_le_mul_right _ (hCe x)

open Classical in
/-- Real source eta bound `r log log r / sqrt (log r)` for the actual original table counter.
The asymptotic statement starts at sixteen declared variables; smaller cases are covered by the
rounded theorem, with all zero/one/empty/direct branches retained. -/
theorem exists_count_realEta_certificate :
    ∃ count : (ℕ × List Table) → ℕ,
    ∃ cs : NativeCertificate count encTablePayload encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encTablePayload x).length + 1) ^ e) ∧
      ∀ {r m : ℕ} (w : Fin m → ℕ) (scope : (i : Fin m) → Fin (w i) ↪ Fin r)
        (R : (i : Fin m) → Finset (Fin (w i) → Bool)) (_hR : ∀ i, DimensionOne (R i)),
        count (tablePayload w scope R) =
          Fintype.card {σ : Fin r → Bool // Satisfies w scope R σ} ∧
        (16 ≤ r → let x := tablePayload w scope R
          (cs.time x : ℝ) ≤ (C : ℝ) * ((encTablePayload x).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale r)) := by
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_sharp_certificate
  refine ⟨count, cs, C, e, 6 * A, hs, ?_⟩
  intro r m w scope R hR
  refine ⟨(h w scope R hR).1, fun hr => ?_⟩
  have ht : (cs.time (tablePayload w scope R) : ℝ) ≤ (C : ℝ) *
      ((encTablePayload (tablePayload w scope R)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale r) := by
    exact_mod_cast (h w scope R hR).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hr) (by positivity))

end Cslib.Logic.PL.VCOne.BinaryFrontend
