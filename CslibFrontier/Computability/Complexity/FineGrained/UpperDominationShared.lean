/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.UpperDominationSharedBounds
public import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Native shared-marker upper-domination counting

Instantiate the actual ordinary width-three counter in the refined queries of
[ChenJiangZhu2027], Appendix D.3 (PDF p.35). Both query storage, both binary answers and subtraction
are charged. The whole execution has sharp time in original vertices and polynomial workspace
on all raw inputs, including query writing and binary reconstruction.

## Main results

* `exists_count_sharp_certificate`: complete rounded sharp-time native certificate.
* `exists_count_realEta_certificate`: source single-log-log clock and global polynomial workspace.
* `exists_count_polySpace`: the corresponding plain polynomial-workspace interface.
-/

public section

namespace Cslib.Logic.PL.UpperDomination.Unique.SharedMarkers

open Turing.MultiTapeTM Cslib.Complexity Cslib.Circuits.Frontier.IncidenceNetwork

private theorem valid_query {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℤ) (hn : 1 ≤ n) (β : Bool) :
    CNF.validDeclaredInput 3 (oldDeclaration (ofGraph G k) + n) (query (ofGraph G k) β) := by
  apply CNF.validDeclaredInput_eq_true_iff.mpr
  refine ⟨query_width _ _, ?_⟩
  intro v hv
  obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.mp (List.mem_toFinset.mp hv)
  exact Finset.mem_range.mpr (query_indices G k hn β c hc (v, b) hl)

open Classical in
private theorem execute_compile_correct {counter : ℕ × CNF ℕ → ℕ}
    (hspec : ∀ x, counter x = if CNF.validDeclaredInput 3 x.1 x.2 then
      x.2.modelCountOn (Finset.range x.1) else 0)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ) :
    TwoBoundary.BinaryFrontend.execute counter (compile (ofGraph G k)) =
      Fintype.card {S : Set (Fin n) // Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)} := by
  rw [← compile_count G k]
  by_cases hn : n = 0
  · obtain ⟨B, P, he, hb, hp, hl, _⟩ := Unique.representation G k
    have hem : P = [] := List.length_eq_zero_iff.mp (by omega)
    subst P
    have hnraw : IndependentDomination.order (graph (ofGraph G k)) = 0 := hn
    rw [compile, ite_eq_left hnraw, he]
    exact TwoBoundary.BinaryFrontend.execute_correct (b := 3) (d := 0) hspec B [] hb (by simp)
  · have hn' : 1 ≤ n := by omega
    have hnraw : IndependentDomination.order (graph (ofGraph G k)) ≠ 0 := hn
    simp only [compile, hnraw, ↓reduceIte, TwoBoundary.BinaryFrontend.execute,
      Sum.isLeft_inr, Bool.false_eq_true, TwoBoundary.BinaryFrontend.first,
      TwoBoundary.BinaryFrontend.second, TwoBoundary.BinaryFrontend.value]
    have hnval : IndependentDomination.order (graph (ofGraph G k)) = n := rfl
    rw [hspec, hspec]
    simp only [hnval, valid_query G k hn' false, valid_query G k hn' true, ↓reduceIte,
      WeightedRow.BinaryPlan.queryCount_eq_modelCountOn]


private theorem compiled_dimensions (x : Input) :
    (TwoBoundary.BinaryFrontend.first (compile x)).1 ≤
        6 * IndependentDomination.order (graph x) + auxiliary x ∧
      (TwoBoundary.BinaryFrontend.second (compile x)).1 ≤
        6 * IndependentDomination.order (graph x) + auxiliary x := by
  obtain ⟨hd, hp, hfull⟩ := layout x
  have hdecl : TwoBoundary.BinaryFrontend.declared (Unique.build x) =
      TwoBoundary.BinaryFrontend.declared (UpperDomination.build x) := rfl
  unfold compile
  split_ifs
  · have h := TwoBoundary.BinaryFrontend.dimensions (Unique.build x)
    rw [hdecl, hd, hfull] at h
    constructor <;> omega
  · simp only [TwoBoundary.BinaryFrontend.first, TwoBoundary.BinaryFrontend.second]
    simp only [oldDeclaration, hdecl, hd, hfull]
    constructor <;> omega

open Classical in
/-- The complete actual width-three execution has sharp rounded time in original vertices and
polynomial workspace on all raw inputs. Construction, selectors, dispatch, both counter calls,
answer lengths and binary reconstruction are charged by native certificates. -/
theorem exists_count_sharp_certificate :
    ∃ counter : ℕ × CNF ℕ → ℕ, ∃ count : Input → ℕ,
      ∃ cs : Cslib.GenericRAM.NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, count x = TwoBoundary.BinaryFrontend.execute counter (compile x)) ∧
      (∀ q, counter q = if CNF.validDeclaredInput 3 q.1 q.2 then
        q.2.modelCountOn (Finset.range q.1) else 0) ∧
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
        count (ofGraph G k) =
          Fintype.card {S : Set (Fin n) // Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)} ∧
        cs.time (ofGraph G k) ≤ C * ((encInput (ofGraph G k)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨β, N₀, Ncut, cp, D, hcp, hcorrect⟩ :=
    exists_countGeneralParity_sharp_certificate 3 (by decide)
  let counter := countGeneralParity 3 β N₀ Ncut
  have hcpS : PolyBounded (fun x => (TwoBoundary.BinaryFrontend.encCounter x).length) cp.space :=
    PolyBounded.of_forall_le D D fun x => (hcp x).2
  obtain ⟨ce, heS, O₀, hO₀, hceTime⟩ := TwoBoundary.BinaryFrontend.exists_execute_overhead cp hcpS
  obtain ⟨hf, ht⟩ := TwoBoundary.BinaryFrontend.selectors_polytime
  let cc := Cslib.GenericRAM.NativeCertificate.ofPolyTime compile_polytime
  have hcc := Cslib.GenericRAM.NativeCertificate.ofPolyTime_isPolynomial compile_polytime
  let cs := ce.comp cc
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space ce cc heS hcc.2
  let out := compile
  let qf (x : Input) := TwoBoundary.BinaryFrontend.first (out x)
  let qt (x : Input) := TwoBoundary.BinaryFrontend.second (out x)
  let O (x : Input) := cc.time x + O₀ (out x)
  let Bf (x : Input) := D * ((TwoBoundary.BinaryFrontend.encCounter (qf x)).length + 1) ^ D
  let Bt (x : Input) := D * ((TwoBoundary.BinaryFrontend.encCounter (qt x)).length + 1) ^ D
  let W (x : Input) := O x + Bf x + Bt x
  have hlen := compile_polytime.polyBounded_length
  have hO : PolyBounded (fun x : Input => (encInput x).length) O :=
    hcc.1.add (hO₀.comp hlen)
  have hBf : PolyBounded (fun x : Input => (encInput x).length) Bf :=
    (PolyBounded.const D).mul (((hf.polyBounded_length.comp hlen).add (.const 1)).pow D)
  have hBt : PolyBounded (fun x : Input => (encInput x).length) Bt :=
    (PolyBounded.const D).mul (((ht.polyBounded_length.comp hlen).add (.const 1)).pow D)
  let K := 2 ^ (D * (5 * Nat.logLogSqrtLogScale 2097152))
  let Z (x : Input) := K * W x + cs.space x
  have hZ : PolyBounded (fun x : Input => (encInput x).length) Z :=
    ((PolyBounded.const K).mul ((hO.add hBf).add hBt)).add hcsS
  obtain ⟨C, e, hCe⟩ := hZ.exists_le
  refine ⟨counter, TwoBoundary.BinaryFrontend.execute counter ∘ compile, cs, C, e, 38200 * D,
    fun _ => rfl, hcorrect, fun x => (Nat.le_add_left _ _).trans (hCe x), ?_⟩
  intro n G _ k
  let x := ofGraph G k
  let a := (CardinalityInterval.circuit n k.toNat n).size
  have ha : a ≤ 952 * (n + 1) := CardinalityInterval.size_circuit n k.toNat n
  have haux : auxiliary x = a := IndependentDominationInterval.auxiliary_ofGraph G k.toNat n
  have hscale (flag : Bool) : Nat.logLogSqrtLogScale
      (if flag then (qt x).1 else (qf x).1) ≤
        38200 * Nat.logLogSqrtLogScale n + 5 * Nat.logLogSqrtLogScale 2097152 := by
    have hdim : (if flag then (qt x).1 else (qf x).1) ≤ 6 * n + a := by
      have hd := compiled_dimensions x
      rw [haux] at hd
      change (qf x).1 ≤ 6 * n + a ∧ (qt x).1 ≤ 6 * n + a at hd
      cases flag <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> tauto
    by_cases hn : 1910 ≤ n
    · have hm := Nat.logLogSqrtLogScale_le_of_le
        (hdim.trans (by omega : 6 * n + a ≤ 1910 * n)) (by omega : 4 ≤ 1910 * n)
      have hl := Nat.logLogSqrtLogScale_mul_le 1910 (by omega : max 4 1910 ≤ n)
      omega
    · have hm := Nat.logLogSqrtLogScale_le_of_le
        (hdim.trans (by omega : 6 * n + a ≤ 2097152)) (by decide : 4 ≤ 2097152)
      omega
  let E := 2 ^ ((38200 * D) * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have hK : 0 < K := Nat.two_pow_pos _
  have hpow (flag : Bool) :
      2 ^ (D * Nat.logLogSqrtLogScale (if flag then (qt x).1 else (qf x).1)) ≤ K * E := by
    calc _ ≤ 2 ^ (D * (38200 * Nat.logLogSqrtLogScale n +
        5 * Nat.logLogSqrtLogScale 2097152)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left D (hscale flag))
      _ = _ := by dsimp only [K, E]; rw [Nat.mul_add, pow_add, mul_comm]; congr 1; ring
  have hfTime := (hcp (qf x)).1.trans (Nat.mul_le_mul_left (Bf x) (hpow false))
  have htTime := (hcp (qt x)).1.trans (Nat.mul_le_mul_left (Bt x) (hpow true))
  have hOTime : O x ≤ O x * (K * E) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE)
  have hraw : cs.time x ≤ W x * (K * E) := by
    have hbase := hceTime (out x)
    have hr : cs.time x ≤ O x + cp.time (qf x) + cp.time (qt x) := by
      change cc.time x + ce.time (out x) ≤ _
      dsimp only [O, qf, qt]
      omega
    calc _ ≤ O x + cp.time (qf x) + cp.time (qt x) := hr
      _ ≤ O x * (K * E) + Bf x * (K * E) + Bt x * (K * E) :=
        Nat.add_le_add (Nat.add_le_add hOTime hfTime) htTime
      _ = _ := by dsimp only [W]; ring
  constructor
  · exact execute_compile_correct hcorrect G k
  · calc cs.time x ≤ Z x * E := hraw.trans (by
          have h : K * W x ≤ Z x := Nat.le_add_right _ _
          have := Nat.mul_le_mul_right E h
          nlinarith)
      _ ≤ _ := Nat.mul_le_mul_right E (hCe x)

open Classical in
/-- The real single-log-log source clock of the complete refined counter. Rounded estimates
cover every smaller graph and all degenerate/empty cases. -/
theorem exists_count_realEta_certificate :
    ∃ counter : ℕ × CNF ℕ → ℕ, ∃ count : Input → ℕ,
      ∃ cs : Cslib.GenericRAM.NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, count x = TwoBoundary.BinaryFrontend.execute counter (compile x)) ∧
      (∀ q, counter q = if CNF.validDeclaredInput 3 q.1 q.2 then
        q.2.modelCountOn (Finset.range q.1) else 0) ∧
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
        count (ofGraph G k) =
          Fintype.card {S : Set (Fin n) // Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)} ∧
        (16 ≤ n → (cs.time (ofGraph G k) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G k)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) := by
  obtain ⟨counter, count, cs, C, e, A, hexec, hcounter, hs, h⟩ := exists_count_sharp_certificate
  refine ⟨counter, count, cs, C, e, 6 * A, hexec, hcounter, hs, ?_⟩
  intro n G _ k
  refine ⟨(h G k).1, fun hn => ?_⟩
  have ht : (cs.time (ofGraph G k) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofGraph G k)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale n) := by exact_mod_cast (h G k).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Nat.two_pow_mul_logLogSqrtLogScale_le A hn) (by positivity))

open Classical in
/-- The sharp certificate also supplies the whole-execution polynomial-workspace interface. -/
theorem exists_count_polySpace :
    ∃ count : Input → ℕ, ComputableInPolySpace count encInput encNat ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
        count (ofGraph G k) =
          Fintype.card {S : Set (Fin n) // Minimal G.IsDominatingSet S ∧ k ≤ (Nat.card S : ℤ)} := by
  obtain ⟨_, count, cs, C, e, _, _, _, hs, h⟩ := exists_count_sharp_certificate
  have hs' := PolyBounded.of_forall_le C e hs
  exact ⟨count, ComputableInPolySpace.of_inSpace hs' (ComputableInSpace.of_inO cs.computes),
    fun G _ k => (h G k).1⟩

end Cslib.Logic.PL.UpperDomination.Unique.SharedMarkers
