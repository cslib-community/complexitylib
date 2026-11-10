/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.WeightedComparisonCounting
public import CslibFrontier.Computability.PolyTime.CNF.PartitionSizeVectors
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists
import CslibFrontier.Computability.Complexity.FineGrained.DegreePartitionDistribution
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Actual complete joint polynomial-weight distributions

Generate every ordered weight vector, invoke the proved actual augmented counter, and retain
all vector tags/counts including zeros. Original predicates and annotation multiplicity remain
unchanged. Fixed family size and exponent give polynomially many sequential calls; the native
list-map theorem charges retained output prefixes and every call. Source:
[ChenJiangZhu2027], Corollary A.2, PDF p.29.

## Main results

* `exists_distribution_sharp_certificate`: actual full output, exact counts, native time and space.
* `grid_coverage`, `grid_nodup`, `output_length`: exact ordered-bin coverage and length.
* `output_bits_le`, `exists_distribution_realEta_certificate`: full output and real η bounds.
* `query_count`: one or two ordinary queries per bin, rather than for the entire table.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum.Distribution

open Turing.MultiTapeTM Cslib.GenericRAM Cslib.Complexity Logic.PL
open DegreePartition

/-- Original CNF/DNF counting frame and binary coefficient/polarity rows; no target advice. -/
abbrev Input := TwoBoundary.BinaryFrontend.Input × List (List (ℕ × Bool))
/-- The unchanged original counting instance. -/
@[expose] def original (x : Input) := x.1
/-- Runtime coefficient/polarity data, one row per fixed comparison label. -/
@[expose] def rows (x : Input) := x.2
/-- Shared original variable declaration, including unused/zero-weight bits. -/
@[expose] def declared (x : Input) := TwoBoundary.BinaryFrontend.declared (original x)
/-- Full original binary frame with the original unary declaration. -/
abbrev encInput := encPair TwoBoundary.BinaryFrontend.encInput
  (encList (encList (encPair encNat encBool)))
/-- Actual coefficient upper bound for every original assignment under the source promise. -/
@[expose] def upper (c : ℕ) (x : Input) : ℕ := declared x ^ (c + 1)
/-- Actual complete fixed-dimensional grid, first coordinate slowest, with zeros retained. -/
@[expose] def grid (r c : ℕ) (x : Input) := SizeVectors.vectors r (upper c x)
/-- Original data and one actual generated weight vector. -/
abbrev Case := Input × List ℕ
/-- Original frame for one coefficient request. -/
@[expose] def data (p : Case) := p.1
/-- Actual vector, with no claimed feasibility or supplied count. -/
@[expose] def vector (p : Case) := p.2
/-- Original frame paired with the framed binary weight vector. -/
abbrev encCase := encPair encInput (encList encNat)
/-- Actual exact-target input, with targets derived from the generated vector. -/
@[expose] def request (p : Case) : WithBase.Input :=
  (original (data p), (rows (data p), (vector p).map (fun k : ℕ => (k : ℤ))))
/-- A tagged vector/coefficient entry; vector order retains original comparison labels. -/
abbrev Entry := List ℕ × ℕ
/-- Framed binary vector tag followed by binary original-assignment count. -/
abbrev encEntry := encPair (encList encNat) encNat
/-- Actual output-tag writing after the coefficient call. -/
@[expose] def attach (p : Case × ℕ) : Entry := let (q, answer) := p; (vector q, answer)
/-- Actual original-input coefficient request and tagged output. -/
@[expose] def coefficient (count : WithBase.Input → ℕ) (p : Case) : Entry :=
  attach (p, count (request p))
/-- Complete actual joint-distribution traversal and output. -/
@[expose] def run (r c : ℕ) (count : WithBase.Input → ℕ) (x : Input) : List Entry :=
  (grid r c x).map (fun v => coefficient count (x, v))
/-- Canonical source formulas and shared original weighted literals, without target inputs. -/
@[expose] def ofData {n r : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool) : Input :=
  (TwoBoundary.BinaryFrontend.ofFinite B P,
    Family.rows (Family.ofData weights positive (fun _ => 0)))
/-- Conventional original-assignment coefficient; it is a specification, not the runtime oracle. -/
@[expose] noncomputable def countForVector {n r : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool) (v : List ℕ) : ℕ :=
  Nat.card {x : Fin n → Bool //
    (∀ j, value (weights j) (positive j) x = v.getD j.val 0) ∧
      B.eval x = true ∧ ∀ p ∈ P, DNF.eval x p = true}

private theorem grid_polytime (r c : ℕ) :
    ComputableInPolyTime (grid r c) encInput (encList (encList encNat)) := by
  have hn : ComputableInPolyTime declared encInput encUnary := by
    unfold declared original encInput TwoBoundary.BinaryFrontend.encInput
      TwoBoundary.BinaryFrontend.declared
    fun_prop
  exact (SizeVectors.vectors_polytime r).comp ((ComputableInPolyTime.unary_pow (c + 1)).comp hn)

private theorem request_polytime :
    ComputableInPolyTime request encCase WithBase.encInput := by
  have ht : ComputableInPolyTime (fun v : List ℕ => v.map (fun k : ℕ => (k : ℤ)))
      (encList encNat) (encList encIntBin) := ComputableInPolyTime.intBin_natCast.map
  unfold request original rows data vector encCase encInput WithBase.encInput
  fun_prop

private theorem attach_polytime :
    ComputableInPolyTime attach (encPair encCase encNat) encEntry := by
  unfold attach vector encEntry encCase
  fun_prop

/-- The actual complete grid has polynomially many entries for each fixed r and c. -/
theorem grid_length (r c : ℕ) (x : Input) : (grid r c x).length = (declared x ^ (c + 1) + 1) ^ r :=
  SizeVectors.length_vectors _ _

/-- Every labeled weight vector occurs exactly once, including impossible/zero-count bins. -/
theorem grid_coverage (r c : ℕ) (x : Input) (v : List ℕ) :
    v ∈ grid r c x ↔ v.length = r ∧ ∀ k ∈ v, k ≤ declared x ^ (c + 1) :=
  SizeVectors.mem_vectors _ _ _

private theorem request_ofData {n r : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool) (v : List ℕ)
    (hv : v.length = r) : request (ofData B P weights positive, v) =
      WithBase.ofData B P weights positive (fun j => (v.getD j.val 0 : ℤ)) := by
  have hvec : List.ofFn (fun j : Fin r => v.getD j.val 0) = v := by
    subst r
    have he : (fun j : Fin v.length => v.getD j.val 0) = fun j : Fin v.length => v[j.val] := by
      funext j
      exact List.getD_eq_getElem v 0 j.isLt
    rw [he]
    exact List.ofFn_getElem
  change (TwoBoundary.BinaryFrontend.ofFinite B P,
    (Family.rows (Family.ofData weights positive (fun _ => 0)), v.map (fun k : ℕ => (k : ℤ)))) = _
  dsimp only [WithBase.ofData, Family.rows, Family.targets, Family.ofData]
  congr 2
  calc v.map (fun k : ℕ => (k : ℤ)) =
      (List.ofFn (fun j : Fin r => v.getD j.val 0)).map (fun k : ℕ => (k : ℤ)) :=
        congrArg (List.map (fun k : ℕ => (k : ℤ))) hvec.symm
    _ = _ := by simp only [List.map_ofFn, Function.comp_def]

open Classical in
/-- Complete actual joint output, exact original coefficients, rounded single-loglog native time
and global polynomial peak workspace. The actual counter is instantiated, not assumed. -/
theorem exists_distribution_sharp_certificate (r b d c : ℕ) :
    ∃ distribution : Input → List Entry,
      ∃ cs : NativeCertificate distribution encInput (encList encEntry), ∃ C e A : ℕ,
        (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
        ∀ {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
          (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool)
          (_hw : ∀ j i, weights j i ≤ n ^ c)
          (_hb : ∀ clause ∈ B, clause.length ≤ b) (_hp : ∀ p ∈ P, ∀ t ∈ p, t.length ≤ d),
          distribution (ofData B P weights positive) =
            (SizeVectors.vectors r (n ^ (c + 1))).map
              (fun v => (v, countForVector B P weights positive v)) ∧
          cs.time (ofData B P weights positive) ≤
            C * ((encInput (ofData B P weights positive)).length + 1) ^ e *
              2 ^ (A * Nat.logLogSqrtLogScale (n + P.length)) := by
  obtain ⟨counter, cp, pC, f, A, hs, ht⟩ :=
    WithBase.exists_count_sharp_certificate (fun _ : Fin r => .eq) b d c
  let cq := NativeCertificate.ofPolyTime request_polytime
  have hq := NativeCertificate.ofPolyTime_isPolynomial request_polytime
  let cn := cp.comp cq
  have hnS := SparseCNFLeafCounter.polyBounded_comp_space cp cq
    (PolyBounded.of_forall_le pC f hs) hq.2
  let ci : NativeCertificate (fun p : Case => p) encCase encCase :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let pair := ci.prod cn
  have hpairS : PolyBounded (fun p => (encCase p).length) pair.space :=
    PolyBounded.self.add hnS
  have hpairL := SparseCNFLeafCounter.polyBounded_output_of_space pair hpairS
  let tag := NativeCertificate.ofPolyTime attach_polytime
  have htag := NativeCertificate.ofPolyTime_isPolynomial attach_polytime
  let cc : NativeCertificate (coefficient counter) encCase encEntry :=
    (tag.comp pair).congr fun _ => rfl
  have hccS := SparseCNFLeafCounter.polyBounded_comp_space tag pair htag.2 hpairS
  have hccL := SparseCNFLeafCounter.polyBounded_output_of_space cc hccS
  let identity : NativeCertificate (fun x : Input => x) encInput encInput :=
    NativeCertificate.linear (ComputableInO.of_eq fun _ => rfl)
  let cg := NativeCertificate.ofPolyTime (grid_polytime r c)
  have hg := NativeCertificate.ofPolyTime_isPolynomial (grid_polytime r c)
  let cs : NativeCertificate (run r c counter) encInput (encList encEntry) :=
    ⟨_, _, ComputableInO.mapWith cc.computes identity.computes cg.computes⟩
  let L (x : Input) := (encInput x).length
  let G (x : Input) := (encList (encList encNat) (grid r c x)).length
  let N (x : Input) := (grid r c x).length
  let U (x : Input) := 2 * L x + G x + 1
  have hG : PolyBounded L G := (grid_polytime r c).polyBounded_length
  have hN : PolyBounded L N := hG.mono fun x => length_le_length_encList _ _
  have hU : PolyBounded L U := ((PolyBounded.const 2).mul .self).add hG |>.add (PolyBounded.const 1)
  have hcase (x : Input) (v : List ℕ) (hv : v ∈ grid r c x) :
      (encCase (x, v)).length ≤ U x := by
    have h := length_le_encList_of_mem (encList encNat) hv
    have he : (encCase (x, v)).length =
        2 * (encInput x).length + 1 + (encList encNat v).length := length_encPair (x, v)
    rw [he]
    dsimp only [U, L, G]
    omega
  obtain ⟨cL, eL, hLb⟩ := hccL.exists_le
  obtain ⟨cS, eS, hSb⟩ := hccS.exists_le
  let V (x : Input) := cL * (U x + 1) ^ eL
  let S (x : Input) := cS * (U x + 1) ^ eS
  have hV : PolyBounded L V := (PolyBounded.const cL).mul ((hU.add (PolyBounded.const 1)).pow eL)
  have hS : PolyBounded L S := (PolyBounded.const cS).mul ((hU.add (PolyBounded.const 1)).pow eS)
  have hval (x : Input) (v : List ℕ) (hv : v ∈ grid r c x) :
      (encEntry (coefficient counter (x, v))).length ≤ V x :=
    (hLb _).trans (Nat.mul_le_mul_left cL
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hcase x v hv) 1) eL))
  have hmaxS (x : Input) : listMax (fun v => cc.space (x, v)) (grid r c x) ≤ S x := by
    apply listMax_le
    intro v hv
    exact (hSb _).trans (Nat.mul_le_mul_left cS
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hcase x v hv) 1) eS))
  let O (x : Input) := N x * (2 * V x + 1)
  have hO : PolyBounded L O := hN.mul (((PolyBounded.const 2).mul hV).add (PolyBounded.const 1))
  have hout (x : Input) : (encList encEntry (run r c counter x)).length ≤ O x := by
    have h := length_encList_le encEntry (run r c counter x) (b := V x) (by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
      exact hval x v hv)
    simpa only [run, List.length_map] using h
  let F (p : Case) := (encCase p).length + cq.time p +
    tag.time (p, counter (request p)) + pC * ((WithBase.encInput (request p)).length + 1) ^ f
  have hF : PolyBounded (fun p => (encCase p).length) F :=
    ((PolyBounded.self.add hq.1).add (htag.1.comp hpairL)).add
      ((PolyBounded.const pC).mul
        ((request_polytime.polyBounded_length.add (PolyBounded.const 1)).pow f))
  obtain ⟨cF, eF, hFb⟩ := hF.exists_le
  let M (x : Input) := cF * (U x + 1) ^ eF
  have hM : PolyBounded L M := (PolyBounded.const cF).mul ((hU.add (PolyBounded.const 1)).pow eF)
  let SP (x : Input) := L x + identity.space x + cg.space x + L x + G x + O x + S x
  have hSP : PolyBounded L SP :=
    (((((PolyBounded.self.add .self).add hg.2).add .self).add hG).add hO).add hS
  have hspace (x : Input) : cs.space x ≤ SP x := by
    change L x + identity.space x + cg.space x + L x + G x +
      (encList encEntry (run r c counter x)).length +
        listMax (fun v => cc.space (x, v)) (grid r c x) ≤ _
    dsimp only [SP]
    exact Nat.add_le_add (Nat.add_le_add_left (hout x) _) (hmaxS x)
  let W (x : Input) := L x + identity.time x + cg.time x +
    (N x + 1) * (L x + G x + O x + M x) + SP x
  have hW : PolyBounded L W :=
    (((PolyBounded.self.add .self).add hg.1).add
      ((hN.add (PolyBounded.const 1)).mul (((PolyBounded.self.add hG).add hO).add hM))).add hSP
  obtain ⟨C, e, hCe⟩ := hW.exists_le
  refine ⟨run r c counter, cs, C, e, A, fun x => ?_, ?_⟩
  · exact (hspace x).trans ((Nat.le_add_left _ _).trans (hCe x))
  intro n B P weights positive hw hb hp
  let x := ofData B P weights positive
  let E := 2 ^ (A * Nat.logLogSqrtLogScale (n + P.length))
  have hE : 0 < E := Nat.two_pow_pos _
  have hpoint (v : List ℕ) (hv : v ∈ grid r c x) :
      counter (request (x, v)) = countForVector B P weights positive v ∧
      cp.time (request (x, v)) ≤
        pC * ((WithBase.encInput (request (x, v))).length + 1) ^ f * E := by
    have hvlen := (grid_coverage r c x v).mp hv |>.1
    have h := ht B P weights positive (fun j => (v.getD j.val 0 : ℤ)) hw hb hp
    rw [← request_ofData B P weights positive v hvlen] at h
    simpa only [countForVector, ← Nat.card_eq_fintype_card, Comparison.Holds, Nat.cast_inj] using h
  constructor
  · change (grid r c x).map (fun v => coefficient counter (x, v)) = _
    apply List.map_congr_left
    intro v hv
    exact Prod.ext rfl (hpoint v hv).1
  · have hmaxT : listMax (fun v => cc.time (x, v)) (grid r c x) ≤ M x * E := by
      apply listMax_le
      intro v hv
      have hpT := (hpoint v hv).2
      have hother := Nat.le_mul_of_pos_right
        ((encCase (x, v)).length + cq.time (x, v) + tag.time ((x, v), counter (request (x, v)))) hE
      have ht : cc.time (x, v) ≤ F (x, v) * E := by
        change (encCase (x, v)).length + (cq.time (x, v) + cp.time (request (x, v))) +
          tag.time ((x, v), counter (request (x, v))) ≤ _
        dsimp only [F]
        rw [Nat.add_mul]
        nlinarith
      have hf := (hFb (x, v)).trans (Nat.mul_le_mul_left cF
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hcase x v hv) 1) eF))
      exact ht.trans (Nat.mul_le_mul_right E hf)
    have ht : cs.time x ≤ W x * E := by
      change L x + identity.time x + cg.time x + (N x + 1) *
        (L x + G x + (encList encEntry (run r c counter x)).length +
          listMax (fun v => cc.time (x, v)) (grid r c x)) ≤ _
      have ho := Nat.le_mul_of_pos_right (L x + G x + O x) hE
      have hh := Nat.add_le_add (Nat.add_le_add_left (hout x) (L x + G x)) hmaxT
      have hm := Nat.mul_le_mul_left (N x + 1) hh
      have ha := Nat.le_mul_of_pos_right (L x + identity.time x + cg.time x) hE
      dsimp only [W]
      nlinarith
    exact ht.trans (Nat.mul_le_mul_right E (hCe x))

/-- Exactly one output entry for each actual generated bin, in the grid's labeled order. -/
theorem output_length (r c : ℕ) (counter : WithBase.Input → ℕ) (x : Input) :
    (run r c counter x).length = (declared x ^ (c + 1) + 1) ^ r := by
  rw [run, List.length_map, grid_length]

/-- No vector tags are duplicated by the actual traversal. -/
theorem grid_nodup (r c : ℕ) (x : Input) : (grid r c x).Nodup :=
  SizeVectors.nodup_vectors _ _

open Classical in
/-- Each coefficient counts original Boolean assignments, not extra test-gate choices. -/
theorem coefficient_le_two_pow {n r : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool) (v : List ℕ) :
    countForVector B P weights positive v ≤ 2 ^ n := by
  unfold countForVector
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype_le _).trans_eq (by simp)

/-- Explicit framed binary output size, including every vector tag and every zero coefficient.
It is independent of, and does not substitute for, the actual machine-time proof above. -/
theorem output_bits_le {n r : ℕ} (c : ℕ) (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool) :
    (encList encEntry ((SizeVectors.vectors r (n ^ (c + 1))).map
      (fun v => (v, countForVector B P weights positive v)))).length ≤
      (n ^ (c + 1) + 1) ^ r *
        (2 * (2 * r * (2 * (n ^ (c + 1) + 1) + 1) + n + 2) + 1) := by
  have h := length_encList_le encEntry
    ((SizeVectors.vectors r (n ^ (c + 1))).map
      (fun v => (v, countForVector B P weights positive v)))
    (b := 2 * r * (2 * (n ^ (c + 1) + 1) + 1) + n + 2) (by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
      have hvB := DegreePartition.Distribution.vector_bits_le v hv
      have hb : (encNat (countForVector B P weights positive v)).length ≤ n + 1 := by
        have hs := Nat.size_le_size (coefficient_le_two_pow B P weights positive v)
        simpa only [encNat_apply, Nat.size_eq_bits_len, Nat.size_pow] using hs
      simp only [encEntry, length_encPair]
      nlinarith)
  simpa only [List.length_map, SizeVectors.length_vectors] using h

/-- Every assignment's actual weight vector lies in the complete generated grid. -/
theorem attainable_vector_mem {n r : ℕ} (c : ℕ) (weights : Fin r → Fin n → ℕ)
    (positive : Fin r → Fin n → Bool) (x : Fin n → Bool)
    (hw : ∀ j i, weights j i ≤ n ^ c) :
    (List.ofFn fun j => value (weights j) (positive j) x) ∈
      SizeVectors.vectors r (n ^ (c + 1)) := by
  apply (SizeVectors.mem_vectors _ _ _).mpr
  refine ⟨List.length_ofFn, ?_⟩
  intro k hk
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hk
  unfold value
  calc _ ≤ ∑ _ : Fin n, n ^ c := Finset.sum_le_sum fun i _ => by
          have hb : (literal (positive j i) (x i)).toNat ≤ 1 := by
            cases literal (positive j i) (x i) <;> decide
          nlinarith [hw j i]
    _ = _ := by simp [pow_succ, Nat.mul_comm]

open Classical in
/-- The complete actual output has the unshifted real source exponent, exact tagged coefficients,
explicit framed output bound and global polynomial peak workspace. -/
theorem exists_distribution_realEta_certificate (r b d c : ℕ) :
    ∃ distribution : Input → List Entry,
      ∃ cs : NativeCertificate distribution encInput (encList encEntry), ∃ C e A : ℕ,
        (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
        ∀ {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
          (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool)
          (_hw : ∀ j i, weights j i ≤ n ^ c)
          (_hb : ∀ clause ∈ B, clause.length ≤ b) (_hp : ∀ p ∈ P, ∀ t ∈ p, t.length ≤ d),
          distribution (ofData B P weights positive) =
            (SizeVectors.vectors r (n ^ (c + 1))).map
              (fun v => (v, countForVector B P weights positive v)) ∧
          (encList encEntry (distribution (ofData B P weights positive))).length ≤
            (n ^ (c + 1) + 1) ^ r *
              (2 * (2 * r * (2 * (n ^ (c + 1) + 1) + 1) + n + 2) + 1) ∧
          (16 ≤ n + P.length → (cs.time (ofData B P weights positive) : ℝ) ≤
            (C : ℝ) * ((encInput (ofData B P weights positive)).length + 1 : ℕ) ^ e *
              (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale (n + P.length))) := by
  obtain ⟨dist, cs, C, e, A, hs, h⟩ := exists_distribution_sharp_certificate r b d c
  refine ⟨dist, cs, C, e, 6 * A, hs, ?_⟩
  intro n B P weights positive hw hb hp
  have ht := h B P weights positive hw hb hp
  refine ⟨ht.1, ?_, fun hn => ?_⟩
  · rw [ht.1]
    exact output_bits_le c B P weights positive
  · have hR : (cs.time (ofData B P weights positive) : ℝ) ≤
        (C : ℝ) * ((encInput (ofData B P weights positive)).length + 1 : ℕ) ^ e *
          (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale (n + P.length)) := by exact_mod_cast ht.2
    exact hR.trans (mul_le_mul_of_nonneg_left
      (by simpa only [Nat.cast_add] using Nat.two_pow_mul_logLogSqrtLogScale_le A hn)
      (by positivity))

/-- Actual ordinary query trace of all generated coefficient requests, in output-bin order. -/
@[expose] def queries (r c : ℕ) (x : Input) : List (ℕ × CNF ℕ) :=
  (grid r c x).flatMap fun v => TwoBoundary.BinaryFrontend.queries
    (TwoBoundary.BinaryFrontend.compile
      (WithBase.build (fun _ : Fin r => .eq) c (request (x, v))))

/-- One ordinary query per bin without original predicates, two otherwise; full distributions
use polynomially many pairs, rather than claiming two queries for the whole table. -/
theorem query_count (r c : ℕ) (x : Input) :
    (queries r c x).length = (declared x ^ (c + 1) + 1) ^ r *
      (if (TwoBoundary.BinaryFrontend.conditions (original x)).isEmpty then 1 else 2) := by
  unfold queries
  simp only [List.length_flatMap]
  simp_rw [TwoBoundary.BinaryFrontend.compile_query_count]
  have hc (v : List ℕ) : TwoBoundary.BinaryFrontend.conditions
      (WithBase.build (fun _ : Fin r => .eq) c (request (x, v))) =
      TwoBoundary.BinaryFrontend.conditions (original x) := rfl
  simp_rw [hc]
  simp [grid_length, Function.const_def]

end Cslib.Circuits.Boolean.WeightedSum.Distribution
