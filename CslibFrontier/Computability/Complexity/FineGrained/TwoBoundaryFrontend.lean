/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.TwoBoundaryFrontend
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceGeneralResources
public import CslibFrontier.Computability.Complexity.FineGrained.WeightedCountingPlan
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter

/-!
# Complete sharp resources for the original explicit DNF frontend

Instantiate the proved general-density fixed-width native counter in the actual Theorem 1.1
constructor. Empty condition lists make one counting call; nonempty lists make two sequential
calls and a binary subtraction. Construction, query copies, output lengths and peak workspace
are charged. The exponent depends on original declaration plus number of conditions, without
assuming that this number is linear in the declaration. See [ChenJiangZhu2027], PDF pp. 4–5.
-/

public section

namespace Cslib.Logic.PL.TwoBoundary.BinaryFrontend

open Turing.MultiTapeTM Cslib.Complexity Cslib.GenericRAM
open Cslib.Circuits.Frontier.IncidenceNetwork
open VCOne

/-- The first actual query, on either output branch. -/
@[expose] def first : Output → ℕ × CNF ℕ
  | .inl q => q
  | .inr (N, qf, _) => (N, qf)
/-- The second query; its fallback is never counted in the one-query branch. -/
@[expose] def second : Output → ℕ × CNF ℕ
  | .inl _ => (0, [])
  | .inr (N, _, qt) => (N, qt)
/-- Count the actual emitted queries and reconstruct, making only one call for no conditions. -/
@[expose] def execute (counter : ℕ × CNF ℕ → ℕ) (o : Output) : ℕ :=
  if o.isLeft then counter (first o) else counter (first o) - counter (second o)

private abbrev encCounter := encPair encUnary encCNF

private theorem selectors_polytime :
    ComputableInPolyTime first encOutput encCounter ∧
      ComputableInPolyTime second encOutput encCounter := by
  let el := encPair encUnary encSignedCNF
  let er := encPair encUnary (encPair encSignedCNF encSignedCNF)
  have hgetL := (ComputableInO.getLeft?_deg el er).computableInPolyTime
  have hl := (ComputableInDegree.getD (enc₁ := el) (0, [])).computableInPolyTime.comp hgetL
  have hgetR := (ComputableInO.getRight?_deg el er).computableInPolyTime
  have hr := (ComputableInDegree.getD (enc₁ := er) (0, [], [])).computableInPolyTime.comp hgetR
  have htag := (ComputableInO.isLeft_deg el er).computableInPolyTime
  constructor
  · exact (htag.ite' hl (hr.fst'.prod hr.snd'.fst')).of_enc_eq fun o => by
      cases o <;> rfl
  · exact (htag.ite' (.const (0, [])) (hr.fst'.prod hr.snd'.snd')).of_enc_eq fun o => by
      cases o <;> rfl

private theorem dimensions (x : Input) :
    (first (compile x)).1 ≤ declared x + (conditions x).length ∧
      (second (compile x)).1 ≤ declared x + (conditions x).length := by
  unfold compile
  split_ifs <;> simp only [first, second] <;> omega

private theorem valid_queries {n b d : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (hb : ∀ c ∈ B, c.length ≤ b) (hp : ∀ p ∈ P, ∀ t ∈ p, t.length ≤ d)
    (N : ℕ) (q : CNF ℕ) (hq : (N, q) ∈ queries (compile (ofFinite B P))) :
    CNF.validDeclaredInput (max b (d + 2)) N q = true := by
  have h := compile_budget B P hb hp N q hq
  apply CNF.validDeclaredInput_eq_true_iff.mpr
  refine ⟨fun c hc => (h.2.2 c hc).1, ?_⟩
  intro v hv
  obtain ⟨c, hc, s, hs⟩ := CNF.mem_vars.mp (List.mem_toFinset.mp hv)
  exact Finset.mem_range.mpr ((h.2.2 c hc).2 (v, s) hs)

private theorem execute_correct {b d : ℕ} {counter : ℕ × CNF ℕ → ℕ}
    (hcounter : ∀ x, counter x = if CNF.validDeclaredInput (max b (d + 2)) x.1 x.2 then
      x.2.modelCountOn (Finset.range x.1) else 0)
    {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
    (hb : ∀ c ∈ B, c.length ≤ b) (hp : ∀ p ∈ P, ∀ t ∈ p, t.length ≤ d) :
    execute counter (compile (ofFinite B P)) = value (compile (ofFinite B P)) := by
  generalize he : compile (ofFinite B P) = o
  cases o with
  | inl q =>
    rcases q with ⟨N, q⟩
    have hq := valid_queries B P hb hp N q (by rw [he]; simp [queries])
    simp only [execute, Sum.isLeft_inl, ↓reduceIte, first, value, hcounter, hq]
    exact (WeightedRow.BinaryPlan.queryCount_eq_modelCountOn N q).symm
  | inr q =>
    rcases q with ⟨N, qf, qt⟩
    have hf := valid_queries B P hb hp N qf (by rw [he]; simp [queries])
    have ht := valid_queries B P hb hp N qt (by rw [he]; simp [queries])
    simp only [execute, Sum.isLeft_inr, Bool.false_eq_true, ↓reduceIte, first, second,
      value, hcounter, hf, ht]
    rw [WeightedRow.BinaryPlan.queryCount_eq_modelCountOn,
      WeightedRow.BinaryPlan.queryCount_eq_modelCountOn]

/-- One actual original-input counter, global polynomial space, and sharp time for every fixed
side/term width. The exponent parameter is `n + number of conditions`, not silently `n`. -/
theorem exists_count_sharp_certificate (b d : ℕ) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
        (_hb : ∀ c ∈ B, c.length ≤ b) (_hp : ∀ p ∈ P, ∀ t ∈ p, t.length ≤ d),
        count (ofFinite B P) =
          Fintype.card {σ : Fin n → Bool // B.eval σ = true ∧ ∀ p ∈ P, DNF.eval σ p = true} ∧
        cs.time (ofFinite B P) ≤ C * ((encInput (ofFinite B P)).length + 1) ^ e *
          2 ^ (A * Nat.logLogSqrtLogScale (n + P.length)) := by
  obtain ⟨β, N₀, Ncut, cp, D, hcp, hcorrect⟩ :=
    exists_countGeneralParity_sharp_certificate (max b (d + 2)) (by omega)
  let counter := countGeneralParity (max b (d + 2)) β N₀ Ncut
  have hcpS : PolyBounded (fun x => (encCounter x).length) cp.space :=
    PolyBounded.of_forall_le D D fun x => (hcp x).2
  obtain ⟨hf, ht⟩ := selectors_polytime
  let sf := NativeCertificate.ofPolyTime hf
  let st := NativeCertificate.ofPolyTime ht
  have hsf := NativeCertificate.ofPolyTime_isPolynomial hf
  have hst := NativeCertificate.ofPolyTime_isPolynomial ht
  let cf := cp.comp sf
  let ct := cp.comp st
  have hsF := SparseCNFLeafCounter.polyBounded_comp_space cp sf hcpS hsf.2
  have hsT := SparseCNFLeafCounter.polyBounded_comp_space cp st hcpS hst.2
  let both := cf.prod ct
  have hsBoth := SparseCNFLeafCounter.polyBounded_prod_space cf ct hsF hsT
  let sub := NativeCertificate.ofPolyTime ComputableInPolyTime.binary_sub
  have hsub := NativeCertificate.ofPolyTime_isPolynomial ComputableInPolyTime.binary_sub
  let reconstruct := sub.comp both
  have hsRec := SparseCNFLeafCounter.polyBounded_comp_space sub both hsub.2 hsBoth
  let htag := (ComputableInO.isLeft_deg (encPair encUnary encSignedCNF)
    (encPair encUnary (encPair encSignedCNF encSignedCNF))).computableInPolyTime
  let tag := NativeCertificate.ofPolyTime htag
  have htagP := NativeCertificate.ofPolyTime_isPolynomial htag
  let ce : NativeCertificate (execute counter) encOutput encNat :=
    (NativeCertificate.branch tag cf reconstruct).congr fun _ => rfl
  have heS : PolyBounded (fun p => (encOutput p).length) ce.space :=
    ((htagP.2.add hsF).add hsRec).mono fun p => by
      change tag.space p + (if p.isLeft then cf.space p else reconstruct.space p) ≤
        tag.space p + cf.space p + reconstruct.space p
      split_ifs <;> omega
  let cc := NativeCertificate.ofPolyTime compile_polytime
  have hcc := NativeCertificate.ofPolyTime_isPolynomial compile_polytime
  let cs := ce.comp cc
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space ce cc heS hcc.2
  let out := compile
  let qf (x : Input) := first (out x)
  let qt (x : Input) := second (out x)
  let O (x : Input) := cc.time x + tag.time (out x) + sf.time (out x) + st.time (out x) +
    sub.time (counter (qf x), counter (qt x))
  let Bf (x : Input) := D * ((encCounter (qf x)).length + 1) ^ D
  let Bt (x : Input) := D * ((encCounter (qt x)).length + 1) ^ D
  let W (x : Input) := O x + Bf x + Bt x
  have hlen := compile_polytime.polyBounded_length
  have hpost := hsub.1.comp (SparseCNFLeafCounter.polyBounded_output_of_space both hsBoth)
  have hO : PolyBounded (fun x : Input => (encInput x).length) O :=
    (((hcc.1.add (htagP.1.comp hlen)).add (hsf.1.comp hlen)).add
      (hst.1.comp hlen)).add (hpost.comp hlen)
  have hBf : PolyBounded (fun x : Input => (encInput x).length) Bf :=
    (PolyBounded.const D).mul (((hf.polyBounded_length.comp hlen).add (.const 1)).pow D)
  have hBt : PolyBounded (fun x : Input => (encInput x).length) Bt :=
    (PolyBounded.const D).mul (((ht.polyBounded_length.comp hlen).add (.const 1)).pow D)
  let K := 2 ^ (D * (5 * Nat.logLogSqrtLogScale 32))
  let Z (x : Input) := K * W x + cs.space x
  have hZ : PolyBounded (fun x : Input => (encInput x).length) Z :=
    ((PolyBounded.const K).mul ((hO.add hBf).add hBt)).add hcsS
  obtain ⟨C, e, hCe⟩ := hZ.exists_le
  refine ⟨_, cs, C, e, 5 * D, fun x => (Nat.le_add_left _ _).trans (hCe x), ?_⟩
  intro n B P hb hp
  let x := ofFinite B P
  let m := n + P.length
  have hscale (flag : Bool) : Nat.logLogSqrtLogScale
      (if flag then (qt x).1 else (qf x).1) ≤
        5 * Nat.logLogSqrtLogScale m + 5 * Nat.logLogSqrtLogScale 32 := by
    have hdim : (if flag then (qt x).1 else (qf x).1) ≤ m := by
      have hd := dimensions x
      cases flag
      · simpa only [Bool.false_eq_true, ↓reduceIte, qf, out, m, x, ofFinite, declared,
          conditions, List.length_map] using hd.1
      · simpa only [↓reduceIte, qt, out, m, x, ofFinite, declared, conditions,
          List.length_map] using hd.2
    by_cases hm : 4 ≤ m
    · exact (Nat.logLogSqrtLogScale_le_of_le hdim hm).trans (by omega)
    · have hsmall := Nat.logLogSqrtLogScale_le_of_le
        (hdim.trans (by omega : m ≤ 32)) (by decide : 4 ≤ 32)
      omega
  let E := 2 ^ ((5 * D) * Nat.logLogSqrtLogScale m)
  have hE : 0 < E := Nat.two_pow_pos _
  have hK : 0 < K := Nat.two_pow_pos _
  have hpow (flag : Bool) :
      2 ^ (D * Nat.logLogSqrtLogScale (if flag then (qt x).1 else (qf x).1)) ≤ K * E := by
    calc _ ≤ 2 ^ (D * (5 * Nat.logLogSqrtLogScale m + 5 * Nat.logLogSqrtLogScale 32)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left D (hscale flag))
      _ = _ := by dsimp only [K, E]; rw [Nat.mul_add, pow_add, mul_comm]; congr 1; ring
  have hfTime := (hcp (qf x)).1.trans (Nat.mul_le_mul_left (Bf x) (hpow false))
  have htTime := (hcp (qt x)).1.trans (Nat.mul_le_mul_left (Bt x) (hpow true))
  have hOTime : O x ≤ O x * (K * E) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE)
  have hraw : cs.time x ≤ W x * (K * E) := by
    change cc.time x + (tag.time (out x) + (if (out x).isLeft then
      sf.time (out x) + cp.time (qf x) else
      (sf.time (out x) + cp.time (qf x)) + (st.time (out x) + cp.time (qt x)) +
        sub.time (counter (qf x), counter (qt x)))) ≤ _
    by_cases hl : (out x).isLeft = true
    · simp only [hl, ↓reduceIte]
      calc _ ≤ O x + cp.time (qf x) + cp.time (qt x) := by dsimp only [O]; omega
        _ ≤ O x * (K * E) + Bf x * (K * E) + Bt x * (K * E) :=
          Nat.add_le_add (Nat.add_le_add hOTime hfTime) htTime
        _ = _ := by dsimp only [W]; ring
    · simp only [hl, Bool.false_eq_true, ↓reduceIte]
      calc _ ≤ O x + cp.time (qf x) + cp.time (qt x) := by dsimp only [O]; omega
        _ ≤ O x * (K * E) + Bf x * (K * E) + Bt x * (K * E) :=
          Nat.add_le_add (Nat.add_le_add hOTime hfTime) htTime
        _ = _ := by dsimp only [W]; ring
  constructor
  · change execute counter (compile (ofFinite B P)) = _
    rw [execute_correct hcorrect B P hb hp, compile_count]
  · calc cs.time x ≤ Z x * E := hraw.trans (by
          have h : K * W x ≤ Z x := Nat.le_add_right _ _
          have := Nat.mul_le_mul_right E h
          nlinarith)
      _ ≤ _ := Nat.mul_le_mul_right E (hCe x)

/-- The real single-log-log source exponent for the complete generic original-input counter.
No relation between number of conditions and number of declared bits is assumed. -/
theorem exists_count_realEta_certificate (b d : ℕ) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (B : CNF (Fin n)) (P : List (DNF (Fin n)))
        (_hb : ∀ c ∈ B, c.length ≤ b) (_hp : ∀ p ∈ P, ∀ t ∈ p, t.length ≤ d),
        count (ofFinite B P) =
          Fintype.card {σ : Fin n → Bool // B.eval σ = true ∧ ∀ p ∈ P, DNF.eval σ p = true} ∧
        (16 ≤ n + P.length →
          (cs.time (ofFinite B P) : ℝ) ≤ (C : ℝ) *
            ((encInput (ofFinite B P)).length + 1 : ℕ) ^ e *
              (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale (n + P.length))) := by
  obtain ⟨count, cs, C, e, A, hs, h⟩ := exists_count_sharp_certificate b d
  refine ⟨count, cs, C, e, 6 * A, hs, ?_⟩
  intro n B P hb hp
  refine ⟨(h B P hb hp).1, fun hn => ?_⟩
  have ht : (cs.time (ofFinite B P) : ℝ) ≤ (C : ℝ) *
      ((encInput (ofFinite B P)).length + 1 : ℕ) ^ e *
        (2 : ℝ) ^ (A * Nat.logLogSqrtLogScale (n + P.length)) := by
    exact_mod_cast (h B P hb hp).2
  exact ht.trans (mul_le_mul_of_nonneg_left
    (by simpa only [Nat.cast_add] using Nat.two_pow_mul_logLogSqrtLogScale_le A hn)
    (by positivity))

end Cslib.Logic.PL.TwoBoundary.BinaryFrontend
