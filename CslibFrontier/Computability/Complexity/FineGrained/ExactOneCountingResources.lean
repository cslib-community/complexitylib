/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactOnePathPlan
public import CslibFrontier.Computability.Complexity.FineGrained.WeightedCountingPlan
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.IncidenceGeneralResources
import all CslibFrontier.Computability.PolyTime.CNF.SparseCNFLeafCounter
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Sharp resources for the actual signed-row/side-CNF dispatcher

The original binary clauses determine construction, rank, direct candidates and both queries.
The actual general-density width-three counter is instantiated, with sequential execution and
binary subtraction. Polynomial workspace includes both outputs and all construction stages.
The rounded exponent has one log-log factor. This is the signed-equation endpoint underlying
[ChenJiangZhu2027], Theorem 6.3; connecting the actual table writer remains separate.
-/

public section

namespace Cslib.Logic.PL.ExactOne.BinaryPlan

open Cslib.Complexity Cslib.GenericRAM Turing.MultiTapeTM
open Cslib.Circuits.Frontier.IncidenceNetwork
open WeightedRow.BinaryPlan

private abbrev encCounter := encPair encUnary encCNF

private theorem counterInput_binary_polytime (β : Bool) :
    ComputableInPolyTime (counterInput β) encOutput encCounter := by
  have hget := (ComputableInO.getRight?_deg encNat
    (encPair encUnary (encPair VCOne.encSignedCNF VCOne.encSignedCNF))).computableInPolyTime
  have hq := (ComputableInDegree.getD (enc₁ := encPair encUnary
    (encPair VCOne.encSignedCNF VCOne.encSignedCNF)) (0, ([], []))).computableInPolyTime.comp hget
  unfold counterInput
  cases β
  · exact hq.fst'.prod hq.snd'.fst'
  · exact hq.fst'.prod hq.snd'.snd'

private theorem dimension_le {n : ℕ} {p : Output}
    (hp : WithinBudget n 1 p) (b : Bool) : (counterInput b p).1 ≤ 2 * n := by
  cases p with
  | inl a => simp [counterInput]
  | inr q =>
    rcases q with ⟨N, qf, qt⟩
    simp only [counterInput, Sum.getRight?_inr, Option.getD_some]
    exact hp.1.trans (by omega)

/-- One actual binary algorithm has global polynomial space and sharp rounded running time
on signed distinct-variable equations with a binary side formula. Scopes/polarities occur only
in the semantic theorem; the executable input contains neither them nor rank/candidate advice. -/
theorem exists_count_sharp_certificate :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (B E : CNF (Fin n))
        (_hb : ∀ c ∈ B, c.length ≤ 2) (_he : ∀ c ∈ E, c.length ≤ n)
        (S : Fin E.length → Finset (Fin n)) (p : Fin E.length → Fin n → Bool)
        (_h : ∀ i, (E.get i).Perm (signedClause (S i) (p i))),
        let x : Input := (n, (B.relabel Fin.val, E.relabel Fin.val))
        count x = sourceCount B S p ∧
          cs.time x ≤ C * ((encInput x).length + 1) ^ e *
            2 ^ (A * Nat.logLogSqrtLogScale n) := by
  obtain ⟨β, N₀, Ncut, cp, D, hcp, hcorrect⟩ :=
    exists_countGeneralParity_sharp_certificate 3 (by decide)
  let counter := countGeneralParity 3 β N₀ Ncut
  have hcpS : PolyBounded (fun x => (encCounter x).length) cp.space :=
    PolyBounded.of_forall_le D D fun x => (hcp x).2
  let hf := counterInput_binary_polytime false
  let ht := counterInput_binary_polytime true
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
  have htag := (ComputableInO.isLeft_deg encNat
    (encPair encUnary (encPair VCOne.encSignedCNF VCOne.encSignedCNF))).computableInPolyTime
  have hget := (ComputableInO.getLeft?_deg encNat
    (encPair encUnary (encPair VCOne.encSignedCNF VCOne.encSignedCNF))).computableInPolyTime
  have hdir := (ComputableInDegree.getD (enc₁ := encNat) 0).computableInPolyTime.comp hget
  let tag := NativeCertificate.ofPolyTime htag
  let dir := NativeCertificate.ofPolyTime hdir
  have htagP := NativeCertificate.ofPolyTime_isPolynomial htag
  have hdirP := NativeCertificate.ofPolyTime_isPolynomial hdir
  let ce : NativeCertificate (execute counter) encOutput encNat :=
    (NativeCertificate.branch tag dir reconstruct).congr fun _ => rfl
  have heS : PolyBounded (fun p => (encOutput p).length) ce.space :=
    ((htagP.2.add hdirP.2).add hsRec).mono fun p => by
      change tag.space p + (if p.isLeft then dir.space p else reconstruct.space p) ≤
        tag.space p + dir.space p + reconstruct.space p
      split_ifs <;> omega
  let hcompile := compile_polytime
  let cc := NativeCertificate.ofPolyTime hcompile
  have hcc := NativeCertificate.ofPolyTime_isPolynomial hcompile
  let cs := ce.comp cc
  have hcsS := SparseCNFLeafCounter.polyBounded_comp_space ce cc heS hcc.2
  let out (x : Input) := compile x
  let qf (x : Input) := counterInput false (out x)
  let qt (x : Input) := counterInput true (out x)
  let O (x : Input) := cc.time x + tag.time (out x) + dir.time (out x) +
    sf.time (out x) + st.time (out x) + sub.time (counter (qf x), counter (qt x))
  let Bf (x : Input) := D * ((encCounter (qf x)).length + 1) ^ D
  let Bt (x : Input) := D * ((encCounter (qt x)).length + 1) ^ D
  let W (x : Input) := O x + Bf x + Bt x
  have hlen := hcompile.polyBounded_length
  have hpost := hsub.1.comp (SparseCNFLeafCounter.polyBounded_output_of_space both hsBoth)
  have hO : PolyBounded (fun x : Input => (encInput x).length) O :=
    ((((hcc.1.add (htagP.1.comp hlen)).add (hdirP.1.comp hlen)).add
      (hsf.1.comp hlen)).add (hst.1.comp hlen)).add (hpost.comp hlen)
  have hBf : PolyBounded (fun x : Input => (encInput x).length) Bf :=
    (PolyBounded.const D).mul (((hf.polyBounded_length.comp hlen).add (.const 1)).pow D)
  have hBt : PolyBounded (fun x : Input => (encInput x).length) Bt :=
    (PolyBounded.const D).mul (((ht.polyBounded_length.comp hlen).add (.const 1)).pow D)
  let K := 2 ^ (D * (5 * Nat.logLogSqrtLogScale 32))
  let Z (x : Input) := K * W x + cs.space x
  have hZ : PolyBounded (fun x : Input => (encInput x).length) Z :=
    ((PolyBounded.const K).mul ((hO.add hBf).add hBt)).add hcsS
  obtain ⟨C, e, hCe⟩ := hZ.exists_le
  refine ⟨_, cs, C, e, 40 * D, fun x => (Nat.le_add_left _ _).trans (hCe x), ?_⟩
  intro n B rows hb he S p h
  let x : Input := (n, (B.relabel Fin.val, rows.relabel Fin.val))
  have hbudget : WeightedRow.BinaryPlan.WithinBudget n 1 (out x) :=
    compile_withinBudget B rows hb he
  have hscale (b : Bool) : Nat.logLogSqrtLogScale (counterInput b (out x)).1 ≤
      40 * Nat.logLogSqrtLogScale n + 5 * Nat.logLogSqrtLogScale 32 := by
    have hN := dimension_le hbudget b
    by_cases hn : 4 ≤ n
    · calc _ ≤ 5 * Nat.logLogSqrtLogScale (2 * n) :=
            Nat.logLogSqrtLogScale_le_of_le hN (by omega)
        _ ≤ 5 * (4 * 2 * Nat.logLogSqrtLogScale n) := Nat.mul_le_mul_left 5
            (Nat.logLogSqrtLogScale_mul_le 2 (by omega))
        _ ≤ _ := by omega
    · have hsmall := Nat.logLogSqrtLogScale_le_of_le
        (by omega : (counterInput b (out x)).1 ≤ 32) (by decide : 4 ≤ 32)
      omega
  let E := 2 ^ ((40 * D) * Nat.logLogSqrtLogScale n)
  have hE : 0 < E := Nat.two_pow_pos _
  have hK : 0 < K := Nat.two_pow_pos _
  have hpow (b : Bool) : 2 ^ (D * Nat.logLogSqrtLogScale (counterInput b (out x)).1) ≤ K * E := by
    calc _ ≤ 2 ^ (D * (40 * Nat.logLogSqrtLogScale n + 5 * Nat.logLogSqrtLogScale 32)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left D (hscale b))
      _ = _ := by dsimp only [K, E]; rw [Nat.mul_add, pow_add, mul_comm]; congr 1; ring
  have hfTime := (hcp (qf x)).1.trans (Nat.mul_le_mul_left (Bf x) (hpow false))
  have htTime := (hcp (qt x)).1.trans (Nat.mul_le_mul_left (Bt x) (hpow true))
  have hOTime : O x ≤ O x * (K * E) := Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE)
  have hraw : cs.time x ≤ W x * (K * E) := by
    change cc.time x + (tag.time (out x) + (if (out x).isLeft then dir.time (out x) else
      (sf.time (out x) + cp.time (qf x)) + (st.time (out x) + cp.time (qt x)) +
        sub.time (counter (qf x), counter (qt x)))) ≤ _
    by_cases hl : (out x).isLeft = true
    · simp only [hl, ↓reduceIte]
      have hbare : cc.time x + (tag.time (out x) + dir.time (out x)) ≤ W x := by
        dsimp only [W, O]
        omega
      exact hbare.trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos hK hE))
    · simp only [hl, Bool.false_eq_true, ↓reduceIte]
      calc _ ≤ O x + cp.time (qf x) + cp.time (qt x) := by dsimp only [O]; omega
        _ ≤ O x * (K * E) + Bf x * (K * E) + Bt x * (K * E) :=
          Nat.add_le_add (Nat.add_le_add hOTime hfTime) htTime
        _ = _ := by dsimp only [W]; ring
  constructor
  · change execute counter (compile x) = _
    rw [execute_correct hcorrect hbudget, compile_count_of_perm B rows S p h]
  · calc cs.time x ≤ Z x * E := hraw.trans (by
          have h : K * W x ≤ Z x := Nat.le_add_right _ _
          have := Nat.mul_le_mul_right E h
          nlinarith)
      _ ≤ _ := Nat.mul_le_mul_right E (hCe x)

end Cslib.Logic.PL.ExactOne.BinaryPlan
