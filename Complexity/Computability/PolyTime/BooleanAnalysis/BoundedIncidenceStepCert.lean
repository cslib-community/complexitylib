/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceSemantics
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Native Step and Measurement-Payload Certificates for Bounded-Incidence Branch Evaluation

This file establishes polynomial-time stage certificates and uniform `ComputableInO` /
`PolyBounded`-workspace bounds for the inner group-cube and two-pass measurement-fiber payload
evaluators of the bounded-incidence $\mathbb{F}_2$ polynomial-system branch algorithm of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (§3.3, Lemma 3.2, p. 23;
§§5.3–5.4, Proposition 5.3, pp. 37–38; Appendix B.2–B.3, pp. 48–50).

Specifically, we define explicit bit-list encodings for the closed stage contexts `GroupEvalCtx`,
`MeasStepCtx`, and `SubsetStepCtx`, certify `validBranchEvalParams`, `validDesignShape`, and
`evalGroupFactorJet` in polynomial time, and compose `BooleanMeasurements.searchCertificate`
(Pass 1) with `CommonCountingAccum.computableInO_streamGroupJetSum` and
`CommonCountingAccum.computableInPolyTime_prodJet` (Pass 2) across the $r_u$ variable groups to
certify the per-measurement-word payload `evalMeasPayload` in
$O\bigl((r_u (2^{d_{\max}} + 1) + 1) \cdot \operatorname{poly}(|\mathrm{input}|)\bigr)$ time and
globally polynomial workspace.

## Main definitions

* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.encGroupEvalCtx`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.encMeasStepCtx`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.encSubsetStepCtx`: bit-list encodings for
  the closed step contexts of `CommonCountingAccum.streamGroupJetSum`, `MeasurementFold.run`, and
  `SubsetPairFold.run`.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.maxGroupDim`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.maxAllGroupDim`: unary-clamped maximum
  variable-group dimensions at a single interpolation node and across all $Q_u$ nodes.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.evalMeasPayload`: standalone two-pass
  measurement-word payload returning `some prodJet` when all $r_u$ group fibers are nonempty and
  `none` otherwise.

## Main results

* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.computableInPolyTime_validBranchEvalParams`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.computableInPolyTime_validDesignShape`,
  `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.computableInPolyTime_evalGroupFactorJet`:
  polynomial-time certificates for the entry guard, design-shape guard, and restricted local-cube
  group factor-jet summand.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.measurementStepBody_eq`: decomposition of
  `measurementStepBody` through `evalMeasPayload` and `Option.elim`.
* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.exists_computableInO_measPayload`: uniform
  `ComputableInO` time and `PolyBounded` workspace bound for `evalMeasPayload`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §3.3 (Lemma 3.2, p. 23),
  §§5.3–5.4 (Proposition 5.3, pp. 37–38), and Appendix B.2–B.3 (pp. 48–50).
-/

@[expose] public section

namespace Cslib.Complexity.SubexponentialSAT.SparsePolyCounter

open Finset Cslib Cslib.BitString Cslib.CommonCountingAccum Cslib.Complexity Cslib.GenericRAM
open Cslib.LinearAlgebra Turing.MultiTapeTM

local notation "encSys" => encList (encList (encList encNat))

/-! ### 1. Stage Encodings and Polynomial-Time Step Helpers -/

section StageHelpers

open ComputableInPolyTime

private abbrev encJet : JetRows ↪ List Bool := encList (encList encIntBin)
private abbrev encGroupEqEntry : (List (List ℕ) × List (List (List ℤ))) ↪ List Bool :=
  encPair (encList (encList encNat)) (encList (encList (encList encIntBin)))

/-- Bit-list encoding for `GroupEvalCtx`, encoding `(n', J, ℓ, k')` in unary, `(node, dDen)` and
measurement vectors in signed binary, bit masks via `encBits`, and precollected group equations with
replacement-row tables as nested lists. -/
def encGroupEvalCtx : GroupEvalCtx ↪ List Bool :=
  encPair
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
    (encPair
      (encPair encIntBin encIntBin)
      (encPair
        (encPair (encList encNat) (encPair (encList (encList encIntBin)) (encList encIntBin)))
        (encPair
          (encPair encBits (encPair encBits encBits))
          (encList (encPair (encList (encList encNat)) (encList (encList (encList encIntBin))))))))

/-- Bit-list encoding for `MeasStepCtx`, encoding `(n', r_u, m_rows)` and `(J, ℓ, k')` in unary
together with node parameters, per-group variable/measurement slices, subset bit masks, and
precollected group equations. -/
def encMeasStepCtx : MeasStepCtx ↪ List Bool :=
  encPair
    (encPair encUnary (encPair encUnary encUnary))
    (encPair
      (encPair encUnary (encPair encUnary encUnary))
      (encPair
        (encPair encIntBin encIntBin)
        (encPair
          (encPair (encList (encList encNat)) (encList (encList (encList encIntBin))))
          (encPair
            (encPair encBits encBits)
            (encList (encList
              (encPair (encList (encList encNat)) (encList (encList (encList encIntBin))))))))))

/-- Bit-list encoding for `SubsetStepCtx`, encoding `(n', r_u, m_rows)` and `(J, ℓ, k')` in unary,
`(c_meas, D_cap)` as `(encUnary, encNat)`, and the fixed per-node group and equation tables. -/
def encSubsetStepCtx : SubsetStepCtx ↪ List Bool :=
  encPair
    (encPair encUnary (encPair encUnary encUnary))
    (encPair
      (encPair encUnary encNat)
      (encPair
        (encPair encUnary (encPair encUnary encUnary))
        (encPair
          (encPair encIntBin encIntBin)
          (encPair
            (encPair (encList (encList encNat)) (encList (encList (encList encIntBin))))
            (encList (encList
              (encPair (encList (encList encNat)) (encList (encList (encList encIntBin))))))))))

private theorem bi_bool_and {α : Type} {encIn : α ↪ List Bool} {a b : α → Bool}
    (ha : ComputableInPolyTime a encIn encBool)
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => a x && b x) encIn encBool :=
  bool_and.comp (ha.prod hb)

private theorem bi_bool_not_or {α : Type} {encIn : α ↪ List Bool} {a b : α → Bool}
    (ha : ComputableInPolyTime a encIn encBool)
    (hb : ComputableInPolyTime b encIn encBool) :
    ComputableInPolyTime (fun x => !(a x) || b x) encIn encBool :=
  (of_finite (fun p : Bool × Bool => !p.1 || p.2)).comp (ha.prod hb)

private theorem bi_allWith {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {xs : α → List β} {test : α × β → Bool}
    (hxs : ComputableInPolyTime xs encA (encList encB))
    (htest : ComputableInPolyTime test (encPair encA encB) encBool) :
    ComputableInPolyTime (fun x => (xs x).all fun b => test (x, b)) encA encBool :=
  allWithEncoding htest id' hxs

private theorem bi_filterWithId {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {test : γ × α → Bool} {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encIn encA) encBool)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x => (list x).filter fun a => test (x, a))
      encIn (encList encA) :=
  filterWithInput (test := fun x a => test (x, a)) hlist htest

private theorem bi_mapWithId {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool} {f : γ × α → β} {list : γ → List α}
    (hf : ComputableInPolyTime f (encPair encIn encA) encB)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x => (list x).map fun a => f (x, a)) encIn (encList encB) :=
  mapWithInput (f := fun x a => f (x, a)) hlist hf

private theorem bi_unary_add : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    (encPair encUnary encUnary) encUnary := by fun_prop

private theorem bi_unary_mul : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.2)
    (encPair encUnary encUnary) encUnary := by fun_prop

private theorem bi_unary_min : ComputableInPolyTime (fun p : ℕ × ℕ => min p.1 p.2)
    (encPair encUnary encUnary) encUnary := by fun_prop

private theorem bi_unary_max : ComputableInPolyTime (fun p : ℕ × ℕ => max p.1 p.2)
    (encPair encUnary encUnary) encUnary := by fun_prop

private theorem bi_binary_le' {α : Type} {encIn : α ↪ List Bool} {a b : α → ℕ}
    (ha : ComputableInPolyTime a encIn encNat) (hb : ComputableInPolyTime b encIn encNat) :
    ComputableInPolyTime (fun x => decide (a x ≤ b x)) encIn encBool :=
  binary_le.comp (ha.prod hb)

private theorem bi_binary_add' {α : Type} {encIn : α ↪ List Bool} {a b : α → ℕ}
    (ha : ComputableInPolyTime a encIn encNat) (hb : ComputableInPolyTime b encIn encNat) :
    ComputableInPolyTime (fun x => a x + b x) encIn encNat :=
  binary_add.comp (ha.prod hb)

private theorem bi_intBin_add : ComputableInPolyTime (fun p : ℤ × ℤ => p.1 + p.2)
    (encPair encIntBin encIntBin) encIntBin := by fun_prop

private theorem bi_intBin_add' {α : Type} {encIn : α ↪ List Bool} {a b : α → ℤ}
    (ha : ComputableInPolyTime a encIn encIntBin)
    (hb : ComputableInPolyTime b encIn encIntBin) :
    ComputableInPolyTime (fun x => a x + b x) encIn encIntBin :=
  bi_intBin_add.comp (ha.prod hb)

private theorem bi_intBin_pow : ComputableInPolyTime (fun p : ℤ × ℕ => p.1 ^ p.2)
    (encPair encIntBin encUnary) encIntBin := by fun_prop

private theorem bi_intBin_pow' {α : Type} {encIn : α ↪ List Bool} {a : α → ℤ} {b : α → ℕ}
    (ha : ComputableInPolyTime a encIn encIntBin) (hb : ComputableInPolyTime b encIn encUnary) :
    ComputableInPolyTime (fun x => a x ^ b x) encIn encIntBin :=
  bi_intBin_pow.comp (ha.prod hb)

private theorem bi_cons {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : α × List α => p.1 :: p.2)
      (encPair enc (encList enc)) (encList enc) := by fun_prop

private theorem bi_cons' {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {head : γ → α} {tail : γ → List α}
    (hhead : ComputableInPolyTime head encIn encA)
    (htail : ComputableInPolyTime tail encIn (encList encA)) :
    ComputableInPolyTime (fun x => head x :: tail x) encIn (encList encA) :=
  (bi_cons encA).comp (hhead.prod htail)

private theorem bi_listAppend {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × List α => p.1 ++ p.2)
      (encPair (encList enc) (encList enc)) (encList enc) := by fun_prop

private theorem bi_listAppend' {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {left right : γ → List α}
    (hleft : ComputableInPolyTime left encIn (encList encA))
    (hright : ComputableInPolyTime right encIn (encList encA)) :
    ComputableInPolyTime (fun x => left x ++ right x) encIn (encList encA) :=
  (bi_listAppend encA).comp (hleft.prod hright)

private theorem bi_replicate_base {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : ℕ × α => List.replicate p.1 p.2)
      (encPair encUnary enc) (encList enc) := by fun_prop

private theorem bi_replicate {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} {v : γ → α}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hv : ComputableInPolyTime v encIn encA) :
    ComputableInPolyTime (fun x => List.replicate (n x) (v x)) encIn (encList encA) :=
  (bi_replicate_base encA).comp (hn.prod hv)

private theorem bi_takeUnary {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × ℕ => p.1.take p.2)
      (encPair (encList enc) encUnary) (encList enc) := by fun_prop

private theorem bi_listTakeWithInput {α γ : Type} {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {list : γ → List α} {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun x => (list x).take (count x)) encIn (encList encA) :=
  (bi_takeUnary encA).comp (hlist.prod hcount)

private theorem bi_dropUnary {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × ℕ => p.1.drop p.2)
      (encPair (encList enc) encUnary) (encList enc) := by fun_prop

private theorem bi_listDropWithInput {α γ : Type} {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {list : γ → List α} {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun x => (list x).drop (count x)) encIn (encList encA) :=
  (bi_dropUnary encA).comp (hlist.prod hcount)

private theorem bi_flatten {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime List.flatten (encList (encList enc)) (encList enc) := by fun_prop

private theorem bi_listGetD_nat_dyn {α : Type} {encIn : α ↪ List Bool}
    {xs : α → List ℕ} {idx fallback : α → ℕ}
    (hxs : ComputableInPolyTime xs encIn (encList encNat))
    (hidx : ComputableInPolyTime idx encIn encUnary)
    (hfb : ComputableInPolyTime fallback encIn encNat) :
    ComputableInPolyTime (fun x => (xs x).getD (idx x) (fallback x)) encIn encNat := by
  have hlt := binary_lt' (unary_to_binary.comp hidx)
    (unary_to_binary.comp ((length_list encNat).comp hxs))
  have h0 := (listGetD (encA := encNat) 0).comp (hxs.prod hidx)
  refine (hlt.ite' h0 hfb).of_enc_eq fun x => ?_
  congr 1; dsimp only [Function.comp_apply]
  by_cases h : idx x < (xs x).length
  · simp only [h, decide_true, ↓reduceIte]
    rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte,
      List.getD_eq_default _ _ (Nat.le_of_not_lt h)]

/-- `validBranchEvalParams` is computable in polynomial time on `encBranchEvalInput`. -/
theorem computableInPolyTime_validBranchEvalParams :
    ComputableInPolyTime validBranchEvalParams encBranchEvalInput encBool := by
  unfold validBranchEvalParams encBranchEvalInput
  let encQuad := encPair encNat (encPair encNat (encPair encNat encNat))
  let eR := encPair encQuad (encPair encQuad encSys)
  have hp1 := fst (encPair encUnary encUnary) eR; have hp2 := snd (encPair encUnary encUnary) eR
  have hn' := hp1.fst'; have hk' := hp1.snd'
  have hsched := hp2.snd'.fst'; have heqs := hp2.snd'.snd'
  have hr := hsched.fst'; have hQ := hsched.snd'.fst'
  have hR := hsched.snd'.snd'.fst'; have hA₀ := hsched.snd'.snd'.snd'
  have hn_b := unary_to_binary.comp hn'; have hk_b := unary_to_binary.comp hk'
  have hQu := binary_min_unary' hn' hQ
  have hru := binary_min_unary' hn' hr
  have h2Qu := bi_unary_add.comp (hQu.prod hQu)
  have hpow : ComputableInPolyTime
      (fun inp : BranchEvalInput => (min inp.1.1 inp.2.2.1.1) ^ (2 * min inp.1.1 inp.2.2.1.2.1))
      (encPair (encPair encUnary encUnary) eR) encNat :=
    (binary_pow.comp ((unary_to_binary.comp hru).prod h2Qu)).of_enc_eq
      fun inp => by congr 1; dsimp only [Function.comp_apply]; congr 1; omega
  have hc1 := bi_binary_le' (const 1) hn_b; have hc2 := bi_binary_le' (const 2) hr
  have hc3 := bi_binary_le' (const 1) hR; have hc4 := binary_lt' hR hQ
  have hc5 := bi_binary_le' hQ hn_b; have hc6 := bi_binary_le' hr hn_b
  have hc7 := bi_binary_le' (bi_binary_add' hA₀ hR) (bi_binary_add' hQ (const 1))
  have hc8 := bi_binary_le' hpow hn_b
  have hc9 := computableInPolyTime_checkVarsLt.comp (hn'.prod heqs)
  have hc10 := computableInPolyTime_checkCanonicalSystem.comp heqs
  have hc11 := bi_binary_le'
    (unary_to_binary.comp (computableInPolyTime_sysMaxDegree.comp heqs)) hk_b
  exact bi_bool_and (bi_bool_and (bi_bool_and (bi_bool_and (bi_bool_and
    (bi_bool_and (bi_bool_and (bi_bool_and (bi_bool_and (bi_bool_and
      hc1 hc2) hc3) hc4) hc5) hc6) hc7) hc8) hc9) hc10) hc11

/-- `validDesignShape` is computable in polynomial time when `(n', r_u, m_eq)` are given in unary
and `data` is encoded via `encReplacementDesignData`. -/
theorem computableInPolyTime_validDesignShape {α : Type} {encIn : α ↪ List Bool}
    {n' r_u m_eq : α → ℕ} {data : α → ReplacementDesignData}
    (hn' : ComputableInPolyTime n' encIn encUnary)
    (hru : ComputableInPolyTime r_u encIn encUnary)
    (hmeq : ComputableInPolyTime m_eq encIn encUnary)
    (hdata : ComputableInPolyTime data encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => validDesignShape (n' x) (r_u x) (m_eq x) (data x))
      encIn encBool := by
  unfold validDesignShape
  have hmrows : ComputableInPolyTime (fun x => (data x).measurementMatrix.length) encIn encUnary :=
    (length_list (encList encIntBin)).comp (computableInPolyTime_measurementMatrix hdata)
  have hlhs := bi_unary_mul.comp (hru.prod hmrows)
  have hrhs := bi_unary_mul.comp ((bi_unary_mul.comp ((const 4).prod
      (bi_unary_add.comp (hn'.prod (const 1))))).prod
    (bi_unary_add.comp ((bi_unary_add.comp ((bi_unary_mul.comp (hmeq.prod hn')).prod hn')).prod
      (const 1))))
  have h1 := unary_le' hlhs hrhs
  have hvgs := computableInPolyTime_varGroups hdata
  let e1 := encPair encIn (encList (encList encNat))
  let e2 := encPair e1 (encList encNat)
  have hn_q := hn'.comp ((fst encIn (encList (encList encNat))).comp (fst e1 (encList encNat)))
  have h2n_b := unary_to_binary.comp (bi_unary_add.comp (hn_q.prod hn_q))
  have hlen_b := unary_to_binary.comp ((length_list encNat).comp (snd e1 (encList encNat)))
  have hcmp : ComputableInPolyTime
      (fun q : (α × List (List ℕ)) × List ℕ => decide (q.2.length ≤ 2 * n' q.1.1)) e2 encBool := by
    refine (bi_binary_le' hlen_b h2n_b).of_enc_eq fun q => ?_
    congr 1; apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, decide_eq_true_eq]; omega
  have hall := bi_allWith hvgs (bi_allWith (snd encIn (encList (encList encNat))) hcmp)
  exact bi_bool_and h1 hall

private theorem length_applyGroupBits (n' : ℕ) (Vg : List ℕ) (ug base : List Bool) :
    (applyGroupBits n' Vg ug base).length = n' := by
  simp only [applyGroupBits, List.length_map, List.length_range]

private theorem computableInPolyTime_applyGroupBits {α : Type} {encIn : α ↪ List Bool}
    {n' : α → ℕ} {Vg : α → List ℕ} {ug base : α → List Bool}
    (hn' : ComputableInPolyTime n' encIn encUnary)
    (hVg : ComputableInPolyTime Vg encIn (encList encNat))
    (hug : ComputableInPolyTime ug encIn encBits)
    (hbase : ComputableInPolyTime base encIn encBits) :
    ComputableInPolyTime (fun x => applyGroupBits (n' x) (Vg x) (ug x) (base x))
      encIn encBits := by
  let e1 := encPair encIn encUnary
  let hx1 := fst encIn encUnary; let hv_un := snd encIn encUnary
  let ePar := encPair encNat (encPair encNat (encPair (encList encNat) encBits))
  have hpar : ComputableInPolyTime
      (fun p : α × ℕ => (n' p.1, (p.2, (Vg p.1, ug p.1)))) e1 ePar :=
    (unary_to_binary.comp (hn'.comp hx1)).prod
      ((unary_to_binary.comp hv_un).prod ((hVg.comp hx1).prod (hug.comp hx1)))
  have hlist := range.comp ((length_list encNat).comp (hVg.comp hx1))
  have hinit := bitsGetDWithInput (hbase.comp hx1) hv_un false
  let stepFn (par : ℕ × ℕ × List ℕ × List Bool) (cur : Bool) (j : ℕ) : Bool :=
    if par.2.2.1.getD j par.1 == par.2.1 then par.2.2.2.getD j false else cur
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ × List ℕ × List Bool) × Bool) × ℕ => stepFn q.1.1 q.1.2 q.2)
      (encPair (encPair ePar encBool) encUnary) encBool := by
    let ePB := encPair ePar encBool
    have hp := (fst ePar encBool).comp (fst ePB encUnary)
    have hcur := (snd ePar encBool).comp (fst ePB encUnary); have hj := snd ePB encUnary
    have hn_s := hp.fst'; have hv_s := hp.snd'.fst'
    have hVg_s := hp.snd'.snd'.fst'; have hug_s := hp.snd'.snd'.snd'
    have hgetV := bi_listGetD_nat_dyn hVg_s hj hn_s
    have hgetU := bitsGetDWithInput hug_s hj false
    exact (beq hgetV hv_s).ite' hgetU hcur
  have hfold := foldlWith hpar hlist hinit hstep (.const 1)
    (fun _ _ _ => by simp only [encBool_apply, List.length_singleton, le_rfl])
  exact (bits_encList_polyTime encBool).2.comp (mapWithInput (range.comp hn') hfold)

private theorem computableInPolyTime_buildBaseAssignment {α : Type} {encIn : α ↪ List Bool}
    {n' r_u : α → ℕ} {vGroups_t : α → List (List ℕ)} {reps : α → List (List Bool)}
    (hn' : ComputableInPolyTime n' encIn encUnary)
    (hru : ComputableInPolyTime r_u encIn encUnary)
    (hvgs : ComputableInPolyTime vGroups_t encIn (encList (encList encNat)))
    (hreps : ComputableInPolyTime reps encIn (encList encBits)) :
    ComputableInPolyTime (fun x => buildBaseAssignment (n' x) (r_u x) (vGroups_t x) (reps x))
      encIn encBits := by
  let ePar := encPair encUnary (encPair (encList (encList encNat)) (encList encBits))
  have hpar : ComputableInPolyTime (fun x => (n' x, (vGroups_t x, reps x))) encIn ePar :=
    hn'.prod (hvgs.prod hreps)
  have hlist := range.comp hru
  have hinit := (bits_encList_polyTime encBool).2.comp (bi_replicate hn' (const false))
  let stepFn (par : ℕ × List (List ℕ) × List (List Bool)) (acc : List Bool) (g : ℕ) : List Bool :=
    applyGroupBits par.1 (par.2.1.getD g []) (par.2.2.getD g []) acc
  have hstep : ComputableInPolyTime
      (fun q : ((ℕ × List (List ℕ) × List (List Bool)) × List Bool) × ℕ =>
        stepFn q.1.1 q.1.2 q.2)
      (encPair (encPair ePar encBits) encUnary) encBits := by
    let ePB := encPair ePar encBits
    have hp := (fst ePar encBits).comp (fst ePB encUnary)
    have hacc := (snd ePar encBits).comp (fst ePB encUnary)
    have hg := snd ePB encUnary
    have hVg := (listGetD (encA := encList encNat) []).comp (hp.snd'.fst'.prod hg)
    have hug := (listGetD (encA := encBits) []).comp (hp.snd'.snd'.prod hg)
    exact computableInPolyTime_applyGroupBits hp.fst' hVg hug hacc
  have hlen_fold (n : ℕ) (vgs : List (List ℕ)) (rps : List (List Bool)) :
      ∀ (xs : List ℕ) (acc : List Bool), acc.length = n →
        (xs.foldl (stepFn (n, vgs, rps)) acc).length = n := by
    intro xs; induction xs with
    | nil => exact fun _ h => h
    | cons _ _ ih => intro _ _; exact ih _ (length_applyGroupBits _ _ _ _)
  exact foldlWith hpar hlist hinit hstep hn'.polyBounded fun x _ _ => by
    simp only [encBits_apply]
    exact (hlen_fold (n' x) (vGroups_t x) (reps x) _ _ List.length_replicate).le

private theorem computableInPolyTime_checkRestrictedGroup {α : Type} {encIn : α ↪ List Bool}
    {n' : α → ℕ} {indE : α → List Bool} {Vg : α → List ℕ} {ug : α → List Bool}
    (hn' : ComputableInPolyTime n' encIn encUnary)
    (hindE : ComputableInPolyTime indE encIn encBits)
    (hVg : ComputableInPolyTime Vg encIn (encList encNat))
    (hug : ComputableInPolyTime ug encIn encBits) :
    ComputableInPolyTime (fun x => checkRestrictedGroup (n' x) (indE x) (Vg x) (ug x))
      encIn encBool := by
  unfold checkRestrictedGroup
  have hrange := range.comp ((length_list encNat).comp hVg)
  have hx := fst encIn encUnary
  have hj := snd encIn encUnary
  have hgetV := bi_listGetD_nat_dyn (hVg.comp hx) hj (unary_to_binary.comp (hn'.comp hx))
  have hindE_x := hindE.comp hx
  have hlenE : ComputableInPolyTime (fun p : α × ℕ => (indE p.1).length)
      (encPair encIn encUnary) encUnary :=
    length_bits_comp hindE_x
  have hv_cap := binary_min_unary' hlenE hgetV
  have hgetE : ComputableInPolyTime
      (fun p : α × ℕ => (indE p.1).getD ((Vg p.1).getD p.2 (n' p.1)) false)
      (encPair encIn encUnary) encBool := by
    refine (bitsGetDWithInput hindE_x hv_cap false).of_enc_eq fun p => ?_
    congr 1; dsimp only [Function.comp_apply]
    by_cases h : (Vg p.1).getD p.2 (n' p.1) < (indE p.1).length
    · rw [Nat.min_eq_right (Nat.le_of_lt h)]
    · rw [Nat.min_eq_left (Nat.le_of_not_lt h), List.getD_eq_default _ _ le_rfl,
        List.getD_eq_default _ _ (Nat.le_of_not_lt h)]
  have hgetU := bitsGetDWithInput (hug.comp hx) hj false
  exact bi_allWith hrange (bi_bool_not_or hgetE hgetU)

private theorem computableInPolyTime_buildEqRowTables {α : Type} {encIn : α ↪ List Bool}
    {n' : α → ℕ} {eqs' : α → List (List (List ℕ))} {data : α → ReplacementDesignData}
    (hn' : ComputableInPolyTime n' encIn encUnary)
    (heqs : ComputableInPolyTime eqs' encIn encSys)
    (hdata : ComputableInPolyTime data encIn encReplacementDesignData) :
    ComputableInPolyTime (fun x => buildEqRowTables (n' x) (eqs' x) (data x))
      encIn (encList (encList (encList (encList encIntBin)))) := by
  unfold buildEqRowTables
  have hrf := range.comp ((length_list (encList (encList encNat))).comp heqs)
  let e1 := encPair encIn encUnary
  have hrn := range.comp (hn'.comp (fst encIn encUnary))
  have hq1 := fst e1 encUnary
  have hd2 := hdata.comp ((fst encIn encUnary).comp hq1)
  have hf2 : ComputableInPolyTime (fun q : (α × ℕ) × ℕ => q.1.2) (encPair e1 encUnary) encNat :=
    unary_to_binary.comp ((snd encIn encUnary).comp hq1)
  have hv2 : ComputableInPolyTime (fun q : (α × ℕ) × ℕ => q.2) (encPair e1 encUnary) encNat :=
    unary_to_binary.comp (snd e1 encUnary)
  exact mapWithInput hrf (mapWithInput hrn (computableInPolyTime_lookupReplacementRow hd2 hf2 hv2))

private theorem computableInPolyTime_groupEquationsAt {α : Type} {encIn : α ↪ List Bool}
    {eqs' : α → List (List (List ℕ))} {factorGroups : α → List (List ℕ)}
    {eqRowTables : α → List (List (List (List ℤ)))} {t g : α → ℕ}
    (heqs : ComputableInPolyTime eqs' encIn encSys)
    (hfg : ComputableInPolyTime factorGroups encIn (encList (encList encNat)))
    (htab : ComputableInPolyTime eqRowTables encIn
      (encList (encList (encList (encList encIntBin)))))
    (ht : ComputableInPolyTime t encIn encUnary)
    (hg : ComputableInPolyTime g encIn encUnary) :
    ComputableInPolyTime
      (fun x => groupEquationsAt (eqs' x) (factorGroups x) (eqRowTables x) (t x) (g x))
      encIn (encList encGroupEqEntry) := by
  unfold groupEquationsAt
  have hrf := range.comp ((length_list (encList (encList encNat))).comp heqs)
  have hx := fst encIn encUnary
  have hf_u := snd encIn encUnary
  have hrow := (listGetD (encA := encList encNat) []).comp ((hfg.comp hx).prod hf_u)
  have hval := (listGetD (encA := encNat) 0).comp (hrow.prod (ht.comp hx))
  have hfilt := bi_filterWithId (decide_eq' hval (unary_to_binary.comp (hg.comp hx))) hrf
  have hpair := ((listGetD (encA := encList (encList encNat)) []).comp
      ((heqs.comp hx).prod hf_u)).prod
    ((listGetD (encA := encList (encList (encList encIntBin))) []).comp
      ((htab.comp hx).prod hf_u))
  exact bi_mapWithId hpair hfilt

/-- `evalGroupFactorJet` is computable in polynomial time on
`encPair encGroupEvalCtx (encPair encUnary encBits)`, matching the body-certificate obligation of
`CommonCountingAccum.computableInO_streamGroupJetSum`. -/
theorem computableInPolyTime_evalGroupFactorJet :
    ComputableInPolyTime evalGroupFactorJet
      (encPair encGroupEvalCtx (encPair encUnary encBits)) (encList (encList encIntBin)) := by
  unfold evalGroupFactorJet encGroupEvalCtx
  let eC1 := encPair encUnary (encPair encUnary (encPair encUnary encUnary))
  let eC2 := encPair (encPair encIntBin encIntBin)
    (encPair (encPair (encList encNat) (encPair (encList (encList encIntBin)) (encList encIntBin)))
      (encPair (encPair encBits (encPair encBits encBits)) (encList encGroupEqEntry)))
  let eCtx := encPair eC1 eC2; let eIn := encPair eCtx (encPair encUnary encBits)
  have hctx := fst eCtx (encPair encUnary encBits)
  have hug := (snd eCtx (encPair encUnary encBits)).snd'
  have hc1 := hctx.fst'; have hc2 := hctx.snd'
  have hn' : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.1.1)
      eIn encUnary := hc1.fst'
  have hJ : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.1.2.1)
      eIn encUnary := hc1.snd'.fst'
  have hℓ : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.1.2.2.1)
      eIn encUnary := hc1.snd'.snd'.fst'
  have hk' : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.1.2.2.2)
      eIn encUnary := hc1.snd'.snd'.snd'
  have hnode : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.2.1.1)
      eIn encIntBin := hc2.fst'.fst'
  have hdDen : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.2.1.2)
      eIn encIntBin := hc2.fst'.snd'
  have hVg : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.2.2.1.1)
      eIn (encList encNat) := hc2.snd'.fst'.fst'
  have hCtg : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.2.2.1.2.1)
      eIn (encList (encList encIntBin)) := hc2.snd'.fst'.snd'.fst'
  have hyg : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.2.2.1.2.2)
      eIn (encList encIntBin) := hc2.snd'.fst'.snd'.snd'
  have hindE : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.2.2.2.1.1)
      eIn encBits := hc2.snd'.snd'.fst'.fst'
  have hindU : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.2.2.2.1.2.1)
      eIn encBits := hc2.snd'.snd'.fst'.snd'.fst'
  have hxStar : ComputableInPolyTime (fun p : GroupEvalCtx × (ℕ × List Bool) => p.1.2.2.2.1.2.2)
      eIn encBits := hc2.snd'.snd'.fst'.snd'.snd'
  have hgrpEqs := hc2.snd'.snd'.snd'
  have hchk1 := computableInPolyTime_checkRestrictedGroup hn' hindE hVg hug
  have hchk2 := (BooleanMeasurements.test_polyTime
    (fst (encList (encList encIntBin)) (encList encIntBin))
    (snd (encList (encList encIntBin)) (encList encIntBin))).comp
    ((hCtg.prod hyg).prod hug)
  have hx := computableInPolyTime_applyGroupBits hn' hVg hug hxStar
  have hp0 := fst eIn encGroupEqEntry
  have heq := snd eIn encGroupEqEntry
  have hindU_m := (bits_encList_polyTime encBool).1.comp (hindU.comp hp0)
  have hx_m := (bits_encList_polyTime encBool).1.comp (hx.comp hp0)
  have hvarJ := computableInPolyTime_evalAffineInputZJetTable (hJ.comp hp0)
    (hnode.comp hp0) heq.snd' hindU_m hx_m
  have hfac := computableInPolyTime_evalEquationParityFactorJet (hJ.comp hp0)
    (hℓ.comp hp0) (hk'.comp hp0) (hdDen.comp hp0) hvarJ heq.fst'
  have hprod := CommonCountingAccum.computableInPolyTime_prodJet hJ hℓ (bi_mapWithId hfac hgrpEqs)
  have hzero := computableInPolyTime_zeroJet hJ hℓ
  exact (bi_bool_and hchk1 hchk2).ite' hprod hzero

end StageHelpers

/-! ### 2. Bounded-Range Loop Combinators and Measurement-Payload Certificate -/

section LoopCertificates

open ComputableInPolyTime

/-- Maximum unary-clamped variable-group dimension `min (2 * n') |V_{t,g}|` across `g < r_u` at a
fixed interpolation node `t`. -/
def maxGroupDim (n' r_u : ℕ) (vGroups_t : List (List ℕ)) : ℕ :=
  ((List.range r_u).map fun g => min (2 * n') (vGroups_t.getD g []).length).foldl max 0

/-- Maximum unary-clamped variable-group dimension across all nodes `t < Q_u` and groups
`g < r_u`. -/
def maxAllGroupDim (n' Q_u r_u : ℕ) (varGroups : List (List (List ℕ))) : ℕ :=
  ((List.range Q_u).map fun t => maxGroupDim n' r_u (varGroups.getD t [])).foldl max 0

private theorem min_length_le_maxGroupDim {n' r_u g : ℕ} {vGroups_t : List (List ℕ)}
    (hg : g < r_u) :
    min (2 * n') (vGroups_t.getD g []).length ≤ maxGroupDim n' r_u vGroups_t :=
  le_foldl_max_of_mem (List.mem_map.mpr ⟨g, List.mem_range.mpr hg, rfl⟩)

private theorem maxGroupDim_le_maxAllGroupDim {n' Q_u r_u t : ℕ}
    {varGroups : List (List (List ℕ))} (ht : t < Q_u) :
    maxGroupDim n' r_u (varGroups.getD t []) ≤ maxAllGroupDim n' Q_u r_u varGroups :=
  le_foldl_max_of_mem (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)

private theorem foldl_optAddJet_spec (J ℓ j M : ℕ) (f : ℕ → Option JetRows)
    (hf : ∀ i < j, ∀ y, f i = some y → ∀ j' < J, ∀ u' < ℓ, (rowEntry y j' u').natAbs ≤ M) :
    let res := (List.range j).foldl
      (fun acc i => (f i).elim acc (fun y => addJet J ℓ acc y)) (zeroJet J ℓ)
    IsTableShape J ℓ res ∧ ∀ j' < J, ∀ u' < ℓ, (rowEntry res j' u').natAbs ≤ j * M := by
  induction j with
  | zero =>
    exact ⟨isTableShape_zeroJet J ℓ, fun _ _ _ _ => by
      simp only [List.range_zero, List.foldl_nil, rowEntry_zeroJet, Int.natAbs_zero, Nat.zero_mul,
        le_rfl]⟩
  | succ k ih =>
    obtain ⟨hsh, hbd⟩ := ih fun i hi => hf i (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    cases hfk : f k with
    | none =>
      exact ⟨hsh, fun j' hj' u' hu' =>
        (hbd j' hj' u' hu').trans (Nat.mul_le_mul_right M (Nat.le_succ k))⟩
    | some y =>
      refine ⟨isTableShape_addJet J ℓ _ y, fun j' hj' u' hu' => ?_⟩
      rw [Option.elim_some, rowEntry_addJet _ _ hj' hu']
      exact (Int.natAbs_add_le _ _).trans
        ((Nat.add_le_add (hbd j' hj' u' hu') (hf k (by omega) y hfk j' hj' u' hu')).trans_eq
          (by ring))

private theorem length_encJetRows_foldl_optAddJet_le {J ℓ j N M : ℕ} {f : ℕ → Option JetRows}
    (hj : j ≤ N)
    (hf : ∀ i < j, ∀ y, f i = some y → ∀ j' < J, ∀ u' < ℓ, (rowEntry y j' u').natAbs ≤ M) :
    (encJet ((List.range j).foldl
      (fun acc i => (f i).elim acc (fun y => addJet J ℓ acc y)) (zeroJet J ℓ))).length ≤
      J * (2 * (ℓ * (2 * (N.size + M.size) + 3)) + 1) := by
  obtain ⟨hsh, hbd⟩ := foldl_optAddJet_spec J ℓ j M f hf
  exact CommonCountingAccum.length_encJetRows_le_of_size_le hsh fun j' hj' u' hu' =>
    (Nat.size_le_size ((hbd j' hj' u' hu').trans (Nat.mul_le_mul_right M hj))).trans
      (Nat.size_mul_le N M)

private def mapRangeStep {γ δ : Type} (f : γ × ℕ → δ)
    (p : ℕ × ((ℕ × γ) × List δ)) : (ℕ × γ) × List δ :=
  if decide (p.1 < p.2.1.1) then (p.2.1, p.2.2 ++ [f (p.2.1.2, min p.2.1.1 p.1)]) else p.2

private theorem run_mapRangeStep {γ δ : Type} (f : γ × ℕ → δ) {m : ℕ} (c : γ) {j : ℕ}
    (hj : j ≤ m) :
    (IndexFold.run (mapRangeStep f) j ((m, c), [])).2 =
      ((m, c), (List.range j).map fun i => f (c, i)) := by
  induction j with
  | zero => rfl
  | succ k ih =>
    have hk : k < m := Nat.lt_of_succ_le hj
    have hprev := ih (Nat.le_of_lt hk)
    have hst : IndexFold.run (mapRangeStep f) k ((m, c), []) =
        (k, ((m, c), (List.range k).map fun i => f (c, i))) :=
      Prod.ext (IndexFold.run_index _ _ _) hprev
    rw [IndexFold.run_succ, hst]
    simp only [IndexFold.step, mapRangeStep, hk, decide_true, ↓reduceIte,
      Nat.min_eq_right (Nat.le_of_lt hk), List.range_succ, List.map_append, List.map_cons,
      List.map_nil]

private theorem exists_computableInO_mapRange {ι γ δ : Type} {encIn : ι ↪ List Bool}
    {encC : γ ↪ List Bool} {encB : δ ↪ List Bool} {m : ι → ℕ} {ctx : ι → γ} {f : γ × ℕ → δ}
    (hm : ComputableInPolyTime m encIn encUnary) (hctx : ComputableInPolyTime ctx encIn encC)
    {Tf Sf : γ × ℕ → ℕ} (hSf : PolyBounded (fun p => (encPair encC encUnary p).length) Sf)
    (hcf : ComputableInO f (encPair encC encUnary) encB Tf Sf)
    (R : ι → ℕ) (hR : ∀ x, ∀ i < m x, Tf (ctx x, i) ≤ R x) :
    ∃ P : ι → ℕ, PolyBounded (fun x => (encIn x).length) P ∧
      ComputableInO (fun x => (List.range (m x)).map fun i => f (ctx x, i))
        encIn (encList encB) (fun x => (m x + 1) * (R x + P x)) P := by
  let cf : NativeCertificate f (encPair encC encUnary) encB := ⟨Tf, Sf, hcf⟩
  let encAcc := encPair (encPair encUnary encC) (encList encB)
  let eSt := encPair encNat encAcc
  have hm_b : ComputableInPolyTime m encIn encNat := unary_to_binary.comp hm
  have hinit : ComputableInPolyTime (fun x : ι => ((m x, ctx x), ([] : List δ))) encIn encAcc :=
    (hm.prod hctx).prod (const [])
  have hcond : ComputableInPolyTime (fun p : ℕ × ((ℕ × γ) × List δ) => decide (p.1 < p.2.1.1))
      eSt encBool :=
    binary_lt' (fst encNat encAcc) (unary_to_binary.comp (snd encNat encAcc).fst'.fst')
  have hprep : ComputableInPolyTime
      (fun p : ℕ × ((ℕ × γ) × List δ) => (p.2.1.2, min p.2.1.1 p.1))
      eSt (encPair encC encUnary) :=
    (snd encNat encAcc).fst'.snd'.prod
      (binary_min_unary' (snd encNat encAcc).fst'.fst' (fst encNat encAcc))
  have hcomb : ComputableInPolyTime
      (fun q : (ℕ × ((ℕ × γ) × List δ)) × δ => (q.1.2.1, q.1.2.2 ++ [q.2]))
      (encPair eSt encB) encAcc := by
    have hq1 := fst eSt encB; have hq2 := snd eSt encB
    exact hq1.snd'.fst'.prod (bi_listAppend' hq1.snd'.snd' (bi_cons' hq2 (const [])))
  let cCond := NativeCertificate.ofPolyTime hcond
  let cPrep := NativeCertificate.ofPolyTime hprep
  let cComb := NativeCertificate.ofPolyTime hcomb
  let cId := NativeCertificate.linear (ei := eSt) (ComputableInO.of_eq fun _ => rfl)
  let cYes := cComb.comp (cId.prod (cf.comp cPrep))
  let cNo := NativeCertificate.snd cId
  let cb₀ := NativeCertificate.branch cCond cYes cNo
  have hcCond := NativeCertificate.ofPolyTime_isPolynomial hcond
  have hcPrep := NativeCertificate.ofPolyTime_isPolynomial hprep
  have hcComb := NativeCertificate.ofPolyTime_isPolynomial hcomb
  have hcArg_sp : HasPolySpace (cId.prod (cf.comp cPrep)) :=
    hasPolySpace_prod .self (hasPolySpace_comp hSf hcPrep.2)
  have hcYes_sp : HasPolySpace cYes := hasPolySpace_comp hcComb.2 hcArg_sp
  let S_cb : ℕ × ((ℕ × γ) × List δ) → ℕ := fun p => cCond.space p + cYes.space p + cNo.space p
  have hScb_pb : PolyBounded (fun p => (eSt p).length) S_cb :=
    (hcCond.2.add hcYes_sp).add .self
  let cb : NativeCertificate (mapRangeStep f) eSt encAcc :=
    ⟨cb₀.time, S_cb, cb₀.computes.mono_le (fun _ => le_rfl) fun p => by
      dsimp only [cb₀, S_cb, NativeCertificate.branch_space]; split_ifs <;> omega⟩
  have hover_pb : PolyBounded (fun p => (eSt p).length)
      (fun p => cCond.time p + (eSt p).length + cPrep.time p +
        cComb.time (p, f (p.2.1.2, min p.2.1.1 p.1)) + cNo.time p) :=
    ((((hcCond.1.add .self).add hcPrep.1).add
      (hcComb.1.comp (polyBounded_length_of_hasPolySpace hcArg_sp))).add .self)
  obtain ⟨c_ov, d_ov, hov_le⟩ := hover_pb.exists_le
  obtain ⟨ce, de, hf_len⟩ := (polyBounded_length_of_hasPolySpace (c := cf) hSf).exists_le
  have hm_pb := hm.polyBounded
  have hctx_pb := hctx.polyBounded_length
  let L_el : ι → ℕ := fun x => 2 * (encC (ctx x)).length + 2 * m x + 1
  have hLel_pb : PolyBounded (fun x => (encIn x).length) L_el :=
    (((PolyBounded.const 2).mul hctx_pb).add ((PolyBounded.const 2).mul hm_pb)).add (.const 1)
  let E_el : ι → ℕ := fun x => ce * (L_el x + 1) ^ de
  have hEel_pb := NativeCertificate.polyBounded_pow_of_polyBounded hLel_pb ce de
  let B_acc : ι → ℕ := fun x =>
    2 * (2 * m x + 2 * (encC (ctx x)).length + 1) + 1 + m x * (2 * E_el x + 1)
  have hBacc_pb : PolyBounded (fun x => (encIn x).length) B_acc :=
    (((PolyBounded.const 2).mul
      ((((PolyBounded.const 2).mul hm_pb).add
        ((PolyBounded.const 2).mul hctx_pb)).add (.const 1))).add (.const 1)).add
      (hm_pb.mul (((PolyBounded.const 2).mul hEel_pb).add (.const 1)))
  have hB : ∀ x j, j ≤ m x →
      (encAcc (IndexFold.run (mapRangeStep f) j ((m x, ctx x), [])).2).length ≤ B_acc x := by
    intro x j hj
    rw [run_mapRangeStep f (ctx x) hj]
    have hlst := length_encList_le encB ((List.range j).map fun i => f (ctx x, i)) (b := E_el x)
      fun y hy => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
        have hi_lt := List.mem_range.mp hi
        have hlen_in : (encPair encC encUnary (ctx x, i)).length ≤ L_el x := by
          simp only [length_encPair, encUnary_apply, List.length_replicate, L_el]; omega
        exact (hf_len (ctx x, i)).trans
          (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left (Nat.add_le_add_right hlen_in 1) de))
    simp only [List.length_map, List.length_range] at hlst
    have hlst' := hlst.trans (Nat.mul_le_mul_right (2 * E_el x + 1) hj)
    simp only [encAcc, length_encPair, encUnary_apply, List.length_replicate, B_acc]; omega
  have hcnt_pb := hm_b.polyBounded_length
  let S_st : ι → ℕ := fun x => 2 * (encNat (m x)).length + 1 + B_acc x
  have hSst_pb := (((PolyBounded.const 2).mul hcnt_pb).add (.const 1)).add hBacc_pb
  let P_cb : ι → ℕ := fun x => c_ov * (S_st x + 1) ^ d_ov
  have hPcb_pb := NativeCertificate.polyBounded_pow_of_polyBounded hSst_pb c_ov d_ov
  obtain ⟨P, hP_pb, hcomp⟩ := computableInO_snd_indexFold
    (.ofPolyTime hm_b) (.ofPolyTime hinit) cb
    (NativeCertificate.ofPolyTime_isPolynomial hm_b)
    (NativeCertificate.ofPolyTime_isPolynomial hinit) hScb_pb hBacc_pb hB R P_cb hPcb_pb
    fun x j hj hst_len => by
      have hov := (hov_le (IndexFold.run (mapRangeStep f) j ((m x, ctx x), []))).trans
        (Nat.mul_le_mul_left c_ov (Nat.pow_le_pow_left (Nat.add_le_add_right hst_len 1) d_ov))
      have hst_eq : IndexFold.run (mapRangeStep f) j ((m x, ctx x), []) =
          (j, ((m x, ctx x), (List.range j).map fun i => f (ctx x, i))) :=
        Prod.ext (IndexFold.run_index _ _ _) (run_mapRangeStep f (ctx x) hj)
      dsimp only [cb, cb₀, cYes, cId] at hov ⊢
      simp only [NativeCertificate.branch_time, NativeCertificate.comp_time,
        NativeCertificate.prod_time, NativeCertificate.linear_time, Function.comp_apply] at hov ⊢
      by_cases hlt : j < m x
      · have hcond_t : decide ((IndexFold.run (mapRangeStep f) j ((m x, ctx x), [])).1 <
            (IndexFold.run (mapRangeStep f) j ((m x, ctx x), [])).2.1.1) = true := by
          rw [hst_eq]; exact decide_eq_true hlt
        have hcf_t : cf.time ((IndexFold.run (mapRangeStep f) j ((m x, ctx x), [])).2.1.2,
            min (IndexFold.run (mapRangeStep f) j ((m x, ctx x), [])).2.1.1
              (IndexFold.run (mapRangeStep f) j ((m x, ctx x), [])).1) ≤ R x := by
          rw [hst_eq]; dsimp only; rw [Nat.min_eq_right (Nat.le_of_lt hlt)]; exact hR x j hlt
        simp only [hcond_t, ↓reduceIte]
        change cCond.time _ + (_ + (cPrep.time _ + cf.time _) + cComb.time _) ≤ _
        dsimp only [P_cb, S_st] at hov ⊢; omega
      · have hcond_f : decide ((IndexFold.run (mapRangeStep f) j ((m x, ctx x), [])).1 <
            (IndexFold.run (mapRangeStep f) j ((m x, ctx x), [])).2.1.1) = false := by
          rw [hst_eq]; exact decide_eq_false hlt
        simp only [hcond_f, Bool.false_eq_true, ↓reduceIte]
        dsimp only [P_cb, S_st] at hov ⊢; omega
  let cRes : NativeCertificate _ encIn encAcc := ⟨_, _, hcomp⟩
  refine ⟨P, hP_pb, ((NativeCertificate.snd cRes).computes.of_enc_eq fun x => ?_)⟩
  congr 1; exact (congrArg Prod.snd (run_mapRangeStep f (ctx x) (m := m x) le_rfl)).symm

private theorem absorb_step_add (K P₀ P₁ : ℕ) (hK : 1 ≤ K) :
    K * P₀ + P₁ ≤ K * (P₀ + P₁) := by
  calc K * P₀ + P₁ ≤ K * P₀ + K * P₁ := Nat.add_le_add_left (Nat.le_mul_of_pos_left P₁ hK) _
    _ = K * (P₀ + P₁) := (Nat.mul_add K P₀ P₁).symm

private theorem mapRange_group_bound (r_u G P₀ P₁ : ℕ) :
    (r_u + 1) * ((if r_u = 0 then 0 else (G + 1) * P₀) + P₁) ≤
      (r_u * (G + 1) + 1) * (2 * (P₀ + P₁)) := by
  by_cases hr0 : r_u = 0
  · subst hr0; simp only [↓reduceIte, zero_add, one_mul, Nat.zero_mul]; omega
  · simp only [hr0, ↓reduceIte]
    calc (r_u + 1) * ((G + 1) * P₀ + P₁)
        ≤ (2 * r_u) * ((G + 1) * (P₀ + P₁)) :=
          Nat.mul_le_mul (by omega) (absorb_step_add (G + 1) P₀ P₁ (Nat.succ_pos G))
      _ = (r_u * (G + 1)) * (2 * (P₀ + P₁)) := by ring
      _ ≤ (r_u * (G + 1) + 1) * (2 * (P₀ + P₁)) := Nat.mul_le_mul_right _ (Nat.le_succ _)

/-- Standalone per-measurement-word two-pass payload: slices `word` across the `r_u` variable
groups, searches each unrestricted group fiber via `BooleanMeasurements.search` (Pass 1), and when
every fiber is nonempty streams restricted local-cube factor-jet sums via
`CommonCountingAccum.streamGroupJetSum` and returns `some (prodJet J ℓ groupJets)` (Pass 2). -/
def evalMeasPayload (wc : List ℤ × MeasStepCtx) : Option JetRows :=
  let word := wc.1; let ctx := wc.2
  let n' := ctx.1.1; let r_u := ctx.1.2.1; let m_rows := ctx.1.2.2
  let J := ctx.2.1.1; let ℓ := ctx.2.1.2.1; let k' := ctx.2.1.2.2
  let node := ctx.2.2.1.1; let dDen := ctx.2.2.1.2
  let vGroups_t := ctx.2.2.2.1.1; let grpMeas_t := ctx.2.2.2.1.2
  let indE := ctx.2.2.2.2.1.1; let indU := ctx.2.2.2.2.1.2; let grpEqLists := ctx.2.2.2.2.2
  let repOpts := (List.range r_u).map fun g =>
    BooleanMeasurements.search Prod.fst Prod.snd
      ((grpMeas_t.getD g [], (word.drop (g * m_rows)).take m_rows),
        min (2 * n') (vGroups_t.getD g []).length)
  if repOpts.all Option.isSome then
    let xStar := buildBaseAssignment n' r_u vGroups_t (repOpts.map fun o => o.getD [])
    let groupJets := (List.range r_u).map fun g =>
      CommonCountingAccum.streamGroupJetSum evalGroupFactorJet J ℓ
        (min (2 * n') (vGroups_t.getD g []).length)
        ((n', J, ℓ, k'), (node, dDen),
          (vGroups_t.getD g [], grpMeas_t.getD g [], (word.drop (g * m_rows)).take m_rows),
          (indE, indU, xStar), grpEqLists.getD g [])
    some (CommonCountingAccum.prodJet J ℓ groupJets)
  else none

/-- `measurementStepBody` factors into `evalMeasPayload` followed by optional `addJet`
accumulation. -/
theorem measurementStepBody_eq (inp : ((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows)) :
    measurementStepBody inp =
      (evalMeasPayload (inp.1.2, inp.2.1)).elim inp.2
        (fun y => (inp.2.1, addJet inp.2.1.2.1.1 inp.2.1.2.1.2.1 inp.2.2 y)) := by
  unfold measurementStepBody evalMeasPayload; dsimp only; split_ifs <;> rfl

/-- Uniform `ComputableInO` runtime and global `PolyBounded` workspace bound for `evalMeasPayload`,
running in `(r_u * (2 ^ maxGroupDim + 1) + 1) * P` steps and `P` workspace. -/
theorem exists_computableInO_measPayload :
    ∃ P : List ℤ × MeasStepCtx → ℕ,
      PolyBounded (fun wc => (encPair (encList encIntBin) encMeasStepCtx wc).length) P ∧
      ComputableInO evalMeasPayload (encPair (encList encIntBin) encMeasStepCtx)
        (encOption (encList (encList encIntBin)))
        (fun wc =>
          (wc.2.1.2.1 * (2 ^ maxGroupDim wc.2.1.1 wc.2.1.2.1 wc.2.2.2.2.1.1 + 1) + 1) * P wc)
        P := by
  let eWC := encPair (encList encIntBin) encMeasStepCtx
  have hru_wc : ComputableInPolyTime (fun wc : List ℤ × MeasStepCtx => wc.2.1.2.1)
      eWC encUnary := by
    have hctx := snd (encList encIntBin) encMeasStepCtx
    unfold encMeasStepCtx at hctx
    exact hctx.fst'.snd'.fst'
  have hprepS : ComputableInPolyTime
      (fun p : (List ℤ × MeasStepCtx) × ℕ =>
        ((p.1.2.2.2.2.1.2.getD p.2 [], (p.1.1.drop (p.2 * p.1.2.1.2.2)).take p.1.2.1.2.2),
          min (2 * p.1.2.1.1) (p.1.2.2.2.2.1.1.getD p.2 []).length))
      (encPair eWC encUnary)
      (encPair (encPair (encList (encList encIntBin)) (encList encIntBin)) encUnary) := by
    have hwc := fst eWC encUnary; have hg := snd eWC encUnary
    unfold eWC encMeasStepCtx at hwc
    have hword := hwc.fst'; have hctx := hwc.snd'
    have hn' := hctx.fst'.fst'; have hm := hctx.fst'.snd'.snd'
    have hvgs := hctx.snd'.snd'.snd'.fst'.fst'; have hgm := hctx.snd'.snd'.snd'.fst'.snd'
    have hCtg := (listGetD (encA := encList (encList encIntBin)) []).comp (hgm.prod hg)
    have hyg := bi_listTakeWithInput
      (bi_listDropWithInput hword (bi_unary_mul.comp (hg.prod hm))) hm
    have hVg := (listGetD (encA := encList encNat) []).comp (hvgs.prod hg)
    have hdg := bi_unary_min.comp
      ((bi_unary_mul.comp ((const 2).prod hn')).prod ((length_list encNat).comp hVg))
    exact (hCtg.prod hyg).prod hdg
  have hM_pr := fst (encList (encList encIntBin)) (encList encIntBin)
  have ht_pr := snd (encList (encList encIntBin)) (encList encIntBin)
  let cSBase := BooleanMeasurements.searchCertificate hM_pr ht_pr
  let cPrepS := NativeCertificate.ofPolyTime hprepS
  let cSOne := cSBase.comp cPrepS
  have hcPrepS := NativeCertificate.ofPolyTime_isPolynomial hprepS
  have hcSOne_sp : HasPolySpace cSOne :=
    hasPolySpace_comp
      (BooleanMeasurements.polyBounded_searchCertificate_space hM_pr ht_pr) hcPrepS.2
  obtain ⟨ovS, hovS_pb, hovS_eq⟩ :=
    BooleanMeasurements.exists_polyBounded_searchCertificate_time hM_pr ht_pr
  obtain ⟨cs1, ds1, hs1_le⟩ :=
    (hcPrepS.1.add (hovS_pb.comp hprepS.polyBounded_length)).exists_le
  let Ps1 : List ℤ × MeasStepCtx → ℕ := fun wc =>
    cs1 * (2 * (eWC wc).length + 2 * wc.2.1.2.1 + 1 + 1) ^ ds1
  have hPs1_pb := NativeCertificate.polyBounded_pow_of_polyBounded
    ((((PolyBounded.const 2).mul .self).add
      ((PolyBounded.const 2).mul hru_wc.polyBounded)).add (.const 1)) cs1 ds1
  obtain ⟨Pm1, hPm1_pb, hcomp1⟩ := exists_computableInO_mapRange hru_wc
    id' hcSOne_sp cSOne.computes
    (fun wc => if wc.2.1.2.1 = 0 then 0 else
      (2 ^ maxGroupDim wc.2.1.1 wc.2.1.2.1 wc.2.2.2.2.1.1 + 1) * Ps1 wc)
    fun wc g hg => by
      have hr0 : wc.2.1.2.1 ≠ 0 := by omega
      simp only [hr0, ↓reduceIte]
      have hlen : (encPair eWC encUnary (wc, g)).length ≤
          2 * (eWC wc).length + 2 * wc.2.1.2.1 + 1 := by
        simp only [length_encPair, encUnary_apply, List.length_replicate]; omega
      have hov := (hs1_le (wc, g)).trans
        (Nat.mul_le_mul_left cs1 (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) ds1))
      have hd_le := min_length_le_maxGroupDim (n' := wc.2.1.1) (vGroups_t := wc.2.2.2.2.1.1) hg
      have hpow_le := Nat.pow_le_pow_right Nat.zero_lt_two hd_le
      change cPrepS.time (wc, g) + cSBase.time _ ≤ _
      rw [hovS_eq]
      calc cPrepS.time (wc, g) + (2 ^ min (2 * wc.2.1.1) (wc.2.2.2.2.1.1.getD g []).length + 1) *
            ovS _
          ≤ (2 ^ maxGroupDim wc.2.1.1 wc.2.1.2.1 wc.2.2.2.2.1.1 + 1) * ovS _ +
              cPrepS.time (wc, g) := by
            rw [Nat.add_comm]
            exact Nat.add_le_add_right
              (Nat.mul_le_mul_right _ (Nat.succ_le_succ hpow_le)) _
        _ ≤ (2 ^ maxGroupDim wc.2.1.1 wc.2.1.2.1 wc.2.2.2.2.1.1 + 1) *
              (ovS _ + cPrepS.time (wc, g)) := absorb_step_add _ _ _ (Nat.succ_pos _)
        _ ≤ (2 ^ maxGroupDim wc.2.1.1 wc.2.1.2.1 wc.2.2.2.2.1.1 + 1) * Ps1 wc :=
            Nat.mul_le_mul_left _ (by dsimp only [cPrepS, Ps1] at hov ⊢; omega)
  let P_pass1 : List ℤ × MeasStepCtx → ℕ := fun wc => 2 * (Ps1 wc + Pm1 wc)
  have hPpass1_pb : PolyBounded (fun wc => (eWC wc).length) P_pass1 :=
    (PolyBounded.const 2).mul (hPs1_pb.add hPm1_pb)
  let cPass1 : NativeCertificate _ eWC (encList (encOption encBits)) :=
    ⟨fun wc => (wc.2.1.2.1 * (2 ^ maxGroupDim wc.2.1.1 wc.2.1.2.1 wc.2.2.2.2.1.1 + 1) + 1) *
        P_pass1 wc, Pm1,
      hcomp1.mono_le (fun wc => mapRange_group_bound _ _ _ _) fun _ => le_rfl⟩
  let eWR := encPair eWC (encList (encOption encBits))
  let eWX := encPair eWC encBits
  have hcond : ComputableInPolyTime
      (fun wr : (List ℤ × MeasStepCtx) × List (Option (List Bool)) => wr.2.all Option.isSome)
      eWR encBool :=
    bi_allWith (snd eWC (encList (encOption encBits))) (optionIsSome (snd eWR (encOption encBits)))
  have hxStar : ComputableInPolyTime
      (fun wr : (List ℤ × MeasStepCtx) × List (Option (List Bool)) =>
        (wr.1, buildBaseAssignment wr.1.2.1.1 wr.1.2.1.2.1 wr.1.2.2.2.2.1.1
          (wr.2.map fun o => o.getD []))) eWR eWX := by
    have hwc := fst eWC (encList (encOption encBits))
    have hro := snd eWC (encList (encOption encBits))
    have hctx := hwc.snd'
    unfold encMeasStepCtx at hctx
    have hreps := bi_mapWithId (optionGetDWithInput (snd eWR (encOption encBits)) (const [])) hro
    have hb := computableInPolyTime_buildBaseAssignment hctx.fst'.fst'
      hctx.fst'.snd'.fst' hctx.snd'.snd'.snd'.fst'.fst' hreps
    exact hwc.prod hb
  have hru_wx : ComputableInPolyTime (fun wx : (List ℤ × MeasStepCtx) × List Bool => wx.1.2.1.2.1)
      eWX encUnary := hru_wc.comp (fst eWC encBits)
  let eWXG := encPair eWX encUnary
  have hJ_g : ComputableInPolyTime (fun p : ((List ℤ × MeasStepCtx) × List Bool) × ℕ =>
      p.1.1.2.2.1.1) eWXG encUnary := by
    have hp1 := fst eWX encUnary
    unfold eWX eWC encMeasStepCtx at hp1
    exact hp1.fst'.snd'.snd'.fst'.fst'
  have hℓ_g : ComputableInPolyTime (fun p : ((List ℤ × MeasStepCtx) × List Bool) × ℕ =>
      p.1.1.2.2.1.2.1) eWXG encUnary := by
    have hp1 := fst eWX encUnary
    unfold eWX eWC encMeasStepCtx at hp1
    exact hp1.fst'.snd'.snd'.fst'.snd'.fst'
  have hd_g : ComputableInPolyTime (fun p : ((List ℤ × MeasStepCtx) × List Bool) × ℕ =>
      min (2 * p.1.1.2.1.1) (p.1.1.2.2.2.2.1.1.getD p.2 []).length) eWXG encUnary := by
    have hp1 := fst eWX encUnary; have hg := snd eWX encUnary
    unfold eWX eWC encMeasStepCtx at hp1
    have hctx := hp1.fst'.snd'
    have hVg := (listGetD (encA := encList encNat) []).comp
      (hctx.snd'.snd'.snd'.fst'.fst'.prod hg)
    exact bi_unary_min.comp
      ((bi_unary_mul.comp ((const 2).prod hctx.fst'.fst')).prod ((length_list encNat).comp hVg))
  have hctx_g : ComputableInPolyTime (fun p : ((List ℤ × MeasStepCtx) × List Bool) × ℕ =>
      ((p.1.1.2.1.1, p.1.1.2.2.1.1, p.1.1.2.2.1.2.1, p.1.1.2.2.1.2.2),
        (p.1.1.2.2.2.1.1, p.1.1.2.2.2.1.2),
        (p.1.1.2.2.2.2.1.1.getD p.2 [], p.1.1.2.2.2.2.1.2.getD p.2 [],
          (p.1.1.1.drop (p.2 * p.1.1.2.1.2.2)).take p.1.1.2.1.2.2),
        (p.1.1.2.2.2.2.2.1.1, p.1.1.2.2.2.2.2.1.2, p.1.2),
        p.1.1.2.2.2.2.2.2.getD p.2 [])) eWXG encGroupEvalCtx := by
    have hp1 := fst eWX encUnary; have hg := snd eWX encUnary
    unfold eWX eWC encMeasStepCtx at hp1
    unfold encGroupEvalCtx
    have hword := hp1.fst'.fst'; have hctx := hp1.fst'.snd'; have hx := hp1.snd'
    have hc1 := hctx.fst'; have hc2 := hctx.snd'
    have hm := hc1.snd'.snd'
    have hVg := (listGetD (encA := encList encNat) []).comp (hc2.snd'.snd'.fst'.fst'.prod hg)
    have hCtg := (listGetD (encA := encList (encList encIntBin)) []).comp
      (hc2.snd'.snd'.fst'.snd'.prod hg)
    have hyg := bi_listTakeWithInput
      (bi_listDropWithInput hword (bi_unary_mul.comp (hg.prod hm))) hm
    have heqs := (listGetD (encA := encList encGroupEqEntry) []).comp
      (hc2.snd'.snd'.snd'.snd'.prod hg)
    exact (hc1.fst'.prod hc2.fst').prod
      (hc2.snd'.fst'.prod ((hVg.prod (hCtg.prod hyg)).prod
        ((hc2.snd'.snd'.snd'.fst'.fst'.prod (hc2.snd'.snd'.snd'.fst'.snd'.prod hx)).prod heqs)))
  obtain ⟨Pg0, hPg0_pb, hstreamOne⟩ := CommonCountingAccum.computableInO_streamGroupJetSum
    hJ_g hℓ_g hd_g hctx_g computableInPolyTime_evalGroupFactorJet
  obtain ⟨cg1, dg1, hg1_le⟩ := hPg0_pb.exists_le
  let Pg1 : (List ℤ × MeasStepCtx) × List Bool → ℕ := fun wx =>
    cg1 * (2 * (eWX wx).length + 2 * wx.1.2.1.2.1 + 1 + 1) ^ dg1
  have hPg1_pb := NativeCertificate.polyBounded_pow_of_polyBounded
    ((((PolyBounded.const 2).mul .self).add
      ((PolyBounded.const 2).mul hru_wx.polyBounded)).add (.const 1)) cg1 dg1
  obtain ⟨Pm2, hPm2_pb, hcomp2⟩ := exists_computableInO_mapRange hru_wx
    id' hPg0_pb hstreamOne
    (fun wx => if wx.1.2.1.2.1 = 0 then 0 else
      (2 ^ maxGroupDim wx.1.2.1.1 wx.1.2.1.2.1 wx.1.2.2.2.2.1.1 + 1) * Pg1 wx)
    fun wx g hg => by
      have hr0 : wx.1.2.1.2.1 ≠ 0 := by omega
      simp only [hr0, ↓reduceIte]
      have hlen : (eWXG (wx, g)).length ≤ 2 * (eWX wx).length + 2 * wx.1.2.1.2.1 + 1 := by
        simp only [eWXG, length_encPair, encUnary_apply, List.length_replicate]; omega
      have hov := (hg1_le (wx, g)).trans
        (Nat.mul_le_mul_left cg1 (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) dg1))
      have hd_le := min_length_le_maxGroupDim (n' := wx.1.2.1.1) (vGroups_t := wx.1.2.2.2.2.1.1) hg
      exact Nat.mul_le_mul (Nat.succ_le_succ (Nat.pow_le_pow_right Nat.zero_lt_two hd_le)) hov
  let cGrpJets : NativeCertificate _ eWX (encList encJet) :=
    ⟨fun wx =>
        (wx.1.2.1.2.1 * (2 ^ maxGroupDim wx.1.2.1.1 wx.1.2.1.2.1 wx.1.2.2.2.2.1.1 + 1) + 1) *
          (2 * (Pg1 wx + Pm2 wx)), Pm2,
      hcomp2.mono_le (fun _ => mapRange_group_bound _ _ _ _) fun _ => le_rfl⟩
  have hprodSome : ComputableInPolyTime
      (fun wj : ((List ℤ × MeasStepCtx) × List Bool) × List JetRows =>
        some (CommonCountingAccum.prodJet wj.1.1.2.2.1.1 wj.1.1.2.2.1.2.1 wj.2))
      (encPair eWX (encList encJet)) (encOption encJet) := by
    have hwj1 := fst eWX (encList encJet); have hwj2 := snd eWX (encList encJet)
    have hJ_p : ComputableInPolyTime
        (fun wj : ((List ℤ × MeasStepCtx) × List Bool) × List JetRows => wj.1.1.2.2.1.1)
        (encPair eWX (encList encJet)) encUnary := by
      unfold eWX eWC encMeasStepCtx; exact hwj1.fst'.snd'.snd'.fst'.fst'
    have hℓ_p : ComputableInPolyTime
        (fun wj : ((List ℤ × MeasStepCtx) × List Bool) × List JetRows => wj.1.1.2.2.1.2.1)
        (encPair eWX (encList encJet)) encUnary := by
      unfold eWX eWC encMeasStepCtx; exact hwj1.fst'.snd'.snd'.fst'.snd'.fst'
    exact (optionSome encJet).comp
      (CommonCountingAccum.computableInPolyTime_prodJet hJ_p hℓ_p hwj2)
  let cCondWR := NativeCertificate.ofPolyTime hcond
  let cXStar := NativeCertificate.ofPolyTime hxStar
  let cProdS := NativeCertificate.ofPolyTime hprodSome
  have hnoneWR : ComputableInPolyTime (fun _ => (none : Option JetRows)) eWR (encOption encJet) :=
    const none
  let cNoWR := NativeCertificate.ofPolyTime hnoneWR
  let cIdWC := NativeCertificate.linear (ei := eWC) (ComputableInO.of_eq fun _ => rfl)
  let cIdWX := NativeCertificate.linear (ei := eWX) (ComputableInO.of_eq fun _ => rfl)
  let cYesWR := (cProdS.comp (cIdWX.prod cGrpJets)).comp cXStar
  let cBrWR := NativeCertificate.branch cCondWR cYesWR cNoWR
  let cFull := cBrWR.comp (cIdWC.prod cPass1)
  have hspX := NativeCertificate.ofPolyTime_isPolynomial hxStar
  have hspP := NativeCertificate.ofPolyTime_isPolynomial hprodSome
  have hspC := NativeCertificate.ofPolyTime_isPolynomial hcond
  have hspN := NativeCertificate.ofPolyTime_isPolynomial hnoneWR
  have hspWXJ : HasPolySpace (cIdWX.prod cGrpJets) := hasPolySpace_prod .self hPm2_pb
  have hspY : HasPolySpace cYesWR := hasPolySpace_comp (hasPolySpace_comp hspP.2 hspWXJ) hspX.2
  have hspBr : HasPolySpace cBrWR := ((hspC.2.add hspY).add hspN.2).mono fun p => by
    dsimp only [cBrWR, cCondWR, cNoWR]; simp only [NativeCertificate.branch_space]
    split_ifs <;> omega
  have hspWCR : HasPolySpace (cIdWC.prod cPass1) := hasPolySpace_prod .self hPm1_pb
  have hcFull_sp : HasPolySpace cFull := hasPolySpace_comp hspBr hspWCR
  have hlenWR_pb := polyBounded_length_of_hasPolySpace hspWCR
  have hlenWX_pb := (polyBounded_length_of_hasPolySpace hspX.2).comp hlenWR_pb
  have hlenWXJ_pb := (polyBounded_length_of_hasPolySpace hspWXJ).comp hlenWX_pb
  let wr_fn (wc : List ℤ × MeasStepCtx) : (List ℤ × MeasStepCtx) × List (Option (List Bool)) :=
    (wc, (List.range wc.2.1.2.1).map fun g =>
      BooleanMeasurements.search Prod.fst Prod.snd
        ((wc.2.2.2.2.1.2.getD g [], (wc.1.drop (g * wc.2.1.2.2)).take wc.2.1.2.2),
          min (2 * wc.2.1.1) (wc.2.2.2.2.1.1.getD g []).length))
  let wx_fn (wc : List ℤ × MeasStepCtx) : (List ℤ × MeasStepCtx) × List Bool :=
    let wr := wr_fn wc
    (wr.1, buildBaseAssignment wr.1.2.1.1 wr.1.2.1.2.1 wr.1.2.2.2.2.1.1
      (wr.2.map fun o => o.getD []))
  let wj_fn (wc : List ℤ × MeasStepCtx) : ((List ℤ × MeasStepCtx) × List Bool) × List JetRows :=
    let wx := wx_fn wc
    (wx, (List.range wx.1.2.1.2.1).map fun g =>
      CommonCountingAccum.streamGroupJetSum evalGroupFactorJet wx.1.2.2.1.1 wx.1.2.2.1.2.1
        (min (2 * wx.1.2.1.1) (wx.1.2.2.2.2.1.1.getD g []).length)
        ((wx.1.2.1.1, wx.1.2.2.1.1, wx.1.2.2.1.2.1, wx.1.2.2.1.2.2),
          (wx.1.2.2.2.1.1, wx.1.2.2.2.1.2),
          (wx.1.2.2.2.2.1.1.getD g [], wx.1.2.2.2.2.1.2.getD g [],
            (wx.1.1.drop (g * wx.1.2.1.2.2)).take wx.1.2.1.2.2),
          (wx.1.2.2.2.2.2.1.1, wx.1.2.2.2.2.2.1.2, wx.2), wx.1.2.2.2.2.2.2.getD g []))
  let P_all : List ℤ × MeasStepCtx → ℕ := fun wc =>
    P_pass1 wc + 2 * (Pg1 (wx_fn wc) + Pm2 (wx_fn wc)) + (eWC wc).length +
      cCondWR.time (wr_fn wc) + cNoWR.time (wr_fn wc) + cXStar.time (wr_fn wc) +
      (eWX (wx_fn wc)).length + cProdS.time (wj_fn wc) + cFull.space wc
  have hPall_pb : PolyBounded (fun wc => (eWC wc).length) P_all :=
    (((((((((hPpass1_pb.add ((PolyBounded.const 2).mul
      ((hPg1_pb.comp hlenWX_pb).add (hPm2_pb.comp hlenWX_pb)))).add .self).add
      (hspC.1.comp hlenWR_pb)).add (hspN.1.comp hlenWR_pb)).add
      (hspX.1.comp hlenWR_pb)).add hlenWX_pb).add (hspP.1.comp hlenWXJ_pb)).add hcFull_sp))
  refine ⟨P_all, hPall_pb, (cFull.computes.of_enc_eq fun _ => rfl).mono_le (fun wc => ?_)
    fun wc => by dsimp only [P_all]; omega⟩
  set K := wc.2.1.2.1 * (2 ^ maxGroupDim wc.2.1.1 wc.2.1.2.1 wc.2.2.2.2.1.1 + 1) + 1
  have hK : 1 ≤ K := Nat.succ_pos _
  dsimp only [cFull, cBrWR, cYesWR, cIdWC, cIdWX, cPass1, cGrpJets]
  simp only [NativeCertificate.comp_time, NativeCertificate.prod_time,
    NativeCertificate.branch_time, NativeCertificate.linear_time, Function.comp_apply]
  split_ifs
  · change ((eWC wc).length + K * P_pass1 wc) +
        (cCondWR.time (wr_fn wc) + (cXStar.time (wr_fn wc) +
          (((eWX (wx_fn wc)).length + K * (2 * (Pg1 (wx_fn wc) + Pm2 (wx_fn wc)))) +
            cProdS.time (wj_fn wc)))) ≤ K * P_all wc
    dsimp only [P_all]
    have h1 := Nat.le_mul_of_pos_left ((eWC wc).length + cCondWR.time (wr_fn wc) +
      cXStar.time (wr_fn wc) + (eWX (wx_fn wc)).length + cProdS.time (wj_fn wc)) hK
    simp only [Nat.mul_add] at h1 ⊢; omega
  · change ((eWC wc).length + K * P_pass1 wc) +
        (cCondWR.time (wr_fn wc) + cNoWR.time (wr_fn wc)) ≤ K * P_all wc
    dsimp only [P_all]
    have h1 := Nat.le_mul_of_pos_left
      ((eWC wc).length + cCondWR.time (wr_fn wc) + cNoWR.time (wr_fn wc)) hK
    simp only [Nat.mul_add] at h1 ⊢; omega

end LoopCertificates

end Cslib.Complexity.SubexponentialSAT.SparsePolyCounter
