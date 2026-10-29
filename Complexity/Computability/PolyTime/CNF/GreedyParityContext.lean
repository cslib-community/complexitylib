/-
Copyright (c) 2026 Anton Kovsharov, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.PolyTime.CNF.GreedyParitySearch
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Greedy parity search with an encoded context

The selector and greedy program are those of `GreedyParitySearch`; this module supplies one
native machine for a counter on `(context, rows)`. The context is part of every live state and
counter input. Its encoding is charged even when candidate enumeration or the outer loop is empty.
This closes the fixed-counter interface gap without constructing the common-zero counter or the
initial Tanner matrix of [OpenAI2026ETH], §§6.2–6.3 (pp. 42–43).

## Main definitions

* `GreedyContext.selectCertificate`: uniform context-dependent candidate selection.
* `GreedyContext.greedyCertificate`: the existing `greedyParityRows` on a runtime context.

## Main results

* `GreedyContext.computableInO_greedy`: independent time and polynomial-workspace bounds.
* `GreedyContext.count_greedy_eq_card_sat`: the fixed-counter correctness theorem pointwise.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§6.2–6.3.

The certificate construction extends Anton Kovsharov's `GreedyParitySearch` implementation.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.GreedyContext

open Finset Cslib.BitString Cslib.GenericRAM Turing.MultiTapeTM

variable {C : Type} (encC : C ↪ List Bool)

/-- Full selector input: context, unary width and tuple length, and retained rows. -/
def encInput : (C × ℕ × ℕ × List (List Bool)) ↪ List Bool :=
  encPair encC encSelectBestIn

/-- Full greedy input: context, unary round parameter, width and tuple length, and rows. -/
def encGreedyInput : (C × ℕ × ℕ × ℕ × List (List Bool)) ↪ List Bool :=
  encPair encC encGreedyIn

/-- The original selector accumulator with the counter's runtime context retained. -/
private def encAcc : (C × SelectBestAcc) ↪ List Bool := encPair encC encSelectBestAcc

variable {encC}

end Cslib.Logic.PL.CNF.GreedyContext
end

public section
namespace Cslib.Logic.PL.CNF.GreedyContext

open Finset Cslib.BitString Cslib.GenericRAM Turing.MultiTapeTM
variable {C : Type} {encC : C ↪ List Bool}

private def augment (s : ℕ × C × SelectBestAcc) : C × List (List Bool) :=
  (s.2.1, augCandidateRows (s.1, s.2.2))

private theorem augment_polyTime : ComputableInPolyTime (augment (C := C))
    (encPair encNat (encAcc encC)) (encPair encC (encList encBits)) := by
  unfold augment encAcc
  exact (by fun_prop : ComputableInPolyTime (fun s : ℕ × C × SelectBestAcc => s.2.1)
    (encPair encNat (encPair encC encSelectBestAcc)) encC).prod
      (computableInPolyTime_augCandidateRows.comp (by fun_prop))

private def finish (p : (ℕ × C × SelectBestAcc) × ℕ) : C × SelectBestAcc :=
  (p.1.2.1, finishSelectBestStep ((p.1.1, p.1.2.2), p.2))

private theorem finish_polyTime : ComputableInPolyTime (finish (C := C))
    (encPair (encPair encNat (encAcc encC)) encNat) (encAcc encC) := by
  unfold finish encAcc
  exact (by fun_prop : ComputableInPolyTime
    (fun p : (ℕ × C × SelectBestAcc) × ℕ => p.1.2.1)
    (encPair (encPair encNat (encPair encC encSelectBestAcc)) encNat) encC).prod
      (computableInPolyTime_finishSelectBestStep.comp (by fun_prop))

private def step (count : C × List (List Bool) → ℕ)
    (s : ℕ × C × SelectBestAcc) : C × SelectBestAcc :=
  (s.2.1, selectBestStep (fun rows => count (s.2.1, rows)) (s.1, s.2.2))

private noncomputable def stepCertificate {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encPair encC (encList encBits)) encNat) :
    NativeCertificate (step count) (encPair encNat (encAcc encC)) (encAcc encC) :=
  let cId := NativeCertificate.linear (ComputableInO.of_linear
    (.of_eq fun _ : ℕ × C × SelectBestAcc => rfl))
  ((NativeCertificate.ofPolyTime finish_polyTime).comp
    (cId.prod (cCount.comp (NativeCertificate.ofPolyTime augment_polyTime)))).congr fun _ => rfl

private theorem run_eq (count : C × List (List Bool) → ℕ) (c : C)
    (acc : SelectBestAcc) (j : ℕ) :
    IndexFold.run (step count) j (c, acc) =
      (j, c, (IndexFold.run (selectBestStep (fun rows => count (c, rows))) j acc).2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [IndexFold.run_succ, ih, IndexFold.run_succ]
    simp only [IndexFold.step, step, IndexFold.run_index]
    congr 3
    exact Prod.ext (IndexFold.run_index _ _ _).symm rfl

private theorem run_params (count : C × List (List Bool) → ℕ) (c : C)
    (m P j : ℕ) (rows : List (List Bool)) :
    let s := IndexFold.run (step count) j (c, (m, P), rows, none)
    s.2.1 = c ∧ s.2.2.1 = (m, P) ∧ s.2.2.2.1 = rows := by
  induction j with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ j ih =>
    simp only [IndexFold.run_succ, IndexFold.step, step, selectBestStep,
      ih.1, ih.2.1, ih.2.2, and_self]

private def countIn (a : C × ℕ × ℕ × List (List Bool)) : ℕ :=
  candidateTupleCount a.2.1 a.2.2.1

private theorem countIn_polyTime :
    ComputableInPolyTime (countIn (C := C)) (encInput encC) encNat := by
  unfold countIn encInput encSelectBestIn
  exact computableInPolyTime_candidateTupleCount' (by fun_prop) (by fun_prop)

private def initIn (a : C × ℕ × ℕ × List (List Bool)) : C × SelectBestAcc :=
  (a.1, (a.2.1, a.2.2.1), a.2.2.2, none)

private theorem initIn_polyTime :
    ComputableInPolyTime (initIn (C := C)) (encInput encC) (encAcc encC) := by
  unfold initIn encInput encSelectBestIn encAcc encSelectBestAcc
  fun_prop

private def extract (r : ℕ × C × SelectBestAcc) : List Bool :=
  r.2.2.2.2.elim (List.replicate r.2.2.1.1 false) Prod.fst

private theorem extract_polyTime :
    ComputableInPolyTime (extract (C := C)) (encPair encNat (encAcc encC)) encBits := by
  unfold extract encAcc encSelectBestAcc
  let eBest := encPair encBits encNat
  let encRest := encPair (encList encBits) (encOption eBest)
  let encS := encPair (encPair encUnary encUnary) encRest
  have hacc := (ComputableInPolyTime.snd encC encS).comp
    (ComputableInPolyTime.snd encNat (encPair encC encS))
  have hm := (ComputableInPolyTime.fst encUnary encUnary).comp
    ((ComputableInPolyTime.fst (encPair encUnary encUnary) encRest).comp hacc)
  have hopt := (ComputableInPolyTime.snd (encList encBits) (encOption eBest)).comp
    ((ComputableInPolyTime.snd (encPair encUnary encUnary) encRest).comp hacc)
  exact ComputableInPolyTime.optionElimWithInput hopt
    ((ComputableInPolyTime.bitsReplicate false).comp hm)
    ((ComputableInPolyTime.fst encBits encNat).comp
      (ComputableInPolyTime.snd (encPair encNat (encPair encC encS)) eBest))

/-- One fixed native selector for all encoded contexts. Empty candidate spaces return the zero
row, exactly as `selectBestTestRow`; otherwise its first-minimum semantics are unchanged. -/
noncomputable def selectCertificate {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encPair encC (encList encBits)) encNat) :
    NativeCertificate (fun a : C × ℕ × ℕ × List (List Bool) =>
      selectBestTestRow (fun rows => count (a.1, rows)) a.2.1 a.2.2.1 a.2.2.2)
      (encInput encC) encBits :=
  ((NativeCertificate.ofPolyTime extract_polyTime).comp
    (IndexFold.certificate (NativeCertificate.ofPolyTime countIn_polyTime)
      (NativeCertificate.ofPolyTime initIn_polyTime) (stepCertificate cCount))).congr fun a => by
    have hp := (run_params count a.1 a.2.1 a.2.2.1
      (candidateTupleCount a.2.1 a.2.2.1) a.2.2.2).2.1
    rw [run_eq] at hp
    simp only [Function.comp_apply, countIn, initIn, run_eq, extract,
      selectBestTestRow, show (IndexFold.run
        (selectBestStep (fun rows => count (a.1, rows)))
        (candidateTupleCount a.2.1 a.2.2.1) ((a.2.1, a.2.2.1), a.2.2.2, none)).2.1.1 = a.2.1
        by rw [hp]]

private def appendRow (p : (C × ℕ × ℕ × List (List Bool)) × List Bool) :
    C × ℕ × ℕ × List (List Bool) :=
  (p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2 ++ [p.2])

private theorem appendRow_polyTime : ComputableInPolyTime (appendRow (C := C))
    (encPair (encInput encC) encBits) (encInput encC) := by
  unfold appendRow encInput encSelectBestIn
  fun_prop

private def outerStep (count : C × List (List Bool) → ℕ)
    (s : C × ℕ × ℕ × List (List Bool)) : C × ℕ × ℕ × List (List Bool) :=
  (s.1, s.2.1, s.2.2.1, s.2.2.2 ++
    [selectBestTestRow (fun rows => count (s.1, rows)) s.2.1 s.2.2.1 s.2.2.2])

private theorem outerStep_iterate (count : C × List (List Bool) → ℕ) (c : C)
    (m P i : ℕ) (rows : List (List Bool)) :
    (outerStep count)^[i] (c, m, P, rows) =
      (c, m, P, greedyParityRowsAt (fun rows => count (c, rows)) m P rows i) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', ih, outerStep, greedyParityRowsAt_succ]

private noncomputable def outerCertificate {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encPair encC (encList encBits)) encNat) :
    NativeCertificate (outerStep count) (encInput encC) (encInput encC) :=
  let cId := NativeCertificate.linear (ComputableInO.of_linear
    (.of_eq fun _ : C × ℕ × ℕ × List (List Bool) => rfl))
  ((NativeCertificate.ofPolyTime appendRow_polyTime).comp
    (cId.prod (selectCertificate cCount))).congr fun _ => rfl

private def roundCount (a : C × ℕ × ℕ × ℕ × List (List Bool)) : ℕ := 3 * a.2.1

private theorem roundCount_polyTime :
    ComputableInPolyTime (roundCount (C := C)) (encGreedyInput encC) encNat := by
  unfold roundCount encGreedyInput encGreedyIn
  exact ComputableInPolyTime.unary_to_binary.comp (by fun_prop)

private def outerInit (a : C × ℕ × ℕ × ℕ × List (List Bool)) :
    C × ℕ × ℕ × List (List Bool) := (a.1, a.2.2)

private theorem outerInit_polyTime :
    ComputableInPolyTime (outerInit (C := C)) (encGreedyInput encC) (encInput encC) := by
  unfold outerInit encGreedyInput encGreedyIn encInput
  fun_prop

/-- One fixed machine runs `3n` greedy rounds for the runtime context. The context survives every
candidate and round; the returned rows are the original `greedyParityRows` specialization. -/
noncomputable def greedyCertificate {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encPair encC (encList encBits)) encNat) :
    NativeCertificate (fun a : C × ℕ × ℕ × ℕ × List (List Bool) =>
      greedyParityRows (fun rows => count (a.1, rows)) a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
      (encGreedyInput encC) (encList encBits) :=
  (NativeCertificate.snd (NativeCertificate.snd (NativeCertificate.snd
    (NativeCertificate.iterate (NativeCertificate.ofPolyTime roundCount_polyTime)
      (NativeCertificate.ofPolyTime outerInit_polyTime) (outerCertificate cCount))))).congr
    fun ⟨_, _, _, _, _⟩ => by simp only [roundCount, outerInit, outerStep_iterate]; rfl

/-- The existing Lemma 6.2 correctness theorem, specialized at a runtime context. Positivity,
initial support, and counter agreement on the stated bounded candidate systems are essential.
This statement constructs neither that counter nor the initial rows. -/
theorem count_greedy_eq_card_sat {V : Type*} [Fintype V] [DecidableEq V]
    (count : C × List (List Bool) → ℕ) (c : C) (φ : CNF V) {P : ℕ}
    (hn : 1 ≤ Fintype.card V) (hP : 1 ≤ P) {initRows : List (List Bool)}
    (hinit_len : ∀ r ∈ initRows, r.length = φ.length)
    (hcount : ∀ rows, (∀ r ∈ rows, r.length = φ.length) →
      rows.length ≤ initRows.length + 3 * Fintype.card V →
      (∀ r ∈ rows, r ∈ initRows ∨ r.count true ≤ P) →
      count (c, rows) = numPassing φ.violations (rows.map (ofList φ.length)))
    (hinit : ∀ σ : V → Bool,
      PassesTests φ.violations (initRows.map (ofList φ.length)) σ →
        φ.eval σ = false → φ.length ≤ P * weight (φ.violations σ)) :
    count (c, greedyParityRows (fun rows => count (c, rows))
      (Fintype.card V) φ.length P initRows) =
      #{σ : V → Bool | φ.eval σ = true} :=
  countSys_greedyParityRows_eq_card_sat φ hn hP hinit_len hcount hinit

private theorem input_le (c : C) (m P : ℕ) (rows : List (List Bool)) :
    (encC c).length ≤ (encInput encC (c, m, P, rows)).length ∧
    m ≤ (encInput encC (c, m, P, rows)).length ∧
    P ≤ (encInput encC (c, m, P, rows)).length ∧
    (encList encBits rows).length ≤ (encInput encC (c, m, P, rows)).length := by
  simp only [encInput, encSelectBestIn, length_encPair, encUnary_apply, List.length_replicate]
  exact ⟨by omega, by omega, by omega, by omega⟩

private theorem select_bounds {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encPair encC (encList encBits)) encNat)
    (hSpace : PolyBounded (fun r => (encPair encC (encList encBits) r).length) cCount.space) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧ Monotone poly ∧
      (∀ a : C × ℕ × ℕ × List (List Bool),
        (∀ R : ℕ,
          (∀ j ≤ candidateTupleCount a.2.1 a.2.2.1,
            cCount.time (a.1, a.2.2.2 ++
              [materializeTestRow a.2.1 (decodeTestTuple a.2.1 a.2.2.1 j)]) ≤ R) →
          (selectCertificate cCount).time a ≤
            (candidateTupleCount a.2.1 a.2.2.1 + 1) * (poly (encInput encC a).length + R)) ∧
        (selectCertificate cCount).space a ≤ poly (encInput encC a).length) := by
  obtain ⟨cOut, _, hOutLen⟩ := cCount.computes
  obtain ⟨pSp, hpSp, hmSp, hSp⟩ := exists_mono_poly hSpace
  obtain ⟨pCn, hpCn, _, hCn⟩ := exists_mono_poly_cert (countIn_polyTime (encC := encC))
  obtain ⟨pCi, hpCi, _, hCi⟩ := exists_mono_poly_cert (initIn_polyTime (encC := encC))
  obtain ⟨pAug, hpAug, hmAug, hAug⟩ := exists_mono_poly_cert (augment_polyTime (encC := encC))
  obtain ⟨pFin, hpFin, hmFin, hFin⟩ :=
    exists_mono_poly_cert (finish_polyTime (encC := encC))
  obtain ⟨pExt, hpExt, hmExt, hExt⟩ :=
    exists_mono_poly_cert (extract_polyTime (encC := encC))
  let qSys (L : ℕ) := pSp (5 * L + 2); let vBound (L : ℕ) := cOut * (qSys L + 1)
  let bAcc (L : ℕ) := 12 * L + vBound L + 7; let lIdx (L : ℕ) := 2 * L * L + 1
  let bFull (L : ℕ) := 2 * lIdx L + 1 + bAcc L; let finIn (L : ℕ) := 2 * bFull L + 1 + vBound L
  let cbOver (L : ℕ) := bFull L + pAug (bFull L) + qSys L + pFin (finIn L)
  let roundOver (L : ℕ) := 2 * bFull L + 2 * (lIdx L + 1) ^ 2 + cbOver L
  let initExt (L : ℕ) := pCn L + L + pCi L + pExt (bFull L) + lIdx L
  have hraw : Cslib.PolynomiallyBounded (fun L => initExt L + roundOver L) := by
    dsimp only [initExt, roundOver, cbOver, finIn, bFull, lIdx, bAcc, vBound, qSys]; fun_prop
  obtain ⟨poly, hpoly, hmpoly, hle_poly⟩ := exists_mono_poly (.of_polynomiallyBounded id hraw)
  refine ⟨poly, hpoly, hmpoly, fun ⟨c, m, P, rows⟩ => ?_⟩; dsimp only
  obtain ⟨hc_le, hm_le, hP_le, hrows_le⟩ := input_le (encC := encC) c m P rows
  set L := (encInput encC (c, m, P, rows)).length; set K := candidateTupleCount m P
  have hpolyL : initExt L + roundOver L ≤ poly L := hle_poly L
  let candRow (j : ℕ) := materializeTestRow m (decodeTestTuple m P j)
  let runAt (j : ℕ) := IndexFold.run (step count) j (c, (m, P), rows, none)
  have hq_j (j : ℕ) : cCount.space (c, rows ++ [candRow j]) ≤ qSys L :=
    (hSp _).trans (hmSp (by
      simp only [length_encPair, candRow, encList_append, List.length_append,
        encList_cons, encList_nil,
        List.append_nil, length_frame, encBits_apply, length_materializeTestRow]; omega))
  have hv_j (j : ℕ) : (encNat (count (c, rows ++ [candRow j]))).length ≤ vBound L :=
    (hOutLen _).trans (Nat.mul_le_mul_left cOut (Nat.add_le_add_right (hq_j j) 1))
  have hlIdx : (encNat K).length ≤ lIdx L := by
    refine (length_encNat_candidateTupleCount_le m P).trans ?_
    have := Nat.mul_le_mul hP_le (show 2 * m ≤ 2 * L by omega); dsimp only [lIdx]; nlinarith
  have hbAcc (j : ℕ) : (encAcc encC (runAt j).2).length ≤ bAcc L := by
    have hb := length_encSelectBestAcc_run_le (fun r => count (c, r)) m P j rows
      (fun i _ => hv_j i)
    simp only [runAt, run_eq, encAcc, length_encPair]
    dsimp only [bAcc]
    omega
  have hbFull (j : ℕ) (hj : j ≤ K) : (encPair encNat (encAcc encC) (runAt j)).length ≤ bFull L :=
    (IndexFold.length_run_le (step count) (c, (m, P), rows, none)
      hj (hbAcc j)).trans (by dsimp only [bFull]; omega)
  let cb := stepCertificate cCount; let rstep := IndexFold.roundCertificate cb
  let initPair : ℕ × C × SelectBestAcc := (0, c, (m, P), rows, none)
  let cn := NativeCertificate.ofPolyTime (countIn_polyTime (encC := encC))
  let ci := NativeCertificate.ofPolyTime (initIn_polyTime (encC := encC))
  let cExt := NativeCertificate.ofPolyTime (extract_polyTime (encC := encC))
  set M := NativeCertificate.maxStateLength (encPair encNat (encAcc encC))
    (IndexFold.step (step count)) K initPair
  set RT := NativeCertificate.maxRoundTime rstep K initPair
  set RS := NativeCertificate.maxRoundSpace rstep K initPair
  have hmaxS : M ≤ bFull L := NativeCertificate.maxStateLength_le _ _ _ _ hbFull
  have hcb_bounds (j : ℕ) (hj : j ≤ K) :
      cb.time (runAt j) ≤ cbOver L + cCount.time (c, rows ++ [candRow j]) ∧
        cb.space (runAt j) ≤ cbOver L := by
    let st := runAt j
    have hparams : st.2.1 = c ∧ st.2.2.1 = (m, P) ∧ st.2.2.2.1 = rows :=
      run_params count c m P j rows
    have hidx : st.1 = j := IndexFold.run_index (step count) j (c, (m, P), rows, none)
    have haug_st : augment st = (c, rows ++ [candRow j]) := by
      simp only [augment, augCandidateRows, candRowOfState, candRow]
      rw [hparams.1, hparams.2.2, hidx,
        show st.2.2.1.1 = m by rw [hparams.2.1],
        show st.2.2.1.2 = P by rw [hparams.2.1]]
    have hst_len : (encPair encNat (encAcc encC) st).length ≤ bFull L := hbFull j hj
    have hfin_len : (encPair (encPair encNat (encAcc encC)) encNat
        (st, count (augment st))).length ≤ finIn L := by
      rw [length_encPair, haug_st]; have := hv_j j; dsimp only [finIn]; omega
    have haugT := (hAug st).1.trans (hmAug hst_len); have haugS := (hAug st).2.trans (hmAug hst_len)
    have hfinT := (hFin (st, count (augment st))).1.trans (hmFin hfin_len)
    have hfinS := (hFin (st, count (augment st))).2.trans (hmFin hfin_len)
    have hcntT : cCount.time (augment st) = cCount.time (c, rows ++ [candRow j]) :=
      congrArg cCount.time haug_st
    have hcntS : cCount.space (augment st) ≤ qSys L := haug_st ▸ hq_j j
    refine ⟨?_, ?_⟩
    · change ((encPair encNat (encAcc encC) st).length +
          ((NativeCertificate.ofPolyTime (augment_polyTime (encC := encC))).time st +
            cCount.time (augment st))) +
        (NativeCertificate.ofPolyTime (finish_polyTime (encC := encC))).time
          (st, count (augment st)) ≤ _; dsimp only [cbOver]; omega
    · change ((encPair encNat (encAcc encC) st).length +
          ((NativeCertificate.ofPolyTime (augment_polyTime (encC := encC))).space st +
            cCount.space (augment st))) +
        (NativeCertificate.ofPolyTime (finish_polyTime (encC := encC))).space
          (st, count (augment st)) ≤ _; dsimp only [cbOver]; omega
  have hcn_a : cn.time (c, m, P, rows) ≤ pCn L ∧ cn.space (c, m, P, rows) ≤ pCn L :=
    hCn (c, m, P, rows)
  have hci_a : ci.time (c, m, P, rows) ≤ pCi L ∧ ci.space (c, m, P, rows) ≤ pCi L :=
    hCi (c, m, P, rows)
  have hextT : cExt.time (runAt K) ≤ pExt (bFull L) :=
    (hExt (runAt K)).1.trans (hmExt (hbFull K le_rfl))
  have hextS : cExt.space (runAt K) ≤ pExt (bFull L) :=
    (hExt (runAt K)).2.trans (hmExt (hbFull K le_rfl))
  refine ⟨fun R hR => ?_, ?_⟩
  · have hmaxRT : RT ≤ bFull L + (lIdx L + 1) ^ 2 + cbOver L + R := by
      refine NativeCertificate.maxRoundTime_le _ _ _ fun j hj => ?_
      have hst_len := hbFull j hj
      have hj_len : (encNat (runAt j).1).length ≤ lIdx L := by
        rw [IndexFold.run_index]
        have hm : (encNat j).length ≤ (encNat K).length := by
          simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hj
        exact hm.trans hlIdx
      have hsq : ((encNat (runAt j).1).length + 1) ^ 2 ≤ (lIdx L + 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      have hcbT := (hcb_bounds j hj).1
      have hRJ : cCount.time (c, rows ++ [candRow j]) ≤ R := hR j hj
      change (encPair encNat (encAcc encC) (runAt j)).length +
        ((encNat (runAt j).1).length + 1) ^ 2 + cb.time (runAt j) ≤ _; omega
    have hsqN : ((encNat K).length + 1) ^ 2 ≤ (lIdx L + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hround_sum : RT + M + ((encNat K).length + 1) ^ 2 ≤ roundOver L + R := by
      dsimp only [roundOver]; omega
    calc (selectCertificate cCount).time (c, m, P, rows)
        = cn.time (c, m, P, rows) + (L + ci.time (c, m, P, rows)) +
            (K + 1) * (RT + M + ((encNat K).length + 1) ^ 2) + cExt.time (runAt K) := rfl
      _ ≤ initExt L + (K + 1) * (roundOver L + R) := by
            have h1 : cn.time (c, m, P, rows) + (L + ci.time (c, m, P, rows)) +
                cExt.time (runAt K) ≤
              initExt L := by dsimp only [initExt]; omega
            have h2 := Nat.mul_le_mul_left (K + 1) hround_sum; omega
      _ ≤ (K + 1) * initExt L + (K + 1) * (roundOver L + R) :=
            Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) _
      _ = (K + 1) * (initExt L + roundOver L + R) := by ring
      _ ≤ (K + 1) * (poly L + R) := Nat.mul_le_mul_left _ (by omega)
  · have hmaxRS : RS ≤ bFull L + (lIdx L + 1) + cbOver L := by
      refine NativeCertificate.maxRoundSpace_le _ _ _ fun j hj => ?_
      have hst_len := hbFull j hj
      have hj_len : (encNat (runAt j).1).length ≤ lIdx L := by
        rw [IndexFold.run_index]
        have hm : (encNat j).length ≤ (encNat K).length := by
          simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hj
        exact hm.trans hlIdx
      have hcbS := (hcb_bounds j hj).2
      change (encPair encNat (encAcc encC) (runAt j)).length +
        ((encNat (runAt j).1).length + 1) + cb.space (runAt j) ≤ _; omega
    have hlin_sq : lIdx L + 1 ≤ 2 * (lIdx L + 1) ^ 2 := by nlinarith
    calc (selectCertificate cCount).space (c, m, P, rows)
        = cn.space (c, m, P, rows) + (L + ci.space (c, m, P, rows)) + RS + M + (encNat K).length +
            cExt.space (runAt K) := rfl
      _ ≤ initExt L + roundOver L := by dsimp only [initExt, roundOver]; omega
      _ ≤ poly L := hpolyL

/-- Uniform selector time and polynomial workspace, measured in the full context/input encoding.
The counter-time premise includes `j = (2m)^P`: the native iterator uses inclusive prefix maxima,
so this endpoint is charged even though that candidate is not executed. -/
theorem computableInO_select {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encPair encC (encList encBits)) encNat)
    (hSpace : PolyBounded (fun r => (encPair encC (encList encBits) r).length) cCount.space)
    (R : C × ℕ × ℕ × List (List Bool) → ℕ)
    (hR : ∀ a, ∀ j ≤ candidateTupleCount a.2.1 a.2.2.1,
      cCount.time
        (a.1, a.2.2.2 ++ [materializeTestRow a.2.1 (decodeTestTuple a.2.1 a.2.2.1 j)]) ≤ R a) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO
        (fun a : C × ℕ × ℕ × List (List Bool) =>
          selectBestTestRow (fun r => count (a.1, r)) a.2.1 a.2.2.1 a.2.2.2)
        (encInput encC) encBits
        (fun a => (candidateTupleCount a.2.1 a.2.2.1 + 1) * (poly (encInput encC a).length + R a))
        (fun a => poly (encInput encC a).length) := by
  obtain ⟨poly, hpoly, _, hB⟩ := select_bounds cCount hSpace
  exact ⟨poly, hpoly, (selectCertificate cCount).computes.mono_le
    (fun a => (hB a).1 (R a) (hR a)) (fun a => (hB a).2)⟩

private theorem greedy_input_le (c : C) (n m P : ℕ) (rows : List (List Bool)) :
    (encC c).length ≤ (encGreedyInput encC (c, n, m, P, rows)).length ∧
    n ≤ (encGreedyInput encC (c, n, m, P, rows)).length ∧
    m ≤ (encGreedyInput encC (c, n, m, P, rows)).length ∧
    P ≤ (encGreedyInput encC (c, n, m, P, rows)).length ∧
    (encList encBits rows).length ≤ (encGreedyInput encC (c, n, m, P, rows)).length := by
  simp only [encGreedyInput, encGreedyIn, encSelectBestIn, length_encPair,
    encUnary_apply, List.length_replicate]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- One uniform machine and polynomial for all encoded contexts, with independent native time
`O((3n + 1) ((2m)^P + 1) (poly(L) + R))` and workspace `O(poly(L))`, where `L` is the full
context/input encoding length. The binary clock, retained rows/context, incumbent count, and final
output are charged; workspace is not multiplied by either loop length.

The inclusive resource maxima require `hR` also at `i = 3n` and `j = (2m)^P`. These are resource
obligations on extra endpoint candidates, not extra calls in the executable program. In particular,
their row-length bound can exceed the correctness theorem's candidate bound by one. Polynomial
counter workspace is a separate, global joint-input assumption; counter time need not be polynomial.
This supplies the context interface for [OpenAI2026ETH], §6.3, not its common-zero counter. -/
theorem computableInO_greedy {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encPair encC (encList encBits)) encNat)
    (hSpace : PolyBounded (fun r => (encPair encC (encList encBits) r).length) cCount.space)
    (R : C × ℕ × ℕ × ℕ × List (List Bool) → ℕ)
    (hR : ∀ a, ∀ i ≤ 3 * a.2.1, ∀ j ≤ candidateTupleCount a.2.2.1 a.2.2.2.1,
      cCount.time (a.1,
      greedyParityRowsAt (fun r => count (a.1, r)) a.2.2.1 a.2.2.2.1 a.2.2.2.2 i ++
        [materializeTestRow a.2.2.1 (decodeTestTuple a.2.2.1 a.2.2.2.1 j)]) ≤ R a) :
    ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
      ComputableInO
        (fun a : C × ℕ × ℕ × ℕ × List (List Bool) =>
          greedyParityRows (fun r => count (a.1, r)) a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
        (encGreedyInput encC) (encList encBits)
        (fun a => (3 * a.2.1 + 1) * (candidateTupleCount a.2.2.1 a.2.2.2.1 + 1) *
          (poly (encGreedyInput encC a).length + R a))
        (fun a => poly (encGreedyInput encC a).length) := by
  obtain ⟨polySel, hpolySel, hmpolySel, hSelB⟩ := select_bounds cCount hSpace
  obtain ⟨pCn, hpCn, _, hCn⟩ := exists_mono_poly_cert (roundCount_polyTime (encC := encC))
  obtain ⟨pCi, hpCi, _, hCi⟩ := exists_mono_poly_cert (outerInit_polyTime (encC := encC))
  obtain ⟨pApp, hpApp, hmApp, hApp⟩ := exists_mono_poly_cert (appendRow_polyTime (encC := encC))
  let bOuter (L : ℕ) := 6 * L * L + 10 * L + 3; let selDom (L : ℕ) := polySel (bOuter L)
  let bAppIn (L : ℕ) := 2 * bOuter L + 1 + L
  let outerFixed (L : ℕ) := 2 * bOuter L + pApp (bAppIn L) + (3 * L + 1) ^ 2
  let initOuter (L : ℕ) := pCn L + pCi L + 3 * L
  let poly (L : ℕ) := initOuter L + outerFixed L + selDom L
  have hpoly : Cslib.PolynomiallyBounded poly := by
    dsimp only [poly, initOuter, outerFixed, bAppIn, selDom, bOuter]; fun_prop
  have hboth : ∀ a : C × ℕ × ℕ × ℕ × List (List Bool),
      (greedyCertificate cCount).time a ≤
        (3 * a.2.1 + 1) * (candidateTupleCount a.2.2.1 a.2.2.2.1 + 1) *
          (poly (encGreedyInput encC a).length + R a) ∧
      (greedyCertificate cCount).space a ≤ poly (encGreedyInput encC a).length := by
    rintro ⟨c, n, m, P, rows₀⟩; dsimp only
    obtain ⟨hc_le, hn_le, hm_le, hP_le, hrows0_le⟩ := greedy_input_le (encC := encC) c n m P rows₀
    set L := (encGreedyInput encC (c, n, m, P, rows₀)).length; set K := candidateTupleCount m P
    set R₀ := R (c, n, m, P, rows₀)
    have hbOuter (i : ℕ) (hi : i ≤ 3 * n) :
        (encInput encC ((outerStep count)^[i] (c, m, P, rows₀))).length ≤ bOuter L := by
      simp only [outerStep_iterate, encInput, encSelectBestIn, length_encPair,
        encUnary_apply, List.length_replicate, length_encList_greedyParityRowsAt]
      have hgrow : i * (2 * m + 1) ≤ (3 * L) * (2 * L + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have hxp : (3 * L) * (2 * L + 1) = 6 * L * L + 3 * L := by ring
      dsimp only [bOuter]; omega
    let cstep := outerCertificate cCount
    let cn := NativeCertificate.ofPolyTime (roundCount_polyTime (encC := encC))
    let ci := NativeCertificate.ofPolyTime (outerInit_polyTime (encC := encC))
    set MO := NativeCertificate.maxStateLength (encInput encC)
      (outerStep count) (3 * n) (c, m, P, rows₀)
    set RTO := NativeCertificate.maxRoundTime cstep (3 * n) (c, m, P, rows₀)
    set RSO := NativeCertificate.maxRoundSpace cstep (3 * n) (c, m, P, rows₀)
    have hmaxS : MO ≤ bOuter L := NativeCertificate.maxStateLength_le _ _ _ _ hbOuter
    have hstep_b (i : ℕ) (hi : i ≤ 3 * n) :
        let st := (outerStep count)^[i] (c, m, P, rows₀)
        cstep.time st ≤ bOuter L + (K + 1) * (selDom L + R₀) + pApp (bAppIn L) ∧
          cstep.space st ≤ bOuter L + selDom L + pApp (bAppIn L) := by
      dsimp only; set st := (outerStep count)^[i] (c, m, P, rows₀)
      have hst_eq : st = (c, m, P, greedyParityRowsAt (fun r => count (c, r)) m P rows₀ i) :=
        outerStep_iterate count c m P i rows₀
      have hst_len : (encInput encC st).length ≤ bOuter L := hbOuter i hi
      have hpoly_sel_le : polySel (encInput encC st).length ≤ selDom L := hmpolySel hst_len
      have hsel_t : (selectCertificate cCount).time st ≤ (K + 1) * (selDom L + R₀) := by
        have h1 := (hSelB st).1 R₀ (by simpa only [hst_eq] using hR (c, n, m, P, rows₀) i hi)
        rw [show candidateTupleCount st.2.1 st.2.2.1 = K by simp only [hst_eq, K]] at h1
        exact h1.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hpoly_sel_le _))
      have hsel_s : (selectCertificate cCount).space st ≤ selDom L :=
        (hSelB st).2.trans hpoly_sel_le
      set selRow := selectBestTestRow (fun r => count (st.1, r)) st.2.1 st.2.2.1 st.2.2.2
      have happ_in_len : (encPair (encInput encC) encBits (st, selRow)).length ≤ bAppIn L := by
        rw [length_encPair]
        have hrow_len : (encBits selRow).length ≤ L := by
          simp only [selRow, hst_eq, encBits_apply, length_selectBestTestRow]; exact hm_le
        dsimp only [bAppIn]; omega
      have happ_t := (hApp (st, selRow)).1.trans (hmApp happ_in_len)
      have happ_s := (hApp (st, selRow)).2.trans (hmApp happ_in_len)
      refine ⟨?_, ?_⟩
      · change ((encInput encC st).length + (selectCertificate cCount).time st) +
          (NativeCertificate.ofPolyTime (appendRow_polyTime (encC := encC))).time
            (st, selRow) ≤ _; omega
      · change ((encInput encC st).length + (selectCertificate cCount).space st) +
          (NativeCertificate.ofPolyTime (appendRow_polyTime (encC := encC))).space
            (st, selRow) ≤ _; omega
    have h3n_len : (encNat (3 * n)).length ≤ 3 * L := by
      rw [encNat_apply, Nat.size_eq_bits_len]; exact (Nat.size_le_self (3 * n)).trans (by omega)
    have hcn_a : cn.time (c, n, m, P, rows₀) ≤ pCn L ∧ cn.space (c, n, m, P, rows₀) ≤ pCn L :=
      hCn (c, n, m, P, rows₀)
    have hci_a : ci.time (c, n, m, P, rows₀) ≤ pCi L ∧
        ci.space (c, n, m, P, rows₀) ≤ pCi L := hCi (c, n, m, P, rows₀)
    refine ⟨?_, ?_⟩
    · have hmaxRT : RTO ≤ bOuter L + (K + 1) * (selDom L + R₀) + pApp (bAppIn L) :=
        NativeCertificate.maxRoundTime_le cstep (3 * n) (c, m, P, rows₀) fun i hi =>
          (hstep_b i hi).1
      have h3n_sq : ((encNat (3 * n)).length + 1) ^ 2 ≤ (3 * L + 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      have hper : RTO + MO + ((encNat (3 * n)).length + 1) ^ 2 ≤
          (K + 1) * (outerFixed L + selDom L + R₀) :=
        calc RTO + MO + ((encNat (3 * n)).length + 1) ^ 2
            ≤ outerFixed L + (K + 1) * (selDom L + R₀) := by dsimp only [outerFixed]; omega
          _ ≤ (K + 1) * outerFixed L + (K + 1) * (selDom L + R₀) :=
                Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) _
          _ = (K + 1) * (outerFixed L + selDom L + R₀) := by ring
      calc (greedyCertificate cCount).time (c, n, m, P, rows₀)
          = cn.time (c, n, m, P, rows₀) + ci.time (c, n, m, P, rows₀) +
              (3 * n + 1) * (RTO + MO + ((encNat (3 * n)).length + 1) ^ 2) := rfl
        _ ≤ initOuter L + (3 * n + 1) * ((K + 1) * (outerFixed L + selDom L + R₀)) :=
              Nat.add_le_add (by dsimp only [initOuter]; omega) (Nat.mul_le_mul_left _ hper)
        _ = initOuter L + ((3 * n + 1) * (K + 1)) * (outerFixed L + selDom L + R₀) := by ring
        _ ≤ ((3 * n + 1) * (K + 1)) * initOuter L +
              ((3 * n + 1) * (K + 1)) * (outerFixed L + selDom L + R₀) :=
              Nat.add_le_add_right
                (Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))) _
        _ = (3 * n + 1) * (K + 1) * (poly L + R₀) := by dsimp only [poly]; ring
    · have hmaxRS : RSO ≤ bOuter L + selDom L + pApp (bAppIn L) :=
        NativeCertificate.maxRoundSpace_le cstep (3 * n) (c, m, P, rows₀) fun i hi =>
          (hstep_b i hi).2
      calc (greedyCertificate cCount).space (c, n, m, P, rows₀)
          = cn.space (c, n, m, P, rows₀) + ci.space (c, n, m, P, rows₀) +
              RSO + MO + (encNat (3 * n)).length := rfl
        _ ≤ poly L := by dsimp only [poly, initOuter, outerFixed]; omega
  exact ⟨poly, hpoly, (greedyCertificate cCount).computes.mono_le
    (fun a => (hboth a).1) (fun a => (hboth a).2)⟩

/-- Whenever `cCount` uses polynomial workspace, `greedyParityRows` runs in polynomial space. -/
theorem computableInPolySpace_greedy {count : C × List (List Bool) → ℕ}
    (cCount : NativeCertificate count (encPair encC (encList encBits)) encNat)
    (hSpace : PolyBounded (fun r => (encPair encC (encList encBits) r).length) cCount.space) :
    ComputableInPolySpace
      (fun a : C × ℕ × ℕ × ℕ × List (List Bool) =>
        greedyParityRows (fun r => count (a.1, r)) a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
      (encGreedyInput encC) (encList encBits) := by
  let cell (a : C × ℕ × ℕ × ℕ × List (List Bool)) (i j : ℕ) : ℕ :=
    cCount.time (a.1,
      greedyParityRowsAt (fun r => count (a.1, r)) a.2.2.1 a.2.2.2.1 a.2.2.2.2 i ++
      [materializeTestRow a.2.2.1 (decodeTestTuple a.2.2.1 a.2.2.2.1 j)])
  let rowMax (a : C × ℕ × ℕ × ℕ × List (List Bool)) (i : ℕ) : ℕ :=
    listMax (cell a i) (List.range (candidateTupleCount a.2.2.1 a.2.2.2.1 + 1))
  let R (a : C × ℕ × ℕ × ℕ × List (List Bool)) : ℕ :=
    listMax (rowMax a) (List.range (3 * a.2.1 + 1))
  have hR : ∀ a, ∀ i ≤ 3 * a.2.1, ∀ j ≤ candidateTupleCount a.2.2.1 a.2.2.2.1, cell a i j ≤ R a :=
    fun a i hi j hj => (le_listMax (f := cell a i) (List.mem_range.mpr (by omega))).trans
      (le_listMax (f := rowMax a) (List.mem_range.mpr (by omega)))
  obtain ⟨poly, hpoly, c, hc, hl⟩ := computableInO_greedy cCount hSpace R hR
  exact ⟨_, fun n => c * (poly n + 1), by fun_prop, hc, hl⟩

end Cslib.Logic.PL.CNF.GreedyContext

end
