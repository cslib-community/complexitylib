/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.Exponents
public import CslibFrontier.Computability.Complexity.FineGrained.FunctionRates
public import CslibFrontier.Computability.Complexity.FineGrained.Reduction
public import CslibFrontier.Computability.Complexity.Problems.SharpThreeSAT
import CslibFrontier.Computability.Complexity.FineGrained.CountingTreeBound
import CslibFrontier.Computability.Complexity.FineGrained.Sparsification
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import CslibFrontier.Foundations.Analysis.SublinearEnvelope
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# `#k-SAT` exponents, `#ETH`, and `#SETH`

This module develops the exact-counting rate theory for `#k-SAT`, measuring counters with the
function-time notions `Cslib.Complexity.ComputableInExpTime` and `ComputableInSubexpTime` of
`CslibFrontier.Computability.Complexity.FineGrained.FunctionRates`:

* `Cslib.Complexity.SharpKSAT k` counts the satisfying assignments of width-`≤ k` formulas and
  returns `0` outside that syntax (`SharpKSAT 3 = SharpThreeSAT`).
* `Cslib.Complexity.sharpSatExponent k` is the counting exponent `s^#_k`: the infimum of the
  `δ ≥ 0` for which `SharpKSAT k` is computable within time `2 ^ (δ * n)` times a polynomial in `L`.
* `Cslib.Complexity.SharpETH` (`#ETH`) and `Cslib.Complexity.SharpSETH` (`#SETH`) are the counting
  analogues of `ETH` and `SETH` [CyganEtAl2015].

Because `SharpKSAT k φ ≤ 2 ^ φ.numVars`, its binary output has length linear in `L`, so any
polynomial-time predicate on the count transfers a counting rate `δ` to a decision rate `δ` without
exponent loss (`DecidableInExpTime.of_computableInExpTime_polyBounded`,
`DecidableInExpTime.KSAT_of_SharpKSAT`). Hence `satExponent k ≤ sharpSatExponent k ≤ 1` for every
`k`, `SharpETH ↔ 0 < sharpSatExponent 3`, `SharpSETH ↔ Tendsto sharpSatExponent atTop (𝓝 1)`, and
clause-measured counting rates transfer to variable-measured counting rates through disjoint
counting sparsification (`exists_computableInExpTime_SharpKSAT_numVars_of_length`,
`SharpETH_iff_not_computableInSubexpTime_length`). In addition, `SETH → ETH` (`SETH.eth`) follows
unconditionally via `toThreeSAT` clause-splitting and `3`-SAT sparsification, and
`unrestrictedSatExponent` distinguishes unbounded-width `SAT` from fixed-width
`⨆ k, satExponent k`.

## Main definitions

* `Cslib.Complexity.SharpKSAT`, `Cslib.Complexity.sharpSatExponent`,
  `Cslib.Complexity.unrestrictedSatExponent`: `#k-SAT`, its exponent, and the unrestricted `SAT`
  exponent.
* `Cslib.Complexity.SharpETH`, `Cslib.Complexity.SharpSETH`: the counting exponential time
  hypotheses.

## Main results

* `Cslib.Complexity.DecidableInExpTime.KSAT_of_SharpKSAT`: exact-rate decision from counting.
* `Cslib.Complexity.SharpSAT_computableInExpTime_one`,
  `Cslib.Complexity.SharpKSAT_computableInExpTime_one`: exhaustive counting in time `2 ^ n · poly`.
* `Cslib.Complexity.sharpSatExponent_nonneg`, `Cslib.Complexity.sharpSatExponent_le_one`,
  `Cslib.Complexity.sharpSatExponent_mono`, `Cslib.Complexity.satExponent_le_sharpSatExponent`:
  `0 ≤ s_k ≤ s^#_k ≤ 1` and monotonicity in `k`.
* `Cslib.Complexity.satExponent_eq_sInf_pos`, `Cslib.Complexity.sharpSatExponent_eq_sInf_pos`,
  `Cslib.Complexity.SETH_iff_iSup_ge_three_eq_one`,
  `Cslib.Complexity.SharpSETH_iff_iSup_ge_three_eq_one`, `Cslib.Complexity.SETH.eth`: positive-`δ`
  infima, finite-prefix suprema, and `SETH → ETH`.
* `Cslib.Complexity.SharpETH_iff_sharpSatExponent_pos`,
  `Cslib.Complexity.SharpSETH_iff_tendsto`,
  `Cslib.Complexity.SharpETH_iff_not_computableInSubexpTime_length`: exponent and clause-rate
  characterizations.

## References

* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing Turing.MultiTapeTM Filter Topology

/-! ### `#k-SAT` and exhaustive model counting -/

/-- `#k-SAT`: the number of satisfying assignments of `φ` on its occurring variables when every
clause of `φ` has length at most `k`, and `0` otherwise. -/
@[expose] def SharpKSAT (k : ℕ) (φ : CNF ℕ) : ℕ :=
  if φ.all (fun c => decide (c.length ≤ k)) then SharpSAT φ else 0

/-- At width `3`, `SharpKSAT 3` is `SharpThreeSAT`. -/
@[simp] theorem SharpKSAT_three : SharpKSAT 3 = SharpThreeSAT := rfl

/-- `SharpKSAT k` never exceeds `SharpSAT`. -/
theorem SharpKSAT_le_SharpSAT (k : ℕ) (φ : CNF ℕ) : SharpKSAT k φ ≤ SharpSAT φ := by
  unfold SharpKSAT
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- `SharpKSAT k φ` is at most `2 ^ φ.numVars`. -/
theorem SharpKSAT_le_two_pow_numVars (k : ℕ) (φ : CNF ℕ) : SharpKSAT k φ ≤ 2 ^ φ.numVars :=
  (SharpKSAT_le_SharpSAT k φ).trans (CNF.modelCount_le_two_pow_numVars φ)

/-- A formula lies in `KSAT k` iff its guarded model count `SharpKSAT k φ` is positive. -/
theorem mem_KSAT_iff_pos_SharpKSAT {k : ℕ} {φ : CNF ℕ} :
    φ ∈ KSAT k ↔ 0 < SharpKSAT k φ := by
  simp only [KSAT, Set.mem_ofPred_eq, SharpKSAT]
  split_ifs with hw
  · simp only [List.all_eq_true, decide_eq_true_eq] at hw
    exact ⟨fun h => SharpSAT.mem_SAT_iff.mp h.2, fun h => ⟨hw, SharpSAT.mem_SAT_iff.mpr h⟩⟩
  · simp only [List.all_eq_true, decide_eq_true_eq] at hw
    exact ⟨fun h => absurd h.1 hw, fun h => absurd h (Nat.lt_irrefl 0)⟩

/-- On width-`≤ k` formulas, `SharpKSAT k φ` equals `φ.modelCount`. -/
theorem SharpKSAT_of_width {k : ℕ} {φ : CNF ℕ} (h : ∀ c ∈ φ, c.length ≤ k) :
    SharpKSAT k φ = φ.modelCount := by
  have hw : (φ.all fun c => decide (c.length ≤ k)) = true :=
    List.all_eq_true.mpr fun c hc => decide_eq_true (h c hc)
  simp only [SharpKSAT, hw, ↓reduceIte, SharpSAT]

/-- Outside clause width `k`, `SharpKSAT k φ` returns `0`. -/
theorem SharpKSAT_of_not_width {k : ℕ} {φ : CNF ℕ} (h : ¬∀ c ∈ φ, c.length ≤ k) :
    SharpKSAT k φ = 0 := by
  have hw : (φ.all fun c => decide (c.length ≤ k)) = false := by
    rw [Bool.eq_false_iff, ne_eq, List.all_eq_true]
    exact fun hall => h fun c hc => decide_eq_true_eq.mp (hall c hc)
  simp only [SharpKSAT, hw, Bool.false_eq_true, ↓reduceIte]

/-- The binary encoding of `SharpSAT φ` has length bounded linearly in `(encCNF φ).length`. -/
theorem polyBounded_length_encNat_SharpSAT :
    PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) (fun φ => (encNat (SharpSAT φ)).length) := by
  refine PolyBounded.of_forall_le 2 1 fun φ => ?_
  have h1 : (encNat (SharpSAT φ)).length ≤ (encNat (2 ^ φ.numVars)).length :=
    length_encNat_mono (CNF.modelCount_le_two_pow_numVars φ)
  have h2 : (encNat (2 ^ φ.numVars)).length = φ.numVars + 1 := by
    rw [encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
  have h3 : φ.numVars ≤ (encCNF φ).length := φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
  rw [pow_one]
  omega

/-- The binary encoding of `SharpKSAT k φ` has length bounded linearly in `(encCNF φ).length`. -/
theorem polyBounded_length_encNat_SharpKSAT (k : ℕ) :
    PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
      (fun φ => (encNat (SharpKSAT k φ)).length) :=
  polyBounded_length_encNat_SharpSAT.mono fun φ => length_encNat_mono (SharpKSAT_le_SharpSAT k φ)

namespace BruteForceCount

/-- State of exhaustive model counting over the `2 ^ |distinctVars|` numbered assignments. -/
structure State where
  /-- Input formula being counted. -/
  formula : CNF ℕ
  /-- Cached duplicate-free list of occurring variables (`formula.distinctVars`). -/
  varsList : List ℕ
  /-- Current assignment index in `0, …, 2 ^ |varsList|`. -/
  index : ℕ
  /-- Running count of satisfying assignments among indices `< index`. -/
  acc : ℕ
  deriving Inhabited

/-- Framed encoding of `BruteForceCount.State`. -/
enc_structure encState : State where
  formula : encCNF, varsList : (encList encNat), index : encNat, acc : encNat

/-- Initial state before testing any numbered assignment. -/
@[expose] def init (φ : CNF ℕ) : State :=
  { formula := φ, varsList := φ.distinctVars, index := 0, acc := 0 }

/-- Test `bitsAssignment s.varsList s.index` and advance `s.index`. -/
@[expose] def step (s : State) : State :=
  { formula := s.formula
    varsList := s.varsList
    index := s.index + 1
    acc := if s.formula.eval (bitsAssignment s.varsList s.index) then s.acc + 1 else s.acc }

/-- Total number of assignments `2 ^ φ.distinctVars.length` to inspect. -/
@[expose] def rounds (φ : CNF ℕ) : ℕ := 2 ^ φ.distinctVars.length

/-- Exhaustive model counter returning the accumulated count after `rounds φ` steps. -/
@[expose] def count (φ : CNF ℕ) : ℕ := ((step)^[rounds φ] (init φ)).acc

private theorem iterate_step_init (φ : CNF ℕ) (m : ℕ) :
    (step)^[m] (init φ) =
      { formula := φ
        varsList := φ.distinctVars
        index := m
        acc := (List.range m).countP fun r => φ.eval (bitsAssignment φ.distinctVars r) } := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, step, List.range_succ, List.countP_append,
      List.countP_cons, List.countP_nil]
    dsimp only
    cases φ.eval (bitsAssignment φ.distinctVars m) <;> simp

private theorem toNat_ofBoolListLE_bitsAssignment {vs : List ℕ} (hnd : vs.Nodup) {i : ℕ}
    (hi : i < 2 ^ vs.length) :
    (BitVec.ofBoolListLE (vs.map (bitsAssignment vs i))).toNat = i := by
  have hlt : (BitVec.ofBoolListLE (vs.map (bitsAssignment vs i))).toNat < 2 ^ vs.length :=
    (BitVec.isLt _).trans_eq (by simp)
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < vs.length
  · rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some,
      bitsAssignment, List.Nodup.idxOf_getElem hnd j hj]
  · have hpow : 2 ^ vs.length ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (not_lt.mp hj)
    rw [Nat.testBit_lt_two_pow (hlt.trans_le hpow), Nat.testBit_lt_two_pow (hi.trans_le hpow)]

/-- Exhaustive enumeration of `bitsAssignment φ.distinctVars` computes `φ.modelCount`. -/
theorem count_eq_modelCount (φ : CNF ℕ) : count φ = φ.modelCount := by
  rw [count, iterate_step_init, rounds, List.countP_range_eq_card_filter]
  symm
  set vs := φ.distinctVars
  refine CNF.modelCount_eq_card_filter
    (fun σ => (⟨(BitVec.ofBoolListLE (vs.map σ)).toNat,
      (BitVec.isLt _).trans_eq (by simp)⟩ : Fin (2 ^ vs.length)))
    (fun i => φ.eval (bitsAssignment vs i.val) = true)
    (fun σ τ _ _ => ?_) (fun i => ?_)
  · constructor
    · intro h v hv
      have hlt : vs.idxOf v < vs.length :=
        List.idxOf_lt_length_iff.mpr (CNF.mem_distinctVars.mpr hv)
      have hbit := congrArg (fun n => n.testBit (vs.idxOf v)) (Fin.mk.inj h)
      simpa only [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt, Option.map_some,
        Option.getD_some] using hbit
    · intro h
      have hmap : vs.map σ = vs.map τ :=
        List.map_congr_left fun v hv => h v (CNF.mem_distinctVars.mp hv)
      refine Fin.ext ?_
      dsimp only
      rw [hmap]
  · constructor
    · intro hi
      refine ⟨bitsAssignment vs i.val, hi, Fin.ext ?_⟩
      exact toNat_ofBoolListLE_bitsAssignment φ.nodup_distinctVars i.isLt
    · rintro ⟨σ, hσ, rfl⟩
      refine (CNF.eval_congr fun v hv => ?_).trans hσ
      have hidx : vs.idxOf v < vs.length :=
        List.idxOf_lt_length_iff.mpr (CNF.mem_distinctVars.mpr hv)
      rw [bitsAssignment, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
        List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hidx,
        List.getElem_idxOf hidx]
      rfl

open ComputableInPolyTime in
private theorem computableInPolyTime_init : ComputableInPolyTime init encCNF encState := by
  have := SAT.computableInPolyTime_distinctVars
  unfold init
  fun_prop

open ComputableInPolyTime in
private theorem computableInPolyTime_rounds : ComputableInPolyTime rounds encCNF encNat := by
  have := SAT.computableInPolyTime_distinctVars
  unfold rounds
  exact binary_two_pow.comp (by fun_prop)

open ComputableInPolyTime in
private theorem computableInPolyTime_step : ComputableInPolyTime step encState encState := by
  have heval : ComputableInPolyTime
      (fun s : State => s.formula.eval (bitsAssignment s.varsList s.index))
      encState encBool := by
    have hpair : ComputableInPolyTime
        (fun s : State => ((s.formula, s.varsList), s.index))
        encState (encPair (encPair encCNF (encList encNat)) encNat) := by fun_prop
    exact computableInPolyTime_eval_bitsAssignment.comp hpair
  unfold step
  fun_prop

end BruteForceCount

/-- **`#SAT` by exhaustive counting:** `SharpSAT` (for arbitrary unbounded clause width) is
computable within time `2 ^ n` times a polynomial in the encoded formula length, where
`n = φ.numVars`. -/
theorem SharpSAT_computableInExpTime_one :
    ComputableInExpTime SharpSAT encCNF encNat CNF.numVars 1 := by
  open BruteForceCount in
  obtain ⟨di, _, hi⟩ := computableInPolyTime_init.exists_degree
  obtain ⟨dn, _, hn⟩ := computableInPolyTime_rounds.exists_degree
  obtain ⟨ds, _, hs⟩ := computableInPolyTime_step.exists_degree
  obtain ⟨ci, di_len, hi_len⟩ := computableInPolyTime_init.polyBounded_length.exists_le
  let stateBound (φ : CNF ℕ) : ℕ :=
    2 * ci * ((encCNF φ).length + 1) ^ di_len + 4 * φ.numVars + 16
  have hstate (φ : CNF ℕ) (m : ℕ) (hm : m ≤ rounds φ) :
      (encState ((BruteForceCount.step)^[m] (init φ))).length ≤ stateBound φ := by
    rw [iterate_step_init]
    have hinit := hi_len φ
    have hacc_le : ((List.range m).countP fun r => φ.eval (bitsAssignment φ.distinctVars r)) ≤ m :=
      List.countP_le_length.trans (by simp)
    have hm_len : (encNat m).length ≤ φ.numVars + 1 := by
      have h1 := length_encNat_mono hm
      rw [rounds, φ.length_distinctVars, encNat_two_pow, List.length_append,
        List.length_replicate, List.length_singleton] at h1
      exact h1
    have hacc_len : (encNat ((List.range m).countP
        fun r => φ.eval (bitsAssignment φ.distinctVars r))).length ≤ φ.numVars + 1 :=
      (length_encNat_mono hacc_le).trans hm_len
    have hbase : (encCNF φ).length + (encList encNat φ.distinctVars).length ≤
        (encState (init φ)).length := by
      simp only [init, encState_apply, length_encPair]
      omega
    have hci1 : (encState (init φ)).length ≤ ci * ((encCNF φ).length + 1) ^ di_len := hinit
    simp only [encState_apply, encStateFields, length_encPair, stateBound, Nat.mul_assoc]
    omega
  let R (φ : CNF ℕ) : ℕ := (stateBound φ + 1) ^ ds
  have hround (φ : CNF ℕ) (m : ℕ) (hm : m ≤ rounds φ) :
      ((encState ((BruteForceCount.step)^[m] (init φ))).length + 1) ^ ds ≤ R φ :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (hstate φ m hm) 1) ds
  have hit := ComputableInO.iterate hn.inO hi.inO hs.inO hround hround hstate
  obtain ⟨da, _, ha⟩ := (show ComputableInPolyTime State.acc encState encNat by
    fun_prop).exists_degree
  have hcountO := (ha.inO.comp hit).of_enc_eq (g := SharpSAT) fun φ =>
    congrArg encNat (count_eq_modelCount φ).symm
  have hB_poly : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) stateBound := by
    have hn_poly : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length) CNF.numVars :=
      PolyBounded.self.mono fun φ => φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
    dsimp only [stateBound]
    exact (((PolyBounded.const (2 * ci)).mul
      ((PolyBounded.self.add (.const 1)).pow di_len)).add
      ((PolyBounded.const 4).mul hn_poly)).add (.const 16)
  have hP_poly : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
      (fun φ => ((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
        (stateBound φ + 1) ^ da) :=
    (((PolyBounded.self.add (.const 1)).pow dn).add
      ((PolyBounded.self.add (.const 1)).pow di)).add ((hB_poly.add (.const 1)).pow da)
  have hQ_poly : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
      (fun φ => R φ + stateBound φ + ((encNat (rounds φ)).length + 1) ^ 2) := by
    have hr_poly : PolyBounded (fun φ : CNF ℕ => (encCNF φ).length)
        (fun φ => (encNat (rounds φ)).length) :=
      PolyBounded.of_forall_le 2 1 fun φ => by
        rw [rounds, φ.length_distinctVars, encNat_two_pow, List.length_append,
          List.length_replicate, List.length_singleton, pow_one]
        have := φ.numVars_le_length_vars.trans (SAT.length_vars_le φ)
        omega
    exact (((hB_poly.add (.const 1)).pow ds).add hB_poly).add ((hr_poly.add (.const 1)).pow 2)
  obtain ⟨c, e, hbound⟩ := exists_le_mul_two_pow_of_polyBounded hQ_poly hP_poly
    (μ := CNF.numVars) (T := fun φ => (((encCNF φ).length + 1) ^ dn + ((encCNF φ).length + 1) ^ di +
      (rounds φ + 1) * (R φ + stateBound φ + ((encNat (rounds φ)).length + 1) ^ 2)) +
      ((encState ((BruteForceCount.step)^[rounds φ] (init φ))).length + 1) ^ da)
    fun φ => by
      have hfin := Nat.pow_le_pow_left
        (Nat.add_le_add_right (hstate φ (rounds φ) le_rfl) 1) da
      have hr : (rounds φ + 1) * (R φ + stateBound φ + ((encNat (rounds φ)).length + 1) ^ 2) =
          (2 ^ φ.numVars + 1) * (R φ + stateBound φ + ((encNat (rounds φ)).length + 1) ^ 2) :=
        congrArg (fun n => (n + 1) * _) (by rw [rounds, φ.length_distinctVars])
      omega
  refine ComputableInExpTime.of_computableInO hcountO c e fun φ => ?_
  have hb := hbound φ
  rw [Nat.mul_assoc] at hb
  rw [one_mul, Real.rpow_natCast]
  exact_mod_cast hb

/-- **`#k-SAT` by exhaustive counting:** for every width `k`, `SharpKSAT k` is computable within
time `2 ^ n` times a polynomial in the encoded formula length. -/
theorem SharpKSAT_computableInExpTime_one (k : ℕ) :
    ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars 1 :=
  SharpSAT_computableInExpTime_one.ite_polyTime zero_le_one
    (computableInPolyTime_all_length_le k) (ComputableInPolyTime.const 0)

/-! ### Decision-from-counting and width transfers -/

/-- Any `#k-SAT` counter at exponential rate `δ ≥ 0` decides `k`-SAT at the exact same rate `δ`. -/
theorem DecidableInExpTime.KSAT_of_SharpKSAT {k : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars δ) :
    DecidableInExpTime (KSAT k) encCNF CNF.numVars δ := by
  have hpos : ComputableInPolyTime (fun n : ℕ => decide (0 < n)) encNat encBool :=
    ComputableInPolyTime.binary_lt.comp
      ((ComputableInPolyTime.const 0).prod ComputableInPolyTime.id')
  have hdec := DecidableInExpTime.of_computableInExpTime_polyBounded hδ h
    (polyBounded_length_encNat_SharpKSAT k) hpos
  have heq : {φ : CNF ℕ | decide (0 < SharpKSAT k φ) = true} = KSAT k := by
    ext φ
    simp only [Set.mem_ofPred_eq, decide_eq_true_eq, mem_KSAT_iff_pos_SharpKSAT]
  rwa [heq] at hdec

/-- Subexponential `#k-SAT` counting gives subexponential `k`-SAT decision. -/
theorem DecidableInSubexpTime.KSAT_of_SharpKSAT {k : ℕ}
    (h : ComputableInSubexpTime (SharpKSAT k) encCNF encNat CNF.numVars) :
    DecidableInSubexpTime (KSAT k) encCNF CNF.numVars :=
  fun δ hδ => DecidableInExpTime.KSAT_of_SharpKSAT hδ.le (h δ hδ)

/-- A counter for `#k'-SAT` gives a counter for `#k-SAT` whenever `k ≤ k'`. -/
theorem ComputableInExpTime.SharpKSAT_of_le {k k' : ℕ} (hk : k ≤ k') {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ComputableInExpTime (SharpKSAT k') encCNF encNat CNF.numVars δ) :
    ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars δ := by
  have hite := h.ite_polyTime hδ (computableInPolyTime_all_length_le k)
    (ComputableInPolyTime.const 0)
  have heq : (fun φ : CNF ℕ => if φ.all (fun c => decide (c.length ≤ k)) then SharpKSAT k' φ
      else 0) = SharpKSAT k := by
    funext φ
    unfold SharpKSAT
    split_ifs with h₁ h₂
    · rfl
    · simp only [List.all_eq_true, decide_eq_true_eq] at h₁ h₂
      exact absurd (fun c hc => (h₁ c hc).trans hk) h₂
    · rfl
  rwa [heq] at hite

/-! ### The `#k-SAT` exponent `sharpSatExponent`, `SharpETH`, and `SharpSETH` -/

/-- The counting exponent `s^#_k` of `#k-SAT`: the infimum of the `δ ≥ 0` for which `SharpKSAT k`
is computable within time `2 ^ (δ * n)` times a polynomial in the encoded formula length, where
`n = φ.numVars`. -/
@[expose] noncomputable def sharpSatExponent (k : ℕ) : ℝ :=
  sInf {δ | 0 ≤ δ ∧ ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars δ}

/-- **`#ETH` (the counting exponential time hypothesis):** for some `δ > 0`, `#3-SAT`
(`SharpThreeSAT`) is not computable within time `2 ^ (δ * n)` times any polynomial in the encoded
formula length. -/
@[expose] def SharpETH : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ¬ComputableInExpTime SharpThreeSAT encCNF encNat CNF.numVars δ

/-- **`#SETH` (the strong counting exponential time hypothesis):** for every `ε > 0` there is a
width `k` such that `#k-SAT` (`SharpKSAT k`) is not computable within time `2 ^ ((1 - ε) * n)`
times any polynomial in the encoded formula length. -/
@[expose] def SharpSETH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ,
    ¬ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars (1 - ε)

private abbrev sharpExponents (k : ℕ) : Set ℝ :=
  {δ | 0 ≤ δ ∧ ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars δ}

private theorem one_mem_sharpExponents (k : ℕ) : (1 : ℝ) ∈ sharpExponents k :=
  ⟨zero_le_one, SharpKSAT_computableInExpTime_one k⟩

private theorem bddBelow_sharpExponents (k : ℕ) : BddBelow (sharpExponents k) :=
  ⟨0, fun _ h => h.1⟩

/-- The counting exponent of `#k-SAT` is nonnegative. -/
theorem sharpSatExponent_nonneg (k : ℕ) : 0 ≤ sharpSatExponent k :=
  le_csInf ⟨1, one_mem_sharpExponents k⟩ fun _ h => h.1

/-- **Exhaustive counting bound:** `sharpSatExponent k ≤ 1` for every `k`. -/
theorem sharpSatExponent_le_one (k : ℕ) : sharpSatExponent k ≤ 1 :=
  csInf_le (bddBelow_sharpExponents k) (one_mem_sharpExponents k)

/-- `sharpSatExponent k` is at most every attainable counting rate `δ ≥ 0`. -/
theorem sharpSatExponent_le {k : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars δ) :
    sharpSatExponent k ≤ δ :=
  csInf_le (bddBelow_sharpExponents k) ⟨hδ, h⟩

/-- Below `sharpSatExponent k` there is no `#k-SAT` counter. -/
theorem not_computableInExpTime_of_lt_sharpSatExponent {k : ℕ} {δ : ℝ} (hδ₀ : 0 ≤ δ)
    (hδ : δ < sharpSatExponent k) :
    ¬ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars δ := fun h =>
  absurd (sharpSatExponent_le hδ₀ h) (not_le.mpr hδ)

/-- An unattainable rate `δ` bounds `sharpSatExponent k` from below. -/
theorem le_sharpSatExponent_of_not_computableInExpTime {k : ℕ} {δ : ℝ}
    (h : ¬ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars δ) :
    δ ≤ sharpSatExponent k :=
  le_csInf ⟨1, one_mem_sharpExponents k⟩ fun _ hδ' =>
    le_of_not_gt fun hlt => h (hδ'.2.mono hlt.le)

/-- `sharpSatExponent` is monotone in the clause width `k`. -/
theorem sharpSatExponent_mono : Monotone sharpSatExponent := fun k k' hk =>
  csInf_le_csInf (bddBelow_sharpExponents k) ⟨1, one_mem_sharpExponents k'⟩ fun _ hδ =>
    ⟨hδ.1, hδ.2.SharpKSAT_of_le hk hδ.1⟩

/-- **Decision vs. counting exponent:** `satExponent k ≤ sharpSatExponent k` for every `k`. -/
theorem satExponent_le_sharpSatExponent (k : ℕ) : satExponent k ≤ sharpSatExponent k :=
  le_csInf ⟨1, one_mem_sharpExponents k⟩ fun _ hδ =>
    satExponent_le hδ.1 (DecidableInExpTime.KSAT_of_SharpKSAT hδ.1 hδ.2)

/-- `#ETH` holds iff `#3-SAT` is not computable in subexponential time in `numVars`. -/
theorem SharpETH_iff_not_computableInSubexpTime :
    SharpETH ↔ ¬ComputableInSubexpTime SharpThreeSAT encCNF encNat CNF.numVars := by
  simp only [SharpETH, ComputableInSubexpTime, not_forall, exists_prop]

/-- **`#ETH` in terms of the counting exponent:** `SharpETH ↔ 0 < sharpSatExponent 3`. -/
theorem SharpETH_iff_sharpSatExponent_pos : SharpETH ↔ 0 < sharpSatExponent 3 := by
  constructor
  · rintro ⟨δ, hδ, h⟩
    exact hδ.trans_le (le_sharpSatExponent_of_not_computableInExpTime h)
  · intro h
    exact ⟨sharpSatExponent 3 / 2, half_pos h,
      not_computableInExpTime_of_lt_sharpSatExponent (half_pos h).le (half_lt_self h)⟩

/-- `sharpSatExponent k = 0` iff `SharpKSAT k` is computable in subexponential time. -/
theorem sharpSatExponent_eq_zero_iff_computableInSubexpTime {k : ℕ} :
    sharpSatExponent k = 0 ↔ ComputableInSubexpTime (SharpKSAT k) encCNF encNat CNF.numVars := by
  constructor
  · intro h δ hδ
    by_contra hnc
    have hle := le_sharpSatExponent_of_not_computableInExpTime hnc
    linarith
  · intro h
    refine le_antisymm (le_of_not_gt fun hpos => ?_) (sharpSatExponent_nonneg k)
    exact not_computableInExpTime_of_lt_sharpSatExponent (half_pos hpos).le (half_lt_self hpos)
      (h (sharpSatExponent k / 2) (half_pos hpos))

/-- **`#SETH` in terms of the counting exponents:** `SharpSETH ↔ sharpSatExponent k → 1`. -/
theorem SharpSETH_iff_tendsto : SharpSETH ↔ Tendsto sharpSatExponent atTop (𝓝 1) := by
  constructor
  · intro h
    rw [Metric.tendsto_atTop]
    intro ε hε
    set η := min ε 1 / 2
    have hη : 0 < η := half_pos (lt_min hε one_pos)
    have hηε : η < ε := (half_lt_self (lt_min hε one_pos)).trans_le (min_le_left ε 1)
    have hη₁ : 0 ≤ 1 - η := by
      dsimp only [η]
      linarith [min_le_right ε 1]
    obtain ⟨k, hk⟩ := h η hη
    refine ⟨k, fun k' hk' => ?_⟩
    have h₁ : 1 - η ≤ sharpSatExponent k' :=
      le_sharpSatExponent_of_not_computableInExpTime fun h' => hk (h'.SharpKSAT_of_le hk' hη₁)
    have h₂ := sharpSatExponent_le_one k'
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  · intro h ε hε
    set η := min ε 1 / 2
    have hη : 0 < η := half_pos (lt_min hε one_pos)
    have hηε : η ≤ ε := (half_lt_self (lt_min hε one_pos)).le.trans (min_le_left ε 1)
    have hη₁ : 0 ≤ 1 - η := by
      dsimp only [η]
      linarith [min_le_right ε 1]
    obtain ⟨k, hk⟩ := (h.eventually (lt_mem_nhds (by linarith : 1 - η < 1))).exists
    exact ⟨k, fun h' => not_computableInExpTime_of_lt_sharpSatExponent hη₁ hk
      (h'.mono (by linarith))⟩

/-- Decision hardness implies counting hardness (`ETH → SharpETH`); note both hypotheses are
refuted in this library, while the contrapositive transfer `DecidableInSubexpTime.KSAT_of_SharpKSAT`
is unconditional. -/
theorem ETH.sharpETH (h : ETH) : SharpETH := by
  rw [ETH_iff_satExponent_pos] at h
  rw [SharpETH_iff_sharpSatExponent_pos]
  exact h.trans_le (satExponent_le_sharpSatExponent 3)

/-- Strong decision hardness implies strong counting hardness (`SETH → SharpSETH`); the underlying
fixed-width transfer `DecidableInExpTime.KSAT_of_SharpKSAT` is unconditional. -/
theorem SETH.sharpSETH (h : SETH) : SharpSETH := by
  intro ε hε
  by_cases h1 : 1 ≤ ε
  · obtain ⟨k, hk⟩ := h 1 one_pos
    refine ⟨k, fun hcount => hk ?_⟩
    have h0 : 1 - ε ≤ 0 := by linarith
    have hc0 : ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars 0 := hcount.mono h0
    simpa only [sub_self] using DecidableInExpTime.KSAT_of_SharpKSAT le_rfl hc0
  · obtain ⟨k, hk⟩ := h ε hε
    exact ⟨k, fun hcount => hk (DecidableInExpTime.KSAT_of_SharpKSAT (by linarith) hcount)⟩

/-! ### Positive-rate infima, finite-prefix suprema, `SETH → ETH`, and unrestricted `SAT` -/

/-- `satExponent k` equals the infimum over strictly positive rates `δ > 0`. -/
theorem satExponent_eq_sInf_pos (k : ℕ) :
    satExponent k = sInf {δ : ℝ | 0 < δ ∧ DecidableInExpTime (KSAT k) encCNF CNF.numVars δ} :=
  csInf_nonneg_eq_csInf_pos (fun _ _ hle h => h.mono hle) (KSAT_decidableInExpTime_one k)

/-- `sharpSatExponent k` equals the infimum over strictly positive rates `δ > 0`. -/
theorem sharpSatExponent_eq_sInf_pos (k : ℕ) :
    sharpSatExponent k =
      sInf {δ : ℝ | 0 < δ ∧ ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars δ} :=
  csInf_nonneg_eq_csInf_pos (fun _ _ hle h => h.mono hle) (SharpKSAT_computableInExpTime_one k)

/-- Dropping any finite prefix `k < K` leaves `⨆ k, satExponent k` unchanged. -/
theorem iSup_ge_satExponent_eq_iSup (K : ℕ) :
    (⨆ k : {k : ℕ // K ≤ k}, satExponent k.val) = ⨆ k : ℕ, satExponent k :=
  iSup_ge_eq_iSup_of_monotone satExponent_mono satExponent_le_one K

/-- `SETH` holds iff `⨆ k : ℕ, satExponent k = 1`. -/
theorem SETH_iff_iSup_eq_one : SETH ↔ (⨆ k : ℕ, satExponent k) = 1 :=
  SETH_iff_tendsto.trans
    (tendsto_atTop_nhds_one_iff_iSup_eq_one satExponent_mono satExponent_le_one)

/-- `SETH` holds iff `⨆ k ≥ 3, satExponent k = 1`. -/
theorem SETH_iff_iSup_ge_three_eq_one :
    SETH ↔ (⨆ k : {k : ℕ // 3 ≤ k}, satExponent k.val) = 1 := by
  rw [iSup_ge_satExponent_eq_iSup 3, SETH_iff_iSup_eq_one]

/-- Dropping any finite prefix `k < K` leaves `⨆ k, sharpSatExponent k` unchanged. -/
theorem iSup_ge_sharpSatExponent_eq_iSup (K : ℕ) :
    (⨆ k : {k : ℕ // K ≤ k}, sharpSatExponent k.val) = ⨆ k : ℕ, sharpSatExponent k :=
  iSup_ge_eq_iSup_of_monotone sharpSatExponent_mono sharpSatExponent_le_one K

/-- `SharpSETH` holds iff `⨆ k : ℕ, sharpSatExponent k = 1`. -/
theorem SharpSETH_iff_iSup_eq_one : SharpSETH ↔ (⨆ k : ℕ, sharpSatExponent k) = 1 :=
  SharpSETH_iff_tendsto.trans
    (tendsto_atTop_nhds_one_iff_iSup_eq_one sharpSatExponent_mono sharpSatExponent_le_one)

/-- `SharpSETH` holds iff `⨆ k ≥ 3, sharpSatExponent k = 1`. -/
theorem SharpSETH_iff_iSup_ge_three_eq_one :
    SharpSETH ↔ (⨆ k : {k : ℕ // 3 ≤ k}, sharpSatExponent k.val) = 1 := by
  rw [iSup_ge_sharpSatExponent_eq_iSup 3, SharpSETH_iff_iSup_eq_one]

/-- Clause-splitting reduction (`toThreeSAT`) transfers subexponential clause-count decidability of
`ThreeSAT` to `KSAT k` for every fixed width `k` (each width-`≤ k` clause splits into at most
`max 1 k` width-`≤ 3` clauses). -/
theorem DecidableInSubexpTime.KSAT_length_of_ThreeSAT_length (k : ℕ)
    (h3 : DecidableInSubexpTime ThreeSAT encCNF List.length) :
    DecidableInSubexpTime (KSAT k) encCNF List.length := by
  let reduceWidth (φ : CNF ℕ) : CNF ℕ :=
    if φ.all (fun c => decide (c.length ≤ k)) then toThreeSAT φ else [[]]
  have hr : ComputableInPolyTime reduceWidth encCNF encCNF :=
    ComputableInPolyTime.ite' (computableInPolyTime_all_length_le k)
      computableInPolyTime_toThreeSAT (ComputableInPolyTime.const [[]])
  refine h3.of_reduction hr (fun φ => ?_) (c := max 1 k) fun φ => ?_
  · dsimp only [reduceWidth]
    by_cases hw : (φ.all fun c => decide (c.length ≤ k)) = true
    · simp only [hw, ↓reduceIte, mem_ThreeSAT_toThreeSAT_iff]
      have hw' : ∀ c ∈ φ, c.length ≤ k := fun c hc =>
        decide_eq_true_eq.mp (List.all_eq_true.mp hw c hc)
      exact ⟨fun h => h.2, fun h => ⟨hw', h⟩⟩
    · simp only [hw, Bool.false_eq_true, ↓reduceIte]
      have hnot_ksat : φ ∉ KSAT k := fun h =>
        hw (List.all_eq_true.mpr fun c hc => decide_eq_true (h.1 c hc))
      have hnot_3sat : ([[]] : CNF ℕ) ∉ ThreeSAT := by
        rintro ⟨-, σ, hσ⟩
        exact Bool.false_ne_true hσ
      exact ⟨fun h => absurd h hnot_ksat, fun h => absurd h hnot_3sat⟩
  · dsimp only [reduceWidth]
    split_ifs with hw
    · simp only [List.all_eq_true, decide_eq_true_eq] at hw
      have hlen_eq : (toThreeSAT φ).length = (φ.map fun c => max 1 (c.length - 2)).sum := by
        rw [toThreeSAT, CNF.relabel, List.length_map, CNF.length_to3CNF]
      have hsum_le : (φ.map fun c => max 1 (c.length - 2)).sum ≤ φ.length * max 1 k := by
        refine (List.sum_le_length_nsmul _ (max 1 k) fun n hn => ?_).trans (by simp)
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
        have hck := hw c hc
        omega
      rw [hlen_eq, Nat.mul_comm]
      omega
    · simp only [List.length_singleton]
      omega

/-- **Strong ETH implies ETH (`SETH → ETH`)** via clause-splitting (`toThreeSAT`) and IPZ
sparsification (`DecidableInSubexpTime.numVars_of_length`), without invoking the native counting
refutation: if `ThreeSAT` is decidable in subexponential time in variables, then it is decidable in
subexponential time in clauses, hence every fixed-width `KSAT k` is decidable in subexponential
time in clauses and (by sparsification) in variables, contradicting `SETH`. -/
theorem SETH.eth (h : SETH) : ETH := by
  by_contra hnot
  have h3_len : DecidableInSubexpTime ThreeSAT encCNF List.length := by
    by_contra hnot_len
    exact hnot (ETH_iff_not_decidableInSubexpTime_length.mpr hnot_len)
  obtain ⟨k, hk⟩ := h (1 / 2) (by norm_num)
  have hk_vars : DecidableInSubexpTime (KSAT k) encCNF CNF.numVars :=
    (DecidableInSubexpTime.KSAT_length_of_ThreeSAT_length k h3_len).numVars_of_length
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hhalf] at hk
  exact hk (hk_vars (1 / 2) (by norm_num))

/-- **Unrestricted `SAT` exponent**: infimum of `δ ≥ 0` such that `SAT` (with unbounded clause
width) is decidable within time `2 ^ (δ * n) * poly(L)`. Unlike `SETH`, which takes `⨆ k, s_k` over
fixed clause widths, `unrestrictedSatExponent` requires a single machine per `δ` handling arbitrary
clause widths simultaneously. -/
@[expose] noncomputable def unrestrictedSatExponent : ℝ :=
  sInf {δ : ℝ | 0 ≤ δ ∧ DecidableInExpTime SAT encCNF CNF.numVars δ}

theorem unrestrictedSatExponent_nonneg : 0 ≤ unrestrictedSatExponent :=
  le_csInf ⟨1, zero_le_one, SAT_decidableInExpTime_one⟩ fun _ h => h.1

theorem unrestrictedSatExponent_le_one : unrestrictedSatExponent ≤ 1 :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨zero_le_one, SAT_decidableInExpTime_one⟩

/-- Every fixed-width exponent `satExponent k` is bounded above by `unrestrictedSatExponent`. -/
theorem satExponent_le_unrestrictedSatExponent (k : ℕ) :
    satExponent k ≤ unrestrictedSatExponent := by
  refine le_csInf ⟨1, zero_le_one, SAT_decidableInExpTime_one⟩ fun δ ⟨hδ, h⟩ =>
    satExponent_le hδ ?_
  rw [KSAT_eq_inter k (KSAT_subset_SAT k) le_rfl]
  exact h.inter (computableInPolyTime_all_length_le k) hδ

/-- `⨆ k, satExponent k ≤ unrestrictedSatExponent`. -/
theorem iSup_satExponent_le_unrestrictedSatExponent :
    (⨆ k : ℕ, satExponent k) ≤ unrestrictedSatExponent :=
  ciSup_le satExponent_le_unrestrictedSatExponent

/-- Under `SETH`, `unrestrictedSatExponent = 1`. -/
theorem SETH.unrestrictedSatExponent_eq_one (h : SETH) : unrestrictedSatExponent = 1 :=
  le_antisymm unrestrictedSatExponent_le_one
    ((SETH_iff_iSup_eq_one.mp h).symm.le.trans iSup_satExponent_le_unrestrictedSatExponent)

/-! ### Clause-measured vs. variable-measured counting rates (counting sparsification) -/

/-- **From variables to clauses for `#k-SAT`.** Because a width-`≤ k` formula with `m` clauses has
at most `k * m` variables, a `#k-SAT` counter at variable rate `δ ≥ 0` runs at clause rate
`k * δ`. -/
theorem ComputableInExpTime.SharpKSAT_length_of_numVars {k : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars δ) :
    ComputableInExpTime (SharpKSAT k) encCNF encNat List.length (k * δ) := by
  obtain ⟨e, h⟩ := h
  obtain ⟨t, c, hO, ht⟩ := h.exists_computableInO
  obtain ⟨dw, _, hw⟩ := (computableInPolyTime_all_length_le k).exists_degree
  obtain ⟨dc, _, hc0⟩ := (ComputableInPolyTime.const (encIn := encCNF) (0 : ℕ)).exists_degree
  have hite := (hw.inO.ite hO hc0.inO).of_enc_eq (g := SharpKSAT k) fun φ => congrArg encNat <| by
    split_ifs with hφ
    · simp only [SharpKSAT, hφ, ↓reduceIte]
    · simp only [SharpKSAT, hφ, Bool.false_eq_true, ↓reduceIte]
  refine ComputableInExpTime.of_computableInO hite (2 * c + 3) (dw + dc + e) fun φ => ?_
  set L : ℝ := ((encCNF φ).length : ℝ)
  have hL1 : (1 : ℝ) ≤ L + 1 := by
    dsimp only [L]
    linarith [(Nat.cast_nonneg (encCNF φ).length : (0 : ℝ) ≤ _)]
  have hX1 : (1 : ℝ) ≤ 2 ^ (k * δ * φ.length) := Real.one_le_rpow (by norm_num) (by positivity)
  have hdw : (L + 1) ^ dw ≤ 2 ^ (k * δ * φ.length) * (L + 1) ^ (dw + dc + e) :=
    (pow_le_pow_right₀ hL1 (by omega)).trans (le_mul_of_one_le_left (by positivity) hX1)
  have hdc : (L + 1) ^ dc ≤ 2 ^ (k * δ * φ.length) * (L + 1) ^ (dw + dc + e) :=
    (pow_le_pow_right₀ hL1 (by omega)).trans (le_mul_of_one_le_left (by positivity) hX1)
  have he : (L + 1) ^ e ≤ (L + 1) ^ (dw + dc + e) := pow_le_pow_right₀ hL1 (by omega)
  have hc_nn : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hpos : (0 : ℝ) ≤ 2 ^ (k * δ * φ.length) * (L + 1) ^ (dw + dc + e) := by positivity
  change ((((encCNF φ).length + 1) ^ dw +
    if φ.all (fun cl => decide (cl.length ≤ k)) then t φ
    else ((encCNF φ).length + 1) ^ dc : ℕ) : ℝ) ≤ _
  split_ifs with hφ
  · simp only [List.all_eq_true, decide_eq_true_eq] at hφ
    have hn : (φ.numVars : ℝ) ≤ k * φ.length := by exact_mod_cast CNF.numVars_le_mul_length hφ
    have hexp : (2 : ℝ) ^ (δ * φ.numVars) ≤ 2 ^ (k * δ * φ.length) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have hmul := mul_le_mul hexp he (by positivity) (by positivity)
    have hmulc := mul_le_mul_of_nonneg_left hmul hc_nn
    have hc1 : (c : ℝ) ≤ c * (2 ^ (k * δ * φ.length) * (L + 1) ^ (dw + dc + e)) :=
      le_mul_of_one_le_right hc_nn (one_le_mul_of_one_le_of_one_le hX1 (one_le_pow₀ hL1))
    push_cast
    dsimp only [L] at *
    nlinarith [ht φ]
  · push_cast
    dsimp only [L] at *
    nlinarith

/-- Subexponential `#k-SAT` counting in `numVars` gives subexponential counting in `length`. -/
theorem ComputableInSubexpTime.SharpKSAT_length_of_numVars {k : ℕ}
    (h : ComputableInSubexpTime (SharpKSAT k) encCNF encNat CNF.numVars) :
    ComputableInSubexpTime (SharpKSAT k) encCNF encNat List.length := by
  intro δ hδ
  refine ((h (δ / (k + 1)) (by positivity)).SharpKSAT_length_of_numVars (by positivity)).mono ?_
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-- **From clauses to variables via disjoint counting sparsification.** For every width `k` and
every `ε > 0`, there is a constant `c` such that any `#k-SAT` counter within time
`2 ^ (δ * m) · poly(L)` (`δ ≥ 0`, `m = φ.length`) yields a `#k-SAT` counter within time
`2 ^ ((ε + c * δ) * n) · poly(L)` (`n = φ.numVars`). -/
theorem exists_computableInExpTime_SharpKSAT_numVars_of_length (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ δ : ℝ, 0 ≤ δ →
      ComputableInExpTime (SharpKSAT k) encCNF encNat List.length δ →
      ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars (ε + c * δ) := by
  open CountingSparsify ClauseSet.Sparsification in
  set K : ℕ := max k 1
  have hK : 1 ≤ K := le_max_right _ _
  have hkK : k ≤ K := le_max_left _ _
  obtain ⟨B_raw, hB_raw⟩ := exists_nat_gt (1 / ε)
  set B : ℕ := max B_raw 1
  have hB1 : 1 ≤ B := le_max_right _ _
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB1
  have hBε : 1 / (B : ℝ) ≤ ε := by
    have hgt : 1 / ε < (B : ℝ) := hB_raw.trans_le (by exact_mod_cast le_max_left B_raw 1)
    rw [div_lt_iff₀ hε] at hgt
    rw [div_le_iff₀ hBpos]
    linarith
  set M : ℕ := countingThresholdBase K B
  refine ⟨occBound K M, fun δ hδ h => ?_⟩
  obtain ⟨e, h⟩ := h
  obtain ⟨t, c, hgO, ht⟩ := h.exists_computableInO
  obtain ⟨T, C₀, E, hsearchO, hT⟩ :=
    exists_computableInO_search_countingThresholdBase hK hkK hB1 hgO
      (fun ψ _ _ => SharpKSAT_le_two_pow_numVars k ψ) hδ ht
  have hfun : search M K k B (SharpKSAT k) = SharpKSAT k := by
    funext φ
    exact search_eq_ite_modelCount ((by decide : 1 ≤ 2).trans (two_le_countingThresholdBase K B))
      hK (two_le_countingThresholdBase K B) hkK (countingTreeBound_countingThresholdBase hK hB1)
      (fun ψ hw _ => SharpKSAT_of_width hw) φ
  rw [hfun] at hsearchO
  have hrate : ComputableInExpTime (SharpKSAT k) encCNF encNat CNF.numVars
      (1 / B + occBound K M * δ) := by
    refine ComputableInExpTime.of_computableInO hsearchO (2 * C₀ + 1) E fun φ => ?_
    have hTφ := hT φ
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 / (B : ℝ) + occBound K M * δ) * φ.numVars) *
        (((encCNF φ).length : ℝ) + 1) ^ E :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) (by positivity))
        (one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _)))
    have hC₀ : (C₀ : ℝ) ≤ C₀ * ((2 : ℝ) ^ ((1 / (B : ℝ) + occBound K M * δ) * φ.numVars) *
        (((encCNF φ).length : ℝ) + 1) ^ E) :=
      le_mul_of_one_le_right (Nat.cast_nonneg C₀) h1
    push_cast
    linarith
  exact hrate.mono (by linarith)

/-- Subexponential `#k-SAT` counting in clause count `length` gives subexponential counting in
variable count `numVars`. -/
theorem ComputableInSubexpTime.SharpKSAT_numVars_of_length {k : ℕ}
    (h : ComputableInSubexpTime (SharpKSAT k) encCNF encNat List.length) :
    ComputableInSubexpTime (SharpKSAT k) encCNF encNat CNF.numVars := by
  intro δ hδ
  obtain ⟨c, hc⟩ := exists_computableInExpTime_SharpKSAT_numVars_of_length k (half_pos hδ)
  have hδ' : 0 < δ / 2 / (c + 1) := by positivity
  refine (hc _ hδ'.le (h _ hδ')).mono ?_
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have : (c : ℝ) * (δ / 2 / (c + 1)) ≤ δ / 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **`#ETH` in terms of clauses:** `SharpETH` holds iff `#3-SAT` is not computable in
subexponential time in the number of clauses. -/
theorem SharpETH_iff_not_computableInSubexpTime_length :
    SharpETH ↔ ¬ComputableInSubexpTime SharpThreeSAT encCNF encNat List.length := by
  rw [SharpETH_iff_not_computableInSubexpTime, ← SharpKSAT_three]
  exact ⟨fun h hlen => h hlen.SharpKSAT_numVars_of_length,
    fun h hnum => h hnum.SharpKSAT_length_of_numVars⟩

end Cslib.Complexity
