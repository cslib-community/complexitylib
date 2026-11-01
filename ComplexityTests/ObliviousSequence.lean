/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Hashing.KWise
public import Complexity.Computability.WordRAM.Randomized.ObliviousSequence

/-!
# Oblivious-Sequence Specification and Word-RAM `HashFamilyDS` Interface Tests

Verifies the state-free oblivious-sequence specification `Cslib.DataStructure.ObliviousSequenceSpec`
and the randomized Word-RAM interfaces `Cslib.WordRAM.Randomized.ObliviousSequenceDS` and
`Cslib.WordRAM.Randomized.HashFamilyDS`:
* deterministic and relational `Cslib.Stateful.Spec` and `Cslib.WordRAM.Randomized.SubroutineDS`
  instances embed canonically into `ObliviousSequenceSpec` and `ObliviousSequenceDS` via
  `Stateful.Spec.toObliviousSequenceSpec` and `SubroutineDS.toObliviousSequenceDS`;
* the self-contained Word-RAM `k`-wise independent hash family
  `Cslib.Algorithms.WordRAM.Hashing.KWise` instantiates `HashFamilyDS` and induces an
  `ObliviousSequenceDS` realizing `Cslib.DataStructure.kWiseHashSpec k U (2 ^ M)` (over both
  `Basis.exact` and `Basis.standard`), with a concrete numerical multi-epoch non-vacuity check;
* a pure two-level hash family (`twoLevelTrinomialEval`) and a concrete single-epoch repeated-key
  model (`toyTwoLevelEval`) exercise `whpKWiseHashSpec_contract_evalHashOps_prod` with non-zero
  failure probability (`0 < E * δ = 1 / 2 < 1`), within-epoch repeated-key coherence, and a concrete
  transcript distribution that satisfies `whpKWiseHashSpec` while refuting `kWiseHashSpec`;
* oversized-key checks (`U = 3, w = 1, u = 2`) and ordinary-import client checks for
  `Stateful.Spec.Transcript.labels_map_fst`, `Cslib.Probability.uniformOfFintype_map_restrict_eq`,
  `Cslib.Probability.coupledWithin_uniformOfFintype_prod_restrict`,
  `evalHashOps_eq_of_afterCurrentEpoch_eq_some`, and `evalHashOpsFromSeed_map_equiv`.
-/

@[expose] public section

namespace ComplexityTests.ObliviousSequence

open Cslib Cslib.DataStructure Cslib.Probability Cslib.WordRAM Cslib.WordRAM.Randomized
open Cslib.Algorithms.WordRAM.Hashing
open Cslib.Probability.PMF (uniformOfFintype uniformOfFintype_apply)
open scoped ENNReal

/-! ## 1. Embedding `Stateful.Spec` and `SubroutineDS` into `ObliviousSequenceDS` -/

/-- Deterministic toggle specification on `State := Fin 2` with operation `PUnit`: each step flips
`s ↦ 1 - s` and returns the new state. -/
abbrev toggleSpec : Stateful.Spec.{0, 0, 0} :=
  Stateful.Spec.ofFn (State := Fin 2) (Op := PUnit) (Result := fun _ => Fin 2)
    fun s _ => (⟨1 - s.val, by omega⟩, ⟨1 - s.val, by omega⟩)

/-- Canonical `ObliviousSequenceSpec` induced by `toggleSpec` from initial state `0 : Fin 2`. -/
abbrev toggleObliviousSequenceSpec : ObliviousSequenceSpec.{0, 0} :=
  toggleSpec.toObliviousSequenceSpec 0

/-- On `toggleObliviousSequenceSpec`, a transcript distribution satisfies `Contract ops μ` if and
only if every supported transcript equals `(toggleSpec.run 0 ops).2`. -/
theorem toggleObliviousSequenceSpec_contract_iff (ops : List PUnit)
    (μ : PMF (List (Sigma toggleSpec.Result))) :
    toggleObliviousSequenceSpec.Contract ops μ ↔
      ∀ out ∈ μ.support, out = (toggleSpec.run 0 ops).2 := by
  have hv : toggleSpec.ValidHistory 0 ops :=
    toggleSpec.validHistory_of_forall_valid (fun _ _ => trivial) 0 ops
  exact toggleSpec.toObliviousSequenceSpec_contract_iff_of_hasStepFn 0 hv μ

/-- Nondeterministic relational coin specification on `State := Fin 2` with operation `PUnit`: each
step may transition to either `0` or `1` and returns the new state `s'`. -/
abbrev relCoinSpec : Stateful.Spec.{0, 0, 0} where
  State := Fin 2
  Op := PUnit
  Result _ := Fin 2
  step _ _ s' a := s' = a

/-- Subroutine code with 5 registers (`0` = `baseReg`, `1` = `frontierReg`, `2` = `zeroReg`,
`3` = `curReg` / output, `4` = `oneReg`) whose operation body samples `r3 ← rand r4` in `Fin 2`. -/
def relCoinCode : SubroutineCode .exact 5 0 where
  allocSpan := .op (.copy 0 1)
  initSetup := .op (.const 4 1)
  code := .rand 3 4
  baseReg := 0
  frontierReg := 1
  zeroReg := 2
  oneReg := 4
  curReg := 3
  incCur := Op.exactBin .add 3 3 4
  initParams := Fin.elim0
  input i := i == 3
  output := 3

/-- Representation invariant for `relCoinCode`: machine words are `w`-bounded, `baseReg = base`,
and `oneReg = 1`. -/
def relCoinRep (w base : ℕ) (_θ : Fin 2) (_s : Fin 2) (x : Data 5) : Prop :=
  x.Bounded w ∧ x.regs 0 = base ∧ x.regs 4 = 1

private theorem fits_one_of_pos {w : ℕ} (hw : 1 ≤ w) : Fits w 1 :=
  fits_one (by omega)

private theorem pmf_map_snd_const {α β γ : Type*} (q : PMF α) (f : α → β) (c : γ) :
    (q.map fun a => (f a, c)).map Prod.snd = PMF.pure c := by
  ext y
  classical
  rw [PMF.map_comp]
  by_cases h : y = c <;> simp [PMF.map_apply, h, q.tsum_coe]

/-- Relational `SubroutineDS` certificate for `relCoinCode` over `relCoinSpec`. -/
noncomputable abbrev relCoinSubroutineDS (w base : ℕ) (hw : 1 ≤ w) :
    Randomized.SubroutineDS relCoinCode relCoinSpec w base Fin.elim0 0 where
  Seed := Fin 2
  seedLaw := uniformOfFintype (Fin 2)
  seedSlack := 1
  seedSlack_ne_top := ENNReal.one_ne_top
  space := 0
  spanTime := 1
  setupTime := 1
  initPotential := 0
  charge _ _ := 1
  rep := relCoinRep w base
  potential _ _ := 0
  encode _ _ := 0
  argMatch _ _ := True
  decode _ regs := some ⟨regs 3 % 2, Nat.mod_lt _ (by decide)⟩
  bounded h := h.1
  arguments_fit _ _ _ _ := fits_zero w
  encode_matches _ _ := trivial
  rep_supported hreg _ hb' hrep :=
    ⟨hb', by rw [hreg 0 rfl, hrep.2.1], by rw [hreg 4 rfl, hrep.2.2]⟩
  potential_supported _ _ _ := rfl
  clear_nodup := by decide
  params_not_clear j := Fin.elim0 j
  incCur_eval {x} h1 hfit := by
    change Data.put w x 3 (x.regs 3 + x.regs 4) =
      some (x.set relCoinCode.curReg (x.regs relCoinCode.curReg + 1))
    change x.regs 4 = 1 at h1
    rw [h1]
    exact Data.put_of_fits hfit
  span_exec _ hfr _ := by
    refine ⟨_, ExecWithin.copy, rfl, ?_, ?_, fun j => Fin.elim0 j⟩
    · simpa [relCoinCode, Data.set] using hfr
    · simpa [relCoinCode, Data.set] using hfr
  setup_exec {x₁} hx₁ hb₁ hfr₁ _ _ := by
    let x₂ : Data 5 := x₁.set 4 1
    let ν₀ : PMF (Fin 2 × Data 5) := (uniformOfFintype (Fin 2)).map fun θ => (θ, x₂)
    refine ⟨ν₀, ?_, ?_, ?_⟩
    · have hex : ExecCodeDist (B := .exact) w (.op (.const 4 1)) x₁ (PMF.pure x₂) (1 : ℕ) :=
        ExecCodeDist.of_exec (Exec.const (fits_one_of_pos hw))
      exact hex.congr_dist (pmf_map_snd_const (uniformOfFintype (Fin 2)) id x₂).symm (by simp)
    · intro θ
      rw [PMF.map_comp]
      simp
    · intro p hp
      rw [PMF.mem_support_map_iff] at hp
      obtain ⟨θ, _, rfl⟩ := hp
      refine ⟨?_, ?_, Nat.le_refl 0, Modifies.refl _ _⟩
      · simpa [relCoinCode, x₂, Data.set] using hfr₁
      · refine ⟨hx₁.set (fits_one_of_pos hw), ?_, ?_⟩
        · simp [x₂, Data.set, ← hb₁, relCoinCode]
        · simp [x₂, Data.set]
  step_exec _ ν _ hseed hsupp := by
    let μ_step : CoupledState (Fin 2) (Fin 2) 5 → PMF (CoupledState (Fin 2) (Fin 2) 5) := fun t =>
      (uniformOfFintype (Fin (t.data.regs 4 + 1))).map fun k =>
        ⟨t.seed, ⟨k.val % 2, Nat.mod_lt _ (by decide)⟩, t.data.set 3 k.val⟩
    refine ⟨μ_step, fun _ => 1, ?_, ?_, nofun, ?_⟩
    · intro t ht
      obtain ⟨_, ⟨hbp, hb0, ho4⟩, _⟩ := hsupp t ht
      refine ⟨?_, ?_⟩
      · have hr := ExecCodeDist.rand (B := .exact) (w := w) (x := t.data) (dst := 3) (src := 4)
          (hbp.1 4)
        refine hr.congr_dist ?_ le_rfl
        rw [ProbComp.eval_unifFin, PMF.map_comp]
        rfl
      · intro q hq
        rw [PMF.mem_support_map_iff] at hq
        obtain ⟨k, _, rfl⟩ := hq
        have hk1 : k.val ≤ 1 := by omega
        refine ⟨⟨k.val % 2, Nat.mod_lt _ (by decide)⟩, rfl, ?_, ⟨?_, ?_, ?_⟩, Modifies.refl _ _⟩
        · simp [Data.set]
        · exact hbp.set ((fits_one_of_pos hw).of_le hk1)
        · simp [Data.set, hb0]
        · simp [Data.set, ho4]
    · intro θ'
      have hmap : (ν.bind μ_step).map CoupledState.seed = ν.map CoupledState.seed := by
        rw [PMF.map_bind, PMF.map]
        refine congrArg (ν.bind ·) (funext fun t => ?_)
        ext θ
        rw [PMF.map_comp]
        change ((uniformOfFintype (Fin (t.data.regs 4 + 1))).map (Function.const _ t.seed)) θ =
          PMF.pure t.seed θ
        simp
      rw [hmap]
      exact hseed θ'
    · simp [ν.tsum_coe]

/-- Canonical `ObliviousSequenceDS` embedding of `relCoinSubroutineDS` via
`SubroutineDS.toObliviousSequenceDS`. -/
noncomputable abbrev relCoinObliviousDS (w base : ℕ) (hw : 1 ≤ w) :
    ObliviousSequenceDS relCoinCode (relCoinSpec.toObliviousSequenceSpec 0) w base Fin.elim0 :=
  (relCoinSubroutineDS w base hw).toObliviousSequenceDS (fun _ => 1) (fun _ _ _ => le_rfl)

/-- End-to-end expected-time and distributional contract theorem for `relCoinObliviousDS`. -/
theorem relCoinObliviousDS_seq_expected (w base : ℕ) (hw : 1 ≤ w)
    (ops : List PUnit) {x₀ : Data 5}
    (hx₀ : x₀.Bounded w) (hfr : x₀.regs 1 = base) :
    let O := relCoinObliviousDS w base hw
    ∃ (ν₀ : PMF (LatentState O.Latent 5))
      (ν_final : PMF (SeqOutcome O.Latent relCoinSpec.Result 5)) (T_ops : ℝ≥0∞),
      ExecCodeDist w relCoinCode.initFresh x₀ (ν₀.map LatentState.data) O.initTime ∧
      O.Steps ops (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
      (∀ t ∈ ν_final.support, t.data.Bounded w) ∧
      (relCoinSpec.toObliviousSequenceSpec 0).Contract ops
        (ν_final.map SeqOutcome.transcript) ∧
      O.initTime + T_ops ≤
        O.initTime + (O.initPotential : ℝ≥0∞) + (O.totalCharge ops : ℝ≥0∞) := by
  intro O
  have hv : (relCoinSpec.toObliviousSequenceSpec 0).ValidOpSeq ops :=
    relCoinSpec.validOpSeq_of_forall_valid (fun _ _ => trivial) 0 ops
  have hz : ∀ a ∈ (Block.mk base O.space).footprint, x₀.mem a = 0 := by
    change ∀ a ∈ (Block.mk base 0).footprint, x₀.mem a = 0
    simp [Block.footprint]
  exact O.seq_expected ops hx₀ hfr (fun j => Fin.elim0 j) hz hv

/-! ## 2. Word-RAM `KWise` instantiation of `HashFamilyDS` and `ObliviousSequenceDS` -/

/-- Package the self-contained Word-RAM `k`-wise independent hash family
`Cslib.Algorithms.WordRAM.Hashing.KWise` (`Complexity/Algorithms/WordRAM/Hashing/KWise.lean`) into a
`Cslib.WordRAM.Randomized.HashFamilyDS` over `Basis.exact` on `18` core registers and `3`
initialization parameters `![n_max, U, M]`. -/
noncomputable abbrev kWiseHashFamilyDS {w base n_max U M k : ℕ}
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + KWise.space n_max k))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    HashFamilyDS .exact 18 3 w base U (2 ^ M) ![n_max, U, M] where
  Seed := Fin k → Fin (2 ^ trinomialDeg U M)
  eval := trinomialPolyHash (trinomialStep U M) k U M
  space := KWise.space n_max k
  tableRep := KWise.TableRep base (KWise.chunkBits n_max) U M k
  seedRep := KWise.SeedRep base U M k
  baseReg := 0
  keyReg := 1
  outReg := 2
  initParams := ![1, 2, 3]
  key_ne_base := by decide
  params_ne_base j := by fin_cases j <;> decide
  fits_space := hfit_space
  fits_tag := hfit_n.of_le (by omega)
  fits_key u := hfit_U.of_le (by omega)
  addReg := Op.exactBin .add
  addReg_eval _ _ _ hfit := Data.put_of_fits hfit
  initTableCode := KWise.initTableCode k
  initTableSteps := KWise.initTableSteps n_max U M
  resampleCode := KWise.resampleCode k
  resampleSteps := 5 * k + 10
  evalCode := KWise.evalCode k
  evalSteps := KWise.evalSteps n_max U M k
  initTable_exec {x} _ hbase hpar _ := by
    have hq_pos : 0 < trinomialDeg U M := by
      dsimp only [trinomialDeg]
      positivity
    have hfit_q : Fits w (2 ^ trinomialDeg U M) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    have h1 : x.regs 1 = n_max := hpar 0
    have h2 : x.regs 2 = U := hpar 1
    have h3 : x.regs 3 = M := hpar 2
    obtain ⟨y, hex, htab, hy0, hmod⟩ :=
      KWise.initTableCode_execWithin hbase h1 h2 h3 hfit_space hfit_n hfit_U hfit_q
    refine ⟨y, hex, hy0, htab, ?_⟩
    intro a ha
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    exact hmod a ha
  resample_exec {x} _ hbase htab := by
    have hq_pos : 0 < trinomialDeg U M := by
      dsimp only [trinomialDeg]
      positivity
    have hfit_q : Fits w (2 ^ trinomialDeg U M) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    have hpow : 0 < 2 ^ (2 * KWise.chunkBits n_max) := by positivity
    have hfit_end : Fits w (base + 8 + k) :=
      hfit_space.of_le (by
        change base + 8 + k ≤ base + (8 + k + 2 ^ (2 * KWise.chunkBits n_max))
        omega)
    refine HashFamilyDS.resample_exec_of_execRand
      (fun m => KWise.extractSeeds base U M k m)
      (KWise.resampleCode_execRand htab hbase hfit_end hfit_q)
      (KWise.map_extractSeeds_eval_resampleComp base U M k x) ?_
    intro z hz
    obtain ⟨⟨⟨htab', hseed'⟩, hz0, hout⟩, hsteps⟩ :=
      KWise.mem_support_resampleComp htab hbase hz
    refine ⟨hz0, htab', hseed', ?_, hsteps⟩
    intro a ha
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    dsimp only [KWise.space, KWise.spaceFromB] at ha
    exact hout a (by omega)
  eval_exec θ u {x} _ hbase hkey htab hseed := by
    obtain ⟨y, hex, hy0, _, hy2, hymem⟩ :=
      KWise.evalCode_execWithin u ⟨htab, hseed⟩ hbase hkey hw hfit_space
    exact ⟨y, hex, hymem, hy0, hy2⟩

/-- Canonical `ObliviousSequenceDS` certificate for `KWise` realizing
`Cslib.DataStructure.kWiseHashSpec k U (2 ^ M)`. -/
noncomputable abbrev kWiseObliviousSequenceDS {w base n_max U M k : ℕ}
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + KWise.space n_max k))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    ObliviousSequenceDS
      (kWiseHashFamilyDS hw hfit_space hfit_n hfit_U).subroutineCode
      (kWiseHashSpec k U (2 ^ M))
      w base ![n_max, U, M] :=
  letI : DecidableEq (kWiseHashFamilyDS hw hfit_space hfit_n hfit_U).Seed :=
    inferInstanceAs (DecidableEq (Fin k → Fin (2 ^ trinomialDeg U M)))
  (kWiseHashFamilyDS hw hfit_space hfit_n hfit_U).toKWiseObliviousSequenceDS
    (isKWiseIndependentHash_trinomialPolyHash
      (le_two_pow_trinomialDeg U M) (le_trinomialDeg U M))

/-- Standard-basis lifting of `kWiseHashFamilyDS`. -/
noncomputable def kWiseHashFamilyDS_standard {w base n_max U M k : ℕ}
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + KWise.space n_max k))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    HashFamilyDS .standard 18 3 w base U (2 ^ M) ![n_max, U, M] :=
  (kWiseHashFamilyDS hw hfit_space hfit_n hfit_U).toStandard

/-- Standard-basis lifting of `kWiseObliviousSequenceDS`. -/
noncomputable def kWiseObliviousSequenceDS_standard {w base n_max U M k : ℕ}
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + KWise.space n_max k))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    ObliviousSequenceDS
      (kWiseHashFamilyDS hw hfit_space hfit_n hfit_U).subroutineCode.toStandard
      (kWiseHashSpec k U (2 ^ M))
      w base ![n_max, U, M] :=
  (kWiseObliviousSequenceDS hw hfit_space hfit_n hfit_U).toStandard

/-- End-to-end expected-time and `kWiseHashSpec` correctness guarantee for `KWise` across any
oblivious multi-epoch hash operation sequence `ops` with at most `k` distinct keys per epoch. -/
theorem kWiseObliviousSequenceDS_seq_expected {w base n_max U M k : ℕ}
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + KWise.space n_max k))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1))
    (ops : List (HashOp U))
    {x₀ : Data 23}
    (hx₀ : x₀.Bounded w)
    (hfr : x₀.regs (hashFrontierReg 18) = base)
    (hpar : ∀ j : Fin 3, x₀.regs (hashCoreReg (![1, 2, 3] j)) = (![n_max, U, M] : Fin 3 → ℕ) j)
    (hz : ∀ a ∈ (Block.mk base (KWise.space n_max k)).footprint, x₀.mem a = 0)
    (hv : BoundedEpochKeys k ops) :
    let O := kWiseObliviousSequenceDS hw hfit_space hfit_n hfit_U
    ∃ (ν₀ : PMF (LatentState O.Latent 23))
      (ν_final : PMF (SeqOutcome O.Latent (@HashResult U (2 ^ M)) 23)) (T_ops : ℝ≥0∞),
      ExecCodeDist w (kWiseHashFamilyDS hw hfit_space hfit_n hfit_U).subroutineCode.initFresh
        x₀ (ν₀.map LatentState.data) O.initTime ∧
      O.Steps ops (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
      (∀ t ∈ ν_final.support, t.data.Bounded w) ∧
      ν_final.map SeqOutcome.transcript = idealHashTranscriptPMF (2 ^ M) ops ∧
      O.initTime + T_ops ≤ O.initTime + (O.totalCharge ops : ℝ≥0∞) := by
  intro O
  obtain ⟨ν₀, ν_final, T_ops, hinit, hsteps, hbd, hcontract, hcost⟩ :=
    O.seq_expected ops hx₀ hfr hpar hz hv
  have hpot : O.initPotential = 0 := rfl
  rw [hpot] at hcost
  refine ⟨ν₀, ν_final, T_ops, hinit, hsteps, hbd, hcontract, ?_⟩
  simpa using hcost

/-- Concrete numerical non-vacuity check for `kWiseObliviousSequenceDS`: at `w = 64`, `base = 0`,
`n_max = 8`, `U = 16`, `M = 4`, `k = 3`, a two-epoch oblivious sequence
`[.eval 1, .eval 2, .resample, .eval 3]` satisfies all word-size and `BoundedEpochKeys`
preconditions simultaneously, preserves `Data.Bounded 64` across all final machine states, and
executes with exact `idealHashTranscriptPMF 16` output distribution. -/
theorem kWiseObliviousSequenceDS_nonvacuous :
    let ops : List (HashOp 16) := [.eval 1, .eval 2, .resample, .eval 3]
    let x₀ : Data 23 :=
      (((Data.init [] : Data 23).set (hashCoreReg 1) 8).set (hashCoreReg 2) 16).set
        (hashCoreReg 3) 4
    ∃ (hw : 2 * trinomialDeg 16 4 ≤ 64)
      (hfit_space : Fits 64 (0 + KWise.space 8 3))
      (hfit_n : Fits 64 (max 8 2))
      (hfit_U : Fits 64 (max 16 2 + 1)),
      let O := kWiseObliviousSequenceDS hw hfit_space hfit_n hfit_U
      ∃ (ν₀ : PMF (LatentState O.Latent 23))
        (ν_final : PMF (SeqOutcome O.Latent (@HashResult 16 (2 ^ 4)) 23)) (T_ops : ℝ≥0∞),
        ExecCodeDist 64 (kWiseHashFamilyDS hw hfit_space hfit_n hfit_U).subroutineCode.initFresh
          x₀ (ν₀.map LatentState.data) O.initTime ∧
        O.Steps ops (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
        (∀ t ∈ ν_final.support, t.data.Bounded 64) ∧
        ν_final.map SeqOutcome.transcript = idealHashTranscriptPMF (2 ^ 4) ops ∧
        O.initTime + T_ops ≤ O.initTime + (O.totalCharge ops : ℝ≥0∞) := by
  intro ops x₀
  have hdeg := trinomialDeg_le_three_mul 16 4
  have htb : 3 * max (Nat.clog 2 (max 16 2)) (max 4 1) = 12 := by decide
  rw [htb] at hdeg
  have hw : 2 * trinomialDeg 16 4 ≤ 64 := by omega
  have hfit_space : Fits 64 (0 + KWise.space 8 3) := by decide
  have hfit_n : Fits 64 (max 8 2) := by decide
  have hfit_U : Fits 64 (max 16 2 + 1) := by decide
  refine ⟨hw, hfit_space, hfit_n, hfit_U, ?_⟩
  have hx₀ : x₀.Bounded 64 :=
    (((Data.Bounded.init (by simp [InputFits])).set (by decide)).set (by decide)).set (by decide)
  have hfr : x₀.regs (hashFrontierReg 18) = 0 := by decide
  have hpar : ∀ j : Fin 3, x₀.regs (hashCoreReg (![1, 2, 3] j)) = (![8, 16, 4] : Fin 3 → ℕ) j := by
    intro j
    fin_cases j <;> decide
  have hz : ∀ a ∈ (Block.mk 0 (KWise.space 8 3)).footprint, x₀.mem a = 0 := by
    intro a _
    simp [x₀, Data.set, Data.init]
  have hv : BoundedEpochKeys 3 ops := by
    dsimp only [ops]
    rw [BoundedEpochKeys]
    refine ⟨by decide, ?_⟩
    change BoundedEpochKeys 3 [HashOp.eval 3]
    rw [BoundedEpochKeys]
    exact ⟨by decide, trivial⟩
  exact kWiseObliviousSequenceDS_seq_expected hw hfit_space hfit_n hfit_U ops hx₀ hfr hpar hz hv

/-! ## 3. Word-admissibility checks: oversized-key rejection and `ExecSteps` preservation -/

/-- At universe size `U = 3` and word width `w = 1`, key `u = ⟨2, by decide⟩` has value
`2 = 2 ^ 1`, so no `HashFamilyDS` instance can exist because `fits_key` requires `Fits 1 2`. -/
theorem isEmpty_hashFamilyDS_oversized_key {B : Basis} {r_core k_init base m : ℕ}
    {params : Fin k_init → ℕ} :
    IsEmpty (HashFamilyDS B r_core k_init 1 base 3 m params) := by
  refine ⟨fun H => ?_⟩
  have hfit : Fits 1 2 := H.fits_key ⟨2, by decide⟩
  revert hfit
  decide

/-- At universe size `U = 3` and word width `w = 1`, `ExecSteps` rejects any sequence containing
`HashOp.eval ⟨2, by decide⟩` whenever `encode` places the key value `2` into an input register
`keyReg`. -/
theorem not_execSteps_oversized_eval_key {B : Basis} {r k_init base space k m : ℕ} [NeZero m]
    (P : SubroutineCode B (r + 1) k_init) (Latent : Type*)
    (encode : HashOp 3 → Fin (r + 1) → ℕ)
    (decode : (o : HashOp 3) → (Fin (r + 1) → ℕ) → Option (HashResult m o))
    (keyReg : Fin (r + 1)) (hin : P.input keyReg = true)
    (henc : encode (.eval (⟨2, by decide⟩ : Fin 3)) keyReg = 2)
    (ν ν_final : PMF (SeqOutcome Latent (@HashResult 3 m) (r + 1))) (T_ops : ℝ≥0∞) :
    ¬ ExecSteps P (kWiseHashSpec k 3 m) Latent 1 base space encode decode
        [HashOp.eval (⟨2, by decide⟩ : Fin 3)] ν ν_final T_ops := by
  intro hsteps
  have hfit : Fits 1 (encode (.eval (⟨2, by decide⟩ : Fin 3)) keyReg) :=
    hsteps.arguments_fit (.eval (⟨2, by decide⟩ : Fin 3)) (List.Mem.head _) keyReg hin
  rw [henc] at hfit
  revert hfit
  decide

/-! ## 4. Two-level high-probability hash family (`whpKWiseHashSpec`) non-vacuity -/

/-- Two-level hash evaluation `twoLevelTrinomialEval`:
* when the top seed is `true`, evaluates `trinomialPolyHash (trinomialStep U M) k U M` (which is
  `k`-wise independent);
* when the top seed is `false`, returns the constant `0` (failing `k`-wise independence). -/
noncomputable def twoLevelTrinomialEval (k U M : ℕ) (α : Bool)
    (c : Fin k → Fin (2 ^ trinomialDeg U M)) (u : Fin U) : Fin (2 ^ M) :=
  if α then trinomialPolyHash (trinomialStep U M) k U M c u
  else ⟨0, Nat.two_pow_pos M⟩

/-- On the good top-seed set `{true}`, `twoLevelTrinomialEval k U M true` is `k`-wise
independent. -/
theorem isKWiseIndependentHash_twoLevelTrinomialEval_true (k U M : ℕ) :
    IsKWiseIndependentHash k (twoLevelTrinomialEval k U M true) :=
  isKWiseIndependentHash_trinomialPolyHash (le_two_pow_trinomialDeg U M) (le_trinomialDeg U M)

/-- Under uniform resampling on `Bool × (Fin k → Fin (2 ^ trinomialDeg U M))`,
`twoLevelTrinomialEval k U M` satisfies `(whpKWiseHashSpec k U (2 ^ M) (1 / 2)).Contract ops` on
every `k`-key-per-epoch sequence `ops`. -/
theorem twoLevelTrinomialEval_satisfies_whpKWiseHashSpec {k U M : ℕ} {ops : List (HashOp U)}
    (hv : BoundedEpochKeys k ops) :
    (whpKWiseHashSpec k U (2 ^ M)
      (((Finset.univ \ ({true} : Finset Bool)).card : ℝ≥0∞) / Fintype.card Bool)).Contract ops
      (evalHashOps (uniformOfFintype (Bool × (Fin k → Fin (2 ^ trinomialDeg U M))))
        (fun p => twoLevelTrinomialEval k U M p.1 p.2) ops) := by
  refine whpKWiseHashSpec_contract_evalHashOps_prod (twoLevelTrinomialEval k U M) {true} ?_ hv
  intro α hα
  rw [Finset.mem_singleton.mp hα]
  exact isKWiseIndependentHash_twoLevelTrinomialEval_true k U M

/-- Instantiate `HashFamilyDS.toWhpKWiseObliviousSequenceDS` on `kWiseHashFamilyDS` via the product
equivalence `(Equiv.punitProd _).symm` and `GoodTop := {PUnit.unit}`. -/
noncomputable def kWiseWhpObliviousSequenceDS {w base n_max U M k : ℕ}
    (hw : 2 * trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + KWise.space n_max k))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    ObliviousSequenceDS
      (kWiseHashFamilyDS hw hfit_space hfit_n hfit_U).subroutineCode
      (whpKWiseHashSpec k U (2 ^ M)
        (((Finset.univ \ ({PUnit.unit} : Finset PUnit)).card : ℝ≥0∞) /
          (Fintype.card PUnit : ℝ≥0∞)))
      w base ![n_max, U, M] :=
  letI : DecidableEq (Fin k → Fin (2 ^ trinomialDeg U M)) := inferInstance
  (kWiseHashFamilyDS hw hfit_space hfit_n hfit_U).toWhpKWiseObliviousSequenceDS
    (Equiv.punitProd (Fin k → Fin (2 ^ trinomialDeg U M))).symm
    {PUnit.unit}
    (fun _ _ =>
      isKWiseIndependentHash_trinomialPolyHash
        (le_two_pow_trinomialDeg U M) (le_trinomialDeg U M))

/-! ## 5. Single-epoch repeated-key approximate-contract separation -/

/-- Concrete two-level hash family on `U = 1, m = 2` with `TopSeed = Bool` and `BotSeed = Fin 2`:
* when `α = true`, returns the uniform bottom seed `b : Fin 2`;
* when `α = false`, returns the constant `0 : Fin 2`. -/
def toyTwoLevelEval : Bool → Fin 2 → Fin 1 → Fin 2
  | true, b, _ => b
  | false, _, _ => 0

/-- On the good top seed `true`, `toyTwoLevelEval true` is `1`-wise independent. -/
theorem isKWiseIndependentHash_toyTwoLevelEval_true :
    IsKWiseIndependentHash 1 (toyTwoLevelEval true) where
  dens_filter_restrict_eq {T} hT y := by
    interval_cases hc : T.card
    · obtain rfl := Finset.card_eq_zero.1 hc
      have hfilter :
          ({i | (∅ : Finset (Fin 1)).restrict (toyTwoLevelEval true i) = y} : Finset (Fin 2)) =
            Finset.univ :=
        Finset.filter_true_of_mem fun i _ => funext fun x => (Finset.notMem_empty _ x.2).elim
      rw [hfilter, Finset.dens_univ]
      simp
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hc
      have hfilter :
          ({i | ({x} : Finset (Fin 1)).restrict (toyTwoLevelEval true i) = y} : Finset (Fin 2)) =
            {y ⟨x, Finset.mem_singleton_self x⟩} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Subtype.forall,
          Finset.mem_singleton, Finset.restrict, toyTwoLevelEval]
        exact ⟨fun hi => hi x rfl, by rintro rfl a rfl; rfl⟩
      rw [hfilter, Finset.dens_eq_card_div_card]
      simp

/-- Single-epoch operation sequence querying key `0 : Fin 1` twice without resampling. -/
def toyRepeatedEvalOps : List (HashOp 1) :=
  [.eval 0, .eval 0]

/-- Transcript distribution of `toyTwoLevelEval` on `toyRepeatedEvalOps` under uniform seed
`Bool × Fin 2`. -/
noncomputable def toyRepeatedEvalDist : PMF (List (HashLabel 1 2)) :=
  evalHashOps (uniformOfFintype (Bool × Fin 2))
    (fun p => toyTwoLevelEval p.1 p.2) toyRepeatedEvalOps

/-- Within-epoch coherence: every transcript in `toyRepeatedEvalDist.support` returns the *same*
hash value `v : Fin 2` on both evaluations of key `0`. -/
theorem toyRepeatedEvalDist_coherent {out : List (HashLabel 1 2)}
    (hout : out ∈ toyRepeatedEvalDist.support) :
    ∃ v : Fin 2, out = [⟨.eval 0, v⟩, ⟨.eval 0, v⟩] := by
  dsimp only [toyRepeatedEvalDist, toyRepeatedEvalOps, evalHashOps, evalHashOpsFromSeed] at hout
  simp only [PMF.pure_map, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hout
  obtain ⟨p, _, rfl⟩ := hout
  exact ⟨toyTwoLevelEval p.1 p.2 0, rfl⟩

private theorem evalHashOps_toyRepeatedEvalOps {Seed : Type*} (seedLaw : PMF Seed)
    (eval : Seed → Fin 1 → Fin 2) :
    evalHashOps seedLaw eval toyRepeatedEvalOps =
      seedLaw.map (fun s => [⟨HashOp.eval 0, eval s 0⟩, ⟨HashOp.eval 0, eval s 0⟩]) := by
  dsimp only [toyRepeatedEvalOps, evalHashOps, evalHashOpsFromSeed]
  simp only [PMF.pure_map]
  rfl

/-- The all-zero repeated-evaluation transcript `[⟨.eval 0, 0⟩, ⟨.eval 0, 0⟩]` has probability
`3 / 4` under `toyRepeatedEvalDist`, whereas `idealHashTranscriptPMF 2 toyRepeatedEvalOps` assigns
probability `1 / 2`. -/
theorem toyRepeatedEvalDist_apply_zero_ne_ideal :
    let out₀ : List (HashLabel 1 2) := [⟨.eval 0, 0⟩, ⟨.eval 0, 0⟩]
    toyRepeatedEvalDist out₀ = 3 / 4 ∧
      idealHashTranscriptPMF 2 toyRepeatedEvalOps out₀ = 1 / 2 := by
  intro out₀
  have hv : BoundedEpochKeys 1 toyRepeatedEvalOps := by
    dsimp only [toyRepeatedEvalOps]
    rw [BoundedEpochKeys]
    exact ⟨by decide, trivial⟩
  have hideal_eq :
      idealHashTranscriptPMF 2 toyRepeatedEvalOps =
        evalHashOps (uniformOfFintype (Fin 2)) (toyTwoLevelEval true) toyRepeatedEvalOps :=
    (kWiseHashSpec_contract_evalHashOps isKWiseIndependentHash_toyTwoLevelEval_true hv).symm
  have hne01 : ([⟨HashOp.eval (0 : Fin 1), (0 : Fin 2)⟩, ⟨HashOp.eval 0, 0⟩] :
      List (HashLabel 1 2)) ≠ [⟨HashOp.eval 0, 1⟩, ⟨HashOp.eval 0, 1⟩] := by
    intro h
    injection h with hhead _
    injection hhead with _ hval
    exact Fin.zero_ne_one hval
  constructor
  · dsimp only [toyRepeatedEvalDist]
    rw [evalHashOps_toyRepeatedEvalOps, PMF.map_apply, tsum_fintype,
      Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [uniformOfFintype_apply, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
      out₀, toyTwoLevelEval, hne01, ↓reduceIte, add_zero, div_eq_mul_inv]
    norm_num
    ring
  · rw [hideal_eq, evalHashOps_toyRepeatedEvalOps, PMF.map_apply, tsum_fintype, Fin.sum_univ_two]
    simp only [uniformOfFintype_apply, Fintype.card_fin, out₀, toyTwoLevelEval, hne01, ↓reduceIte,
      add_zero, one_div]
    norm_num

/-- `toyRepeatedEvalDist` satisfies `(whpKWiseHashSpec 1 1 2 (1 / 2)).Contract toyRepeatedEvalOps`
with non-trivial error budget `0 < (epochCount toyRepeatedEvalOps : ℝ≥0∞) * (1 / 2) = 1 / 2 < 1`,
while refuting the exact contract `(kWiseHashSpec 1 1 2).Contract toyRepeatedEvalOps`. -/
theorem toyRepeatedEvalDist_whp_and_not_exact :
    (epochCount toyRepeatedEvalOps : ℝ≥0∞) * (1 / 2) = 1 / 2 ∧
    (0 : ℝ≥0∞) < (epochCount toyRepeatedEvalOps : ℝ≥0∞) * (1 / 2) ∧
    (epochCount toyRepeatedEvalOps : ℝ≥0∞) * (1 / 2) < 1 ∧
    (whpKWiseHashSpec 1 1 2 (1 / 2)).Contract toyRepeatedEvalOps toyRepeatedEvalDist ∧
    ¬ (kWiseHashSpec 1 1 2).Contract toyRepeatedEvalOps toyRepeatedEvalDist := by
  have hepoch : (epochCount toyRepeatedEvalOps : ℝ≥0∞) * (1 / 2) = 1 / 2 := by
    change ((1 : ℕ) : ℝ≥0∞) * (1 / 2) = 1 / 2
    simp
  refine ⟨hepoch, ?_, ?_, ?_, ?_⟩
  · rw [hepoch]
    exact ENNReal.div_pos one_ne_zero ENNReal.ofNat_ne_top
  · rw [hepoch]
    exact ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top
  · have hv : BoundedEpochKeys 1 toyRepeatedEvalOps := by
      dsimp only [toyRepeatedEvalOps]
      rw [BoundedEpochKeys]
      exact ⟨by decide, trivial⟩
    have hwhp :=
      whpKWiseHashSpec_contract_evalHashOps_prod toyTwoLevelEval {true}
        (fun α hα => by
          rw [Finset.mem_singleton.mp hα]
          exact isKWiseIndependentHash_toyTwoLevelEval_true) hv
    have hδ :
        (((Finset.univ \ ({true} : Finset Bool)).card : ℝ≥0∞) / Fintype.card Bool) = 1 / 2 := by
      have hc : (Finset.univ \ ({true} : Finset Bool)).card = 1 := by decide
      rw [hc, Fintype.card_bool]
      simp
    rwa [hδ] at hwhp
  · intro hexact
    change toyRepeatedEvalDist = idealHashTranscriptPMF 2 toyRepeatedEvalOps at hexact
    obtain ⟨h1, h2⟩ := toyRepeatedEvalDist_apply_zero_ne_ideal
    rw [hexact, h2] at h1
    have h1_real := congrArg ENNReal.toReal h1
    norm_num at h1_real

/-! ## 6. Exported decomposition, seed-transport, and coupling helper API checks -/

/-- Ordinary-import client check for `Stateful.Spec.Transcript.labels_map_fst`. -/
theorem transcript_labels_map_fst_client (D : Stateful.Spec) (tr : D.Transcript) :
    tr.labels.map Sigma.fst = tr.ops :=
  tr.labels_map_fst

/-- Ordinary-import client check for `Cslib.Probability.uniformOfFintype_map_restrict_eq` and
`Cslib.Probability.coupledWithin_uniformOfFintype_prod_restrict`. -/
theorem probability_restrict_and_coupling_client
    {T : Finset (Fin 1)} (hT : T.card ≤ 1) :
    (uniformOfFintype (Fin 2)).map (fun θ => T.restrict (toyTwoLevelEval true θ)) =
      uniformOfFintype (T → Fin 2) ∧
    PMF.CoupledWithin
      ((uniformOfFintype (Bool × Fin 2)).map (fun p => T.restrict (toyTwoLevelEval p.1 p.2)))
      (uniformOfFintype (T → Fin 2))
      (((Finset.univ \ ({true} : Finset Bool)).card : ℝ≥0∞) / Fintype.card Bool) :=
  ⟨Cslib.Probability.uniformOfFintype_map_restrict_eq
      isKWiseIndependentHash_toyTwoLevelEval_true hT,
    Cslib.Probability.coupledWithin_uniformOfFintype_prod_restrict toyTwoLevelEval {true}
      (fun α hα => by
        rw [Finset.mem_singleton.mp hα]
        exact isKWiseIndependentHash_toyTwoLevelEval_true) hT⟩

/-- Ordinary-import client check for `evalHashOps_eq_of_afterCurrentEpoch_eq_some` and
`evalHashOpsFromSeed_map_equiv`. -/
theorem evalHashOps_decomposition_and_map_equiv_client
    (seedLaw : PMF (Fin 2)) (eval : Fin 2 → Fin 1 → Fin 2) (e : Fin 2 ≃ Bool) (θ : Fin 2) :
    let ops : List (HashOp 1) := [.eval 0, .resample, .eval 0]
    evalHashOps seedLaw eval ops =
      ((seedLaw.map (fun s => (currentEpochKeys ops).restrict (eval s))).map
        (currentEpochPrefixTranscript 2 ops)).bind (fun pref =>
          (evalHashOps seedLaw eval [.eval 0]).map (fun tailOut =>
            pref ++ (⟨.resample, PUnit.unit⟩ :: tailOut))) ∧
    evalHashOpsFromSeed seedLaw eval θ ops =
      evalHashOpsFromSeed (seedLaw.map e) (fun b => eval (e.symm b)) (e θ) ops :=
  ⟨evalHashOps_eq_of_afterCurrentEpoch_eq_some seedLaw eval rfl,
    evalHashOpsFromSeed_map_equiv seedLaw eval e θ [.eval 0, .resample, .eval 0]⟩

end ComplexityTests.ObliviousSequence
