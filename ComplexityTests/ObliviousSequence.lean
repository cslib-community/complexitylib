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
* a pure two-level hash family (`twoLevelTrinomialEval`) exercises
  `whpKWiseHashSpec_contract_evalHashOps_prod` with non-zero failure probability, and
  `kWiseHashFamilyDS` instantiates `HashFamilyDS.toWhpKWiseObliviousSequenceDS` to realize
  `Cslib.DataStructure.whpKWiseHashSpec`.
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
  resample_exec {x} hbase htab := by
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
  eval_exec θ u {x} hbase hkey htab hseed := by
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
      ν_final.map SeqOutcome.transcript = idealHashTranscriptPMF (2 ^ M) ops ∧
      O.initTime + T_ops ≤ O.initTime + (O.totalCharge ops : ℝ≥0∞) := by
  intro O
  obtain ⟨ν₀, ν_final, T_ops, hinit, hsteps, hcontract, hcost⟩ :=
    O.seq_expected ops hx₀ hfr hpar hz hv
  have hpot : O.initPotential = 0 := rfl
  rw [hpot] at hcost
  refine ⟨ν₀, ν_final, T_ops, hinit, hsteps, hcontract, ?_⟩
  simpa using hcost

/-- Concrete numerical non-vacuity check for `kWiseObliviousSequenceDS`: at `w = 64`, `base = 0`,
`n_max = 8`, `U = 16`, `M = 4`, `k = 3`, a two-epoch oblivious sequence
`[.eval 1, .eval 2, .resample, .eval 3]` satisfies all word-size and `BoundedEpochKeys`
preconditions simultaneously and executes with exact `idealHashTranscriptPMF 16` output
distribution. -/
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

/-! ## 3. Two-level high-probability hash family (`whpKWiseHashSpec`) non-vacuity -/

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

end ComplexityTests.ObliviousSequence
