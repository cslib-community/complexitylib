/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.Randomized.Expected
public import Complexity.Computability.WordRAM.Randomized.Subroutine

/-!
# Randomized Word-RAM geometric loop and subroutine interface tests

Verifies the distributional structured execution relation `ExecCodeDist`, the geometric Las Vegas
loop expected-time bound `ExecCodeDist.loop_geometric`, and the randomized Word-RAM subroutine
interface `Cslib.WordRAM.Randomized.SubroutineDS`:
* a concrete geometric coin-flipping Las Vegas loop (`while r0 == r1 do r0 ← rand r1` with
  `r1 = 1` and exit probability `1 / 2` per iteration) almost surely halts with `r0 = 0` and
  bounded expected step count;
* a concrete randomized data structure executing `Instr.rand` during its operations instantiates
  `Cslib.WordRAM.Randomized.SubroutineDS` and exercises `toStandard`, `initFresh_exec`,
  `initClear_exec`, `frame_caller_dist` (across a randomized caller step), `call_rename`, and
  `seq_expected_amortized`.
-/

@[expose] public section

namespace ComplexityTests.WordRAMRandomizedSubroutine

open Cslib Cslib.WordRAM Cslib.WordRAM.Randomized
open Cslib.Probability.PMF (uniformOfFintype uniformOfFintype_apply)
open scoped ENNReal

/-! ## 1. Geometric coin-flipping Las Vegas loop (`ExecCodeDist.loop_geometric`) -/

abbrev g0 : Fin 2 := 0
abbrev g1 : Fin 2 := 1

/-- Geometric Las Vegas loop: while `r0 == r1` (with `r1 = 1`), sample `r0 ← rand r1` uniformly
from `{0, 1}`. Each iteration exits with probability `1 / 2` in `1` body instruction. -/
def geomCoinLoop : Code .exact 2 :=
  .loop (.eq g0 g1) (.rand g0 g1)

/-- Loop-head invariant: `x` is `w`-bounded and `r1 = 1`. -/
def geomInv (w : ℕ) (x : Data 2) : Prop :=
  x.Bounded w ∧ x.regs g1 = 1

/-- Loop-exit postcondition: `x` is `w`-bounded, `r0 = 0`, and `r1 = 1`. -/
def geomPost (w : ℕ) (x : Data 2) : Prop :=
  x.Bounded w ∧ x.regs g0 = 0 ∧ x.regs g1 = 1

/-- Single-iteration transition distribution of `r0 ← rand r1` when `r1 = 1`. -/
noncomputable def geomBodyDist (x : Data 2) : PMF (Data 2) :=
  (uniformOfFintype (Fin (x.regs g1 + 1))).map fun k => x.set g0 k.val

private theorem fits_one_of_pos {w : ℕ} (hw : 1 ≤ w) : Fits w 1 :=
  fits_one (by omega)

theorem geomCoinLoop_execCodeDist {w : ℕ} (hw : 1 ≤ w) (x₀ : Data 2)
    (hx₀ : geomInv w x₀ ∧ (Cond.eq g0 g1).Holds x₀) :
    ∃ μ_exit : PMF (Data 2),
      ExecCodeDist w geomCoinLoop x₀ μ_exit (((1 : ℝ≥0∞) + 2) / (2 : ℝ≥0∞)⁻¹ + 2) ∧
      ∀ y ∈ μ_exit.support, ¬(Cond.eq g0 g1).Holds y ∧ geomPost w y := by
  have hp_pos : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ := by simp
  have hp_top : ((2 : ℝ≥0∞)⁻¹) ≠ ⊤ := by simp
  have hbody : ∀ z, geomInv w z → (Cond.eq g0 g1).Holds z →
      ExecCodeDist (B := .exact) w (.rand g0 g1) z (geomBodyDist z) 1 := by
    intro z ⟨hbz, _⟩ _
    simpa [geomBodyDist, ProbComp.eval_unifFin] using ExecCodeDist.rand (B := .exact) (hbz.1 g1)
  have hB : ∀ z, geomInv w z → (Cond.eq g0 g1).Holds z → (1 : ℝ≥0∞) ≤ 1 :=
    fun _ _ _ => le_rfl
  have hinv : ∀ z, geomInv w z → (Cond.eq g0 g1).Holds z →
      ∀ y ∈ (geomBodyDist z).support, LoopStateInv (.eq g0 g1) (geomInv w) (geomPost w) y := by
    intro x ⟨hbx, hr1⟩ _ y hy
    rw [geomBodyDist, PMF.mem_support_map_iff] at hy
    obtain ⟨k, _, rfl⟩ := hy
    have hk_lt : k.val < 2 := by omega
    have hby : (x.set g0 k.val).Bounded w := by
      refine hbx.set ?_
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk_lt with hk0 | hk1
      · have hk0' : k.val = 0 := Nat.lt_one_iff.mp hk0
        rw [hk0']
        exact fits_zero w
      · rw [hk1]
        exact fits_one_of_pos hw
    have hy_r1 : (x.set g0 k.val).regs g1 = 1 := by
      simp [Data.set, hr1]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk_lt with hk0 | hk1
    · have hk0' : k.val = 0 := Nat.lt_one_iff.mp hk0
      right
      refine ⟨?_, hby, ?_, hy_r1⟩
      · simp [Cond.Holds, Data.set, hr1, hk0']
      · simp [Data.set, hk0']
    · left
      refine ⟨?_, hby, hy_r1⟩
      simp [Cond.Holds, Data.set, hr1, hk1]
  have hp_exit : ∀ z, geomInv w z → (Cond.eq g0 g1).Holds z →
      (2 : ℝ≥0∞)⁻¹ ≤ (geomBodyDist z).toOuterMeasure {y | ¬(Cond.eq g0 g1).Holds y} := by
    intro x ⟨_, hr1⟩ _
    classical
    rw [PMF.toOuterMeasure_apply]
    have h_zero_lt : 0 < x.regs g1 + 1 := by omega
    let k₀ : Fin (x.regs g1 + 1) := ⟨0, h_zero_lt⟩
    let y₀ : Data 2 := x.set g0 0
    have hy₀_not : ¬(Cond.eq g0 g1).Holds y₀ := by
      simp [y₀, Cond.Holds, Data.set, hr1]
    have h1 : (2 : ℝ≥0∞)⁻¹ ≤ geomBodyDist x y₀ := by
      rw [geomBodyDist, PMF.map_apply]
      have hle := le_tsum
        (f := fun k : Fin (x.regs g1 + 1) =>
          if y₀ = x.set g0 k.val then uniformOfFintype (Fin (x.regs g1 + 1)) k else 0) k₀
      simpa [y₀, k₀, uniformOfFintype_apply, hr1] using hle
    have h2 : geomBodyDist x y₀ ≤
        ∑' y, Set.indicator {y | ¬(Cond.eq g0 g1).Holds y} (geomBodyDist x) y := by
      calc
        geomBodyDist x y₀
          = Set.indicator {y | ¬(Cond.eq g0 g1).Holds y} (geomBodyDist x) y₀ := by
            rw [Set.indicator_of_mem hy₀_not]
        _ ≤ ∑' y, Set.indicator {y | ¬(Cond.eq g0 g1).Holds y} (geomBodyDist x) y :=
            le_tsum (f := fun y => Set.indicator {y | ¬(Cond.eq g0 g1).Holds y}
              (geomBodyDist x) y) y₀
    exact le_trans h1 h2
  have hx₀_inv : LoopStateInv (.eq g0 g1) (geomInv w) (geomPost w) x₀ := Or.inl ⟨hx₀.2, hx₀.1⟩
  refine ⟨loopExitPMF (.eq g0 g1) geomBodyDist x₀,
    ExecCodeDist.loop_geometric (geomInv w) (geomPost w) hp_pos hp_top hbody hB hinv hp_exit
      hx₀_inv,
    fun y hy =>
      (mem_support_loopExitPMF hp_pos hp_top hinv hp_exit hx₀_inv hy).1⟩

/-- Complete flat program for the geometric coin-flipping loop exercises `program_halts`:
it halts almost surely from `r0 = 1, r1 = 1` with finite expected step count. -/
theorem geomCoinLoop_halts {w : ℕ} (hw : 1 ≤ w) :
    let x₀ : Data 2 := ((Data.init [] : Data 2).set g0 1).set g1 1
    AlmostSurelyHalts w (geomCoinLoop.program g0) ⟨0, x₀⟩ ∧
    expectedTime w (geomCoinLoop.program g0) ⟨0, x₀⟩ ≤
      ((1 : ℝ≥0∞) + 2) / (2 : ℝ≥0∞)⁻¹ + 2 + 1 := by
  intro x₀
  have hx₀_inv : geomInv w x₀ := by
    refine ⟨?_, by simp [x₀, Data.set]⟩
    exact ((Data.Bounded.init (by simp [InputFits])).set
      (fits_one_of_pos hw)).set (fits_one_of_pos hw)
  have hx₀_cond : (Cond.eq g0 g1).Holds x₀ := by
    simp [x₀, Cond.Holds, Data.set]
  obtain ⟨μ_exit, hex, _⟩ := geomCoinLoop_execCodeDist hw x₀ ⟨hx₀_inv, hx₀_cond⟩
  obtain ⟨hExp, _, hAS, _⟩ := hex.program_halts g0
  have h12_ne : (1 : ℝ≥0∞) + 2 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.ofNat_ne_top⟩
  have hT_ne : ((1 : ℝ≥0∞) + 2) / (2 : ℝ≥0∞)⁻¹ + 2 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.div_ne_top h12_ne (by simp), ENNReal.ofNat_ne_top⟩
  exact ⟨hAS hT_ne, hExp⟩

/-! ## 2. Concrete randomized data structure (`Cslib.WordRAM.Randomized.SubroutineDS`) -/

/-- Trivial stateful specification for a randomized sampler subroutine whose implementation invokes
`Instr.rand` during each operation. -/
def coinSpec : Stateful.Spec.{0, 0, 0} where
  State := PUnit
  Op := PUnit
  Result _ := PUnit
  step _ _ := (PUnit.unit, PUnit.unit)

/-- Subroutine code with 5 registers (`0` = `baseReg`, `1` = `frontierReg`, `2` = `zeroReg`,
`3` = `curReg` / scratch output, `4` = `oneReg`). Its operation body `code` executes
`r3 ← rand r4` (`Instr.rand`), with `r4 = 1`, so it samples both `0` and `1`. -/
def coinSubroutineCode : SubroutineCode .exact 5 0 where
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

/-- Representation invariant for `coinSubroutineCode`: machine words are `w`-bounded, `baseReg`
holds `base`, and `oneReg` holds `1`. -/
def coinRep (w base : ℕ) (_θ : Fin 2) (_s : PUnit) (x : Data 5) : Prop :=
  x.Bounded w ∧ x.regs 0 = base ∧ x.regs 4 = 1

private theorem pmf_map_fst_const {α β γ : Type*} (q : PMF α) (b : β) (g : α → γ) :
    (q.map fun a => (b, g a)).map Prod.fst = PMF.pure b := by
  ext θ
  classical
  rw [PMF.map_comp]
  by_cases h : θ = b <;> simp [PMF.map_apply, h, q.tsum_coe]

private theorem pmf_map_snd_const {α β γ : Type*} (q : PMF α) (f : α → β) (c : γ) :
    (q.map fun a => (f a, c)).map Prod.snd = PMF.pure c := by
  ext y
  classical
  rw [PMF.map_comp]
  by_cases h : y = c <;> simp [PMF.map_apply, h, q.tsum_coe]

/-- Concrete randomized `SubroutineDS` certificate for `coinSubroutineCode` with latent seed type
`Fin 2` and uniform reference distribution `uniformOfFintype (Fin 2)`. The native operation
samples from `Fin 2`; its randomness is separate from this latent coupling seed. -/
noncomputable def coinSubroutineDS (w base : ℕ) (hw : 1 ≤ w) :
    Cslib.WordRAM.Randomized.SubroutineDS
      coinSubroutineCode coinSpec w base Fin.elim0 PUnit.unit where
  Seed := Fin 2
  seedLaw := uniformOfFintype (Fin 2)
  seedSlack := 1
  seedSlack_ne_top := ENNReal.one_ne_top
  space := 0
  spanTime := 1
  setupTime := 1
  initPotential := 0
  charge _ _ := 1
  rep := coinRep w base
  potential _ _ := 0
  encode _ _ := 0
  argMatch _ _ := True
  decode _ _ := some PUnit.unit
  bounded h := h.1
  rep_unique _ _ := rfl
  arguments_fit _ _ _ _ := fits_zero w
  encode_matches _ _ := trivial
  rep_supported hreg _ hb' hrep :=
    ⟨hb',
      by rw [hreg 0 rfl, hrep.2.1],
      by rw [hreg 4 rfl, hrep.2.2]⟩
  potential_supported _ _ _ := rfl
  clear_nodup := by decide
  params_not_clear j := Fin.elim0 j
  incCur_eval {x} h1 hfit := by
    change Data.put w x 3 (x.regs 3 + x.regs 4) =
      some (x.set coinSubroutineCode.curReg (x.regs coinSubroutineCode.curReg + 1))
    change x.regs 4 = 1 at h1
    rw [h1]
    exact Data.put_of_fits hfit
  span_exec hx hfr _ := by
    refine ⟨_, ExecWithin.copy, rfl, ?_, ?_, fun j => Fin.elim0 j⟩
    · simpa [coinSubroutineCode, Data.set] using hfr
    · simpa [coinSubroutineCode, Data.set] using hfr
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
      · simpa [coinSubroutineCode, x₂, Data.set] using hfr₁
      · refine ⟨hx₁.set (fits_one_of_pos hw), ?_, ?_⟩
        · simp [x₂, Data.set, ← hb₁, coinSubroutineCode]
        · simp [x₂, Data.set]
  step_exec _ ν _ hseed hsupp := by
    let μ_step : Fin 2 × Data 5 → PMF (Fin 2 × Data 5) := fun p =>
      (uniformOfFintype (Fin (p.2.regs 4 + 1))).map fun k => (p.1, p.2.set 3 k.val)
    refine ⟨μ_step, fun _ => 1, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨⟨hbp, hb0, ho4⟩, _⟩ := hsupp p hp
      refine ⟨?_, ?_⟩
      · have hr := ExecCodeDist.rand (B := .exact) (w := w) (x := p.2) (dst := 3) (src := 4)
          (hbp.1 4)
        refine hr.congr_dist ?_ le_rfl
        rw [ProbComp.eval_unifFin, PMF.map_comp]
        rfl
      · intro q hq
        rw [PMF.mem_support_map_iff] at hq
        obtain ⟨k, _, rfl⟩ := hq
        have hk1 : k.val ≤ 1 := by omega
        refine ⟨rfl, ⟨?_, ?_, ?_⟩, Modifies.refl _ _⟩
        · exact hbp.set ((fits_one_of_pos hw).of_le hk1)
        · simp [Data.set, hb0]
        · simp [Data.set, ho4]
    · intro θ'
      have hmap : (ν.bind μ_step).map Prod.fst = ν.map Prod.fst := by
        rw [PMF.map_bind, PMF.map]
        refine congrArg (ν.bind ·) (funext fun p => ?_)
        exact pmf_map_fst_const (uniformOfFintype (Fin (p.2.regs 4 + 1))) p.1
          (fun k => p.2.set 3 k.val)
      rw [hmap]
      exact hseed θ'
    · simp [ν.tsum_coe]

/-- The concrete represented state with `oneReg = 1` executes the native sampler in one body
instruction, and its output register is exactly fair on both `0` and `1`. -/
theorem coinSubroutineCode_two_outcomes {w : ℕ} (hw : 1 ≤ w) :
    let x : Data 5 := (Data.init []).set 4 1
    let μ : PMF (Data 5) := (uniformOfFintype (Fin 2)).map fun k => x.set 3 k.val
    coinRep w 0 0 PUnit.unit x ∧
      ExecCodeDist w coinSubroutineCode.code x μ 1 ∧
      (μ.map fun y => y.regs 3) 0 = (2 : ℝ≥0∞)⁻¹ ∧
      (μ.map fun y => y.regs 3) 1 = (2 : ℝ≥0∞)⁻¹ := by
  intro x μ
  have hx : x.Bounded w :=
    (Data.Bounded.init (by simp [InputFits])).set (fits_one_of_pos hw)
  refine ⟨⟨hx, by simp [x, Data.set], by simp [x, Data.set]⟩, ?_, ?_, ?_⟩
  · have hsource : x.regs 4 = 1 := by simp [x, Data.set]
    have he := ExecCodeDist.rand (B := .exact) (w := w) (x := x) (dst := 3) (src := 4) (hx.1 4)
    rw [ProbComp.eval_unifFin, hsource] at he
    exact he
  · simp [μ, PMF.map_comp, Function.comp_def, PMF.map_apply, tsum_fintype,
      Fin.sum_univ_two, uniformOfFintype_apply, Data.set]
  · simp [μ, PMF.map_comp, Function.comp_def, PMF.map_apply, tsum_fintype,
      Fin.sum_univ_two, uniformOfFintype_apply, Data.set]

/-- Standard-basis lifting of `coinSubroutineDS`. -/
noncomputable def coinSubroutineDS_standard (w base : ℕ) (hw : 1 ≤ w) :
    Cslib.WordRAM.Randomized.SubroutineDS
      coinSubroutineCode.toStandard coinSpec w base Fin.elim0 PUnit.unit :=
  (coinSubroutineDS w base hw).toStandard

/-- Fresh initialization + multi-operation expected-amortized sequence bound for
`coinSubroutineDS`. -/
theorem coinSubroutineDS_seq_amortized (w base : ℕ) (hw : 1 ≤ w)
    (ops : List PUnit) {x₀ : Data 5}
    (hx₀ : x₀.Bounded w) (hfr : x₀.regs 1 = base) :
    let C := coinSubroutineDS w base hw
    ∃ (ν₀ ν_final : PMF (C.Seed × Data 5)) (T_ops : ℝ≥0∞),
      ExecCodeDist w coinSubroutineCode.initFresh x₀ (ν₀.map Prod.snd) C.initTime ∧
      C.ExecSteps PUnit.unit ops ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      (∀ p ∈ ν_final.support, C.rep p.1 (coinSpec.run PUnit.unit ops).1 p.2) ∧
      C.initTime + T_ops + (∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)) ≤
        C.initTime + (C.initPotential : ℝ≥0∞) +
          (coinSpec.totalCost C.charge PUnit.unit ops : ℝ≥0∞) := by
  intro C
  have hvalid : coinSpec.ValidHistory PUnit.unit ops := by
    induction ops with
    | nil => trivial
    | cons _ _ ih => exact ⟨trivial, ih⟩
  have hz : ∀ a ∈ (Block.mk base C.space).footprint, x₀.mem a = 0 := by
    change ∀ a ∈ (Block.mk base 0).footprint, x₀.mem a = 0
    simp [Block.footprint]
  exact C.seq_expected_amortized ops hx₀ hfr (fun j => Fin.elim0 j) hz hvalid

/-- From concrete empty memory, initialization and two genuine coin-sampling bodies have
expected cost at most four; external argument delivery is uncharged by `ExecSteps`. -/
example :
    let C := coinSubroutineDS 1 0 (by decide)
    ∃ (ν₀ ν_final : PMF (C.Seed × Data 5)) (T_ops : ℝ≥0∞),
      ExecCodeDist 1 coinSubroutineCode.initFresh (Data.init []) (ν₀.map Prod.snd) C.initTime ∧
      C.ExecSteps PUnit.unit [PUnit.unit, PUnit.unit] ν₀ ν_final T_ops ∧
      C.initTime + T_ops ≤ 4 := by
  intro C
  obtain ⟨ν₀, ν_final, T_ops, hinit, hsteps, _, _, hcost⟩ :=
    coinSubroutineDS_seq_amortized 1 0 (by decide) [PUnit.unit, PUnit.unit]
      (x₀ := (Data.init [] : Data 5))
      (Data.Bounded.init (by simp [InputFits])) (by simp [Data.init])
  refine ⟨ν₀, ν_final, T_ops, hinit, hsteps, ?_⟩
  have hT : T_ops ≤ 2 := by
    simpa [C, coinSubroutineDS, Cslib.WordRAM.Randomized.SubroutineDS.initTime,
      Stateful.Spec.totalCost, coinSpec] using hcost
  have hinitTime : C.initTime = 2 := by
    norm_num [C, coinSubroutineDS, Cslib.WordRAM.Randomized.SubroutineDS.initTime]
  rw [hinitTime]
  calc
    2 + T_ops ≤ 2 + 2 := add_le_add le_rfl hT
    _ = 4 := by norm_num

/-- Dirty-memory initialization via `initClear_exec` for `coinSubroutineDS`. -/
theorem coinSubroutineDS_initClear (w base : ℕ) (hw : 1 ≤ w) {x₀ : Data 5}
    (hx₀ : x₀.Bounded w) (hfr : x₀.regs 1 = base) :
    let C := coinSubroutineDS w base hw
    ∃ ν₀ : PMF (C.Seed × Data 5),
      ExecCodeDist w coinSubroutineCode.initClear x₀ (ν₀.map Prod.snd)
        (C.initTime + (4 * C.space + 6 : ℕ)) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs coinSubroutineCode.frontierReg = base + C.space ∧
        C.rep p.1 PUnit.unit p.2 ∧
        C.potential p.1 p.2 ≤ C.initPotential ∧
        Modifies (Block.mk base C.space).footprint x₀.mem p.2.mem := by
  intro C
  exact C.initClear_exec hx₀ hfr (fun j => Fin.elim0 j)

/-- Inline caller subroutine invocation via `call_rename` for `coinSubroutineDS`: a caller with
6 registers embeds `Fin 5` via `Fin.castSucc`, executes `prep := .op (.const 5 0)` on its own
register `r5`, and invokes `coinSubroutineCode.code.rename Fin.castSucc`. -/
theorem coinSubroutineDS_call_rename (w base : ℕ) (hw : 1 ≤ w)
    (ν : PMF ((coinSubroutineDS w base hw).Seed × Data 6))
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤
      (coinSubroutineDS w base hw).seedSlack * (coinSubroutineDS w base hw).seedLaw θ)
    (hrep : ∀ p ∈ ν.support,
      (coinSubroutineDS w base hw).rep p.1 PUnit.unit (p.2.comap Fin.castSucc)) :
    let C := coinSubroutineDS w base hw
    let prep : Code .exact 6 := .op (.const 5 0)
    ∃ (μ_call : C.Seed × Data 6 → PMF (C.Seed × Data 6))
      (T_call : C.Seed × Data 6 → ℝ≥0∞),
      (∀ p ∈ ν.support,
        ExecCodeDist w (.seq prep (coinSubroutineCode.code.rename Fin.castSucc))
          p.2 ((μ_call p).map Prod.snd) (T_call p) ∧
        ∀ q ∈ (μ_call p).support,
          C.decode PUnit.unit (q.2.comap Fin.castSucc).regs =
            some (coinSpec.step PUnit.unit PUnit.unit).2 ∧
          C.rep q.1 (coinSpec.step PUnit.unit PUnit.unit).1 (q.2.comap Fin.castSucc) ∧
          ∃ x' ∈ (PMF.pure (p.2.set 5 0) : PMF (Data 6)).support,
            Modifies (Block.mk base C.space).footprint x'.mem q.2.mem ∧
            ∀ j ∉ Set.range (Fin.castSucc : Fin 5 → Fin 6), q.2.regs j = x'.regs j) ∧
      (∀ θ', ((ν.bind μ_call).map Prod.fst) θ' ≤ C.seedSlack * C.seedLaw θ') ∧
      (∑' p, ν p * (T_call p +
          ∑' q, μ_call p q * (C.potential q.1 (q.2.comap Fin.castSucc) : ℝ≥0∞))) ≤
        1 + (C.charge PUnit.unit PUnit.unit : ℝ≥0∞) +
          ∑' p, ν p * (C.potential p.1 (p.2.comap Fin.castSucc) : ℝ≥0∞) := by
  intro C prep
  refine C.call_rename (Fin.castSucc_injective 5) PUnit.unit ν
    (prep := prep) (B_prep := 1)
    (μ_prep := fun p => PMF.pure (p.2.set 5 0)) (T_prep := fun _ => 1)
    trivial hseed hrep ?_
  intro p hp
  refine ⟨?_, le_rfl, ?_⟩
  · simpa [prep] using ExecCodeDist.of_exec (B := .exact) (w := w) (x := p.2)
      (Exec.const (d := (5 : Fin 6)) (fits_zero w))
  · intro x' hx'
    rw [PMF.mem_support_pure_iff] at hx'
    subst hx'
    have hbp : (p.2.comap Fin.castSucc).Bounded w := C.bounded (hrep p hp)
    refine ⟨?_, ?_, fun _ _ => rfl, trivial⟩
    · refine ⟨fun i => ?_, hbp.2⟩
      have hne : Fin.castSucc i ≠ (5 : Fin 6) := Fin.castSucc_ne_last i
      simp only [Data.comap_regs, Data.set_regs, Function.update_of_ne hne]
      exact hbp.1 i
    · intro i _
      have hne : Fin.castSucc i ≠ (5 : Fin 6) := Fin.castSucc_ne_last i
      simp [Data.set, hne]

/-- Caller framing across a randomized caller step: a caller with 6 registers embeds `Fin 5` via
`Fin.castSucc` and executes `r5 ← rand r4` on its own register `r5` (`5 : Fin 6`), preserving the
coupled seed marginal bound, `rep`, and expected potential via `frame_caller_dist`. -/
theorem coinSubroutineDS_caller_rand_frame (w base : ℕ) (hw : 1 ≤ w)
    (ν : PMF ((coinSubroutineDS w base hw).Seed × Data 6))
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤
      (coinSubroutineDS w base hw).seedSlack * (coinSubroutineDS w base hw).seedLaw θ)
    (hrep : ∀ p ∈ ν.support,
      (coinSubroutineDS w base hw).rep p.1 PUnit.unit (p.2.comap Fin.castSucc)) :
    let C := coinSubroutineDS w base hw
    let μ_caller : C.Seed × Data 6 → PMF (Data 6) := fun p =>
      (uniformOfFintype (Fin 2)).map fun k => p.2.set 5 k.val
    (∀ p ∈ ν.support, ExecCodeDist (B := .exact) w (.rand 5 4) p.2 (μ_caller p) 1) ∧
    (∀ θ, ((C.frameDist ν μ_caller).map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
    (∀ q ∈ (C.frameDist ν μ_caller).support, C.rep q.1 PUnit.unit (q.2.comap Fin.castSucc)) ∧
    (∑' q, C.frameDist ν μ_caller q * (C.potential q.1 (q.2.comap Fin.castSucc) : ℝ≥0∞)) =
      ∑' p, ν p * (C.potential p.1 (p.2.comap Fin.castSucc) : ℝ≥0∞) := by
  intro C μ_caller
  refine ⟨?_, ?_⟩
  · intro p hp
    have hsource : p.2.regs 4 = 1 := (hrep p hp).2.2
    have hfit : Fits w (p.2.regs 4) := by rw [hsource]; exact fits_one_of_pos hw
    have he := ExecCodeDist.rand (B := .exact) (w := w) (x := p.2) (dst := 5) (src := 4) hfit
    rw [ProbComp.eval_unifFin, hsource] at he
    exact he
  · refine C.frame_caller_dist (F := ∅) hseed hrep (Finset.disjoint_empty_right _) ?_
    intro p hp x' hx'
    rw [PMF.mem_support_map_iff] at hx'
    obtain ⟨k, _, rfl⟩ := hx'
    have hbp : (p.2.comap Fin.castSucc).Bounded w := C.bounded (hrep p hp)
    refine ⟨?_, ?_, Modifies.refl _ _⟩
    · refine ⟨fun i => ?_, hbp.2⟩
      have hne : Fin.castSucc i ≠ (5 : Fin 6) := Fin.castSucc_ne_last i
      simp only [Data.comap_regs, Data.set_regs, Function.update_of_ne hne]
      exact hbp.1 i
    · intro i _
      have hne : Fin.castSucc i ≠ (5 : Fin 6) := Fin.castSucc_ne_last i
      simp [Data.set, hne]

end ComplexityTests.WordRAMRandomizedSubroutine
