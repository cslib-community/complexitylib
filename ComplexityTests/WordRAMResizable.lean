/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.BoundedExec
public import Complexity.Computability.WordRAM.Resizable.Randomized
public import Complexity.DataStructure.Memory.Resizable
import Complexity.Tactic.Realize

/-!
# End-to-end tests for the Resizable Word RAM, `ExecBounded` `realize` bridge, and `ExecRCodeDist`

Concrete end-to-end checks for Milestone M1 of the word-granular **Resizable Word RAM**
(`Cslib.WordRAM.Resizable`, `Cslib.WordRAM.BoundedExec`, and
`Cslib.DataStructure.Memory.Resizable`):

1. `by realize` synthesizing `RealizesBounded` directly (without modifying `Tactic/Realize.lean`) on
   both sequential read/write/arithmetic code (`addToNext`) and `iterate` pointer chasing
   (`chaseProg`), while keeping existing `Realizes` goals intact, and lifting directly to
   `RDemonicExec` and `ExecRProgramDist` via `RDemonicExec.of_realizesBounded`.
2. Adversarial `DemonicGrow` erased by `growZeroCode`, composed with `.rand` and `.shrink` in
   `ExecRCodeDist`, transported along `Basis.Simulates.exactStandard` to `Basis.standard`, and
   compiled via `toExecRProgramDist` with an explicit peak-frontier bound `x.frontier + 4`.
3. Randomized `while` termination via `ExecRCodeDist.loop_geometric`.
4. Soundness check `not_execRProgramDist_halt` confirming `[.halt out]` cannot satisfy any
   state-changing or frontier-growing transition.
5. `Memory.Resizable.spec_refines_demonicSpec`, `demonicStep_grow_of_demonicGrow`, and
   `Block.realizes_of_unchangedOutside`.
-/

@[expose] public section

namespace ComplexityTests.WordRAMResizable

open scoped ENNReal
open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable

/-! ## 1. `by realize` → `RealizesBounded` → `RDemonicExec` → `ExecRProgramDist` -/

/-- Single-word encoding. -/
abbrev singleWord : ℕ ↪ (Fin 1 → ℕ) :=
  (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

/-- Two-word input encoding. -/
abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) :=
  appendWords singleWord singleWord

/-- Read `s.mem d.1`, write `s.mem d.1 + d.2` into `d.1 + 1`, and read it back. -/
def addToNext (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let v ← Memory.read d.1
  Memory.write (d.1 + 1) (v + d.2)
  Memory.read (d.1 + 1)

/-- `by realize` synthesizes `RealizesBounded` directly without touching `Tactic/Realize.lean`. -/
theorem addToNext_realizesBounded :
    RealizesBounded .exact addToNext pairWords singleWord
      (fun w d s => Fits w (d.1 + 1) ∧ Fits w (s.mem d.1 + d.2))
      (fun _ _ => 0) := by
  realize
  all_goals first | exact h.1 | exact h.2

/-- Follow `d.1` pointers starting from `d.2` using `iterate`. -/
def chaseProg (d : ℕ × ℕ) : Memory.Prog ℕ :=
  iterate (fun x : ℕ × ℕ => Memory.read x.2) d.1 d.2 d.1

/-- `by realize` synthesizes `RealizesBounded` for `iterate` loops. -/
theorem chaseProg_realizesBounded :
    RealizesBounded .exact chaseProg pairWords singleWord
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Ordinary `Realizes` goals continue to elaborate identically via `by realize`. -/
theorem chaseProg_realizes :
    Realizes .exact chaseProg pairWords singleWord
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- `addToNext` preserves `s.frontier`, so `RDemonicExec.of_realizesBounded` lifts its compiled
`Code .exact` directly onto the Resizable Word RAM and compiles to `ExecRProgramDist`. -/
theorem addToNext_lifts_to_execRProgramDist {w L_peak : ℕ} (base delta : ℕ) :
    ∃ (r : ℕ) (fr src0 src1 out : Fin r) (p : RProgram .exact r),
      ∀ (x : RData r),
        x.Bounded w →
        x.frontier ≤ L_peak →
        x.regs fr = x.frontier →
        x.regs src0 = base →
        x.regs src1 = delta →
        base + 1 < x.frontier →
        Fits w (base + 1) →
        Fits w (x.mem base + delta) →
        ∃ (y : RData r) (T : ℕ),
          ExecRProgramDist w p out x (PMF.pure y) (T + 1) L_peak ∧
          y.frontier = x.frontier ∧
          y.mem (base + 1) = x.mem base + delta ∧
          y.regs out = x.mem base + delta := by
  obtain ⟨n, C, emit, hspec⟩ := addToNext_realizesBounded
  let r := n + 5
  have hr3 : 3 < r := by dsimp [r]; omega
  let frontier : Fin r := ⟨0, by omega⟩
  let src0 : Fin r := ⟨1, by omega⟩
  let src1 : Fin r := ⟨2, by omega⟩
  let src : Fin 2 → Fin r := ![src0, src1]
  let tmp : Fin (1 + n + 1) → Fin r := fun j => ⟨j.val + 3, by dsimp [r]; omega⟩
  let out : Fin r := tmp (Fin.castAdd (n + 1) 0)
  let code : RCode .exact r := RCode.ofCode (emit frontier src tmp)
  refine ⟨r, frontier, src0, src1, out, code.program out, ?_⟩
  intro x hx hL_peak hfr hbase hdelta hlt hfit1 hfit2
  have hi : Function.Injective tmp := fun a b hab => by
    have hv := congrArg Fin.val hab; simp only [tmp] at hv; exact Fin.ext (by omega)
  have hd : ∀ i j, src i ≠ tmp j := fun i j hij => by
    have hv := congrArg Fin.val hij
    fin_cases i <;> simp [src, src0, src1, tmp, r] at hv
  have hf : ∀ j, tmp j ≠ frontier := fun j hj => by
    have hv := congrArg Fin.val hj; simp [tmp, frontier] at hv
  have hs : ∀ i, src i ≠ frontier := fun i hsi => by
    have hv := congrArg Fin.val hsi
    fin_cases i <;> simp [src, src0, src1, frontier, r] at hv
  have hin : x.regs ∘ src = pairWords (base, delta) := by
    funext i
    fin_cases i
    · exact hbase
    · exact hdelta
  have hsafe : Fits w (base + 1) ∧ Fits w ((memoryState frontier x.toData).mem base + delta) :=
    ⟨hfit1, hfit2⟩
  have hv : (Memory.spec w).ValidHistory (memoryState frontier x.toData)
      ((Memory.spec w).clientHistory (memoryState frontier x.toData)
        (addToNext (base, delta))) := by
    change base < x.regs frontier ∧ (base + 1 < x.regs frontier ∧ Fits w (x.mem base + delta)) ∧
      base + 1 < x.regs frontier ∧ True
    rw [hfr]
    exact ⟨by omega, ⟨hlt, hfit2⟩, hlt, trivial⟩
  have hnoalloc : ((Memory.spec w).clientState
      (memoryState frontier x.toData) (addToNext (base, delta))).frontier ≤ x.frontier := by
    change x.regs frontier ≤ x.frontier
    omega
  obtain ⟨y_d, hdem, hm_eq, hout, _⟩ :=
    RDemonicExec.of_realizesBounded (B := .exact)
      (p := addToNext) (input := pairWords) (output := singleWord)
      (safe := fun w d s => Fits w (d.1 + 1) ∧ Fits w (s.mem d.1 + d.2))
      (work := fun _ _ => 0)
      hspec frontier src tmp hi hd hf hs (base, delta) hx hL_peak hin hsafe hv hnoalloc
  set y : RData r := ⟨y_d.regs, y_d.mem, x.frontier⟩
  refine ⟨y, _, (ExecRCodeDist.of_demonicExec hdem).toExecRProgramDist out, rfl, ?_, ?_⟩
  · have hmem_eq := congrArg (fun s : Memory.State => s.mem (base + 1)) hm_eq
    change y_d.mem (base + 1) = Function.update x.mem (base + 1) (x.mem base + delta) (base + 1)
      at hmem_eq
    simpa [y] using hmem_eq
  · have hout0 := hout 0
    change y_d.regs out = Function.update x.mem (base + 1) (x.mem base + delta) (base + 1) at hout0
    simpa [y] using hout0

/-! ## 2. `growZeroCode` erasing demonic growth + `.rand` + `.shrink` + `exactStandard` -/

/-- Allocate 4 words via `growZeroCode` (erasing any demonic dirty words), sample a uniform word in
`[0, 4]` into register `6`, store and reload it in the newly allocated word `x.frontier`, and
shrink the 4 words before halting. -/
def growSampleShrinkCode : RCode .exact 7 :=
  .seq (.op (.const 0 4)) <|
  .seq (growZeroCode 0 1 2 3 4 5) <|
  .seq (.rand 6 0) <|
  .seq (RCode.ofCode (.seq (.op (.store 1 6)) (.op (.load 6 1)))) <|
       (.shrink 0)

/-- Full `ExecRCodeDist` → `Basis.standard` → `ExecRProgramDist` pipeline for
`growSampleShrinkCode`,
certifying peak frontier `x.frontier + 4` while restoring final frontier `x.frontier` and canonical
zeroed memory `x.mem` across every adaptive adversary. -/
theorem growSampleShrinkCode_standard_execRProgramDist {w : ℕ} {x : RData 7}
    (hx : x.Bounded w) (hfit4 : Fits w 4) (hfit_grow : Fits w (x.frontier + 4)) :
    ∃ μ : PMF (RData 7),
      (∀ y ∈ μ.support, y.frontier = x.frontier ∧ y.mem = x.mem ∧ y.regs 6 ≤ 4) ∧
      ExecRProgramDist w
        ((growSampleShrinkCode.mapSimulates Basis.Simulates.exactStandard).program 6)
        6 x μ 30 (x.frontier + 4) := by
  set L_peak := x.frontier + 4
  have h1 : Fits w 1 := hfit4.of_le (by omega)
  set x₁ := x.set 0 4
  have hx₁_bdd : x₁.Bounded w := hx.set hfit4
  have e_const : RDemonicExec (B := .exact) w L_peak (.op (.const 0 4)) x 1 (· = x₁) :=
    RDemonicExec.const (by omega) hfit4
  have hnodup : ([0, 1, 2, 3, 4, 5] : List (Fin 7)).Nodup := by decide
  have e_grow := growZeroCode_exec (w := w) (L_peak := L_peak)
    (count := 0) (result := 1) (cur := 2) (stop := 3) (zero := 4) (one := 5)
    hx₁_bdd hnodup h1 (by simp [x₁, L_peak]) (by simpa [x₁] using hfit_grow)
  set regs₂ : Fin 7 → ℕ :=
    Function.update (Function.update (Function.update (Function.update (Function.update
      x₁.regs 4 0) 5 1) 1 x₁.frontier) 2 x₁.frontier) 3 (x₁.frontier + x₁.regs 0) |>
      fun regs => Function.update regs 2 (x₁.frontier + x₁.regs 0)
  set x₂ : RData 7 := ⟨regs₂, x₁.mem, x₁.frontier + x₁.regs 0⟩
  have hx₂_fr : x₂.frontier = x.frontier + 4 := by simp [x₂, x₁]
  have hx₂_r0 : x₂.regs 0 = 4 := by simp [x₂, regs₂, x₁]
  have hx₂_r1 : x₂.regs 1 = x.frontier := by simp [x₂, regs₂, x₁]
  have hx₂_mem : x₂.mem = x.mem := rfl
  have d_rand : ExecRCodeDist (B := .exact) w (.rand 6 0) x₂
      ((ProbComp.unifFin (x₂.regs 0)).eval.map fun k => x₂.set 6 k.val) 1 L_peak :=
    ExecRCodeDist.rand (by rw [hx₂_fr]) (by rw [hx₂_r0]; exact hfit4)
  let postState (z : RData 7) : RData 7 := ⟨z.regs, x.mem, x.frontier⟩
  have htail : ∀ z ∈ ((ProbComp.unifFin (x₂.regs 0)).eval.map fun k => x₂.set 6 k.val).support,
      ExecRCodeDist (B := .exact) w
        (.seq (RCode.ofCode (.seq (.op (.store 1 6)) (.op (.load 6 1)))) (.shrink 0))
        z (PMF.pure (postState z)) 3 L_peak := by
    intro z hz
    rw [PMF.mem_support_map_iff] at hz
    obtain ⟨k, _, rfl⟩ := hz
    set z₀ := x₂.set 6 k.val
    have hz₀_r1 : z₀.regs 1 = x.frontier := by simp [z₀, hx₂_r1]
    have hz₀_r0 : z₀.regs 0 = 4 := by simp [z₀, hx₂_r0]
    have hz₀_fr : z₀.frontier = x.frontier + 4 := hx₂_fr
    have eb_st : ExecBounded (B := .exact) w (x.frontier + 1) (.op (.store 1 6)) z₀.toData
        (z₀.toData.write x.frontier k.val) 1 := by
      simpa [z₀, RData.toData, hz₀_r1, hx₂_r1] using
        ExecBounded.store (B := .exact) (w := w) (L := x.frontier + 1)
          (a := 1) (s := 6) (x := z₀.toData) (by simp [RData.toData, hz₀_r1])
    have eb_ld : ExecBounded (B := .exact) w (x.frontier + 1) (.op (.load 6 1))
        (z₀.toData.write x.frontier k.val)
        ((z₀.toData.write x.frontier k.val).set 6 k.val) 1 := by
      have hmem_at : (z₀.toData.write x.frontier k.val).mem
          ((z₀.toData.write x.frontier k.val).regs 1) = k.val := by
        simp [Data.write, RData.toData, hz₀_r1]
      have hld := ExecBounded.load (B := .exact) (w := w) (L := x.frontier + 1)
        (d := 6) (a := 1) (x := z₀.toData.write x.frontier k.val)
        (by simp [Data.write, RData.toData, hz₀_r1])
      rwa [hmem_at] at hld
    have ed_rw : RDemonicExec (B := .exact) w L_peak
        (RCode.ofCode (.seq (.op (.store 1 6)) (.op (.load 6 1)))) z₀ 2
        (· = ⟨z₀.regs, Function.update x.mem x.frontier k.val, x.frontier + 4⟩) := by
      have h12 := RDemonicExec.of_execBounded (x := z₀) (L_peak := L_peak)
        (by rw [hz₀_fr]) (by omega) (eb_st.seq eb_ld)
      refine h12.mono le_rfl ?_
      rintro _ rfl
      ext a
      · simp [z₀, Data.set, Data.write, RData.set, RData.toData]
      · simp [z₀, Data.set, Data.write, RData.set, RData.toData, hx₂_mem]
      · exact hz₀_fr
    set z₁ : RData 7 := ⟨z₀.regs, Function.update x.mem x.frontier k.val, x.frontier + 4⟩
    have hclear_eq : clear z₁.mem (z₁.frontier - z₁.regs 0) (z₁.regs 0) = x.mem := by
      funext a
      have hfr_sub : z₁.frontier - z₁.regs 0 = x.frontier := by simp [z₁, z₀, hz₀_r0]
      have hlen : z₁.regs 0 = 4 := by simp [z₁, z₀, hz₀_r0]
      rw [hfr_sub, hlen]
      by_cases hown : (Block.mk x.frontier 4).Owns a
      · rw [clear_of_owns hown]
        exact (hx.2.2 a hown.1).symm
      · rw [clear_of_not_owns hown]
        have hne : a ≠ x.frontier := by simp only [Block.Owns] at hown; omega
        simp [z₁, Function.update_of_ne hne]
    have ed_sh : RDemonicExec (B := .exact) w L_peak (.shrink 0) z₁ 1 (· = postState z₀) := by
      refine RDemonicExec.shrink (by simp [z₁, L_peak]) (by simp [z₁, z₀, hz₀_r0]) ?_
      rw [hclear_eq]
      simp [postState, z₁, z₀, hz₀_r0]
    exact ExecRCodeDist.of_demonicExec (ed_rw.seq_eq ed_sh)
  have d_mid := d_rand.seq_const htail (fun _ _ => le_rfl)
  have d_all : ExecRCodeDist (B := .exact) w growSampleShrinkCode x
      (((ProbComp.unifFin (x₂.regs 0)).eval.map fun k => x₂.set 6 k.val).bind
        (fun z => PMF.pure (postState z))) 28 L_peak := by
    have h := (ExecRCodeDist.of_demonicExec e_const).seq_pure
      ((ExecRCodeDist.of_demonicExec e_grow).seq_pure d_mid)
    simpa [growSampleShrinkCode, x₁, x₂, regs₂, add_assoc] using
      h.mono (by simp [x₁]; norm_num)
  have d_std := (d_all.mapSimulates Basis.Simulates.exactStandard).toExecRProgramDist 6
  refine ⟨_, ?_, d_std.mono (by norm_num) le_rfl⟩
  intro y hy
  rw [PMF.mem_support_bind_iff] at hy
  obtain ⟨z, hz, hyz⟩ := hy
  rw [PMF.support_pure, Set.mem_singleton_iff] at hyz
  rw [PMF.mem_support_map_iff] at hz
  obtain ⟨k, _, rfl⟩ := hz
  subst hyz
  refine ⟨rfl, rfl, ?_⟩
  have hk := k.isLt
  simp only [postState, RData.set, Function.update_self]
  omega

/-! ## 3. Geometric `while` loop (`ExecRCodeDist.loop_geometric`) -/

/-- Flip a fair coin into register `0` while `0 < r0` (`r2 = 0`, `r1 = 1`). -/
def coinFlipLoop : RCode .exact 3 :=
  .loop (.lt 2 0) (.rand 0 1)

/-- `ExecRCodeDist.loop_geometric` certifies `O(1)` expected steps and `PeakFrontierLe` on
`coinFlipLoop`. -/
theorem coinFlipLoop_execRCodeDist {w L_peak : ℕ} {x : RData 3}
    (hL : x.frontier ≤ L_peak) (hfit1 : Fits w 1) (hr1 : x.regs 1 = 1) (hr2 : x.regs 2 = 0) :
    ∃ μ : PMF (RData 3),
      (∀ y ∈ μ.support, y.regs 0 = 0 ∧ y.frontier ≤ L_peak) ∧
      ExecRCodeDist w coinFlipLoop x μ
        ((1 + 2) / (ProbComp.unifFin 1).eval 0 + 2) L_peak := by
  let I : RData 3 → Prop := fun z => z.regs 1 = 1 ∧ z.regs 2 = 0 ∧ z.frontier ≤ L_peak
  let Q : RData 3 → Prop := fun z => z.regs 2 = 0 ∧ z.frontier ≤ L_peak
  let μ_body : RData 3 → PMF (RData 3) := fun z =>
    (ProbComp.unifFin (z.regs 1)).eval.map fun k => z.set 0 k.val
  let p_exit : ℝ≥0∞ := (ProbComp.unifFin 1).eval 0
  have hp_pos : 0 < p_exit := by
    refine pos_iff_ne_zero.mpr ((PMF.mem_support_iff (ProbComp.unifFin 1).eval 0).mp ?_)
    rw [ProbComp.support_eval]
    exact ProbComp.mem_support_unifFin 1 0
  have hp_top : p_exit ≠ ⊤ := PMF.apply_ne_top (ProbComp.unifFin 1).eval 0
  have hinv_all : ∀ z : RData 3, I z → RLoopStateInv (.lt 2 0) I Q z := fun z hz => by
    by_cases hc : (Cond.lt 2 0).Holds z.toData
    · exact Or.inl ⟨hc, hz⟩
    · exact Or.inr ⟨hc, hz.2.1, hz.2.2⟩
  have hinv_step : ∀ z, I z → (Cond.lt 2 0).Holds z.toData →
      ∀ y ∈ (μ_body z).support, RLoopStateInv (.lt 2 0) I Q y := by
    intro z hz _ y hy
    rw [PMF.mem_support_map_iff] at hy
    obtain ⟨k, _, rfl⟩ := hy
    exact hinv_all _ ⟨by simp [hz.1], by simp [hz.2.1], hz.2.2⟩
  have hp_exit_le : ∀ z, I z → (Cond.lt 2 0).Holds z.toData →
      p_exit ≤ (μ_body z).toOuterMeasure {y : RData 3 | ¬(Cond.lt 2 0).Holds y.toData} := by
    classical
    intro z ⟨hz1, hz2, _⟩ _
    let y₀ := z.set 0 0
    have hy₀_mem : y₀ ∈ {y : RData 3 | ¬(Cond.lt 2 0).Holds y.toData} := by
      simp [y₀, Cond.Holds, RData.toData, RData.set, hz2]
    have hp_le_apply : p_exit ≤ μ_body z y₀ := by
      dsimp only [μ_body]
      rw [hz1, PMF.map_apply]
      refine le_trans ?_
        (le_tsum (f := fun k : Fin 2 =>
          if y₀ = z.set 0 k.val then (ProbComp.unifFin 1).eval k else 0) 0)
      simp [y₀, p_exit]
    refine hp_le_apply.trans ?_
    rw [PMF.toOuterMeasure_apply]
    refine le_trans ?_
      (le_tsum (f := Set.indicator {y : RData 3 | ¬(Cond.lt 2 0).Holds y.toData} (μ_body z)) y₀)
    rw [Set.indicator_of_mem hy₀_mem]
  have hx_inv : RLoopStateInv (.lt 2 0) I Q x := hinv_all x ⟨hr1, hr2, hL⟩
  have hexec := ExecRCodeDist.loop_geometric (B := .exact) (w := w) (L_peak := L_peak)
    (cond := .lt 2 0) (body := .rand 0 1) I Q
    (μ_body := μ_body) (T_body := fun _ => 1) (B_body := 1) (p_exit := p_exit) (x := x)
    hp_pos hp_top
    (fun z hz _ => ExecRCodeDist.rand hz.2.2 (by rw [hz.1]; exact hfit1))
    (fun _ _ _ => le_rfl)
    hinv_step
    hp_exit_le
    (fun _ _ hQz => hQz.2)
    hx_inv
  refine ⟨loopExitRPMF (.lt 2 0) μ_body x, fun y hy => ?_, hexec⟩
  obtain ⟨⟨hnc, hQy⟩, _⟩ := mem_support_loopExitRPMF hp_pos hp_top hinv_step hp_exit_le hx_inv hy
  simp only [Cond.Holds, RData.toData, hQy.1, not_lt, Nat.le_zero] at hnc
  exact ⟨hnc, hQy.2⟩

/-! ## 4. Soundness checks (`not_execRProgramDist_halt`) -/

/-- A 1-instruction `[.halt out]` stub cannot satisfy `ExecRProgramDist` for a transition that grows
`frontier` by `4` words. -/
theorem halt_cannot_fake_grow (w L_peak : ℕ) (out : Fin 2) (x : RData 2) (T : ℝ≥0∞) :
    ¬ExecRProgramDist (B := .standard) w [.halt out] out x
      (PMF.pure ⟨x.regs, x.mem, x.frontier + 4⟩) T L_peak := by
  refine not_execRProgramDist_halt (y := ⟨x.regs, x.mem, x.frontier + 4⟩) (by simp) ?_
  intro heq
  have hfr := congrArg RData.frontier heq
  dsimp only at hfr
  omega

/-- A 1-instruction `[.halt 0]` stub cannot satisfy `ExecRProgramDist` for a transition that
increments register `0`. -/
theorem halt_cannot_fake_inc (w L_peak : ℕ) (x : RData 2) (T : ℝ≥0∞) :
    ¬ExecRProgramDist (B := .standard) w [.halt 0] 0 x
      (PMF.pure (x.set 0 (x.regs 0 + 1))) T L_peak := by
  refine not_execRProgramDist_halt (y := x.set 0 (x.regs 0 + 1)) (by simp) ?_
  intro heq
  have hr := congrArg (fun d : RData 2 => d.regs 0) heq
  simp [RData.set] at hr

/-! ## 5. Word-granular resizable memory specification checks -/

/-- `Memory.Resizable.spec w` refines `Memory.Resizable.demonicSpec w` and preserves `Canonical w`
and disjoint `Block.Realizes` across resizes. -/
theorem memoryResizable_refinement_and_frame (w : ℕ) (b : Block)
    {s : Memory.State} {vs : Fin b.length → ℕ}
    (hcan : Memory.Resizable.Canonical w s) (hfit : Fits w (s.frontier + 8))
    (hb : b.Realizes s.mem vs) (hb_fit : b.base + b.length ≤ s.frontier) :
    let ref := Memory.Resizable.specRefinesDemonicSpec w
    Nonempty (Refinement (Memory.Resizable.demonicSpec w) (Memory.Resizable.spec w)) ∧
      Memory.Resizable.Canonical w (Memory.Resizable.step s (.grow 8)).1 ∧
      b.Realizes (Memory.Resizable.step s (.grow 8)).1.mem vs ∧
      ref.abs s = s := by
  refine ⟨Memory.Resizable.spec_refines_demonicSpec w,
    Memory.Resizable.canonical_step hcan hfit, ?_, rfl⟩
  refine Memory.Resizable.Block.realizes_of_unchangedOutside b hb ?_
    (Memory.Resizable.UnchangedOutside.step_grow s 8) (fun _ _ hmem => hmem)
  simp only [Memory.Resizable.step_grow]
  omega

end ComplexityTests.WordRAMResizable
