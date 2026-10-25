/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.Randomized
public import Complexity.Computability.WordRAM.Notation

/-!
# Randomized word-RAM unit tests

Verifies the randomized Word-RAM operational semantics, `ram[ ... ]` notation, and resource
measures:
* `rand(0)` returns `0` without faulting, charges `1` `rand` call (not `0`), and costs `0` entropy
  bits;
* `rand(2 ^ w - 1)` via the overflow-free `allOnes` setup (`1 ≤ w`) samples uniformly from
  `Fin (2 ^ w)` in `1` `rand` call and `w` entropy bits;
* `rand(n)` with `n ≥ 2 ^ w` on a raw unbounded state faults in `1` step;
* a two-call coin-sum program (`rand(1)` twice) produces the exact `(1/4, 1/2, 1/4)` law on
  `{0, 1, 2}` within `2` `rand` calls and `2` entropy bits;
* two-way deterministic agreement on `IsRandFree` programs.
-/

@[expose] public section

namespace ComplexityTests.WordRAMRandomized

open Cslib Cslib.WordRAM
open Cslib.Probability.PMF (uniformOfFintype uniformOfFintype_apply uniformOfFintype_map_equiv)
open scoped ENNReal

/-! ## 1. `rand(0)`: succeeds with `0`, charges `1` call and `0` bits -/

abbrev r0 : Fin 4 := 0
abbrev r1 : Fin 4 := 1
abbrev r2 : Fin 4 := 2
abbrev r3 : Fin 4 := 3

/-- Structured program executing `r0 ← rand r1` where `r1 = 0` on `Data.init []`. -/
abbrev randZeroCode : Code .standard 4 := ram[ r0 ← rand r1 ]

/-- Complete flat program for `rand(0)`. -/
abbrev randZeroProg : Program .standard 4 := randZeroCode.program r0

theorem randZero_eval (w : ℕ) :
    evalRand w randZeroProg 2 (.init []) =
      PMF.pure (.halted 0 ((Data.init [] : Data 4).set r0 0)) := by
  have hex : ExecRand w randZeroCode (.init []) (do
      let k ← ProbComp.unifFin 0
      pure (((Data.init [] : Data 4).set r0 k.val), 1)) :=
    ExecRand.rand (fits_zero w)
  have hrun := hex.runRand_program r0 (T := 2) fun z hz => by
    obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hk
    omega
  rw [evalRand, State.init, hrun, ProbComp.eval_map, ProbComp.eval_bind,
    ProbComp.eval_unifFin]
  have hunif0 : uniformOfFintype (Fin 1) = PMF.pure (0 : Fin 1) := by
    ext i
    rw [Subsingleton.elim i 0]
    simp [uniformOfFintype_apply]
  rw [hunif0, PMF.pure_bind, ProbComp.eval_pure, PMF.pure_map]
  rfl

theorem randZero_halts_and_calls (w : ℕ) :
    HaltsWithin w randZeroProg (.init []) 2 ∧
    RandCallsBounded w randZeroProg (.init []) 2 1 ∧
    RandBitsBounded w randZeroProg (.init []) 2 0 := by
  have hw : ExecRandWithin w randZeroCode (.init []) (fun y => y.regs r0 = 0) 1 1 :=
    ExecRandWithin.rand (fits_zero w) fun k => by
      have hk : k.val = 0 := Nat.lt_one_iff.mp k.isLt
      simp only [Data.set_regs, Function.update_self, hk]
  obtain ⟨hhalt, hcalls, -⟩ := hw.program r0 (T' := 2) le_rfl
  refine ⟨hhalt, hcalls, ?_⟩
  have hex : ExecRand w randZeroCode (.init []) (do
      let k ← ProbComp.unifFin 0
      pure (((Data.init [] : Data 4).set r0 k.val), 1)) :=
    ExecRand.rand (fits_zero w)
  have hrun := hex.runRand_program r0 (T := 2) fun z hz => by
    obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hk
    omega
  rw [RandBitsBounded, State.init, hrun]
  refine (OracleComp.isCostBounded_map_iff _ _ _).mpr ?_
  have hq : OracleComp.IsCostBounded unifBitCost (ProbComp.unifFin 0) (unifBitCost 0) :=
    OracleComp.IsCostBounded.query 0
  rw [unifBitCost_zero] at hq
  simpa only [Nat.add_zero] using hq.bind fun _ => .pure _ 0

/-- `rand(0)` genuinely charges `1` call: a budget of `0` calls is violated. -/
theorem randZero_not_zero_calls (w : ℕ) :
    ¬RandCallsBounded w randZeroProg (.init []) 2 0 := by
  intro h0
  have hex : ExecRand w randZeroCode (.init []) (do
      let k ← ProbComp.unifFin 0
      pure (((Data.init [] : Data 4).set r0 k.val), 1)) :=
    ExecRand.rand (fits_zero w)
  have hrun := hex.runRand_program r0 (T := 2) fun z hz => by
    obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hk
    omega
  rw [RandCallsBounded, State.init, hrun] at h0
  have h0' := (OracleComp.isCostBounded_map_iff _ _ _).mp h0
  obtain ⟨hle, -⟩ := OracleComp.IsCostBounded.liftBind_iff.mp h0'
  omega

/-! ## 2. `rand(2 ^ w - 1)` via overflow-free `allOnes` (`1 ≤ w`) -/

abbrev a_one : Fin 6 := 0
abbrev a_w : Fin 6 := 1
abbrev a_w1 : Fin 6 := 2
abbrev a_hi : Fin 6 := 3
abbrev a_lo : Fin 6 := 4
abbrev a_out : Fin 6 := 5

abbrev allOnesSetup : Code .standard 6 := ram[
  a_one ← #1;
  a_w ← width%;
  a_w1 ← a_w - a_one;
  a_hi ← a_one <<< a_w1;
  a_lo ← a_hi - a_one;
  a_lo ← a_hi + a_lo
]

/-- Computes `2 ^ w - 1` without overflow for any `1 ≤ w` and samples uniformly from
`[0, 2 ^ w - 1]`. -/
abbrev allOnesRandCode : Code .standard 6 := ram[
  ⟪allOnesSetup⟫;
  a_out ← rand a_lo
]

abbrev allOnesRandProg : Program .standard 6 := allOnesRandCode.program a_out

private theorem allOnesSetup_exec {w : ℕ} (hw : 1 ≤ w) (x : Data 6) :
    ∃ y, Exec w allOnesSetup x y 6 ∧ y.regs a_lo = 2 ^ w - 1 := by
  have hw0 : w ≠ 0 := by omega
  have h2w1 : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hpos_hi : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
  have hsum : 2 ^ (w - 1) + (2 ^ (w - 1) - 1) = 2 ^ w - 1 := by
    have hpow : 2 ^ w = 2 ^ (w - 1) + 2 ^ (w - 1) := by
      conv_lhs => rw [show w = (w - 1) + 1 by omega, Nat.pow_succ, Nat.mul_two]
    omega
  have hfit_mask : Fits w (2 ^ w - 1) := by
    rw [fits_iff]
    have : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    omega
  have e1 : Exec (B := .standard) w (.op (.const a_one 1)) x (x.set a_one 1) 1 :=
    Exec.const (fits_one hw0)
  let x1 := x.set a_one 1
  have e2 : Exec (B := .standard) w (.op (.width a_w)) x1 (x1.set a_w w) 1 := Exec.width
  let x2 := x1.set a_w w
  have hsub1 : Fits w (BinOp.sub.eval (x2.regs a_w) (x2.regs a_one)) := by
    simp only [x2, x1, Data.set_regs, Function.update_self,
      Function.update_of_ne (by decide : a_one ≠ a_w), BinOp.eval]
    exact (fits_self w).of_le (Nat.sub_le _ _)
  have e3 := Exec.bin (w := w) (x := x2) (f := .sub) (d := a_w1) (i := a_w) (j := a_one) hsub1
  let x3 := x2.set a_w1 (BinOp.sub.eval (x2.regs a_w) (x2.regs a_one))
  have hx3_w1 : x3.regs a_w1 = w - 1 := by
    simp only [x3, x2, x1, Data.set_regs, Function.update_self,
      Function.update_of_ne (by decide : a_one ≠ a_w), BinOp.eval]
  have hx3_one : x3.regs a_one = 1 := by
    simp only [x3, x2, x1, Data.set_regs, Function.update_self,
      Function.update_of_ne (by decide : a_one ≠ a_w1),
      Function.update_of_ne (by decide : a_one ≠ a_w)]
  have hshl : BinOp.shiftLeft.eval (x3.regs a_one) (x3.regs a_w1) = 2 ^ (w - 1) := by
    simp only [BinOp.eval, hx3_one, hx3_w1, Nat.shiftLeft_eq, Nat.one_mul]
  have e4 := Exec.bin (w := w) (x := x3) (f := .shiftLeft) (d := a_hi) (i := a_one) (j := a_w1)
    (by rw [fits_iff, hshl]; exact h2w1)
  let x4 := x3.set a_hi (BinOp.shiftLeft.eval (x3.regs a_one) (x3.regs a_w1))
  have hx4_hi : x4.regs a_hi = 2 ^ (w - 1) := by
    simp only [x4, Data.set_regs, Function.update_self, hshl]
  have hx4_one : x4.regs a_one = 1 := by
    simp only [x4, Data.set_regs, Function.update_of_ne (by decide : a_one ≠ a_hi), hx3_one]
  have hsub2 : BinOp.sub.eval (x4.regs a_hi) (x4.regs a_one) = 2 ^ (w - 1) - 1 := by
    simp only [BinOp.eval, hx4_hi, hx4_one]
  have e5 := Exec.bin (w := w) (x := x4) (f := .sub) (d := a_lo) (i := a_hi) (j := a_one)
    (by rw [fits_iff, hsub2]; omega)
  let x5 := x4.set a_lo (BinOp.sub.eval (x4.regs a_hi) (x4.regs a_one))
  have hx5_hi : x5.regs a_hi = 2 ^ (w - 1) := by
    simp only [x5, Data.set_regs, Function.update_of_ne (by decide : a_hi ≠ a_lo), hx4_hi]
  have hx5_lo : x5.regs a_lo = 2 ^ (w - 1) - 1 := by
    simp only [x5, Data.set_regs, Function.update_self, hsub2]
  have hadd : BinOp.add.eval (x5.regs a_hi) (x5.regs a_lo) = 2 ^ w - 1 := by
    simp only [BinOp.eval, hx5_hi, hx5_lo, hsum]
  have e6 := Exec.bin (w := w) (x := x5) (f := .add) (d := a_lo) (i := a_hi) (j := a_lo)
    (by rw [hadd]; exact hfit_mask)
  let x6 := x5.set a_lo (BinOp.add.eval (x5.regs a_hi) (x5.regs a_lo))
  refine ⟨x6, ?_, by simp only [x6, Data.set_regs, Function.update_self, hadd]⟩
  exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))

/-- `allOnesRandProg` halts in `8` steps using `1` `rand` call (`w` bits) and induces the exact
uniform distribution on `Fin (2 ^ w)` (`[0, 2 ^ w - 1]`). -/
theorem allOnesRand_uniform {w : ℕ} (hw : 1 ≤ w) :
    HaltsWithin w allOnesRandProg (.init []) 8 ∧
    RandCallsBounded w allOnesRandProg (.init []) 8 1 ∧
    RandBitsBounded w allOnesRandProg (.init []) 8 w ∧
    ((evalRand w allOnesRandProg 8 (.init [])).map fun
      | .halted v _ => v
      | _ => 0) = (uniformOfFintype (Fin (2 ^ w))).map Fin.val := by
  obtain ⟨y, hy_exec, hy_lo⟩ := allOnesSetup_exec hw (.init [])
  have hfit : Fits w (y.regs a_lo) := by
    rw [fits_iff, hy_lo]
    have : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    omega
  have hex : ExecRand w allOnesRandCode (.init [])
      ((fun z => (z.1, 6 + z.2)) <$> do
        let k ← ProbComp.unifFin (y.regs a_lo)
        pure (y.set a_out k.val, 1)) :=
    hy_exec.seqRand (ExecRand.rand hfit)
  have hT : ∀ z ∈ (((fun z : Data 6 × ℕ => (z.1, 6 + z.2)) <$> do
      let k ← ProbComp.unifFin (y.regs a_lo)
      pure (y.set a_out k.val, 1))).support, z.2 + 1 ≤ 8 := by
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₀
    cases OracleComp.eq_of_mem_supportWith_pure hk
    omega
  have hrun := hex.runRand_program a_out (T := 8) hT
  have hhalt : HaltsWithin w allOnesRandProg (.init []) 8 := by
    intro cfg hcfg
    rw [State.init, hrun] at hcfg
    obtain ⟨z, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    exact ⟨z.1.regs a_out, z.1, rfl⟩
  have hcalls : RandCallsBounded w allOnesRandProg (.init []) 8 1 := by
    rw [RandCallsBounded, State.init, hrun]
    refine (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.isCostBounded_map_iff _ _ _).mpr ?_)
    simpa only [Nat.add_zero] using
      (ProbComp.isQueryBounded_unifFin (y.regs a_lo)).bind fun _ => .pure _ 0
  have hbits : RandBitsBounded w allOnesRandProg (.init []) 8 w := by
    simpa only [Nat.one_mul] using hcalls.randBitsBounded
  refine ⟨hhalt, hcalls, hbits, ?_⟩
  have hm_eq : ((fun z => Cfg.halted (z.1.regs a_out) z.1) <$>
      ((fun z => (z.1, 6 + z.2)) <$> do
        let k ← ProbComp.unifFin (y.regs a_lo)
        pure (y.set a_out k.val, 1))) =
      (fun k => Cfg.halted k.val (y.set a_out k.val)) <$> ProbComp.unifFin (y.regs a_lo) := by
    simp only [← bind_pure_comp, bind_assoc, pure_bind, Data.set_regs, Function.update_self]
  rw [evalRand, State.init, hrun, hm_eq, ProbComp.eval_map, PMF.map_comp, ProbComp.eval_unifFin]
  have hcard : y.regs a_lo + 1 = 2 ^ w := by
    rw [hy_lo]
    exact Nat.sub_add_cancel Nat.one_le_two_pow
  have hunif : uniformOfFintype (Fin (2 ^ w)) =
      (uniformOfFintype (Fin (y.regs a_lo + 1))).map (finCongr hcard) :=
    (uniformOfFintype_map_equiv (finCongr hcard)).symm
  rw [hunif, PMF.map_comp]
  congr 1

/-! ## 3. `n ≥ 2 ^ w` faults on unbounded raw states -/

theorem rand_out_of_range_faults (w : ℕ) (n : ℕ) (hn : 2 ^ w ≤ n) :
    let p : Program .standard 1 := [.rand 0 0, .halt 0]
    let s : State 1 := ⟨0, ⟨fun _ => n, fun _ => 0⟩⟩
    runRand w p 1 (.running s) = pure .faulted ∧
    evalRand w p 1 s = PMF.pure .faulted ∧
    ¬FaultFree w p s ∧
    ∀ T, ¬HaltsWithin w p s T := by
  intro p s
  have hnot : ¬Fits w (s.data.regs 0) := by
    rw [fits_iff]
    change ¬n < 2 ^ w
    omega
  have h1 : runRand w p 1 (.running s) = pure .faulted := by
    rw [runRand_succ, stepRand_rand_of_not_fits (by rfl) hnot, pure_bind, runRand_zero]
  have heval : evalRand w p 1 s = PMF.pure .faulted := by
    simp only [evalRand, h1, ProbComp.eval_pure]
  have hnf : ¬FaultFree w p s := fun hff => hff 1 (by rw [h1]; rfl)
  exact ⟨h1, heval, hnf, fun T hhw => hnf hhw.faultFree⟩

/-! ## 4. Multi-call distribution: sum of two `rand(1)` coins is `(1/4, 1/2, 1/4)` -/

/-- Draws two independent uniform bits via `rand(1)` and returns their sum in `r3`. -/
abbrev twoCoinsCode : Code .standard 4 := ram[
  r0 ← #1;
  r1 ← rand r0;
  r2 ← rand r0;
  r3 ← r1 + r2
]

abbrev twoCoinsProg : Program .standard 4 := twoCoinsCode.program r3

theorem twoCoins_dist {w : ℕ} (hw : 2 ≤ w) :
    let outLaw := (evalRand w twoCoinsProg 5 (.init [])).map fun
      | .halted v _ => v
      | _ => 99
    HaltsWithin w twoCoinsProg (.init []) 5 ∧
    RandCallsBounded w twoCoinsProg (.init []) 5 2 ∧
    outLaw 0 = (1 : ℝ≥0∞) / 4 ∧
    outLaw 1 = (1 : ℝ≥0∞) / 2 ∧
    outLaw 2 = (1 : ℝ≥0∞) / 4 := by
  intro outLaw
  have hfit1 : Fits w 1 := fits_one (by omega)
  have hfit2 : Fits w 2 := by
    rw [fits_iff]
    have : 2 ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    omega
  let x0 : Data 4 := .init []
  let x1 : Data 4 := x0.set r0 1
  have e0 : Exec (B := .standard) w (.op (.const r0 1)) x0 x1 1 := Exec.const hfit1
  have hx1_0 : x1.regs r0 = 1 := by simp only [x1, Data.set_regs, Function.update_self]
  have hr1 : ExecRand (B := .standard) w (.rand r1 r0) x1 (do
      let k1 ← ProbComp.unifFin 1
      pure (x1.set r1 k1.val, 1)) := by
    have h := ExecRand.rand (B := .standard) (w := w) (x := x1) (dst := r1) (src := r0)
      (by rw [hx1_0]; exact hfit1)
    rw [hx1_0] at h
    exact h
  have hr23 : ∀ z₁ ∈ (do
        let k1 ← ProbComp.unifFin 1
        pure (x1.set r1 k1.val, 1) : ProbComp (Data 4 × ℕ)).support,
      ExecRand (B := .standard) w (ram[ r2 ← rand r0; r3 ← r1 + r2 ]) z₁.1 (do
        let k2 ← ProbComp.unifFin 1
        pure ((z₁.1.set r2 k2.val).set r3 (z₁.1.regs r1 + k2.val), 2)) := by
    intro z₁ hz₁
    obtain ⟨k1, -, hk1⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁
    cases OracleComp.eq_of_mem_supportWith_pure hk1
    have hregs0 : (x1.set r1 k1.val).regs r0 = 1 := by
      simp only [x1, Data.set_regs, Function.update_self,
        Function.update_of_ne (by decide : r0 ≠ r1)]
    have h_r2 : ExecRand (B := .standard) w (.rand r2 r0) (x1.set r1 k1.val) (do
        let k2 ← ProbComp.unifFin 1
        pure ((x1.set r1 k1.val).set r2 k2.val, 1)) := by
      have h := ExecRand.rand (B := .standard) (w := w) (x := x1.set r1 k1.val)
        (dst := r2) (src := r0) (by rw [hregs0]; exact hfit1)
      rw [hregs0] at h
      exact h
    have h_seq := ExecRand.seq h_r2
      (m₂ := fun y => pure (y.set r3 (y.regs r1 + y.regs r2), 1))
      fun z₂ hz₂ => by
        obtain ⟨k2, -, hk2⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₂
        cases OracleComp.eq_of_mem_supportWith_pure hk2
        have hsum_fit : Fits w
            (BinOp.add.eval (((x1.set r1 k1.val).set r2 k2.val).regs r1)
              (((x1.set r1 k1.val).set r2 k2.val).regs r2)) := by
          simp only [BinOp.eval, Data.set_regs, Function.update_self,
            Function.update_of_ne (by decide : r1 ≠ r2)]
          exact hfit2.of_le (by omega)
        simpa only [BinOp.eval] using
          (Exec.bin (x := (x1.set r1 k1.val).set r2 k2.val)
            (f := .add) (d := r3) (i := r1) (j := r2) hsum_fit).execRand
    convert h_seq using 1
    rw [bind_assoc]
    refine congrArg (ProbComp.unifFin 1 >>= ·) (funext fun k2 => ?_)
    simp only [pure_bind, Data.set_regs, Function.update_self,
      Function.update_of_ne (by decide : r1 ≠ r2), show 1 + 1 = 2 by rfl]
  let m1 : ProbComp (Data 4 × ℕ) := do
    let k1 ← ProbComp.unifFin 1
    pure (x1.set r1 k1.val, 1)
  let m2 (u : Data 4) : ProbComp (Data 4 × ℕ) := do
    let k2 ← ProbComp.unifFin 1
    pure ((u.set r2 k2.val).set r3 (u.regs r1 + k2.val), 2)
  have hex : ExecRand w twoCoinsCode x0
      ((fun z => (z.1, 1 + z.2)) <$> (do
        let z₁ ← m1
        let z₂ ← m2 z₁.1
        pure (z₂.1, z₁.2 + z₂.2))) :=
    e0.seqRand (ExecRand.seq hr1 hr23)
  have hT : ∀ z ∈ (((fun z : Data 4 × ℕ => (z.1, 1 + z.2)) <$> (do
        let z₁ ← m1
        let z₂ ← m2 z₁.1
        pure (z₂.1, z₁.2 + z₂.2)))).support, z.2 + 1 ≤ 5 := by
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₀
    obtain ⟨k1, -, hk1⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁
    cases OracleComp.eq_of_mem_supportWith_pure hk1
    obtain ⟨z₂, hz₂, hfin⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    obtain ⟨k2, -, hk2⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₂
    cases OracleComp.eq_of_mem_supportWith_pure hk2
    cases OracleComp.eq_of_mem_supportWith_pure hfin
    omega
  have hrun := hex.runRand_program r3 (T := 5) hT
  have hhalt : HaltsWithin w twoCoinsProg (.init []) 5 := by
    intro cfg hcfg
    rw [State.init, hrun] at hcfg
    obtain ⟨z, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    exact ⟨z.1.regs r3, z.1, rfl⟩
  have hcalls : RandCallsBounded w twoCoinsProg (.init []) 5 2 := by
    rw [RandCallsBounded, State.init, hrun]
    refine (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.isCostBounded_map_iff _ _ _).mpr ?_)
    have hq1 : m1.IsQueryBounded 1 := by
      simpa only [Nat.add_zero] using (ProbComp.isQueryBounded_unifFin 1).bind fun _ => .pure _ 0
    rw [show (2 : ℕ) = 1 + 1 from rfl]
    refine hq1.bind fun z₁ => ?_
    have hq2 : (m2 z₁.1).IsQueryBounded 1 := by
      simpa only [Nat.add_zero] using (ProbComp.isQueryBounded_unifFin 1).bind fun _ => .pure _ 0
    simpa only [Nat.add_zero] using hq2.bind fun _ => .pure _ 0
  have houtLaw : outLaw = ((ProbComp.unifFin 1).eval.bind fun k1 =>
      (ProbComp.unifFin 1).eval.map fun k2 => k1.val + k2.val) := by
    have hm_eq : ((fun z => Cfg.halted (z.1.regs r3) z.1) <$>
        ((fun z => (z.1, 1 + z.2)) <$> (do
          let z₁ ← m1
          let z₂ ← m2 z₁.1
          pure (z₂.1, z₁.2 + z₂.2)))) =
        (do
          let k1 ← ProbComp.unifFin 1
          let k2 ← ProbComp.unifFin 1
          pure (Cfg.halted (k1.val + k2.val)
            (((x1.set r1 k1.val).set r2 k2.val).set r3 (k1.val + k2.val)))) := by
      simp only [m1, m2, ← bind_pure_comp, bind_assoc, pure_bind, Data.set_regs,
        Function.update_self]
    change ((evalRand w twoCoinsProg 5 (.init [])).map _) = _
    rw [evalRand, State.init, hrun, hm_eq, ← ProbComp.eval_map]
    simp only [← bind_pure_comp, bind_assoc, pure_bind, ProbComp.eval_bind]
    refine congrArg ((ProbComp.unifFin 1).eval.bind ·) (funext fun k1 => ?_)
    rw [← ProbComp.eval_map, ← ProbComp.eval_bind]
    rfl
  have hval (v : ℕ) : outLaw v =
      ∑ k1 : Fin 2, (2 : ℝ≥0∞)⁻¹ *
        ∑ k2 : Fin 2, (2 : ℝ≥0∞)⁻¹ * (if k1.val + k2.val = v then 1 else 0) := by
    rw [houtLaw, ProbComp.eval_unifFin, PMF.bind_apply, tsum_fintype]
    refine Finset.sum_congr rfl fun k1 _ => ?_
    rw [uniformOfFintype_apply, Fintype.card_fin, Nat.cast_two, PMF.map_apply, tsum_fintype]
    congr 1
    refine Finset.sum_congr rfl fun k2 _ => ?_
    rw [uniformOfFintype_apply, Fintype.card_fin, Nat.cast_two]
    by_cases h : k1.val + k2.val = v
    · simp only [h, ↓reduceIte, mul_one]
    · have h' : v ≠ k1.val + k2.val := Ne.symm h
      simp only [h, h', ↓reduceIte, mul_zero]
  have hinv : (2 : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ = (1 : ℝ≥0∞) / 4 := by
    rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  refine ⟨hhalt, hcalls, ?_, ?_, ?_⟩
  · rw [hval 0, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, ↓reduceIte, mul_one,
      Nat.reduceAdd, Nat.reduceEqDiff, one_ne_zero, mul_zero, add_zero, zero_add]
    exact hinv
  · rw [hval 1, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, zero_ne_one, ↓reduceIte, mul_zero,
      zero_add, mul_one, Nat.add_eq_left, one_ne_zero, add_zero]
    rw [hinv, ← two_mul, show (2 : ℝ≥0∞) * (1 / 4) = 1 / 2 by
      rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, one_mul,
        show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
        ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
        ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]]
  · rw [hval 2, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, Nat.reduceEqDiff, ↓reduceIte, mul_zero,
      add_zero, mul_one, zero_add]
    exact hinv

/-! ## 5. Deterministic `IsRandFree` agreement non-vacuity check -/

abbrev detAddCode : Code .standard 4 := ram[
  r0 ← #3;
  r1 ← #4;
  r2 ← r0 + r1
]

abbrev detAddProg : Program .standard 4 := detAddCode.program r2

theorem detAdd_isRandFree : detAddProg.IsRandFree :=
  detAddCode.isRandFree_program.mpr (by decide)

theorem detAdd_agrees :
    (∃ d, runRand 4 detAddProg 4 (.running (.init [])) = pure (.halted 7 d)) ∧
    ∃ n ≤ 4, Executes 4 detAddProg (.init []) 7 n := by
  have he : Exec 4 detAddCode (.init [])
      ((((Data.init [] : Data 4).set r0 3).set r1 4).set r2 7) 3 := by
    have e1 : Exec (B := .standard) 4 (.op (.const r0 3)) (.init [])
        ((Data.init [] : Data 4).set r0 3) 1 :=
      Exec.const (by decide)
    have e2 : Exec (B := .standard) 4 (.op (.const r1 4)) ((Data.init [] : Data 4).set r0 3)
        (((Data.init [] : Data 4).set r0 3).set r1 4) 1 :=
      Exec.const (by decide)
    have e3 : Exec (B := .standard) 4 (.op (.bin .add r2 r0 r1))
        (((Data.init [] : Data 4).set r0 3).set r1 4)
        ((((Data.init [] : Data 4).set r0 3).set r1 4).set r2 7) 1 :=
      Exec.bin (by decide)
    exact e1.seq (e2.seq e3)
  have hrun := he.runRand_program r2 (T := 4) le_rfl
  have hex_d : ∃ d, runRand 4 detAddProg 4 (.running (.init [])) = pure (.halted 7 d) :=
    ⟨_, hrun⟩
  exact ⟨hex_d,
    (exists_data_runRand_eq_pure_halted_iff_executes_of_isRandFree detAdd_isRandFree).mp hex_d⟩

end ComplexityTests.WordRAMRandomized

end
