/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.MSB
public import Complexity.Computability.WordRAM.Multiword.Circuit
public import Complexity.Computability.WordRAM.Multiword.Compile
public import Complexity.Computability.WordRAM.Multiword.CircuitRun
public import Complexity.Computability.WordRAM.Compile
import Mathlib.Tactic.FinCases

/-!
# Checked constant-instruction most-significant-bit execution

The 44 virtual slots spell out the arithmetic in `MSB.msb`. Slot zero holds the input;
the other 43 slots are constants or binary standard RAM operations. The checked compiler
expands them into standard instructions at the original physical word width, using eighteen
half-word digits per virtual value. Every virtual intermediate fits in `6w` bits.

## Main definitions

* `MSB.Program.values`: the mathematical value at each virtual slot.
* `MSB.Program.ops`: the source operations, with an unused placeholder at slot zero.
* `MSB.Program.output`, `MSB.Program.zeroTest`: physical registers for the final scalar answer and
  input-zero test.
* `MSB.Program.positiveCode`, `MSB.Program.twoBitCode`, `MSB.Program.code`,
  `MSB.Program.finishCode`: the compiled multiword graph, width-two fallback, and zero-dispatch
  wrappers.
* `MSB.Program.scalarCode`: composable register entry with charged workspace initialization.
* `MSB.Program.program`: a halting program for the ordinary singleton input encoding.

## Main results

* `MSB.Program.eval_ops`: each executed operation computes its specified value.
* `MSB.Program.ops_earlier`: each operation reads only earlier slots.
* `MSB.Program.values_output`: the final slot contains the highest set-bit index.
* `MSB.Program.exec_scalarCode`: arbitrary-memory register entry for widths at least three.
* `MSB.Program.executes_program`: halting execution within 200001 instructions for `w ≥ 2`.

Code depends on the width through preprocessing constants, with uniformly bounded size and
836 physical registers. The scalar entry uses registers four and six for input and output;
the remainder of its register workspace may change. Memory is preserved exactly. There is
no uniform fixed-code preprocessing theorem or claim that the constants are generated at run time.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.MSB.Program

open Cslib.WordRAM
open Cslib.WordRAM.Multiword.Circuit

/-- The values of the 44 virtual slots. The two comparison/count stages use the
named pure expressions from `MSB`, so their intermediate bounds remain reusable. -/
def values (s x : ℕ) : Fin 44 → ℕ :=
  let f := clusterMask s
  let h := x &&& f
  let r := x ^^^ h
  let d := f - r
  let e := d &&& f
  let y := clusterMarkers s x
  let z := clusterSummary s x
  let c := smallMSB s z
  let v := (x >>> (c * s)) &&& (2 ^ s - 1)
  ![x, f, h, r, d, e, f ^^^ e, y, compressionMultiplier s,
    y * compressionMultiplier s, s * s,
    (y * compressionMultiplier s) >>> (s * s), 2 ^ s - 1, z,
    2 ^ s, 2 ^ s + z, ones s, (2 ^ s + z) * ones s, powers s,
    (2 ^ s + z) * ones s - powers s, guards s,
    ((2 ^ s + z) * ones s - powers s) &&& guards s, s, powerFlags s z,
    powerFlags s z * ones s, (s - 1) * (s + 1),
    (powerFlags s z * ones s) >>> ((s - 1) * (s + 1)),
    2 ^ (s + 1) - 1, powerCount s z, 1, c, c * s, x >>> (c * s), v,
    2 ^ s + v, (2 ^ s + v) * ones s, (2 ^ s + v) * ones s - powers s,
    ((2 ^ s + v) * ones s - powers s) &&& guards s, powerFlags s v,
    powerFlags s v * ones s,
    (powerFlags s v * ones s) >>> ((s - 1) * (s + 1)),
    powerCount s v, smallMSB s v, c * s + smallMSB s v]

/-- Source operations in destination order. Slot zero is an unused placeholder:
execution starts at slot one with the input already present in slot zero. -/
def ops (s : ℕ) : Fin 44 → Operation 44 :=
  ![.constant 0, .constant (clusterMask s), .binary .and 0 1,
    .binary .xor 0 2, .binary .sub 1 3, .binary .and 4 1,
    .binary .xor 1 5, .binary .or 2 6, .constant (compressionMultiplier s),
    .binary .mul 7 8, .constant (s * s), .binary .shiftRight 9 10,
    .constant (2 ^ s - 1), .binary .and 11 12, .constant (2 ^ s),
    .binary .add 14 13, .constant (ones s), .binary .mul 15 16,
    .constant (powers s), .binary .sub 17 18, .constant (guards s),
    .binary .and 19 20, .constant s, .binary .shiftRight 21 22,
    .binary .mul 23 16, .constant ((s - 1) * (s + 1)),
    .binary .shiftRight 24 25, .constant (2 ^ (s + 1) - 1),
    .binary .and 26 27, .constant 1, .binary .sub 28 29,
    .binary .mul 30 22, .binary .shiftRight 0 31, .binary .and 32 12,
    .binary .add 14 33, .binary .mul 34 16, .binary .sub 35 18,
    .binary .and 36 20, .binary .shiftRight 37 22, .binary .mul 38 16,
    .binary .shiftRight 39 25, .binary .and 40 27, .binary .sub 41 29,
    .binary .add 31 42]

/-- Slot zero is the supplied input. -/
private theorem values_input (s x : ℕ) : values s x 0 = x := rfl

-- Reducing both 44-entry vectors in the last finite cases exceeds the default depth.
set_option maxRecDepth 2048 in
/-- Every executed source node agrees with its pure arithmetic expression. -/
theorem eval_ops (s x : ℕ) (i : Fin 44) (hi : i ≠ 0) :
    (ops s i).eval (values s x) = values s x i := by
  fin_cases i <;> first | exact (hi rfl).elim | rfl

/-- All source operands precede their destination, including the unused constant
placeholder at zero. Hence each executed destination is fresh. -/
theorem ops_earlier (s : ℕ) (i : Fin 44) : (ops s i).Earlier i := by
  fin_cases i <;> first | exact True.intro | exact ⟨by decide, by decide⟩

/-- On nonzero inputs, the last slot is exactly the arithmetic expression `msb`. -/
private theorem values_output_msb (s x : ℕ) (hx : 0 < x) :
    values s x 43 = msb s x := by
  simp [values, msb, show x ≠ 0 by omega]

/-- With the width-dependent cluster size, the final source value is the highest
set-bit index. This is a source-graph result, without a RAM execution assertion. -/
theorem values_output {w x : ℕ} (hx0 : 0 < x) (hx : x < 2 ^ w) :
    values (clusterSize w) x 43 = x.log2 := by
  rw [values_output_msb _ _ hx0]
  exact widthMSB_eq_log2 hx

/-- Each virtual value occurs in an audited stage list, apart from the unit constant,
the selected-cluster offset, the unmasked selected input, and the final output. -/
private theorem values_mem (s x : ℕ) (i : Fin 44) :
    values s x i ∈ clusterStageValues s x ∨
    values s x i ∈ powerStageValues s (clusterSummary s x) ∨
    values s x i ∈ powerStageValues s
      ((x >>> (smallMSB s (clusterSummary s x) * s)) &&& (2 ^ s - 1)) ∨
    values s x i = 1 ∨
    values s x i = smallMSB s (clusterSummary s x) * s ∨
    values s x i = x >>> (smallMSB s (clusterSummary s x) * s) ∨
    values s x i = values s x 43 := by
  fin_cases i <;> simp [values, clusterStageValues, powerStageValues]

/-- All 44 virtual values fit in the audited `6w` virtual bits. -/
private theorem values_lt {w x : ℕ} (hw : 0 < w) (hx0 : 0 < x) (hx : x < 2 ^ w)
    (i : Fin 44) : values (clusterSize w) x i < 2 ^ (6 * w) := by
  obtain ⟨hc, hz, hv, hoff, hout⟩ := widthMSB_virtual_bounds hw hx
  rcases values_mem (clusterSize w) x i with h | h | h | h | h | h | h
  · exact hc _ h
  · exact hz _ h
  · exact hv _ h
  · rw [h]
    exact Nat.one_lt_two_pow (by omega)
  · rw [h]
    exact hoff
  · rw [h, Nat.shiftRight_eq_div_pow]
    exact (Nat.div_le_self _ _).trans_lt
      (hx.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  · rw [h, values_output_msb _ _ hx0]
    exact hout

/-- At widths at least three, the precomputed cluster size is strictly smaller than
the physical width. -/
private theorem clusterSize_lt {w : ℕ} (hw : 3 ≤ w) : clusterSize w < w := by
  obtain ⟨_, _, hsq, hsw⟩ := clusterSize_bounds (show 0 < w by omega)
  by_contra h
  have he : clusterSize w = w := by omega
  rw [he] at hsq
  nlinarith

/-- Twice the physical width itself fits in a physical word at widths at least three. -/
private theorem twice_width_lt {w : ℕ} (hw : 3 ≤ w) : 2 * w < 2 ^ w := by
  induction w, hw using Nat.le_induction with
  | base => decide
  | succ w hw ih =>
    rw [pow_succ]
    nlinarith

/-- The two guarded comparison inputs and their sums fit in physical words. -/
private theorem guarded_fits {w z : ℕ} (hw : 3 ≤ w) (hz : z < 2 ^ clusterSize w) :
    Fits w (2 ^ clusterSize w) ∧ Fits w z ∧ Fits w (2 ^ clusterSize w + z) := by
  have hs := clusterSize_lt hw
  have hp : 2 ^ clusterSize w < 2 ^ w := Nat.pow_lt_pow_right (by decide) hs
  refine ⟨hp, hz.trans hp, ?_⟩
  have hadd : 2 ^ clusterSize w + z < 2 ^ (clusterSize w + 1) := by
    rw [pow_succ]
    omega
  exact hadd.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

/-- Every shift count used by the source graph fits in one physical word. -/
private theorem shift_amounts_fit {w x : ℕ} (hw : 3 ≤ w) :
    Fits w (clusterSize w * clusterSize w) ∧ Fits w (clusterSize w) ∧
    Fits w ((clusterSize w - 1) * (clusterSize w + 1)) ∧
    Fits w (smallMSB (clusterSize w) (clusterSummary (clusterSize w) x) *
      clusterSize w) := by
  obtain ⟨hs, _, hsq, hsw⟩ := clusterSize_bounds (show 0 < w by omega)
  have htw := twice_width_lt hw
  have hc := smallMSB_lt hs (clusterSummary_lt (clusterSize w) x)
  refine ⟨hsq.trans_lt htw, ?_, ?_, ?_⟩
  · exact hsw.trans_lt (by have := Nat.lt_two_pow_self (n := w); exact this)
  · have hpred : (clusterSize w - 1) * (clusterSize w + 1) ≤
        clusterSize w * clusterSize w := by
      have hp : clusterSize w - 1 + 1 = clusterSize w := by omega
      nlinarith
    exact (hpred.trans hsq).trans_lt htw
  · have hmul := Nat.mul_le_mul_right (clusterSize w) hc.le
    exact (hmul.trans hsq).trans_lt htw

/-- The final addition has fitting operands and result. -/
private theorem output_add_fits {w x : ℕ} (hx0 : 0 < x) (hx : x < 2 ^ w) :
    let s := clusterSize w
    let c := smallMSB s (clusterSummary s x)
    let v := (x >>> (c * s)) &&& (2 ^ s - 1)
    Fits w (c * s) ∧ Fits w (smallMSB s v) ∧ Fits w (c * s + smallMSB s v) := by
  dsimp only
  have he := values_output hx0 hx
  change smallMSB (clusterSize w) (clusterSummary (clusterSize w) x) * clusterSize w +
    smallMSB (clusterSize w)
      ((x >>> (smallMSB (clusterSize w) (clusterSummary (clusterSize w) x) *
        clusterSize w)) &&& (2 ^ clusterSize w - 1)) = x.log2 at he
  have hl : x.log2 < w := (Nat.log2_lt (by omega)).mpr hx
  have hfit : x.log2 < 2 ^ w := hl.trans Nat.lt_two_pow_self
  unfold Fits
  omega

/-- Every executed node satisfies the concrete multiword compiler's admissibility
contract. Only the additions and shift counts require physical-word bounds. -/
private theorem ops_admissible {w x : ℕ} (hw : 3 ≤ w) (hx0 : 0 < x) (hx : x < 2 ^ w)
    (i : Fin 44) (hi : i ≠ 0) :
    (ops (clusterSize w) i).Admissible w (values (clusterSize w) x) := by
  have hbound : (ops (clusterSize w) i).eval (values (clusterSize w) x) <
      2 ^ (6 * w) := by
    rw [eval_ops _ _ _ hi]
    exact values_lt (by omega) hx0 hx i
  have hz := guarded_fits hw (clusterSummary_lt (clusterSize w) x)
  have hv := guarded_fits hw (z :=
      (x >>> (smallMSB (clusterSize w) (clusterSummary (clusterSize w) x) *
        clusterSize w)) &&& (2 ^ clusterSize w - 1)) (by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos _))
  have hs := shift_amounts_fit (x := x) hw
  have ho := output_add_fits hx0 hx
  refine ⟨hbound, ?_⟩
  fin_cases i <;> first
    | exact True.intro
    | exact hz
    | exact hv
    | exact ho
    | exact hs.1
    | exact hs.2.1
    | exact hs.2.2.1
    | exact hs.2.2.2

open Cslib.WordRAM
open Cslib.WordRAM.Multiword

/-- Physical register containing the final scalar answer. -/
abbrev output : Fin (Bank.capacity 44 + 4) := ⟨6, by decide⟩

/-- A physical zero used for the input-zero branch. -/
abbrev zeroTest : Fin (Bank.capacity 44 + 4) := ⟨5, by decide⟩

/-- The forty-three arithmetic nodes, followed by checked scalar reconstruction. -/
def positiveCode (w : ℕ) : Code .standard (Bank.capacity 44 + 4) :=
  .seq (Circuit.run (Circuit.emit w) (ops (clusterSize w)) 1 43)
    (Transfer.assemble (Bank.regs (43 : Fin 44)) output)

private theorem size_positiveCode (w : ℕ) : (positiveCode w).size ≤ 172045 := by
  have hrun := Circuit.size_run (Circuit.emit w) (Circuit.size_emit w)
    (ops (clusterSize w)) 1 43
  simp only [positiveCode, Code.size, Transfer.size_assemble, Bank.length_regs]
  omega

/-- Execution of the actual expanded graph on a positive input. Every virtual operation is
discharged by `Circuit.exec_emit`, which uses the checked single-word routines. -/
private theorem exec_positiveCode {w z : ℕ} (hw : 3 ≤ w) (hz0 : 0 < z) (hz : z < 2 ^ w)
    (x : Data (Bank.capacity 44 + 4))
    (hx : Bank.Encodes w x (Circuit.prefix (values (clusterSize w) z) 1)) :
    ∃ y, ExecWithin w (positiveCode w) x y 172045 ∧
      y.regs output = z.log2 ∧ y.mem = x.mem := by
  obtain ⟨u, heu, hu, hum⟩ := Circuit.exec_run (Circuit.emit w)
    (fun d op x v he ha hx => Circuit.exec_emit (by omega) d op x hx he ha)
    (ops (clusterSize w)) (values (clusterSize w) z) 1 43 (by decide)
    (fun i hi _ => by
      have hine : i ≠ 0 := by intro h; subst i; simp at hi
      exact ⟨ops_earlier _ i, eval_ops _ _ i hine, ops_admissible hw hz0 hz i hine⟩)
    x hx
  have hp : Circuit.prefix (values (clusterSize w) z) (1 + 43) =
      values (clusterSize w) z := by
    funext i
    exact ite_eq_left i.isLt
  rw [hp] at hu
  have hval : Multiword.value (radix w) u (Bank.regs (43 : Fin 44)) = z.log2 :=
    (hu 43).2.trans (values_output hz0 hz)
  have hfit : Fits w (Multiword.value (radix w) u (Bank.regs (43 : Fin 44))) := by
    rw [hval]
    exact ((Nat.log2_lt (by omega : z ≠ 0)).mpr hz).trans Nat.lt_two_pow_self
  obtain ⟨y, hey, hy, hyf, _⟩ := Transfer.exec_assemble (by omega)
    (Bank.regs (43 : Fin 44)) output (Bank.digit_regs 43) u hfit
  refine ⟨y, ?_, hy.trans hval, hyf.1.trans hum⟩
  simpa only [positiveCode, Bank.length_regs] using heu.seq hey.within

/-- Width two needs only division by two: its possible indices are zero and one. -/
def twoBitCode : Code .standard (Bank.capacity 44 + 4) := ram[
  Bank.inputReg ← #1;
  Bank.inputReg ← *Bank.inputReg;
  zeroTest ← #2;
  output ← Bank.inputReg / zeroTest ]

/-- The width-selected checked program. For larger widths the zero case returns zero and
positive inputs execute the full graph. All constants and conversions are charged. -/
def code (w : ℕ) : Code .standard (Bank.capacity 44 + 4) :=
  if w = 2 then twoBitCode else
    .seq (Bank.input (0 : Fin 44))
      (.seq (.op (.const zeroTest 0))
        (.branch (.eq Bank.inputReg zeroTest) (.op (.const output 0)) (positiveCode w)))

/-- A fixed register count and a fixed code-size bound, shared by every physical width. -/
theorem size_code (w : ℕ) : (code w).size ≤ 200000 := by
  by_cases hw : w = 2
  · simp [code, hw, twoBitCode, Code.size]
  · have hp := size_positiveCode w
    simp only [code, ite_eq_right hw, Code.size, Bank.size_input]
    omega

/-- The complete standard-basis program executes at the original physical width, from the
ordinary singleton RAM input, within a constant instruction count independent of width.
No preloaded wide constants, digit encodings, or MSB oracle are assumptions. -/
theorem exec_code {w z : ℕ} (hw : 2 ≤ w) (hz : z < 2 ^ w) :
    ∃ y, ExecWithin w (code w) (Data.init [z]) y 200000 ∧
      y.regs output = z.log2 ∧ y.mem = (Data.init [z] : Data (Bank.capacity 44 + 4)).mem := by
  by_cases hw2 : w = 2
  · subst w
    have hdiv : Fits 2 (z / 2) := (show Fits 2 z from hz).of_le (Nat.div_le_self z 2)
    have he : ∃ y, Exec 2 twoBitCode (Data.init [z]) y 4 ∧ y.regs output = z / 2 ∧
        y.mem = (Data.init [z] : Data (Bank.capacity 44 + 4)).mem := by
      let y : Data (Bank.capacity 44 + 4) :=
        ((((Data.init [z]).set Bank.inputReg 1).set Bank.inputReg z).set zeroTest 2).set
          output (z / 2)
      refine ⟨y, ?_, ?_, rfl⟩
      · ram_eval [twoBitCode, y, Data.init, Bank.inputReg, zeroTest, output, hdiv]
        simp [hdiv]
      · simp [y]
    obtain ⟨y, he, hy, hm⟩ := he
    have hlog : z / 2 = z.log2 := by
      have hz4 : z < 4 := hz
      interval_cases z <;> rfl
    refine ⟨y, ?_, hy.trans hlog, hm⟩
    change ExecWithin 2 twoBitCode (Data.init [z]) y 200000
    exact he.within.mono (by decide)
  · have hw3 : 3 ≤ w := by omega
    obtain ⟨u, heu, hu, hum, huz⟩ := Bank.exec_input hw hz (0 : Fin 44)
    let t := u.set zeroTest 0
    have het : Exec (B := .standard) w (.op (.const zeroTest 0)) u t 1 :=
      Exec.const (fits_zero w)
    have htp : Bank.Encodes w t (Function.update (fun _ => 0) (0 : Fin 44) z) := by
      intro j
      have he (i : Fin (Bank.capacity 44 + 4)) (hi : i ∈ Bank.regs j) :
          t.regs i = u.regs i := by
        have hh := Bank.mem_regs hi
        have hine : i ≠ zeroTest := by
          intro h
          have := congrArg Fin.val h
          dsimp only [zeroTest] at this
          omega
        simp only [t, Data.set_regs, Function.update_of_ne hine]
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [he i hi]; exact (hu j).1 i hi
      · exact (congrArg (Nat.ofDigits (radix w)) (List.map_congr_left he)).trans (hu j).2
    have htin : t.regs Bank.inputReg = z := by
      simpa only [t, Data.set_regs, Function.update_of_ne (by decide :
        (Bank.inputReg : Fin (Bank.capacity 44 + 4)) ≠ zeroTest)] using huz
    have htzero : t.regs zeroTest = 0 := by simp [t]
    by_cases hz0 : z = 0
    · let y := t.set output 0
      have hezero : Exec (B := .standard) w (.op (.const output 0)) t y 1 :=
        Exec.const (fits_zero w)
      have hbranch := Exec.branch_pos (c := Cond.eq Bank.inputReg zeroTest)
        (neg := positiveCode w)
        (by simpa only [Cond.holds_eq, htin, htzero] using hz0) hezero
      refine ⟨y, ?_, ?_, hum⟩
      · have hh := heu.seq (het.seq hbranch)
        simpa only [code, ite_eq_right hw2] using hh.within.mono (by decide : 49 ≤ 200000)
      · simp [y, hz0]
    · have hprefix : Function.update (fun _ => 0) (0 : Fin 44) z =
          Circuit.prefix (values (clusterSize w) z) 1 := by
        funext i
        by_cases hi : i = 0
        · subst i; simp [Circuit.prefix, values_input]
        · have hi0 : 1 ≤ i.val := by
            have : i.val ≠ 0 := fun h => hi (Fin.ext h)
            omega
          simp only [Function.update_of_ne hi, Circuit.prefix,
            ite_eq_right (by omega : ¬i.val < 1)]
      rw [hprefix] at htp
      obtain ⟨y, hey, hy, hym⟩ := exec_positiveCode hw3 (by omega) hz t htp
      have hbranch := ExecWithin.branch_neg (cond := Cond.eq Bank.inputReg zeroTest)
        (pos := .op (.const output 0))
        (by simpa only [Cond.holds_eq, htin, htzero] using hz0) hey
      refine ⟨y, ?_, hy, hym.trans hum⟩
      have hh := heu.within.seq (het.within.seq hbranch)
      simpa only [code, ite_eq_right hw2] using hh.mono (by decide : 172094 ≤ 200000)

/-- Zero dispatch and positive arithmetic after the input bank entry has been established. -/
def finishCode (w : ℕ) : Code .standard (Bank.capacity 44 + 4) :=
  .seq (.op (.const zeroTest 0))
    (.branch (.eq Bank.inputReg zeroTest) (.op (.const output 0)) (positiveCode w))

private theorem exec_finishCode {w z : ℕ} (hw : 3 ≤ w) (hz : z < 2 ^ w)
    (x : Data (Bank.capacity 44 + 4))
    (hx : Bank.Encodes w x (Function.update (fun _ => 0) (0 : Fin 44) z))
    (hin : x.regs Bank.inputReg = z) :
    ∃ y, ExecWithin w (finishCode w) x y 172048 ∧
      y.regs output = z.log2 ∧ y.mem = x.mem := by
  let t := x.set zeroTest 0
  have het : Exec (B := .standard) w (.op (.const zeroTest 0)) x t 1 :=
    Exec.const (fits_zero w)
  have htp : Bank.Encodes w t (Function.update (fun _ => 0) (0 : Fin 44) z) := by
    intro j
    have he (i : Fin (Bank.capacity 44 + 4)) (hi : i ∈ Bank.regs j) :
        t.regs i = x.regs i := by
      have hh := Bank.mem_regs hi
      have hine : i ≠ zeroTest := by
        intro h
        have := congrArg Fin.val h
        dsimp only [zeroTest] at this
        omega
      simp only [t, Data.set_regs, Function.update_of_ne hine]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [he i hi]; exact (hx j).1 i hi
    · exact (congrArg (Nat.ofDigits (radix w)) (List.map_congr_left he)).trans (hx j).2
  have htin : t.regs Bank.inputReg = z := by
    simpa only [t, Data.set_regs, Function.update_of_ne (by decide :
      (Bank.inputReg : Fin (Bank.capacity 44 + 4)) ≠ zeroTest)] using hin
  have htzero : t.regs zeroTest = 0 := by simp [t]
  by_cases hz0 : z = 0
  · let y := t.set output 0
    have hey : Exec (B := .standard) w (.op (.const output 0)) t y 1 :=
      Exec.const (fits_zero w)
    have heb := Exec.branch_pos (c := Cond.eq Bank.inputReg zeroTest)
      (neg := positiveCode w) (by simpa only [Cond.holds_eq, htin, htzero] using hz0) hey
    exact ⟨y, (het.seq heb).within.mono (by decide), by simp [y, hz0], rfl⟩
  · have hp : Function.update (fun _ => 0) (0 : Fin 44) z =
        Circuit.prefix (values (clusterSize w) z) 1 := by
      funext i
      by_cases hi : i = 0
      · subst i; simp [Circuit.prefix, values_input]
      · have hi0 : 1 ≤ i.val := by
          have : i.val ≠ 0 := fun h => hi (Fin.ext h)
          omega
        simp only [Function.update_of_ne hi, Circuit.prefix,
          ite_eq_right (by omega : ¬i.val < 1)]
    rw [hp] at htp
    obtain ⟨y, hey, hy, hym⟩ := exec_positiveCode hw (by omega) hz t htp
    have heb := ExecWithin.branch_neg (cond := Cond.eq Bank.inputReg zeroTest)
      (pos := .op (.const output 0))
      (by simpa only [Cond.holds_eq, htin, htzero] using hz0) hey
    exact ⟨y, het.within.seq heb, hy, hym⟩

/-- Register entry point for composition. The caller supplies its fitting input in physical
register four. All 792 bank digits are cleared, the input is split in 44 instructions, and
the same checked graph returns its answer in physical register six. No memory is read. -/
def scalarCode (w : ℕ) : Code .standard (Bank.capacity 44 + 4) :=
  .seq (Bank.clear 44)
    (.seq (Transfer.split Bank.inputReg (Bank.regs (0 : Fin 44))) (finishCode w))

/-- The scalar-entry MSB code has size at most `200000` at every word width. -/
theorem size_scalarCode (w : ℕ) : (scalarCode w).size ≤ 200000 := by
  have hp := size_positiveCode w
  simp only [scalarCode, finishCode, Code.size, Bank.size_clear, Transfer.size_split,
    Bank.length_regs]
  omega

/-- Composable scalar-register execution. The entire incoming register file and memory may
be arbitrary. Only the input register must fit. The routine preserves memory exactly and
returns `Nat.log2` in physical register six within 200000 instructions, including clearing.
Registers inside this 836-register workspace may change; renamed embeddings frame all others. -/
theorem exec_scalarCode {w : ℕ} (hw : 3 ≤ w) (x : Data (Bank.capacity 44 + 4))
    (hz : Fits w (x.regs Bank.inputReg)) :
    ∃ y, ExecWithin w (scalarCode w) x y 200000 ∧
      y.regs output = (x.regs Bank.inputReg).log2 ∧ y.mem = x.mem := by
  obtain ⟨u, heu, hu, hum, hin⟩ := Bank.exec_clear (w := w) (by omega) x
  obtain ⟨t, het, htb, htv, htf, htp⟩ := Transfer.exec_split_eighteen (w := w) (by omega)
    Bank.inputReg (Bank.regs (0 : Fin 44)) (Bank.length_regs 0)
    (by dsimp [Workspace.IsDigit, Bank.inputReg]; omega)
    (Bank.digit_regs 0) (Bank.nodup_regs 0) u (by rwa [hin])
  have htbank := Bank.encodes_update hu (0 : Fin 44) _ htb htv
    (fun i hi hid => htp i (by dsimp [Workspace.IsDigit]; omega) hid)
  rw [hin] at htbank
  have hnot : (Bank.inputReg : Fin (Bank.capacity 44 + 4)) ∉ Bank.regs (0 : Fin 44) := by
    intro hi
    have hh := Bank.mem_regs hi
    dsimp only [Bank.inputReg] at hh
    omega
  have htin : t.regs Bank.inputReg = x.regs Bank.inputReg :=
    (htp Bank.inputReg (by dsimp [Workspace.IsDigit, Bank.inputReg]; omega) hnot).trans hin
  obtain ⟨y, hey, hy, hym⟩ := exec_finishCode hw hz t htbank htin
  refine ⟨y, ?_, hy, hym.trans (htf.1.trans hum)⟩
  have hh := heu.within.seq (het.within.seq hey)
  simpa only [scalarCode] using hh.mono (by decide : 172885 ≤ 200000)

/-- The complete flat standard-basis program, with its final halt charged separately. -/
def program (w : ℕ) : Cslib.WordRAM.Program .standard (Bank.capacity 44 + 4) :=
  (code w).program output

/-- The assembled halting MSB program has at most `200001` instructions. -/
theorem length_program (w : ℕ) : (program w).length ≤ 200001 := by
  have hs := size_code w
  simp only [program, Code.program, List.length_append, Code.length_assemble,
    List.length_singleton]
  omega

/-- Actual halting execution returning the most-significant-set-bit index, with zero
returning zero. The register count and the time bound are independent of physical width. -/
theorem executes_program {w z : ℕ} (hw : 2 ≤ w) (hz : z < 2 ^ w) :
    ∃ t ≤ 200001, Executes w (program w) (State.init [z]) z.log2 t := by
  obtain ⟨y, ⟨t, ht, he⟩, hy, _⟩ := exec_code hw hz
  refine ⟨t + 1, by omega, ?_⟩
  simpa only [program, State.init, hy] using he.executes output

end Cslib.Algorithms.WordRAM.FusionTree.MSB.Program

end
