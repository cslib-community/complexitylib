/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.CellProbe.Randomized
public import CslibFrontier.Computability.WordRAM.Subroutine
public import CslibFrontier.Computability.WordRAM.Randomized.Expected
import CslibFrontier.Foundations.Analysis.ENNRealTsum
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import Mathlib.Data.Finset.Sort

/-!
# Simulating Word-RAM Programs in the Adaptive Cell-Probe Model

This file builds the computational simulation bridge (`Cslib.CellProbe`) from deterministic,
finite-tree randomized, and unbounded Las Vegas Word-RAM executions (`Cslib.WordRAM`) to adaptive
cell-probe trees (`ProbeTree`, `RandProbeTree`; [Miltersen1999], §1.2, pp. 1–2).

On a `w`-bit Word RAM with `r` registers and contiguous memory footprint `[base, base + S)`, two
model differences require explicit accounting in a formal simulation:
1. **Persistent registers across operations:** A cell-probe scheme keeps state between operations
   solely in `Mem cells wCell` (`Fin cells → Fin (2 ^ wCell)`), with no registers surviving across
   operation boundaries. Given an input-register mask `input : Fin r → Bool` (such as `P.input` on
   `WordRAM.SubroutineCode B r k_init`), only the `persCount input` persistent registers with
   `input i = false` survive between calls:
   * **Standard `w`-bit layout (`standardLayout`):** Allocates `S + persCount input` cells of width
     `w` (`0` extra cells and `0` extra probes when `∀ i, input i = true`), reloading persistent
     registers in `persCount input` reads and spilling them at halt in `persCount input` writes
     (`2 * persCount input` additive probes per operation).
   * **Wide-cell single-spill layout (`wideLayout`):** Packs all `persCount input` persistent
     registers in base `2 ^ w` into `1` cell of width
     `wideWidth input w := max (persCount input) 1 * w` over `S + 1` cells, paying `0` extra probes
     when `persCount input = 0` and `2` extra probes (`1` read + `1` write) whenever
     `persCount input > 0`, independent of `r`.
2. **Unallocated reads and unbounded Las Vegas loops:**
   * Replacing Word-RAM memory outside `[base, base + S)` by `0` (`zeroOutside base S`) keeps loads
     and stores outside `[base, base + S)` in a pure-Lean intra-operation map at `0` probe cost;
     when `Modifies (Block.mk base S).footprint` holds at halt, outside memory returns to `0` at
     every operation boundary.
   * Writes inside `[base, base + S)` are buffered in pure Lean during a clocked `K`-step run and
     flushed only at halt, so `reads + flushedWrites ≤ continuingSteps` and cell memory remains
     untouched if execution is still active at step `K`. On that `> K` tail event (probability
     tending to `0` as `K → ∞` whenever `expectedTime < ⊤`), the simulator reads all `S` data
     cells, selects a reachable halting post-state in pure Lean from `haltedLim` (`> 0` by
     almost-sure halting, hence in the target support), and writes the resulting packed memory
     (`2 * S + overhead` extra probes on the tail), preserving **100% zero-error support
     correctness** at finite tree depth while achieving expected probes `≤ T + overhead + η` for any
     `η > 0`.

The `zeroOutside` framing, `persistentRegCount` / wide-cell register-spill layouts, and buffered
finite-horizon Las Vegas truncation are original library constructions connecting `Cslib.WordRAM`
to `Cslib.CellProbe`. For data-structure `Impl` bridges and contrapositive lower-bound transfer
corollaries, see `CslibFrontier.DataStructure.CellProbe.OfWordRAM`.

## Main definitions

* `Cslib.CellProbe.persRegs`, `Cslib.CellProbe.persCount`,
  `Cslib.CellProbe.persistentRegCount`: persistent register set and count (`input i = false`).
* `Cslib.CellProbe.zeroOutside`: zero Word-RAM memory outside `[base, base + S)`.
* `Cslib.CellProbe.packMem`, `Cslib.CellProbe.unpackData`, `Cslib.CellProbe.canonicalData`:
  standard `w`-bit packing between `WordRAM.Data r` and `Mem (S + persCount input) w`.
* `Cslib.CellProbe.wideWidth`, `Cslib.CellProbe.wideSubroutineWidth`,
  `Cslib.CellProbe.packMemWide`, `Cslib.CellProbe.unpackDataWide`,
  `Cslib.CellProbe.canonicalDataWide`: single-cell base-`2 ^ w` register packing over `S + 1` cells
  of width `max (persCount input) 1 * w`.
* `Cslib.CellProbe.RegLayout`, `Cslib.CellProbe.standardLayout`, `Cslib.CellProbe.wideLayout`:
  unified cell-layout interface shared by deterministic and randomized simulators.
* `Cslib.CellProbe.simProgDet`, `Cslib.CellProbe.simProgInitDet`,
  `Cslib.CellProbe.simProgDetAuto`, `Cslib.CellProbe.simProgRand`: clocked and automatic-fuel
  deterministic (`ProbeTree`) and buffered randomized (`RandProbeTree`) flat-program simulators.
* `Cslib.CellProbe.ExecProgramDist`: distributional execution contract for flat `WordRAM.Program`s.

## Main results

* `Cslib.CellProbe.persistentRegCount_eq_zero_of_all_input`,
  `Cslib.CellProbe.persistentRegCount_le`: zero-overhead specialization and register-count bound.
* `Cslib.CellProbe.simProgDet_spec`, `Cslib.CellProbe.simProgDetAuto_spec`,
  `Cslib.CellProbe.simExecWithin`, `Cslib.CellProbe.simExecWithinWide`: deterministic flat-program
  and structured `ExecWithin` simulation in `≤ T + 2 * r_pers` (or `≤ T + 2` wide) probes.
* `Cslib.CellProbe.simExecRand`, `Cslib.CellProbe.simExecRandWide`: exact-distribution finite-tree
  `ExecRand` simulation in `RandProbeTree` with zero `η` slack.
* `Cslib.CellProbe.ExecProgramDist.haltedLim_eq`,
  `Cslib.CellProbe.execProgramDist_of_execCodeDist`,
  `Cslib.CellProbe.simProgRand_lasVegas_spec`, `Cslib.CellProbe.exists_uniform_cutoff`:
  exact halting-law identification, compilation of `ExecCodeDist` to `ExecProgramDist`, and
  uniform-horizon buffered Las Vegas simulation with zero-error support preservation and arbitrary
  `η > 0` expected-probe slack.

## References

* [P. B. Miltersen, *Cell Probe Complexity — a Survey*, §1.2][Miltersen1999]
* [A. C.-C. Yao, *Probabilistic Computations: Toward a Unified Measure of Complexity*][Yao1977]
-/

public section

namespace Cslib.CellProbe

open Cslib.WordRAM Cslib.Probability
open scoped ENNReal

/-! ### 1. Persistent register accounting -/

/-- Subset of registers `i : Fin r` that persist across calls (`input i = false`). -/
@[expose] def persRegs {r : ℕ} (input : Fin r → Bool) : Finset (Fin r) :=
  Finset.univ.filter fun i => !input i

/-- Number of persistent registers (`input i = false`) under calling-convention mask `input`. -/
@[expose] def persCount {r : ℕ} (input : Fin r → Bool) : ℕ :=
  (persRegs input).card

@[simp]
theorem mem_persRegs {r : ℕ} {input : Fin r → Bool} {i : Fin r} :
    i ∈ persRegs input ↔ input i = false := by
  simp [persRegs]

@[simp]
theorem persCount_eq_zero_of_all_input {r : ℕ} {input : Fin r → Bool}
    (h : ∀ i, input i = true) : persCount input = 0 := by
  simp [persCount, persRegs, h]

theorem persCount_le {r : ℕ} (input : Fin r → Bool) : persCount input ≤ r :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin r)

/-- Number of persistent registers (`P.input i = false`) of a `WordRAM.SubroutineCode`. -/
@[expose] def persistentRegCount {B : Basis} {r k_init : ℕ} (P : SubroutineCode B r k_init) : ℕ :=
  (Finset.univ.filter fun i : Fin r => !P.input i).card

theorem persistentRegCount_eq_persCount {B : Basis} {r k_init : ℕ}
    (P : SubroutineCode B r k_init) : persistentRegCount P = persCount P.input := by
  rfl

@[simp]
theorem persistentRegCount_eq_zero_of_all_input {B : Basis} {r k_init : ℕ}
    {P : SubroutineCode B r k_init} (h : ∀ i, P.input i = true) :
    persistentRegCount P = 0 :=
  persCount_eq_zero_of_all_input h

theorem persistentRegCount_le {B : Basis} {r k_init : ℕ} (P : SubroutineCode B r k_init) :
    persistentRegCount P ≤ r :=
  persCount_le P.input

/-- Canonical order-preserving enumeration of persistent registers
`Fin (persCount input) → Fin r`. -/
def persReg {r : ℕ} (input : Fin r → Bool) (k : Fin (persCount input)) : Fin r :=
  ((persRegs input).orderIsoOfFin rfl k).1

theorem persReg_input_eq_false {r : ℕ} (input : Fin r → Bool) (k : Fin (persCount input)) :
    input (persReg input k) = false :=
  mem_persRegs.mp ((persRegs input).orderIsoOfFin rfl k).2

theorem persReg_injective {r : ℕ} (input : Fin r → Bool) :
    Function.Injective (persReg input) := fun _ _ h =>
  ((persRegs input).orderIsoOfFin rfl).injective (Subtype.ext h)

/-- Inverse index of a persistent register `i : Fin r` (`input i = false`) in
`Fin (persCount input)`. -/
def persIdx {r : ℕ} (input : Fin r → Bool) (i : Fin r) (hi : input i = false) :
    Fin (persCount input) :=
  ((persRegs input).orderIsoOfFin rfl).symm ⟨i, mem_persRegs.mpr hi⟩

@[simp]
theorem persReg_persIdx {r : ℕ} (input : Fin r → Bool) (i : Fin r) (hi : input i = false) :
    persReg input (persIdx input i hi) = i := by
  simp [persReg, persIdx]

@[simp]
theorem persIdx_persReg {r : ℕ} (input : Fin r → Bool) (k : Fin (persCount input)) :
    persIdx input (persReg input k) (persReg_input_eq_false input k) = k :=
  OrderIso.symm_apply_apply ((persRegs input).orderIsoOfFin rfl) k

/-! ### 2. `zeroOutside` framing, standard & wide-cell memory packing, and `RegLayout` -/

/-- Replace Word-RAM memory outside `[base, base + S)` with `0`, preserving registers and
`[base, base + S)`. -/
@[expose] def zeroOutside {r : ℕ} (base S : ℕ) (x : Data r) : Data r where
  regs := x.regs
  mem a := if base ≤ a ∧ a < base + S then x.mem a else 0

@[simp]
theorem zeroOutside_regs {r : ℕ} (base S : ℕ) (x : Data r) :
    (zeroOutside base S x).regs = x.regs :=
  rfl

theorem zeroOutside_mem_of_mem_footprint {r : ℕ} {base S a : ℕ} (x : Data r)
    (ha : a ∈ (Block.mk base S).footprint) :
    (zeroOutside base S x).mem a = x.mem a := by
  have hown : base ≤ a ∧ a < base + S := Block.mem_footprint.mp ha
  simp [zeroOutside, hown]

theorem zeroOutside_mem_of_not_owns {r : ℕ} {base S a : ℕ} (x : Data r)
    (ha : ¬(base ≤ a ∧ a < base + S)) :
    (zeroOutside base S x).mem a = 0 := by
  simp [zeroOutside, ha]

theorem zeroOutside_bounded {r w : ℕ} (base S : ℕ) {x : Data r} (hx : x.Bounded w) :
    (zeroOutside base S x).Bounded w := by
  refine ⟨hx.1, fun a => ?_⟩
  by_cases ha : base ≤ a ∧ a < base + S
  · simpa [zeroOutside, ha] using hx.2 a
  · simp [zeroOutside, ha]

/-- Truncate a natural number into `Fin (2 ^ w)` (identity on `Fits w v`). -/
@[expose] def wordOfNat (w v : ℕ) : Fin (2 ^ w) :=
  if h : v < 2 ^ w then ⟨v, h⟩ else ⟨0, Nat.two_pow_pos w⟩

@[simp]
theorem wordOfNat_val_of_fits {w v : ℕ} (h : Fits w v) : (wordOfNat w v).1 = v := by
  have hlt : v < 2 ^ w := h
  simp [wordOfNat, hlt]

/-- Pack `x : Data r` (`[base, base + S)` plus persistent registers) into
`Mem (S + persCount input) w`. -/
def packMem {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) (x : Data r) :
    Mem (S + persCount input) w := fun c =>
  if hc : c.1 < S then
    wordOfNat w (x.mem (base + c.1))
  else
    wordOfNat w (x.regs (persReg input ⟨c.1 - S, by omega⟩))

/-- Unpack `m : Mem (S + persCount input) w` with caller-supplied input registers `argRegs` into
`Data r` (with `0` outside `[base, base + S)`). -/
def unpackData {r : ℕ} (input : Fin r → Bool) (argRegs : Fin r → ℕ) (base S w : ℕ)
    (m : Mem (S + persCount input) w) : Data r where
  regs i :=
    if hi : input i = true then argRegs i
    else (m (Fin.natAdd S (persIdx input i (Bool.eq_false_iff.mpr hi)))).1
  mem a :=
    if ha : base ≤ a ∧ a < base + S then
      (m (Fin.castAdd (persCount input) ⟨a - base, by omega⟩)).1
    else 0

/-- Canonical `Data r` view of `m : Mem (S + persCount input) w` setting scratch input registers to
`0`. -/
def canonicalData {r : ℕ} (input : Fin r → Bool) (base S w : ℕ)
    (m : Mem (S + persCount input) w) : Data r :=
  unpackData input (fun _ => 0) base S w m

theorem unpackData_bounded {r : ℕ} {input : Fin r → Bool} {argRegs : Fin r → ℕ}
    {base S w : ℕ} (harg : ∀ i, input i = true → Fits w (argRegs i))
    (m : Mem (S + persCount input) w) :
    (unpackData input argRegs base S w m).Bounded w := by
  refine ⟨fun i => ?_, fun a => ?_⟩
  · dsimp only [unpackData]
    split_ifs with hi
    · exact harg i hi
    · exact (m _).isLt
  · dsimp only [unpackData]
    split_ifs with ha
    · exact (m _).isLt
    · exact fits_zero w

theorem canonicalData_bounded {r : ℕ} (input : Fin r → Bool) (base S w : ℕ)
    (m : Mem (S + persCount input) w) :
    (canonicalData input base S w m).Bounded w :=
  unpackData_bounded (fun _ _ => fits_zero w) m

theorem unpackData_packMem_regs {r : ℕ} {input : Fin r → Bool} {argRegs : Fin r → ℕ}
    {base S w : ℕ} {x : Data r} (hx : x.Bounded w) (i : Fin r) :
    (unpackData input argRegs base S w (packMem input base S w x)).regs i =
      if input i then argRegs i else x.regs i := by
  dsimp only [unpackData]
  split_ifs with hi
  · rfl
  · have hfalse : input i = false := Bool.eq_false_iff.mpr hi
    set k := persIdx input i hfalse
    have hnotlt : ¬ (Fin.natAdd S k).1 < S := by simp
    simp only [packMem, hnotlt, ↓reduceDIte]
    have hsub : (⟨(Fin.natAdd S k).1 - S, by omega⟩ : Fin (persCount input)) = k := by
      ext; simp
    rw [hsub, persReg_persIdx input i hfalse, wordOfNat_val_of_fits (hx.1 i)]

theorem unpackData_packMem_mem {r : ℕ} {input : Fin r → Bool} {argRegs : Fin r → ℕ}
    {base S w : ℕ} {x : Data r} (hx : x.Bounded w) (a : ℕ) :
    (unpackData input argRegs base S w (packMem input base S w x)).mem a =
      (zeroOutside base S x).mem a := by
  dsimp only [unpackData, zeroOutside]
  split_ifs with ha
  · have hlt : a - base < S := by omega
    have hadd : base + (a - base) = a := by omega
    simp only [packMem, Fin.val_castAdd, hlt, ↓reduceDIte, hadd,
      wordOfNat_val_of_fits (hx.2 a)]
  · rfl

/-! #### Wide-cell base-`2 ^ w` persistent-register codec (`wideLayout`) -/

/-- Wide cell bit-width `max (persCount input) 1 * w` packing all persistent registers into `1`
cell while remaining at least `w` bits wide when `persCount input = 0`. -/
@[expose] def wideWidth {r : ℕ} (input : Fin r → Bool) (w : ℕ) : ℕ :=
  max (persCount input) 1 * w

/-- Subroutine specialization `max (persistentRegCount P) 1 * w` of `wideWidth`. -/
@[expose] def wideSubroutineWidth {B : Basis} {r k_init : ℕ}
    (P : SubroutineCode B r k_init) (w : ℕ) : ℕ :=
  max (persistentRegCount P) 1 * w

theorem le_wideWidth {r : ℕ} (input : Fin r → Bool) (w : ℕ) : w ≤ wideWidth input w := by
  have h1 : 1 ≤ max (persCount input) 1 := le_max_right _ _
  calc w = 1 * w := (one_mul w).symm
    _ ≤ max (persCount input) 1 * w := Nat.mul_le_mul_right w h1

theorem persCount_mul_le_wideWidth {r : ℕ} (input : Fin r → Bool) (w : ℕ) :
    persCount input * w ≤ wideWidth input w :=
  Nat.mul_le_mul_right w (le_max_left _ _)

/-- Encode `k` `w`-bit words as a single natural number `< 2 ^ (k * w)` in base `2 ^ w`. -/
def packDigits : (k w : ℕ) → (Fin k → Fin (2 ^ w)) → ℕ
  | 0, _, _ => 0
  | k + 1, w, f => (f 0).1 + 2 ^ w * packDigits k w (fun j => f j.succ)

theorem packDigits_lt : ∀ (k w : ℕ) (f : Fin k → Fin (2 ^ w)), packDigits k w f < 2 ^ (k * w)
  | 0, w, _ => by simp [packDigits]
  | k + 1, w, f => by
    have hlo : (f 0).1 < 2 ^ w := (f 0).isLt
    have hhi : packDigits k w (fun j => f j.succ) < 2 ^ (k * w) :=
      packDigits_lt k w (fun j => f j.succ)
    have hpow : 2 ^ ((k + 1) * w) = 2 ^ w * 2 ^ (k * w) := by
      rw [Nat.add_mul, one_mul, Nat.add_comm (k * w) w, Nat.pow_add]
    rw [packDigits, hpow]
    have hle : packDigits k w (fun j => f j.succ) + 1 ≤ 2 ^ (k * w) := hhi
    calc
      (f 0).1 + 2 ^ w * packDigits k w (fun j => f j.succ)
        < 2 ^ w + 2 ^ w * packDigits k w (fun j => f j.succ) := by omega
      _ = 2 ^ w * (packDigits k w (fun j => f j.succ) + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ (k * w) := Nat.mul_le_mul_left _ hle

/-- Decode `k` `w`-bit words in base `2 ^ w` from a natural number `val`. -/
def unpackDigits : (k w val : ℕ) → Fin k → Fin (2 ^ w)
  | 0, _, _ => Fin.elim0
  | k + 1, w, val =>
    Fin.cons ⟨val % 2 ^ w, Nat.mod_lt _ (Nat.two_pow_pos w)⟩ (unpackDigits k w (val / 2 ^ w))

@[simp]
theorem unpackDigits_packDigits :
    ∀ (k w : ℕ) (f : Fin k → Fin (2 ^ w)), unpackDigits k w (packDigits k w f) = f
  | 0, _, f => funext fun j => j.elim0
  | k + 1, w, f => by
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    set lo := (f 0).1
    set hi := packDigits k w (fun j => f j.succ)
    have hmod : (lo + 2 ^ w * hi) % 2 ^ w = lo := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (f 0).isLt]
    have hdiv : (lo + 2 ^ w * hi) / 2 ^ w = hi := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (f 0).isLt, zero_add]
    funext j
    refine j.cases ?_ (fun i => ?_)
    · dsimp only [packDigits, unpackDigits]
      rw [Fin.cons_zero]
      exact Fin.ext hmod
    · dsimp only [packDigits, unpackDigits]
      rw [Fin.cons_succ]
      change unpackDigits k w ((lo + 2 ^ w * hi) / 2 ^ w) i = f i.succ
      rw [hdiv, unpackDigits_packDigits k w (fun j => f j.succ)]

theorem packDigits_eq_zero_of_zero {k w : ℕ} (hk : k = 0) (f : Fin k → Fin (2 ^ w)) :
    packDigits k w f = 0 := by
  subst hk
  rfl

/-- Invariant asserting that data cells `0 .. S - 1` of a wide-cell memory hold `w`-bit values. -/
def DataCellsBounded (S w wCell : ℕ) (m : Mem (S + 1) wCell) : Prop :=
  ∀ j : Fin S, (m (Fin.castAdd 1 j)).1 < 2 ^ w

/-- Pack `x : Data r` into `Mem (S + 1) (wideWidth input w)`: cells `0 .. S - 1` hold
`x.mem (base + j)`, and cell `S` holds all `persCount input` persistent registers in base `2 ^ w`.
-/
def packMemWide {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) (x : Data r) :
    Mem (S + 1) (wideWidth input w) := fun c =>
  if hc : c.1 < S then
    ⟨(wordOfNat w (x.mem (base + c.1))).1,
      lt_of_lt_of_le (wordOfNat w _).isLt
        (Nat.pow_le_pow_right (by omega) (le_wideWidth input w))⟩
  else
    have hlt_pers :
        packDigits (persCount input) w (fun k => wordOfNat w (x.regs (persReg input k))) <
          2 ^ wideWidth input w :=
      lt_of_lt_of_le (packDigits_lt _ _ _)
        (Nat.pow_le_pow_right (by omega) (persCount_mul_le_wideWidth input w))
    ⟨packDigits (persCount input) w (fun k => wordOfNat w (x.regs (persReg input k))), hlt_pers⟩

theorem dataCellsBounded_packMemWide {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) (x : Data r) :
    DataCellsBounded S w (wideWidth input w) (packMemWide input base S w x) := by
  intro j
  simp [packMemWide, j.isLt]

/-- Unpack `m : Mem (S + 1) (wideWidth input w)` with `argRegs` into `Data r`. -/
def unpackDataWide {r : ℕ} (input : Fin r → Bool) (argRegs : Fin r → ℕ) (base S w : ℕ)
    (m : Mem (S + 1) (wideWidth input w)) : Data r where
  regs i :=
    if hi : input i = true then argRegs i
    else
      (unpackDigits (persCount input) w (m (Fin.last S)).1
        (persIdx input i (Bool.eq_false_iff.mpr hi))).1
  mem a :=
    if ha : base ≤ a ∧ a < base + S then
      (m (Fin.castAdd 1 ⟨a - base, by omega⟩)).1 % 2 ^ w
    else 0

/-- Canonical `Data r` view of `m : Mem (S + 1) (wideWidth input w)` with `0` on `input` registers.
-/
def canonicalDataWide {r : ℕ} (input : Fin r → Bool) (base S w : ℕ)
    (m : Mem (S + 1) (wideWidth input w)) : Data r :=
  unpackDataWide input (fun _ => 0) base S w m

theorem unpackDataWide_bounded {r : ℕ} {input : Fin r → Bool} {argRegs : Fin r → ℕ}
    {base S w : ℕ} (harg : ∀ i, input i = true → Fits w (argRegs i))
    (m : Mem (S + 1) (wideWidth input w)) :
    (unpackDataWide input argRegs base S w m).Bounded w := by
  refine ⟨fun i => ?_, fun a => ?_⟩
  · dsimp only [unpackDataWide]
    split_ifs with hi
    · exact harg i hi
    · exact (unpackDigits _ _ _ _).isLt
  · dsimp only [unpackDataWide]
    split_ifs with ha
    · exact Nat.mod_lt _ (Nat.two_pow_pos w)
    · exact fits_zero w

theorem canonicalDataWide_bounded {r : ℕ} (input : Fin r → Bool) (base S w : ℕ)
    (m : Mem (S + 1) (wideWidth input w)) :
    (canonicalDataWide input base S w m).Bounded w :=
  unpackDataWide_bounded (fun _ _ => fits_zero w) m

theorem unpackDataWide_packMemWide_regs {r : ℕ} {input : Fin r → Bool} {argRegs : Fin r → ℕ}
    {base S w : ℕ} {x : Data r} (hx : x.Bounded w) (i : Fin r) :
    (unpackDataWide input argRegs base S w (packMemWide input base S w x)).regs i =
      if input i then argRegs i else x.regs i := by
  dsimp only [unpackDataWide]
  split_ifs with hi
  · rfl
  · have hfalse : input i = false := Bool.eq_false_iff.mpr hi
    have hnotlt : ¬ (Fin.last S).1 < S := by simp
    simp only [packMemWide, hnotlt, ↓reduceDIte, unpackDigits_packDigits]
    rw [persReg_persIdx input i hfalse, wordOfNat_val_of_fits (hx.1 i)]

theorem unpackDataWide_packMemWide_mem {r : ℕ} {input : Fin r → Bool} {argRegs : Fin r → ℕ}
    {base S w : ℕ} {x : Data r} (hx : x.Bounded w) (a : ℕ) :
    (unpackDataWide input argRegs base S w (packMemWide input base S w x)).mem a =
      (zeroOutside base S x).mem a := by
  dsimp only [unpackDataWide, zeroOutside]
  split_ifs with ha
  · have hlt : a - base < S := by omega
    have hadd : base + (a - base) = a := by omega
    simp only [packMemWide, Fin.val_castAdd, hlt, ↓reduceDIte, hadd]
    rw [Nat.mod_eq_of_lt (wordOfNat w _).isLt, wordOfNat_val_of_fits (hx.2 a)]
  · rfl

/-! #### Finite multi-cell read/write helpers and unified `RegLayout` -/

/-- Read `n` cells `idx 0, …, idx (n - 1)` sequentially in `n` probes without mutating memory. -/
def readFin {cells wCell : ℕ} :
    ∀ {n : ℕ}, (Fin n → Fin cells) → ProbeTree cells wCell (Fin n → Fin (2 ^ wCell))
  | 0, _ => pure Fin.elim0
  | _ + 1, idx => do
      let v₀ ← ProbeTree.read (idx 0)
      let rest ← readFin (fun j => idx j.succ)
      pure (Fin.cons v₀ rest)

@[simp]
theorem run_readFin {cells wCell : ℕ} :
    ∀ {n : ℕ} (idx : Fin n → Fin cells) (m : Mem cells wCell),
      (readFin idx).run m = (fun j => m (idx j), m)
  | 0, _, m => Prod.ext (funext fun j => j.elim0) rfl
  | _ + 1, idx, m => by
    simp only [readFin, ProbeTree.run_bind, ProbeTree.run_read, run_readFin, ProbeTree.run_pure]
    refine Prod.ext (funext fun j => ?_) rfl
    exact j.cases rfl (fun _ => rfl)

@[simp]
theorem probes_readFin {cells wCell : ℕ} :
    ∀ {n : ℕ} (idx : Fin n → Fin cells) (m : Mem cells wCell),
      (readFin idx).probes m = n
  | 0, _, _ => rfl
  | n + 1, idx, m => by
    simp only [readFin, ProbeTree.probes_bind, ProbeTree.probes_read, ProbeTree.run_read,
      probes_readFin, run_readFin, ProbeTree.probes_pure]
    omega

/-- Write `vals 0, …, vals (n - 1)` to `idx 0, …, idx (n - 1)` sequentially in `n` probes. -/
def writeFin {cells wCell : ℕ} :
    ∀ {n : ℕ}, (Fin n → Fin cells) → (Fin n → Fin (2 ^ wCell)) → ProbeTree cells wCell PUnit
  | 0, _, _ => pure PUnit.unit
  | _ + 1, idx, vals => do
      let _ ← ProbeTree.write (idx 0) (vals 0)
      writeFin (fun j => idx j.succ) (fun j => vals j.succ)

@[simp]
theorem probes_writeFin {cells wCell : ℕ} :
    ∀ {n : ℕ} (idx : Fin n → Fin cells) (vals : Fin n → Fin (2 ^ wCell)) (m : Mem cells wCell),
      (writeFin idx vals).probes m = n
  | 0, _, _, _ => rfl
  | n + 1, idx, vals, m => by
    simp only [writeFin, ProbeTree.probes_bind, ProbeTree.probes_write, ProbeTree.run_write,
      probes_writeFin]
    omega

theorem nextMem_writeFin_apply {cells wCell : ℕ} :
    ∀ {n : ℕ} {idx : Fin n → Fin cells}, Function.Injective idx →
      ∀ (vals : Fin n → Fin (2 ^ wCell)) (m : Mem cells wCell) (j : Fin n),
        ((writeFin idx vals).run m).2 (idx j) = vals j
  | 0, _, _, _, _, j => j.elim0
  | n + 1, idx, hinj, vals, m, j => by
    have hinj' : Function.Injective (fun i : Fin n => idx i.succ) := fun a b h =>
      Fin.succ_injective _ (hinj h)
    refine j.cases ?_ (fun i => ?_)
    · simp only [writeFin, ProbeTree.run_bind, ProbeTree.run_write]
      have hnot : ∀ a : Fin n, idx 0 ≠ idx a.succ := fun a h =>
        Fin.succ_ne_zero a (hinj h.symm)
      have hpres : ∀ {k : ℕ} (f : Fin k → Fin cells) (vf : Fin k → Fin (2 ^ wCell))
          (m₀ : Mem cells wCell) (c : Fin cells),
          (∀ a : Fin k, c ≠ f a) → ((writeFin f vf).run m₀).2 c = m₀ c := by
        intro k
        induction k with
        | zero => intro _ _ _ _ _; rfl
        | succ k ih =>
          intro f vf m₀ c hc
          simp only [writeFin, ProbeTree.run_bind, ProbeTree.run_write]
          rw [ih _ _ _ c (fun a => hc a.succ), Function.update_of_ne (hc 0)]
      rw [hpres _ _ _ (idx 0) hnot, Function.update_self]
    · simp only [writeFin, ProbeTree.run_bind, ProbeTree.run_write]
      exact nextMem_writeFin_apply hinj' (fun a : Fin n => vals a.succ)
        (Function.update m (idx 0) (vals 0)) i

theorem nextMem_writeFin_of_forall_ne {cells wCell : ℕ} :
    ∀ {n : ℕ} (idx : Fin n → Fin cells) (vals : Fin n → Fin (2 ^ wCell))
      (m : Mem cells wCell) (c : Fin cells),
      (∀ j, c ≠ idx j) → ((writeFin idx vals).run m).2 c = m c
  | 0, _, _, _, _, _ => rfl
  | _ + 1, idx, vals, m, c, hne => by
    simp only [writeFin, ProbeTree.run_bind, ProbeTree.run_write]
    rw [nextMem_writeFin_of_forall_ne _ _ _ c (fun j => hne j.succ),
      Function.update_of_ne (hne 0)]

/-- Unified register/memory layout for Word-RAM-to-cell-probe simulation over `S + regCells` cells
of width `wCell` (`w ≤ wCell`). Instantiated by `standardLayout` (`regCells = persCount input`,
`wCell = w`) and `wideLayout` (`regCells = 1`, `wCell = wideWidth input w`). -/
structure RegLayout (r : ℕ) (input : Fin r → Bool) (base S w regCells wCell : ℕ) where
  /-- Cell width is at least the Word-RAM word width `w`. -/
  hw : w ≤ wCell
  /-- Number of probes used to reload persistent registers at operation entry. -/
  reloadProbes : ℕ
  /-- Number of probes used to spill persistent registers at operation exit. -/
  spillProbes : ℕ
  /-- Reload persistent registers and install caller arguments `argRegs` on `input` registers. -/
  reload : (Fin r → ℕ) → ProbeTree (S + regCells) wCell (Fin r → ℕ)
  /-- Spill persistent registers from final `regs` back to dedicated register cells. -/
  spill : (Fin r → ℕ) → ProbeTree (S + regCells) wCell PUnit
  /-- Pack a Word-RAM `Data r` state into `Mem (S + regCells) wCell`. -/
  pack : Data r → Mem (S + regCells) wCell
  /-- Unpack `Mem (S + regCells) wCell` with `argRegs` into `Data r` (`0` outside `[base, base+S)`).
  -/
  unpack : (Fin r → ℕ) → Mem (S + regCells) wCell → Data r
  /-- Well-formedness of `m` on untouched data/register cells (`True` on `standardLayout`). -/
  ValidMem : Mem (S + regCells) wCell → Prop
  validMem_pack : ∀ (y : Data r), ValidMem (pack y)
  validMem_data : ∀ {m : Mem (S + regCells) wCell}, ValidMem m →
    ∀ idx : Fin S, (m (Fin.castAdd regCells idx)).1 < 2 ^ w
  unpack_pers_fits : ∀ (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell) (i : Fin r),
    input i = false → Fits w ((unpack argRegs m).regs i)
  run_reload : ∀ (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell),
    (reload argRegs).run m = ((unpack argRegs m).regs, m)
  probes_reload : ∀ (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell),
    (reload argRegs).probes m = reloadProbes
  probes_spill : ∀ (regs : Fin r → ℕ) (m : Mem (S + regCells) wCell),
    (spill regs).probes m = spillProbes
  nextMem_spill_data : ∀ (regs : Fin r → ℕ) (m : Mem (S + regCells) wCell) (idx : Fin S),
    ((spill regs).run m).2 (Fin.castAdd regCells idx) = m (Fin.castAdd regCells idx)
  nextMem_spill_reg : ∀ (y : Data r) (m : Mem (S + regCells) wCell) (c : Fin (S + regCells)),
    (∀ d : Fin (S + regCells), S ≤ d.1 → m d = m d) →
    (persCount input = 0 → ∀ d : Fin (S + regCells), S ≤ d.1 → m d = pack y d) →
    S ≤ c.1 → ((spill y.regs).run m).2 c = pack y c
  validMem_reg_zero : ∀ {m : Mem (S + regCells) wCell}, ValidMem m →
    persCount input = 0 → ∀ (y : Data r) (d : Fin (S + regCells)), S ≤ d.1 → m d = pack y d
  pack_data : ∀ (y : Data r) (idx : Fin S),
    pack y (Fin.castAdd regCells idx) =
      ⟨(wordOfNat w (y.mem (base + idx.1))).1,
        lt_of_lt_of_le (wordOfNat w _).isLt (Nat.pow_le_pow_right (by omega) hw)⟩
  unpack_mem : ∀ (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell) (a : ℕ),
    (unpack argRegs m).mem a =
      if ha : base ≤ a ∧ a < base + S then
        (m (Fin.castAdd regCells ⟨a - base, by omega⟩)).1 % 2 ^ w
      else 0
  unpack_regs_input : ∀ (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell) (i : Fin r),
    input i = true → (unpack argRegs m).regs i = argRegs i
  unpack_regs_pers : ∀ (argRegs₁ argRegs₂ : Fin r → ℕ) (m : Mem (S + regCells) wCell) (i : Fin r),
    input i = false → (unpack argRegs₁ m).regs i = (unpack argRegs₂ m).regs i
  unpack_pack_regs : ∀ (argRegs : Fin r → ℕ) {x : Data r}, x.Bounded w → ∀ i : Fin r,
    (unpack argRegs (pack x)).regs i = if input i then argRegs i else x.regs i

namespace RegLayout

variable {r : ℕ} {input : Fin r → Bool} {base S w regCells wCell : ℕ}

/-- Total reload + spill probe overhead per operation. -/
@[expose] def overhead (L : RegLayout r input base S w regCells wCell) : ℕ :=
  L.reloadProbes + L.spillProbes

/-- Canonical `Data r` view setting `input` registers to `0`. -/
def canonical (L : RegLayout r input base S w regCells wCell)
    (m : Mem (S + regCells) wCell) : Data r :=
  L.unpack (fun _ => 0) m

theorem unpack_bounded (L : RegLayout r input base S w regCells wCell)
    {argRegs : Fin r → ℕ} (harg : ∀ i, input i = true → Fits w (argRegs i))
    (m : Mem (S + regCells) wCell) :
    (L.unpack argRegs m).Bounded w := by
  refine ⟨fun i => ?_, fun a => ?_⟩
  · by_cases hi : input i = true
    · rw [L.unpack_regs_input argRegs m i hi]
      exact harg i hi
    · exact L.unpack_pers_fits argRegs m i (Bool.eq_false_iff.mpr hi)
  · rw [L.unpack_mem]
    split_ifs
    · exact Nat.mod_lt _ (Nat.two_pow_pos w)
    · exact fits_zero w

theorem canonical_bounded (L : RegLayout r input base S w regCells wCell)
    (m : Mem (S + regCells) wCell) :
    (L.canonical m).Bounded w :=
  L.unpack_bounded (fun _ _ => fits_zero w) m

theorem unpack_pack_mem (L : RegLayout r input base S w regCells wCell)
    (argRegs : Fin r → ℕ) {x : Data r} (hx : x.Bounded w) (a : ℕ) :
    (L.unpack argRegs (L.pack x)).mem a = (zeroOutside base S x).mem a := by
  rw [L.unpack_mem]
  dsimp only [zeroOutside]
  split_ifs with ha
  · rw [L.pack_data x ⟨a - base, by omega⟩]
    dsimp only
    have hadd : base + (a - base) = a := by omega
    rw [hadd, Nat.mod_eq_of_lt (wordOfNat w _).isLt, wordOfNat_val_of_fits (hx.2 a)]
  · rfl

end RegLayout

/-- Standard `w`-bit cell layout over `S + persCount input` cells (`overhead = 2 * persCount input`,
equal to `0` when `∀ i, input i = true`). -/
def standardLayout {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    RegLayout r input base S w (persCount input) w where
  hw := le_rfl
  reloadProbes := persCount input
  spillProbes := persCount input
  reload argRegs := do
    let vals ← readFin (fun k : Fin (persCount input) => Fin.natAdd S k)
    pure fun i =>
      if hi : input i = true then argRegs i
      else (vals (persIdx input i (Bool.eq_false_iff.mpr hi))).1
  spill regs :=
    writeFin (fun k : Fin (persCount input) => Fin.natAdd S k)
      (fun k => wordOfNat w (regs (persReg input k)))
  pack := packMem input base S w
  unpack argRegs m := unpackData input argRegs base S w m
  ValidMem _ := True
  validMem_pack _ := trivial
  validMem_data {m} _ idx := (m (Fin.castAdd (persCount input) idx)).isLt
  unpack_pers_fits argRegs m i hi := by
    dsimp only [unpackData]
    split_ifs with h
    · exact absurd (hi.symm.trans h) Bool.false_ne_true
    · exact (m _).isLt
  run_reload argRegs m := by
    simp only [ProbeTree.run_bind, run_readFin, ProbeTree.run_pure]
    rfl
  probes_reload argRegs m := by
    simp only [ProbeTree.probes_bind, probes_readFin, run_readFin, ProbeTree.probes_pure, add_zero]
  probes_spill regs m := probes_writeFin _ _ m
  nextMem_spill_data regs m idx :=
    nextMem_writeFin_of_forall_ne _ _ m (Fin.castAdd (persCount input) idx) fun k heq => by
      have hval : idx.1 = S + k.1 := by simpa using congrArg Fin.val heq
      omega
  nextMem_spill_reg y m c _ _ hc := by
    let k : Fin (persCount input) := ⟨c.1 - S, by omega⟩
    have hc_eq : c = Fin.natAdd S k := Fin.ext (by simp [k]; omega)
    have hinj : Function.Injective (fun j : Fin (persCount input) => Fin.natAdd S j) :=
      fun a b h => Fin.ext (by simpa using congrArg Fin.val h)
    rw [hc_eq, nextMem_writeFin_apply hinj]
    have hnotlt : ¬ (Fin.natAdd S k).1 < S := by simp
    simp only [packMem, hnotlt, ↓reduceDIte]
    have hsub : (⟨(Fin.natAdd S k).1 - S, by omega⟩ : Fin (persCount input)) = k := by
      ext; simp
    rw [hsub]
  validMem_reg_zero _ h0 _ d hd := by
    have hlt := d.isLt
    omega
  pack_data y idx := by simp [packMem]
  unpack_mem argRegs m a := by
    dsimp only [unpackData]
    split_ifs with ha
    · exact (Nat.mod_eq_of_lt (m _).isLt).symm
    · rfl
  unpack_regs_input argRegs m i hi := by simp [unpackData, hi]
  unpack_regs_pers _ _ m i hi := by simp [unpackData, hi]
  unpack_pack_regs argRegs {_} hx i := unpackData_packMem_regs hx i

@[simp]
theorem standardLayout_overhead {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    (standardLayout input base S w).overhead = 2 * persCount input := by
  simp [RegLayout.overhead, standardLayout, two_mul]

@[simp]
theorem standardLayout_spillProbes {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    (standardLayout input base S w).spillProbes = persCount input := by
  simp [standardLayout]

theorem standardLayout_validMem {r : ℕ} (input : Fin r → Bool) (base S w : ℕ)
    (m : Mem (S + persCount input) w) :
    (standardLayout input base S w).ValidMem m := by
  simp [standardLayout]

/-- Wide-cell single-spill layout over `S + 1` cells of width `wideWidth input w` (`0` probes for
reload + spill when `persCount input = 0`, `2` probes when `persCount input > 0`). -/
def wideLayout {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    RegLayout r input base S w 1 (wideWidth input w) where
  hw := le_wideWidth input w
  reloadProbes := if persCount input = 0 then 0 else 1
  spillProbes := if persCount input = 0 then 0 else 1
  reload argRegs :=
    if h0 : persCount input = 0 then
      pure fun i =>
        if hi : input i = true then argRegs i
        else False.elim (by
          have hmem : i ∈ persRegs input := mem_persRegs.mpr (Bool.eq_false_iff.mpr hi)
          have hpos : 0 < persCount input := Finset.card_pos.mpr ⟨i, hmem⟩
          omega)
    else do
      let cellVal ← ProbeTree.read (Fin.last S)
      pure fun i =>
        if hi : input i = true then argRegs i
        else
          (unpackDigits (persCount input) w cellVal.1
            (persIdx input i (Bool.eq_false_iff.mpr hi))).1
  spill regs :=
    if h0 : persCount input = 0 then
      pure PUnit.unit
    else
      have hlt_pers :
          packDigits (persCount input) w (fun k => wordOfNat w (regs (persReg input k))) <
            2 ^ wideWidth input w :=
        lt_of_lt_of_le (packDigits_lt _ _ _)
          (Nat.pow_le_pow_right (by omega) (persCount_mul_le_wideWidth input w))
      ProbeTree.write (Fin.last S)
        ⟨packDigits (persCount input) w (fun k => wordOfNat w (regs (persReg input k))), hlt_pers⟩
  pack := packMemWide input base S w
  unpack argRegs m := unpackDataWide input argRegs base S w m
  ValidMem m := DataCellsBounded S w (wideWidth input w) m ∧
    (persCount input = 0 → (m (Fin.last S)).1 = 0)
  validMem_pack y := ⟨dataCellsBounded_packMemWide input base S w y, fun h0 => by
    simp [packMemWide, packDigits_eq_zero_of_zero h0]⟩
  validMem_data hm := hm.1
  unpack_pers_fits argRegs m i hi := by
    dsimp only [unpackDataWide]
    split_ifs with h
    · exact absurd (hi.symm.trans h) Bool.false_ne_true
    · exact (unpackDigits _ _ _ _).isLt
  run_reload argRegs m := by
    by_cases h0 : persCount input = 0
    · simp only [h0, ↓reduceDIte, ProbeTree.run_pure]
      refine Prod.ext (funext fun i => ?_) rfl
      dsimp only [unpackDataWide]
      split_ifs with hi
      · rfl
      · exfalso
        have hmem : i ∈ persRegs input := mem_persRegs.mpr (Bool.eq_false_iff.mpr hi)
        have hpos : 0 < persCount input := Finset.card_pos.mpr ⟨i, hmem⟩
        omega
    · simp only [h0, ↓reduceDIte, ProbeTree.run_bind, ProbeTree.run_read, ProbeTree.run_pure]
      rfl
  probes_reload argRegs m := by
    by_cases h0 : persCount input = 0 <;> simp [h0]
  probes_spill regs m := by
    by_cases h0 : persCount input = 0 <;> simp [h0]
  nextMem_spill_data regs m idx := by
    by_cases h0 : persCount input = 0
    · simp [h0]
    · simp only [h0, ↓reduceDIte, ProbeTree.run_write]
      have hne : Fin.castAdd 1 idx ≠ Fin.last S := fun heq => by
        have hval : idx.1 = S := by simpa using congrArg Fin.val heq
        omega
      exact Function.update_of_ne hne _ m
  nextMem_spill_reg y m c _ hzero hc := by
    have hc_eq : c = Fin.last S := Fin.ext (by simp; omega)
    subst hc_eq
    by_cases h0 : persCount input = 0
    · simp only [h0, ↓reduceDIte, ProbeTree.run_pure]
      exact hzero h0 (Fin.last S) hc
    · simp [h0, packMemWide]
  validMem_reg_zero hm h0 y d hd := by
    have hd_eq : d = Fin.last S := Fin.ext (by simp; omega)
    subst hd_eq
    refine Fin.ext ?_
    simp [hm.2 h0, packMemWide, packDigits_eq_zero_of_zero h0]
  pack_data y idx := by simp [packMemWide]
  unpack_mem _ _ _ := rfl
  unpack_regs_input argRegs m i hi := by simp [unpackDataWide, hi]
  unpack_regs_pers _ _ m i hi := by simp [unpackDataWide, hi]
  unpack_pack_regs argRegs {_} hx i := unpackDataWide_packMemWide_regs hx i

@[simp]
theorem wideLayout_overhead {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    (wideLayout input base S w).overhead = if persCount input = 0 then 0 else 2 := by
  by_cases h0 : persCount input = 0 <;> simp [RegLayout.overhead, wideLayout, h0]

theorem wideLayout_overhead_le {r : ℕ} (input : Fin r → Bool) (base S w : ℕ) :
    (wideLayout input base S w).overhead ≤ 2 := by
  rw [wideLayout_overhead]
  split_ifs <;> omega


/-! ### 3. Intra-operation write buffer and deterministic `ProbeTree` simulation -/

/-- Intra-operation simulator configuration over `[base, base + S)` with pure-Lean write buffer
`writeBuf` and outside-footprint memory `extMem`. -/
inductive SimOutcome (S w r : ℕ) : Type where
  | running (pc : ℕ) (regs : Fin r → ℕ) (writeBuf : Fin S → Option (Fin (2 ^ w))) (extMem : ℕ → ℕ)
  | halted (out : ℕ) (regs : Fin r → ℕ) (writeBuf : Fin S → Option (Fin (2 ^ w))) (extMem : ℕ → ℕ)
  | faulted

/-- Number of modified cells buffered in `writeBuf`. -/
def dirtyCount {S w : ℕ} (writeBuf : Fin S → Option (Fin (2 ^ w))) : ℕ :=
  (Finset.univ.filter fun idx : Fin S => (writeBuf idx).isSome).card

private theorem dirtyCount_empty (S w : ℕ) :
    dirtyCount (fun _ : Fin S => (none : Option (Fin (2 ^ w)))) = 0 := by
  simp [dirtyCount]

private theorem dirtyCount_update_le {S w : ℕ} (writeBuf : Fin S → Option (Fin (2 ^ w)))
    (idx : Fin S) (v : Fin (2 ^ w)) :
    dirtyCount (Function.update writeBuf idx (some v)) ≤ dirtyCount writeBuf + 1 := by
  have hsub :
      (Finset.univ.filter fun j : Fin S => (Function.update writeBuf idx (some v) j).isSome) ⊆
        insert idx (Finset.univ.filter fun j : Fin S => (writeBuf j).isSome) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_cases hji : j = idx
    · subst hji
      exact Finset.mem_insert_self j _
    · rw [Function.update_of_ne hji] at hj
      exact Finset.mem_insert_of_mem (by simp [hj])
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- Reconstruct the full Word-RAM `Data r` represented by `(regs, writeBuf, extMem)` over base
memory `m`. -/
def reconstructData {r S regCells w wCell : ℕ} (base : ℕ) (m : Mem (S + regCells) wCell)
    (regs : Fin r → ℕ) (writeBuf : Fin S → Option (Fin (2 ^ w))) (extMem : ℕ → ℕ) : Data r where
  regs := regs
  mem a :=
    if ha : base ≤ a ∧ a < base + S then
      match writeBuf ⟨a - base, by omega⟩ with
      | some v => v.1
      | none => (m (Fin.castAdd regCells ⟨a - base, by omega⟩)).1 % 2 ^ w
    else extMem a

private theorem reconstructData_init {r : ℕ} {input : Fin r → Bool}
    {base S w regCells wCell : ℕ} (L : RegLayout r input base S w regCells wCell)
    (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell) :
    reconstructData (w := w) base m (L.unpack argRegs m).regs (fun _ => none) (fun _ => 0) =
      L.unpack argRegs m := by
  ext i
  · rfl
  · simp only [reconstructData, L.unpack_mem]

/-- Embed a `w`-bit word into `Fin (2 ^ wCell)` when `w ≤ wCell`. -/
def liftCellWord {w wCell : ℕ} (hw : w ≤ wCell) (v : Fin (2 ^ w)) : Fin (2 ^ wCell) :=
  ⟨v.1, lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega) hw)⟩

/-- Flush modified cells from `writeBuf` (`0 .. j - 1`) to data cells `0 .. S - 1`. -/
def flushAux {S regCells w wCell : ℕ} (hw : w ≤ wCell)
    (writeBuf : Fin S → Option (Fin (2 ^ w))) :
    (j : ℕ) → j ≤ S → ProbeTree (S + regCells) wCell PUnit
  | 0, _ => pure PUnit.unit
  | k + 1, hk => do
      let _ ← flushAux hw writeBuf k (by omega)
      let idx : Fin S := ⟨k, hk⟩
      match writeBuf idx with
      | none => pure PUnit.unit
      | some v => ProbeTree.write (Fin.castAdd regCells idx) (liftCellWord hw v)

/-- Flush all modified cells of `writeBuf` to `Mem (S + regCells) wCell` in `dirtyCount writeBuf`
write probes. -/
def flushWriteBuf {S regCells w wCell : ℕ} (hw : w ≤ wCell)
    (writeBuf : Fin S → Option (Fin (2 ^ w))) : ProbeTree (S + regCells) wCell PUnit :=
  flushAux hw writeBuf S le_rfl

private theorem flushAux_spec {S regCells w wCell : ℕ} (hw : w ≤ wCell)
    (writeBuf : Fin S → Option (Fin (2 ^ w))) :
    ∀ (j : ℕ) (hj : j ≤ S) (m : Mem (S + regCells) wCell),
      (flushAux hw writeBuf j hj).probes m =
        ((Finset.univ.filter fun idx : Fin S => idx.1 < j ∧ (writeBuf idx).isSome)).card ∧
      (∀ idx : Fin S, idx.1 < j →
        ((flushAux hw writeBuf j hj).run m).2 (Fin.castAdd regCells idx) =
          match writeBuf idx with
          | some v => liftCellWord hw v
          | none => m (Fin.castAdd regCells idx)) ∧
      (∀ c : Fin (S + regCells), j ≤ c.1 →
        ((flushAux hw writeBuf j hj).run m).2 c = m c)
  | 0, _, m => by
    dsimp only [flushAux]
    refine ⟨?_, fun _ h => by omega, fun _ _ => rfl⟩
    simp
  | k + 1, hk, m => by
    obtain ⟨hpr, hlt, hge⟩ := flushAux_spec hw writeBuf k (by omega) m
    set m₁ := ((flushAux hw writeBuf k (by omega)).run m).2
    set idx_k : Fin S := ⟨k, hk⟩
    have hpart :
        (Finset.univ.filter fun idx : Fin S => idx.1 < k + 1 ∧ (writeBuf idx).isSome) =
          if (writeBuf idx_k).isSome then
            insert idx_k (Finset.univ.filter fun idx : Fin S => idx.1 < k ∧ (writeBuf idx).isSome)
          else
            Finset.univ.filter fun idx : Fin S => idx.1 < k ∧ (writeBuf idx).isSome := by
      by_cases hs : (writeBuf idx_k).isSome = true
      · rw [ite_eq_left_iff.mpr fun h => absurd hs h]
        refine Finset.ext fun idx => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with hlt_k | heq_k
          · exact Or.inr ⟨hlt_k, h2⟩
          · exact Or.inl (Fin.ext heq_k)
        · rintro (rfl | ⟨hlt_k, h2⟩)
          · exact ⟨by simp [idx_k], hs⟩
          · exact ⟨by omega, h2⟩
      · rw [ite_eq_right_iff.mpr fun h => absurd h hs]
        refine Finset.ext fun idx => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with hlt_k | heq_k
          · exact ⟨hlt_k, h2⟩
          · have : idx = idx_k := Fin.ext heq_k
            subst this
            exact absurd h2 hs
        · rintro ⟨hlt_k, h2⟩
          exact ⟨by omega, h2⟩
    have hnotMem :
        idx_k ∉ (Finset.univ.filter fun idx : Fin S => idx.1 < k ∧ (writeBuf idx).isSome) := by
      simp [idx_k]
    dsimp only [flushAux]
    cases hwb : writeBuf idx_k with
    | none =>
      simp only [ProbeTree.probes_bind, ProbeTree.probes_pure, add_zero,
        ProbeTree.run_bind, ProbeTree.run_pure]
      refine ⟨?_, ?_, ?_⟩
      · rw [hpr, hpart]
        simp only [hwb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      · intro idx hidx
        rcases Nat.lt_succ_iff_lt_or_eq.mp hidx with hlt_k | heq_k
        · exact hlt idx hlt_k
        · have : idx = idx_k := Fin.ext heq_k
          subst this
          rw [hwb]
          exact hge (Fin.castAdd regCells idx_k) (by simp [idx_k])
      · intro c hc
        exact hge c (by omega)
    | some v =>
      simp only [ProbeTree.probes_bind, ProbeTree.probes_write,
        ProbeTree.run_bind, ProbeTree.run_write]
      refine ⟨?_, ?_, ?_⟩
      · rw [hpr, hpart]
        simp only [hwb, Option.isSome_some, ↓reduceIte, Finset.card_insert_of_notMem hnotMem]
      · intro idx hidx
        rcases Nat.lt_succ_iff_lt_or_eq.mp hidx with hlt_k | heq_k
        · have hne : Fin.castAdd regCells idx ≠ Fin.castAdd regCells idx_k := fun h => by
            have : idx.1 = k := by simpa [idx_k] using congrArg Fin.val h
            omega
          rw [Function.update_of_ne hne]
          exact hlt idx hlt_k
        · have : idx = idx_k := Fin.ext heq_k
          subst this
          rw [hwb]
          exact Function.update_self _ _ _
      · intro c hc
        have hne : c ≠ Fin.castAdd regCells idx_k := fun h => by
          have : c.1 = k := by simpa [idx_k] using congrArg Fin.val h
          omega
        rw [Function.update_of_ne hne]
        exact hge c (by omega)

theorem probes_flushWriteBuf {S regCells w wCell : ℕ} (hw : w ≤ wCell)
    (writeBuf : Fin S → Option (Fin (2 ^ w))) (m : Mem (S + regCells) wCell) :
    (flushWriteBuf hw writeBuf).probes m = dirtyCount writeBuf := by
  obtain ⟨hpr, _, _⟩ := flushAux_spec hw writeBuf S le_rfl m
  rw [flushWriteBuf, hpr, dirtyCount]
  congr 1
  refine Finset.ext fun idx => ?_
  simp

/-- Flush `writeBuf` and spill persistent registers according to `L`, producing `L.pack y` whenever
`y = reconstructData base m regs writeBuf extMem` and `y.Bounded w` and `L.ValidMem m`. -/
def commitHalted {r : ℕ} {input : Fin r → Bool} {base S w regCells wCell : ℕ}
    (L : RegLayout r input base S w regCells wCell)
    (regs : Fin r → ℕ) (writeBuf : Fin S → Option (Fin (2 ^ w))) :
    ProbeTree (S + regCells) wCell PUnit := do
  let _ ← flushWriteBuf L.hw writeBuf
  L.spill regs

theorem commitHalted_spec {r : ℕ} {input : Fin r → Bool} {base S w regCells wCell : ℕ}
    (L : RegLayout r input base S w regCells wCell)
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m)
    (regs : Fin r → ℕ) (writeBuf : Fin S → Option (Fin (2 ^ w))) (extMem : ℕ → ℕ) :
    ((commitHalted L regs writeBuf).run m).2 =
        L.pack (reconstructData base m regs writeBuf extMem) ∧
      (commitHalted L regs writeBuf).probes m = dirtyCount writeBuf + L.spillProbes := by
  set y := reconstructData base m regs writeBuf extMem
  obtain ⟨hpr_f, hlt_f, hge_f⟩ := flushAux_spec L.hw writeBuf S le_rfl m
  set m₁ := ((flushWriteBuf L.hw writeBuf).run m).2
  have hm₁_reg : ∀ d : Fin (S + regCells), S ≤ d.1 → m₁ d = m d := fun d hd => hge_f d hd
  refine ⟨funext fun c => ?_, ?_⟩
  · by_cases hc : c.1 < S
    · let idx : Fin S := ⟨c.1, hc⟩
      have hc_eq : c = Fin.castAdd regCells idx := Fin.ext rfl
      rw [hc_eq]
      simp only [commitHalted, ProbeTree.run_bind]
      change ((L.spill regs).run m₁).2 (Fin.castAdd regCells idx) = _
      rw [L.nextMem_spill_data regs m₁ idx, L.pack_data y idx]
      have hfl : m₁ (Fin.castAdd regCells idx) =
          match writeBuf idx with
          | some v => liftCellWord L.hw v
          | none => m (Fin.castAdd regCells idx) := hlt_f idx hc
      have hown : base ≤ base + idx.1 ∧ base + idx.1 < base + S := ⟨by omega, by omega⟩
      have hsub : (⟨base + idx.1 - base, by omega⟩ : Fin S) = idx := by ext; simp
      have hymem : y.mem (base + idx.1) =
          match writeBuf idx with
          | some v => v.1
          | none => (m (Fin.castAdd regCells idx)).1 % 2 ^ w := by
        dsimp only [y, reconstructData]
        split_ifs
        rw [hsub]
      rw [hfl]
      cases hwb : writeBuf idx with
      | some v =>
        rw [hymem]
        simp [hwb, liftCellWord, wordOfNat_val_of_fits v.isLt]
      | none =>
        have hlt_m : (m (Fin.castAdd regCells idx)).1 < 2 ^ w := L.validMem_data hm idx
        rw [hymem]
        simp only [hwb, Nat.mod_eq_of_lt hlt_m, wordOfNat_val_of_fits hlt_m]
    · have hge : S ≤ c.1 := Nat.le_of_not_lt hc
      simp only [commitHalted, ProbeTree.run_bind]
      change ((L.spill y.regs).run m₁).2 c = L.pack y c
      exact L.nextMem_spill_reg y m₁ c (fun _ _ => rfl)
        (fun h0 d hd => (hm₁_reg d hd).trans (L.validMem_reg_zero hm h0 y d hd)) hge
  · simp only [commitHalted, ProbeTree.probes_bind, probes_flushWriteBuf, L.probes_spill]

/-! #### Single-step and clocked deterministic `ProbeTree` simulation -/

/-- One step of buffered deterministic flat-program simulation in `ProbeTree` (issuing `1` read
probe on an uncached `.load` inside `[base, base + S)` and `0` probes on all other instructions). -/
def simStepDet {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ) (p : Program B r) :
    SimOutcome S w r → ProbeTree (S + regCells) wCell (SimOutcome S w r)
  | .halted out regs wb ext => pure (.halted out regs wb ext)
  | .faulted => pure .faulted
  | .running pc regs writeBuf extMem =>
    match p[pc]? with
    | none => pure .faulted
    | some (.halt i) => pure (.halted (regs i) regs writeBuf extMem)
    | some (.jump t) => pure (.running t regs writeBuf extMem)
    | some (.branch c t) =>
      pure (.running (if c.Holds ⟨regs, fun _ => 0⟩ then t else pc + 1) regs writeBuf extMem)
    | some (.rand _ _) => pure .faulted
    | some (.op (.const d v)) =>
      if Fits w v then
        pure (.running (pc + 1) (Function.update regs d v) writeBuf extMem)
      else
        pure .faulted
    | some (.op (.copy d src)) =>
      pure (.running (pc + 1) (Function.update regs d (regs src)) writeBuf extMem)
    | some (.op (.alu f d args)) =>
      match B.interp w f (regs ∘ args) with
      | some v =>
        if Fits w v then
          pure (.running (pc + 1) (Function.update regs d v) writeBuf extMem)
        else
          pure .faulted
      | none => pure .faulted
    | some (.op (.load d a)) =>
      let addr := regs a
      if ha : base ≤ addr ∧ addr < base + S then
        let idx : Fin S := ⟨addr - base, by omega⟩
        match writeBuf idx with
        | some v =>
          pure (.running (pc + 1) (Function.update regs d v.1) writeBuf extMem)
        | none => do
          let raw ← ProbeTree.read (Fin.castAdd regCells idx)
          pure (.running (pc + 1) (Function.update regs d (raw.1 % 2 ^ w)) writeBuf extMem)
      else
        pure (.running (pc + 1) (Function.update regs d (extMem addr)) writeBuf extMem)
    | some (.op (.store a src)) =>
      let addr := regs a
      let val := regs src
      if ha : base ≤ addr ∧ addr < base + S then
        pure (.running (pc + 1) regs
          (Function.update writeBuf ⟨addr - base, by omega⟩ (some (wordOfNat w val))) extMem)
      else
        pure (.running (pc + 1) regs writeBuf (Function.update extMem addr val))

private theorem cond_holds_regs_only {r : ℕ} (c : Cond r) (x : Data r) :
    c.Holds ⟨x.regs, fun _ => 0⟩ ↔ c.Holds x := by
  cases c <;> rfl

theorem simStepDet_nextMem {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ) (p : Program B r)
    (st : SimOutcome S w r) (m : Mem (S + regCells) wCell) :
    ((simStepDet (regCells := regCells) (wCell := wCell) base p st).run m).2 = m := by
  cases st with
  | halted => rfl
  | faulted => rfl
  | running pc regs writeBuf extMem =>
    dsimp only [simStepDet]
    rcases hp : p[pc]? with _ | instr
    · rfl
    · cases instr with
      | op o =>
        cases o with
        | const d v =>
          dsimp only
          by_cases hv : Fits w v <;> simp [hv]
        | copy d src => rfl
        | alu f d args =>
          dsimp only
          cases B.interp w f (regs ∘ args) with
          | none => rfl
          | some v =>
            dsimp only
            by_cases hv : Fits w v <;> simp [hv]
        | load d a =>
          dsimp only
          split_ifs with ha
          · cases writeBuf ⟨regs a - base, by omega⟩ <;> simp
          · rfl
        | store a src =>
          dsimp only
          split_ifs <;> rfl
      | jump => rfl
      | branch => rfl
      | halt => rfl
      | rand => rfl

/-- Exact single-step correspondence between `simStepDet` and `WordRAM.step`. -/
theorem simStepDet_spec {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ) (p : Program B r)
    (pc : ℕ) {regs : Fin r → ℕ} {writeBuf : Fin S → Option (Fin (2 ^ w))} {extMem : ℕ → ℕ}
    (m : Mem (S + regCells) wCell)
    (hx : (reconstructData base m regs writeBuf extMem).Bounded w) :
    let x := reconstructData base m regs writeBuf extMem
    let t := simStepDet (regCells := regCells) (w := w) (wCell := wCell)
      base p (.running pc regs writeBuf extMem)
    (t.run m).2 = m ∧
    match step w p ⟨pc, x⟩ with
    | .next s' =>
      ∃ writeBuf' extMem',
        (t.run m).1 = .running s'.pc s'.data.regs writeBuf' extMem' ∧
        reconstructData base m s'.data.regs writeBuf' extMem' = s'.data ∧
        t.probes m + dirtyCount writeBuf' ≤ 1 + dirtyCount writeBuf
    | .halt v =>
      (t.run m).1 = .halted v regs writeBuf extMem ∧ t.probes m = 0
    | .fault =>
      (t.run m).1 = .faulted ∧ t.probes m = 0 := by
  intro x t
  refine ⟨simStepDet_nextMem base p _ m, ?_⟩
  dsimp only [t, simStepDet, step]
  rcases hp : p[pc]? with _ | instr
  · simp
  · cases instr with
    | halt i => simp [x, reconstructData]
    | jump tgt =>
      exact ⟨writeBuf, extMem, rfl, rfl, by simp⟩
    | branch c tgt =>
      dsimp only
      have hc : c.Holds ⟨regs, fun _ => 0⟩ ↔ c.Holds x := cond_holds_regs_only c x
      exact ⟨writeBuf, extMem, by simp [hc, x, reconstructData], rfl, by simp⟩
    | rand _ _ => simp
    | op o =>
      cases o with
      | const d v =>
        dsimp only
        by_cases hv : Fits w v
        · simp only [Op.eval_const, Data.put_of_fits hv, hv, ↓reduceIte, ProbeTree.run_pure,
            ProbeTree.probes_pure, zero_add]
          exact ⟨writeBuf, extMem, rfl, Data.ext rfl rfl,
            le_add_of_nonneg_left (Nat.zero_le _)⟩
        · have hput : x.put w d v = none := by simp [Data.put, hv]
          simp [Op.eval_const, hput, hv]
      | copy d src =>
        dsimp only
        simp only [Op.eval_copy, ProbeTree.run_pure, ProbeTree.probes_pure, zero_add]
        exact ⟨writeBuf, extMem, rfl, Data.ext rfl rfl,
          le_add_of_nonneg_left (Nat.zero_le _)⟩
      | alu f d args =>
        dsimp only
        have hargs : (x.regs ∘ args) = (regs ∘ args) := rfl
        rw [Op.eval_alu, hargs]
        cases hbi : B.interp w f (regs ∘ args) with
        | none => simp
        | some v =>
          dsimp only [Option.bind]
          by_cases hv : Fits w v
          · simp only [Data.put_of_fits hv, hv, ↓reduceIte, ProbeTree.run_pure,
              ProbeTree.probes_pure, zero_add]
            exact ⟨writeBuf, extMem, rfl, Data.ext rfl rfl,
              le_add_of_nonneg_left (Nat.zero_le _)⟩
          · have hput : x.put w d v = none := by simp [Data.put, hv]
            simp [hput, hv]
      | load d a =>
        dsimp only [Op.eval_load]
        have haddr : x.regs a = regs a := rfl
        by_cases ha : base ≤ regs a ∧ regs a < base + S
        · simp only [ha, and_self, ↓reduceDIte]
          cases hwb : writeBuf ⟨regs a - base, by omega⟩ with
          | some v =>
            have hxmem : x.mem (regs a) = v.1 := by
              dsimp only [x, reconstructData]
              split_ifs
              rw [hwb]
            simp only [ProbeTree.run_pure, ProbeTree.probes_pure, zero_add]
            refine ⟨writeBuf, extMem, ?_, ?_, le_add_of_nonneg_left (Nat.zero_le _)⟩
            · dsimp only [Data.set]
              rw [haddr, hxmem]
              rfl
            · refine Data.ext ?_ rfl
              funext i
              dsimp only [Data.set, x, reconstructData]
          | none =>
            have hxmem : x.mem (regs a) =
                (m (Fin.castAdd regCells ⟨regs a - base, by omega⟩)).1 % 2 ^ w := by
              dsimp only [x, reconstructData]
              split_ifs
              rw [hwb]
            simp only [ProbeTree.run_bind, ProbeTree.run_read, ProbeTree.run_pure,
              ProbeTree.probes_bind, ProbeTree.probes_read, ProbeTree.probes_pure, add_zero]
            refine ⟨writeBuf, extMem, ?_, ?_, le_rfl⟩
            · dsimp only [Data.set]
              rw [haddr, hxmem]
              rfl
            · refine Data.ext ?_ rfl
              funext i
              dsimp only [Data.set, x, reconstructData]
        · simp only [ha, ↓reduceDIte, ProbeTree.run_pure, ProbeTree.probes_pure, zero_add]
          have hxmem : x.mem (regs a) = extMem (regs a) := by
            dsimp only [x, reconstructData]
            split_ifs
            rfl
          refine ⟨writeBuf, extMem, ?_, ?_, le_add_of_nonneg_left (Nat.zero_le _)⟩
          · dsimp only [Data.set]
            rw [haddr, hxmem]
            rfl
          · refine Data.ext ?_ rfl
            funext i
            dsimp only [Data.set, x, reconstructData]
      | store a src =>
        dsimp only [Op.eval_store]
        have hfit_val : Fits w (regs src) := hx.1 src
        by_cases ha : base ≤ regs a ∧ regs a < base + S
        · simp only [ha, and_self, ↓reduceDIte, ProbeTree.run_pure, ProbeTree.probes_pure, zero_add]
          set wb' := Function.update writeBuf ⟨regs a - base, by omega⟩
            (some (wordOfNat w (regs src)))
          refine ⟨wb', extMem, rfl, ?_, ?_⟩
          · refine Data.ext rfl (funext fun b => ?_)
            dsimp only [reconstructData, Data.write, x]
            by_cases hb : b = regs a
            · subst hb
              rw [Function.update_self]
              split_ifs
              simp [wb', wordOfNat_val_of_fits hfit_val]
            · rw [Function.update_of_ne hb]
              by_cases hba : base ≤ b ∧ b < base + S
              · have hne_idx : (⟨b - base, by omega⟩ : Fin S) ≠ ⟨regs a - base, by omega⟩ :=
                  fun h => hb (by
                    have hval : b - base = regs a - base := congrArg Fin.val h
                    omega)
                split_ifs
                simp only [wb', Function.update_of_ne hne_idx]
              · split_ifs
                rfl
          · exact Nat.add_comm _ 1 ▸ dirtyCount_update_le writeBuf _ _
        · simp only [ha, ↓reduceDIte, ProbeTree.run_pure, ProbeTree.probes_pure, zero_add]
          refine ⟨writeBuf, Function.update extMem (regs a) (regs src), rfl, ?_,
            le_add_of_nonneg_left (Nat.zero_le _)⟩
          refine Data.ext rfl (funext fun b => ?_)
          dsimp only [reconstructData, Data.write, x]
          by_cases hb : b = regs a
          · subst hb
            rw [Function.update_self, Function.update_self]
            split_ifs
            rfl
          · rw [Function.update_of_ne hb, Function.update_of_ne hb]

/-- Run `simStepDet` for `K` clocked steps. -/
def simLoopDet {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ) (p : Program B r) :
    ℕ → SimOutcome S w r → ProbeTree (S + regCells) wCell (SimOutcome S w r)
  | 0, st => pure st
  | K + 1, st => do
      let st' ← simStepDet base p st
      simLoopDet base p K st'

private theorem simLoopDet_add {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) (K₁ K₂ : ℕ) (st : SimOutcome S w r) :
    simLoopDet (regCells := regCells) (wCell := wCell) base p (K₁ + K₂) st =
      (do
        let st' ← simLoopDet (regCells := regCells) (wCell := wCell) base p K₁ st
        simLoopDet (regCells := regCells) (wCell := wCell) base p K₂ st') := by
  induction K₁ generalizing st with
  | zero => simp [simLoopDet]
  | succ K₁ ih =>
    rw [Nat.succ_add]
    simp only [simLoopDet, bind_assoc, ih]

private theorem simLoopDet_halted {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) (K : ℕ) (out : ℕ) (regs : Fin r → ℕ)
    (wb : Fin S → Option (Fin (2 ^ w))) (ext : ℕ → ℕ) (m : Mem (S + regCells) wCell) :
    (simLoopDet (regCells := regCells) (wCell := wCell) base p K (.halted out regs wb ext)).run m =
      (.halted out regs wb ext, m) ∧
    (simLoopDet (regCells := regCells) (wCell := wCell) base p K (.halted out regs wb ext)).probes m
      = 0 := by
  induction K with
  | zero => exact ⟨rfl, rfl⟩
  | succ K ih =>
    simp only [simLoopDet, simStepDet, ProbeTree.run_bind, ProbeTree.run_pure,
      ProbeTree.probes_bind, ProbeTree.probes_pure, zero_add]
    exact ih

private theorem simLoopDet_of_runs {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) {s t : State r} {n : ℕ}
    (hruns : Runs w p s t n)
    {regs : Fin r → ℕ} {wb : Fin S → Option (Fin (2 ^ w))} {ext : ℕ → ℕ}
    (m : Mem (S + regCells) wCell)
    (hrec : reconstructData base m regs wb ext = s.data)
    (hs_bdd : s.data.Bounded w) :
    ∃ wb' ext',
      (simLoopDet (regCells := regCells) (wCell := wCell)
        base p n (.running s.pc regs wb ext)).run m =
          (.running t.pc t.data.regs wb' ext', m) ∧
      reconstructData base m t.data.regs wb' ext' = t.data ∧
      (simLoopDet (regCells := regCells) (wCell := wCell)
        base p n (.running s.pc regs wb ext)).probes m + dirtyCount wb' ≤
          n + dirtyCount wb := by
  induction hruns with
  | refl =>
    have hregs : regs = s.data.regs := congrArg Data.regs hrec
    subst hregs
    exact ⟨wb, ext, rfl, hrec, by simp [simLoopDet]⟩
  | tail u v_st n' hpref hstep ih =>
    obtain ⟨wb₁, ext₁, hrun_pref, hrec₁, hpr_pref⟩ := ih
    have hu_bdd : u.data.Bounded w := Runs.bounded hpref hs_bdd
    have hbdd₁ : (reconstructData base m u.data.regs wb₁ ext₁).Bounded w := hrec₁ ▸ hu_bdd
    have hspec := simStepDet_spec (regCells := regCells) (wCell := wCell) base p u.pc m hbdd₁
    dsimp only at hspec
    have hstep_u : step w p u = .next v_st := hstep
    rw [hrec₁, hstep_u] at hspec
    obtain ⟨hm_eq, wb', ext', hrun1, hrec', hpr1⟩ := hspec
    have hstep_run :
        (simStepDet (regCells := regCells) (wCell := wCell) base p
          (.running u.pc u.data.regs wb₁ ext₁)).run m =
            (.running v_st.pc v_st.data.regs wb' ext', m) :=
      Prod.ext hrun1 hm_eq
    refine ⟨wb', ext', ?_, hrec', ?_⟩
    · rw [simLoopDet_add base p n' 1]
      simp only [ProbeTree.run_bind, hrun_pref, simLoopDet, hstep_run, ProbeTree.run_pure]
    · rw [simLoopDet_add base p n' 1]
      simp only [ProbeTree.probes_bind, hrun_pref, simLoopDet, hstep_run, ProbeTree.probes_pure,
        add_zero]
      omega

private theorem simLoopDet_of_runs_halt {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) {s t : State r} {n v K : ℕ}
    (hruns : Runs w p s t n) (hhalt : step w p t = .halt v) (hK : n + 1 ≤ K)
    {regs : Fin r → ℕ} {wb : Fin S → Option (Fin (2 ^ w))} {ext : ℕ → ℕ}
    (m : Mem (S + regCells) wCell)
    (hrec : reconstructData base m regs wb ext = s.data)
    (hs_bdd : s.data.Bounded w) :
    ∃ wb' ext',
      (simLoopDet (regCells := regCells) (wCell := wCell)
        base p K (.running s.pc regs wb ext)).run m =
          (.halted v t.data.regs wb' ext', m) ∧
      reconstructData base m t.data.regs wb' ext' = t.data ∧
      (simLoopDet (regCells := regCells) (wCell := wCell)
        base p K (.running s.pc regs wb ext)).probes m + dirtyCount wb' ≤
          n + dirtyCount wb := by
  obtain ⟨wb₁, ext₁, hrun_pref, hrec₁, hpr_pref⟩ :=
    simLoopDet_of_runs (regCells := regCells) (wCell := wCell) base p hruns m hrec hs_bdd
  have ht_bdd : t.data.Bounded w := hruns.bounded hs_bdd
  have hbdd₁ : (reconstructData base m t.data.regs wb₁ ext₁).Bounded w := hrec₁ ▸ ht_bdd
  have hspec := simStepDet_spec (regCells := regCells) (wCell := wCell) base p t.pc m hbdd₁
  dsimp only at hspec
  rw [hrec₁, hhalt] at hspec
  obtain ⟨hm_eq, hrun1, hpr1⟩ := hspec
  have hstep_run :
      (simStepDet (regCells := regCells) (wCell := wCell) base p
        (.running t.pc t.data.regs wb₁ ext₁)).run m = (.halted v t.data.regs wb₁ ext₁, m) :=
    Prod.ext hrun1 hm_eq
  have hK_split : K = n + (1 + (K - (n + 1))) := by omega
  obtain ⟨hrem_run, hrem_pr⟩ :=
    simLoopDet_halted (regCells := regCells) (wCell := wCell) base p (K - (n + 1)) v
      t.data.regs wb₁ ext₁ m
  refine ⟨wb₁, ext₁, ?_, hrec₁, ?_⟩
  · rw [hK_split, simLoopDet_add base p n (1 + (K - (n + 1)))]
    simp only [ProbeTree.run_bind, hrun_pref]
    rw [Nat.add_comm 1, simLoopDet]
    simp only [ProbeTree.run_bind, hstep_run, hrem_run]
  · rw [hK_split, simLoopDet_add base p n (1 + (K - (n + 1)))]
    simp only [ProbeTree.probes_bind, hrun_pref]
    rw [Nat.add_comm 1, simLoopDet]
    simp only [ProbeTree.probes_bind, hpr1, hstep_run, hrem_pr]
    omega

theorem nextMem_writeFin_id {cells wCell : ℕ} (vals m : Mem cells wCell) :
    ((writeFin (fun i : Fin cells => i) vals).run m).2 = vals := by
  funext j
  exact nextMem_writeFin_apply (fun _ _ h => h) vals m j

/-! #### Deterministic flat-program and structured `ExecWithin` entrypoints -/

/-- Clocked deterministic `ProbeTree` simulator for a flat `WordRAM.Program B r`: reloads
persistent registers according to `L`, runs `K` buffered steps of `p` from `pc = 0`, and on clean
halt flushes modified data cells and spills persistent registers. -/
def simProgDet {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ) :
    ProbeTree (S + regCells) wCell Out := do
  let regs₀ ← L.reload argRegs
  let out ← simLoopDet base p K (.running 0 regs₀ (fun _ => none) (fun _ => 0))
  match out with
  | .halted v regs' writeBuf' _ =>
    let _ ← commitHalted L regs' writeBuf'
    pure ((decode v regs').getD defaultAns)
  | _ => pure defaultAns

/-- Any halting run of `p` from `⟨0, L.unpack argRegs m⟩` with `n` continuing steps (`n + 1 ≤ K`)
is simulated identically by `simProgDet` in at most `n + L.overhead` cell probes, leaving
`L.pack t.data` in memory. -/
theorem simProgDet_spec {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out)
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {t : State r} {n v K : ℕ}
    (hruns : Runs w p ⟨0, L.unpack argRegs m⟩ t n)
    (hhalt : step w p t = .halt v) (hK : n + 1 ≤ K) :
    (simProgDet L p argRegs decode defaultAns K).run m =
        ((decode v t.data.regs).getD defaultAns, L.pack t.data) ∧
      (simProgDet L p argRegs decode defaultAns K).probes m ≤ n + L.overhead := by
  have hx₀_bdd : (L.unpack argRegs m).Bounded w := L.unpack_bounded harg m
  have hrec₀ :
      reconstructData (w := w) base m (L.unpack argRegs m).regs (fun _ => none) (fun _ => 0) =
        L.unpack argRegs m :=
    reconstructData_init L argRegs m
  obtain ⟨wb', ext', hloop_run, hrec', hloop_pr⟩ :=
    simLoopDet_of_runs_halt (regCells := regCells) (wCell := wCell) base p hruns hhalt hK m
      hrec₀ hx₀_bdd
  dsimp only at hloop_run hloop_pr
  have hdirty0 : dirtyCount (fun _ : Fin S => (none : Option (Fin (2 ^ w)))) = 0 :=
    dirtyCount_empty S w
  obtain ⟨hcommit_mem, hcommit_pr⟩ := commitHalted_spec L hm t.data.regs wb' ext'
  rw [hrec'] at hcommit_mem
  refine ⟨?_, ?_⟩
  · simp only [simProgDet, ProbeTree.run_bind, L.run_reload, hloop_run, ProbeTree.run_pure]
    exact Prod.ext rfl hcommit_mem
  · simp only [simProgDet, ProbeTree.probes_bind, L.probes_reload, L.run_reload, hloop_run,
      hcommit_pr, ProbeTree.probes_pure, add_zero, RegLayout.overhead]
    omega

/-- Clocked deterministic `ProbeTree` initializer simulator: starts from externally supplied
initial registers `initRegs` (`0` reload probes), runs `K` buffered steps of `p` on zeroed cell
memory, and on clean halt flushes modified data cells and spills persistent registers in
`L.spillProbes` probes. -/
def simProgInitDet {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (initRegs : Fin r → ℕ) (K : ℕ) :
    ProbeTree (S + regCells) wCell PUnit := do
  let out ← simLoopDet base p K (.running 0 initRegs (fun _ => none) (fun _ => 0))
  match out with
  | .halted _ regs' writeBuf' _ => commitHalted L regs' writeBuf'
  | _ => pure PUnit.unit

/-- Starting from zeroed cell memory `fun _ => 0` (when `hm₀ : L.ValidMem (fun _ => 0)`), any
halting run of `p` from `⟨0, { regs := initRegs, mem := fun _ => 0 }⟩` in `n` continuing steps
(`n + 1 ≤ K`) is simulated by `simProgInitDet` in at most `n + L.spillProbes` cell probes, leaving
`L.pack t.data` in memory. -/
theorem simProgInitDet_spec {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (initRegs : Fin r → ℕ)
    (hm₀ : L.ValidMem (fun _ => 0))
    (hregs : ∀ i, Fits w (initRegs i))
    {t : State r} {n v K : ℕ}
    (hruns : Runs w p ⟨0, { regs := initRegs, mem := fun _ => 0 }⟩ t n)
    (hhalt : step w p t = .halt v) (hK : n + 1 ≤ K) :
    (simProgInitDet L p initRegs K).run (fun _ => 0) = (PUnit.unit, L.pack t.data) ∧
      (simProgInitDet L p initRegs K).probes (fun _ => 0) ≤ n + L.spillProbes := by
  set m₀ : Mem (S + regCells) wCell := fun _ => 0
  have hx₀_bdd : ({ regs := initRegs, mem := fun _ => 0 } : Data r).Bounded w :=
    ⟨hregs, fun _ => fits_zero w⟩
  have hrec₀ :
      reconstructData (w := w) base m₀ initRegs (fun _ => none) (fun _ => 0) =
        { regs := initRegs, mem := fun _ => 0 } := by
    ext i
    · rfl
    · simp only [reconstructData, m₀, Fin.val_zero, Nat.zero_mod]
      split_ifs <;> rfl
  obtain ⟨wb', ext', hloop_run, hrec', hloop_pr⟩ :=
    simLoopDet_of_runs_halt (regCells := regCells) (wCell := wCell) base p hruns hhalt hK m₀
      hrec₀ hx₀_bdd
  dsimp only at hloop_run hloop_pr
  have hdirty0 : dirtyCount (fun _ : Fin S => (none : Option (Fin (2 ^ w)))) = 0 :=
    dirtyCount_empty S w
  obtain ⟨hcommit_mem, hcommit_pr⟩ := commitHalted_spec L hm₀ t.data.regs wb' ext'
  rw [hrec'] at hcommit_mem
  refine ⟨?_, ?_⟩
  · simp only [simProgInitDet, ProbeTree.run_bind, hloop_run]
    exact Prod.ext rfl hcommit_mem
  · simp only [simProgInitDet, ProbeTree.probes_bind, hloop_run, hcommit_pr]
    omega

/-- Exact halting step count of `p` from `⟨0, L.unpack argRegs m⟩` when a halting run exists, or
`0` otherwise. -/
noncomputable def haltFuel {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ) (m : Mem (S + regCells) wCell) : ℕ :=
  letI := Classical.propDecidable
  if h : ∃ n, ∃ v, Executes w p ⟨0, L.unpack argRegs m⟩ v n then Classical.choose h else 0

/-- Uniform fuel across all `m : Mem (S + regCells) wCell` on which `p` halts. -/
noncomputable def autoFuel {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ) : ℕ :=
  Finset.univ.sup (haltFuel L p argRegs)

theorem le_autoFuel_of_runs_halt {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    {p : Program B r} {argRegs : Fin r → ℕ} {m : Mem (S + regCells) wCell}
    {t : State r} {n v : ℕ}
    (hruns : Runs w p ⟨0, L.unpack argRegs m⟩ t n) (hhalt : step w p t = .halt v) :
    n + 1 ≤ autoFuel L p argRegs := by
  have hex : Executes w p ⟨0, L.unpack argRegs m⟩ v (n + 1) := ⟨t, n, hruns, hhalt, rfl⟩
  have hmem : ∃ n', ∃ v', Executes w p ⟨0, L.unpack argRegs m⟩ v' n' := ⟨n + 1, v, hex⟩
  have heq : haltFuel L p argRegs m = n + 1 := by
    dsimp only [haltFuel]
    split_ifs
    obtain ⟨v', hex'⟩ := Classical.choose_spec hmem
    exact (hex'.unique hex).2
  rw [← heq]
  exact Finset.le_sup (f := haltFuel L p argRegs) (Finset.mem_univ m)

/-- Automatic-fuel deterministic `ProbeTree` simulator: chooses fuel uniformly over the finite
memory space `Mem (S + regCells) wCell` so callers need not supply an external step bound `K`. -/
noncomputable def simProgDetAuto {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) :
    ProbeTree (S + regCells) wCell Out :=
  simProgDet L p argRegs decode defaultAns (autoFuel L p argRegs)

/-- Automatic-fuel simulation of any deterministic halting run of `p` in `≤ n + L.overhead` cell
probes (`≤ T_flat - 1 + L.overhead` when `Executes w p ⟨0, x₀⟩ v T_flat`). -/
theorem simProgDetAuto_spec {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out)
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {t : State r} {n v : ℕ}
    (hruns : Runs w p ⟨0, L.unpack argRegs m⟩ t n)
    (hhalt : step w p t = .halt v) :
    (simProgDetAuto L p argRegs decode defaultAns).run m =
        ((decode v t.data.regs).getD defaultAns, L.pack t.data) ∧
      (simProgDetAuto L p argRegs decode defaultAns).probes m ≤ n + L.overhead :=
  simProgDet_spec L p argRegs decode defaultAns hm harg hruns hhalt
    (le_autoFuel_of_runs_halt L hruns hhalt)

/-- Structured `ExecWithin` simulation in standard `w`-bit layout (`S + persCount input` cells of
width `w`): simulates `c` in at most `T + 2 * persCount input` probes (`≤ T` when
`persCount input = 0`). -/
theorem simExecWithin {B : Basis} {r S w : ℕ} {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (c : Code B r) (retReg : Fin r) (argRegs : Fin r → ℕ)
    (decode : (Fin r → ℕ) → Option Out) (defaultAns : Out)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    (m : Mem (S + persCount input) w) {y : Data r} {T : ℕ}
    (hexec : ExecWithin w c (unpackData input argRegs base S w m) y T) :
    let tree := simProgDetAuto (standardLayout input base S w) (c.program retReg) argRegs
      (fun _ regs => decode regs) defaultAns
    tree.run m = ((decode y.regs).getD defaultAns, packMem input base S w y) ∧
      tree.probes m ≤ T + 2 * persCount input := by
  intro tree
  obtain ⟨n, hn_le, hex⟩ := hexec
  have hruns : Runs w (c.program retReg) ⟨0, unpackData input argRegs base S w m⟩
      ⟨0 + c.size, y⟩ n :=
    hex.runs (pc := 0) (p := c.program retReg) (Program.Contains.self _).append_left
  have hhalt : step w (c.program retReg) ⟨0 + c.size, y⟩ = .halt (y.regs retReg) :=
    step_halt (by simp [Code.program])
  obtain ⟨hrun, hpr⟩ :=
    simProgDetAuto_spec (standardLayout input base S w) (c.program retReg) argRegs
      (fun _ regs => decode regs) defaultAns trivial harg hruns hhalt
  refine ⟨hrun, hpr.trans ?_⟩
  rw [standardLayout_overhead]
  omega

/-- Structured `ExecWithin` simulation in wide-cell single-spill layout (`S + 1` cells of width
`wideWidth input w`): simulates `c` in at most `T + (if persCount input = 0 then 0 else 2)` probes
(`≤ T + 2` regardless of `r`). -/
theorem simExecWithinWide {B : Basis} {r S w : ℕ} {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (c : Code B r) (retReg : Fin r) (argRegs : Fin r → ℕ)
    (decode : (Fin r → ℕ) → Option Out) (defaultAns : Out)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {m : Mem (S + 1) (wideWidth input w)}
    (hm : (wideLayout input base S w).ValidMem m) {y : Data r} {T : ℕ}
    (hexec : ExecWithin w c (unpackDataWide input argRegs base S w m) y T) :
    let tree := simProgDetAuto (wideLayout input base S w) (c.program retReg) argRegs
      (fun _ regs => decode regs) defaultAns
    tree.run m = ((decode y.regs).getD defaultAns, packMemWide input base S w y) ∧
      tree.probes m ≤ T + (if persCount input = 0 then 0 else 2) := by
  intro tree
  obtain ⟨n, hn_le, hex⟩ := hexec
  have hruns : Runs w (c.program retReg) ⟨0, unpackDataWide input argRegs base S w m⟩
      ⟨0 + c.size, y⟩ n :=
    hex.runs (pc := 0) (p := c.program retReg) (Program.Contains.self _).append_left
  have hhalt : step w (c.program retReg) ⟨0 + c.size, y⟩ = .halt (y.regs retReg) :=
    step_halt (by simp [Code.program])
  obtain ⟨hrun, hpr⟩ :=
    simProgDetAuto_spec (wideLayout input base S w) (c.program retReg) argRegs
      (fun _ regs => decode regs) defaultAns hm harg hruns hhalt
  refine ⟨hrun, hpr.trans ?_⟩
  rw [wideLayout_overhead]
  omega


/-! ### 4. Randomized (`ExecRand`) and unbounded Las Vegas (`ExecProgramDist` / `ExecCodeDist`)
simulation in `RandProbeTree` -/

/-- Project a buffered `SimOutcome` over base memory `m` to the corresponding `WordRAM.RandCfg r`.
-/
def SimOutcome.toRandCfg {r S regCells w wCell : ℕ} (base : ℕ)
    (m : Mem (S + regCells) wCell) : SimOutcome S w r → RandCfg r
  | .running pc regs wb ext => .running ⟨pc, reconstructData base m regs wb ext⟩
  | .halted out regs wb ext => .halted out (reconstructData base m regs wb ext)
  | .faulted => .faulted

/-- Number of buffered modified cells carried by a `SimOutcome`. -/
def SimOutcome.dirty {S w r : ℕ} : SimOutcome S w r → ℕ
  | .running _ _ wb _ => dirtyCount wb
  | .halted _ _ wb _ => dirtyCount wb
  | .faulted => 0

/-- Boolean predicate for active configurations not yet positioned at `Instr.halt` (the only
configurations on which `simStepRand` can increase `probes + dirty` by `1`). -/
def isContinuingCfg {B : Basis} {r : ℕ} (p : Program B r) : RandCfg r → Bool
  | .running s =>
    match p[s.pc]? with
    | some (.halt _) => false
    | _ => true
  | _ => false

/-- One step of buffered randomized flat-program simulation in `RandProbeTree`: maps `Instr.rand`
to `0`-probe `RandProbeTree.sample (ProbComp.unifFin ...)` and delegates all other instructions to
`RandProbeTree.ofProbeTree (simStepDet ...)`. -/
def simStepRand {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ) (p : Program B r) :
    SimOutcome S w r → RandProbeTree (S + regCells) wCell (SimOutcome S w r)
  | .running pc regs writeBuf extMem =>
    match p[pc]? with
    | some (.rand dst src) =>
      if Fits w (regs src) then do
        let k ← RandProbeTree.sample (ProbComp.unifFin (regs src))
        pure (.running (pc + 1) (Function.update regs dst k.val) writeBuf extMem)
      else
        pure .faulted
    | _ => RandProbeTree.ofProbeTree (simStepDet base p (.running pc regs writeBuf extMem))
  | st => pure st

private theorem stepRand_eq_ofOutcome_of_not_rand {B : Basis} {r w : ℕ} {p : Program B r}
    {s : State r} (h : ∀ dst src, p[s.pc]? ≠ some (.rand dst src)) :
    stepRand w p (.running s) = pure (.ofOutcome s.data (step w p s)) := by
  rcases hpc : p[s.pc]? with _ | (_ | _ | _ | _ | ⟨dst, src⟩)
  · simp only [stepRand, hpc]
  · simp only [stepRand, hpc]
  · simp only [stepRand, hpc]
  · simp only [stepRand, hpc]
  · simp only [stepRand, hpc]
  · exact absurd hpc (h dst src)

private theorem simStepRand_spec {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) (st : SimOutcome S w r) (m : Mem (S + regCells) wCell)
    (hcfg : (st.toRandCfg (w := w) base m).Bounded w) :
    let t := simStepRand (regCells := regCells) (w := w) (wCell := wCell) base p st
    (t.run m).map (fun z => z.1.1.toRandCfg base m) =
      (stepRand w p (st.toRandCfg base m)).eval ∧
    ∀ z ∈ (t.run m).support,
      z.1.2 = m ∧
      (z.1.1.toRandCfg (w := w) base m).Bounded w ∧
      z.2 + z.1.1.dirty ≤
        (if isContinuingCfg p (st.toRandCfg base m) then 1 else 0) + st.dirty := by
  intro t
  have hmain :
      (t.run m).map (fun z => z.1.1.toRandCfg base m) =
        (stepRand w p (st.toRandCfg base m)).eval ∧
      ∀ z ∈ (t.run m).support,
        z.1.2 = m ∧
        z.2 + z.1.1.dirty ≤
          (if isContinuingCfg p (st.toRandCfg base m) then 1 else 0) + st.dirty := by
    cases st with
    | halted out regs wb ext =>
      refine ⟨?_, ?_⟩
      · simp [t, simStepRand, SimOutcome.toRandCfg, stepRand_halted]
      · intro z hz
        simp only [t, simStepRand, RandProbeTree.run_pure, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨rfl, by simp [isContinuingCfg, SimOutcome.toRandCfg, SimOutcome.dirty]⟩
    | faulted =>
      refine ⟨?_, ?_⟩
      · simp [t, simStepRand, SimOutcome.toRandCfg, stepRand_faulted]
      · intro z hz
        simp only [t, simStepRand, RandProbeTree.run_pure, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨rfl, by simp [isContinuingCfg, SimOutcome.toRandCfg, SimOutcome.dirty]⟩
    | running pc regs wb ext =>
      set x := reconstructData (w := w) base m regs wb ext
      have hx : x.Bounded w := hcfg
      have hcfg_st :
          (SimOutcome.running pc regs wb ext).toRandCfg (w := w) base m = .running ⟨pc, x⟩ := rfl
      by_cases hrand : ∃ dst src, p[pc]? = some (.rand dst src)
      · obtain ⟨dst, src, hp⟩ := hrand
        have hcont : isContinuingCfg p (.running ⟨pc, x⟩) = true := by
          simp [isContinuingCfg, hp]
        by_cases hfit : Fits w (regs src)
        · have hfit' : Fits w (x.regs src) := hfit
          have hstep : stepRand w p (.running ⟨pc, x⟩) = (do
              let k ← ProbComp.unifFin (regs src)
              pure (.running ⟨pc + 1, x.set dst k.val⟩)) :=
            stepRand_rand_of_fits (s := ⟨pc, x⟩) hp hfit'
          have ht_eq : t = (do
              let k ← RandProbeTree.sample (ProbComp.unifFin (regs src))
              pure (.running (pc + 1) (Function.update regs dst k.val) wb ext)) := by
            simp [t, simStepRand, hp, hfit]
          refine ⟨?_, ?_⟩
          · dsimp only [SimOutcome.toRandCfg]
            rw [ht_eq, hstep, ProbComp.eval_bind]
            simp only [RandProbeTree.run_bind, RandProbeTree.run_sample, PMF.map_bind,
              PMF.bind_map, RandProbeTree.run_pure, PMF.pure_map, ProbComp.eval_pure,
              Function.comp_def, zero_add]
            refine congrArg (PMF.bind (ProbComp.unifFin (regs src)).eval) (funext fun k => ?_)
            exact congrArg PMF.pure (congrArg (RandCfg.running ∘ State.mk (pc + 1))
              (Data.ext rfl rfl))
          · intro z hz
            rw [ht_eq] at hz
            simp only [RandProbeTree.run_bind, RandProbeTree.run_sample, PMF.mem_support_bind_iff,
              PMF.mem_support_map_iff, RandProbeTree.run_pure, PMF.support_pure,
              Set.mem_singleton_iff] at hz
            obtain ⟨_, ⟨k, _, rfl⟩, _, rfl, rfl⟩ := hz
            refine ⟨rfl, ?_⟩
            rw [hcfg_st, hcont]
            simp [SimOutcome.dirty]
        · have hfit' : ¬Fits w (x.regs src) := hfit
          have hstep : stepRand w p (.running ⟨pc, x⟩) = pure .faulted :=
            stepRand_rand_of_not_fits (s := ⟨pc, x⟩) hp hfit'
          have ht_eq : t = pure .faulted := by simp [t, simStepRand, hp, hfit]
          refine ⟨?_, ?_⟩
          · dsimp only [SimOutcome.toRandCfg]
            rw [ht_eq, hstep]
            simp
          · intro z hz
            rw [ht_eq] at hz
            simp only [RandProbeTree.run_pure, PMF.support_pure, Set.mem_singleton_iff] at hz
            subst hz
            refine ⟨rfl, ?_⟩
            rw [hcfg_st, hcont]
            simp [SimOutcome.dirty]
      · have hnot_rand : ∀ dst src, p[pc]? ≠ some (.rand dst src) := fun dst src h =>
          hrand ⟨dst, src, h⟩
        have ht_eq :
            t = RandProbeTree.ofProbeTree (simStepDet base p (.running pc regs wb ext)) := by
          dsimp only [t, simStepRand]
          rcases hpc : p[pc]? with _ | (_ | _ | _ | _ | ⟨dst, src⟩)
          · rfl
          · rfl
          · rfl
          · rfl
          · rfl
          · exact absurd hpc (hnot_rand dst src)
        have hstep : stepRand w p (.running ⟨pc, x⟩) = pure (.ofOutcome x (step w p ⟨pc, x⟩)) :=
          stepRand_eq_ofOutcome_of_not_rand (s := ⟨pc, x⟩) hnot_rand
        have hdet := simStepDet_spec (regCells := regCells) (wCell := wCell) base p pc m hx
        dsimp only at hdet
        obtain ⟨hm_eq, hdet_out⟩ := hdet
        refine ⟨?_, ?_⟩
        · dsimp only [SimOutcome.toRandCfg]
          rw [ht_eq, RandProbeTree.run_ofProbeTree, PMF.pure_map, hstep, ProbComp.eval_pure]
          refine congrArg PMF.pure ?_
          cases hs_out : step w p ⟨pc, x⟩ with
          | next s' =>
            rw [hs_out] at hdet_out
            obtain ⟨wb', ext', hrun1, hrec', _⟩ := hdet_out
            rw [hrun1]
            simp [hrec', RandCfg.ofOutcome]
          | halt v =>
            rw [hs_out] at hdet_out
            rw [hdet_out.1]
            simp [RandCfg.ofOutcome, x]
          | fault =>
            rw [hs_out] at hdet_out
            rw [hdet_out.1]
            rfl
        · intro z hz
          rw [ht_eq, RandProbeTree.run_ofProbeTree, PMF.support_pure, Set.mem_singleton_iff] at hz
          subst hz
          refine ⟨hm_eq, ?_⟩
          cases hs_out : step w p ⟨pc, x⟩ with
          | next s' =>
            rw [hs_out] at hdet_out
            obtain ⟨wb', ext', hrun1, _, hpr1⟩ := hdet_out
            have hcont : isContinuingCfg p (.running ⟨pc, x⟩) = true := by
              dsimp only [isContinuingCfg]
              rcases hpc : p[pc]? with _ | (_ | _ | _ | i | _)
              · rfl
              · rfl
              · rfl
              · rfl
              · rw [step_halt (s := ⟨pc, x⟩) hpc] at hs_out
                cases hs_out
              · rfl
            rw [hcfg_st, hcont, hrun1]
            simpa [SimOutcome.dirty] using hpr1
          | halt v =>
            rw [hs_out] at hdet_out
            rw [hdet_out.1, hdet_out.2]
            simp [SimOutcome.dirty]
          | fault =>
            rw [hs_out] at hdet_out
            rw [hdet_out.1, hdet_out.2]
            have hcont : isContinuingCfg p (.running ⟨pc, x⟩) = true := by
              dsimp only [isContinuingCfg]
              rcases hpc : p[pc]? with _ | (_ | _ | _ | i | _)
              · rfl
              · rfl
              · rfl
              · rfl
              · rw [step_halt (s := ⟨pc, x⟩) hpc] at hs_out
                cases hs_out
              · rfl
            rw [hcfg_st, hcont]
            simp [SimOutcome.dirty]
  refine ⟨hmain.1, fun z hz => ?_⟩
  obtain ⟨hm_z, hpr_z⟩ := hmain.2 z hz
  have hmem_step : z.1.1.toRandCfg base m ∈ (stepRand w p (st.toRandCfg base m)).support := by
    rw [← ProbComp.support_eval, ← hmain.1, PMF.mem_support_map_iff]
    exact ⟨z, hz, rfl⟩
  exact ⟨hm_z, stepRand_bounded hcfg hmem_step, hpr_z⟩

/-- Clocked `K`-step buffered randomized execution in `RandProbeTree`. -/
def simLoopRand {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ) (p : Program B r) :
    ℕ → SimOutcome S w r → RandProbeTree (S + regCells) wCell (SimOutcome S w r)
  | 0, st => pure st
  | K + 1, st => do
      let st' ← simStepRand base p st
      simLoopRand base p K st'

private theorem simLoopRand_add {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) (K₁ K₂ : ℕ) (st : SimOutcome S w r) :
    simLoopRand (regCells := regCells) (wCell := wCell) base p (K₁ + K₂) st =
      (do
        let st' ← simLoopRand (regCells := regCells) (wCell := wCell) base p K₁ st
        simLoopRand (regCells := regCells) (wCell := wCell) base p K₂ st') := by
  induction K₁ generalizing st with
  | zero => simp [simLoopRand]
  | succ K₁ ih =>
    rw [Nat.succ_add]
    simp only [simLoopRand, bind_assoc, ih]

private theorem simStepRand_worstCase_probes {B : Basis} {r S regCells w wCell : ℕ}
    (base : ℕ) (p : Program B r) (st : SimOutcome S w r) (m : Mem (S + regCells) wCell) :
    ∀ z ∈ ((simStepRand (regCells := regCells) (w := w) (wCell := wCell) base p st).run m).support,
      z.1.2 = m ∧ z.2 ≤ 1 := by
  cases st with
  | halted =>
    intro z hz
    simp only [simStepRand, RandProbeTree.run_pure, PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, by omega⟩
  | faulted =>
    intro z hz
    simp only [simStepRand, RandProbeTree.run_pure, PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, by omega⟩
  | running pc regs wb ext =>
    intro z hz
    dsimp only [simStepRand] at hz
    rcases hp : p[pc]? with _ | instr
    · simp only [hp, RandProbeTree.run_ofProbeTree, simStepDet, ProbeTree.run_pure,
        ProbeTree.probes_pure, PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨rfl, by omega⟩
    · cases instr with
      | rand dst src =>
        simp only [hp] at hz
        by_cases hfit : Fits w (regs src)
        · simp only [hfit, ↓reduceIte, RandProbeTree.run_bind, RandProbeTree.run_sample,
            PMF.mem_support_bind_iff, PMF.mem_support_map_iff, RandProbeTree.run_pure,
            PMF.support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨_, ⟨_, _, rfl⟩, _, rfl, rfl⟩ := hz
          exact ⟨rfl, by omega⟩
        · simp only [hfit, ↓reduceIte, RandProbeTree.run_pure, PMF.support_pure,
            Set.mem_singleton_iff] at hz
          subst hz
          exact ⟨rfl, by omega⟩
      | op o =>
        simp only [hp, RandProbeTree.run_ofProbeTree, PMF.support_pure,
          Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨simStepDet_nextMem base p _ m, ?_⟩
        dsimp only [simStepDet]
        rw [hp]
        cases o with
        | const d v => dsimp only; by_cases hv : Fits w v <;> simp [hv]
        | copy d src => simp
        | alu f d args =>
          dsimp only
          cases B.interp w f (regs ∘ args) with
          | none => simp
          | some v => dsimp only; by_cases hv : Fits w v <;> simp [hv]
        | load d a =>
          dsimp only
          split_ifs with ha
          · cases writeBuf : wb ⟨regs a - base, by omega⟩ <;> simp
          · simp
        | store a src =>
          dsimp only
          split_ifs <;> simp
      | jump =>
        simp only [hp, RandProbeTree.run_ofProbeTree, simStepDet, ProbeTree.run_pure,
          ProbeTree.probes_pure, PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨rfl, by omega⟩
      | branch =>
        simp only [hp, RandProbeTree.run_ofProbeTree, simStepDet, ProbeTree.run_pure,
          ProbeTree.probes_pure, PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨rfl, by omega⟩
      | halt =>
        simp only [hp, RandProbeTree.run_ofProbeTree, simStepDet, ProbeTree.run_pure,
          ProbeTree.probes_pure, PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact ⟨rfl, by omega⟩

private theorem simLoopRand_worstCase_probes {B : Basis} {r S regCells w wCell : ℕ}
    (base : ℕ) (p : Program B r) (K : ℕ) (st : SimOutcome S w r) (m : Mem (S + regCells) wCell) :
    ∀ z ∈
      ((simLoopRand (regCells := regCells) (w := w) (wCell := wCell) base p K st).run m).support,
      z.1.2 = m ∧ z.2 ≤ K := by
  induction K generalizing st with
  | zero =>
    intro z hz
    simp only [simLoopRand, RandProbeTree.run_pure, PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, le_rfl⟩
  | succ K ih =>
    intro z hz
    simp only [simLoopRand, RandProbeTree.run_bind, PMF.mem_support_bind_iff,
      PMF.mem_support_map_iff] at hz
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hz
    obtain ⟨hm₁, hpr₁⟩ := simStepRand_worstCase_probes base p st m z₁ hz₁
    rw [hm₁] at hz₂
    obtain ⟨hm₂, hpr₂⟩ := ih z₁.1.1 z₂ hz₂
    exact ⟨hm₂, by omega⟩

private theorem simLoopRand_spec {B : Basis} {r S regCells w wCell : ℕ} (base : ℕ)
    (p : Program B r) (K : ℕ) (st : SimOutcome S w r) (m : Mem (S + regCells) wCell)
    (hcfg : (st.toRandCfg (w := w) base m).Bounded w) :
    let loop := simLoopRand (regCells := regCells) (w := w) (wCell := wCell) base p K st
    (loop.run m).map (fun z => z.1.1.toRandCfg base m) =
      (runRand w p K (st.toRandCfg base m)).eval ∧
    (∀ z ∈ (loop.run m).support,
      z.1.2 = m ∧
      (z.1.1.toRandCfg (w := w) base m).Bounded w ∧
      z.2 + z.1.1.dirty ≤ K + st.dirty) ∧
    (∑' z, (loop.run m) z * ((z.2 + z.1.1.dirty : ℕ) : ℝ≥0∞)) ≤
      (st.dirty : ℝ≥0∞) +
        ∑ t ∈ Finset.range K,
          (runRand w p t (st.toRandCfg base m)).eval.toOuterMeasure
            {cfg | isContinuingCfg p cfg = true} := by
  induction K with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simp [simLoopRand]
    · intro z hz
      simp only [simLoopRand, RandProbeTree.run_pure, PMF.support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨rfl, hcfg, by simp⟩
    · simp only [simLoopRand, RandProbeTree.run_pure, Finset.range_zero, Finset.sum_empty,
        add_zero]
      rw [tsum_eq_single ((st, m), 0) (fun z hz => by simp [PMF.pure_apply, hz])]
      simp
  | succ K ih =>
    obtain ⟨hmap_K, hsup_K, hexp_K⟩ := ih
    set loop_K := simLoopRand (regCells := regCells) (w := w) (wCell := wCell) base p K st
    have hsplit :
        simLoopRand (regCells := regCells) (w := w) (wCell := wCell) base p (K + 1) st =
          (loop_K >>= simStepRand base p) := by
      rw [simLoopRand_add base p K 1 st]
      refine congrArg (loop_K >>= ·) (funext fun st' => ?_)
      simp [simLoopRand]
    refine ⟨?_, ?_, ?_⟩
    · rw [hsplit, RandProbeTree.run_bind, PMF.map_bind, runRand_add w p K 1, ProbComp.eval_bind]
      have hbind_lhs :
          ((loop_K.run m).bind fun x =>
              PMF.map ((fun z => z.1.1.toRandCfg base m) ∘ fun y => (y.1, x.2 + y.2))
                ((simStepRand base p x.1.1).run x.1.2)) =
            (loop_K.run m).bind fun x =>
              (stepRand w p (x.1.1.toRandCfg base m)).eval := by
        refine PMF.bind_congr_on_support _ _ _ fun z₁ hz₁ => ?_
        obtain ⟨hm₁, hbdd₁, _⟩ := hsup_K z₁ hz₁
        rw [hm₁]
        have h1 := (simStepRand_spec base p z₁.1.1 m hbdd₁).1
        simpa [Function.comp_def] using h1
      change ((loop_K.run m).bind fun x =>
          PMF.map (fun z => z.1.1.toRandCfg base m)
            (((simStepRand base p x.1.1).run x.1.2).map fun y => (y.1, x.2 + y.2))) = _
      simp only [PMF.map_comp]
      rw [hbind_lhs, ← hmap_K, PMF.bind_map]
      refine congrArg (PMF.bind (loop_K.run m)) (funext fun z₁ => ?_)
      simp [runRand_succ, runRand_zero]
    · intro z hz
      rw [hsplit, RandProbeTree.run_bind, PMF.mem_support_bind_iff] at hz
      obtain ⟨z₁, hz₁, hz₂⟩ := hz
      rw [PMF.mem_support_map_iff] at hz₂
      obtain ⟨z₂, hz₂_mem, rfl⟩ := hz₂
      obtain ⟨hm₁, hbdd₁, hpr₁⟩ := hsup_K z₁ hz₁
      rw [hm₁] at hz₂_mem
      obtain ⟨hm₂, hbdd₂, hpr₂⟩ := (simStepRand_spec base p z₁.1.1 m hbdd₁).2 z₂ hz₂_mem
      refine ⟨hm₂, hbdd₂, ?_⟩
      dsimp only
      set d₁ := z₁.1.1.dirty
      set d₂ := z₂.1.1.dirty
      set d₀ := st.dirty
      by_cases hcont : isContinuingCfg p (z₁.1.1.toRandCfg base m) = true
      · simp only [hcont, ↓reduceIte] at hpr₂
        omega
      · simp only [hcont, Bool.false_eq_true, ↓reduceIte] at hpr₂
        omega
    · rw [hsplit, RandProbeTree.run_bind, Probability.PMF.tsum_bind_mul]
      have hstep_le : ∀ z₁,
          (loop_K.run m) z₁ *
              (∑' z, (((simStepRand base p z₁.1.1).run z₁.1.2).map
                (fun y => (y.1, z₁.2 + y.2))) z * ((z.2 + z.1.1.dirty : ℕ) : ℝ≥0∞)) ≤
            (loop_K.run m) z₁ * ((z₁.2 + z₁.1.1.dirty : ℕ) : ℝ≥0∞) +
              (loop_K.run m) z₁ *
                Set.indicator {cfg | isContinuingCfg p cfg = true} 1
                  (z₁.1.1.toRandCfg base m) := by
        intro z₁
        by_cases hz₁ : z₁ ∈ (loop_K.run m).support
        · obtain ⟨hm₁, hbdd₁, _⟩ := hsup_K z₁ hz₁
          rw [hm₁, Probability.PMF.tsum_map_mul, ← mul_add]
          refine mul_le_mul' le_rfl ?_
          set μ_s := (simStepRand (regCells := regCells) (w := w) (wCell := wCell)
            base p z₁.1.1).run m
          set inc : ℝ≥0∞ :=
            Set.indicator {cfg | isContinuingCfg p cfg = true} 1 (z₁.1.1.toRandCfg base m)
          have hpt : ∀ z₂,
              μ_s z₂ * ((z₁.2 + z₂.2 + z₂.1.1.dirty : ℕ) : ℝ≥0∞) ≤
                μ_s z₂ * (((z₁.2 + z₁.1.1.dirty : ℕ) : ℝ≥0∞) + inc) := by
            intro z₂
            by_cases hz₂ : z₂ ∈ μ_s.support
            · refine mul_le_mul' le_rfl ?_
              obtain ⟨_, _, hpr₂⟩ := (simStepRand_spec base p z₁.1.1 m hbdd₁).2 z₂ hz₂
              set d₁ := z₁.1.1.dirty
              set d₂ := z₂.1.1.dirty
              by_cases hc : isContinuingCfg p (z₁.1.1.toRandCfg base m) = true
              · simp only [hc, ↓reduceIte] at hpr₂
                have hinc : inc = 1 := Set.indicator_of_mem hc 1
                rw [hinc, ← Nat.cast_one, ← Nat.cast_add]
                exact (Nat.cast_le (α := ℝ≥0∞)).mpr (by omega)
              · simp only [hc, Bool.false_eq_true, ↓reduceIte, zero_add] at hpr₂
                have hinc : inc = 0 := Set.indicator_of_notMem hc 1
                rw [hinc, add_zero]
                exact (Nat.cast_le (α := ℝ≥0∞)).mpr (by omega)
            · rw [(PMF.apply_eq_zero_iff _ _).mpr hz₂, zero_mul, zero_mul]
          refine (tsum_le_tsum hpt).trans ?_
          rw [ENNReal.tsum_mul_right, μ_s.tsum_coe, one_mul]
        · rw [(PMF.apply_eq_zero_iff _ _).mpr hz₁, zero_mul, zero_mul, zero_mul, add_zero]
      refine (tsum_le_tsum hstep_le).trans ?_
      rw [tsum_add, Finset.sum_range_succ, ← add_assoc]
      refine add_le_add hexp_K (le_of_eq ?_)
      have hpush :
          (∑' z₁, (loop_K.run m) z₁ *
              Set.indicator {cfg | isContinuingCfg p cfg = true} 1 (z₁.1.1.toRandCfg base m)) =
            ∑' cfg, ((loop_K.run m).map (fun z => z.1.1.toRandCfg base m)) cfg *
              Set.indicator {cfg | isContinuingCfg p cfg = true} 1 cfg := by
        exact (Probability.PMF.tsum_map_mul (loop_K.run m) (fun z => z.1.1.toRandCfg base m)
          (Set.indicator {cfg | isContinuingCfg p cfg = true} 1)).symm
      rw [hpush, hmap_K, ← Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator]

/-! #### Exact telescoping of the `.halt` instruction step -/

private theorem stepRand_haltedSet_identity {B : Basis} {r w : ℕ} (p : Program B r)
    (cfg : RandCfg r) :
    Set.indicator {c | isContinuingCfg p c = true} (1 : RandCfg r → ℝ≥0∞) cfg +
        (stepRand w p cfg).eval.toOuterMeasure (RandCfg.haltedSet r) =
      Set.indicator (RandCfg.runningSet r) (1 : RandCfg r → ℝ≥0∞) cfg +
        Set.indicator (RandCfg.haltedSet r) (1 : RandCfg r → ℝ≥0∞) cfg := by
  cases cfg with
  | halted v d =>
    have hmem : RandCfg.halted v d ∈ RandCfg.haltedSet r := ⟨v, d, rfl⟩
    have hnot_run : RandCfg.halted v d ∉ RandCfg.runningSet r := by simp
    have hnot_cont : ¬isContinuingCfg p (.halted v d) = true := by simp [isContinuingCfg]
    rw [Set.indicator_of_notMem hnot_cont, Set.indicator_of_notMem hnot_run,
      Set.indicator_of_mem hmem]
    simp [stepRand_halted, PMF.toOuterMeasure_pure_apply, hmem]
  | faulted =>
    have hnot_h : (RandCfg.faulted : RandCfg r) ∉ RandCfg.haltedSet r := by simp
    have hnot_r : (RandCfg.faulted : RandCfg r) ∉ RandCfg.runningSet r := by simp
    have hnot_c : ¬isContinuingCfg p .faulted = true := by simp [isContinuingCfg]
    rw [Set.indicator_of_notMem hnot_c, Set.indicator_of_notMem hnot_r,
      Set.indicator_of_notMem hnot_h]
    simp [stepRand_faulted, PMF.toOuterMeasure_pure_apply, hnot_h]
  | running s =>
    have hmem_r : RandCfg.running s ∈ RandCfg.runningSet r := ⟨s, rfl⟩
    have hnot_h : RandCfg.running s ∉ RandCfg.haltedSet r := by simp
    rw [Set.indicator_of_mem hmem_r, Set.indicator_of_notMem hnot_h]
    by_cases hh : ∃ i, p[s.pc]? = some (.halt i)
    · obtain ⟨i, hp⟩ := hh
      have hnot_c : ¬isContinuingCfg p (.running s) = true := by simp [isContinuingCfg, hp]
      have hmem_next : RandCfg.halted (s.data.regs i) s.data ∈ RandCfg.haltedSet r := ⟨_, _, rfl⟩
      rw [Set.indicator_of_notMem hnot_c, stepRand_halt hp]
      simp [PMF.toOuterMeasure_pure_apply, hmem_next]
    · have hc : isContinuingCfg p (.running s) = true := by
        dsimp only [isContinuingCfg]
        rcases hp : p[s.pc]? with _ | (_ | _ | _ | i | _)
        · rfl
        · rfl
        · rfl
        · rfl
        · exact absurd ⟨i, hp⟩ hh
        · rfl
      have hzero : (stepRand w p (.running s)).eval.toOuterMeasure (RandCfg.haltedSet r) = 0 := by
        rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
        intro cfg' hmem_s hmem_halt
        rw [ProbComp.support_eval] at hmem_s
        obtain ⟨v, d, rfl⟩ := hmem_halt
        by_cases hrand : ∃ dst src, p[s.pc]? = some (.rand dst src)
        · obtain ⟨dst, src, hp⟩ := hrand
          by_cases hfit : Fits w (s.data.regs src)
          · rw [stepRand_rand_of_fits hp hfit] at hmem_s
            obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hmem_s
            cases OracleComp.eq_of_mem_supportWith_pure hk
          · rw [stepRand_rand_of_not_fits hp hfit] at hmem_s
            cases OracleComp.eq_of_mem_supportWith_pure hmem_s
        · rw [stepRand_eq_ofOutcome_of_not_rand fun dst src h => hrand ⟨dst, src, h⟩] at hmem_s
          have heq := OracleComp.eq_of_mem_supportWith_pure hmem_s
          cases hs_step : step w p s with
          | next _ => rw [hs_step] at heq; cases heq
          | fault => rw [hs_step] at heq; cases heq
          | halt v' =>
            rcases hp : p[s.pc]? with _ | (_ | _ | _ | i | _)
            · simp [step, hp] at hs_step
            · simp only [step, hp] at hs_step
              split at hs_step <;> cases hs_step
            · simp [step, hp] at hs_step
            · simp [step, hp] at hs_step
            · exact hh ⟨i, hp⟩
            · simp [step, hp] at hs_step
      rw [Set.indicator_of_mem hc, hzero]

theorem continuing_sum_add_halted_eq_running_sum {B : Basis} {r w : ℕ} (p : Program B r)
    (s₀ : State r) (K : ℕ) :
    (∑ t ∈ Finset.range K,
        (evalRand w p t s₀).toOuterMeasure {cfg | isContinuingCfg p cfg = true}) +
      (evalRand w p K s₀).toOuterMeasure (RandCfg.haltedSet r) =
      ∑ t ∈ Finset.range K, (evalRand w p t s₀).toOuterMeasure (RandCfg.runningSet r) := by
  induction K with
  | zero =>
    have hnot : RandCfg.running s₀ ∉ RandCfg.haltedSet r := by simp
    simp [evalRand, PMF.toOuterMeasure_pure_apply, hnot]
  | succ K ih =>
    have hstep_eval : evalRand w p (K + 1) s₀ =
        (evalRand w p K s₀).bind (fun cfg => (stepRand w p cfg).eval) := by
      rw [evalRand, runRand_add w p K 1, ProbComp.eval_bind]
      simp only [evalRand, runRand_succ, runRand_zero, bind_pure]
    have hstep_rel :
        (evalRand w p K s₀).toOuterMeasure {cfg | isContinuingCfg p cfg = true} +
          (evalRand w p (K + 1) s₀).toOuterMeasure (RandCfg.haltedSet r) =
        (evalRand w p K s₀).toOuterMeasure (RandCfg.runningSet r) +
          (evalRand w p K s₀).toOuterMeasure (RandCfg.haltedSet r) := by
      rw [hstep_eval, PMF.toOuterMeasure_bind_apply,
        Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator (evalRand w p K s₀)
          {cfg | isContinuingCfg p cfg = true},
        Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator (evalRand w p K s₀)
          (RandCfg.runningSet r),
        Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator (evalRand w p K s₀)
          (RandCfg.haltedSet r),
        ← tsum_add, ← tsum_add]
      refine tsum_congr fun cfg => ?_
      rw [← mul_add, ← mul_add, stepRand_haltedSet_identity (w := w) p cfg]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, add_assoc, hstep_rel,
      ← add_assoc, add_right_comm _ _ ((evalRand w p K s₀).toOuterMeasure (RandCfg.haltedSet r)),
      ih]

theorem continuing_sum_le_of_almostSurelyHalts {B : Basis} {r w : ℕ} {p : Program B r}
    {s₀ : State r} {T : ℝ≥0∞} (has : AlmostSurelyHalts w p s₀)
    (hexp : expectedTime w p s₀ ≤ T + 1) (K : ℕ) :
    (∑ t ∈ Finset.range K,
        (evalRand w p t s₀).toOuterMeasure {cfg | isContinuingCfg p cfg = true}) ≤ T := by
  set S_K := ∑ t ∈ Finset.range K,
    (evalRand w p t s₀).toOuterMeasure {cfg | isContinuingCfg p cfg = true}
  have hM : ∀ M : ℕ, S_K + (evalRand w p M s₀).toOuterMeasure (RandCfg.haltedSet r) ≤ T + 1 := by
    intro M
    let N := max K M
    have hSK_le : S_K ≤ ∑ t ∈ Finset.range N,
        (evalRand w p t s₀).toOuterMeasure {cfg | isContinuingCfg p cfg = true} :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_left K M))
    have hHM_le :
        (evalRand w p M s₀).toOuterMeasure (RandCfg.haltedSet r) ≤
          (evalRand w p N s₀).toOuterMeasure (RandCfg.haltedSet r) :=
      evalRand_haltedSet_mono w p s₀ (le_max_right K M)
    have hsum_le :
        (∑ t ∈ Finset.range N, (evalRand w p t s₀).toOuterMeasure (RandCfg.runningSet r)) ≤
          expectedTime w p s₀ :=
      sum_le_tsum (Finset.range N)
    exact (add_le_add hSK_le hHM_le).trans
      ((continuing_sum_add_halted_eq_running_sum p s₀ N).le.trans (hsum_le.trans hexp))
  have hiSup : S_K + 1 ≤ T + 1 := by
    have hsup_eq :
        S_K + (⨆ M : ℕ, (evalRand w p M s₀).toOuterMeasure (RandCfg.haltedSet r)) =
          ⨆ M : ℕ, (S_K + (evalRand w p M s₀).toOuterMeasure (RandCfg.haltedSet r)) := by
      rw [add_comm S_K, @ENNReal.iSup_add ℕ]
      exact iSup_congr fun M => add_comm _ S_K
    calc S_K + 1
      _ = S_K + ⨆ M : ℕ, (evalRand w p M s₀).toOuterMeasure (RandCfg.haltedSet r) := by
          rw [has.2]
      _ = ⨆ M : ℕ, (S_K + (evalRand w p M s₀).toOuterMeasure (RandCfg.haltedSet r)) := hsup_eq
      _ ≤ T + 1 := iSup_le hM
  exact (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp hiSup

/-! #### Halting-limit identification, `ExecProgramDist`, and zero-error fallback -/

/-- Supremum halting probability of `p` from `⟨0, x⟩` at `(vy.1, vy.2)`. -/
@[expose] noncomputable def haltedLim {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (x : Data r)
    (vy : ℕ × Data r) : ℝ≥0∞ :=
  ⨆ K : ℕ, evalRand w p K ⟨0, x⟩ (.halted vy.1 vy.2)

theorem evalRand_halted_mono {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (s : State r)
    (v : ℕ) (y : Data r) :
    Monotone fun K => evalRand w p K s (.halted v y) := by
  refine monotone_nat_of_le_succ fun K => ?_
  have hstep : evalRand w p (K + 1) s =
      (evalRand w p K s).bind (fun cfg => (stepRand w p cfg).eval) := by
    rw [evalRand, runRand_add w p K 1, ProbComp.eval_bind]
    simp only [evalRand, runRand_succ, runRand_zero, bind_pure]
  rw [hstep, PMF.bind_apply]
  refine le_trans ?_
    (le_tsum (fun cfg => (evalRand w p K s) cfg * (stepRand w p cfg).eval (.halted v y))
      (.halted v y))
  simp [stepRand_halted]

theorem tsum_haltedLim_le_one {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (x : Data r) :
    (∑' vy : ℕ × Data r, haltedLim w p x vy) ≤ 1 := by
  dsimp only [haltedLim]
  rw [ENNReal.tsum_iSup_of_monotone (f := fun K (vy : ℕ × Data r) =>
    evalRand w p K ⟨0, x⟩ (.halted vy.1 vy.2))
    (fun vy => evalRand_halted_mono w p ⟨0, x⟩ vy.1 vy.2)]
  refine iSup_le fun K => ?_
  have hinj : Function.Injective (fun vy : ℕ × Data r => RandCfg.halted vy.1 vy.2) := by
    rintro ⟨v₁, y₁⟩ ⟨v₂, y₂⟩ h
    cases h
    rfl
  refine (tsum_comp_le_tsum_of_injective hinj (evalRand w p K ⟨0, x⟩)).trans ?_
  rw [(evalRand w p K ⟨0, x⟩).tsum_coe]

/-- Distributional execution contract for a flat `WordRAM.Program B r`: from `⟨0, x⟩`, `p` never
faults, has expected instruction count at most `T`, and dominates `μ : PMF (ℕ × Data r)` at its
supremum halting probabilities. Because `∑' vy, μ vy = 1` and `∑' vy, haltedLim w p x vy ≤ 1`,
domination forces exact equality `haltedLim w p x vy = μ vy` (`ExecProgramDist.haltedLim_eq`) and
almost-sure halting (`ExecProgramDist.almostSurelyHalts`). -/
@[expose] def ExecProgramDist {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (x : Data r)
    (μ : PMF (ℕ × Data r)) (T : ℝ≥0∞) : Prop :=
  expectedTime w p ⟨0, x⟩ ≤ T ∧
  RandFaultFree w p ⟨0, x⟩ ∧
  ∀ vy : ℕ × Data r, μ vy ≤ haltedLim w p x vy

namespace ExecProgramDist

variable {B : Basis} {r w : ℕ} {p : Program B r} {x : Data r} {μ : PMF (ℕ × Data r)} {T : ℝ≥0∞}

theorem haltedLim_eq (h : ExecProgramDist w p x μ T) (vy : ℕ × Data r) :
    haltedLim w p x vy = μ vy := by
  refine le_antisymm ?_ (h.2.2 vy)
  by_contra hnot
  have hlt : μ vy < haltedLim w p x vy := lt_of_not_ge hnot
  have hsum_μ := (μ.tsum_coe).symm.trans (tsum_eq_add_tsum_ite (f := fun z => μ z) vy)
  have hsum_lim := (tsum_eq_add_tsum_ite (f := haltedLim w p x) vy).symm.trans_le
    (tsum_haltedLim_le_one w p x)
  have hrest_ne_top :
      (∑' z : ℕ × Data r, @ite ℝ≥0∞ (z = vy) (Classical.propDecidable _) 0 (μ z)) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hsum_μ
    exact ENNReal.one_ne_top hsum_μ
  refine lt_irrefl (1 : ℝ≥0∞)
    ((hsum_μ.trans_lt (ENNReal.add_lt_add_of_lt_of_le hrest_ne_top hlt
      (tsum_le_tsum fun z => ?_))).trans_le hsum_lim)
  split_ifs
  · exact le_rfl
  · exact h.2.2 z

theorem evalRand_halted_le (h : ExecProgramDist w p x μ T) (K : ℕ) (vy : ℕ × Data r) :
    evalRand w p K ⟨0, x⟩ (.halted vy.1 vy.2) ≤ μ vy := by
  rw [← h.haltedLim_eq vy]
  exact le_iSup (fun k => evalRand w p k ⟨0, x⟩ (.halted vy.1 vy.2)) K

theorem almostSurelyHalts (h : ExecProgramDist w p x μ T) :
    AlmostSurelyHalts w p ⟨0, x⟩ := by
  refine ⟨h.2.1, le_antisymm
    (iSup_le fun _ => Probability.PMF.toOuterMeasure_le_one _ _) ?_⟩
  have h1 : (1 : ℝ≥0∞) = ∑' vy : ℕ × Data r, haltedLim w p x vy := by
    simp_rw [h.haltedLim_eq]
    exact μ.tsum_coe.symm
  rw [h1]
  dsimp only [haltedLim]
  rw [ENNReal.tsum_iSup_of_monotone (f := fun K (vy : ℕ × Data r) =>
    evalRand w p K ⟨0, x⟩ (.halted vy.1 vy.2))
    (fun vy => evalRand_halted_mono w p ⟨0, x⟩ vy.1 vy.2)]
  refine iSup_mono fun K => ?_
  rw [PMF.toOuterMeasure_apply]
  have hinj : Function.Injective (fun vy : ℕ × Data r => RandCfg.halted vy.1 vy.2) := by
    rintro ⟨v₁, y₁⟩ ⟨v₂, y₂⟩ heq
    cases heq
    rfl
  refine (tsum_le_tsum fun vy => ?_).trans
    (tsum_comp_le_tsum_of_injective hinj
      (Set.indicator (RandCfg.haltedSet r) (evalRand w p K ⟨0, x⟩)))
  have hmem : RandCfg.halted vy.1 vy.2 ∈ RandCfg.haltedSet r := ⟨vy.1, vy.2, rfl⟩
  rw [Set.indicator_of_mem hmem]

end ExecProgramDist

/-- Lift a structured `ExecCodeDist w c x μ T` certificate to `ExecProgramDist` on `c.program out`.
-/
theorem execProgramDist_of_execCodeDist {B : Basis} {r w : ℕ} {c : Code B r} {x : Data r}
    {μ : PMF (Data r)} {T : ℝ≥0∞} (h : ExecCodeDist w c x μ T) (out : Fin r) :
    ExecProgramDist w (c.program out) x (μ.map fun y => (y.regs out, y)) (T + 1) := by
  obtain ⟨hexp, hff, _, hdom⟩ := h.program_halts out
  refine ⟨hexp, hff, fun ⟨v, y⟩ => ?_⟩
  classical
  rw [PMF.map_apply]
  by_cases hv : v = y.regs out
  · subst hv
    rw [tsum_eq_single y]
    · simp only [↓reduceIte]
      exact hdom y
    · intro z hzy
      split_ifs with heq
      · exact absurd ((Prod.mk.injEq _ _ _ _).mp heq).2.symm hzy
      · rfl
  · refine le_trans (le_of_eq ?_) zero_le
    rw [tsum_eq_zero_iff]
    intro a
    split_ifs with heq
    · obtain ⟨hv_eq, hy_eq⟩ := (Prod.mk.injEq _ _ _ _).mp heq
      subst hy_eq
      exact absurd hv_eq hv
    · rfl

/-- Pure-Lean fallback halting outcome for `p` from `⟨0, x⟩`: selects a reachable `(v, y)` with
positive halting limit `0 < haltedLim w p x (v, y)` when one exists, or `(0, x)` otherwise. -/
noncomputable def fallbackOutcome {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (x : Data r) :
    ℕ × Data r :=
  letI := Classical.propDecidable
  if h : ∃ vy : ℕ × Data r, 0 < haltedLim w p x vy then Classical.choose h else (0, x)

theorem fallbackOutcome_mem_support {B : Basis} {r w : ℕ} {p : Program B r} {x : Data r}
    {μ : PMF (ℕ × Data r)} {T : ℝ≥0∞} (h : ExecProgramDist w p x μ T) :
    fallbackOutcome w p x ∈ μ.support := by
  obtain ⟨vy₀, hvy₀⟩ := μ.support_nonempty
  have hex : ∃ vy : ℕ × Data r, 0 < haltedLim w p x vy := by
    refine ⟨vy₀, ?_⟩
    rw [h.haltedLim_eq vy₀]
    exact pos_iff_ne_zero.mpr ((PMF.mem_support_iff _ _).mp hvy₀)
  dsimp only [fallbackOutcome]
  split_ifs
  have hpos : 0 < haltedLim w p x (Classical.choose hex) := Classical.choose_spec hex
  rw [h.haltedLim_eq] at hpos
  exact (PMF.mem_support_iff _ _).mpr (ne_of_gt hpos)

/-- Buffered finite-horizon `RandProbeTree` simulator for a flat `WordRAM.Program B r`:
1. Reloads persistent registers via `L.reload argRegs` (`regs₀ = (L.unpack argRegs m).regs`).
2. Runs `K` buffered steps via `simLoopRand` without mutating cell memory `m`.
3. On `.halted v regs' writeBuf' _`, flushes `writeBuf'` and spills persistent registers via
   `commitHalted`.
4. On the `> K` tail (`.running`), reads the `S` untouched data cells of `m`, reconstructs
   `x₀ = L.unpack argRegs m` in pure Lean, selects `vy = fallbackOutcome w p x₀` (`∈ μ.support`!),
   and writes `L.pack vy.2` (`2 * S + regCells` probes on the tail), preserving **100% zero-error
   support correctness** at finite tree depth. -/
noncomputable def simProgRand {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ) :
    RandProbeTree (S + regCells) wCell Out := do
  let regs₀ ← RandProbeTree.ofProbeTree (L.reload argRegs)
  let out ← simLoopRand base p K (.running 0 regs₀ (fun _ => none) (fun _ => 0))
  match out with
  | .halted v regs' writeBuf' _ =>
    let _ ← RandProbeTree.ofProbeTree (commitHalted L regs' writeBuf')
    pure ((decode v regs').getD defaultAns)
  | _ =>
    let dataVals ← RandProbeTree.ofProbeTree
      (readFin (fun j : Fin S => Fin.castAdd regCells j))
    let x₀ : Data r :=
      { regs := regs₀
        mem := fun a =>
          if ha : base ≤ a ∧ a < base + S then
            (dataVals ⟨a - base, by omega⟩).1 % 2 ^ w
          else 0 }
    let vy := fallbackOutcome w p x₀
    let _ ← RandProbeTree.ofProbeTree (writeFin (fun c => c) (L.pack vy.2))
    pure ((decode vy.1 vy.2.regs).getD defaultAns)

/-- Post-loop completion step of `simProgRand`, factored for clean expectation analysis. -/
private noncomputable def finishSimProgRand {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (regs₀ : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) :
    SimOutcome S w r → RandProbeTree (S + regCells) wCell Out
  | .halted v regs' writeBuf' _ => do
      let _ ← RandProbeTree.ofProbeTree (commitHalted L regs' writeBuf')
      pure ((decode v regs').getD defaultAns)
  | _ => do
      let dataVals ← RandProbeTree.ofProbeTree
        (readFin (fun j : Fin S => Fin.castAdd regCells j))
      let x₀ : Data r :=
        { regs := regs₀
          mem := fun a =>
            if ha : base ≤ a ∧ a < base + S then
              (dataVals ⟨a - base, by omega⟩).1 % 2 ^ w
            else 0 }
      let vy := fallbackOutcome w p x₀
      let _ ← RandProbeTree.ofProbeTree (writeFin (fun c => c) (L.pack vy.2))
      pure ((decode vy.1 vy.2.regs).getD defaultAns)

private theorem simProgRand_eq_bind {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ) :
    simProgRand (w := w) L p argRegs decode defaultAns K = (do
      let regs₀ ← RandProbeTree.ofProbeTree (L.reload argRegs)
      let out ← simLoopRand base p K (.running 0 regs₀ (fun _ => none) (fun _ => 0))
      finishSimProgRand (w := w) L p regs₀ decode defaultAns out) := by
  refine congrArg (RandProbeTree.ofProbeTree (L.reload argRegs) >>= ·) (funext fun regs₀ => ?_)
  refine congrArg (simLoopRand base p K (.running 0 regs₀ (fun _ => none) (fun _ => 0)) >>= ·)
    (funext fun out => ?_)
  cases out <;> rfl

private theorem finishSimProgRand_fallback_run {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out)
    (m : Mem (S + regCells) wCell) (out : SimOutcome S w r)
    (hnot_halt : ∀ v regs' wb' ext', out ≠ .halted v regs' wb' ext') :
    (finishSimProgRand (w := w) L p (L.unpack argRegs m).regs decode defaultAns out).run m =
      PMF.pure
        (((decode (fallbackOutcome w p (L.unpack argRegs m)).1
            (fallbackOutcome w p (L.unpack argRegs m)).2.regs).getD defaultAns,
          L.pack (fallbackOutcome w p (L.unpack argRegs m)).2),
         2 * S + regCells) := by
  set x₀ := L.unpack argRegs m
  have hx₀_eq :
      ({ regs := x₀.regs
         mem := fun a =>
           if ha : base ≤ a ∧ a < base + S then
             (m (Fin.castAdd regCells ⟨a - base, by omega⟩)).1 % 2 ^ w
           else 0 } : Data r) = x₀ := by
    refine Data.ext rfl (funext fun a => ?_)
    exact (L.unpack_mem argRegs m a).symm
  cases out with
  | halted v regs' wb' ext' => exact absurd rfl (hnot_halt v regs' wb' ext')
  | running _ _ _ _ | faulted =>
    dsimp only [finishSimProgRand]
    simp only [RandProbeTree.run_bind, RandProbeTree.run_ofProbeTree, PMF.pure_bind,
      run_readFin, probes_readFin, RandProbeTree.run_pure, PMF.pure_map, add_zero,
      probes_writeFin, nextMem_writeFin_id]
    rw [hx₀_eq]
    exact congrArg PMF.pure (Prod.ext rfl (by omega))

/-- Unconditional worst-case probe bound for `simProgRand` on **any** memory `m`: every path issues
at most `K + 2 * S + regCells + L.overhead` cell probes. -/
theorem simProgRand_worstCase_probes {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ)
    (m : Mem (S + regCells) wCell) :
    ∀ z ∈ ((simProgRand (w := w) L p argRegs decode defaultAns K).run m).support,
      z.2 ≤ K + 2 * S + regCells + L.overhead := by
  intro z hz
  rw [simProgRand_eq_bind] at hz
  simp only [RandProbeTree.run_bind, RandProbeTree.run_ofProbeTree, L.run_reload,
    L.probes_reload, PMF.pure_bind, PMF.mem_support_map_iff, PMF.mem_support_bind_iff] at hz
  obtain ⟨z_mid, ⟨z_loop, hz_loop, z_fin, hz_fin, rfl⟩, rfl⟩ := hz
  obtain ⟨hm_loop, hpr_loop⟩ := simLoopRand_worstCase_probes base p K _ m z_loop hz_loop
  rw [hm_loop] at hz_fin
  cases hout : z_loop.1.1 with
  | halted v regs' wb' ext' =>
    rw [hout] at hz_fin
    simp only [finishSimProgRand, RandProbeTree.run_bind, RandProbeTree.run_ofProbeTree,
      PMF.pure_bind, RandProbeTree.run_pure, PMF.pure_map, add_zero, PMF.support_pure,
      Set.mem_singleton_iff] at hz_fin
    subst hz_fin
    have hdirty_le : dirtyCount wb' ≤ S := by
      simpa [dirtyCount] using Finset.card_filter_le (Finset.univ : Finset (Fin S)) _
    have hcom_pr : (commitHalted L regs' wb').probes m = dirtyCount wb' + L.spillProbes := by
      simp [commitHalted, ProbeTree.probes_bind, probes_flushWriteBuf, L.probes_spill]
    rw [hcom_pr]
    have hov : L.overhead = L.reloadProbes + L.spillProbes := rfl
    omega
  | running _ _ _ _ =>
    rw [hout, finishSimProgRand_fallback_run L p argRegs decode defaultAns m _ (by simp),
      PMF.support_pure, Set.mem_singleton_iff] at hz_fin
    subst hz_fin
    have hov : L.overhead = L.reloadProbes + L.spillProbes := rfl
    omega
  | faulted =>
    rw [hout, finishSimProgRand_fallback_run L p argRegs decode defaultAns m _ (by simp),
      PMF.support_pure, Set.mem_singleton_iff] at hz_fin
    subst hz_fin
    have hov : L.overhead = L.reloadProbes + L.spillProbes := rfl
    omega

theorem simProgRand_expectedProbes_le_worstCase {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ)
    (m : Mem (S + regCells) wCell) :
    (simProgRand (w := w) L p argRegs decode defaultAns K).expectedProbes m ≤
      ((K + 2 * S + regCells + L.overhead : ℕ) : ℝ≥0∞) := by
  set tree := simProgRand (w := w) L p argRegs decode defaultAns K
  rw [RandProbeTree.expectedProbes]
  have hpt : ∀ z, (tree.run m) z * (z.2 : ℝ≥0∞) ≤
      (tree.run m) z * ((K + 2 * S + regCells + L.overhead : ℕ) : ℝ≥0∞) := by
    intro z
    by_cases hz : z ∈ (tree.run m).support
    · exact mul_le_mul' le_rfl ((Nat.cast_le (α := ℝ≥0∞)).mpr
        (simProgRand_worstCase_probes L p argRegs decode defaultAns K m z hz))
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hz, zero_mul, zero_mul]
  refine (tsum_le_tsum hpt).trans ?_
  rw [ENNReal.tsum_mul_right, (tree.run m).tsum_coe, one_mul]

/-- **Main single-step Las Vegas simulation theorem (`simProgRand_lasVegas_spec`):**
Under `hm : L.ValidMem m`, `harg`, and `hdist : ExecProgramDist w p (L.unpack argRegs m) μ T`:
1. **100% zero-error support soundness (at any finite `K`):** every outcome `(ans, m')` in the
   support of `(simProgRand L p argRegs decode defaultAns K).run m` comes from some
   `vy ∈ μ.support` with `ans = (decode vy.1 vy.2.regs).getD defaultAns` and `m' = L.pack vy.2`!
2. **Expected probe bound:**
   `expectedProbes ≤ continuingSum K + L.overhead + p_run(K) * (2 * S + regCells)`.
3. **Continuation coupling inequality:** for any bounded continuation `g ≤ B_rem` on support,
   `E_{simProgRand}[g] ≤ E_{vy ~ μ}[g (decode vy, L.pack vy.2)] + p_run(K) * B_rem`! -/
theorem simProgRand_lasVegas_spec {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (p : Program B r) (argRegs : Fin r → ℕ)
    (decode : ℕ → (Fin r → ℕ) → Option Out) (defaultAns : Out) (K : ℕ)
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {μ : PMF (ℕ × Data r)} {T : ℝ≥0∞}
    (hdist : ExecProgramDist w p (L.unpack argRegs m) μ T) :
    let x₀ := L.unpack argRegs m
    let tree := simProgRand (w := w) L p argRegs decode defaultAns K
    let p_run := (evalRand w p K ⟨0, x₀⟩).toOuterMeasure (RandCfg.runningSet r)
    (∀ z ∈ (tree.run m).support,
      ∃ vy ∈ μ.support, z.1 = ((decode vy.1 vy.2.regs).getD defaultAns, L.pack vy.2)) ∧
    tree.expectedProbes m ≤
      (∑ t ∈ Finset.range K,
          (evalRand w p t ⟨0, x₀⟩).toOuterMeasure {cfg | isContinuingCfg p cfg = true}) +
        (L.overhead : ℝ≥0∞) + p_run * ((2 * S + regCells : ℕ) : ℝ≥0∞) ∧
    ∀ (g : Out × Mem (S + regCells) wCell → ℝ≥0∞) (B_rem : ℝ≥0∞),
      (∀ om ∈ ((tree.run m).map Prod.fst).support, g om ≤ B_rem) →
      (∑' om, ((tree.run m).map Prod.fst) om * g om) ≤
        (∑' vy, μ vy * g ((decode vy.1 vy.2.regs).getD defaultAns, L.pack vy.2)) +
          p_run * B_rem := by
  intro x₀ tree p_run
  have hx₀_bdd : x₀.Bounded w := L.unpack_bounded harg m
  set st₀ : SimOutcome S w r := .running 0 x₀.regs (fun _ => none) (fun _ => 0)
  have hst₀_cfg : st₀.toRandCfg (w := w) base m = .running ⟨0, x₀⟩ := by
    simp [st₀, SimOutcome.toRandCfg, reconstructData_init L argRegs m, x₀]
  have hst₀_bdd : (st₀.toRandCfg (w := w) base m).Bounded w := by
    rw [hst₀_cfg]
    exact hx₀_bdd
  obtain ⟨hmap_loop, hsup_loop, hexp_loop⟩ := simLoopRand_spec base p K st₀ m hst₀_bdd
  rw [hst₀_cfg] at hmap_loop hexp_loop
  set loop := simLoopRand (regCells := regCells) (w := w) (wCell := wCell) base p K st₀
  have hdirty_st₀ : st₀.dirty = 0 := dirtyCount_empty S w
  rw [hdirty_st₀, Nat.cast_zero, zero_add] at hexp_loop
  have hno_fault : ∀ z ∈ (loop.run m).support, z.1.1 ≠ .faulted := by
    intro z hz hflt
    have hmem_eval : (z.1.1.toRandCfg (w := w) base m) ∈ (evalRand w p K ⟨0, x₀⟩).support := by
      rw [evalRand, ← hmap_loop, PMF.mem_support_map_iff]
      exact ⟨z, hz, rfl⟩
    rw [hflt, SimOutcome.toRandCfg, support_evalRand] at hmem_eval
    exact hdist.2.1 K hmem_eval
  have htree_run :
      tree.run m =
        (loop.run m).bind fun z_l =>
          ((finishSimProgRand (w := w) L p x₀.regs decode defaultAns z_l.1.1).run z_l.1.2).map
            fun (out, p₂) => (out, L.reloadProbes + z_l.2 + p₂) := by
    dsimp only [tree]
    rw [simProgRand_eq_bind, RandProbeTree.run_bind, RandProbeTree.run_ofProbeTree,
      L.run_reload, L.probes_reload, PMF.pure_bind]
    change (RandProbeTree.run (loop >>= _) m).map _ = _
    rw [RandProbeTree.run_bind, PMF.map_bind]
    refine congrArg (PMF.bind (loop.run m)) (funext fun ⟨⟨st_l, m_l⟩, p_l⟩ => ?_)
    rw [PMF.map_comp]
    refine congrArg
      (fun f => PMF.map f
        ((finishSimProgRand (w := w) L p x₀.regs decode defaultAns st_l).run m_l))
      (funext fun ⟨out, p₂⟩ => Prod.ext rfl (by dsimp only [Function.comp_apply]; omega))
  have hfin_halted : ∀ v regs' wb' ext',
      (finishSimProgRand (w := w) L p x₀.regs decode defaultAns (.halted v regs' wb' ext')).run m =
        PMF.pure (((decode v regs').getD defaultAns,
          L.pack (reconstructData base m regs' wb' ext')),
          dirtyCount wb' + L.spillProbes) := by
    intro v regs' wb' ext'
    obtain ⟨hcm_mem, hcm_pr⟩ := commitHalted_spec L hm regs' wb' ext'
    simp only [finishSimProgRand, RandProbeTree.run_bind, RandProbeTree.run_ofProbeTree,
      PMF.pure_bind, RandProbeTree.run_pure, PMF.pure_map, add_zero]
    rw [hcm_mem, hcm_pr]
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: 100% zero-error support soundness!
    intro z hz
    rw [htree_run, PMF.mem_support_bind_iff] at hz
    obtain ⟨⟨⟨st_l, m_l⟩, p_l⟩, hz_l, hz_f⟩ := hz
    rw [PMF.mem_support_map_iff] at hz_f
    obtain ⟨z_f, hz_f_mem, rfl⟩ := hz_f
    obtain ⟨hm_l, _, _⟩ := hsup_loop _ hz_l
    dsimp only at hm_l hz_f_mem
    rw [hm_l] at hz_f_mem
    cases st_l with
    | faulted => exact absurd rfl (hno_fault _ hz_l)
    | halted v regs' wb' ext' =>
      rw [hfin_halted] at hz_f_mem
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz_f_mem
      subst hz_f_mem
      set y := reconstructData (w := w) base m regs' wb' ext'
      have hmem_eval : RandCfg.halted v y ∈ (evalRand w p K ⟨0, x₀⟩).support := by
        rw [evalRand, ← hmap_loop, PMF.mem_support_map_iff]
        exact ⟨((.halted v regs' wb' ext', m_l), p_l), hz_l, rfl⟩
      have hpos : 0 < evalRand w p K ⟨0, x₀⟩ (.halted v y) :=
        pos_iff_ne_zero.mpr ((PMF.mem_support_iff _ _).mp hmem_eval)
      have hvy_mem : (v, y) ∈ μ.support := by
        rw [PMF.mem_support_iff]
        exact ne_of_gt (hpos.trans_le (hdist.evalRand_halted_le K (v, y)))
      exact ⟨(v, y), hvy_mem, rfl⟩
    | running pc regs' wb' ext' =>
      rw [finishSimProgRand_fallback_run L p argRegs decode defaultAns m _ (by simp)]
        at hz_f_mem
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz_f_mem
      subst hz_f_mem
      exact ⟨fallbackOutcome w p x₀, fallbackOutcome_mem_support hdist, rfl⟩
  · -- Part 2: Expected probe bound!
    rw [RandProbeTree.expectedProbes, htree_run, Probability.PMF.tsum_bind_mul]
    set S_run : Set (RandCfg r) := RandCfg.runningSet r
    have hpt : ∀ z_l,
        (loop.run m) z_l *
            (∑' z,
              (((finishSimProgRand (w := w) L p x₀.regs decode defaultAns z_l.1.1).run z_l.1.2).map
                (fun (out, p₂) => (out, L.reloadProbes + z_l.2 + p₂))) z * (z.2 : ℝ≥0∞)) ≤
          (loop.run m) z_l * ((z_l.2 + z_l.1.1.dirty : ℕ) : ℝ≥0∞) +
            (loop.run m) z_l * (L.overhead : ℝ≥0∞) +
            (loop.run m) z_l *
              (Set.indicator S_run 1 (z_l.1.1.toRandCfg base m) *
                ((2 * S + regCells : ℕ) : ℝ≥0∞)) := by
      rintro ⟨⟨st_l, m_l⟩, p_l⟩
      by_cases hz_l : ((st_l, m_l), p_l) ∈ (loop.run m).support
      · obtain ⟨hm_l, _, _⟩ := hsup_loop _ hz_l
        dsimp only at hm_l ⊢
        rw [hm_l, Probability.PMF.tsum_map_mul]
        cases st_l with
        | faulted => exact absurd rfl (hno_fault _ hz_l)
        | halted v regs' wb' ext' =>
          rw [hfin_halted]
          rw [tsum_eq_single (((decode v regs').getD defaultAns,
              L.pack (reconstructData base m regs' wb' ext')), dirtyCount wb' + L.spillProbes)
            (fun z hz => by simp [PMF.pure_apply, hz])]
          simp only [PMF.pure_apply_self, one_mul, SimOutcome.dirty]
          have hnot_r : (SimOutcome.halted v regs' wb' ext').toRandCfg (w := w) base m ∉ S_run := by
            simp [S_run, SimOutcome.toRandCfg]
          rw [Set.indicator_of_notMem hnot_r, zero_mul, mul_zero, add_zero, ← mul_add,
            ← Nat.cast_add]
          refine mul_le_mul' le_rfl ((Nat.cast_le (α := ℝ≥0∞)).mpr ?_)
          have hov : L.overhead = L.reloadProbes + L.spillProbes := rfl
          omega
        | running pc regs' wb' ext' =>
          rw [finishSimProgRand_fallback_run L p argRegs decode defaultAns m _ (by simp)]
          set vy := fallbackOutcome w p x₀
          rw [tsum_eq_single (((decode vy.1 vy.2.regs).getD defaultAns, L.pack vy.2),
              2 * S + regCells)
            (fun z hz => by simp [PMF.pure_apply, hz])]
          simp only [PMF.pure_apply_self, one_mul, SimOutcome.dirty]
          have hmem_r :
              (SimOutcome.running pc regs' wb' ext').toRandCfg (w := w) base m ∈ S_run :=
            ⟨_, rfl⟩
          rw [Set.indicator_of_mem hmem_r, Pi.one_apply, one_mul, ← mul_add, ← mul_add,
            ← Nat.cast_add, ← Nat.cast_add]
          refine mul_le_mul' le_rfl ((Nat.cast_le (α := ℝ≥0∞)).mpr ?_)
          have hov : L.overhead = L.reloadProbes + L.spillProbes := rfl
          omega
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hz_l]
        simp
    refine (tsum_le_tsum hpt).trans ?_
    rw [tsum_add, tsum_add,
      ENNReal.tsum_mul_right, (loop.run m).tsum_coe, one_mul]
    have htail_eq :
        (∑' z_l, (loop.run m) z_l *
            (Set.indicator S_run 1 (z_l.1.1.toRandCfg base m) *
              ((2 * S + regCells : ℕ) : ℝ≥0∞))) =
          p_run * ((2 * S + regCells : ℕ) : ℝ≥0∞) := by
      simp_rw [← mul_assoc]
      rw [ENNReal.tsum_mul_right]
      congr 1
      have hpush := (Probability.PMF.tsum_map_mul (loop.run m)
        (fun z => z.1.1.toRandCfg (w := w) base m) (Set.indicator S_run 1)).symm
      rw [hpush, hmap_loop, ← Probability.PMF.toOuterMeasure_eq_tsum_mul_indicator]
      rfl
    rw [htail_eq]
    exact add_le_add (add_le_add hexp_loop le_rfl) le_rfl
  · -- Part 3: Continuation coupling inequality!
    intro g B_rem hg_le
    rw [Probability.PMF.tsum_map_mul, htree_run, Probability.PMF.tsum_bind_mul]
    set vy_fb := fallbackOutcome w p x₀
    set om_fb : Out × Mem (S + regCells) wCell :=
      ((decode vy_fb.1 vy_fb.2.regs).getD defaultAns, L.pack vy_fb.2)
    set f_om : ℕ × Data r → Out × Mem (S + regCells) wCell :=
      fun vy => ((decode vy.1 vy.2.regs).getD defaultAns, L.pack vy.2)
    set h_cfg : RandCfg r → ℝ≥0∞ := fun cfg =>
      match cfg with
      | .halted v y => g (f_om (v, y))
      | .running _ => B_rem
      | .faulted => 0
    have hpt_g : ∀ z_l,
        (loop.run m) z_l *
            (∑' z,
              (((finishSimProgRand (w := w) L p x₀.regs decode defaultAns z_l.1.1).run z_l.1.2).map
                (fun (out, p₂) => (out, L.reloadProbes + z_l.2 + p₂))) z * g z.1) ≤
          (loop.run m) z_l * h_cfg (z_l.1.1.toRandCfg base m) := by
      rintro ⟨⟨st_l, m_l⟩, p_l⟩
      by_cases hz_l : ((st_l, m_l), p_l) ∈ (loop.run m).support
      · obtain ⟨hm_l, _, _⟩ := hsup_loop _ hz_l
        dsimp only at hm_l ⊢
        rw [hm_l, Probability.PMF.tsum_map_mul]
        cases st_l with
        | faulted => exact absurd rfl (hno_fault _ hz_l)
        | halted v regs' wb' ext' =>
          rw [hfin_halted]
          set y := reconstructData (w := w) base m regs' wb' ext'
          rw [tsum_eq_single (((decode v regs').getD defaultAns, L.pack y),
              dirtyCount wb' + L.spillProbes)
            (fun z hz => by simp [PMF.pure_apply, hz])]
          have hy_regs : y.regs = regs' := rfl
          simp [SimOutcome.toRandCfg, h_cfg, f_om, y, hy_regs]
        | running pc regs' wb' ext' =>
          have hom_mem : om_fb ∈ ((tree.run m).map Prod.fst).support := by
            rw [PMF.mem_support_map_iff]
            refine ⟨(om_fb, L.reloadProbes + p_l + (2 * S + regCells)), ?_, rfl⟩
            rw [htree_run, PMF.mem_support_bind_iff]
            refine ⟨((.running pc regs' wb' ext', m_l), p_l), hz_l, ?_⟩
            dsimp only
            rw [hm_l,
              finishSimProgRand_fallback_run L p argRegs decode defaultAns m _ (by simp),
              PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff]
          rw [finishSimProgRand_fallback_run L p argRegs decode defaultAns m _ (by simp)]
          change (loop.run m) ((.running pc regs' wb' ext', m), p_l) *
              (∑' z, (PMF.pure (om_fb, 2 * S + regCells)) z * g z.1) ≤ _
          rw [tsum_eq_single (om_fb, 2 * S + regCells)
            (fun z hz => by simp [PMF.pure_apply, hz])]
          simp only [PMF.pure_apply_self, one_mul, SimOutcome.toRandCfg, h_cfg]
          exact mul_le_mul' le_rfl (hg_le om_fb hom_mem)
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hz_l, zero_mul, zero_mul]
    refine (tsum_le_tsum hpt_g).trans ?_
    have hpush_g :
        (∑' z_l, (loop.run m) z_l * h_cfg (z_l.1.1.toRandCfg base m)) =
          ∑' cfg, (evalRand w p K ⟨0, x₀⟩) cfg * h_cfg cfg := by
      have hp := (Probability.PMF.tsum_map_mul (loop.run m)
        (fun z => z.1.1.toRandCfg (w := w) base m) h_cfg).symm
      rw [hp, hmap_loop]
      rfl
    rw [hpush_g]
    have hcfg_split : ∀ cfg : RandCfg r,
        (evalRand w p K ⟨0, x₀⟩) cfg * h_cfg cfg =
          (match cfg with
           | .halted v y => (evalRand w p K ⟨0, x₀⟩) (.halted v y) * g (f_om (v, y))
           | _ => 0) +
          Set.indicator (RandCfg.runningSet r) (evalRand w p K ⟨0, x₀⟩) cfg * B_rem := by
      intro cfg
      cases cfg with
      | halted v y =>
        have hnot : RandCfg.halted v y ∉ RandCfg.runningSet r := by simp
        rw [Set.indicator_of_notMem hnot]
        simp [h_cfg]
      | running s =>
        have hmem : RandCfg.running s ∈ RandCfg.runningSet r := ⟨s, rfl⟩
        rw [Set.indicator_of_mem hmem]
        simp [h_cfg]
      | faulted =>
        have hnot : (RandCfg.faulted : RandCfg r) ∉ RandCfg.runningSet r := by simp
        rw [Set.indicator_of_notMem hnot]
        simp [h_cfg]
    simp_rw [hcfg_split]
    rw [tsum_add, ENNReal.tsum_mul_right, ← PMF.toOuterMeasure_apply]
    refine add_le_add ?_ le_rfl
    set term_halt : RandCfg r → ℝ≥0∞ := fun cfg =>
      match cfg with
      | .halted v y => (evalRand w p K ⟨0, x₀⟩) (.halted v y) * g (f_om (v, y))
      | _ => 0
    have hinj_halt : Function.Injective (fun vy : ℕ × Data r => RandCfg.halted vy.1 vy.2) :=
      fun ⟨v₁, y₁⟩ ⟨v₂, y₂⟩ h => by cases h; rfl
    have heq_vy :
        (∑' cfg : RandCfg r, term_halt cfg) =
          ∑' vy : ℕ × Data r, (evalRand w p K ⟨0, x₀⟩) (.halted vy.1 vy.2) * g (f_om vy) := by
      symm
      refine Function.Injective.tsum_eq hinj_halt (f := term_halt) fun cfg hcfg => ?_
      cases cfg with
      | halted v y => exact ⟨(v, y), rfl⟩
      | running _ | faulted => exact absurd rfl hcfg
    rw [heq_vy]
    exact tsum_le_tsum fun vy => mul_le_mul' (hdist.evalRand_halted_le K vy) le_rfl

/-! #### Exact finite-tree `ExecRand` simulation (`simExecRand`, `simExecRandWide`) -/

/-- Maximum step count across all leaves of a finite `ProbComp (α × ℕ)` computation tree. -/
noncomputable def probCompMaxSnd {α : Type} : ProbComp (α × ℕ) → ℕ
  | .pure z => z.2
  | .liftBind n cont => Finset.univ.sup fun c : Fin (n + 1) => probCompMaxSnd (cont c)

theorem snd_le_probCompMaxSnd {α : Type} :
    ∀ (m : ProbComp (α × ℕ)) {z : α × ℕ}, z ∈ m.support → z.2 ≤ probCompMaxSnd m
  | .pure w, z, hz => by
    cases OracleComp.eq_of_mem_supportWith_pure hz
    exact le_rfl
  | .liftBind n cont, z, hz => by
    rw [← ProbComp.support_eval] at hz
    change z ∈ ((ProbComp.unifOracle n).bind fun c => ProbComp.eval (cont c)).support at hz
    rw [PMF.mem_support_bind_iff] at hz
    obtain ⟨c, -, hc⟩ := hz
    rw [ProbComp.support_eval] at hc
    exact (snd_le_probCompMaxSnd (cont c) hc).trans
      (Finset.le_sup (f := fun c' : Fin (n + 1) => probCompMaxSnd (cont c')) (Finset.mem_univ c))

/-- Uniform finite-tree fuel across all `m : Mem (S + regCells) wCell` on which `ExecRand` holds. -/
noncomputable def autoRandFuel {B : Basis} {r S regCells w wCell : ℕ} {input : Fin r → Bool}
    {base : ℕ} (L : RegLayout r input base S w regCells wCell)
    (c : Code B r) (argRegs : Fin r → ℕ) : ℕ :=
  Finset.univ.sup fun m : Mem (S + regCells) wCell =>
    letI := Classical.propDecidable
    if h : ∃ mc : ProbComp (Data r × ℕ), ExecRand w c (L.unpack argRegs m) mc then
      probCompMaxSnd (Classical.choose h) + 1
    else 0

theorem le_autoRandFuel_of_execRand {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ}
    (L : RegLayout r input base S w regCells wCell)
    {c : Code B r} {argRegs : Fin r → ℕ} {m : Mem (S + regCells) wCell}
    {mc : ProbComp (Data r × ℕ)} (hexec : ExecRand w c (L.unpack argRegs m) mc)
    {z : Data r × ℕ} (hz : z ∈ mc.support) :
    z.2 + 1 ≤ autoRandFuel L c argRegs := by
  let nodeFuel : Mem (S + regCells) wCell → ℕ := fun m' =>
    letI := Classical.propDecidable
    if h : ∃ mc' : ProbComp (Data r × ℕ), ExecRand w c (L.unpack argRegs m') mc' then
      probCompMaxSnd (Classical.choose h) + 1
    else 0
  have hex : ∃ mc' : ProbComp (Data r × ℕ), ExecRand w c (L.unpack argRegs m) mc' := ⟨mc, hexec⟩
  have hmc_eq : Classical.choose hex = mc := (Classical.choose_spec hex).unique hexec
  have hle_node : z.2 + 1 ≤ nodeFuel m := by
    dsimp only [nodeFuel]
    split_ifs
    rw [hmc_eq]
    exact Nat.add_le_add_right (snd_le_probCompMaxSnd mc hz) 1
  exact hle_node.trans (Finset.le_sup (f := nodeFuel) (Finset.mem_univ m))

/-- Exact finite-tree `ExecRand` simulation over an arbitrary `RegLayout`: reproduces the **exact**
`(output, postMem)` distribution of `mc` with **zero** `η` slack and expected probes bounded by
`(ProbComp.expect mc fun z => (z.2 : ℝ≥0∞)) + L.overhead`. -/
theorem simExecRandLayout {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (L : RegLayout r input base S w regCells wCell)
    (c : Code B r) (retReg : Fin r) (argRegs : Fin r → ℕ)
    (decode : (Fin r → ℕ) → Option Out) (defaultAns : Out)
    {m : Mem (S + regCells) wCell} (hm : L.ValidMem m)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {mc : ProbComp (Data r × ℕ)} (hexec : ExecRand w c (L.unpack argRegs m) mc) :
    let tree := simProgRand (w := w) L (c.program retReg) argRegs
      (fun _ regs => decode regs) defaultAns (autoRandFuel L c argRegs)
    (tree.run m).map Prod.fst =
        mc.eval.map (fun z => ((decode z.1.regs).getD defaultAns, L.pack z.1)) ∧
      tree.expectedProbes m ≤
        ProbComp.expect mc (fun z => (z.2 : ℝ≥0∞)) + (L.overhead : ℝ≥0∞) := by
  intro tree
  set K := autoRandFuel L c argRegs
  set x₀ := L.unpack argRegs m
  have hK : ∀ z ∈ mc.support, z.2 + 1 ≤ K := fun z hz => le_autoRandFuel_of_execRand L hexec hz
  have hrun_prog := hexec.runRand_program retReg hK
  have hp_run_zero :
      (evalRand w (c.program retReg) K ⟨0, x₀⟩).toOuterMeasure (RandCfg.runningSet r) = 0 := by
    rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
    rintro cfg hmem ⟨u, rfl⟩
    rw [support_evalRand, hrun_prog] at hmem
    obtain ⟨z, -, hz_eq⟩ := OracleComp.mem_supportWith_map_iff.mp hmem
    cases hz_eq
  have hcdist : ExecCodeDist w c x₀ (mc.eval.map Prod.fst)
      (ProbComp.expect mc fun z => (z.2 : ℝ≥0∞)) := by
    simpa [ProbComp.eval_map] using ExecCodeDist.of_execRand hexec
  have hpdist := execProgramDist_of_execCodeDist hcdist retReg
  obtain ⟨_, hexp_sim, hcoupl⟩ :=
    simProgRand_lasVegas_spec L (c.program retReg) argRegs (fun _ regs => decode regs)
      defaultAns K hm harg hpdist
  rw [hp_run_zero, zero_mul, add_zero] at hexp_sim
  have hcont_le :
      (∑ t ∈ Finset.range K,
          (evalRand w (c.program retReg) t ⟨0, x₀⟩).toOuterMeasure
            {cfg | isContinuingCfg (c.program retReg) cfg = true}) ≤
        ProbComp.expect mc (fun z => (z.2 : ℝ≥0∞)) :=
    continuing_sum_le_of_almostSurelyHalts hpdist.almostSurelyHalts hpdist.1 K
  refine ⟨?_, hexp_sim.trans (add_le_add hcont_le le_rfl)⟩
  set μ₁ := (tree.run m).map Prod.fst
  set μ₂ := mc.eval.map (fun z : Data r × ℕ => ((decode z.1.regs).getD defaultAns, L.pack z.1))
  have hdom_om : ∀ om, μ₁ om ≤ μ₂ om := by
    classical
    intro om
    have hg := hcoupl (fun x => if x = om then 1 else 0) 1 (fun x _ => by split_ifs <;> simp)
    rw [hp_run_zero, zero_mul, add_zero] at hg
    have hlhs : (∑' x, μ₁ x * (if x = om then (1 : ℝ≥0∞) else 0)) = μ₁ om := by
      rw [tsum_eq_single om (fun x hx => by simp [hx])]
      simp
    have hrhs :
        (∑' vy : ℕ × Data r,
            ((mc.eval.map Prod.fst).map fun y => (y.regs retReg, y)) vy *
              (if ((decode vy.2.regs).getD defaultAns, L.pack vy.2) = om then 1 else 0)) =
          μ₂ om := by
      rw [Probability.PMF.tsum_map_mul, Probability.PMF.tsum_map_mul]
      dsimp only [μ₂]
      rw [PMF.map_apply]
      refine tsum_congr fun z => ?_
      by_cases h : ((decode z.1.regs).getD defaultAns, L.pack z.1) = om
      · simp [h]
      · have h' : om ≠ ((decode z.1.regs).getD defaultAns, L.pack z.1) := Ne.symm h
        simp [h, h']
    rwa [hlhs, hrhs] at hg
  ext om
  refine le_antisymm (hdom_om om) ?_
  by_contra hnot
  have hlt : μ₁ om < μ₂ om := lt_of_not_ge hnot
  have hsum1 := (μ₁.tsum_coe).symm.trans (tsum_eq_add_tsum_ite (f := fun z => μ₁ z) om)
  have hsum2 := (tsum_eq_add_tsum_ite (f := fun z => μ₂ z) om).symm.trans μ₂.tsum_coe
  have hrest_ne_top :
      (∑' z, @ite ℝ≥0∞ (z = om) (Classical.propDecidable _) 0 (μ₁ z)) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hsum1
    exact ENNReal.one_ne_top hsum1
  refine lt_irrefl (1 : ℝ≥0∞)
    ((hsum1.trans_lt (ENNReal.add_lt_add_of_lt_of_le hrest_ne_top hlt
      (tsum_le_tsum fun z => ?_))).trans_eq hsum2)
  split_ifs
  · exact le_rfl
  · exact hdom_om z

/-- Exact finite-tree `ExecRand` simulation in standard `w`-bit layout (`S + persCount input` cells
of width `w`, additive overhead `2 * persCount input`). -/
theorem simExecRand {B : Basis} {r S w : ℕ} {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (c : Code B r) (retReg : Fin r) (argRegs : Fin r → ℕ)
    (decode : (Fin r → ℕ) → Option Out) (defaultAns : Out)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    (m : Mem (S + persCount input) w)
    {mc : ProbComp (Data r × ℕ)}
    (hexec : ExecRand w c (unpackData input argRegs base S w m) mc) :
    let L := standardLayout input base S w
    let tree := simProgRand (w := w) L (c.program retReg) argRegs
      (fun _ regs => decode regs) defaultAns (autoRandFuel L c argRegs)
    (tree.run m).map Prod.fst =
        mc.eval.map (fun z => ((decode z.1.regs).getD defaultAns, packMem input base S w z.1)) ∧
      tree.expectedProbes m ≤
        ProbComp.expect mc (fun z => (z.2 : ℝ≥0∞)) + (2 * persCount input : ℕ) := by
  intro L tree
  obtain ⟨hlaw, hexp⟩ := simExecRandLayout L c retReg argRegs decode defaultAns trivial harg hexec
  refine ⟨hlaw, hexp.trans ?_⟩
  rw [standardLayout_overhead]

/-- Exact finite-tree `ExecRand` simulation in wide-cell single-spill layout (`S + 1` cells of width
`wideWidth input w`, additive overhead `if persCount input = 0 then 0 else 2 ≤ 2`). -/
theorem simExecRandWide {B : Basis} {r S w : ℕ} {input : Fin r → Bool} {base : ℕ} {Out : Type}
    (c : Code B r) (retReg : Fin r) (argRegs : Fin r → ℕ)
    (decode : (Fin r → ℕ) → Option Out) (defaultAns : Out)
    (harg : ∀ i, input i = true → Fits w (argRegs i))
    {m : Mem (S + 1) (wideWidth input w)}
    (hm : (wideLayout input base S w).ValidMem m)
    {mc : ProbComp (Data r × ℕ)}
    (hexec : ExecRand w c (unpackDataWide input argRegs base S w m) mc) :
    let L := wideLayout input base S w
    let tree := simProgRand (w := w) L (c.program retReg) argRegs
      (fun _ regs => decode regs) defaultAns (autoRandFuel L c argRegs)
    (tree.run m).map Prod.fst =
        mc.eval.map (fun z =>
          ((decode z.1.regs).getD defaultAns, packMemWide input base S w z.1)) ∧
      tree.expectedProbes m ≤
        ProbComp.expect mc (fun z => (z.2 : ℝ≥0∞)) +
          ((if persCount input = 0 then 0 else 2 : ℕ) : ℝ≥0∞) := by
  intro L tree
  obtain ⟨hlaw, hexp⟩ := simExecRandLayout L c retReg argRegs decode defaultAns hm harg hexec
  refine ⟨hlaw, hexp.trans ?_⟩
  rw [wideLayout_overhead]

/-! #### Antitone tail decay and uniform finite-horizon cutoff selection -/

/-- Active-configuration probability `(evalRand w p K s).toOuterMeasure (RandCfg.runningSet r)` is
antitone in `K` because `.halted` and `.faulted` are absorbing. -/
theorem evalRand_runningSet_antitone {B : Basis} {r : ℕ} (w : ℕ) (p : Program B r) (s : State r) :
    Antitone fun K => (evalRand w p K s).toOuterMeasure (RandCfg.runningSet r) := by
  refine antitone_nat_of_succ_le fun K => ?_
  have hstep : evalRand w p (K + 1) s =
      (evalRand w p K s).bind (fun cfg => (stepRand w p cfg).eval) := by
    rw [evalRand, runRand_add w p K 1, ProbComp.eval_bind]
    simp only [evalRand, runRand_succ, runRand_zero, bind_pure]
  rw [hstep, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine tsum_le_tsum fun cfg => ?_
  cases cfg with
  | running u =>
    have hmem : RandCfg.running u ∈ RandCfg.runningSet r := ⟨u, rfl⟩
    rw [Set.indicator_of_mem hmem]
    simpa using mul_le_mul' le_rfl (Probability.PMF.toOuterMeasure_le_one _ _)
  | halted v d =>
    have hnot : RandCfg.halted v d ∉ RandCfg.runningSet r := by simp
    simp [stepRand_halted, PMF.toOuterMeasure_pure_apply, hnot]
  | faulted =>
    have hnot : (RandCfg.faulted : RandCfg r) ∉ RandCfg.runningSet r := by simp
    simp [stepRand_faulted, PMF.toOuterMeasure_pure_apply, hnot]

/-- For any antitone sequence `a : ℕ → ℝ≥0∞` with `∑' t, a t ≠ ⊤`, `(A + B * K) * a K → 0` as
`K → ∞`. -/
theorem exists_cutoff_mul_le {a : ℕ → ℝ≥0∞} (ha : Antitone a) (hsum : (∑' t, a t) ≠ ⊤)
    (A B : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K ≥ K₀, a K * ((A : ℝ≥0∞) + (B : ℝ≥0∞) * (K : ℝ≥0∞)) ≤ η := by
  have hiSup_all : (∑' t, a t) = ⨆ N : ℕ, ∑ t ∈ Finset.range N, a t := ENNReal.tsum_eq_iSup_nat
  by_cases hS0 : (∑' t, a t) = 0
  · refine ⟨1, le_rfl, fun K _ => ?_⟩
    have haK : a K = 0 := by
      refine le_antisymm ?_ zero_le
      calc a K
        _ ≤ ∑ t ∈ Finset.range (K + 1), a t :=
            Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_self K))
        _ ≤ ⨆ N : ℕ, ∑ t ∈ Finset.range N, a t :=
            le_iSup (fun N => ∑ t ∈ Finset.range N, a t) (K + 1)
        _ = 0 := hiSup_all.symm.trans hS0
    simp [haK]
  · set S := ∑' t, a t
    set C : ℕ := max B 1
    have h1C : 1 ≤ C := le_max_right B 1
    have hC_ne_top : ((3 * C : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top (3 * C)
    set δ : ℝ≥0∞ := min (η / ((3 * C : ℕ) : ℝ≥0∞)) (S / 2)
    have hδ_pos : 0 < δ := lt_min (ENNReal.div_pos hη.ne' hC_ne_top)
      (ENNReal.div_pos hS0 (by norm_num))
    have hsub_lt : S - δ < S := ENNReal.sub_lt_self hsum hS0 hδ_pos.ne'
    have hsub_lt' : S - δ < ⨆ N : ℕ, ∑ t ∈ Finset.range N, a t := hiSup_all ▸ hsub_lt
    rw [lt_iSup_iff] at hsub_lt'
    obtain ⟨N, hN⟩ := hsub_lt'
    refine ⟨max 1 (2 * N + A + 2), le_max_left _ _, fun K hK => ?_⟩
    have hK_ge : 2 * N + A + 2 ≤ K := (le_max_right 1 _).trans hK
    set M : ℕ := K - N
    have hM_mul_le : (M : ℝ≥0∞) * a K ≤ δ := by
      have htail_sum : (∑ i ∈ Finset.range M, a (N + i)) ≤ δ := by
        by_contra hnot
        have hgt : δ < ∑ i ∈ Finset.range M, a (N + i) := lt_of_not_ge hnot
        have hlt_sum :
            (S - δ) + δ < (∑ t ∈ Finset.range N, a t) + ∑ i ∈ Finset.range M, a (N + i) :=
          ENNReal.add_lt_add hN hgt
        have hδ_le_S : δ ≤ S := (min_le_right _ _).trans ENNReal.half_le_self
        rw [tsub_add_cancel_of_le hδ_le_S, ← Finset.sum_range_add] at hlt_sum
        have hle_S : (∑ t ∈ Finset.range (N + M), a t) ≤ S :=
          (le_iSup (fun n => ∑ t ∈ Finset.range n, a t) (N + M)).trans_eq hiSup_all.symm
        exact lt_irrefl S (hlt_sum.trans_le hle_S)
      have hconst : (M : ℝ≥0∞) * a K = ∑ _i ∈ Finset.range M, a K := by
        simp [Finset.sum_const]
      rw [hconst]
      refine (Finset.sum_le_sum fun i hi => ha ?_).trans htail_sum
      rw [Finset.mem_range] at hi
      omega
    have hnat : A + B * K ≤ (3 * C) * M := by
      have hBC : B ≤ C := le_max_left B 1
      have hKM : K ≤ 2 * M := by omega
      have hAM : A ≤ M := by omega
      have h1 : A + B * K ≤ M + C * (2 * M) := Nat.add_le_add hAM (Nat.mul_le_mul hBC hKM)
      have h2 : M ≤ C * M := Nat.le_mul_of_pos_left M h1C
      have h3 : C * M + C * (2 * M) = (3 * C) * M := by ring
      omega
    have hlin_le :
        (A : ℝ≥0∞) + (B : ℝ≥0∞) * (K : ℝ≥0∞) ≤ ((3 * C : ℕ) : ℝ≥0∞) * (M : ℝ≥0∞) := by
      rw [← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_mul]
      exact Nat.cast_le.mpr hnat
    calc a K * ((A : ℝ≥0∞) + (B : ℝ≥0∞) * (K : ℝ≥0∞))
      _ ≤ a K * (((3 * C : ℕ) : ℝ≥0∞) * (M : ℝ≥0∞)) := mul_le_mul' le_rfl hlin_le
      _ = ((3 * C : ℕ) : ℝ≥0∞) * ((M : ℝ≥0∞) * a K) := by ac_rfl
      _ ≤ ((3 * C : ℕ) : ℝ≥0∞) * δ := mul_le_mul' le_rfl hM_mul_le
      _ ≤ ((3 * C : ℕ) : ℝ≥0∞) * (η / ((3 * C : ℕ) : ℝ≥0∞)) :=
          mul_le_mul' le_rfl (min_le_left _ _)
      _ ≤ η := ENNReal.mul_div_le

/-- Uniform finite-horizon cutoff selection across a finite operation alphabet `opsAlphabet` and the
finite memory space `Mem (S + regCells) wCell`: produces a single `K ≥ 1` such that for every
`o ∈ opsAlphabet` and `m` satisfying `Good o m`, the active-tail product
`p_run(K, o, m) * (A + B * K)` is at most `η`. -/
theorem exists_uniform_cutoff {Op : Type*} {B : Basis} {r S regCells w wCell : ℕ}
    {input : Fin r → Bool} {base : ℕ}
    (L : RegLayout r input base S w regCells wCell)
    (opsAlphabet : Finset Op) (Good : Op → Mem (S + regCells) wCell → Prop)
    (prog : Op → Program B r) (argRegs : Op → Fin r → ℕ)
    (hfin : ∀ o ∈ opsAlphabet, ∀ m, Good o m →
      expectedTime w (prog o) ⟨0, L.unpack (argRegs o) m⟩ ≠ ⊤)
    (A B : ℕ) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ o ∈ opsAlphabet, ∀ m, Good o m →
      (evalRand w (prog o) K ⟨0, L.unpack (argRegs o) m⟩).toOuterMeasure (RandCfg.runningSet r) *
        ((A : ℝ≥0∞) + (B : ℝ≥0∞) * (K : ℝ≥0∞)) ≤ η := by
  classical
  let kPair : Op × Mem (S + regCells) wCell → ℕ := fun om =>
    if h : om.1 ∈ opsAlphabet ∧ Good om.1 om.2 then
      Classical.choose (exists_cutoff_mul_le
        (evalRand_runningSet_antitone w (prog om.1) ⟨0, L.unpack (argRegs om.1) om.2⟩)
        (hfin om.1 h.1 om.2 h.2) A B hη)
    else 1
  let pairs : Finset (Op × Mem (S + regCells) wCell) := opsAlphabet ×ˢ Finset.univ
  refine ⟨max 1 (pairs.sup kPair), le_max_left _ _, fun o ho m hgood => ?_⟩
  have hcond : o ∈ opsAlphabet ∧ Good o m := ⟨ho, hgood⟩
  have hspec := Classical.choose_spec (exists_cutoff_mul_le
    (evalRand_runningSet_antitone w (prog o) ⟨0, L.unpack (argRegs o) m⟩)
    (hfin o ho m hgood) A B hη)
  have hk_le : kPair (o, m) ≤ max 1 (pairs.sup kPair) := by
    refine (Finset.le_sup (f := kPair) ?_).trans (le_max_right 1 _)
    exact Finset.mem_product.mpr ⟨ho, Finset.mem_univ m⟩
  have hk_eq : kPair (o, m) = Classical.choose (exists_cutoff_mul_le
      (evalRand_runningSet_antitone w (prog o) ⟨0, L.unpack (argRegs o) m⟩)
      (hfin o ho m hgood) A B hη) := by
    dsimp only [kPair]
    split_ifs
    rfl
  exact hspec.2 _ (hk_eq ▸ hk_le)

end Cslib.CellProbe
