/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.WordRAM.Resizable.Randomized.ObliviousSequence
public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArray
import CslibFrontier.Tactic.Realize

/-!
# Resizable Bit-Packed Array Client and `2×2` Resizable Word RAM Interface Tests

End-to-end tests and reference client for Milestone M2 of the word-granular **Resizable Word RAM**
(`Cslib.DataStructure.WordRAM.Resizable`, `Resizable.Randomized.StateTransitionImpl`, and
`Resizable.Randomized.ObliviousSequenceImpl`):

1. **Resizable `b`-bit packed array (`PackedArrayOp`: `push`, `pop`, `get`, `set`, `length`)** on
   `[base, x.frontier)`: leaf arithmetic and bit-slice updates are synthesized via `Memory.Prog` +
   `by realize` (`RealizesBounded .exact` → `RDemonicExec.of_realizesBounded`) without hand-stepped
   `WordRAM.Code`, composed with `growZeroCode` and `shrinkCode` so the resting footprint is
   `3 + BitPackedArray.packedWords s.length b w = ⌈n * b / w⌉ + 5` words in the **current** length
   `n = s.length` (growing on `push` and shrinking on `pop`), certified via
   `Resizable.StateTransitionImpl.ofFn`, and lifted via `.toStandard`, `.toRandomized`, and
   `.toObliviousSequenceImplOfFn`.
2. **Sequential composition check** (`init → push 19 → push 27 → get 0 → set 0 23 → get 0 → pop →
   length`) at `w = 8, b = 5, base = 4 > 0`, verifying answer correctness across word-boundary
   straddling entries, dynamic frontier growth (`4 → 9 → 10 → 11`) and shrinkage (`11 → 10`), and
   caller memory `[0, 4)` preservation.
3. **Direct `.rand` randomized subroutine check** instantiating
   `Resizable.Randomized.StateTransitionImpl.ofFn` and `seq_expected_amortized_ofFn`.
4. **`.halt`-rejection soundness checks** verifying that a 1-instruction `[.halt out]` stub cannot
   satisfy the compiled flat-`RProgram` sequence guarantees (`not_execProgramSteps_halt`,
   `not_execProgramStepsOfFn_halt`, and `Randomized.not_execProgramSteps_halt`).
-/

public section

namespace CslibFrontierTests.WordRAMResizableDataStructure

open scoped ENNReal
open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure.WordRAM.Resizable
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ## 1. Overflow-free `Memory.Prog` leaf routines via `by realize` -/

/-- Overflow-free decomposition of `packedWords m b w = (m * b + w - 1) / w + 2` for `0 < w`. -/
theorem packedWords_eq_wordOffset_add {m b w : ℕ} (hw : 0 < w) :
    packedWords m b w =
      wordOffset b w m + (if 0 < bitOffset b w m then 1 else 0) + 2 := by
  unfold packedWords
  have hmul : m * b = bitOffset b w m + wordOffset b w m * w := by
    rw [Nat.add_comm, wordOffset_mul_add_bitOffset]
  have hb_lt : bitOffset b w m < w := bitOffset_lt hw
  have hrew : m * b + w - 1 = (bitOffset b w m + (w - 1)) + wordOffset b w m * w := by omega
  rw [hrew, Nat.add_mul_div_right _ _ hw]
  split_ifs with hpos
  · have hdiv : (bitOffset b w m + (w - 1)) / w = 1 := by
      apply Nat.le_antisymm
      · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hw).mpr (by omega))
      · exact (Nat.le_div_iff_mul_le hw).mpr (by omega)
    omega
  · have hb0 : bitOffset b w m = 0 := by omega
    rw [hb0, Nat.zero_add, Nat.div_eq_of_lt (by omega : w - 1 < w)]
    omega

/-- Adding or removing one `b`-bit entry (`b ≤ w`, `0 < w`) changes `packedWords` by `0` or `1`. -/
theorem packedWords_succ_sub_le_one {n b w : ℕ} (hw : 0 < w) (hbw : b ≤ w) :
    packedWords n b w ≤ packedWords (n + 1) b w ∧
      packedWords (n + 1) b w - packedWords n b w ≤ 1 := by
  unfold packedWords
  have hmono : (n * b + w - 1) / w ≤ ((n + 1) * b + w - 1) / w :=
    Nat.div_le_div_right (by rw [Nat.add_mul, one_mul]; omega)
  have hstep : ((n + 1) * b + w - 1) / w ≤ (n * b + w - 1) / w + 1 := by
    have hle : (n + 1) * b + w - 1 ≤ (n * b + w - 1) + 1 * w := by
      rw [Nat.add_mul, one_mul, one_mul]; omega
    exact (Nat.div_le_div_right hle).trans (by rw [Nat.add_mul_div_right _ _ hw])
  omega

/-- `Memory.Prog` computing `min d.1 d.2`. -/
def minProg (d : ℕ × ℕ) : Memory.Prog ℕ :=
  if d.1 < d.2 then pure d.1 else pure d.2

@[simp] theorem runClient_minProg (w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).runClient s (minProg d) = (min d.1 d.2, s, []) := by
  unfold minProg; split_ifs with h
  · change (d.1, s, []) = (min d.1 d.2, s, [])
    exact Prod.ext (Nat.min_eq_left h.le).symm rfl
  · change (d.2, s, []) = (min d.1 d.2, s, [])
    exact Prod.ext (Nat.min_eq_right (by omega)).symm rfl

@[simp] theorem memoryCost_minProg (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (minProg d) s = 0 := by
  unfold minProg; split_ifs <;> rfl

theorem minProg_realizesBounded :
    RealizesBounded .exact minProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ)) (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- `Memory.Prog` computing `2 ^ k - 1` without overflow for every `k ≤ w` (`0 < w`). -/
def maskProg (k : ℕ) : Memory.Prog ℕ :=
  if k = 0 then pure 0 else pure (((1 <<< (k - 1)) - 1) + (1 <<< (k - 1)))

@[simp] theorem runClient_maskProg (w k : ℕ) (s : Memory.State) :
    (Memory.spec w).runClient s (maskProg k) = (2 ^ k - 1, s, []) := by
  unfold maskProg
  rcases k with _ | m
  · rfl
  · refine Prod.ext ?_ rfl
    change ((1 <<< m) - 1) + (1 <<< m) = 2 ^ (m + 1) - 1
    rw [Nat.shiftLeft_eq, one_mul, Nat.pow_succ]
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega

@[simp] theorem memoryCost_maskProg (k : ℕ) (s : Memory.State) :
    memoryCost (maskProg k) s = 0 := by
  unfold maskProg; split_ifs <;> rfl

theorem maskProg_realizesBounded :
    RealizesBounded .exact maskProg (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ)) (fun w k _ => 0 < w ∧ k ≤ w) (fun _ _ => 0) := by
  realize
  all_goals
    rcases h with ⟨hw, hkw⟩
    unfold Fits at *
    have hsh : 1 <<< (d - 1) = 2 ^ (d - 1) := by rw [Nat.shiftLeft_eq, one_mul]
    have hge : 1 ≤ 2 ^ (d - 1) := Nat.one_le_two_pow
    have hlt1 : 2 ^ 0 < 2 ^ w := Nat.pow_lt_pow_right (by decide) hw
    have hsum : (2 ^ (d - 1) - 1) + 2 ^ (d - 1) < 2 ^ w := by
      have hd1 : (d - 1) + 1 = d := by omega
      calc (2 ^ (d - 1) - 1) + 2 ^ (d - 1) = 2 ^ ((d - 1) + 1) - 1 := by rw [Nat.pow_succ]; omega
        _ = 2 ^ d - 1 := by rw [hd1]
        _ < 2 ^ d := Nat.sub_lt Nat.one_le_two_pow (by decide)
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hkw
    try rw [hsh]
    omega

/-- `Memory.Prog` computing `packedWords m b w` without `m * b` overflow, taking `((b, w), m)`. -/
def packedWordsProg (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let rem := (d.2 % d.1.2) * d.1.1
  let wOff := (d.2 / d.1.2) * d.1.1 + rem / d.1.2
  let bOff := rem % d.1.2
  let extra ← if 0 < bOff then pure 1 else pure 0
  pure (wOff + extra + 2)

@[simp] theorem runClient_packedWordsProg (w₀ : ℕ) {b w m : ℕ} (hw : 0 < w) (s : Memory.State) :
    (Memory.spec w₀).runClient s (packedWordsProg ((b, w), m)) = (packedWords m b w, s, []) := by
  rw [packedWords_eq_wordOffset_add hw]
  unfold packedWordsProg wordOffset bitOffset
  dsimp only; split_ifs <;> rfl

@[simp] theorem memoryCost_packedWordsProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (packedWordsProg d) s = 0 := by
  unfold packedWordsProg; dsimp only; split_ifs <;> rfl

theorem packedWordsProg_realizesBounded :
    RealizesBounded .exact packedWordsProg (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => w = d.1.2 ∧ 0 < w ∧ d.1.1 ≤ w ∧ Fits w (packedWords d.2 d.1.1 w))
      (fun _ _ => 0) := by
  realize
  all_goals
    rcases h with ⟨rfl, hw, hbw, hfit⟩
    unfold Fits at *
    rw [packedWords_eq_wordOffset_add hw] at hfit
    unfold wordOffset bitOffset at hfit
    try simp only [hc, ↓reduceIte] at hfit
    have hlt1 : 2 ^ 0 < 2 ^ d.1.2 := Nat.pow_lt_pow_right (by decide) hw
    have hrem : (d.2 % d.1.2) * d.1.1 < 2 ^ d.1.2 := mod_mul_lt_two_pow hw hbw d.2
    omega

/-- Straight-line `Memory.Prog` reading `readPacked arrBase b w s.mem idx`, taking
`((arrBase, b), (w, idx))`. -/
def readPackedMemProg (d : (ℕ × ℕ) × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let rem := (d.2.2 % d.2.1) * d.1.2
  let wOff := (d.2.2 / d.2.1) * d.1.2 + rem / d.2.1
  let bOff ← pure (rem % d.2.1)
  let remW ← pure (d.2.1 - bOff)
  let k₀ ← minProg (d.1.2, remW)
  let k₁ ← pure (d.1.2 - k₀)
  let mask₀ ← maskProg k₀
  let mask₁ ← maskProg k₁
  let word₀ ← Memory.read (d.1.1 + wOff)
  let word₁ ← Memory.read (d.1.1 + wOff + 1)
  let low := (word₀ >>> bOff) &&& mask₀
  let high := (word₁ >>> 0) &&& mask₁
  pure (low ^^^ (high <<< k₀))

private theorem bind_eq_freeMBind {α β : Type} (x : Memory.Prog α) (f : α → Memory.Prog β) :
    (x >>= f) = x.bind f := rfl

@[simp] theorem runClient_readPackedMemProg (w : ℕ) (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec w).runClient s (readPackedMemProg d) =
      (readPacked d.1.1 d.1.2 d.2.1 s.mem d.2.2, s,
        [.read (d.1.1 + wordOffset d.1.2 d.2.1 d.2.2),
         .read (d.1.1 + wordOffset d.1.2 d.2.1 d.2.2 + 1)]) := by
  unfold readPackedMemProg
  simp only [bind_eq_freeMBind, StateTransitionSpec.runClient_bind,
    StateTransitionSpec.runClient_pure', runClient_minProg, runClient_maskProg, List.nil_append]
  rfl

theorem validHistory_readPackedMemProg {w : ℕ} {d : (ℕ × ℕ) × (ℕ × ℕ)} {N : ℕ} {s : Memory.State}
    (hw : 0 < d.2.1) (hidx : d.2.2 < N)
    (ha : d.1.1 + packedWords N d.1.2 d.2.1 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readPackedMemProg d)) := by
  have hlt := wordOffset_add_one_lt_packedWords (k := d.1.2) hw hidx
  rw [StateTransitionSpec.clientHistory, runClient_readPackedMemProg]
  change d.1.1 + wordOffset d.1.2 d.2.1 d.2.2 < s.frontier ∧
    d.1.1 + wordOffset d.1.2 d.2.1 d.2.2 + 1 < s.frontier ∧ True
  exact ⟨by omega, by omega, trivial⟩

theorem readPackedMemProg_realizesBounded :
    RealizesBounded .exact readPackedMemProg (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => ∃ N, w = d.2.1 ∧ 0 < w ∧ d.1.2 ≤ w ∧ d.2.2 < N ∧
        Fits w (d.1.1 + packedWords N d.1.2 w))
      (fun _ _ => 0) := by
  have _ := minProg_realizesBounded
  have _ := maskProg_realizesBounded
  realize
  all_goals
    rcases h with ⟨N, rfl, hw, hbw, hidx, hfit⟩
    unfold Fits at *
    try simp only [StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      runClient_minProg, runClient_maskProg]
    have hlt1 : wordOffset d.1.2 d.2.1 d.2.2 + 1 < packedWords N d.1.2 d.2.1 :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hb_lt : bitOffset d.1.2 d.2.1 d.2.2 < d.2.1 := bitOffset_lt hw
    have hrem : (d.2.2 % d.2.1) * d.1.2 < 2 ^ d.2.1 := mod_mul_lt_two_pow hw hbw d.2.2
    unfold wordOffset at hlt1
    unfold bitOffset at hb_lt
    try omega
  · set k₀ := min d.1.2 (d.2.1 - ((d.2.2 % d.2.1) * d.1.2) % d.2.1)
    set k₁ := d.1.2 - k₀
    have hk0_le : k₀ ≤ d.2.1 := (Nat.min_le_left _ _).trans hbw
    have hsum : k₁ + k₀ ≤ d.2.1 := (Nat.sub_add_cancel (Nat.min_le_left _ _)).le.trans hbw
    have hlow_lt :
        ((s.mem (d.1.1 + ((d.2.2 / d.2.1) * d.1.2 + ((d.2.2 % d.2.1) * d.1.2) / d.2.1)) >>>
            (((d.2.2 % d.2.1) * d.1.2) % d.2.1)) &&& (2 ^ k₀ - 1)) < 2 ^ d.2.1 := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact (Nat.mod_lt _ (Nat.two_pow_pos k₀)).trans_le (Nat.pow_le_pow_right (by decide) hk0_le)
    have hhigh_lt :
        (((s.mem (d.1.1 + ((d.2.2 / d.2.1) * d.1.2 + ((d.2.2 % d.2.1) * d.1.2) / d.2.1) + 1) >>>
            0) &&& (2 ^ k₁ - 1)) <<< k₀) < 2 ^ d.2.1 := by
      refine shiftLeft_lt_two_pow_of_lt (a := k₁) ?_ hsum
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos k₁)
    exact Nat.xor_lt_two_pow hlow_lt hhigh_lt
  · set k₀ := min d.1.2 (d.2.1 - ((d.2.2 % d.2.1) * d.1.2) % d.2.1)
    set k₁ := d.1.2 - k₀
    have hsum : k₁ + k₀ ≤ d.2.1 := (Nat.sub_add_cancel (Nat.min_le_left _ _)).le.trans hbw
    refine shiftLeft_lt_two_pow_of_lt (a := k₁) ?_ hsum
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos k₁)

/-- Straight-line `Memory.Prog` writing `val` into `idx` via `writePacked`, taking
`(((arrBase, b), (w, idx)), val)`. -/
def writePackedMemProg (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) : Memory.Prog Unit := do
  let rem := (d.1.2.2 % d.1.2.1) * d.1.1.2
  let wOff := (d.1.2.2 / d.1.2.1) * d.1.1.2 + rem / d.1.2.1
  let bOff ← pure (rem % d.1.2.1)
  let remW ← pure (d.1.2.1 - bOff)
  let k₀ ← minProg (d.1.1.2, remW)
  let k₁ ← pure (d.1.1.2 - k₀)
  let mask₀ ← maskProg k₀
  let mask₁ ← maskProg k₁
  let word₀ ← Memory.read (d.1.1.1 + wOff)
  let old₀ := (word₀ >>> bOff) &&& mask₀
  let val₀ := d.2 &&& mask₀
  Memory.write (d.1.1.1 + wOff) (word₀ ^^^ ((old₀ ^^^ val₀) <<< bOff))
  let word₁ ← Memory.read (d.1.1.1 + wOff + 1)
  let old₁ := (word₁ >>> 0) &&& mask₁
  let val₁ := (d.2 >>> k₀) &&& mask₁
  Memory.write (d.1.1.1 + wOff + 1) (word₁ ^^^ ((old₁ ^^^ val₁) <<< 0))

@[simp] theorem clientResult_writePackedMemProg (w : ℕ) (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)
    (s : Memory.State) :
    (Memory.spec w).clientResult s (writePackedMemProg d) = () := rfl

@[simp] theorem clientState_writePackedMemProg (w : ℕ) (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ)
    (s : Memory.State) :
    (Memory.spec w).clientState s (writePackedMemProg d) =
      { mem := writePacked d.1.1.1 d.1.1.2 d.1.2.1 s.mem d.1.2.2 d.2, frontier := s.frontier } := by
  unfold writePackedMemProg
  simp only [StateTransitionSpec.clientState, bind_eq_freeMBind, StateTransitionSpec.runClient_bind,
    StateTransitionSpec.runClient_pure', runClient_minProg, runClient_maskProg]
  rfl

theorem validHistory_writePackedMemProg {w : ℕ} {d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ} {N : ℕ}
    {s : Memory.State} (hw_eq : w = d.1.2.1) (hw : 0 < w) (hbw : d.1.1.2 ≤ w) (hidx : d.1.2.2 < N)
    (hwf : Memory.WellFormed w s)
    (ha : d.1.1.1 + packedWords N d.1.1.2 d.1.2.1 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writePackedMemProg d)) := by
  subst hw_eq
  have hlt := wordOffset_add_one_lt_packedWords (k := d.1.1.2) hw hidx
  have hb_lt : bitOffset d.1.1.2 d.1.2.1 d.1.2.2 < d.1.2.1 := bitOffset_lt hw
  unfold wordOffset at hlt; unfold bitOffset at hb_lt
  unfold writePackedMemProg
  simp only [StateTransitionSpec.clientHistory, bind_eq_freeMBind,
    StateTransitionSpec.runClient_bind, StateTransitionSpec.runClient_pure', runClient_minProg,
    runClient_maskProg, List.nil_append]
  set wOff := (d.1.2.2 / d.1.2.1) * d.1.1.2 + ((d.1.2.2 % d.1.2.1) * d.1.1.2) / d.1.2.1
  set bOff := ((d.1.2.2 % d.1.2.1) * d.1.1.2) % d.1.2.1
  set k₀ := min d.1.1.2 (d.1.2.1 - bOff)
  set k₁ := d.1.1.2 - k₀
  have hk0_bOff : k₀ + bOff ≤ d.1.2.1 := by
    have : k₀ ≤ d.1.2.1 - bOff := Nat.min_le_right _ _; omega
  have hk1_le : k₁ + 0 ≤ d.1.2.1 := by
    have : k₁ ≤ d.1.1.2 := Nat.sub_le _ _; omega
  have hsh0 : (((s.mem (d.1.1.1 + wOff) >>> bOff) &&& (2 ^ k₀ - 1)) ^^^
      (d.2 &&& (2 ^ k₀ - 1))) <<< bOff < 2 ^ d.1.2.1 := by
    refine shiftLeft_lt_two_pow_of_lt (a := k₀) (Nat.xor_lt_two_pow ?_ ?_) hk0_bOff <;>
    · rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos k₀)
  have hw0 : Fits d.1.2.1 (s.mem (d.1.1.1 + wOff) ^^^
      ((((s.mem (d.1.1.1 + wOff) >>> bOff) &&& (2 ^ k₀ - 1)) ^^^
        (d.2 &&& (2 ^ k₀ - 1))) <<< bOff)) :=
    Nat.xor_lt_two_pow (hwf.2 _) hsh0
  let mem₁ := Function.update s.mem (d.1.1.1 + wOff)
    (s.mem (d.1.1.1 + wOff) ^^^ ((((s.mem (d.1.1.1 + wOff) >>> bOff) &&& (2 ^ k₀ - 1)) ^^^
      (d.2 &&& (2 ^ k₀ - 1))) <<< bOff))
  have hm1 : mem₁ (d.1.1.1 + wOff + 1) < 2 ^ d.1.2.1 := by
    dsimp only [mem₁]; rw [Function.update_of_ne (by omega)]; exact hwf.2 _
  have hsh1 : (((mem₁ (d.1.1.1 + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)) ^^^
      ((d.2 >>> k₀) &&& (2 ^ k₁ - 1))) <<< 0 < 2 ^ d.1.2.1 := by
    refine shiftLeft_lt_two_pow_of_lt (a := k₁) (Nat.xor_lt_two_pow ?_ ?_) hk1_le <;>
    · rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos k₁)
  have hw1 : Fits d.1.2.1 (mem₁ (d.1.1.1 + wOff + 1) ^^^
      ((((mem₁ (d.1.1.1 + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)) ^^^
        ((d.2 >>> k₀) &&& (2 ^ k₁ - 1))) <<< 0)) :=
    Nat.xor_lt_two_pow hm1 hsh1
  change d.1.1.1 + wOff < s.frontier ∧
    ((d.1.1.1 + wOff < s.frontier ∧ Fits d.1.2.1 _) ∧
      d.1.1.1 + wOff + 1 < s.frontier ∧
      (d.1.1.1 + wOff + 1 < s.frontier ∧ Fits d.1.2.1 _) ∧ True)
  exact ⟨by omega, ⟨by omega, hw0⟩, by omega, ⟨by omega, hw1⟩, trivial⟩

theorem writePackedMemProg_realizesBounded :
    RealizesBounded .exact writePackedMemProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => ∃ N, w = d.1.2.1 ∧ 0 < w ∧ d.1.1.2 ≤ w ∧ d.1.2.2 < N ∧
        Fits w (d.1.1.1 + packedWords N d.1.1.2 w))
      (fun _ _ => 0) := by
  have _ := minProg_realizesBounded
  have _ := maskProg_realizesBounded
  realize
  all_goals
    rcases h with ⟨N, rfl, hw, hbw, hidx, hfit⟩
    unfold Fits at *
    try simp only [StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      runClient_minProg, runClient_maskProg]
    have hlt1 : wordOffset d.1.1.2 d.1.2.1 d.1.2.2 + 1 < packedWords N d.1.1.2 d.1.2.1 :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hb_lt : bitOffset d.1.1.2 d.1.2.1 d.1.2.2 < d.1.2.1 := bitOffset_lt hw
    have hrem : (d.1.2.2 % d.1.2.1) * d.1.1.2 < 2 ^ d.1.2.1 := mod_mul_lt_two_pow hw hbw d.1.2.2
    unfold wordOffset at hlt1
    unfold bitOffset at hb_lt
    try omega
  · set bOff := ((d.1.2.2 % d.1.2.1) * d.1.1.2) % d.1.2.1
    set k₀ := min d.1.1.2 (d.1.2.1 - bOff)
    have hk0_bOff : k₀ + bOff ≤ d.1.2.1 := by
      have : k₀ ≤ d.1.2.1 - bOff := Nat.min_le_right _ _; omega
    refine Nat.xor_lt_two_pow (hmem.2 _)
      (shiftLeft_lt_two_pow_of_lt (a := k₀) (Nat.xor_lt_two_pow ?_ ?_) hk0_bOff) <;>
    · rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos k₀)
  · set bOff := ((d.1.2.2 % d.1.2.1) * d.1.1.2) % d.1.2.1
    set k₀ := min d.1.1.2 (d.1.2.1 - bOff)
    have hk0_bOff : k₀ + bOff ≤ d.1.2.1 := by
      have : k₀ ≤ d.1.2.1 - bOff := Nat.min_le_right _ _; omega
    refine shiftLeft_lt_two_pow_of_lt (a := k₀) (Nat.xor_lt_two_pow ?_ ?_) hk0_bOff <;>
    · rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos k₀)
  · set wOff := (d.1.2.2 / d.1.2.1) * d.1.1.2 + ((d.1.2.2 % d.1.2.1) * d.1.1.2) / d.1.2.1
    set bOff := ((d.1.2.2 % d.1.2.1) * d.1.1.2) % d.1.2.1
    set k₀ := min d.1.1.2 (d.1.2.1 - bOff)
    set k₁ := d.1.1.2 - k₀
    have hk1_le : k₁ + 0 ≤ d.1.2.1 := (Nat.add_zero k₁).le.trans ((Nat.sub_le _ _).trans hbw)
    refine Nat.xor_lt_two_pow ?_
      (shiftLeft_lt_two_pow_of_lt (a := k₁) (Nat.xor_lt_two_pow ?_ ?_) hk1_le)
    · rw [Function.update_of_ne (by omega)]; exact hmem.2 _
    · rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos k₁)
    · rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos k₁)
  · set bOff := ((d.1.2.2 % d.1.2.1) * d.1.1.2) % d.1.2.1
    set k₀ := min d.1.1.2 (d.1.2.1 - bOff)
    set k₁ := d.1.1.2 - k₀
    have hk1_le : k₁ + 0 ≤ d.1.2.1 := (Nat.add_zero k₁).le.trans ((Nat.sub_le _ _).trans hbw)
    refine shiftLeft_lt_two_pow_of_lt (a := k₁) (Nat.xor_lt_two_pow ?_ ?_) hk1_le <;>
    · rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos k₁)

/-! ## 2. Array-level `Memory.Prog` leaf routines and `RDemonicExec` boundedness helper -/

/-- Any `RDemonicExec` from `x.Bounded w` witnesses at least one `y.Bounded w` satisfying `P`. -/
private theorem rDemonicExec_exists_bounded {B : Basis} {r w L_peak T : ℕ}
    {c : RCode B r} {x : RData r} {P : RData r → Prop}
    (h : RDemonicExec w L_peak c x T P) (hx : x.Bounded w) :
    ∃ y, P y ∧ y.Bounded w := by
  induction h with
  | op _ he hp => exact ⟨_, hp, hx.evalResizable he⟩
  | grow _ hfit hp =>
    have hg := demonicGrow_clear w _ 1 _ fun _ ha => hx.zero_above ha
    exact ⟨_, hp _ hg, hx.grow hfit hg⟩
  | shrink _ hk hp => exact ⟨_, hp, hx.shrink hk⟩
  | rand _ _ hp => exact ⟨_, hp 0 (Nat.zero_le _), hx.set (fits_zero w)⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨y₁, hy₁, hb₁⟩ := ih₁ hx
    exact ih₂ y₁ hy₁ hb₁
  | branch_pos _ _ ih | branch_neg _ _ ih => exact ih hx
  | loop_exit _ _ hp => exact ⟨_, hp, hx⟩
  | loop_iter _ _ _ ihb ihl =>
    obtain ⟨y₁, hy₁, hb₁⟩ := ihb hx
    exact ihl y₁ hy₁ hb₁
  | mono _ _ hPQ ih =>
    obtain ⟨y, hy, hb⟩ := ih hx
    exact ⟨y, hPQ y hy, hb⟩

/-- Deterministic `RDemonicExec ... (· = y)` automatically preserves `RData.Bounded w`. -/
private theorem rDemonicExec_eq_bounded {B : Basis} {r w L_peak T : ℕ}
    {c : RCode B r} {x y : RData r}
    (h : RDemonicExec w L_peak c x T (· = y)) (hx : x.Bounded w) : y.Bounded w := by
  obtain ⟨_, rfl, hb⟩ := rDemonicExec_exists_bounded h hx
  exact hb

/-- Write `[0, b, w]` into header words `[base, base + 3)`, taking `((base, b), w)`. -/
def initHeaderProg (d : (ℕ × ℕ) × ℕ) : Memory.Prog Unit := do
  Memory.write d.1.1 0
  Memory.write (d.1.1 + 1) d.1.2
  Memory.write (d.1.1 + 2) d.2

theorem initHeaderProg_realizesBounded :
    RealizesBounded .exact initHeaderProg (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => Fits w (d.1.1 + 2)) (fun _ _ => 0) := by
  realize
  all_goals unfold Fits at *; omega

/-- Compute `packedWords (n + 1) b w - packedWords n b w` from header `[n, b, w]` at `base`. -/
def pushDeltaProg (base : ℕ) : Memory.Prog ℕ := do
  let n ← Memory.read base
  let b ← Memory.read (base + 1)
  let w ← Memory.read (base + 2)
  let np1 ← pure (n + 1)
  let pw0 ← packedWordsProg ((b, w), n)
  let pw1 ← packedWordsProg ((b, w), np1)
  pure (pw1 - pw0)

theorem pushDeltaProg_realizesBounded :
    RealizesBounded .exact pushDeltaProg (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w base s =>
        w = s.mem (base + 2) ∧ 0 < w ∧ s.mem (base + 1) ≤ w ∧ Fits w (s.mem base + 1) ∧
          Fits w (base + 3 + packedWords (s.mem base + 1) (s.mem (base + 1)) w))
      (fun _ _ => 0) := by
  have _ := packedWordsProg_realizesBounded
  realize
  all_goals
    rcases h with ⟨rfl, hw, hbw, hfit_n, hfit⟩
    unfold Fits at *
    try simp only [StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      runClient_packedWordsProg _ hw]
    try
      have hstep := packedWords_succ_sub_le_one (n := s.mem d) hw hbw
      omega

/-- Append `val` at packed index `n = s.mem base` and increment `s.mem base`, taking
`(base, val)`. -/
def pushCommitProg (d : ℕ × ℕ) : Memory.Prog Unit := do
  let n ← Memory.read d.1
  let b ← Memory.read (d.1 + 1)
  let w ← Memory.read (d.1 + 2)
  let arrBase ← pure (d.1 + 3)
  writePackedMemProg (((arrBase, b), (w, n)), d.2)
  Memory.write d.1 (n + 1)

theorem pushCommitProg_realizesBounded :
    RealizesBounded .exact pushCommitProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d s =>
        w = s.mem (d.1 + 2) ∧ 0 < w ∧ s.mem (d.1 + 1) ≤ w ∧ Fits w (s.mem d.1 + 1) ∧
          Fits w (d.1 + 3 + packedWords (s.mem d.1 + 1) (s.mem (d.1 + 1)) w))
      (fun _ _ => 0) := by
  have _ := writePackedMemProg_realizesBounded
  realize
  all_goals
    rcases h with ⟨hw_eq, hw, hbw, hfit_n, hfit⟩
    unfold Fits at *
    try exact ⟨s.mem d.1 + 1, hw_eq, hw, hbw, Nat.lt_succ_self _, hfit⟩
    try omega

/-- Prepare `pop`: if `n = 0` return `((0, 0), 0)`; else read `last = readPacked ... (n - 1)`,
decrement `mem[base]` to `n - 1`, and return
`((1, last), packedWords n b w - packedWords (n - 1) b w)`. -/
def popPrepProg (base : ℕ) : Memory.Prog ((ℕ × ℕ) × ℕ) := do
  let n ← Memory.read base
  let b ← Memory.read (base + 1)
  let w ← Memory.read (base + 2)
  if n = 0 then
    pure ((0, 0), 0)
  else
    let nm1 ← pure (n - 1)
    let arrBase ← pure (base + 3)
    let lastVal ← readPackedMemProg ((arrBase, b), (w, nm1))
    let pw0 ← packedWordsProg ((b, w), n)
    let pw1 ← packedWordsProg ((b, w), nm1)
    Memory.write base nm1
    pure ((1, lastVal), pw0 - pw1)

theorem popPrepProg_realizesBounded :
    RealizesBounded .exact popPrepProg (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun w base s =>
        w = s.mem (base + 2) ∧ 0 < w ∧ s.mem (base + 1) ≤ w ∧
          Fits w (base + 3 + packedWords (s.mem base) (s.mem (base + 1)) w))
      (fun _ _ => 0) := by
  have _ := readPackedMemProg_realizesBounded
  have _ := packedWordsProg_realizesBounded
  realize
  all_goals
    rcases h with ⟨rfl, hw, hbw, hfit⟩
    unfold Fits at *
    have hlt1 : 2 ^ 0 < 2 ^ s.mem (d + 2) := Nat.pow_lt_pow_right (by decide) hw
    have hpw_le :
        packedWords (s.mem d - 1) (s.mem (d + 1)) (s.mem (d + 2)) ≤
          packedWords (s.mem d) (s.mem (d + 1)) (s.mem (d + 2)) := by
      unfold packedWords
      have hmul : (s.mem d - 1) * s.mem (d + 1) ≤ s.mem d * s.mem (d + 1) :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      exact Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 2
    try simp only [StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      runClient_readPackedMemProg, runClient_packedWordsProg _ hw]
    try refine ⟨s.mem d, trivial, hw, hbw, by omega, hfit⟩
    try omega

/-- Execute non-resizing `get` (`tag = 2`), `set` (`tag = 3`), or `length` (`tag = 4`), taking
`((base, tag), (arg1, arg2))`. -/
def getSetLenProg (d : (ℕ × ℕ) × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let n ← Memory.read d.1.1
  let b ← Memory.read (d.1.1 + 1)
  let w ← Memory.read (d.1.1 + 2)
  let arrBase ← pure (d.1.1 + 3)
  if d.1.2 = 2 then
    readPackedMemProg ((arrBase, b), (w, d.2.1))
  else if d.1.2 = 3 then
    writePackedMemProg (((arrBase, b), (w, d.2.1)), d.2.2)
    pure 0
  else
    pure n

theorem getSetLenProg_realizesBounded :
    RealizesBounded .exact getSetLenProg (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w d s =>
        w = s.mem (d.1.1 + 2) ∧ 0 < w ∧ s.mem (d.1.1 + 1) ≤ w ∧
          Fits w (d.1.1 + 3 + packedWords (s.mem d.1.1) (s.mem (d.1.1 + 1)) w) ∧
          ((d.1.2 = 2 ∨ d.1.2 = 3) → d.2.1 < s.mem d.1.1))
      (fun _ _ => 0) := by
  have _ := readPackedMemProg_realizesBounded
  have _ := writePackedMemProg_realizesBounded
  realize
  all_goals
    rcases h with ⟨hw_eq, hw, hbw, hfit, hidx_cond⟩
    unfold Fits at *
    try exact ⟨s.mem d.1.1, hw_eq, hw, hbw, hidx_cond (Or.inl hc), hfit⟩
    try exact ⟨s.mem d.1.1, hw_eq, hw, hbw, hidx_cond (Or.inr hc), hfit⟩
    try omega

/-! ## 3. Generic `RealizesBounded` → `RCode` leaf lifter (`emitLeafCode`) -/

/-- Maximum scratch register count required across all five `by realize` leaf certificates. -/
noncomputable def maxLeafScratch : ℕ :=
  max initHeaderProg_realizesBounded.choose <|
  max pushDeltaProg_realizesBounded.choose <|
  max pushCommitProg_realizesBounded.choose <|
  max popPrepProg_realizesBounded.choose
      getSetLenProg_realizesBounded.choose

/-- Register count `18 + maxLeafScratch` for `packedArraySubroutine`:
* `0`: `baseReg`
* `1`: `frReg` (tracks `x.frontier` at rest)
* `2..4`: `tagReg`, `arg1Reg`, `arg2Reg` (`input = true`; `2, 3` also `initParams` `b, w`)
* `5..6`: `outTagReg`, `outValReg`
* `7..12`: `kReg`, `resReg`, `curReg`, `idxReg`, `zReg`, `oReg` (`growZeroCode` / `shrinkCode`)
* `13..`: `by realize` output & scratch temporaries. -/
noncomputable abbrev arrRegs : ℕ := 18 + maxLeafScratch

private noncomputable def emitLeafCode {δ α : Type} [WordEncoding δ] [WordEncoding α]
    {p : δ → Memory.Prog α} {safe : ℕ → δ → Memory.State → Prop}
    (h : RealizesBounded .exact p (WordEncoding.encode (α := δ))
      (WordEncoding.encode (α := α)) safe (fun _ _ => 0))
    (hle_out : WordEncoding.width α ≤ 3) (hle_scr : h.choose ≤ maxLeafScratch)
    (src : Fin (WordEncoding.width δ) → Fin arrRegs) : RCode .exact arrRegs :=
  let C_spec := h.choose_spec.choose_spec
  let emit := C_spec.choose
  let fr : Fin arrRegs := ⟨1, by dsimp [arrRegs]; omega⟩
  let tmp : Fin (WordEncoding.width α + h.choose + 1) → Fin arrRegs :=
    fun j => ⟨13 + j.val, by have := j.isLt; dsimp [arrRegs]; omega⟩
  RCode.ofCode (emit fr src tmp)

private noncomputable def leafConst {δ α : Type} [WordEncoding δ] [WordEncoding α]
    {p : δ → Memory.Prog α} {safe : ℕ → δ → Memory.State → Prop}
    (h : RealizesBounded .exact p (WordEncoding.encode (α := δ))
      (WordEncoding.encode (α := α)) safe (fun _ _ => 0)) : ℕ :=
  h.choose_spec.choose

private theorem emitLeafCode_not_readsWidth {δ α : Type} [WordEncoding δ] [WordEncoding α]
    {p : δ → Memory.Prog α} {safe : ℕ → δ → Memory.State → Prop}
    (h : RealizesBounded .exact p (WordEncoding.encode (α := δ))
      (WordEncoding.encode (α := α)) safe (fun _ _ => 0))
    (hle_out : WordEncoding.width α ≤ 3) (hle_scr : h.choose ≤ maxLeafScratch)
    (src : Fin (WordEncoding.width δ) → Fin arrRegs)
    (hsrc_lt : ∀ i, (src i).val < 7) (hsrc_ne : ∀ i, (src i).val ≠ 1) :
    ¬(emitLeafCode h hle_out hle_scr src).ReadsWidth := by
  let fr : Fin arrRegs := ⟨1, by dsimp [arrRegs]; omega⟩
  let tmp : Fin (WordEncoding.width α + h.choose + 1) → Fin arrRegs :=
    fun j => ⟨13 + j.val, by have := j.isLt; dsimp [arrRegs]; omega⟩
  have hi : Function.Injective tmp := fun a b hab => Fin.ext (by
    have hv := congrArg Fin.val hab; dsimp [tmp] at hv; omega)
  have hd : ∀ i j, src i ≠ tmp j := fun i j hij => by
    have hv := congrArg Fin.val hij; have := hsrc_lt i; dsimp [tmp] at hv; omega
  have hf : ∀ j, tmp j ≠ fr := fun j hj => by
    have hv := congrArg Fin.val hj; dsimp [tmp, fr] at hv; omega
  have hs : ∀ i, src i ≠ fr := fun i hsi => hsrc_ne i (congrArg Fin.val hsi)
  have hspec := h.choose_spec.choose_spec.choose_spec fr src tmp hi hd hf hs
  simpa [emitLeafCode, fr, tmp] using hspec.1

private theorem emitLeafCode_exec {δ α : Type} [WordEncoding δ] [WordEncoding α]
    {p : δ → Memory.Prog α} {safe : ℕ → δ → Memory.State → Prop}
    (h : RealizesBounded .exact p (WordEncoding.encode (α := δ))
      (WordEncoding.encode (α := α)) safe (fun _ _ => 0))
    (hle_out : WordEncoding.width α ≤ 3) (hle_scr : h.choose ≤ maxLeafScratch)
    (src : Fin (WordEncoding.width δ) → Fin arrRegs)
    (hsrc_lt : ∀ i, (src i).val < 7) (hsrc_ne : ∀ i, (src i).val ≠ 1)
    {w L_peak : ℕ} {x : RData arrRegs} (d : δ)
    (hx : x.Bounded w) (hL_peak : x.frontier ≤ L_peak)
    (hfr : x.regs ⟨1, by dsimp [arrRegs]; omega⟩ = x.frontier)
    (hin : x.regs ∘ src = WordEncoding.encode d)
    (hsafe : safe w d { mem := x.mem, frontier := x.frontier })
    (hv : (Memory.spec w).ValidHistory { mem := x.mem, frontier := x.frontier }
      ((Memory.spec w).clientHistory { mem := x.mem, frontier := x.frontier } (p d)))
    (hnoalloc : ((Memory.spec w).clientState
      { mem := x.mem, frontier := x.frontier } (p d)).frontier = x.frontier) :
    let ms : Memory.State := { mem := x.mem, frontier := x.frontier }
    ∃ y : RData arrRegs,
      RDemonicExec w L_peak (emitLeafCode h hle_out hle_scr src) x
        (leafConst h * (memoryCost (p d) ms + 1)) (· = y) ∧
      y.Bounded w ∧
      y.frontier = x.frontier ∧
      y.mem = ((Memory.spec w).clientState ms (p d)).mem ∧
      (∀ (i : Fin arrRegs), i.val < 13 → y.regs i = x.regs i) ∧
      (∀ (j : Fin (WordEncoding.width α)),
        y.regs ⟨13 + j.val, by have := j.isLt; dsimp [arrRegs]; omega⟩ =
          WordEncoding.encode ((Memory.spec w).clientResult ms (p d)) j) := by
  intro ms
  let fr : Fin arrRegs := ⟨1, by dsimp [arrRegs]; omega⟩
  let tmp : Fin (WordEncoding.width α + h.choose + 1) → Fin arrRegs :=
    fun j => ⟨13 + j.val, by have := j.isLt; dsimp [arrRegs]; omega⟩
  have hi : Function.Injective tmp := fun a b hab => Fin.ext (by
    have hv := congrArg Fin.val hab; dsimp [tmp] at hv; omega)
  have hd : ∀ i j, src i ≠ tmp j := fun i j hij => by
    have hv := congrArg Fin.val hij; have := hsrc_lt i; dsimp [tmp] at hv; omega
  have hf : ∀ j, tmp j ≠ fr := fun j hj => by
    have hv := congrArg Fin.val hj; dsimp [tmp, fr] at hv; omega
  have hs : ∀ i, src i ≠ fr := fun i hsi => hsrc_ne i (congrArg Fin.val hsi)
  have hms_eq : memoryState fr x.toData = { mem := x.mem, frontier := x.frontier } := by
    ext <;> [rfl; exact hfr]
  obtain ⟨y_d, hdem, hm_eq, hout, hframe⟩ :=
    RDemonicExec.of_realizesBounded (C := h.choose_spec.choose)
      (output := WordEncoding.encode (α := α)) (work := fun _ _ => 0)
      (emit := fun {r} => h.choose_spec.choose_spec.choose (r := r))
      (fun {r} => h.choose_spec.choose_spec.choose_spec (r := r))
      fr src tmp hi hd hf hs d hx hL_peak hin
      (by rw [hms_eq]; exact hsafe) (by rw [hms_eq]; exact hv)
      (by rw [hms_eq, hnoalloc])
  have hdem' : RDemonicExec w L_peak (emitLeafCode h hle_out hle_scr src) x
      (leafConst h * (memoryCost (p d) ms + 1)) (· = ⟨y_d.regs, y_d.mem, x.frontier⟩) := by
    simpa [emitLeafCode, leafConst, fr, tmp, hms_eq, ms] using hdem
  refine ⟨⟨y_d.regs, y_d.mem, x.frontier⟩, hdem', rDemonicExec_eq_bounded hdem' hx, rfl, ?_, ?_, ?_⟩
  · have hm := congrArg Memory.State.mem hm_eq
    dsimp only at hm ⊢
    rw [hms_eq] at hm
    exact hm
  · intro i hi_lt
    by_cases hif : i = fr
    · subst hif
      have hm := congrArg Memory.State.frontier hm_eq
      change y_d.regs fr =
        ((Memory.spec w).clientState (memoryState fr x.toData) (p d)).frontier at hm
      dsimp only
      rw [hm, hms_eq, hnoalloc, hfr]
    · exact hframe i hif fun j hj => by
        have hv_eq := congrArg Fin.val hj; dsimp [tmp] at hv_eq; omega
  · intro j
    have hj_out := hout j
    simpa [tmp, hms_eq, ms] using hj_out

/-! ## 4. Resizable `b`-bit packed array specification & `SubroutineCode` -/

/-- Operations of a dynamic resizable `b`-bit packed array. -/
inductive PackedArrayOp : Type where
  | push (val : ℕ)
  | pop
  | get (idx : ℕ)
  | set (idx val : ℕ)
  | length
  deriving DecidableEq

/-- Typed result of each `PackedArrayOp`. -/
@[expose] def PackedArrayOp.Result : PackedArrayOp → Type
  | .push _ | .set _ _ => Unit
  | .pop => Option ℕ
  | .get _ | .length => ℕ

/-- Pure state-transition function of a resizable `b`-bit packed array over `List ℕ`. -/
@[expose] def packedArrayStepFn (s : List ℕ) : (o : PackedArrayOp) → List ℕ × o.Result
  | .push val => (s ++ [val], ())
  | .pop => if h : s = [] then ([], none) else (s.dropLast, some (s.getLast h))
  | .get idx => (s, s.getD idx 0)
  | .set idx val => (s.set idx val, ())
  | .length => (s, s.length)

/-- Per-operation validity at bit width `b` and machine word width `w`. -/
@[expose] def packedArrayValid (b w : ℕ) (s : List ℕ) : PackedArrayOp → Prop
  | .push val => val < 2 ^ b ∧ s.length + 1 < 2 ^ w
  | .pop => True
  | .get idx => idx < s.length ∧ idx < 2 ^ w
  | .set idx val => idx < s.length ∧ idx < 2 ^ w ∧ val < 2 ^ b
  | .length => True

/-- Functional `StateTransitionSpec` of a resizable `b`-bit packed array. -/
abbrev packedArraySpec (b w : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn packedArrayStepFn (packedArrayValid b w)

@[simp] theorem memoryCost_readPackedMemProg (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (readPackedMemProg d) s = 2 := by
  unfold readPackedMemProg
  simp only [bind_eq_freeMBind, memoryCost_bind, StateTransitionSpec.clientState,
    StateTransitionSpec.clientResult, runClient_minProg, runClient_maskProg,
    StateTransitionSpec.runClient_pure', memoryCost_minProg, memoryCost_maskProg]
  rfl

@[simp] theorem memoryCost_writePackedMemProg (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (writePackedMemProg d) s = 4 := by
  unfold writePackedMemProg
  simp only [bind_eq_freeMBind, memoryCost_bind, StateTransitionSpec.clientState,
    StateTransitionSpec.clientResult, runClient_minProg, runClient_maskProg,
    StateTransitionSpec.runClient_pure', memoryCost_minProg, memoryCost_maskProg]
  rfl

private def rBase : Fin arrRegs := ⟨0, by dsimp [arrRegs]; omega⟩
private def rFr : Fin arrRegs := ⟨1, by dsimp [arrRegs]; omega⟩
private def rTag : Fin arrRegs := ⟨2, by dsimp [arrRegs]; omega⟩
private def rArg1 : Fin arrRegs := ⟨3, by dsimp [arrRegs]; omega⟩
private def rArg2 : Fin arrRegs := ⟨4, by dsimp [arrRegs]; omega⟩
private def rOutT : Fin arrRegs := ⟨5, by dsimp [arrRegs]; omega⟩
/-- Primary output register of `packedArraySubroutine`. -/
def rOutV : Fin arrRegs := ⟨6, by dsimp [arrRegs]; omega⟩
private def rK : Fin arrRegs := ⟨7, by dsimp [arrRegs]; omega⟩
private def rRes : Fin arrRegs := ⟨8, by dsimp [arrRegs]; omega⟩
private def rCur : Fin arrRegs := ⟨9, by dsimp [arrRegs]; omega⟩
private def rIdx : Fin arrRegs := ⟨10, by dsimp [arrRegs]; omega⟩
private def rZero : Fin arrRegs := ⟨11, by dsimp [arrRegs]; omega⟩
private def rOne : Fin arrRegs := ⟨12, by dsimp [arrRegs]; omega⟩
private def rTmp0 : Fin arrRegs := ⟨13, by dsimp [arrRegs]; omega⟩
private def rTmp1 : Fin arrRegs := ⟨14, by dsimp [arrRegs]; omega⟩
private def rTmp2 : Fin arrRegs := ⟨15, by dsimp [arrRegs]; omega⟩

private noncomputable def initLeafCode : RCode .exact arrRegs :=
  emitLeafCode initHeaderProg_realizesBounded (by decide) (le_max_left _ _) ![rBase, rTag, rArg1]

private noncomputable def pushDeltaLeafCode : RCode .exact arrRegs :=
  emitLeafCode pushDeltaProg_realizesBounded (by decide)
    ((le_max_left _ _).trans (le_max_right _ _)) ![rBase]

private noncomputable def pushCommitLeafCode : RCode .exact arrRegs :=
  emitLeafCode pushCommitProg_realizesBounded (by decide)
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) ![rBase, rArg1]

private noncomputable def popPrepLeafCode : RCode .exact arrRegs :=
  emitLeafCode popPrepProg_realizesBounded (by decide)
    ((le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    ![rBase]

private noncomputable def getSetLenLeafCode : RCode .exact arrRegs :=
  emitLeafCode getSetLenProg_realizesBounded (by decide)
    ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    ![rBase, rTag, rArg1, rArg2]

/-- `SubroutineCode` for the resizable `b`-bit packed array over `Basis.exact`. -/
noncomputable def packedArraySubroutine :
    DataStructure.WordRAM.Resizable.SubroutineCode .exact arrRegs 2 where
  baseReg := rBase
  initParams := ⟨![rTag, rArg1], fun i j hij => by
    fin_cases i <;> fin_cases j <;> simp [rTag, rArg1] at hij ⊢⟩
  input i := decide (i.val = 2 ∨ i.val = 3 ∨ i.val = 4)
  input_baseReg_false := by decide
  initCode :=
    .seq (.op (.const rK 5))
    (.seq (growZeroCode rK rBase rCur rIdx rZero rOne)
    (.seq (.op (.exactBin .add rFr rBase rK)) initLeafCode))
  code :=
    .seq (.op (.const rZero 0))
    (.seq (.op (.const rOne 1))
    (.branch (.eq rTag rZero)
      (.seq pushDeltaLeafCode
      (.seq (.op (.copy rK rTmp0))
      (.seq (growZeroCode rK rRes rCur rIdx rZero rOne)
      (.seq (.op (.exactBin .add rFr rFr rK)) pushCommitLeafCode))))
      (.branch (.eq rTag rOne)
        (.seq popPrepLeafCode
        (.seq (.op (.copy rOutT rTmp0))
        (.seq (.op (.copy rOutV rTmp1))
        (.seq (.op (.copy rK rTmp2))
        (.seq (shrinkCode rK rIdx rZero rOne)
              (.op (.exactBin .sub rFr rFr rK)))))))
        (.seq getSetLenLeafCode (.op (.copy rOutV rTmp0))))))

/-- `packedArraySubroutine` never inspects the ambient word width `w` (`¬ReadsWidth`). -/
theorem packedArraySubroutine_not_readsWidth : ¬packedArraySubroutine.ReadsWidth := by
  unfold DataStructure.WordRAM.Resizable.SubroutineCode.ReadsWidth
  have h1 := emitLeafCode_not_readsWidth initHeaderProg_realizesBounded (by decide)
    (le_max_left _ _) ![rBase, rTag, rArg1]
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
  have h2 := emitLeafCode_not_readsWidth pushDeltaProg_realizesBounded (by decide)
    ((le_max_left _ _).trans (le_max_right _ _)) ![rBase]
    (fun i => by fin_cases i; decide) (fun i => by fin_cases i; decide)
  have h3 := emitLeafCode_not_readsWidth pushCommitProg_realizesBounded (by decide)
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) ![rBase, rArg1]
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
  have h4 := emitLeafCode_not_readsWidth popPrepProg_realizesBounded (by decide)
    ((le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    ![rBase] (fun i => by fin_cases i; decide) (fun i => by fin_cases i; decide)
  have h5 := emitLeafCode_not_readsWidth getSetLenProg_realizesBounded (by decide)
    ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
    ![rBase, rTag, rArg1, rArg2]
    (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
  simp [packedArraySubroutine, initLeafCode, pushDeltaLeafCode, pushCommitLeafCode,
    popPrepLeafCode, getSetLenLeafCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    growZeroCode_not_readsWidth, shrinkCode_not_readsWidth, h1, h2, h3, h4, h5]

/-- Representation invariant for `packedArrayImpl` at `[base, base + 3 + packedWords s.length b w)`:
resting hardware frontier equals `base + 3 + packedWords s.length b w`, header `[base, base + 3)`
stores `[s.length, b, w]`, and packed entries `[0, s.length)` decode to `s`. -/
def packedArrayRep (b w base : ℕ) (s : List ℕ) (x : RData arrRegs) : Prop :=
  x.Bounded w ∧
  x.regs rBase = base ∧
  x.regs rFr = x.frontier ∧
  x.frontier = base + 3 + packedWords s.length b w ∧
  x.mem base = s.length ∧
  x.mem (base + 1) = b ∧
  x.mem (base + 2) = w ∧
  ∀ (i : ℕ) (hi : i < s.length), readPacked (base + 3) b w x.mem i = s[i]

/-- Standalone argument encoder for `PackedArrayOp`. -/
def packedArrayEncode : PackedArrayOp → Fin arrRegs → ℕ
  | .push val, i => if i.val = 2 then 0 else if i.val = 3 then val else 0
  | .pop, i => if i.val = 2 then 1 else 0
  | .get idx, i => if i.val = 2 then 2 else if i.val = 3 then idx else 0
  | .set idx val, i =>
      if i.val = 2 then 3 else if i.val = 3 then idx else if i.val = 4 then val else 0
  | .length, i => if i.val = 2 then 4 else 0

/-- Register-agreement predicate for `PackedArrayOp`. -/
def packedArrayArgMatch (o : PackedArrayOp) (regs : Fin arrRegs → ℕ) : Prop :=
  regs rTag = packedArrayEncode o rTag ∧
  regs rArg1 = packedArrayEncode o rArg1 ∧
  regs rArg2 = packedArrayEncode o rArg2

/-- Output decoder for `PackedArrayOp`. -/
def packedArrayDecode : (o : PackedArrayOp) → (Fin arrRegs → ℕ) → Option o.Result
  | .push _, _ => some ()
  | .pop, regs => some (if regs rOutT = 0 then none else some (regs rOutV))
  | .get _, regs => some (regs rOutV)
  | .set _ _, _ => some ()
  | .length, regs => some (regs rOutV)

/-- Worst-case `O(1)` instruction bound for `packedArraySubroutine.initCode`. -/
noncomputable def packedArrayInitTime : ℕ :=
  35 + 4 * leafConst initHeaderProg_realizesBounded

/-- Worst-case `O(1)` instruction bound per operation of `packedArraySubroutine.code`. -/
noncomputable def packedArrayCharge : ℕ :=
  30 + 4 * leafConst pushDeltaProg_realizesBounded +
    9 * leafConst pushCommitProg_realizesBounded +
    7 * leafConst popPrepProg_realizesBounded +
    8 * leafConst getSetLenProg_realizesBounded

private theorem packedWords_zero_eq_two {b w : ℕ} (hw : 0 < w) : packedWords 0 b w = 2 := by
  unfold packedWords
  rw [Nat.zero_mul, Nat.zero_add, Nat.div_eq_of_lt (by omega : w - 1 < w)]

private theorem packedArray_init_exec {b w base : ℕ} (hw : 3 ≤ w) (hbw : b ≤ w)
    {x₀ : RData arrRegs} (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hpar : ∀ j, x₀.regs (packedArraySubroutine.initParams j) = (![b, w] : Fin 2 → ℕ) j)
    (hfit₀ : Fits w (base + (3 + packedWords ([] : List ℕ).length b w))) :
    ∃ (y : RData arrRegs) (n : ℕ),
      n ≤ packedArrayInitTime ∧
      RDemonicExec w (base + (3 + packedWords ([] : List ℕ).length b w))
        packedArraySubroutine.initCode x₀ n (· = y) ∧
      packedArrayRep b w base [] y ∧
      ∀ addr < base, y.mem addr = x₀.mem addr := by
  have hw0 : 0 < w := by omega
  have hpw0 : packedWords 0 b w = 2 := packedWords_zero_eq_two hw0
  have hfit5 : Fits w (base + 5) := by simpa [hpw0, Nat.add_assoc] using hfit₀
  have hpow3 : 8 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
  have h1 : Fits w 1 := by unfold Fits; omega
  have h5 : Fits w 5 := by unfold Fits; omega
  have hfit_w : Fits w w := Nat.lt_two_pow_self
  have hfit_b : Fits w b := Nat.lt_of_le_of_lt hbw hfit_w
  set L_peak := base + (3 + packedWords 0 b w)
  have hL_eq : L_peak = base + 5 := by simp [L_peak, hpw0]
  set x₁ := x₀.set rK 5
  have e1 : RDemonicExec (B := .exact) w L_peak (.op (.const rK 5)) x₀ 1 (· = x₁) :=
    RDemonicExec.const (by omega) h5
  have hx₁b : x₁.Bounded w := hx₀.set h5
  have hnodup : [rK, rBase, rCur, rIdx, rZero, rOne].Nodup := by
    simp [rK, rBase, rCur, rIdx, rZero, rOne, Fin.ext_iff]
  have e2 := growZeroCode_exec (L_peak := L_peak) (count := rK) (result := rBase) (cur := rCur)
    (idx := rIdx) (zero := rZero) (one := rOne) hx₁b hnodup h1
    (by simp [x₁, rK, hfr₀, hL_eq]) (by simpa [x₁, rK, hfr₀] using hfit5)
  set x₂ := growZeroPost rK rBase rCur rIdx rZero rOne x₁
  have hx₂b : x₂.Bounded w := rDemonicExec_eq_bounded e2 hx₁b
  have hx₂_base : x₂.regs rBase = base := by
    simp [x₂, growZeroPost, x₁, rBase, rK, rCur, rIdx, rZero, rOne, Fin.ext_iff, hfr₀]
  have hx₂_k : x₂.regs rK = 5 := by
    simp [x₂, growZeroPost, x₁, rBase, rK, rCur, rIdx, rZero, rOne, Fin.ext_iff]
  have hx₂_tag : x₂.regs rTag = b := by
    have hp0 := hpar 0
    simpa [packedArraySubroutine, x₂, growZeroPost, x₁, rTag, rBase, rK, rCur, rIdx, rZero, rOne,
      Fin.ext_iff] using hp0
  have hx₂_arg1 : x₂.regs rArg1 = w := by
    have hp1 := hpar 1
    simpa [packedArraySubroutine, x₂, growZeroPost, x₁, rArg1, rBase, rK, rCur, rIdx, rZero, rOne,
      Fin.ext_iff] using hp1
  have hx₂_fr : x₂.frontier = base + 5 := by simp [x₂, growZeroPost, x₁, rK, hfr₀]
  set x₃ := x₂.set rFr (base + 5)
  have e3 : RDemonicExec w L_peak (.op (.exactBin .add rFr rBase rK)) x₂ 1 (· = x₃) :=
    RDemonicExec.exactBin (by omega) (by simp [BinOp.evalExact, hx₂_base, hx₂_k]) hfit5
  have hx₃b : x₃.Bounded w := hx₂b.set hfit5
  have hne_bf : rBase ≠ rFr := fun h => by
    have := congrArg Fin.val h; dsimp [rBase, rFr] at this; omega
  have hne_tf : rTag ≠ rFr := fun h => by
    have := congrArg Fin.val h; dsimp [rTag, rFr] at this; omega
  have hne_af : rArg1 ≠ rFr := fun h => by
    have := congrArg Fin.val h; dsimp [rArg1, rFr] at this; omega
  have hin : x₃.regs ∘ ![rBase, rTag, rArg1] =
      WordEncoding.encode (α := (ℕ × ℕ) × ℕ) ((base, b), w) := by
    funext i; fin_cases i
    · change x₃.regs rBase = base; simp [x₃, RData.set, Function.update_of_ne hne_bf, hx₂_base]
    · change x₃.regs rTag = b; simp [x₃, RData.set, Function.update_of_ne hne_tf, hx₂_tag]
    · change x₃.regs rArg1 = w; simp [x₃, RData.set, Function.update_of_ne hne_af, hx₂_arg1]
  have hv_init : (Memory.spec w).ValidHistory { mem := x₃.mem, frontier := x₃.frontier }
      ((Memory.spec w).clientHistory { mem := x₃.mem, frontier := x₃.frontier }
        (initHeaderProg ((base, b), w))) := by
    change (base < x₃.frontier ∧ Fits w 0) ∧
      (base + 1 < x₃.frontier ∧ Fits w b) ∧
      (base + 2 < x₃.frontier ∧ Fits w w) ∧ True
    simp only [x₃, RData.set_frontier, hx₂_fr]
    exact ⟨⟨by omega, fits_zero w⟩, ⟨by omega, hfit_b⟩, ⟨by omega, hfit_w⟩, trivial⟩
  obtain ⟨y, e4, hyb, hy_fr, hy_mem, hy_regs, _⟩ :=
    emitLeafCode_exec initHeaderProg_realizesBounded (by decide) (le_max_left _ _)
      ![rBase, rTag, rArg1]
      (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
      (L_peak := L_peak) ((base, b), w) hx₃b (by simp [x₃, hx₂_fr, hL_eq])
      (by simp [x₃, rFr, hx₂_fr]) hin
      (by change base + 2 < 2 ^ w; unfold Fits at hfit5; omega) hv_init rfl
  have hex_all : RDemonicExec w L_peak packedArraySubroutine.initCode x₀
      (1 + ((5 * x₁.regs rK + 6) + (1 + leafConst initHeaderProg_realizesBounded * (3 + 1))))
      (· = y) :=
    e1.seq_eq (e2.seq_eq (e3.seq_eq e4))
  have hx₁_k : x₁.regs rK = 5 := by simp [x₁]
  have hy_mem_eq : y.mem =
      Function.update (Function.update (Function.update x₀.mem base 0) (base + 1) b)
        (base + 2) w := hy_mem
  refine ⟨y, _, ?_, hex_all, ?_, ?_⟩
  · simp only [hx₁_k, packedArrayInitTime]; omega
  · refine ⟨hyb, ?_, ?_, ?_, ?_, ?_, ?_, fun _ hi => by simp at hi⟩
    · rw [hy_regs rBase (by decide)]; simp [x₃, RData.set, Function.update_of_ne hne_bf, hx₂_base]
    · rw [hy_regs rFr (by decide), hy_fr]; simp [x₃, hx₂_fr]
    · rw [hy_fr]; simp [x₃, hx₂_fr, hpw0, Nat.add_assoc]
    · rw [hy_mem_eq]; simp
    · rw [hy_mem_eq]; simp
    · rw [hy_mem_eq]; simp
  · intro addr hlt
    rw [hy_mem_eq]
    simp [Function.update_of_ne (by omega : addr ≠ base + 2),
      Function.update_of_ne (by omega : addr ≠ base + 1),
      Function.update_of_ne (by omega : addr ≠ base)]

/-- Per-operation peak word footprint of `packedArraySubroutine.code` relative to `base`. -/
@[expose] def packedArrayPeakSpace (b w : ℕ) (s : List ℕ) : PackedArrayOp → ℕ
  | .push _ => 3 + packedWords (s.length + 1) b w
  | _ => 3 + packedWords s.length b w

private theorem reg_ne {i j : Fin arrRegs} (h : i.val ≠ j.val) : i ≠ j :=
  fun heq => h (congrArg Fin.val heq)

@[simp] private theorem memory_stepFn_read (w : ℕ) (s : Memory.State) (a : ℕ) :
    (Memory.spec w).stepFn s (.read a) = (s, s.mem a) := rfl

@[simp] private theorem memory_stepFn_write (w : ℕ) (s : Memory.State) (a v : ℕ) :
    (Memory.spec w).stepFn s (.write a v) =
      ({ mem := Function.update s.mem a v, frontier := s.frontier }, ()) := rfl

private theorem packedArray_push_exec {b w base val : ℕ} (hw : 3 ≤ w) (hbw : b ≤ w)
    {s : List ℕ} {x : RData arrRegs}
    (hrep : packedArrayRep b w base s x)
    (hv : packedArrayValid b w s (.push val))
    (harg : packedArrayArgMatch (.push val) x.regs)
    (hfit : Fits w (base + packedArrayPeakSpace b w s (.push val))) :
    ∃ (y : RData arrRegs) (n : ℕ),
      n ≤ packedArrayCharge ∧
      RDemonicExec w (base + packedArrayPeakSpace b w s (.push val))
        packedArraySubroutine.code x n (· = y) ∧
      packedArrayDecode (.push val) y.regs = some () ∧
      packedArrayRep b w base (s ++ [val]) y ∧
      ∀ addr < base, y.mem addr = x.mem addr := by
  obtain ⟨hxb, hx_base, hx_rfr, hx_fr, hm0, hm1, hm2, hm_arr⟩ := hrep
  obtain ⟨hval_lt, hn1_lt⟩ := hv
  have hw0 : 0 < w := by omega
  have hpow3 : 8 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
  have h1 : Fits w 1 := by unfold Fits; omega
  have hstep_pw := packedWords_succ_sub_le_one (n := s.length) hw0 hbw
  set L_peak := base + (3 + packedWords (s.length + 1) b w)
  have hfit_peak : Fits w (base + 3 + packedWords (s.length + 1) b w) := by
    simpa [packedArrayPeakSpace, Nat.add_assoc] using hfit
  have hL_cur : x.frontier ≤ L_peak := by rw [hx_fr]; omega
  set x₁ := (x.set rZero 0).set rOne 1
  have e_z : RDemonicExec (B := .exact) w L_peak (.op (.const rZero 0)) x 1
      (· = x.set rZero 0) := RDemonicExec.const hL_cur (fits_zero w)
  have e_o : RDemonicExec (B := .exact) w L_peak (.op (.const rOne 1)) (x.set rZero 0) 1
      (· = x₁) := RDemonicExec.const hL_cur h1
  have hx₁b : x₁.Bounded w := (hxb.set (fits_zero w)).set h1
  have hx₁_tag : x₁.regs rTag = 0 := by
    rw [show x₁.regs rTag = x.regs rTag from by
      simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rTag.val ≠ rOne.val)),
        Function.update_of_ne (reg_ne (by decide : rTag.val ≠ rZero.val))]]
    simpa [packedArrayEncode, rTag] using harg.1
  have hx₁_z : x₁.regs rZero = 0 := by
    simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rZero.val ≠ rOne.val))]
  have hx₁_base : x₁.regs rBase = base := by
    simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOne.val)),
      Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rZero.val)), hx_base]
  have hx₁_arg1 : x₁.regs rArg1 = val := by
    rw [show x₁.regs rArg1 = x.regs rArg1 from by
      simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rArg1.val ≠ rOne.val)),
        Function.update_of_ne (reg_ne (by decide : rArg1.val ≠ rZero.val))]]
    simpa [packedArrayEncode, rArg1] using harg.2.1
  have hx₁_rfr : x₁.regs rFr = x₁.frontier := by
    simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rOne.val)),
      Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rZero.val)), hx_rfr]
  have hp0_pos : 0 < packedWords s.length b w := Nat.succ_pos _
  have hrun_del : (Memory.spec w).runClient { mem := x₁.mem, frontier := x₁.frontier }
      (pushDeltaProg base) =
      (packedWords (s.length + 1) b w - packedWords s.length b w,
        { mem := x₁.mem, frontier := x₁.frontier },
        [.read base, .read (base + 1), .read (base + 2)]) := by
    unfold pushDeltaProg Memory.read
    simp only [bind_eq_freeMBind, StateTransitionSpec.runClient_bind,
      StateTransitionSpec.runClient_lift, StateTransitionSpec.runClient_pure',
      memory_stepFn_read, List.nil_append, List.singleton_append]
    have hmem2 : x₁.mem (base + 2) = w := hm2
    have hmem1 : x₁.mem (base + 1) = b := hm1
    have hmem0 : x₁.mem base = s.length := hm0
    rw [hmem0, hmem1, hmem2]
    simp only [runClient_packedWordsProg _ hw0, List.nil_append]
  have hv_delta : (Memory.spec w).ValidHistory { mem := x₁.mem, frontier := x₁.frontier }
      ((Memory.spec w).clientHistory { mem := x₁.mem, frontier := x₁.frontier }
        (pushDeltaProg base)) := by
    rw [StateTransitionSpec.clientHistory, hrun_del]
    change base < x.frontier ∧ base + 1 < x.frontier ∧ base + 2 < x.frontier ∧ True
    rw [hx_fr]; exact ⟨by omega, by omega, by omega, trivial⟩
  obtain ⟨x₂, e_del, hx₂b, hx₂_fr, hx₂_mem, hx₂_regs, hx₂_out⟩ :=
    emitLeafCode_exec pushDeltaProg_realizesBounded (by decide)
      ((le_max_left _ _).trans (le_max_right _ _)) ![rBase]
      (fun i => by fin_cases i; decide) (fun i => by fin_cases i; decide)
      (L_peak := L_peak) base hx₁b hL_cur hx₁_rfr
      (by funext i; fin_cases i; exact hx₁_base)
      ⟨hm2.symm, hw0, by dsimp only; change x.mem (base + 1) ≤ w; rw [hm1]; exact hbw,
        by dsimp only; change Fits w (x.mem base + 1); rw [hm0]; exact hn1_lt,
        by dsimp only
           change Fits w (base + 3 + packedWords (x.mem base + 1) (x.mem (base + 1)) w)
           rw [hm0, hm1]; exact hfit_peak⟩
      hv_delta (by rw [StateTransitionSpec.clientState, hrun_del])
  set delta := packedWords (s.length + 1) b w - packedWords s.length b w
  have hx₂_tmp0 : x₂.regs rTmp0 = delta := by
    have h0 := hx₂_out 0
    rw [StateTransitionSpec.clientResult, hrun_del] at h0
    exact h0
  set x₃ := x₂.set rK (x₂.regs rTmp0)
  have e_cp : RDemonicExec (B := .exact) w L_peak (.op (.copy rK rTmp0)) x₂ 1 (· = x₃) :=
    RDemonicExec.copy (by rw [hx₂_fr]; exact hL_cur)
  have hx₃b : x₃.Bounded w := hx₂b.set (hx₂b.regs_fits rTmp0)
  have hx₃_k : x₃.regs rK = delta := by simp [x₃, hx₂_tmp0]
  have hx₃_fr : x₃.frontier = base + 3 + packedWords s.length b w := by
    rw [RData.set_frontier, hx₂_fr]; exact hx_fr
  have hnodup : [rK, rRes, rCur, rIdx, rZero, rOne].Nodup := by
    simp [rK, rRes, rCur, rIdx, rZero, rOne, Fin.ext_iff]
  have hfr_add : x₃.frontier + x₃.regs rK = base + 3 + packedWords (s.length + 1) b w := by
    rw [hx₃_fr, hx₃_k]; omega
  have e_gr := growZeroCode_exec (L_peak := L_peak) (count := rK) (result := rRes) (cur := rCur)
    (idx := rIdx) (zero := rZero) (one := rOne) hx₃b hnodup h1
    (by rw [hfr_add]; dsimp [L_peak]; omega) (by rw [hfr_add]; exact hfit_peak)
  set x₄ := growZeroPost rK rRes rCur rIdx rZero rOne x₃
  have hx₄b : x₄.Bounded w := rDemonicExec_eq_bounded e_gr hx₃b
  have hx₄_fr : x₄.frontier = base + 3 + packedWords (s.length + 1) b w := by
    change x₃.frontier + x₃.regs rK = _; exact hfr_add
  have hx₄_rfr : x₄.regs rFr = base + 3 + packedWords s.length b w := by
    have h4 : x₄.regs rFr = x₃.regs rFr := by
      simp [x₄, growZeroPost, rFr, rRes, rCur, rIdx, rZero, rOne, Fin.ext_iff]
    rw [h4, show x₃.regs rFr = x₂.regs rFr from by
      simp [x₃, RData.set, Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rK.val))],
      hx₂_regs rFr (by decide), hx₁_rfr]; exact hx_fr
  have hx₄_k : x₄.regs rK = delta := by
    have h4 : x₄.regs rK = x₃.regs rK := by
      simp [x₄, growZeroPost, rK, rRes, rCur, rIdx, rZero, rOne, Fin.ext_iff]
    rw [h4, hx₃_k]
  have hx₄_base : x₄.regs rBase = base := by
    have h4 : x₄.regs rBase = x₃.regs rBase := by
      simp [x₄, growZeroPost, rBase, rRes, rCur, rIdx, rZero, rOne, Fin.ext_iff]
    rw [h4, show x₃.regs rBase = x₂.regs rBase from by
      simp [x₃, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rK.val))],
      hx₂_regs rBase (by decide), hx₁_base]
  have hx₄_arg1 : x₄.regs rArg1 = val := by
    have h4 : x₄.regs rArg1 = x₃.regs rArg1 := by
      simp [x₄, growZeroPost, rArg1, rRes, rCur, rIdx, rZero, rOne, Fin.ext_iff]
    rw [h4, show x₃.regs rArg1 = x₂.regs rArg1 from by
      simp [x₃, RData.set, Function.update_of_ne (reg_ne (by decide : rArg1.val ≠ rK.val))],
      hx₂_regs rArg1 (by decide), hx₁_arg1]
  set x₅ := x₄.set rFr (base + 3 + packedWords (s.length + 1) b w)
  have e_fr : RDemonicExec (B := .exact) w L_peak (.op (.exactBin .add rFr rFr rK)) x₄ 1
      (· = x₅) :=
    RDemonicExec.exactBin (by rw [hx₄_fr]; dsimp [L_peak]; omega)
      (by simp only [BinOp.evalExact, hx₄_rfr, hx₄_k]; congr 1; omega) hfit_peak
  have hx₅b : x₅.Bounded w := hx₄b.set hfit_peak
  have hx₅_mem : x₅.mem = x.mem := by
    rw [StateTransitionSpec.clientState, hrun_del] at hx₂_mem
    exact hx₂_mem
  have hrun_com : (Memory.spec w).runClient { mem := x₅.mem, frontier := x₅.frontier }
      (pushCommitProg (base, val)) =
      ((), { mem := Function.update (writePacked (base + 3) b w x.mem s.length val) base
               (s.length + 1),
             frontier := x₅.frontier },
        [.read base, .read (base + 1), .read (base + 2)] ++
          ((Memory.spec w).clientHistory { mem := x.mem, frontier := x₅.frontier }
            (writePackedMemProg (((base + 3, b), (w, s.length)), val))) ++
          [.write base (s.length + 1)]) := by
    unfold pushCommitProg Memory.read Memory.write
    simp only [bind_eq_freeMBind, StateTransitionSpec.runClient_bind,
      StateTransitionSpec.runClient_lift, StateTransitionSpec.runClient_pure',
      memory_stepFn_read, memory_stepFn_write, List.nil_append, List.singleton_append]
    rw [hx₅_mem, hm0, hm1, hm2]
    have hcs := clientState_writePackedMemProg w (((base + 3, b), (w, s.length)), val)
      { mem := x.mem, frontier := x₅.frontier }
    dsimp only [StateTransitionSpec.clientState] at hcs
    rw [hcs]
    simp
  have hv_com : (Memory.spec w).ValidHistory { mem := x₅.mem, frontier := x₅.frontier }
      ((Memory.spec w).clientHistory { mem := x₅.mem, frontier := x₅.frontier }
        (pushCommitProg (base, val))) := by
    rw [StateTransitionSpec.clientHistory, hrun_com, hx₅_mem]
    have hwf5 : Memory.WellFormed w { mem := x.mem, frontier := x₅.frontier } :=
      ⟨hx₅b.frontier_fits, hx₅_mem ▸ hx₅b.mem_fits⟩
    have hvw := validHistory_writePackedMemProg (w := w)
      (d := (((base + 3, b), (w, s.length)), val)) (N := s.length + 1)
      (s := { mem := x.mem, frontier := x₅.frontier })
      rfl hw0 hbw (Nat.lt_succ_self _) hwf5 (by simp [x₅, hx₄_fr])
    have hfr5 : x₅.frontier = base + 3 + packedWords (s.length + 1) b w := hx₄_fr
    have hp1_pos : 0 < packedWords (s.length + 1) b w := Nat.succ_pos _
    rw [List.append_assoc]
    change base < x₅.frontier ∧ base + 1 < x₅.frontier ∧ base + 2 < x₅.frontier ∧ _
    refine ⟨by omega, by omega, by omega, ?_⟩
    have hvh_app : ∀ (hist : List (Memory.spec w).Op) (ms : Memory.State),
        (Memory.spec w).ValidHistory ms hist →
        ms.frontier = x₅.frontier →
        (∀ op ∈ hist, ∀ a v, op ≠ .alloc a ∧ op ≠ .allocDirty v) →
        (Memory.spec w).ValidHistory ms (hist ++ [.write base (s.length + 1)]) := by
      intro hist ms hvh hfr_ms hnoa
      induction hist generalizing ms with
      | nil => exact ⟨⟨by rw [hfr_ms]; omega, hn1_lt⟩, trivial⟩
      | cons op rest ih =>
        refine ⟨hvh.1, ih _ hvh.2 ?_ fun o ho => hnoa o (List.mem_cons_of_mem _ ho)⟩
        cases op with
        | read _ => exact hfr_ms
        | write _ _ => exact hfr_ms
        | alloc a => exact absurd rfl (hnoa _ (.head _) a 0).1
        | allocDirty v => exact absurd rfl (hnoa _ (.head _) 0 v).2
    refine hvh_app _ _ hvw rfl ?_
    unfold writePackedMemProg Memory.read Memory.write
    simp only [StateTransitionSpec.clientHistory, bind_eq_freeMBind,
      StateTransitionSpec.runClient_bind, StateTransitionSpec.runClient_lift,
      StateTransitionSpec.runClient_pure', runClient_minProg, runClient_maskProg, List.nil_append,
      List.singleton_append]
    intro op hop a v
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl <;> exact ⟨nofun, nofun⟩
  obtain ⟨y, e_cm, hyb, hy_fr, hy_mem, hy_regs, _⟩ :=
    emitLeafCode_exec pushCommitProg_realizesBounded (by decide)
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) ![rBase, rArg1]
      (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
      (L_peak := L_peak) (base, val) hx₅b (by simp [x₅, hx₄_fr, L_peak, Nat.add_assoc])
      (by simp [x₅, rFr, hx₄_fr])
      (by funext i; fin_cases i
          · change x₅.regs rBase = base
            simp [x₅, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rFr.val)),
              hx₄_base]
          · change x₅.regs rArg1 = val
            simp [x₅, RData.set, Function.update_of_ne (reg_ne (by decide : rArg1.val ≠ rFr.val)),
              hx₄_arg1])
      ⟨by dsimp only; rw [hx₅_mem, hm2], hw0, by dsimp only; rw [hx₅_mem, hm1]; exact hbw,
        by dsimp only; rw [hx₅_mem, hm0]; exact hn1_lt,
        by dsimp only; rw [hx₅_mem, hm0, hm1]; exact hfit_peak⟩
      hv_com (by rw [StateTransitionSpec.clientState, hrun_com])
  have e_push := e_del.seq_eq (e_cp.seq_eq (e_gr.seq_eq (e_fr.seq_eq e_cm)))
  have e_all : RDemonicExec w L_peak packedArraySubroutine.code x _ (· = y) :=
    e_z.seq_eq (e_o.seq_eq (RDemonicExec.branch_pos
      (by simp [Cond.Holds, hx₁_tag, hx₁_z]) e_push))
  have hm_cost_del : memoryCost (pushDeltaProg base) { mem := x₁.mem, frontier := x₁.frontier } =
      3 := by
    unfold pushDeltaProg Memory.read
    simp only [bind_eq_freeMBind, memoryCost_bind, StateTransitionSpec.clientState,
      StateTransitionSpec.clientResult, StateTransitionSpec.runClient_lift,
      StateTransitionSpec.runClient_pure', memoryCost_pure, memoryCost_packedWordsProg]
    rfl
  have hm_cost_cm : memoryCost (pushCommitProg (base, val))
      { mem := x₅.mem, frontier := x₅.frontier } = 8 := by
    unfold pushCommitProg Memory.read Memory.write
    simp only [bind_eq_freeMBind, memoryCost_bind, StateTransitionSpec.clientState,
      StateTransitionSpec.clientResult, StateTransitionSpec.runClient_lift,
      StateTransitionSpec.runClient_pure', memoryCost_pure, memoryCost_writePackedMemProg]
    rfl
  have hy_mem_eq : y.mem =
      Function.update (writePacked (base + 3) b w x.mem s.length val) base (s.length + 1) := by
    rw [StateTransitionSpec.clientState, hrun_com] at hy_mem; exact hy_mem
  refine ⟨y, _, ?_, e_all, rfl, ?_, ?_⟩
  · simp only [hm_cost_del, hm_cost_cm, hx₃_k, packedArrayCharge]; omega
  · refine ⟨hyb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hy_regs rBase (by decide)]
      simp [x₅, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rFr.val)),
        hx₄_base]
    · rw [hy_regs rFr (by decide), hy_fr]; simp [x₅, hx₄_fr]
    · rw [hy_fr]; simp [x₅, hx₄_fr]
    · rw [hy_mem_eq]; simp
    · rw [hy_mem_eq, Function.update_of_ne (by omega),
        writePacked_outside hw0 x.mem (Nat.lt_succ_self _) val (by omega), hm1]
    · rw [hy_mem_eq, Function.update_of_ne (by omega),
        writePacked_outside hw0 x.mem (Nat.lt_succ_self _) val (by omega), hm2]
    · intro i hi
      rw [List.length_append, List.length_singleton] at hi
      have hcongr : readPacked (base + 3) b w y.mem i =
          readPacked (base + 3) b w (writePacked (base + 3) b w x.mem s.length val) i :=
        readPacked_congr (N := s.length + 1) hw0
          (fun addr haddr => by rw [hy_mem_eq, Function.update_of_ne (by omega)]) hi
      rw [hcongr]
      by_cases hieq : i = s.length
      · subst hieq
        rw [readPacked_writePacked_self _ _ _ _ _ hval_lt, List.getElem_append_right le_rfl]
        simp
      · have hilt : i < s.length := by omega
        rw [readPacked_writePacked_of_ne hw0 _ hieq, hm_arr i hilt,
          List.getElem_append_left hilt]
  · intro addr hlt
    rw [hy_mem_eq, Function.update_of_ne (by omega),
      writePacked_outside hw0 x.mem (Nat.lt_succ_self _) val (by omega)]


private theorem evalExact_sub_of_le {a b : ℕ} (h : b ≤ a) :
    BinOp.sub.evalExact a b = some (a - b) := by
  simp [BinOp.evalExact, h]

private theorem packedArray_pop_exec {b w base : ℕ} (hw : 3 ≤ w) (hbw : b ≤ w)
    {s : List ℕ} {x : RData arrRegs}
    (hrep : packedArrayRep b w base s x)
    (harg : packedArrayArgMatch .pop x.regs)
    (hfit : Fits w (base + packedArrayPeakSpace b w s .pop)) :
    ∃ (y : RData arrRegs) (n : ℕ),
      n ≤ packedArrayCharge ∧
      RDemonicExec w (base + packedArrayPeakSpace b w s .pop)
        packedArraySubroutine.code x n (· = y) ∧
      packedArrayDecode .pop y.regs = some (packedArrayStepFn s .pop).2 ∧
      packedArrayRep b w base (packedArrayStepFn s .pop).1 y ∧
      ∀ addr < base, y.mem addr = x.mem addr := by
  obtain ⟨hxb, hx_base, hx_rfr, hx_fr, hm0, hm1, hm2, hm_arr⟩ := hrep
  have hw0 : 0 < w := by omega
  have hpow3 : 8 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
  have h1 : Fits w 1 := by unfold Fits; omega
  set L_peak := base + (3 + packedWords s.length b w)
  have hfit_peak : Fits w (base + 3 + packedWords s.length b w) := by
    simpa [packedArrayPeakSpace, Nat.add_assoc] using hfit
  have hL_cur : x.frontier ≤ L_peak := by rw [hx_fr]; omega
  set x₁ := (x.set rZero 0).set rOne 1
  have e_z : RDemonicExec (B := .exact) w L_peak (.op (.const rZero 0)) x 1
      (· = x.set rZero 0) := RDemonicExec.const hL_cur (fits_zero w)
  have e_o : RDemonicExec (B := .exact) w L_peak (.op (.const rOne 1)) (x.set rZero 0) 1
      (· = x₁) := RDemonicExec.const hL_cur h1
  have hx₁b : x₁.Bounded w := (hxb.set (fits_zero w)).set h1
  have hx₁_tag : x₁.regs rTag = 1 := by
    rw [show x₁.regs rTag = x.regs rTag from by
      simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rTag.val ≠ rOne.val)),
        Function.update_of_ne (reg_ne (by decide : rTag.val ≠ rZero.val))]]
    simpa [packedArrayEncode, rTag] using harg.1
  have hx₁_z : x₁.regs rZero = 0 := by
    simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rZero.val ≠ rOne.val))]
  have hx₁_o : x₁.regs rOne = 1 := by simp [x₁]
  have hx₁_base : x₁.regs rBase = base := by
    simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOne.val)),
      Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rZero.val)), hx_base]
  have hx₁_rfr : x₁.regs rFr = x₁.frontier := by
    simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rOne.val)),
      Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rZero.val)), hx_rfr]
  have hp0_pos : 0 < packedWords s.length b w := Nat.succ_pos _
  have hsafe_pop : w = x₁.mem (base + 2) ∧ 0 < w ∧ x₁.mem (base + 1) ≤ w ∧
      Fits w (base + 3 + packedWords (x₁.mem base) (x₁.mem (base + 1)) w) := by
    refine ⟨hm2.symm, hw0, ?_, ?_⟩
    · change x.mem (base + 1) ≤ w; rw [hm1]; exact hbw
    · change Fits w (base + 3 + packedWords (x.mem base) (x.mem (base + 1)) w)
      rw [hm0, hm1]; exact hfit_peak
  have hnodup_sh : [rK, rIdx, rZero, rOne].Nodup := by
    simp [rK, rIdx, rZero, rOne, Fin.ext_iff]
  by_cases hs : s = []
  · subst hs
    have hrun_pop : (Memory.spec w).runClient { mem := x₁.mem, frontier := x₁.frontier }
        (popPrepProg base) =
        (((0, 0), 0), { mem := x₁.mem, frontier := x₁.frontier },
          [.read base, .read (base + 1), .read (base + 2)]) := by
      unfold popPrepProg Memory.read
      simp only [bind_eq_freeMBind, StateTransitionSpec.runClient_bind,
        StateTransitionSpec.runClient_lift, memory_stepFn_read, List.singleton_append]
      have hm0' : x₁.mem base = 0 := hm0
      simp only [hm0', ↓reduceIte, StateTransitionSpec.runClient_pure']
    have hv_pop : (Memory.spec w).ValidHistory { mem := x₁.mem, frontier := x₁.frontier }
        ((Memory.spec w).clientHistory { mem := x₁.mem, frontier := x₁.frontier }
          (popPrepProg base)) := by
      rw [StateTransitionSpec.clientHistory, hrun_pop]
      change base < x.frontier ∧ base + 1 < x.frontier ∧ base + 2 < x.frontier ∧ True
      rw [hx_fr]; exact ⟨by omega, by omega, by omega, trivial⟩
    obtain ⟨x₂, e_pp, hx₂b, hx₂_fr, hx₂_mem, hx₂_regs, hx₂_out⟩ :=
      emitLeafCode_exec popPrepProg_realizesBounded (by decide)
        ((le_max_left _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))) ![rBase]
        (fun i => by fin_cases i; decide) (fun i => by fin_cases i; decide)
        (L_peak := L_peak) base hx₁b hL_cur hx₁_rfr
        (by funext i; fin_cases i; exact hx₁_base) hsafe_pop hv_pop
        (by rw [StateTransitionSpec.clientState, hrun_pop])
    have hx₂_t0 : x₂.regs rTmp0 = 0 := by
      have h0 := hx₂_out 0; rw [StateTransitionSpec.clientResult, hrun_pop] at h0; exact h0
    have hx₂_t1 : x₂.regs rTmp1 = 0 := by
      have h1' := hx₂_out 1; rw [StateTransitionSpec.clientResult, hrun_pop] at h1'; exact h1'
    have hx₂_t2 : x₂.regs rTmp2 = 0 := by
      have h2 := hx₂_out 2; rw [StateTransitionSpec.clientResult, hrun_pop] at h2; exact h2
    set x₃ := ((x₂.set rOutT (x₂.regs rTmp0)).set rOutV (x₂.regs rTmp1)).set rK (x₂.regs rTmp2)
    have e_c1 : RDemonicExec (B := .exact) w L_peak (.op (.copy rOutT rTmp0)) x₂ 1
        (· = x₂.set rOutT (x₂.regs rTmp0)) := RDemonicExec.copy (by rw [hx₂_fr]; exact hL_cur)
    have e_c2 : RDemonicExec (B := .exact) w L_peak (.op (.copy rOutV rTmp1))
        (x₂.set rOutT (x₂.regs rTmp0)) 1
        (· = (x₂.set rOutT (x₂.regs rTmp0)).set rOutV (x₂.regs rTmp1)) := by
      have hc := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak) (d := rOutV)
        (s := rTmp1) (x := x₂.set rOutT (x₂.regs rTmp0))
        (by simp only [RData.set_frontier]; rw [hx₂_fr]; exact hL_cur)
      simpa [RData.set, Function.update_of_ne (reg_ne (by decide : rTmp1.val ≠ rOutT.val))] using hc
    have e_c3 : RDemonicExec (B := .exact) w L_peak (.op (.copy rK rTmp2))
        ((x₂.set rOutT (x₂.regs rTmp0)).set rOutV (x₂.regs rTmp1)) 1 (· = x₃) := by
      have hc := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak) (d := rK)
        (s := rTmp2) (x := (x₂.set rOutT (x₂.regs rTmp0)).set rOutV (x₂.regs rTmp1))
        (by simp only [RData.set_frontier]; rw [hx₂_fr]; exact hL_cur)
      simpa [x₃, RData.set, Function.update_of_ne (reg_ne (by decide : rTmp2.val ≠ rOutV.val)),
        Function.update_of_ne (reg_ne (by decide : rTmp2.val ≠ rOutT.val))] using hc
    have hx₃b : x₃.Bounded w :=
      ((hx₂b.set (hx₂b.regs_fits _)).set (hx₂b.regs_fits _)).set (hx₂b.regs_fits _)
    have hx₃_k : x₃.regs rK = 0 := by simp [x₃, hx₂_t2]
    have hx₃_fr : x₃.frontier = x.frontier := by simp [x₃, hx₂_fr, x₁]
    have e_sh := shrinkCode_exec (L_peak := L_peak) (count := rK) (idx := rIdx) (zero := rZero)
      (one := rOne) hx₃b hnodup_sh h1 (by rw [hx₃_fr]; exact hL_cur) (by rw [hx₃_k]; omega)
    set x₄ := shrinkPost rK rIdx rZero rOne x₃
    have hx₄b : x₄.Bounded w := rDemonicExec_eq_bounded e_sh hx₃b
    have hx₄_fr : x₄.frontier = x.frontier := by change x₃.frontier - x₃.regs rK = _; omega
    have hx₄_k : x₄.regs rK = 0 := by
      have h4 : x₄.regs rK = x₃.regs rK := by
        simp [x₄, shrinkPost, rK, rIdx, rZero, rOne, Fin.ext_iff]
      rw [h4, hx₃_k]
    have hx₄_rfr : x₄.regs rFr = x.frontier := by
      have h4 : x₄.regs rFr = x₃.regs rFr := by
        simp [x₄, shrinkPost, rFr, rIdx, rZero, rOne, Fin.ext_iff]
      rw [h4, show x₃.regs rFr = x₂.regs rFr from by
        simp [x₃, RData.set, Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rK.val)),
          Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rOutV.val)),
          Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rOutT.val))],
        hx₂_regs rFr (by decide), hx₁_rfr]; rfl
    set y := x₄.set rFr x.frontier
    have e_sub : RDemonicExec (B := .exact) w L_peak (.op (.exactBin .sub rFr rFr rK)) x₄ 1
        (· = y) :=
      RDemonicExec.exactBin (by rw [hx₄_fr]; exact hL_cur)
        (by rw [hx₄_rfr, hx₄_k, evalExact_sub_of_le (Nat.zero_le _)]; simp) hxb.frontier_fits
    have hyb : y.Bounded w := hx₄b.set hxb.frontier_fits
    have e_pop := e_pp.seq_eq (e_c1.seq_eq (e_c2.seq_eq (e_c3.seq_eq (e_sh.seq_eq e_sub))))
    have e_all : RDemonicExec w L_peak packedArraySubroutine.code x _ (· = y) :=
      e_z.seq_eq (e_o.seq_eq (RDemonicExec.branch_neg
        (by simp [Cond.Holds, hx₁_tag, hx₁_z])
        (RDemonicExec.branch_pos (by simp [Cond.Holds, hx₁_tag, hx₁_o]) e_pop)))
    have hm_cost :
        memoryCost (popPrepProg base) { mem := x₁.mem, frontier := x₁.frontier } = 3 := by
      unfold popPrepProg Memory.read
      simp only [bind_eq_freeMBind, memoryCost_bind, StateTransitionSpec.clientState,
        StateTransitionSpec.clientResult, StateTransitionSpec.runClient_lift, memory_stepFn_read]
      have hm0' : x₁.mem base = 0 := hm0
      simp only [hm0', ↓reduceIte, memoryCost_pure]
      rfl
    have hy_mem : y.mem = x.mem := by
      ext addr
      change clear x₃.mem (x₃.frontier - x₃.regs rK) (x₃.regs rK) addr = x.mem addr
      rw [hx₃_k, clear_of_not_owns (by simp [Block.Owns])]
      change x₂.mem addr = x.mem addr
      rw [StateTransitionSpec.clientState, hrun_pop] at hx₂_mem
      exact congrFun hx₂_mem addr
    have hy_outT : y.regs rOutT = 0 := by
      have : y.regs rOutT = x₃.regs rOutT := by
        simp [y, x₄, shrinkPost, RData.set,
          Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rFr.val)),
          Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rIdx.val)),
          Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rOne.val)),
          Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rZero.val))]
      rw [this]; simp [x₃, RData.set,
        Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rK.val)),
        Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rOutV.val)), hx₂_t0]
    refine ⟨y, _, ?_, e_all, ?_, ?_, fun addr _ => by rw [hy_mem]⟩
    · simp only [hm_cost, hx₃_k, packedArrayCharge]; omega
    · simp [packedArrayDecode, packedArrayStepFn, hy_outT]
    · simp only [packedArrayStepFn]
      refine ⟨hyb, ?_, ?_, ?_, ?_, ?_, ?_, fun _ hi => by simp at hi⟩
      · have : y.regs rBase = x₃.regs rBase := by
          simp [y, x₄, shrinkPost, RData.set,
            Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rFr.val)),
            Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rIdx.val)),
            Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOne.val)),
            Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rZero.val))]
        rw [this, show x₃.regs rBase = x₂.regs rBase from by
          simp [x₃, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rK.val)),
            Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOutV.val)),
            Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOutT.val))],
          hx₂_regs rBase (by decide), hx₁_base]
      · simp [y, hx₄_fr]
      · simp [y, hx₄_fr, hx_fr]
      · rw [hy_mem]; exact hm0
      · rw [hy_mem]; exact hm1
      · rw [hy_mem]; exact hm2
  · have hn_pos : 0 < s.length := List.length_pos_iff.mpr hs
    have hn_ne : s.length ≠ 0 := by omega
    have hnm1 : s.length - 1 + 1 = s.length := by omega
    have hstep_pw := packedWords_succ_sub_le_one (b := b) (n := s.length - 1) hw0 hbw
    rw [hnm1] at hstep_pw
    set lastVal := readPacked (base + 3) b w x.mem (s.length - 1)
    set delta := packedWords s.length b w - packedWords (s.length - 1) b w
    have hlast_eq : lastVal = s.getLast hs := by
      rw [List.getLast_eq_getElem hs]; exact hm_arr (s.length - 1) (by omega)
    have hrun_pop : (Memory.spec w).runClient { mem := x₁.mem, frontier := x₁.frontier }
        (popPrepProg base) =
        (((1, lastVal), delta),
          { mem := Function.update x.mem base (s.length - 1), frontier := x₁.frontier },
          [.read base, .read (base + 1), .read (base + 2),
           .read (base + 3 + wordOffset b w (s.length - 1)),
           .read (base + 3 + wordOffset b w (s.length - 1) + 1),
           .write base (s.length - 1)]) := by
      unfold popPrepProg Memory.read Memory.write
      simp only [bind_eq_freeMBind, StateTransitionSpec.runClient_bind,
        StateTransitionSpec.runClient_lift, memory_stepFn_read, List.singleton_append]
      have hm0' : x₁.mem base = s.length := hm0
      have hm1' : x₁.mem (base + 1) = b := hm1
      have hm2' : x₁.mem (base + 2) = w := hm2
      simp only [hm0', hm1', hm2', hn_ne, ↓reduceIte,
        StateTransitionSpec.runClient_bind, StateTransitionSpec.runClient_lift,
        StateTransitionSpec.runClient_pure', runClient_readPackedMemProg,
        runClient_packedWordsProg _ hw0, memory_stepFn_write, List.nil_append, List.cons_append]
      rfl
    have hv_pop : (Memory.spec w).ValidHistory { mem := x₁.mem, frontier := x₁.frontier }
        ((Memory.spec w).clientHistory { mem := x₁.mem, frontier := x₁.frontier }
          (popPrepProg base)) := by
      rw [StateTransitionSpec.clientHistory, hrun_pop]
      have hwo :=
        wordOffset_add_one_lt_packedWords (k := b) hw0 (by omega : s.length - 1 < s.length)
      have hnm1_fits : Fits w (s.length - 1) :=
        (hxb.mem_fits base).of_le (by rw [hm0]; omega)
      change base < x.frontier ∧ base + 1 < x.frontier ∧ base + 2 < x.frontier ∧
        base + 3 + wordOffset b w (s.length - 1) < x.frontier ∧
        base + 3 + wordOffset b w (s.length - 1) + 1 < x.frontier ∧
        (base < x.frontier ∧ Fits w (s.length - 1)) ∧ True
      rw [hx_fr]
      exact ⟨by omega, by omega, by omega, by omega, by omega, ⟨by omega, hnm1_fits⟩, trivial⟩
    obtain ⟨x₂, e_pp, hx₂b, hx₂_fr, hx₂_mem, hx₂_regs, hx₂_out⟩ :=
      emitLeafCode_exec popPrepProg_realizesBounded (by decide)
        ((le_max_left _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))) ![rBase]
        (fun i => by fin_cases i; decide) (fun i => by fin_cases i; decide)
        (L_peak := L_peak) base hx₁b hL_cur hx₁_rfr
        (by funext i; fin_cases i; exact hx₁_base) hsafe_pop hv_pop
        (by rw [StateTransitionSpec.clientState, hrun_pop])
    have hx₂_t0 : x₂.regs rTmp0 = 1 := by
      have h0 := hx₂_out 0; rw [StateTransitionSpec.clientResult, hrun_pop] at h0; exact h0
    have hx₂_t1 : x₂.regs rTmp1 = lastVal := by
      have h1' := hx₂_out 1; rw [StateTransitionSpec.clientResult, hrun_pop] at h1'; exact h1'
    have hx₂_t2 : x₂.regs rTmp2 = delta := by
      have h2 := hx₂_out 2; rw [StateTransitionSpec.clientResult, hrun_pop] at h2; exact h2
    set x₃ := ((x₂.set rOutT (x₂.regs rTmp0)).set rOutV (x₂.regs rTmp1)).set rK (x₂.regs rTmp2)
    have e_c1 : RDemonicExec (B := .exact) w L_peak (.op (.copy rOutT rTmp0)) x₂ 1
        (· = x₂.set rOutT (x₂.regs rTmp0)) := RDemonicExec.copy (by rw [hx₂_fr]; exact hL_cur)
    have e_c2 : RDemonicExec (B := .exact) w L_peak (.op (.copy rOutV rTmp1))
        (x₂.set rOutT (x₂.regs rTmp0)) 1
        (· = (x₂.set rOutT (x₂.regs rTmp0)).set rOutV (x₂.regs rTmp1)) := by
      have hc := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak) (d := rOutV)
        (s := rTmp1) (x := x₂.set rOutT (x₂.regs rTmp0))
        (by simp only [RData.set_frontier]; rw [hx₂_fr]; exact hL_cur)
      simpa [RData.set, Function.update_of_ne (reg_ne (by decide : rTmp1.val ≠ rOutT.val))] using hc
    have e_c3 : RDemonicExec (B := .exact) w L_peak (.op (.copy rK rTmp2))
        ((x₂.set rOutT (x₂.regs rTmp0)).set rOutV (x₂.regs rTmp1)) 1 (· = x₃) := by
      have hc := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak) (d := rK)
        (s := rTmp2) (x := (x₂.set rOutT (x₂.regs rTmp0)).set rOutV (x₂.regs rTmp1))
        (by simp only [RData.set_frontier]; rw [hx₂_fr]; exact hL_cur)
      simpa [x₃, RData.set, Function.update_of_ne (reg_ne (by decide : rTmp2.val ≠ rOutV.val)),
        Function.update_of_ne (reg_ne (by decide : rTmp2.val ≠ rOutT.val))] using hc
    have hx₃b : x₃.Bounded w :=
      ((hx₂b.set (hx₂b.regs_fits _)).set (hx₂b.regs_fits _)).set (hx₂b.regs_fits _)
    have hx₃_k : x₃.regs rK = delta := by simp [x₃, hx₂_t2]
    have hx₃_fr : x₃.frontier = base + 3 + packedWords s.length b w := by
      simp [x₃, hx₂_fr, x₁, hx_fr]
    have e_sh := shrinkCode_exec (L_peak := L_peak) (count := rK) (idx := rIdx) (zero := rZero)
      (one := rOne) hx₃b hnodup_sh h1 (by rw [hx₃_fr]; dsimp [L_peak]; omega)
      (by rw [hx₃_k, hx₃_fr]; omega)
    set x₄ := shrinkPost rK rIdx rZero rOne x₃
    have hx₄b : x₄.Bounded w := rDemonicExec_eq_bounded e_sh hx₃b
    have hx₄_fr : x₄.frontier = base + 3 + packedWords (s.length - 1) b w := by
      change x₃.frontier - x₃.regs rK = _; rw [hx₃_fr, hx₃_k]; omega
    have hx₄_k : x₄.regs rK = delta := by
      have h4 : x₄.regs rK = x₃.regs rK := by
        simp [x₄, shrinkPost, rK, rIdx, rZero, rOne, Fin.ext_iff]
      rw [h4, hx₃_k]
    have hx₄_rfr : x₄.regs rFr = base + 3 + packedWords s.length b w := by
      have h4 : x₄.regs rFr = x₃.regs rFr := by
        simp [x₄, shrinkPost, rFr, rIdx, rZero, rOne, Fin.ext_iff]
      rw [h4, show x₃.regs rFr = x₂.regs rFr from by
        simp [x₃, RData.set, Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rK.val)),
          Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rOutV.val)),
          Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rFr.val).symm)],
        hx₂_regs rFr (by decide), hx₁_rfr]; exact hx_fr
    set newFr := base + 3 + packedWords (s.length - 1) b w
    set y := x₄.set rFr newFr
    have hfit_new : Fits w newFr := hfit_peak.of_le (by dsimp [newFr]; omega)
    have e_sub : RDemonicExec (B := .exact) w L_peak (.op (.exactBin .sub rFr rFr rK)) x₄ 1
        (· = y) :=
      RDemonicExec.exactBin (by rw [hx₄_fr]; dsimp [L_peak]; omega)
        (by rw [hx₄_rfr, hx₄_k, evalExact_sub_of_le (by omega)]; congr 1; dsimp [newFr]; omega)
        hfit_new
    have hyb : y.Bounded w := hx₄b.set hfit_new
    have e_pop := e_pp.seq_eq (e_c1.seq_eq (e_c2.seq_eq (e_c3.seq_eq (e_sh.seq_eq e_sub))))
    have e_all : RDemonicExec w L_peak packedArraySubroutine.code x _ (· = y) :=
      e_z.seq_eq (e_o.seq_eq (RDemonicExec.branch_neg
        (by simp [Cond.Holds, hx₁_tag, hx₁_z])
        (RDemonicExec.branch_pos (by simp [Cond.Holds, hx₁_tag, hx₁_o]) e_pop)))
    have hm_cost :
        memoryCost (popPrepProg base) { mem := x₁.mem, frontier := x₁.frontier } = 6 := by
      unfold popPrepProg Memory.read Memory.write
      simp only [bind_eq_freeMBind, memoryCost_bind, StateTransitionSpec.clientState,
        StateTransitionSpec.clientResult, StateTransitionSpec.runClient_lift, memory_stepFn_read]
      have hm0' : x₁.mem base = s.length := hm0
      have hm1' : x₁.mem (base + 1) = b := hm1
      have hm2' : x₁.mem (base + 2) = w := hm2
      simp only [hm0', hm1', hm2', hn_ne, ↓reduceIte, memoryCost_bind,
        StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
        StateTransitionSpec.runClient_lift, StateTransitionSpec.runClient_pure',
        memoryCost_readPackedMemProg, memoryCost_packedWordsProg, memory_stepFn_write,
        memoryCost_pure]
      rfl
    have hy_mem_lt :
        ∀ addr < newFr, y.mem addr = Function.update x.mem base (s.length - 1) addr := by
      intro addr hlt
      change clear x₃.mem (x₃.frontier - x₃.regs rK) (x₃.regs rK) addr = _
      have hsub : x₃.frontier - x₃.regs rK = newFr := by rw [hx₃_fr, hx₃_k]; dsimp [newFr]; omega
      rw [hsub, clear_of_not_owns (by simp only [Block.Owns]; omega)]
      change x₂.mem addr = _
      rw [StateTransitionSpec.clientState, hrun_pop] at hx₂_mem
      exact congrFun hx₂_mem addr
    have hy_outT : y.regs rOutT = 1 := by
      have : y.regs rOutT = x₃.regs rOutT := by
        simp [y, x₄, shrinkPost, RData.set,
          Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rFr.val)),
          Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rIdx.val)),
          Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rOne.val)),
          Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rZero.val))]
      rw [this]; simp [x₃, RData.set,
        Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rK.val)),
        Function.update_of_ne (reg_ne (by decide : rOutT.val ≠ rOutV.val)), hx₂_t0]
    have hy_outV : y.regs rOutV = lastVal := by
      have : y.regs rOutV = x₃.regs rOutV := by
        simp [y, x₄, shrinkPost, RData.set,
          Function.update_of_ne (reg_ne (by decide : rOutV.val ≠ rFr.val)),
          Function.update_of_ne (reg_ne (by decide : rOutV.val ≠ rIdx.val)),
          Function.update_of_ne (reg_ne (by decide : rOutV.val ≠ rOne.val)),
          Function.update_of_ne (reg_ne (by decide : rOutV.val ≠ rZero.val))]
      rw [this]; simp [x₃, RData.set,
        Function.update_of_ne (reg_ne (by decide : rOutV.val ≠ rK.val)), hx₂_t1]
    have hp_pos_nm1 : 0 < packedWords (s.length - 1) b w := Nat.succ_pos _
    refine ⟨y, _, ?_, e_all, ?_, ?_, ?_⟩
    · simp only [hm_cost, hx₃_k, packedArrayCharge]; omega
    · simp [packedArrayDecode, packedArrayStepFn, hs, hy_outT, hy_outV, hlast_eq]
    · simp only [packedArrayStepFn, hs, ↓reduceDIte]
      refine ⟨hyb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have : y.regs rBase = x₃.regs rBase := by
          simp [y, x₄, shrinkPost, RData.set,
            Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rFr.val)),
            Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rIdx.val)),
            Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOne.val)),
            Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rZero.val))]
        rw [this, show x₃.regs rBase = x₂.regs rBase from by
          simp [x₃, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rK.val)),
            Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOutV.val)),
            Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOutT.val))],
          hx₂_regs rBase (by decide), hx₁_base]
      · simp [y, hx₄_fr, newFr]
      · simp [y, hx₄_fr, newFr, List.length_dropLast]
      · rw [hy_mem_lt base (by dsimp [newFr]; omega), Function.update_self, List.length_dropLast]
      · rw [hy_mem_lt (base + 1) (by dsimp [newFr]; omega), Function.update_of_ne (by omega), hm1]
      · rw [hy_mem_lt (base + 2) (by dsimp [newFr]; omega), Function.update_of_ne (by omega), hm2]
      · intro i hi
        rw [List.length_dropLast] at hi
        have hcongr : readPacked (base + 3) b w y.mem i = readPacked (base + 3) b w x.mem i :=
          readPacked_congr (N := s.length - 1) hw0
            (fun addr haddr => by
              rw [hy_mem_lt addr (by dsimp [newFr]; omega), Function.update_of_ne (by omega)]) hi
        rw [hcongr, hm_arr i (by omega), List.getElem_dropLast]
    · intro addr hlt
      rw [hy_mem_lt addr (by dsimp [newFr]; omega), Function.update_of_ne (by omega)]


private theorem packedArray_getSetLen_exec {b w base : ℕ} (hw : 3 ≤ w) (hbw : b ≤ w)
    {s : List ℕ} {x : RData arrRegs} (o : PackedArrayOp)
    (hnp : ∀ v, o ≠ .push v) (hnpop : o ≠ .pop)
    (hrep : packedArrayRep b w base s x)
    (hv : packedArrayValid b w s o)
    (harg : packedArrayArgMatch o x.regs)
    (hfit : Fits w (base + packedArrayPeakSpace b w s o)) :
    ∃ (y : RData arrRegs) (n : ℕ),
      n ≤ packedArrayCharge ∧
      RDemonicExec w (base + packedArrayPeakSpace b w s o)
        packedArraySubroutine.code x n (· = y) ∧
      packedArrayDecode o y.regs = some (packedArrayStepFn s o).2 ∧
      packedArrayRep b w base (packedArrayStepFn s o).1 y ∧
      ∀ addr < base, y.mem addr = x.mem addr := by
  obtain ⟨hxb, hx_base, hx_rfr, hx_fr, hm0, hm1, hm2, hm_arr⟩ := hrep
  have hw0 : 0 < w := by omega
  have hpow3 : 8 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
  have h1 : Fits w 1 := by unfold Fits; omega
  have hp0_pos : 0 < packedWords s.length b w := Nat.succ_pos _
  cases o with
  | push v => exact absurd rfl (hnp v)
  | pop => exact absurd rfl hnpop
  | get idx =>
    obtain ⟨hidx_lt, _⟩ := hv
    set L_peak := base + (3 + packedWords s.length b w)
    have hfit_peak : Fits w (base + 3 + packedWords s.length b w) := by
      simpa [packedArrayPeakSpace, Nat.add_assoc] using hfit
    have hL_cur : x.frontier ≤ L_peak := by rw [hx_fr]; omega
    set x₁ := (x.set rZero 0).set rOne 1
    have e_z : RDemonicExec (B := .exact) w L_peak (.op (.const rZero 0)) x 1
        (· = x.set rZero 0) := RDemonicExec.const hL_cur (fits_zero w)
    have e_o : RDemonicExec (B := .exact) w L_peak (.op (.const rOne 1)) (x.set rZero 0) 1
        (· = x₁) := RDemonicExec.const hL_cur h1
    have hx₁b : x₁.Bounded w := (hxb.set (fits_zero w)).set h1
    have hx₁_tag : x₁.regs rTag = 2 := by
      rw [show x₁.regs rTag = x.regs rTag from by
        simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rTag.val ≠ rOne.val)),
          Function.update_of_ne (reg_ne (by decide : rTag.val ≠ rZero.val))]]
      simpa [packedArrayEncode, rTag] using harg.1
    have hx₁_arg1 : x₁.regs rArg1 = idx := by
      rw [show x₁.regs rArg1 = x.regs rArg1 from by
        simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rArg1.val ≠ rOne.val)),
          Function.update_of_ne (reg_ne (by decide : rArg1.val ≠ rZero.val))]]
      simpa [packedArrayEncode, rArg1] using harg.2.1
    have hx₁_arg2 : x₁.regs rArg2 = 0 := by
      rw [show x₁.regs rArg2 = x.regs rArg2 from by
        simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rArg2.val ≠ rOne.val)),
          Function.update_of_ne (reg_ne (by decide : rArg2.val ≠ rZero.val))]]
      simpa [packedArrayEncode, rArg2] using harg.2.2
    have hx₁_z : x₁.regs rZero = 0 := by
      simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rZero.val ≠ rOne.val))]
    have hx₁_o : x₁.regs rOne = 1 := by simp [x₁]
    have hx₁_base : x₁.regs rBase = base := by
      simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOne.val)),
        Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rZero.val)), hx_base]
    have hx₁_rfr : x₁.regs rFr = x₁.frontier := by
      simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rOne.val)),
        Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rZero.val)), hx_rfr]
    have hrun : (Memory.spec w).runClient { mem := x₁.mem, frontier := x₁.frontier }
        (getSetLenProg ((base, 2), (idx, 0))) =
        (readPacked (base + 3) b w x.mem idx, { mem := x₁.mem, frontier := x₁.frontier },
          [.read base, .read (base + 1), .read (base + 2),
           .read (base + 3 + wordOffset b w idx),
           .read (base + 3 + wordOffset b w idx + 1)]) := by
      unfold getSetLenProg Memory.read
      simp only [bind_eq_freeMBind, StateTransitionSpec.runClient_bind,
        StateTransitionSpec.runClient_lift, StateTransitionSpec.runClient_pure',
        memory_stepFn_read, ↓reduceIte, List.nil_append, List.singleton_append]
      have hm1' : x₁.mem (base + 1) = b := hm1
      have hm2' : x₁.mem (base + 2) = w := hm2
      rw [hm1', hm2', runClient_readPackedMemProg]
      rfl
    have hv_hist : (Memory.spec w).ValidHistory { mem := x₁.mem, frontier := x₁.frontier }
        ((Memory.spec w).clientHistory { mem := x₁.mem, frontier := x₁.frontier }
          (getSetLenProg ((base, 2), (idx, 0)))) := by
      rw [StateTransitionSpec.clientHistory, hrun]
      have hwo := wordOffset_add_one_lt_packedWords (k := b) hw0 hidx_lt
      change base < x.frontier ∧ base + 1 < x.frontier ∧ base + 2 < x.frontier ∧
        base + 3 + wordOffset b w idx < x.frontier ∧
        base + 3 + wordOffset b w idx + 1 < x.frontier ∧ True
      rw [hx_fr]; exact ⟨by omega, by omega, by omega, by omega, by omega, trivial⟩
    obtain ⟨x₂, e_gs, hx₂b, hx₂_fr, hx₂_mem, hx₂_regs, hx₂_out⟩ :=
      emitLeafCode_exec getSetLenProg_realizesBounded (by decide)
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
        ![rBase, rTag, rArg1, rArg2]
        (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
        (L_peak := L_peak) ((base, 2), (idx, 0)) hx₁b hL_cur hx₁_rfr
        (by funext i; fin_cases i
            · exact hx₁_base
            · exact hx₁_tag
            · exact hx₁_arg1
            · exact hx₁_arg2)
        ⟨hm2.symm, hw0, by dsimp only; change x.mem (base + 1) ≤ w; rw [hm1]; exact hbw,
          by dsimp only; change Fits w (base + 3 + packedWords (x.mem base) (x.mem (base + 1)) w)
             rw [hm0, hm1]; exact hfit_peak,
          fun _ => by dsimp only; change idx < x.mem base; rw [hm0]; exact hidx_lt⟩
        hv_hist (by rw [StateTransitionSpec.clientState, hrun])
    have hx₂_t0 : x₂.regs rTmp0 = s[idx] := by
      have h0 := hx₂_out 0
      rw [StateTransitionSpec.clientResult, hrun] at h0
      exact h0.trans (hm_arr idx hidx_lt)
    set y := x₂.set rOutV (x₂.regs rTmp0)
    have e_cp : RDemonicExec (B := .exact) w L_peak (.op (.copy rOutV rTmp0)) x₂ 1 (· = y) :=
      RDemonicExec.copy (by rw [hx₂_fr]; exact hL_cur)
    have hyb : y.Bounded w := hx₂b.set (hx₂b.regs_fits _)
    have e_all : RDemonicExec w L_peak packedArraySubroutine.code x _ (· = y) :=
      e_z.seq_eq (e_o.seq_eq (RDemonicExec.branch_neg
        (by simp [Cond.Holds, hx₁_tag, hx₁_z])
        (RDemonicExec.branch_neg (by simp [Cond.Holds, hx₁_tag, hx₁_o]) (e_gs.seq_eq e_cp))))
    have hm_cost : memoryCost (getSetLenProg ((base, 2), (idx, 0)))
        { mem := x₁.mem, frontier := x₁.frontier } = 5 := by
      unfold getSetLenProg Memory.read
      simp only [bind_eq_freeMBind, memoryCost_bind, StateTransitionSpec.clientState,
        StateTransitionSpec.clientResult, StateTransitionSpec.runClient_lift,
        StateTransitionSpec.runClient_pure', memory_stepFn_read, ↓reduceIte,
        memoryCost_readPackedMemProg]
      rfl
    have hy_mem : y.mem = x.mem := by
      change x₂.mem = x.mem
      rw [StateTransitionSpec.clientState, hrun] at hx₂_mem; exact hx₂_mem
    refine ⟨y, _, ?_, e_all, ?_, ?_, fun addr _ => by rw [hy_mem]⟩
    · simp only [hm_cost, packedArrayCharge]; omega
    · simp [packedArrayDecode, packedArrayStepFn, y, hx₂_t0, List.getD,
        List.getElem?_eq_getElem hidx_lt]
    · dsimp only [packedArrayStepFn]
      refine ⟨hyb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [y, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOutV.val)),
          hx₂_regs rBase (by decide), hx₁_base]
      · simp [y, RData.set, Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rOutV.val)),
          hx₂_regs rFr (by decide), hx₁_rfr, hx₂_fr]
      · simp [y, hx₂_fr, x₁, hx_fr]
      · rw [hy_mem]; exact hm0
      · rw [hy_mem]; exact hm1
      · rw [hy_mem]; exact hm2
      · intro i hi; rw [hy_mem]; exact hm_arr i hi
  | set idx val =>
    obtain ⟨hidx_lt, _, hval_lt⟩ := hv
    set L_peak := base + (3 + packedWords s.length b w)
    have hfit_peak : Fits w (base + 3 + packedWords s.length b w) := by
      simpa [packedArrayPeakSpace, Nat.add_assoc] using hfit
    have hL_cur : x.frontier ≤ L_peak := by rw [hx_fr]; omega
    set x₁ := (x.set rZero 0).set rOne 1
    have e_z : RDemonicExec (B := .exact) w L_peak (.op (.const rZero 0)) x 1
        (· = x.set rZero 0) := RDemonicExec.const hL_cur (fits_zero w)
    have e_o : RDemonicExec (B := .exact) w L_peak (.op (.const rOne 1)) (x.set rZero 0) 1
        (· = x₁) := RDemonicExec.const hL_cur h1
    have hx₁b : x₁.Bounded w := (hxb.set (fits_zero w)).set h1
    have hx₁_tag : x₁.regs rTag = 3 := by
      rw [show x₁.regs rTag = x.regs rTag from by
        simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rTag.val ≠ rOne.val)),
          Function.update_of_ne (reg_ne (by decide : rTag.val ≠ rZero.val))]]
      simpa [packedArrayEncode, rTag] using harg.1
    have hx₁_arg1 : x₁.regs rArg1 = idx := by
      rw [show x₁.regs rArg1 = x.regs rArg1 from by
        simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rArg1.val ≠ rOne.val)),
          Function.update_of_ne (reg_ne (by decide : rArg1.val ≠ rZero.val))]]
      simpa [packedArrayEncode, rArg1] using harg.2.1
    have hx₁_arg2 : x₁.regs rArg2 = val := by
      rw [show x₁.regs rArg2 = x.regs rArg2 from by
        simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rArg2.val ≠ rOne.val)),
          Function.update_of_ne (reg_ne (by decide : rArg2.val ≠ rZero.val))]]
      simpa [packedArrayEncode, rArg2] using harg.2.2
    have hx₁_z : x₁.regs rZero = 0 := by
      simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rZero.val ≠ rOne.val))]
    have hx₁_o : x₁.regs rOne = 1 := by simp [x₁]
    have hx₁_base : x₁.regs rBase = base := by
      simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOne.val)),
        Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rZero.val)), hx_base]
    have hx₁_rfr : x₁.regs rFr = x₁.frontier := by
      simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rOne.val)),
        Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rZero.val)), hx_rfr]
    have hrun : (Memory.spec w).runClient { mem := x₁.mem, frontier := x₁.frontier }
        (getSetLenProg ((base, 3), (idx, val))) =
        (0, { mem := writePacked (base + 3) b w x.mem idx val, frontier := x₁.frontier },
          [.read base, .read (base + 1), .read (base + 2)] ++
            (Memory.spec w).clientHistory { mem := x.mem, frontier := x₁.frontier }
              (writePackedMemProg (((base + 3, b), (w, idx)), val))) := by
      unfold getSetLenProg Memory.read
      simp only [bind_eq_freeMBind, StateTransitionSpec.runClient_bind,
        StateTransitionSpec.runClient_lift, StateTransitionSpec.runClient_pure',
        memory_stepFn_read, show (3 = 2) ↔ False by decide, ↓reduceIte, List.nil_append,
        List.singleton_append]
      have hm1' : x₁.mem (base + 1) = b := hm1
      have hm2' : x₁.mem (base + 2) = w := hm2
      have hx₁_mem : x₁.mem = x.mem := rfl
      rw [hm1', hm2', hx₁_mem]
      have hcs := clientState_writePackedMemProg w (((base + 3, b), (w, idx)), val)
        { mem := x.mem, frontier := x₁.frontier }
      dsimp only [StateTransitionSpec.clientState] at hcs
      rw [hcs]
      simp [List.append_nil]
    have hv_hist : (Memory.spec w).ValidHistory { mem := x₁.mem, frontier := x₁.frontier }
        ((Memory.spec w).clientHistory { mem := x₁.mem, frontier := x₁.frontier }
          (getSetLenProg ((base, 3), (idx, val)))) := by
      rw [StateTransitionSpec.clientHistory, hrun]
      have hwf1 : Memory.WellFormed w { mem := x.mem, frontier := x₁.frontier } :=
        ⟨hx₁b.frontier_fits, hx₁b.mem_fits⟩
      have hvw := validHistory_writePackedMemProg (w := w)
        (d := (((base + 3, b), (w, idx)), val)) (N := s.length)
        (s := { mem := x.mem, frontier := x₁.frontier })
        rfl hw0 hbw hidx_lt hwf1 (by simp [x₁, hx_fr])
      change base < x.frontier ∧ base + 1 < x.frontier ∧ base + 2 < x.frontier ∧ _
      rw [hx_fr]
      exact ⟨by omega, by omega, by omega, hvw⟩
    obtain ⟨x₂, e_gs, hx₂b, hx₂_fr, hx₂_mem, hx₂_regs, _⟩ :=
      emitLeafCode_exec getSetLenProg_realizesBounded (by decide)
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
        ![rBase, rTag, rArg1, rArg2]
        (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
        (L_peak := L_peak) ((base, 3), (idx, val)) hx₁b hL_cur hx₁_rfr
        (by funext i; fin_cases i
            · exact hx₁_base
            · exact hx₁_tag
            · exact hx₁_arg1
            · exact hx₁_arg2)
        ⟨hm2.symm, hw0, by dsimp only; change x.mem (base + 1) ≤ w; rw [hm1]; exact hbw,
          by dsimp only; change Fits w (base + 3 + packedWords (x.mem base) (x.mem (base + 1)) w)
             rw [hm0, hm1]; exact hfit_peak,
          fun _ => by dsimp only; change idx < x.mem base; rw [hm0]; exact hidx_lt⟩
        hv_hist (by rw [StateTransitionSpec.clientState, hrun])
    set y := x₂.set rOutV (x₂.regs rTmp0)
    have e_cp : RDemonicExec (B := .exact) w L_peak (.op (.copy rOutV rTmp0)) x₂ 1 (· = y) :=
      RDemonicExec.copy (by rw [hx₂_fr]; exact hL_cur)
    have hyb : y.Bounded w := hx₂b.set (hx₂b.regs_fits _)
    have e_all : RDemonicExec w L_peak packedArraySubroutine.code x _ (· = y) :=
      e_z.seq_eq (e_o.seq_eq (RDemonicExec.branch_neg
        (by simp [Cond.Holds, hx₁_tag, hx₁_z])
        (RDemonicExec.branch_neg (by simp [Cond.Holds, hx₁_tag, hx₁_o]) (e_gs.seq_eq e_cp))))
    have hm_cost : memoryCost (getSetLenProg ((base, 3), (idx, val)))
        { mem := x₁.mem, frontier := x₁.frontier } = 7 := by
      unfold getSetLenProg Memory.read
      simp only [bind_eq_freeMBind, memoryCost_bind, StateTransitionSpec.clientState,
        StateTransitionSpec.clientResult, StateTransitionSpec.runClient_lift,
        StateTransitionSpec.runClient_pure', memory_stepFn_read,
        show (3 = 2) ↔ False by decide, ↓reduceIte, memoryCost_writePackedMemProg,
        memoryCost_pure]
      rfl
    have hy_mem : y.mem = writePacked (base + 3) b w x.mem idx val := by
      change x₂.mem = _
      rw [StateTransitionSpec.clientState, hrun] at hx₂_mem; exact hx₂_mem
    refine ⟨y, _, ?_, e_all, rfl, ?_, ?_⟩
    · simp only [hm_cost, packedArrayCharge]; omega
    · dsimp only [packedArrayStepFn]
      refine ⟨hyb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [y, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOutV.val)),
          hx₂_regs rBase (by decide), hx₁_base]
      · simp [y, RData.set, Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rOutV.val)),
          hx₂_regs rFr (by decide), hx₁_rfr, hx₂_fr]
      · simp [y, hx₂_fr, x₁, hx_fr, List.length_set]
      · rw [hy_mem, writePacked_outside hw0 x.mem hidx_lt val (by omega), hm0, List.length_set]
      · rw [hy_mem, writePacked_outside hw0 x.mem hidx_lt val (by omega), hm1]
      · rw [hy_mem, writePacked_outside hw0 x.mem hidx_lt val (by omega), hm2]
      · intro i hi
        rw [List.length_set] at hi
        rw [hy_mem]
        by_cases hieq : i = idx
        · subst hieq
          rw [readPacked_writePacked_self _ _ _ _ _ hval_lt, List.getElem_set_self]
        · rw [readPacked_writePacked_of_ne hw0 _ hieq, hm_arr i hi,
            List.getElem_set_ne (Ne.symm hieq)]
    · intro addr hlt
      rw [hy_mem, writePacked_outside hw0 x.mem hidx_lt val (by omega)]
  | length =>
    set L_peak := base + (3 + packedWords s.length b w)
    have hfit_peak : Fits w (base + 3 + packedWords s.length b w) := by
      simpa [packedArrayPeakSpace, Nat.add_assoc] using hfit
    have hL_cur : x.frontier ≤ L_peak := by rw [hx_fr]; omega
    set x₁ := (x.set rZero 0).set rOne 1
    have e_z : RDemonicExec (B := .exact) w L_peak (.op (.const rZero 0)) x 1
        (· = x.set rZero 0) := RDemonicExec.const hL_cur (fits_zero w)
    have e_o : RDemonicExec (B := .exact) w L_peak (.op (.const rOne 1)) (x.set rZero 0) 1
        (· = x₁) := RDemonicExec.const hL_cur h1
    have hx₁b : x₁.Bounded w := (hxb.set (fits_zero w)).set h1
    have hx₁_tag : x₁.regs rTag = 4 := by
      rw [show x₁.regs rTag = x.regs rTag from by
        simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rTag.val ≠ rOne.val)),
          Function.update_of_ne (reg_ne (by decide : rTag.val ≠ rZero.val))]]
      simpa [packedArrayEncode, rTag] using harg.1
    have hx₁_arg1 : x₁.regs rArg1 = 0 := by
      rw [show x₁.regs rArg1 = x.regs rArg1 from by
        simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rArg1.val ≠ rOne.val)),
          Function.update_of_ne (reg_ne (by decide : rArg1.val ≠ rZero.val))]]
      simpa [packedArrayEncode, rArg1] using harg.2.1
    have hx₁_arg2 : x₁.regs rArg2 = 0 := by
      rw [show x₁.regs rArg2 = x.regs rArg2 from by
        simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rArg2.val ≠ rOne.val)),
          Function.update_of_ne (reg_ne (by decide : rArg2.val ≠ rZero.val))]]
      simpa [packedArrayEncode, rArg2] using harg.2.2
    have hx₁_z : x₁.regs rZero = 0 := by
      simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rZero.val ≠ rOne.val))]
    have hx₁_o : x₁.regs rOne = 1 := by simp [x₁]
    have hx₁_base : x₁.regs rBase = base := by
      simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOne.val)),
        Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rZero.val)), hx_base]
    have hx₁_rfr : x₁.regs rFr = x₁.frontier := by
      simp [x₁, RData.set, Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rOne.val)),
        Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rZero.val)), hx_rfr]
    have hrun : (Memory.spec w).runClient { mem := x₁.mem, frontier := x₁.frontier }
        (getSetLenProg ((base, 4), (0, 0))) =
        (s.length, { mem := x₁.mem, frontier := x₁.frontier },
          [.read base, .read (base + 1), .read (base + 2)]) := by
      unfold getSetLenProg Memory.read
      simp only [bind_eq_freeMBind, StateTransitionSpec.runClient_bind,
        StateTransitionSpec.runClient_lift, StateTransitionSpec.runClient_pure',
        memory_stepFn_read, show (4 = 2) ↔ False by decide, show (4 = 3) ↔ False by decide,
        ↓reduceIte, List.nil_append, List.singleton_append]
      have hm0' : x₁.mem base = s.length := hm0
      rw [hm0']
    have hv_hist : (Memory.spec w).ValidHistory { mem := x₁.mem, frontier := x₁.frontier }
        ((Memory.spec w).clientHistory { mem := x₁.mem, frontier := x₁.frontier }
          (getSetLenProg ((base, 4), (0, 0)))) := by
      rw [StateTransitionSpec.clientHistory, hrun]
      change base < x.frontier ∧ base + 1 < x.frontier ∧ base + 2 < x.frontier ∧ True
      rw [hx_fr]; exact ⟨by omega, by omega, by omega, trivial⟩
    obtain ⟨x₂, e_gs, hx₂b, hx₂_fr, hx₂_mem, hx₂_regs, hx₂_out⟩ :=
      emitLeafCode_exec getSetLenProg_realizesBounded (by decide)
        ((le_max_right _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
        ![rBase, rTag, rArg1, rArg2]
        (fun i => by fin_cases i <;> decide) (fun i => by fin_cases i <;> decide)
        (L_peak := L_peak) ((base, 4), (0, 0)) hx₁b hL_cur hx₁_rfr
        (by funext i; fin_cases i
            · exact hx₁_base
            · exact hx₁_tag
            · exact hx₁_arg1
            · exact hx₁_arg2)
        ⟨hm2.symm, hw0, by dsimp only; change x.mem (base + 1) ≤ w; rw [hm1]; exact hbw,
          by dsimp only; change Fits w (base + 3 + packedWords (x.mem base) (x.mem (base + 1)) w)
             rw [hm0, hm1]; exact hfit_peak,
          fun h => by rcases h with h | h <;> cases h⟩
        hv_hist (by rw [StateTransitionSpec.clientState, hrun])
    have hx₂_t0 : x₂.regs rTmp0 = s.length := by
      have h0 := hx₂_out 0; rw [StateTransitionSpec.clientResult, hrun] at h0; exact h0
    set y := x₂.set rOutV (x₂.regs rTmp0)
    have e_cp : RDemonicExec (B := .exact) w L_peak (.op (.copy rOutV rTmp0)) x₂ 1 (· = y) :=
      RDemonicExec.copy (by rw [hx₂_fr]; exact hL_cur)
    have hyb : y.Bounded w := hx₂b.set (hx₂b.regs_fits _)
    have e_all : RDemonicExec w L_peak packedArraySubroutine.code x _ (· = y) :=
      e_z.seq_eq (e_o.seq_eq (RDemonicExec.branch_neg
        (by simp [Cond.Holds, hx₁_tag, hx₁_z])
        (RDemonicExec.branch_neg (by simp [Cond.Holds, hx₁_tag, hx₁_o]) (e_gs.seq_eq e_cp))))
    have hm_cost : memoryCost (getSetLenProg ((base, 4), (0, 0)))
        { mem := x₁.mem, frontier := x₁.frontier } = 3 := by
      unfold getSetLenProg Memory.read
      simp only [bind_eq_freeMBind, memoryCost_bind, StateTransitionSpec.clientState,
        StateTransitionSpec.clientResult, StateTransitionSpec.runClient_lift,
        StateTransitionSpec.runClient_pure', memory_stepFn_read,
        show (4 = 2) ↔ False by decide, show (4 = 3) ↔ False by decide, ↓reduceIte,
        memoryCost_pure]
      rfl
    have hy_mem : y.mem = x.mem := by
      change x₂.mem = x.mem
      rw [StateTransitionSpec.clientState, hrun] at hx₂_mem; exact hx₂_mem
    refine ⟨y, _, ?_, e_all, ?_, ?_, fun addr _ => by rw [hy_mem]⟩
    · simp only [hm_cost, packedArrayCharge]; omega
    · simp [packedArrayDecode, packedArrayStepFn, y, hx₂_t0]
    · dsimp only [packedArrayStepFn]
      refine ⟨hyb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [y, RData.set, Function.update_of_ne (reg_ne (by decide : rBase.val ≠ rOutV.val)),
          hx₂_regs rBase (by decide), hx₁_base]
      · simp [y, RData.set, Function.update_of_ne (reg_ne (by decide : rFr.val ≠ rOutV.val)),
          hx₂_regs rFr (by decide), hx₁_rfr, hx₂_fr]
      · simp [y, hx₂_fr, x₁, hx_fr]
      · rw [hy_mem]; exact hm0
      · rw [hy_mem]; exact hm1
      · rw [hy_mem]; exact hm2
      · intro i hi; rw [hy_mem]; exact hm_arr i hi

/-! ## 5. Certified `Resizable.StateTransitionImpl` & lifted `2×2` certificates -/

/-- Certified deterministic Resizable Word RAM implementation of the `b`-bit packed array at
arbitrary base address `base`, with resting footprint
`3 + packedWords s.length b w = ⌈s.length * b / w⌉ + 5` words in the **current** length `s.length`
(growing on `push` and shrinking on `pop`). -/
noncomputable abbrev packedArrayImpl (b w base : ℕ) (hw : 3 ≤ w) (hbw : b ≤ w) :
    DataStructure.WordRAM.Resizable.StateTransitionImpl
      packedArraySubroutine (packedArraySpec b w) w base ![b, w] [] :=
  DataStructure.WordRAM.Resizable.StateTransitionImpl.ofFn
    (spaceBound := fun s => 3 + packedWords s.length b w)
    (peakSpaceBound := packedArrayPeakSpace b w)
    (initTime := packedArrayInitTime)
    (initPotential := 0)
    (charge := fun _ _ => packedArrayCharge)
    (rep := packedArrayRep b w base)
    (potential := fun _ => 0)
    (encode := packedArrayEncode)
    (argMatch := packedArrayArgMatch)
    (decode := packedArrayDecode)
    (bounded := fun {_ _} h => by exact h.1)
    (frontier_le := fun h => by
      obtain ⟨_, hb, _, hfr, _⟩ := h
      exact ⟨by omega, by omega, hb⟩)
    (rep_supported := fun {s x x'} hregs hfr hmem hxb' hrep => by
      obtain ⟨_, hb, hrfr, hx_fr, hm0, hm1, hm2, hm_arr⟩ := hrep
      have hw0 : 0 < w := by omega
      have hp_pos : 0 < packedWords s.length b w := Nat.succ_pos _
      refine ⟨hxb', ?_, ?_, hfr.trans hx_fr, ?_, ?_, ?_, ?_⟩
      · rw [hregs rBase (by decide)]; exact hb
      · rw [hregs rFr (by decide), hfr]; exact hrfr
      · rw [hmem base (by omega) (by omega)]; exact hm0
      · rw [hmem (base + 1) (by omega) (by omega)]; exact hm1
      · rw [hmem (base + 2) (by omega) (by omega)]; exact hm2
      · intro i hi
        rw [readPacked_congr (N := s.length) hw0
          (fun addr haddr => hmem addr (by omega) (by omega)) hi]
        exact hm_arr i hi)
    (potential_supported := fun _ _ _ _ => rfl)
    (arguments_fit := fun {s} o hv i hi => by
      have hpow3 : 8 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
      have hpow_bw : 2 ^ b ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hbw
      cases o with
      | push val =>
        obtain ⟨hval, _⟩ := hv
        dsimp only [packedArrayEncode]; split_ifs <;> (unfold Fits; omega)
      | pop =>
        dsimp only [packedArrayEncode]; split_ifs <;> (unfold Fits; omega)
      | get idx =>
        obtain ⟨_, hidx⟩ := hv
        dsimp only [packedArrayEncode]; split_ifs <;> (unfold Fits; omega)
      | set idx val =>
        obtain ⟨_, hidx, hval⟩ := hv
        dsimp only [packedArrayEncode]; split_ifs <;> (unfold Fits; omega)
      | length =>
        dsimp only [packedArrayEncode]; split_ifs <;> (unfold Fits; omega))
    (encode_matches := fun o regs => by
      refine ⟨?_, ?_, ?_⟩ <;> simp [packedArraySubroutine, rTag, rArg1, rArg2])
    (init_exec := fun hx₀ hfr₀ hpar hfit₀ => by
      obtain ⟨y, n, hn, he, hrep, hcaller⟩ :=
        packedArray_init_exec hw hbw hx₀ hfr₀ hpar hfit₀
      exact ⟨y, he.mono hn fun _ hy => hy, hrep, le_rfl, hcaller⟩)
    (step_exec := fun {s x} o hrep hv harg hfit => by
      cases o with
      | push val =>
        obtain ⟨y, n, hn, he, hdec, hrep', hcaller⟩ :=
          packedArray_push_exec hw hbw hrep hv harg hfit
        exact ⟨y, n, he, hdec, hrep', hcaller, by omega⟩
      | pop =>
        obtain ⟨y, n, hn, he, hdec, hrep', hcaller⟩ :=
          packedArray_pop_exec hw hbw hrep harg hfit
        exact ⟨y, n, he, hdec, hrep', hcaller, by omega⟩
      | get idx =>
        obtain ⟨y, n, hn, he, hdec, hrep', hcaller⟩ :=
          packedArray_getSetLen_exec hw hbw (.get idx) (fun _ => nofun) nofun hrep hv harg hfit
        exact ⟨y, n, he, hdec, hrep', hcaller, by omega⟩
      | set idx val =>
        obtain ⟨y, n, hn, he, hdec, hrep', hcaller⟩ :=
          packedArray_getSetLen_exec hw hbw (.set idx val) (fun _ => nofun) nofun hrep hv harg hfit
        exact ⟨y, n, he, hdec, hrep', hcaller, by omega⟩
      | length =>
        obtain ⟨y, n, hn, he, hdec, hrep', hcaller⟩ :=
          packedArray_getSetLen_exec hw hbw .length (fun _ => nofun) nofun hrep hv harg hfit
        exact ⟨y, n, he, hdec, hrep', hcaller, by omega⟩)

/-- Lifted `Basis.standard` implementation of the resizable `b`-bit packed array. -/
noncomputable abbrev packedArrayImplStandard (b w base : ℕ) (hw : 3 ≤ w) (hbw : b ≤ w) :
    DataStructure.WordRAM.Resizable.StateTransitionImpl
      packedArraySubroutine.toStandard (packedArraySpec b w) w base ![b, w] [] :=
  (packedArrayImpl b w base hw hbw).toStandard

/-- Lifted randomized implementation of the resizable `b`-bit packed array. -/
noncomputable abbrev packedArrayImplRand (b w base : ℕ) (hw : 3 ≤ w) (hbw : b ≤ w) :
    DataStructure.WordRAM.Resizable.Randomized.StateTransitionImpl
      packedArraySubroutine (packedArraySpec b w) w base ![b, w] [] :=
  (packedArrayImpl b w base hw hbw).toRandomized

/-- Lifted oblivious-sequence implementation of the resizable `b`-bit packed array. -/
noncomputable abbrev packedArrayObliviousImpl (b w base : ℕ) (hw : 3 ≤ w) (hbw : b ≤ w) :
    DataStructure.WordRAM.Resizable.Randomized.ObliviousSequenceImpl
      packedArraySubroutine ((packedArraySpec b w).toObliviousSequenceSpec []) w base ![b, w] :=
  (packedArrayImplRand b w base hw hbw).toObliviousSequenceImplOfFn


/-! ## 6. End-to-end sequential, randomized `.rand`, and `.halt`-rejection tests -/

/-- Concrete 7-operation test sequence at `b = 5, w = 8, base = 4 > 0`:
`push 19 → push 27 → get 0 → set 0 23 → get 0 → pop → length`.
Note entry `1` (`27`, spanning bits `5..9` across words `base + 3` and `base + 4`) exercises
cross-word bit-packing, `push 27` grows `packedWords` from `3` (`n = 1`) to `4` (`n = 2`), and
`pop` shrinks `packedWords` from `4` (`n = 2`) back to `3` (`n = 1`). -/
def concreteOps : List PackedArrayOp :=
  [.push 19, .push 27, .get 0, .set 0 23, .get 0, .pop, .length]

/-- Prefix `[.push 19, .push 27]` reaching peak resting length `n = 2` (`frontier = 11`). -/
def concreteGrowPrefix : List PackedArrayOp :=
  [.push 19, .push 27]

/-- **Test A1 (Specification answers & word-straddling bit-pack check):**
Running `concreteOps` from `[]` yields final state `[23]` and exact typed observations
`[(), (), 19, (), 23, some 27, 1]`, with resting space growing from `5` (`n = 0`) to `7` (`n = 2`,
hardware frontier `4 + 7 = 11`) and shrinking back to `6` (`n = 1`, hardware frontier
`4 + 6 = 10 < 11`) after `pop`. -/
theorem concreteOps_spec_and_space :
    ((packedArraySpec 5 8).run [] concreteGrowPrefix).1 = [19, 27] ∧
    ((packedArraySpec 5 8).run [] concreteOps).1 = [23] ∧
    ((packedArraySpec 5 8).canonicalTranscript [] concreteOps).labels =
      [⟨.push 19, ()⟩, ⟨.push 27, ()⟩, ⟨.get 0, (19 : ℕ)⟩, ⟨.set 0 23, ()⟩,
       ⟨.get 0, (23 : ℕ)⟩, ⟨.pop, some 27⟩, ⟨.length, (1 : ℕ)⟩] ∧
    4 + (3 + packedWords ([] : List ℕ).length 5 8) = 9 ∧
    4 + (3 + packedWords ((packedArraySpec 5 8).run [] concreteGrowPrefix).1.length 5 8) = 11 ∧
    4 + (3 + packedWords ((packedArraySpec 5 8).run [] concreteOps).1.length 5 8) = 10 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem concreteGrowPrefix_valid :
    (packedArraySpec 5 8).ValidHistory [] concreteGrowPrefix := by
  simp [concreteGrowPrefix, StateTransitionSpec.ValidHistory, packedArraySpec,
    packedArrayValid, packedArrayStepFn]

private theorem concreteGrowPrefix_fits :
    PeakFitsHistory (D := packedArraySpec 5 8) 8 4 (packedArrayPeakSpace 5 8)
      [] concreteGrowPrefix := by
  simp [concreteGrowPrefix, PeakFitsHistory, packedArraySpec, packedArrayPeakSpace,
    packedArrayStepFn, packedWords, Fits]

private theorem concreteOps_valid :
    (packedArraySpec 5 8).ValidHistory [] concreteOps := by
  simp [concreteOps, StateTransitionSpec.ValidHistory, packedArraySpec,
    packedArrayValid, packedArrayStepFn]

private theorem concreteOps_fits :
    PeakFitsHistory (D := packedArraySpec 5 8) 8 4 (packedArrayPeakSpace 5 8) [] concreteOps := by
  simp [concreteOps, PeakFitsHistory, packedArraySpec, packedArrayPeakSpace,
    packedArrayStepFn, packedWords, Fits]

/-- **Test A2 (Sequential composition, dynamic frontier growth/shrinkage & caller `[0, 4)` frame):**
At `w = 8, b = 5, base = 4 > 0`, `packedArrayImpl` and `packedArrayImplStandard` execute
`concreteGrowPrefix` to resting hardware frontier `11` and `concreteOps` to resting hardware
frontier `10 < 11` (shrinking on `pop`), preserving all caller words `[0, 4)` and compiling to flat
`RProgram` execution (`seq_program_amortized_ofFn`) and oblivious distributional execution
(`packedArrayObliviousImpl.seq_toExecRProgramDist`). -/
theorem concreteOps_end_to_end {x₀ : RData arrRegs}
    (hx₀ : x₀.Bounded 8) (hfr₀ : x₀.frontier = 4)
    (hpar : ∀ j, x₀.regs (packedArraySubroutine.initParams j) = (![5, 8] : Fin 2 → ℕ) j) :
    let C := packedArrayImpl 5 8 4 (by decide) (by decide)
    let C_std := packedArrayImplStandard 5 8 4 (by decide) (by decide)
    let C_obl := packedArrayObliviousImpl 5 8 4 (by decide) (by decide)
    (∃ y₀ z_grow t_grow,
      RDemonicExec 8 9 packedArraySubroutine.initCode x₀ packedArrayInitTime (· = y₀) ∧
      y₀.frontier = 9 ∧
      C.ExecSteps [] y₀ concreteGrowPrefix
        ((packedArraySpec 5 8).canonicalTranscript [] concreteGrowPrefix) [19, 27] z_grow t_grow ∧
      z_grow.frontier = 11 ∧
      (∀ addr < 4, z_grow.mem addr = x₀.mem addr)) ∧
    (∃ y₀ z_fin t_prog,
      ExecRProgramDist 8 (packedArraySubroutine.toStandard.initProg rOutV) rOutV x₀ (PMF.pure y₀)
        ((packedArrayInitTime + 1 : ℕ) : ℝ≥0∞) 9 ∧
      C_std.ExecProgramSteps (packedArraySubroutine.toStandard.opProg rOutV) rOutV [] y₀
        concreteOps ((packedArraySpec 5 8).canonicalTranscript [] concreteOps) [23] z_fin t_prog ∧
      z_fin.frontier = 10 ∧
      (∀ addr < 4, z_fin.mem addr = x₀.mem addr)) ∧
    (∃ (ν₀ : PMF (LatentRState C_obl.Latent arrRegs))
       (ν_final : PMF (SeqROutcome C_obl.Latent (packedArraySpec 5 8).Result arrRegs))
       (T_prog : ℝ≥0∞),
      C_obl.ProgramSteps (packedArraySubroutine.opProg rOutV) rOutV concreteOps
        (ν₀.map SeqROutcome.ofLatentRState) ν_final T_prog ∧
      (∀ t ∈ ν_final.support, t.data.frontier ≤ 10 ∧ ∀ addr < 4, t.data.mem addr = x₀.mem addr) ∧
      ((packedArraySpec 5 8).toObliviousSequenceSpec []).Contract concreteOps
        (ν_final.map SeqROutcome.transcript)) := by
  intro C C_std C_obl
  have hfit₀ : Fits 8 (4 + (3 + packedWords ([] : List ℕ).length 5 8)) := by decide
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨y₀, z_grow, t_grow, hinit, hr₀, _, hsteps, hr_z, hcaller, _⟩ :=
      C.seq_amortized_ofFn concreteGrowPrefix hx₀ hfr₀ hpar hfit₀
        concreteGrowPrefix_valid concreteGrowPrefix_fits
    have hrun_grow : ((packedArraySpec 5 8).run [] concreteGrowPrefix).1 = [19, 27] := by decide
    rw [hrun_grow] at hsteps hr_z
    have hy₀_fr : y₀.frontier = 9 := by
      have hf := hr₀.2.2.2.1
      have h9 : 4 + 3 + packedWords ([] : List ℕ).length 5 8 = 9 := by decide
      omega
    have hz_fr : z_grow.frontier = 11 := by
      have hf := hr_z.2.2.2.1
      have h11 : 4 + 3 + packedWords ([19, 27] : List ℕ).length 5 8 = 11 := by decide
      omega
    exact ⟨y₀, z_grow, t_grow, hinit, hy₀_fr, hsteps, hz_fr, hcaller⟩
  · obtain ⟨y₀, z_fin, t_prog, hinit, _, _, hsteps, hr_z, hcaller, _⟩ :=
      C_std.seq_program_amortized_ofFn rOutV concreteOps hx₀ hfr₀ hpar hfit₀
        concreteOps_valid concreteOps_fits
    have hrun_fin : ((packedArraySpec 5 8).run [] concreteOps).1 = [23] := by decide
    rw [hrun_fin] at hsteps hr_z
    have hz_fr : z_fin.frontier = 10 := by
      have hf := hr_z.2.2.2.1
      have h10 : 4 + 3 + packedWords ([23] : List ℕ).length 5 8 = 10 := by decide
      omega
    exact ⟨y₀, z_fin, t_prog, hinit, hsteps, hz_fr, hcaller⟩
  · have hobl_valid : ((packedArraySpec 5 8).toObliviousSequenceSpec []).ValidOpSeq concreteOps :=
      ((packedArraySpec 5 8).validOpSeq_iff_validHistory [] concreteOps).mpr concreteOps_valid
    have hobl_fits : ObliviousPeakFits 8 4 C_obl.peakSpaceBound [] concreteOps :=
      (obliviousPeakFits_iff_peakFitsHistory (packedArraySpec 5 8) 8 4 (packedArrayPeakSpace 5 8)
        [] [] concreteOps).mpr concreteOps_fits
    obtain ⟨ν₀, ν_final, T_prog, _, _, hprog, hfin, hcontract, _⟩ :=
      C_obl.seq_toExecRProgramDist rOutV concreteOps hx₀ hfr₀ hpar hfit₀ hobl_valid hobl_fits
    have h10 : 4 + C_obl.spaceBound concreteOps = 10 := by
      change 4 + (3 + packedWords ((packedArraySpec 5 8).run [] concreteOps).1.length 5 8) = 10
      decide
    exact ⟨ν₀, ν_final, T_prog, hprog,
      fun t ht => ⟨h10 ▸ (hfin t ht).2.1.2.1, (hfin t ht).2.2⟩, hcontract⟩

/-! ### Test B: Direct `.rand` Resizable Word RAM subroutine -/

/-- Operations of a 1-word resizable random-coin slot: `.allocSample` grows `[base, base + 1)`,
samples a fresh uniform bit via hardware `.rand`, and stores it at `mem[base]`; `.release` shrinks
`[base, base + 1)` back to `base`. -/
inductive RandSlotOp : Type where
  | allocSample
  | release
  deriving DecidableEq

/-- Typed result of `RandSlotOp`. -/
@[expose] def RandSlotOp.Result : RandSlotOp → Type
  | _ => Unit

/-- Functional state transition of the 1-word random-coin slot (`Bool` = whether allocated). -/
@[expose] def randSlotStepFn : Bool → (o : RandSlotOp) → Bool × o.Result
  | _, .allocSample => (true, ())
  | _, .release => (false, ())

/-- Validity requires `.allocSample` when unallocated (`false`) and `.release` when allocated. -/
@[expose] def randSlotValid : Bool → RandSlotOp → Prop
  | s, .allocSample => s = false
  | s, .release => s = true

/-- Specification of the 1-word resizable random-coin slot. -/
abbrev randSlotSpec : StateTransitionSpec :=
  StateTransitionSpec.ofFn randSlotStepFn randSlotValid

/-- Direct `.rand` + `.grow` + `.shrink` subroutine over `4` registers (`0 = base`, `1 = tag`,
`2 = coin`, `3 = scratch`). -/
def randSlotSubroutine : DataStructure.WordRAM.Resizable.SubroutineCode .exact 4 0 where
  baseReg := 0
  initParams := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  input i := decide (i.val = 1)
  input_baseReg_false := by decide
  initCode :=
    .seq (.op (.const 3 1))
    (.seq (.rand 2 3)
    (.seq (.grow 0) (.op (.store 0 2))))
  code :=
    .seq (.op (.const 3 0))
    (.branch (.eq 1 3)
      (.seq (.op (.const 3 1))
      (.seq (.rand 2 3)
      (.seq (.grow 3) (.op (.store 0 2)))))
      .shrink)

private theorem write_base_demonicGrow_one {w base v : ℕ} {x : RData 4} {mem' : ℕ → ℕ}
    (hx : x.Bounded w) (hfr : x.frontier = base) (hg : DemonicGrow w base 1 x.mem mem') :
    Function.update mem' base v = Function.update x.mem base v := by
  funext a
  by_cases hab : a = base
  · subst hab; simp
  · rw [Function.update_of_ne hab, Function.update_of_ne hab]
    by_cases hlt : a < base
    · exact hg.1 a hlt
    · rw [hg.2.2 a (by omega), hx.zero_above (by omega)]

/-- Representation invariant coupling latent seed `θ : Fin 2` with `regs 2 = θ.val` and resting
frontier `base + (if s then 1 else 0)`. -/
def randSlotRep (w base : ℕ) (θ : Fin 2) (s : Bool) (x : RData 4) : Prop :=
  x.Bounded w ∧
  x.regs 0 = base ∧
  x.regs 2 = θ.val ∧
  x.frontier = base + (if s then 1 else 0)

/-- Certified direct `.rand` `Randomized.StateTransitionImpl` with non-trivial seed `Seed = Fin 2`
and uniform law `(ProbComp.unifFin 1).eval`. -/
noncomputable abbrev randSlotImpl (w base : ℕ) (hw : 1 ≤ w) :
    DataStructure.WordRAM.Resizable.Randomized.StateTransitionImpl
      randSlotSubroutine randSlotSpec w base Fin.elim0 true :=
  DataStructure.WordRAM.Resizable.Randomized.StateTransitionImpl.ofFn
    (Seed := Fin 2)
    (seedLaw := fun _ => (ProbComp.unifFin 1).eval)
    (seedSlack := 1)
    (spaceBound := fun s => if s then 1 else 0)
    (peakSpaceBound := fun _ _ => 1)
    (initTime := 4)
    (initPotential := 0)
    (charge := fun _ _ => 7)
    (rep := randSlotRep w base)
    (potential := fun _ _ => 0)
    (encode := fun o i =>
      if i.val = 1 then (match o with | .allocSample => 0 | .release => 1) else 0)
    (argMatch := fun o regs => regs 1 = (match o with | .allocSample => 0 | .release => 1))
    (decode := fun _ _ => some ())
    (bounded := fun {_ _ _} h => by exact h.1)
    (frontier_le := fun {_ _ _} h => by
      obtain ⟨_, hb, _, hfr⟩ := h; exact ⟨by omega, by omega, hb⟩)
    (rep_supported := fun {_ _ _ _} hregs hfr _ hxb' hrep => by
      obtain ⟨_, hb, hc, hx_fr⟩ := hrep
      exact ⟨hxb', (hregs 0 (by decide)).trans hb, (hregs 2 (by decide)).trans hc, hfr.trans hx_fr⟩)
    (potential_supported := fun _ _ _ _ => rfl)
    (arguments_fit := fun o _ i _ => by
      have hpow : 2 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
      cases o <;> dsimp only <;> split_ifs <;> (unfold Fits; omega))
    (encode_matches := fun o _ => by simp [randSlotSubroutine])
    (init_exec := fun {x₀} hx₀ hfr₀ _ hfit₀ => by
      have hpow : 2 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
      have h1 : Fits w 1 := by unfold Fits; omega
      set L_peak := base + 1
      set x₁ := x₀.set 3 1
      let stepPost (z : RData 4) : RData 4 :=
        ⟨Function.update z.regs 0 base, Function.update x₀.mem base (z.regs 2), base + 1⟩
      let yOf (θ : Fin 2) : RData 4 := stepPost (x₁.set 2 θ.val)
      let ν₀ : PMF (Fin 2 × RData 4) := (ProbComp.unifFin 1).eval.map fun θ => (θ, yOf θ)
      have e_c : ExecRCodeDist (B := .exact) w (.op (.const 3 1)) x₀ (PMF.pure x₁) 1 L_peak := by
        simpa using ExecRCodeDist.of_demonicExec
          (RDemonicExec.const (B := .exact) (L_peak := L_peak) (d := 3) (by rw [hfr₀]; omega) h1)
      have e_r : ExecRCodeDist (B := .exact) w (.rand 2 3) x₁
          ((ProbComp.unifFin 1).eval.map fun θ => x₁.set 2 θ.val) 1 L_peak :=
        (ExecRCodeDist.rand (B := .exact) (x := x₁) (by simp [x₁]; omega)
          (by simp [x₁, h1])).congr_dist rfl le_rfl
      have e_gs : ∀ z ∈ ((ProbComp.unifFin 1).eval.map fun θ => x₁.set 2 θ.val).support,
          ExecRCodeDist (B := .exact) w (.seq (.grow 0) (.op (.store 0 2))) z
            (PMF.pure (stepPost z)) 2 L_peak := by
        intro z hz
        rw [PMF.mem_support_map_iff] at hz; obtain ⟨θ, _, rfl⟩ := hz
        refine .of_demonicExec (RDemonicExec.grow_seq (T := 1) (by simp [x₁]; omega)
          (by simpa [x₁, hfr₀] using hfit₀) fun mem' hg => ?_)
        refine (RDemonicExec.store (by dsimp only [x₁, RData.set]; rw [hfr₀])
          (by simp)).mono le_rfl ?_
        rintro _ rfl; ext j
        · simp [stepPost, x₁, RData.set, RData.write, hfr₀]
        · have hm := write_base_demonicGrow_one (v := θ.val) hx₀ hfr₀ (by simpa [x₁, hfr₀] using hg)
          simpa [stepPost, x₁, RData.set, RData.write, hfr₀,
            Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0)] using congrFun hm j
        · simp [stepPost, x₁, hfr₀]
      have e_tail : ExecRCodeDist (B := .exact) w
          (.seq (.rand 2 3) (.seq (.grow 0) (.op (.store 0 2)))) x₁
          (ν₀.map Prod.snd) 3 L_peak := by
        refine (ExecRCodeDist.seq e_r e_gs).congr_dist ?_ ?_
        · simp only [ν₀, yOf, PMF.map, Function.comp_apply, PMF.bind_bind, PMF.pure_bind]
        · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]; norm_num
      have e_init : ExecRCodeDist w randSlotSubroutine.initCode x₀ (ν₀.map Prod.snd) 4 L_peak := by
        refine (ExecRCodeDist.seq (μ₂ := fun _ => ν₀.map Prod.snd)
            (T₂ := fun _ => 3) e_c fun z hz => ?_).congr_dist ?_ ?_
        · rw [PMF.support_pure, Set.mem_singleton_iff] at hz; subst hz; exact e_tail
        · simp
        · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]; norm_num
      refine ⟨ν₀, e_init, fun θ => ?_, fun p hp => ?_⟩
      · simp only [ν₀, PMF.map, Function.comp_apply, PMF.bind_bind, PMF.pure_bind,
          PMF.bind_pure, one_mul]
        exact le_rfl
      rw [PMF.mem_support_map_iff] at hp; obtain ⟨θ, _, rfl⟩ := hp
      have hθ : Fits w θ.val := by have := θ.isLt; unfold Fits; omega
      have hyb : (yOf θ).Bounded w := by
        have hb1 : (x₁.set 2 θ.val).Bounded w := (hx₀.set h1).set hθ
        have hgrow0 := demonicGrow_clear w base 1 x₀.mem fun _ ha => hx₀.zero_above (hfr₀ ▸ ha)
        have hb3 := hb1.grow (dst := 0) (hfr₀ ▸ hfit₀) (by simpa [x₁, hfr₀] using hgrow0)
        have hb4 := hb3.write (a := base) (v := θ.val) (by simp [x₁, hfr₀]) hθ
        convert hb4 using 1
        ext j
        · simp [yOf, stepPost, x₁, hfr₀]
        · have hm := write_base_demonicGrow_one (v := θ.val) hx₀ hfr₀ hgrow0
          simpa [yOf, stepPost, x₁, RData.write] using congrFun hm.symm j
        · simp [yOf, stepPost, x₁, hfr₀]
      refine ⟨⟨hyb, by simp [yOf, stepPost], ?_, by simp [yOf, stepPost]⟩, le_rfl,
        fun addr hlt => ?_⟩
      · simp [yOf, stepPost, x₁, RData.set]
      · simp [yOf, stepPost, Function.update_of_ne (by omega : addr ≠ base)])
    (step_exec := fun {s} o ν hv hfit hseed hsupp => by
      have hpow : 2 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
      have h1 : Fits w 1 := by unfold Fits; omega
      set L_peak := base + 1
      cases o with
      | allocSample =>
        have hs_eq : s = false := hv
        subst hs_eq
        let stepPost (p : Fin 2 × RData 4) (z : RData 4) : RData 4 :=
          ⟨Function.update z.regs 3 base, Function.update p.2.mem base (z.regs 2), base + 1⟩
        let yOf (p : Fin 2 × RData 4) (θ' : Fin 2) : RData 4 :=
          stepPost p (((p.2.set 3 0).set 3 1).set 2 θ'.val)
        let μ_step (p : Fin 2 × RData 4) : PMF (Fin 2 × RData 4) :=
          (ProbComp.unifFin 1).eval.map fun θ' => (θ', yOf p θ')
        refine ⟨μ_step, fun _ => 7, fun p hp => ?_, ?_, ?_⟩
        · obtain ⟨⟨hpb, hp_base, _, hp_fr⟩, harg⟩ := hsupp p hp
          have hp_fr' : p.2.frontier = base := by simpa using hp_fr
          set x₁ := p.2.set 3 0
          set x₂ := x₁.set 3 1
          have e_z : ExecRCodeDist (B := .exact) w (.op (.const 3 0)) p.2
              (PMF.pure x₁) 1 L_peak := by
            simpa using ExecRCodeDist.of_demonicExec
              (RDemonicExec.const (B := .exact) (L_peak := L_peak) (d := 3)
                (by rw [hp_fr']; omega) (fits_zero w))
          have e_c : ExecRCodeDist (B := .exact) w (.op (.const 3 1)) x₁
              (PMF.pure x₂) 1 L_peak := by
            simpa using ExecRCodeDist.of_demonicExec
              (RDemonicExec.const (B := .exact) (L_peak := L_peak) (d := 3)
                (by simp [x₁, hp_fr', L_peak]) h1)
          have e_r : ExecRCodeDist (B := .exact) w (.rand 2 3) x₂
              ((ProbComp.unifFin 1).eval.map fun θ' => x₂.set 2 θ'.val) 1 L_peak :=
            (ExecRCodeDist.rand (B := .exact) (x := x₂) (by simp [x₂, x₁, hp_fr', L_peak])
              (by simp [x₂, h1])).congr_dist rfl le_rfl
          have e_gs : ∀ z ∈ ((ProbComp.unifFin 1).eval.map fun θ' => x₂.set 2 θ'.val).support,
              ExecRCodeDist (B := .exact) w (.seq (.grow 3) (.op (.store 0 2))) z
                (PMF.pure (stepPost p z)) 2 L_peak := by
            intro z hz
            rw [PMF.mem_support_map_iff] at hz; obtain ⟨θ', _, rfl⟩ := hz
            have hz_b : (x₂.set 2 θ'.val).regs 0 = base := by
              simp [x₂, x₁, RData.set, hp_base]
            refine .of_demonicExec (RDemonicExec.grow_seq (T := 1)
              (by simp [x₂, x₁, hp_fr', L_peak])
              (by simpa [x₂, x₁, hp_fr'] using hfit) fun mem' hg => ?_)
            refine (RDemonicExec.store (by dsimp only [x₂, x₁, RData.set]; rw [hp_fr'])
              (by simp [x₂, x₁, RData.set, hp_base, hp_fr'])).mono le_rfl ?_
            rintro _ rfl; ext j
            · simp [stepPost, x₂, x₁, RData.set, RData.write, hp_fr']
            · have hm := write_base_demonicGrow_one (v := θ'.val) hpb hp_fr'
                (by simpa [x₂, x₁, hp_fr'] using hg)
              simpa [stepPost, x₂, x₁, RData.set, RData.write, hp_fr', hp_base] using
                congrFun hm j
            · simp [stepPost, x₂, x₁, hp_fr']
          have e_tail : ExecRCodeDist (B := .exact) w
              (.seq (.rand 2 3) (.seq (.grow 3) (.op (.store 0 2)))) x₂
              ((μ_step p).map Prod.snd) 3 L_peak := by
            refine (ExecRCodeDist.seq e_r e_gs).congr_dist ?_ ?_
            · simp only [μ_step, yOf, x₂, x₁, PMF.map, Function.comp_apply, PMF.bind_bind,
                PMF.pure_bind]
            · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]; norm_num
          have e_br_body : ExecRCodeDist (B := .exact) w
              (.seq (.op (.const 3 1)) (.seq (.rand 2 3) (.seq (.grow 3) (.op (.store 0 2))))) x₁
              ((μ_step p).map Prod.snd) 4 L_peak := by
            refine (ExecRCodeDist.seq (μ₂ := fun _ => (μ_step p).map Prod.snd)
                (T₂ := fun _ => 3) e_c fun z hz => ?_).congr_dist ?_ ?_
            · rw [PMF.support_pure, Set.mem_singleton_iff] at hz; subst hz; exact e_tail
            · simp
            · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]; norm_num
          have e_br : ExecRCodeDist (B := .exact) w
              (.branch (.eq 1 3)
                (.seq (.op (.const 3 1)) (.seq (.rand 2 3) (.seq (.grow 3) (.op (.store 0 2)))))
                .shrink)
              x₁ ((μ_step p).map Prod.snd) 5 L_peak :=
            (ExecRCodeDist.branch_pos (cond := .eq 1 3)
              (by simp [Cond.Holds, x₁, RData.set, harg]) e_br_body).mono (by norm_num)
          have e_full : ExecRCodeDist w randSlotSubroutine.code p.2 ((μ_step p).map Prod.snd)
              7 L_peak := by
            refine (ExecRCodeDist.seq (μ₂ := fun _ => (μ_step p).map Prod.snd)
                (T₂ := fun _ => 5) e_z fun z hz => ?_).congr_dist ?_ ?_
            · rw [PMF.support_pure, Set.mem_singleton_iff] at hz; subst hz; exact e_br
            · simp
            · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]; norm_num
          refine ⟨e_full, fun q hq => ?_⟩
          dsimp only [μ_step] at hq; rw [PMF.mem_support_map_iff] at hq
          obtain ⟨θ', _, rfl⟩ := hq
          have hθ' : Fits w θ'.val := by have := θ'.isLt; unfold Fits; omega
          have hyb : (yOf p θ').Bounded w := by
            have hb1 : (x₂.set 2 θ'.val).Bounded w :=
              ((hpb.set (fits_zero w)).set h1).set hθ'
            have hgrow0 :=
              demonicGrow_clear w base 1 p.2.mem fun _ ha => hpb.zero_above (hp_fr' ▸ ha)
            have hb3 := hb1.grow (dst := 3) (by simpa [x₂, x₁, hp_fr', L_peak] using hfit)
              (by simpa [x₂, x₁, hp_fr'] using hgrow0)
            have hb4 := hb3.write (a := base) (v := θ'.val) (by simp [x₂, x₁, hp_fr']) hθ'
            convert hb4 using 1
            ext j
            · simp [yOf, stepPost, x₂, x₁, hp_fr']
            · have hm := write_base_demonicGrow_one (v := θ'.val) hpb hp_fr' hgrow0
              simpa [yOf, stepPost, x₂, x₁, RData.write] using congrFun hm.symm j
            · simp [yOf, stepPost, x₂, x₁, hp_fr']
          refine ⟨rfl, ⟨hyb, ?_, ?_, by simp [yOf, stepPost, randSlotStepFn]⟩,
            fun addr hlt => ?_⟩
          · simp [yOf, stepPost, RData.set, hp_base]
          · simp [yOf, stepPost, RData.set]
          · simp [yOf, stepPost, Function.update_of_ne (by omega : addr ≠ base)]
        · intro θ'
          rw [PMF.map_bind]
          have hmap_fst : ∀ p, (μ_step p).map Prod.fst = (ProbComp.unifFin 1).eval := fun p => by
            simp only [μ_step, PMF.map, Function.comp_apply, PMF.bind_bind, PMF.pure_bind,
              PMF.bind_pure]
          simp [hmap_fst, PMF.bind_const]
        · simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero]
          rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
          simp
      | release =>
        have hs_eq : s = true := hv
        subst hs_eq
        let shrData (x : RData 4) : RData 4 :=
          ⟨(x.set 3 0).regs, clear x.mem base 1, base⟩
        let μ_step (p : Fin 2 × RData 4) : PMF (Fin 2 × RData 4) :=
          PMF.pure (p.1, shrData p.2)
        refine ⟨μ_step, fun _ => 7, fun p hp => ?_, ?_, ?_⟩
        · obtain ⟨⟨hpb, hp_base, hp_coin, hp_fr⟩, harg⟩ := hsupp p hp
          have hp_fr' : p.2.frontier = base + 1 := by simpa using hp_fr
          have e_z : RDemonicExec (B := .exact) w L_peak (.op (.const 3 0)) p.2 1
              (· = p.2.set 3 0) :=
            RDemonicExec.const (L_peak := L_peak) (d := 3) (by rw [hp_fr']) (fits_zero w)
          have e_sh : RDemonicExec (B := .exact) w L_peak .shrink (p.2.set 3 0) 1
              (· = shrData p.2) := by
            refine (RDemonicExec.shrink (by simp [hp_fr']; omega) (by simp [hp_fr']) rfl).mono
              le_rfl ?_
            rintro _ rfl; ext j <;> simp [shrData, hp_fr']
          have e_br := RDemonicExec.branch_neg
            (c := .eq 1 3)
            (pos := .seq (.op (.const 3 1))
              (.seq (.rand 2 3) (.seq (.grow 3) (.op (.store 0 2)))))
            (by simp [Cond.Holds, RData.set, harg]) e_sh
          have e_dem : RDemonicExec w L_peak randSlotSubroutine.code p.2 4 (· = shrData p.2) :=
            e_z.seq_eq e_br
          have e_dist : ExecRCodeDist w randSlotSubroutine.code p.2 ((μ_step p).map Prod.snd)
              7 L_peak :=
            (ExecRCodeDist.of_demonicExec e_dem).congr_dist (by simp [μ_step]) (by norm_num)
          refine ⟨e_dist, fun q hq => ?_⟩
          dsimp only [μ_step] at hq
          rw [PMF.support_pure, Set.mem_singleton_iff] at hq; subst hq
          have hsb : (shrData p.2).Bounded w := rDemonicExec_eq_bounded e_dem hpb
          refine ⟨rfl, ⟨hsb, by simp [shrData, RData.set, hp_base],
            by simp [shrData, RData.set, hp_coin],
            by simp [randSlotSpec, randSlotStepFn, shrData]⟩,
            fun addr hlt => ?_⟩
          dsimp only [shrData]
          exact clear_of_not_owns (by simp only [Block.Owns]; omega)
        · intro θ'
          have hfst : (ν.bind μ_step).map Prod.fst = ν.map Prod.fst := by
            simp only [μ_step, PMF.map, PMF.bind_bind, PMF.pure_bind]; rfl
          rw [hfst]
          exact hseed θ'
        · simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero]
          rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]
          simp)

/-- **Test B (`seq_expected_amortized_ofFn` on a genuine `.rand` Resizable Word RAM subroutine):**
Running `[.release, .allocSample, .release]` from `s₀ = true` at `w = 8, base = 4` exercises
hardware `.rand`, `.grow`, and `.shrink` directly under `Randomized.StateTransitionImpl`. -/
theorem randSlot_end_to_end {x₀ : RData 4} (hx₀ : x₀.Bounded 8) (hfr₀ : x₀.frontier = 4) :
    let ops : List RandSlotOp := [.release, .allocSample, .release]
    ∃ (ν₀ ν_final : PMF ((randSlotImpl 8 4 (by decide)).Seed × RData 4)) (T_ops : ℝ≥0∞),
      ExecRCodeDist 8 randSlotSubroutine.initCode x₀ (ν₀.map Prod.snd) 4 5 ∧
      (randSlotImpl 8 4 (by decide)).ExecStepsOfFn true ops ν₀ ν_final T_ops ∧
      (∀ p ∈ ν_final.support, p.2.frontier = 4 ∧ ∀ addr < 4, p.2.mem addr = x₀.mem addr) ∧
      4 + T_ops ≤ 4 + 21 := by
  intro ops
  let C := randSlotImpl 8 4 (by decide)
  have hv : randSlotSpec.ValidHistory true ops := by
    simp [ops, StateTransitionSpec.ValidHistory, randSlotSpec, randSlotValid, randSlotStepFn]
  have hfit₀ : Fits 8 (4 + C.spaceBound true) := by decide
  have hfit_ops : PeakFitsHistory (D := randSlotSpec) 8 4 C.peakSpaceBound true ops := by
    simp [ops, PeakFitsHistory, C, Fits]
  obtain ⟨ν₀, ν_final, T_ops, he_init, _, hex, _, hfin, hamort⟩ :=
    C.seq_expected_amortized_ofFn ops hx₀ hfr₀ (fun j => Fin.elim0 j) hfit₀ hv hfit_ops
  refine ⟨ν₀, ν_final, T_ops, he_init, hex, fun p hp => ?_, ?_⟩
  · obtain ⟨hrep, hcaller⟩ := hfin p hp
    have hrun : (randSlotSpec.run true ops).1 = false := rfl
    rw [hrun] at hrep
    exact ⟨by simpa using hrep.2.2.2, hcaller⟩
  · have hcost : randSlotSpec.totalCost C.charge true ops = 21 := rfl
    simpa [hcost, C, randSlotImpl] using hamort

/-! ### Test C: `.halt`-rejection soundness tests on compiled flat `RProgram` certificates -/

/-- **Test C1 (Deterministic `.halt`-rejection):** a 1-instruction `[.halt rOutV]` stub cannot
satisfy `(packedArrayImpl 5 8 4 ...).ExecProgramSteps` on `push 19` from `[]`. -/
theorem packedArray_not_execProgramSteps_halt {x z : RData arrRegs}
    (hrep : packedArrayRep 5 8 4 [] x) {tr : (packedArraySpec 5 8).Transcript}
    {s_fin : List ℕ} {t_prog : ℕ} :
    ¬(packedArrayImpl 5 8 4 (by decide) (by decide)).ExecProgramSteps
      [.halt rOutV] rOutV [] x [.push 19] tr s_fin z t_prog := by
  apply DataStructure.WordRAM.Resizable.StateTransitionImpl.not_execProgramSteps_halt
  rintro s₁ a ⟨rfl, rfl⟩ ⟨_, hrep₁⟩
  have hm_old : x.mem 4 = 0 := hrep.2.2.2.2.1
  have hm_new : x.mem 4 = 1 := hrep₁.2.2.2.2.1
  omega

/-- **Test C2 (Randomized `.halt`-rejection):** a 1-instruction `[.halt rOutV]` stub cannot
satisfy `(packedArrayImplRand 5 8 4 ...).ExecProgramStepsOfFn` on `push 19` from `[]`. -/
theorem packedArrayRand_not_execProgramStepsOfFn_halt {x : RData arrRegs}
    (hrep : packedArrayRep 5 8 4 [] x) {ν_final : PMF (Unit × RData arrRegs)} {T_prog : ℝ≥0∞} :
    ¬(packedArrayImplRand 5 8 4 (by decide) (by decide)).ExecProgramStepsOfFn
      [.halt rOutV] rOutV [] [.push 19] (PMF.pure ((), x)) ν_final T_prog := by
  apply DataStructure.WordRAM.Resizable.Randomized.StateTransitionImpl.not_execProgramStepsOfFn_halt
    _ rOutV (p := ((), x)) (by simp)
  rintro ⟨⟩ ⟨_, hrep₁⟩
  have hm_old : x.mem 4 = 0 := hrep.2.2.2.2.1
  have hm_new : x.mem 4 = 1 := hrep₁.2.2.2.2.1
  omega

/-- **Test C3 (Oblivious-sequence `.halt`-rejection):** from initial prefix `[]`, if
`t.data.regs rOutV = 1`, a 1-instruction `[.halt rOutV]` stub cannot simultaneously satisfy
`ProgramSteps` on `[.length]` and `Contract [.length]` (which requires answer `0 ≠ 1`). -/
theorem packedArrayOblivious_not_execProgramSteps_halt
    {t : SeqROutcome (packedArrayObliviousImpl 5 8 4 (by decide) (by decide)).Latent
      (packedArraySpec 5 8).Result arrRegs}
    {ν ν_final : PMF (SeqROutcome (packedArrayObliviousImpl 5 8 4 (by decide) (by decide)).Latent
      (packedArraySpec 5 8).Result arrRegs)}
    {T_prog : ℝ≥0∞}
    (ht : t ∈ ν.support) (htr : t.transcript = []) (hout1 : t.data.regs rOutV = 1)
    (hcontract : ((packedArraySpec 5 8).toObliviousSequenceSpec []).Contract
      [PackedArrayOp.length] (ν_final.map SeqROutcome.transcript)) :
    ¬(packedArrayObliviousImpl 5 8 4 (by decide) (by decide)).ProgramSteps
      [.halt rOutV] rOutV [PackedArrayOp.length] ν ν_final T_prog := by
  apply DataStructure.WordRAM.Resizable.Randomized.not_execProgramSteps_halt rOutV ht
  intro a hdec _ _ u hu hpref
  have hprep_out :
      (packedArraySubroutine.prepare packedArrayEncode PackedArrayOp.length t.data).regs rOutV =
        1 := by
    rw [packedArraySubroutine.prepare_regs_of_not_input (i := rOutV) (by decide)
      PackedArrayOp.length t.data, hout1]
  have ha1 : a = (1 : ℕ) := by
    change packedArrayDecode PackedArrayOp.length
      (packedArraySubroutine.prepare packedArrayEncode PackedArrayOp.length t.data).regs =
      some a at hdec
    dsimp only [packedArrayDecode] at hdec
    rw [hprep_out] at hdec
    exact Option.some.inj hdec.symm
  subst ha1
  have hu_mem : u.transcript ∈ (ν_final.map SeqROutcome.transcript).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨u, hu, rfl⟩
  obtain ⟨tr_u, s_u, hops_u, hlbl_u, htr_v⟩ := hcontract u.transcript hu_mem
  obtain ⟨_, _, hcanon⟩ := ((packedArraySpec 5 8).validTranscript_iff_run [] tr_u s_u).mp htr_v
  rw [hops_u] at hcanon
  rw [htr, List.nil_append, ← hlbl_u, hcanon] at hpref
  obtain ⟨rest, hcons⟩ := hpref
  injection hcons with hstep_eq _
  cases hstep_eq

end CslibFrontierTests.WordRAMResizableDataStructure
