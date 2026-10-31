/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.AcceptCount
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Blocks
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.ChoiceTable
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Interval tensors of a choice-string run

The local pieces of the block-counting identity, Lemma 2.2 of the note *Deterministic
simulations of nondeterministic and randomized time* (30 October 2026) formalized in issue #1833,
which builds on the blocking of Hopcroft, Paul and Valiant [HopcroftPaulValiant1977] in the
three-block form of `Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Blocks`
(compare [Williams2025], Lemma 2.1 and §3.2). The proof idea is original to that note.

Fix a block length `b > 0`. A configuration of a fair-coin table over `Bool` is seen through

* its *block indices* `Turing.Cfg.blockIndex`: the block `p / b` of every head;
* its *control record* `Turing.Cfg.blockControl`: its state, the offset `p mod b` of every head
  in its block, and the track (`Turing.MultiTapeNTM.ChoiceTable.OutputTrack`) of its output;
* its *window contents* `Turing.Cfg.windowContents`: the contents of the three blocks
  `J - 1, J, J + 1` around given block indices `J` on every work tape.

Conversely, `Turing.embedCfg` builds a configuration from block indices, a control record and
window contents, with blank cells outside the windows and an output of the right track. The
*interval step* `Turing.MultiTapePTM.IntervalStep` replays the bits of a time interval from such
an embedded configuration and compares the record, window contents and block indices it leaves
with prescribed ones. The *interval tensor* `Turing.MultiTapePTM.intervalCount` counts the bit
strings `u ∈ {0,1}^b` doing so: the entry `F_i` of the note's equation (3).

**Matching the true run** (`Turing.MultiTapePTM.intervalStep_view_iff`). Embedding the view of a
configuration `c` gives a configuration that agrees with `c` on its state, its heads and its
windows, and whose output has the same track. By the locality of runs
(`Turing.MultiTapePTM.agreeOn_blockWindow_stepCoins`), an interval step from the view of `c`
holds exactly when the true replay from `c` leaves the prescribed record, contents and block
indices. The input tape is not blocked as a word: it is fixed by `input`, which the embedded
configuration shares.

**Splitting the count by schedules** (`Turing.MultiTapePTM.acceptCount_eq_sum_card_schedule`).
The accepting count `A_M(x)` on `q * b` bits is the sum, over the movement schedules `σ` of `q`
intervals, of the number of accepting choice strings with schedule `σ`. The bits of interval `i`
of a choice string `y : Fin (q * b) → Bool` are `y (finProdFinEquiv (i, r))` for `r < b`
(`Turing.MultiTapePTM.intervalStart_succ_ofFn`).

## Main definitions

* `Turing.Cfg.blockIndex`, `Turing.Cfg.blockContents`, `Turing.Cfg.windowContents`: block
  indices and block contents.
* `Turing.BlockControl`, `Turing.Cfg.blockControl`: control records.
* `Turing.embedCfg`: the configuration with given block indices, record and window contents.
* `Turing.MultiTapePTM.IntervalStep`, `Turing.MultiTapePTM.intervalCount`: interval steps and
  interval tensors.

## Main results

* `Turing.MultiTapePTM.acceptCount_eq_sum_card_schedule`: the accepting count split by schedules.
* `Turing.MultiTapePTM.intervalStart_succ_ofFn`: the bits of each interval.
* `Turing.agreeOn_embedCfg_view`: an embedded view agrees with the configuration on its windows.
* `Turing.MultiTapePTM.intervalStep_view_iff`: interval steps from a view are the true replay.
* `Turing.MultiTapePTM.intervalCount_le`: interval tensor entries are at most `2 ^ b`.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On Time Versus Space*][HopcroftPaulValiant1977]
* [R. Williams, *Simulating Time With Square-Root Space*][Williams2025]
-/

public section

namespace Turing

open MultiTapeNTM.ChoiceTable

variable {k : ℕ} {Symbol State : Type}

/-! ### Views of a configuration -/

section View

variable (b : ℕ) [NeZero b] {input : List Symbol}

/-- The block index of every head, with blocks of length `b`: a head at coordinate `p` is in
block `p / b`. -/
@[expose] def Cfg.blockIndex (c : Cfg k Symbol State input) (head : Option (Fin k)) : ℤ :=
  c.headPos head / b

/-- The contents of block `j` of work tape `h`, with blocks of length `b`: the cells
`b * j + r` for `r < b`. -/
@[expose] def Cfg.blockContents (c : Cfg k Symbol State input) (h : Fin k) (j : ℤ) :
    ZMod b → Option Symbol :=
  fun r => c.workTapes h (b * j + r.val)

/-- The contents of the three blocks `J h - 1, J h, J h + 1` around block indices `J` on every
work tape `h`; entry `d : Fin 3` is block `J h + d - 1`. -/
@[expose] def Cfg.windowContents (J : Option (Fin k) → ℤ) (c : Cfg k Symbol State input) :
    Fin k → Fin 3 → ZMod b → Option Symbol :=
  fun h d => c.blockContents b h (J (some h) + d - 1)

end View

section Embed

variable (b : ℕ) [NeZero b] {input : List Bool}

/-- A *control record* with blocks of length `b`: a state, the offset of every head in its block,
and the track of the output. -/
abbrev BlockControl (k : ℕ) (State : Type) (b : ℕ) :=
  Option State × (Option (Fin k) → ZMod b) × OutputTrack

/-- The control record of a configuration: its state, the offset `p mod b` of every head, and the
track of its output. -/
@[expose] def Cfg.blockControl (c : Cfg k Bool State input) :
    BlockControl k State b :=
  (c.state, fun head => (c.headPos head : ZMod b), OutputTrack.ofWord c.output)

/-- The input head position with coordinate `p`, that is, stored position `p + 1`, or the
left end when `p + 1` is out of range. -/
@[expose] def inputPosOfCoord (input : List Bool) (p : ℤ) : Fin (input.length + 2) :=
  if h : 0 ≤ p + 1 ∧ p + 1 < input.length + 2 then ⟨(p + 1).toNat, by omega⟩ else 0

/-- Cell `z` of work tape `h` of the configuration with window contents `w` at block indices `J`:
the entry of `w` if `z` lies in one of the three blocks around `J h`, and blank otherwise. -/
@[expose] def windowCell (J : Option (Fin k) → ℤ) (w : Fin k → Fin 3 → ZMod b → Option Bool)
    (h : Fin k) (z : ℤ) : Option Bool :=
  if hz : 0 ≤ z / b - J (some h) + 1 ∧ z / b - J (some h) + 1 < 3 then
    w h ⟨(z / b - J (some h) + 1).toNat, by omega⟩ z
  else none

/-- The configuration with block indices `J`, control record `c` and window contents `w`: every
head at `b * J + offset`, the work tapes holding `w` on the windows and blank elsewhere, and an
output with the track of `c`. -/
@[expose] def embedCfg (J : Option (Fin k) → ℤ) (c : BlockControl k State b)
    (w : Fin k → Fin 3 → ZMod b → Option Bool) : Cfg k Bool State input where
  state := c.1
  inputPos := inputPosOfCoord input (b * J none + (c.2.1 none).val)
  workTapes := windowCell b J w
  workTapePos h := b * J (some h) + (c.2.1 (some h)).val
  output := c.2.2.toWord

variable {b}

/-- A coordinate is its block start plus its offset. -/
private theorem mul_ediv_add_val_intCast (p : ℤ) :
    (b : ℤ) * (p / b) + ((p : ZMod b).val : ℤ) = p := by
  rw [ZMod.val_intCast]
  exact Int.mul_ediv_add_emod p b

omit [NeZero b] in
/-- The embedded configuration has the output track of its record. -/
@[simp] theorem ofWord_output_embedCfg (J : Option (Fin k) → ℤ) (c : BlockControl k State b)
    (w : Fin k → Fin 3 → ZMod b → Option Bool) :
    OutputTrack.ofWord (embedCfg (input := input) b J c w).output = c.2.2 :=
  OutputTrack.ofWord_toWord _

/-- The cells of the window entries lie in the three blocks around the block index. -/
private theorem mem_blockWindow_of_window {c : Cfg k Bool State input} (h : Fin k) (d : Fin 3)
    (r : ZMod b) :
    b * (c.blockIndex b (some h) + d - 1) + (r.val : ℤ) ∈ c.blockWindow b h := by
  have hb : (0 : ℤ) < b := by exact_mod_cast Nat.pos_of_neZero b
  have hr : (r.val : ℤ) < b := by exact_mod_cast ZMod.val_lt r
  have hd : ((d : ℕ) : ℤ) < 3 := by exact_mod_cast d.isLt
  simp only [Cfg.blockWindow, Cfg.blockIndex, Cfg.headPos_some, Set.mem_Ico]
  constructor <;> nlinarith

/-- **An embedded view agrees with the configuration.** Embedding the block indices, control
record and window contents of `c` gives a configuration with the state, heads and window contents
of `c`. -/
theorem agreeOn_embedCfg_view (c : Cfg k Bool State input) :
    (embedCfg b (c.blockIndex b) (c.blockControl b)
      (c.windowContents b (c.blockIndex b))).AgreeOn (c.blockWindow b) c := by
  have hb : (0 : ℤ) < b := by exact_mod_cast Nat.pos_of_neZero b
  refine ⟨rfl, ?_, ?_, fun h z hz => ?_⟩
  · -- The input head is at its coordinate plus one, which is in range.
    have hpos := mul_ediv_add_val_intCast (b := b) (c.headPos none)
    have hlt := c.inputPos.isLt
    change inputPosOfCoord input
      (b * (c.headPos none / b) + ((c.headPos none : ZMod b)).val) = c.inputPos
    rw [hpos, Cfg.headPos_none]
    unfold inputPosOfCoord
    split_ifs with hcond
    · ext
      simp only
      omega
    · exact absurd ⟨by omega, by omega⟩ hcond
  · funext h
    exact mul_ediv_add_val_intCast (c.headPos (some h))
  · -- A window cell `z` is entry `z / b - J + 1` of the window, at offset `z mod b`.
    simp only [Cfg.blockWindow, Set.mem_Ico] at hz
    have hlo := Int.emod_nonneg z hb.ne'
    have hhi := Int.emod_lt_of_pos z hb
    have hval := mul_ediv_add_val_intCast (b := b) z
    have hdiv := Int.mul_ediv_add_emod z b
    have hJ : c.blockIndex b (some h) = c.workTapePos h / b := rfl
    have h₁ : c.workTapePos h / b - 1 ≤ z / b := by
      by_contra hcon
      have : b * (z / b) ≤ b * (c.workTapePos h / b - 2) :=
        mul_le_mul_of_nonneg_left (by omega) hb.le
      nlinarith
    have h₂ : z / b < c.workTapePos h / b + 2 := by
      by_contra hcon
      have : b * (c.workTapePos h / b + 2) ≤ b * (z / b) :=
        mul_le_mul_of_nonneg_left (by omega) hb.le
      nlinarith
    have hcond : 0 ≤ z / b - c.blockIndex b (some h) + 1 ∧
        z / b - c.blockIndex b (some h) + 1 < 3 := by
      rw [hJ]
      omega
    change windowCell b (c.blockIndex b) (c.windowContents b (c.blockIndex b)) h z = _
    rw [windowCell, dite_eq_left hcond]
    simp only [Cfg.windowContents, Cfg.blockContents]
    rw [Int.toNat_of_nonneg hcond.1,
      show c.blockIndex b (some h) + (z / b - c.blockIndex b (some h) + 1) - 1 = z / b by ring,
      hval]

end Embed

namespace MultiTapePTM

variable (machine : MultiTapePTM k Bool State) {input : List Bool}

/-! ### Interval steps and interval tensors -/

section Interval

variable (b : ℕ) [NeZero b]

/-- **An interval step.** Replaying `coins` from the configuration embedded at block indices `J`
with entering control record `cIn` and window contents `wIn` leaves the control record `cOut`,
the contents `wOut` of the same windows, and moves the block of every head `h` by `δ h`. -/
def IntervalStep (input : List Bool) (J : Option (Fin k) → ℤ) (δ : Option (Fin k) → SignType)
    (cIn : BlockControl k State b) (wIn : Fin k → Fin 3 → ZMod b → Option Bool)
    (coins : List Bool) (cOut : BlockControl k State b)
    (wOut : Fin k → Fin 3 → ZMod b → Option Bool) : Prop :=
  (machine.stepCoins coins (embedCfg (input := input) b J cIn wIn)).blockControl b = cOut ∧
    (machine.stepCoins coins (embedCfg (input := input) b J cIn wIn)).windowContents b J = wOut ∧
    ∀ head, (machine.stepCoins coins (embedCfg (input := input) b J cIn wIn)).blockIndex b head =
      J head + δ head

open scoped Classical in
/-- **The interval tensor**: the number of bit strings `u ∈ {0,1}^b` whose replay is an interval
step from the entering record `cIn` and contents `wIn` at block indices `J` to the leaving record
`cOut` and contents `wOut`, moving the blocks by `δ`. This is the entry `F_i` of the note's
equation (3). -/
noncomputable def intervalCount (input : List Bool) (J : Option (Fin k) → ℤ)
    (δ : Option (Fin k) → SignType) (cIn : BlockControl k State b)
    (wIn : Fin k → Fin 3 → ZMod b → Option Bool)
    (cOut : BlockControl k State b) (wOut : Fin k → Fin 3 → ZMod b → Option Bool) : ℕ :=
  (Finset.univ.filter fun u : Fin b → Bool =>
    machine.IntervalStep b input J δ cIn wIn (List.ofFn u) cOut wOut).card

omit [NeZero b] in
/-- An interval tensor entry is at most the number `2 ^ b` of bit strings. -/
theorem intervalCount_le (input : List Bool) (J : Option (Fin k) → ℤ)
    (δ : Option (Fin k) → SignType) (cIn : BlockControl k State b)
    (wIn : Fin k → Fin 3 → ZMod b → Option Bool)
    (cOut : BlockControl k State b) (wOut : Fin k → Fin 3 → ZMod b → Option Bool) :
    machine.intervalCount b input J δ cIn wIn cOut wOut ≤ 2 ^ b := by
  classical
  unfold intervalCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- **Interval steps from a view are the true replay.** For at most `b` bits, an interval step
from the view of `c` (its block indices, control record and window contents) holds exactly when
replaying the bits from `c` itself leaves the prescribed record and window contents and moves the
blocks by `δ`. -/
theorem intervalStep_view_iff (c : Cfg k Bool State input) {coins : List Bool}
    (hlen : coins.length ≤ b) (δ : Option (Fin k) → SignType) (cOut : BlockControl k State b)
    (wOut : Fin k → Fin 3 → ZMod b → Option Bool) :
    machine.IntervalStep b input (c.blockIndex b) δ (c.blockControl b)
        (c.windowContents b (c.blockIndex b)) coins cOut wOut ↔
      (machine.stepCoins coins c).blockControl b = cOut ∧
        (machine.stepCoins coins c).windowContents b (c.blockIndex b) = wOut ∧
        ∀ head, (machine.stepCoins coins c).blockIndex b head = c.blockIndex b head + δ head := by
  set e := embedCfg (input := input) b (c.blockIndex b) (c.blockControl b)
    (c.windowContents b (c.blockIndex b))
  obtain ⟨hagree, word, hword, hword'⟩ :=
    machine.agreeOn_blockWindow_stepCoins (Nat.pos_of_neZero b) hlen
      (agreeOn_embedCfg_view c).symm (coins := coins)
  replace hagree := hagree.symm
  -- The two replays have the same state, heads, output track and window contents.
  have htrack : OutputTrack.ofWord (machine.stepCoins coins e).output =
      OutputTrack.ofWord (machine.stepCoins coins c).output := by
    rw [hword, hword']
    refine OutputTrack.ofWord_append_eq_of_eq ?_ word
    rw [ofWord_output_embedCfg]
    rfl
  have hcontrol : (machine.stepCoins coins e).blockControl b =
      (machine.stepCoins coins c).blockControl b := by
    rw [Cfg.blockControl, Cfg.blockControl, hagree.state_eq, hagree.headPos_eq, htrack]
  have hwindow : (machine.stepCoins coins e).windowContents b (c.blockIndex b) =
      (machine.stepCoins coins c).windowContents b (c.blockIndex b) := by
    funext h d r
    exact hagree.workTapes_eq h _ (mem_blockWindow_of_window h d r)
  have hindex : (machine.stepCoins coins e).blockIndex b =
      (machine.stepCoins coins c).blockIndex b := by
    funext head
    rw [Cfg.blockIndex, Cfg.blockIndex, hagree.headPos_eq]
  rw [IntervalStep, hcontrol, hwindow, hindex]

end Interval

/-! ### Splitting the accepting count -/

/-- **The accepting count split by schedules.** The accepting choice strings of `q` intervals of
`b` bits are counted schedule by schedule. -/
theorem acceptCount_eq_sum_card_schedule (input : List Bool) (b q : ℕ) :
    machine.acceptCount input (q * b) = ∑ σ : Schedule k q,
      (Finset.univ.filter fun y : Fin (q * b) → Bool =>
        machine.runClosedCoins (List.ofFn y) input = [true] ∧
          machine.schedule b q (List.ofFn y) (Cfg.init machine.initial input) = σ).card := by
  classical
  rw [acceptCount, Cslib.Complexity.acceptCount, Finset.card_eq_sum_card_fiberwise
    (f := fun y : Fin (q * b) → Bool =>
      machine.schedule b q (List.ofFn y) (Cfg.init machine.initial input))
    (t := Finset.univ) fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.filter_filter]
  simp only [decide_eq_true_eq]

/-- **The bits of an interval.** For a choice string `y` of `q` intervals of `b` bits, interval
`i` replays the bits `y (finProdFinEquiv (i, r))`, `r < b`. -/
theorem intervalStart_succ_ofFn {q b : ℕ} (y : Fin (q * b) → Bool) (c : Cfg k Bool State input)
    (i : Fin q) :
    machine.intervalStart b (List.ofFn y) c (i + 1) =
      machine.stepCoins (List.ofFn fun r : Fin b => y (finProdFinEquiv (i, r)))
        (machine.intervalStart b (List.ofFn y) c i) := by
  rw [intervalStart_succ]
  congr 1
  have hi := i.isLt
  have hle : i * b + b ≤ q * b := by nlinarith
  refine List.ext_getElem (by simp; omega) fun r h₁ h₂ => ?_
  simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
  congr 1
  ext
  change i * b + r = r + b * i
  ring

end MultiTapePTM

end Turing
