/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Allocation
public import Complexity.Computability.WordRAM.Function
public import Complexity.Computability.Machines.Turing.MultiTape.Deterministic
public import Complexity.Computability.Machines.Turing.MultiTape.Run
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import Complexity.Foundations.Data.BitString.Counter

/-!
# Word RAMs simulate multi-tape Turing machines

A multi-tape Turing machine with a binary alphabet and finitely many states that halts within `t`
steps is simulated by one fixed word-RAM program over `Basis.additive` in `O(t)` instructions,
at every word size whose words hold addresses linear in `t` and the input length. Together with
`Cslib.WordRAM.Program.ComputesInTime.turingComputableInPolyTime_of_width`, this links polynomial
time on the two models. The construction is the usual one, tape cells as memory words and the
finite control as branches, written for the word RAM of `Cslib.WordRAM`; it is not transcribed
from a source.

## Conventions

* **Input.** The input bit string `x` is given as the word list `x.map Bool.toNat`, so
  `State.init` places its length at address `0` and its bits at addresses `1, …, |x|`. The
  simulator reads the input there; it is not copied. The input head of a configuration is shifted
  by one (`Turing.Cfg.inputPos`), so it is the address of the symbol it reads, and the two blank
  cells `0` and `|x| + 1` are recognized by comparisons.
* **Work tapes.** Cell `z` of work tape `i` is the memory cell `tapeAddr k |x| i z`, past the
  input. The two half-tapes `z ≥ 0` and `z < 0` of all `k` tapes are interleaved, so the address
  of cell `z` is linear in `|z|`. A cell holds `0` for a blank and `b.toNat + 1` for a bit `b`, so
  the zeroed memory beyond the input is the blank tape. Each tape keeps the sign of its head and the
  address of its head cell in registers.
* **Control.** The state is a register, with `m` for the halting state. A step reads the input and
  work symbols and dispatches through a finite decision tree on the state and the symbols read; its
  leaves apply fixed actions. The tree is built from the transition function, so the program
  depends only on the machine.
* **Output.** The program returns the output tape read as a little-endian binary number,
  `Cslib.BitString.lsbValue`. A decision `b`, written as `[b]`, gives `b.toNat`; a binary number
  `v`, written as `Nat.bits v`, gives `v`. The output must be shorter than the word size.
* **Cost.** Unit cost per instruction, the final `halt` included. A step costs at most
  `stepCost k m = 3m + 13k + 14` instructions and the whole run at most
  `simTime k m t = 2k + 13 + t (3m + 13k + 16)`.

## Main definitions

* `Cslib.WordRAM.OfTuring.tapeAddr`: the memory address of a work-tape cell.
* `Cslib.WordRAM.OfTuring.simCode`, `Cslib.WordRAM.OfTuring.simProgram`: the simulator of the
  machine with a given transition function, initial state and numbering of its states.
* `Cslib.WordRAM.OfTuring.Sim`: the data of the simulator represents a configuration.

## Main results

* `Cslib.WordRAM.OfTuring.setupCode_spec`, `Cslib.WordRAM.OfTuring.stepCode_spec`,
  `Cslib.WordRAM.OfTuring.loop_spec`: the setup represents the initial configuration, one step of
  the simulator follows one step of the machine, and the loop follows the run to its halt.
* `Cslib.WordRAM.OfTuring.executes_simProgram`: a halting run of `t` steps is simulated within
  `simTime k m t` instructions, returning the value `Cslib.BitString.lsbValue` of the output tape.
* `Turing.MultiTapeTM.ComputableInPolyTime.exists_wordRAM`,
  `Turing.MultiTapeTM.ComputableInPolyTime.exists_wordRAM_nat`: a function computable in polynomial
  time by a Turing machine is computed by a uniform word-RAM program in polynomially many
  instructions, at every word size above a polynomial threshold.
-/

@[expose] public section

namespace Cslib.WordRAM.OfTuring

open Turing

variable {k m : ℕ} {Q : Type}

/-! ## Encodings -/

/-- The code of a tape symbol in a memory cell: `0` for a blank and `b.toNat + 1` for a bit. -/
def symCode : Option Bool → ℕ
  | none => 0
  | some b => b.toNat + 1

/-- The code of a control state, `m` for the halting state. -/
def stateCode (e : Q ≃ Fin m) : Option Q → ℕ
  | none => m
  | some q => e q

theorem stateCode_lt_iff (e : Q ≃ Fin m) (q : Option Q) :
    stateCode e q < m ↔ q.isSome := by
  cases q <;> simp [stateCode]

/-- The half-tape of a cell: `1` for a negative position and `0` otherwise. -/
def sgnOf (z : ℤ) : ℕ := if z < 0 then 1 else 0

/-- The index of a cell in its half-tape. -/
def magOf (z : ℤ) : ℕ := if z < 0 then (-z - 1).toNat else z.toNat

/-- The memory address of cell `z` of work tape `i` of a machine with `k` work tapes, on an input
of length `n`: the half-tapes of all tapes are interleaved past the input. -/
def tapeAddr (k n : ℕ) (i : Fin k) (z : ℤ) : ℕ := n + 1 + 2 * k * magOf z + 2 * i + sgnOf z

theorem sgnOf_le_one (z : ℤ) : sgnOf z ≤ 1 := by unfold sgnOf; split <;> omega

theorem lt_tapeAddr (k n : ℕ) (i : Fin k) (z : ℤ) : n < tapeAddr k n i z := by
  unfold tapeAddr; omega

private theorem two_mul_add_sgnOf_lt (i : Fin k) (z : ℤ) : 2 * (i : ℕ) + sgnOf z < 2 * k := by
  have := sgnOf_le_one z; omega

/-- Distinct cells have distinct addresses. -/
theorem tapeAddr_injective {k n : ℕ} {i j : Fin k} {z z' : ℤ}
    (h : tapeAddr k n i z = tapeAddr k n j z') : i = j ∧ z = z' := by
  unfold tapeAddr at h
  have hi := two_mul_add_sgnOf_lt i z
  have hj := two_mul_add_sgnOf_lt j z'
  have hm : magOf z = magOf z' := by
    rcases lt_trichotomy (magOf z) (magOf z') with hlt | heq | hgt
    · have : 2 * k * (magOf z + 1) ≤ 2 * k * magOf z' := Nat.mul_le_mul_left _ hlt
      rw [Nat.mul_succ] at this; omega
    · exact heq
    · have : 2 * k * (magOf z' + 1) ≤ 2 * k * magOf z := Nat.mul_le_mul_left _ hgt
      rw [Nat.mul_succ] at this; omega
  rw [hm] at h
  have hs := sgnOf_le_one z
  have hs' := sgnOf_le_one z'
  have hij : (i : ℕ) = j := by omega
  refine ⟨Fin.ext hij, ?_⟩
  have hsz : sgnOf z = sgnOf z' := by omega
  unfold sgnOf at hsz
  unfold magOf at hm
  split_ifs at hsz hm <;> omega

theorem tapeAddr_ne {k n : ℕ} {i j : Fin k} {z z' : ℤ} (h : (i, z) ≠ (j, z')) :
    tapeAddr k n i z ≠ tapeAddr k n j z' := fun he => by
  obtain ⟨rfl, rfl⟩ := tapeAddr_injective he
  exact h rfl

/-- An address of a cell at distance at most `d` from the origin. -/
theorem tapeAddr_lt {k n : ℕ} (i : Fin k) {z : ℤ} {d : ℕ} (hz : z.natAbs ≤ d) :
    tapeAddr k n i z < n + 1 + 2 * k * (d + 1) := by
  have hm : magOf z ≤ d := by unfold magOf; split <;> omega
  have := two_mul_add_sgnOf_lt i z
  have : 2 * k * magOf z ≤ 2 * k * d := Nat.mul_le_mul_left _ hm
  unfold tapeAddr; rw [Nat.mul_succ]; omega

/-! ### Moving a head -/

section Moves

variable {n : ℕ} {i : Fin k} {z : ℤ}

theorem tapeAddr_succ_of_nonneg (hz : 0 ≤ z) :
    tapeAddr k n i (z + 1) = tapeAddr k n i z + 2 * k := by
  have hm : magOf (z + 1) = magOf z + 1 := by unfold magOf; split_ifs <;> omega
  have hs : sgnOf (z + 1) = sgnOf z := by unfold sgnOf; split_ifs <;> omega
  unfold tapeAddr; rw [hm, hs, Nat.mul_succ]; omega

theorem tapeAddr_succ_of_lt_neg_one (hz : z < -1) :
    tapeAddr k n i (z + 1) + 2 * k = tapeAddr k n i z := by
  have hm : magOf z = magOf (z + 1) + 1 := by unfold magOf; split_ifs <;> omega
  have hs : sgnOf (z + 1) = sgnOf z := by unfold sgnOf; split_ifs <;> omega
  unfold tapeAddr; rw [hm, hs, Nat.mul_succ]; omega

theorem tapeAddr_pred_of_pos (hz : 0 < z) :
    tapeAddr k n i (z - 1) + 2 * k = tapeAddr k n i z := by
  have hm : magOf z = magOf (z - 1) + 1 := by unfold magOf; split_ifs <;> omega
  have hs : sgnOf (z - 1) = sgnOf z := by unfold sgnOf; split_ifs <;> omega
  unfold tapeAddr; rw [hm, hs, Nat.mul_succ]; omega

theorem tapeAddr_pred_of_neg (hz : z < 0) :
    tapeAddr k n i (z - 1) = tapeAddr k n i z + 2 * k := by
  have hm : magOf (z - 1) = magOf z + 1 := by unfold magOf; split_ifs <;> omega
  have hs : sgnOf (z - 1) = sgnOf z := by unfold sgnOf; split_ifs <;> omega
  unfold tapeAddr; rw [hm, hs, Nat.mul_succ]; omega

theorem tapeAddr_neg_one : tapeAddr k n i (-1) = tapeAddr k n i 0 + 1 := by
  simp [tapeAddr, magOf, sgnOf]

/-- A head address is below `n + 1 + 2k` exactly at the cells `0` and `-1`. -/
theorem tapeAddr_lt_iff : tapeAddr k n i z < n + 1 + 2 * k ↔ magOf z = 0 := by
  have := two_mul_add_sgnOf_lt i z
  unfold tapeAddr
  constructor
  · intro h
    by_contra hm
    have : 2 * k * 1 ≤ 2 * k * magOf z := Nat.mul_le_mul_left _ (by omega)
    omega
  · intro h; rw [h]; omega

theorem magOf_eq_zero_iff : magOf z = 0 ↔ z = 0 ∨ z = -1 := by
  unfold magOf; split_ifs <;> constructor <;> intro h <;> omega

theorem sgnOf_eq_zero_iff : sgnOf z = 0 ↔ 0 ≤ z := by
  unfold sgnOf; by_cases hz : z < 0 <;> simp [hz]; omega

end Moves

/-! ## Registers and instructions -/

/-- The number of registers of the simulator of a machine with `k` work tapes. -/
abbrev regs (k : ℕ) : ℕ := 12 + 2 * k

/-- The register holding `0`. -/
abbrev rZero : Fin (regs k) := ⟨0, by unfold regs; omega⟩
/-- The register holding `1`. -/
abbrev rOne : Fin (regs k) := ⟨1, by unfold regs; omega⟩
/-- The register holding `n + 1`, the address of the right blank of an input of length `n`. -/
abbrev rEnd : Fin (regs k) := ⟨2, by unfold regs; omega⟩
/-- The register holding the code of the control state. -/
abbrev rState : Fin (regs k) := ⟨3, by unfold regs; omega⟩
/-- The register holding the number `m` of states. -/
abbrev rStates : Fin (regs k) := ⟨4, by unfold regs; omega⟩
/-- The register holding the input head. -/
abbrev rHead : Fin (regs k) := ⟨5, by unfold regs; omega⟩
/-- A scratch register for constants. -/
abbrev rTmp : Fin (regs k) := ⟨6, by unfold regs; omega⟩
/-- A scratch register for the symbol read. -/
abbrev rCur : Fin (regs k) := ⟨7, by unfold regs; omega⟩
/-- The register holding the output tape read as a binary number. -/
abbrev rVal : Fin (regs k) := ⟨8, by unfold regs; omega⟩
/-- The register holding `2 ^ ℓ` for the length `ℓ` of the output tape. -/
abbrev rPow : Fin (regs k) := ⟨9, by unfold regs; omega⟩
/-- The register holding `2k`. -/
abbrev rStride : Fin (regs k) := ⟨10, by unfold regs; omega⟩
/-- The register holding `n + 1 + 2k`: head addresses below it are the cells `0` and `-1`. -/
abbrev rLim : Fin (regs k) := ⟨11, by unfold regs; omega⟩
/-- The register holding the half-tape of the head of tape `i`. -/
abbrev rSgn (i : Fin k) : Fin (regs k) := ⟨12 + 2 * i, by unfold regs; omega⟩
/-- The register holding the address of the head cell of tape `i`. -/
abbrev rAdr (i : Fin k) : Fin (regs k) := ⟨13 + 2 * i, by unfold regs; omega⟩

/-- Do nothing, in one instruction. -/
abbrev skip : Code .additive (regs k) := .op (.copy rZero rZero)

/-- `d ← i + j`. -/
abbrev addC (d i j : Fin (regs k)) : Code .additive (regs k) := .op (Op.addAdditive d i j)

/-- `d ← i - j`, truncated. -/
abbrev subC (d i j : Fin (regs k)) : Code .additive (regs k) :=
  .op (.alu ⟨.bin .sub, by decide⟩ d ![i, j])

/-- `d ← #v`. -/
abbrev constC (d : Fin (regs k)) (v : ℕ) : Code .additive (regs k) := .op (.const d v)

section Exec

variable {w : ℕ} {x : Data (regs k)}

private theorem execWithin_skip : ExecWithin w (skip (k := k)) x x 1 := by
  have h := ExecWithin.copy (B := .additive) (w := w) (x := x) (d := rZero) (s := rZero)
  have hx : x.set rZero (x.regs rZero) = x := by ext <;> simp [Data.set]
  rwa [hx] at h

private theorem execWithin_add {d i j : Fin (regs k)} (h : Fits w (x.regs i + x.regs j)) :
    ExecWithin w (addC d i j) x (x.set d (x.regs i + x.regs j)) 1 :=
  ExecWithin.alu rfl h

private theorem execWithin_sub {d i j : Fin (regs k)} (h : Fits w (x.regs i - x.regs j)) :
    ExecWithin w (subC d i j) x (x.set d (x.regs i - x.regs j)) 1 :=
  ExecWithin.alu rfl h

private theorem execWithin_const {d : Fin (regs k)} {v : ℕ} (h : Fits w v) :
    ExecWithin w (constC d v) x (x.set d v) 1 :=
  ExecWithin.const h

end Exec

/-! ## The simulator -/

/-- Dispatch on the contents of register `reg`: run `body j` when it holds `j < N`, comparing it
with the constants `N - 1, …, 0` loaded into `rTmp`. -/
def dispatch (reg : Fin (regs k)) (body : ℕ → Code .additive (regs k)) :
    ℕ → Code .additive (regs k)
  | 0 => skip
  | j + 1 => .seq (constC rTmp j) (.branch (.eq reg rTmp) (body j) (dispatch reg body j))

/-- Read the input symbol and continue with `next` of it. -/
def inputTree (next : Option Bool → Code .additive (regs k)) : Code .additive (regs k) :=
  .branch (.eq rHead rZero) (next none) <|
  .branch (.eq rHead rEnd) (next none) <|
  .seq (.op (.load rCur rHead)) <|
  .branch (.eq rCur rZero) (next (some false)) (next (some true))

/-- Read the symbols under the heads of the work tapes `rem - 1, …, 0`, record them in `acc`, and
continue with `next` of the recorded symbols. -/
def tapesTree (next : (Fin k → Option Bool) → Code .additive (regs k)) :
    ℕ → (Fin k → Option Bool) → Code .additive (regs k)
  | 0, acc => next acc
  | rem + 1, acc =>
    if h : rem < k then
      .seq (.op (.load rCur (rAdr ⟨rem, h⟩))) <|
      .branch (.eq rCur rZero) (tapesTree next rem (Function.update acc ⟨rem, h⟩ none)) <|
      .branch (.eq rCur rOne) (tapesTree next rem (Function.update acc ⟨rem, h⟩ (some false)))
        (tapesTree next rem (Function.update acc ⟨rem, h⟩ (some true)))
    else skip

/-- Move the head of tape `i` one cell to the right. -/
def moveRight (i : Fin k) : Code .additive (regs k) :=
  .branch (.eq (rSgn i) rZero) (addC (rAdr i) (rAdr i) rStride) <|
  .branch (.lt (rAdr i) rLim) (.seq (constC (rSgn i) 0) (subC (rAdr i) (rAdr i) rOne))
    (subC (rAdr i) (rAdr i) rStride)

/-- Move the head of tape `i` one cell to the left. -/
def moveLeft (i : Fin k) : Code .additive (regs k) :=
  .branch (.eq (rSgn i) rZero)
    (.branch (.lt (rAdr i) rLim) (.seq (constC (rSgn i) 1) (addC (rAdr i) (rAdr i) rOne))
      (subC (rAdr i) (rAdr i) rStride))
    (addC (rAdr i) (rAdr i) rStride)

/-- Move the head of tape `i`. -/
def moveCode (i : Fin k) : SignType → Code .additive (regs k)
  | .zero => skip
  | .neg => moveLeft i
  | .pos => moveRight i

/-- Write on tape `i`, if the action writes. -/
def writeCode (i : Fin k) : Option (Option Bool) → Code .additive (regs k)
  | none => skip
  | some s => .seq (constC rTmp (symCode s)) (.op (.store (rAdr i) rTmp))

/-- The action on tape `i`: write, then move. -/
def tapeCode (i : Fin k) (a : Option (Option Bool) × SignType) : Code .additive (regs k) :=
  .seq (writeCode i a.1) (moveCode i a.2)

/-- The actions on the work tapes in `l`. -/
def tapesCode (act : Action k Bool Q) : List (Fin k) → Code .additive (regs k)
  | [] => skip
  | i :: l => .seq (tapeCode i (act.workTapes i)) (tapesCode act l)

/-- Move the input head, which stays on the blanks `0` and `n + 1` at the ends. -/
def headCode : SignType → Code .additive (regs k)
  | .zero => skip
  | .neg => subC rHead rHead rOne
  | .pos => .branch (.eq rHead rEnd) skip (addC rHead rHead rOne)

/-- Append a symbol to the output tape. -/
def outCode : Option Bool → Code .additive (regs k)
  | none => skip
  | some false => addC rPow rPow rPow
  | some true => .seq (addC rVal rVal rPow) (addC rPow rPow rPow)

/-- Apply an action. -/
def actionCode (e : Q ≃ Fin m) (act : Action k Bool Q) : Code .additive (regs k) :=
  .seq (tapesCode act (List.finRange k)) <|
  .seq (headCode act.inputTape) <|
  .seq (outCode act.output) (constC rState (stateCode e act.state))

/-- One step of the machine with transition function `δ`: dispatch on the state and the symbols
read, and apply the selected action. -/
def stepCode (δ : Q → Option Bool → (Fin k → Option Bool) → Action k Bool Q)
    (e : Q ≃ Fin m) : Code .additive (regs k) :=
  dispatch rState (fun j => if h : j < m then
      inputTree fun a => tapesTree (fun s => actionCode e (δ (e.symm ⟨j, h⟩) a s)) k fun _ => none
    else skip) m

/-- Place the heads of the work tapes in `l` on their cells `0`. -/
def setupTapes : List (Fin k) → Code .additive (regs k)
  | [] => skip
  | i :: l => .seq (constC rTmp (2 * i)) (.seq (addC (rAdr i) rEnd rTmp) (setupTapes l))

/-- Initialize the constants and the initial configuration with state `q₀`. -/
def setupCode (q₀ : Q) (e : Q ≃ Fin m) : Code .additive (regs k) :=
  .seq (.op (.load rEnd rZero)) <|
  .seq (constC rOne 1) <|
  .seq (addC rEnd rEnd rOne) <|
  .seq (constC rHead 1) <|
  .seq (constC rStride (2 * k)) <|
  .seq (addC rLim rEnd rStride) <|
  .seq (constC rStates m) <|
  .seq (constC rState (e q₀)) <|
  .seq (constC rPow 1) (setupTapes (List.finRange k))

/-- The simulator of the machine with transition function `δ` and initial state `q₀`, whose states
are numbered by `e`: set up, then step while the state is not halting. -/
def simCode (δ : Q → Option Bool → (Fin k → Option Bool) → Action k Bool Q) (q₀ : Q)
    (e : Q ≃ Fin m) : Code .additive (regs k) :=
  .seq (setupCode q₀ e) (.loop (.lt rState rStates) (stepCode δ e))

/-- The simulator as a flat program, returning the output tape read as a binary number. -/
def simProgram (δ : Q → Option Bool → (Fin k → Option Bool) → Action k Bool Q)
    (q₀ : Q) (e : Q ≃ Fin m) : Program .additive (regs k) :=
  (simCode δ q₀ e).program rVal

/-- An upper bound on the instructions of one simulated step. -/
def stepCost (k m : ℕ) : ℕ := 3 * m + 13 * k + 14

/-- An upper bound on the instructions of a simulated run of `t` steps, the final `halt`
included. -/
def simTime (k m t : ℕ) : ℕ := 2 * k + 13 + t * (stepCost k m + 2)

/-- Words of the simulator of a run of `t` steps on an input of length `n` stay below this bound,
except for the output. -/
def simBound (k m n t : ℕ) : ℕ := n + 1 + 2 * k * (t + 1) + m + 2

/-! ## The invariant -/

/-- The contents of a tape after an optional write at position `p`. -/
def newTape (t : ℤ → Option Bool) (p : ℤ) : Option (Option Bool) → ℤ → Option Bool
  | none => t
  | some s => Function.update t p s

/-- The registers and memory of the work tapes represent tape contents `T` and head positions `P`,
on an input of length `n`. -/
structure TapesRel (n : ℕ) (x : Data (regs k)) (T : Fin k → ℤ → Option Bool) (P : Fin k → ℤ) :
    Prop where
  /-- The half-tape registers hold the half-tapes of the heads. -/
  sgn : ∀ i, x.regs (rSgn i) = sgnOf (P i)
  /-- The address registers hold the addresses of the head cells. -/
  adr : ∀ i, x.regs (rAdr i) = tapeAddr k n i (P i)
  /-- Every cell of every tape holds the code of its symbol. -/
  tape : ∀ i z, x.mem (tapeAddr k n i z) = symCode (T i z)

/-- The constant registers hold their values, on an input of length `n`. -/
structure Consts (n m : ℕ) (x : Data (regs k)) : Prop where
  /-- `rZero` holds `0`. -/
  zero : x.regs rZero = 0
  /-- `rOne` holds `1`. -/
  one : x.regs rOne = 1
  /-- `rEnd` holds `n + 1`. -/
  fin : x.regs rEnd = n + 1
  /-- `rStates` holds `m`. -/
  states : x.regs rStates = m
  /-- `rStride` holds `2k`. -/
  stride : x.regs rStride = 2 * k
  /-- `rLim` holds `n + 1 + 2k`. -/
  lim : x.regs rLim = n + 1 + 2 * k

/-- The data `x` of the simulator represents the configuration `c`. -/
structure Sim (e : Q ≃ Fin m) {inp : List Bool} (x : Data (regs k))
    (c : Cfg k Bool Q inp) : Prop where
  /-- The constant registers hold their values. -/
  consts : Consts inp.length m x
  /-- `rState` holds the code of the state. -/
  state : x.regs rState = stateCode e c.state
  /-- `rHead` holds the input head, which is the address of the input symbol it reads. -/
  head : x.regs rHead = c.inputPos
  /-- `rVal` holds the output tape read as a binary number. -/
  val : x.regs rVal = BitString.lsbValue c.output
  /-- `rPow` holds `2 ^ ℓ` for the length `ℓ` of the output tape. -/
  pow : x.regs rPow = 2 ^ c.output.length
  /-- The work tapes are represented. -/
  tapes : TapesRel inp.length x c.workTapes c.workTapePos
  /-- The input bits stay at addresses `1, …, n`. -/
  input : ∀ j (h : j < inp.length), x.mem (j + 1) = inp[j].toNat

/-! ## Correctness of the pieces -/

/-- Discharge a disequality of registers. -/
local macro "reg_ne" : tactic => `(tactic| (simp only [ne_eq, Fin.ext_iff] at *; omega))

/-- Simplify reads of updated registers and memory. -/
local macro "reg_simp" : tactic => `(tactic|
  simp (disch := reg_ne) only [Data.set_regs, Data.set_mem, Data.write_regs, Data.write_mem,
    Function.update_self, Function.update_of_ne])

section Pieces

variable {n w : ℕ} {e : Q ≃ Fin m}

private theorem Consts.of_eq {x y : Data (regs k)} (h : Consts n m x)
    (hy : ∀ d : Fin (regs k), d.val < 12 → d ≠ rState → d ≠ rHead → d ≠ rTmp → d ≠ rCur →
      d ≠ rVal → d ≠ rPow → y.regs d = x.regs d) : Consts n m y where
  zero := (hy rZero (by simp) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne)
    (by reg_ne)).trans h.zero
  one := (hy rOne (by simp) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne)
    (by reg_ne)).trans h.one
  fin := (hy rEnd (by simp) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne)
    (by reg_ne)).trans h.fin
  states := (hy rStates (by simp) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne)
    (by reg_ne)).trans h.states
  stride := (hy rStride (by simp) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne)
    (by reg_ne)).trans h.stride
  lim := (hy rLim (by simp) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne)
    (by reg_ne)).trans h.lim

private theorem TapesRel.set {x : Data (regs k)} {T : Fin k → ℤ → Option Bool} {P : Fin k → ℤ}
    (h : TapesRel n x T P) {d : Fin (regs k)} (hd : d.val < 12) (v : ℕ) :
    TapesRel n (x.set d v) T P where
  sgn i := by rw [Data.set_regs, Function.update_of_ne (by reg_ne)]; exact h.sgn i
  adr i := by rw [Data.set_regs, Function.update_of_ne (by reg_ne)]; exact h.adr i
  tape := h.tape

/-- Setting a scratch register preserves the invariant. -/
private theorem Sim.set_scratch {inp : List Bool} {x : Data (regs k)} {c : Cfg k Bool Q inp}
    (h : Sim e x c) {d : Fin (regs k)} (hd : d = rTmp ∨ d = rCur) (v : ℕ) :
    Sim e (x.set d v) c := by
  rcases hd with rfl | rfl <;>
  exact { consts := h.consts.of_eq fun d _ _ _ h₁ h₂ _ _ => by reg_simp
          state := by reg_simp; exact h.state
          head := by reg_simp; exact h.head
          val := by reg_simp; exact h.val
          pow := by reg_simp; exact h.pow
          tapes := h.tapes.set (by simp) v
          input := h.input }

/-- Dispatch selects the body of the value held in the register. -/
private theorem dispatch_spec {reg : Fin (regs k)} (hreg : reg ≠ rTmp)
    {body : ℕ → Code .additive (regs k)}
    {v T : ℕ} {y : Data (regs k)} :
    ∀ {N : ℕ} {x : Data (regs k)}, x.regs reg = v → v < N → N ≤ 2 ^ w →
      ExecWithin w (body v) (x.set rTmp v) y T →
      ExecWithin w (dispatch reg body N) x y (T + 3 * N)
  | 0, _, _, hvN, _, _ => absurd hvN (Nat.not_lt_zero v)
  | N + 1, x, hv, hvN, hN, hbody => by
    have hfit : Fits w N := by unfold Fits; omega
    by_cases h : v = N
    · subst h
      refine ((execWithin_const hfit).seq (ExecWithin.branch_pos ?_ hbody)).mono (by omega)
      simp only [Cond.holds_eq]; reg_simp; exact hv
    · have hset : (x.set rTmp N).set rTmp v = x.set rTmp v := by
        ext <;> simp [Data.set, Function.update_idem]
      have hrest := dispatch_spec hreg (N := N) (x := x.set rTmp N)
        (by reg_simp; exact hv) (by omega) (by omega) (by rwa [hset])
      refine ((execWithin_const hfit).seq (ExecWithin.branch_neg ?_ hrest)).mono (by omega)
      simp only [Cond.holds_eq]; reg_simp; exact fun he => h (hv ▸ he)

private theorem symCode_le (s : Option Bool) : symCode s ≤ 2 := by
  rcases s with _ | _ | _ <;> simp [symCode]

private theorem newTape_none (t : ℤ → Option Bool) (p : ℤ) : newTape t p none = t := rfl

/-- Writing on tape `i`. -/
private theorem writeCode_spec {x : Data (regs k)} {T : Fin k → ℤ → Option Bool} {P : Fin k → ℤ}
    (hT : TapesRel n x T P) (i : Fin k) (wr : Option (Option Bool)) (h2 : Fits w 2) :
    ∃ y, ExecWithin w (writeCode i wr) x y 2 ∧
      TapesRel n y (Function.update T i (newTape (T i) (P i) wr)) P ∧
      (∀ d, d ≠ rTmp → y.regs d = x.regs d) ∧ ∀ a, a ≤ n → y.mem a = x.mem a := by
  cases wr with
  | none =>
    refine ⟨x, execWithin_skip.mono (by omega), ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    rwa [newTape_none, Function.update_eq_self]
  | some s =>
    refine ⟨(x.set rTmp (symCode s)).write (tapeAddr k n i (P i)) (symCode s), ?_, ?_, ?_, ?_⟩
    · have h := (execWithin_const (d := rTmp) (x := x)
        (h2.of_le (symCode_le s))).seq (ExecWithin.store (x := x.set rTmp (symCode s))
          (a := rAdr i) (s := rTmp))
      have ha : (x.set rTmp (symCode s)).regs (rAdr i) = tapeAddr k n i (P i) := by
        reg_simp; exact hT.adr i
      have hv : (x.set rTmp (symCode s)).regs rTmp = symCode s := by reg_simp
      rw [ha, hv] at h
      exact h
    · refine ⟨fun j => ?_, fun j => ?_, fun j z => ?_⟩
      · reg_simp; exact hT.sgn j
      · reg_simp; exact hT.adr j
      · simp only [Data.write_mem, Data.set_mem, Function.update_apply]
        by_cases hjz : (j, z) = (i, P i)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hjz
          simp [newTape]
        · simp only [tapeAddr_ne hjz, ↓reduceIte]
          rw [hT.tape j z]
          by_cases hji : j = i
          · subst hji
            have hz : z ≠ P j := fun hz => hjz (by rw [hz])
            simp [newTape, hz]
          · simp [hji]
    · intro d hd; reg_simp
    · intro a ha
      simp only [Data.write_mem, Data.set_mem]
      rw [Function.update_of_ne (by have := lt_tapeAddr k n i (P i); omega)]

/-- Changing only the registers of tape `i` moves its head. -/
private theorem TapesRel.update {x y : Data (regs k)} {T : Fin k → ℤ → Option Bool} {P : Fin k → ℤ}
    (h : TapesRel n x T P) (i : Fin k) (p : ℤ)
    (hs : y.regs (rSgn i) = sgnOf p) (ha : y.regs (rAdr i) = tapeAddr k n i p)
    (hy : ∀ d, d ≠ rSgn i → d ≠ rAdr i → y.regs d = x.regs d) (hm : y.mem = x.mem) :
    TapesRel n y T (Function.update P i p) where
  sgn j := by
    by_cases hj : j = i
    · subst hj; simpa using hs
    · rw [Function.update_of_ne hj, hy _ (by reg_ne) (by reg_ne)]; exact h.sgn j
  adr j := by
    by_cases hj : j = i
    · subst hj; simpa using ha
    · rw [Function.update_of_ne hj, hy _ (by reg_ne) (by reg_ne)]; exact h.adr j
  tape := hm ▸ h.tape

/-- Moving the head of tape `i`. -/
private theorem moveCode_spec {x : Data (regs k)} {T : Fin k → ℤ → Option Bool} {P : Fin k → ℤ}
    (hT : TapesRel n x T P) (hc : Consts n m x) (i : Fin k) (d : SignType)
    (hfit : Fits w (tapeAddr k n i (P i + d))) (h1 : Fits w 1) :
    ∃ y, ExecWithin w (moveCode i d) x y 6 ∧ TapesRel n y T (Function.update P i (P i + d)) ∧
      (∀ d', d' ≠ rSgn i → d' ≠ rAdr i → y.regs d' = x.regs d') ∧ y.mem = x.mem := by
  have hsi := hT.sgn i
  have hai := hT.adr i
  have hz := hc.zero
  have ho := hc.one
  have hst := hc.stride
  have hl := hc.lim
  cases d with
  | zero =>
    refine ⟨x, execWithin_skip.mono (by omega), ?_, fun _ _ _ => rfl, rfl⟩
    simpa using hT
  | pos =>
    simp only [SignType.pos_eq_one, SignType.coe_one] at hfit ⊢
    by_cases hs : 0 ≤ P i
    · have hv : x.regs (rAdr i) + x.regs rStride = tapeAddr k n i (P i + 1) := by
        rw [hai, hst, tapeAddr_succ_of_nonneg hs]
      refine ⟨_, (ExecWithin.branch_pos ?_ (execWithin_add (hv ▸ hfit))).mono (by omega),
        hT.update i _ ?_ ?_ ?_ rfl, ?_, rfl⟩
      · simp only [Cond.holds_eq, hsi, hz, sgnOf_eq_zero_iff]; exact hs
      · reg_simp; rw [hsi]; unfold sgnOf; split_ifs <;> omega
      · reg_simp; exact hv
      all_goals intro d hd₁ hd₂; reg_simp
    · have hneg : ¬(Cond.eq (rSgn i) rZero).Holds x := by
        simp only [Cond.holds_eq, hsi, hz, sgnOf_eq_zero_iff]; exact hs
      by_cases hm : P i = -1
      · have hlt : (Cond.lt (rAdr i) rLim).Holds x := by
          simp only [Cond.holds_lt, hai, hl, tapeAddr_lt_iff, magOf_eq_zero_iff]; omega
        have hv : (x.set (rSgn i) 0).regs (rAdr i) - (x.set (rSgn i) 0).regs rOne =
            tapeAddr k n i (P i + 1) := by
          reg_simp; rw [hai, ho, hm, tapeAddr_neg_one]; simp
        refine ⟨_, (ExecWithin.branch_neg hneg (ExecWithin.branch_pos hlt
          ((execWithin_const (fits_zero w)).seq (execWithin_sub (hv ▸ hfit))))).mono (by omega),
          hT.update i _ ?_ ?_ ?_ rfl, ?_, rfl⟩
        · reg_simp; rw [hm]; simp [sgnOf]
        · rw [← hv]; reg_simp
        all_goals intro d hd₁ hd₂; reg_simp
      · have hge : ¬(Cond.lt (rAdr i) rLim).Holds x := by
          simp only [Cond.holds_lt, hai, hl, tapeAddr_lt_iff, magOf_eq_zero_iff]; omega
        have hv : x.regs (rAdr i) - x.regs rStride = tapeAddr k n i (P i + 1) := by
          rw [hai, hst, ← tapeAddr_succ_of_lt_neg_one (by omega : P i < -1)]; simp
        refine ⟨_, (ExecWithin.branch_neg hneg (ExecWithin.branch_neg hge
          (execWithin_sub (hv ▸ hfit)))).mono (by omega),
          hT.update i _ ?_ ?_ ?_ rfl, ?_, rfl⟩
        · reg_simp; rw [hsi]; unfold sgnOf; split_ifs <;> omega
        · reg_simp; exact hv
        all_goals intro d hd₁ hd₂; reg_simp
  | neg =>
    simp only [SignType.neg_eq_neg_one, SignType.coe_neg_one, ← sub_eq_add_neg] at hfit ⊢
    by_cases hs : 0 ≤ P i
    · have hpos : (Cond.eq (rSgn i) rZero).Holds x := by
        simp only [Cond.holds_eq, hsi, hz, sgnOf_eq_zero_iff]; exact hs
      by_cases hm : P i = 0
      · have hlt : (Cond.lt (rAdr i) rLim).Holds x := by
          simp only [Cond.holds_lt, hai, hl, tapeAddr_lt_iff, magOf_eq_zero_iff]; omega
        have hv : (x.set (rSgn i) 1).regs (rAdr i) + (x.set (rSgn i) 1).regs rOne =
            tapeAddr k n i (P i - 1) := by
          reg_simp; rw [hai, ho, hm, zero_sub, tapeAddr_neg_one]
        refine ⟨_, (ExecWithin.branch_pos hpos (ExecWithin.branch_pos hlt
          ((execWithin_const h1).seq (execWithin_add (hv ▸ hfit))))).mono (by omega),
          hT.update i _ ?_ ?_ ?_ rfl, ?_, rfl⟩
        · reg_simp; rw [hm]; simp [sgnOf]
        · rw [← hv]; reg_simp
        all_goals intro d hd₁ hd₂; reg_simp
      · have hge : ¬(Cond.lt (rAdr i) rLim).Holds x := by
          simp only [Cond.holds_lt, hai, hl, tapeAddr_lt_iff, magOf_eq_zero_iff]; omega
        have hv : x.regs (rAdr i) - x.regs rStride = tapeAddr k n i (P i - 1) := by
          rw [hai, hst, ← tapeAddr_pred_of_pos (by omega : 0 < P i)]; simp
        refine ⟨_, (ExecWithin.branch_pos hpos (ExecWithin.branch_neg hge
          (execWithin_sub (hv ▸ hfit)))).mono (by omega),
          hT.update i _ ?_ ?_ ?_ rfl, ?_, rfl⟩
        · reg_simp; rw [hsi]; unfold sgnOf; split_ifs <;> omega
        · reg_simp; exact hv
        all_goals intro d hd₁ hd₂; reg_simp
    · have hneg : ¬(Cond.eq (rSgn i) rZero).Holds x := by
        simp only [Cond.holds_eq, hsi, hz, sgnOf_eq_zero_iff]; exact hs
      have hv : x.regs (rAdr i) + x.regs rStride = tapeAddr k n i (P i - 1) := by
        rw [hai, hst, tapeAddr_pred_of_neg (by omega : P i < 0)]
      refine ⟨_, (ExecWithin.branch_neg hneg (execWithin_add (hv ▸ hfit))).mono (by omega),
        hT.update i _ ?_ ?_ ?_ rfl, ?_, rfl⟩
      · reg_simp; rw [hsi]; unfold sgnOf; split_ifs <;> omega
      · reg_simp; exact hv
      all_goals intro d hd₁ hd₂; reg_simp

/-- The action on tape `i`: write, then move. -/
private theorem tapeCode_spec {x : Data (regs k)} {T : Fin k → ℤ → Option Bool} {P : Fin k → ℤ}
    (hT : TapesRel n x T P) (hc : Consts n m x) (i : Fin k) (a : Option (Option Bool) × SignType)
    (hfit : Fits w (tapeAddr k n i (P i + a.2))) (h2 : Fits w 2) :
    ∃ y, ExecWithin w (tapeCode i a) x y 8 ∧
      TapesRel n y (Function.update T i (newTape (T i) (P i) a.1))
        (Function.update P i (P i + a.2)) ∧
      (∀ d, d ≠ rSgn i → d ≠ rAdr i → d ≠ rTmp → y.regs d = x.regs d) ∧
      ∀ b, b ≤ n → y.mem b = x.mem b := by
  obtain ⟨y₁, h₁, hT₁, hr₁, hm₁⟩ := writeCode_spec hT i a.1 h2
  have hc₁ : Consts n m y₁ := hc.of_eq fun d _ _ _ h _ _ _ => hr₁ d h
  obtain ⟨y, h₂, hT₂, hr₂, hm₂⟩ := moveCode_spec hT₁ hc₁ i a.2 hfit (h2.of_le (by norm_num))
  exact ⟨y, h₁.seq h₂, hT₂, fun d hs ha ht => (hr₂ d hs ha).trans (hr₁ d ht),
    fun b hb => by rw [hm₂, hm₁ b hb]⟩

/-- The actions on the work tapes in a list without repetitions. -/
private theorem tapesCode_spec (act : Action k Bool Q) :
    ∀ (L : List (Fin k)), L.Nodup → ∀ {x : Data (regs k)} {T : Fin k → ℤ → Option Bool}
      {P : Fin k → ℤ}, TapesRel n x T P → Consts n m x → Fits w 2 →
      (∀ i ∈ L, Fits w (tapeAddr k n i (P i + (act.workTapes i).2))) →
      ∃ y, ExecWithin w (tapesCode act L) x y (8 * L.length + 1) ∧
        TapesRel n y (fun i => if i ∈ L then newTape (T i) (P i) (act.workTapes i).1 else T i)
          (fun i => if i ∈ L then P i + (act.workTapes i).2 else P i) ∧
        (∀ d : Fin (regs k), d.val < 12 → d ≠ rTmp → y.regs d = x.regs d) ∧
        ∀ b, b ≤ n → y.mem b = x.mem b
  | [], _, x, T, P, hT, _, _, _ =>
    ⟨x, execWithin_skip, by simpa using hT, fun _ _ _ => rfl, fun _ _ => rfl⟩
  | i :: L, hL, x, T, P, hT, hc, h2, hfit => by
    obtain ⟨hiL, hL⟩ := List.nodup_cons.1 hL
    obtain ⟨y₁, h₁, hT₁, hr₁, hm₁⟩ :=
      tapeCode_spec hT hc i (act.workTapes i) (hfit i List.mem_cons_self) h2
    have hc₁ : Consts n m y₁ := hc.of_eq fun d hd _ _ ht _ _ _ => hr₁ d (by reg_ne) (by reg_ne) ht
    obtain ⟨y, h₂, hT₂, hr₂, hm₂⟩ := tapesCode_spec act L hL hT₁ hc₁ h2 (fun j hj => by
      have hji : j ≠ i := fun h => hiL (h ▸ hj)
      simpa [Function.update_of_ne hji] using hfit j (List.mem_cons_of_mem i hj))
    have eT : (fun j => if j ∈ L then
          newTape (Function.update T i (newTape (T i) (P i) (act.workTapes i).1) j)
            (Function.update P i (P i + (act.workTapes i).2) j) (act.workTapes j).1
        else Function.update T i (newTape (T i) (P i) (act.workTapes i).1) j) =
        fun j => if j ∈ i :: L then newTape (T j) (P j) (act.workTapes j).1 else T j := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [hiL]
      · simp [hji]
    have eP : (fun j => if j ∈ L then Function.update P i (P i + (act.workTapes i).2) j +
          (act.workTapes j).2 else Function.update P i (P i + (act.workTapes i).2) j) =
        fun j => if j ∈ i :: L then P j + (act.workTapes j).2 else P j := by
      funext j
      by_cases hji : j = i
      · subst hji; simp [hiL]
      · simp [hji]
    refine ⟨y, (h₁.seq h₂).mono (by simp only [List.length_cons]; omega), ?_, ?_, ?_⟩
    · rw [← eT, ← eP]; exact hT₂
    · intro d hd ht; rw [hr₂ d hd ht, hr₁ d (by reg_ne) (by reg_ne) ht]
    · intro b hb; rw [hm₂ b hb, hm₁ b hb]

private theorem TapesRel.of_eq {x y : Data (regs k)} {T : Fin k → ℤ → Option Bool} {P : Fin k → ℤ}
    (h : TapesRel n x T P) (hr : ∀ d : Fin (regs k), 12 ≤ d.val → y.regs d = x.regs d)
    (hm : y.mem = x.mem) : TapesRel n y T P where
  sgn i := (hr _ (by simp)).trans (h.sgn i)
  adr i := (hr _ (by simp; omega)).trans (h.adr i)
  tape := hm ▸ h.tape

/-- Moving the input head. -/
private theorem headCode_spec {x : Data (regs k)} (hc : Consts n m x) {p : Fin (n + 2)}
    (hp : x.regs rHead = p) (d : SignType) (hfit : Fits w (n + 1)) :
    ∃ y, ExecWithin w (headCode d) x y 3 ∧ y.regs rHead = moveInputPos p d ∧
      (∀ r, r ≠ rHead → y.regs r = x.regs r) ∧ y.mem = x.mem := by
  have hmv := val_moveInputPos_eq p d
  have hpl := p.isLt
  cases d with
  | zero =>
    exact ⟨x, execWithin_skip.mono (by omega), by simpa using hp, fun _ _ => rfl, rfl⟩
  | neg =>
    have hv : x.regs rHead - x.regs rOne = moveInputPos p .neg := by
      simp only [SignType.cast] at hmv; rw [hp, hc.one]; omega
    refine ⟨_, (execWithin_sub (hv ▸ hfit.of_le (by omega))).mono (by omega), ?_, ?_, rfl⟩
    · reg_simp; exact hv
    · intro r hr; reg_simp
  | pos =>
    simp only [SignType.cast] at hmv
    by_cases he : (p : ℕ) = n + 1
    · refine ⟨x, (ExecWithin.branch_pos ?_ execWithin_skip).mono (by omega), ?_, fun _ _ => rfl,
        rfl⟩
      · simp only [Cond.holds_eq, hp, hc.fin, he]
      · rw [hp]; omega
    · have hv : x.regs rHead + x.regs rOne = moveInputPos p .pos := by
        rw [hp, hc.one]; omega
      refine ⟨_, ExecWithin.branch_neg ?_ (execWithin_add (hv ▸ hfit.of_le (by omega))), ?_, ?_,
        rfl⟩
      · simp only [Cond.holds_eq, hp, hc.fin]; exact he
      · reg_simp; exact hv
      · intro r hr; reg_simp

/-- Appending a symbol to the output tape. -/
private theorem outCode_spec {x : Data (regs k)} {l : List Bool}
    (hv : x.regs rVal = BitString.lsbValue l)
    (hp : x.regs rPow = 2 ^ l.length) (o : Option Bool) (hfit : (l ++ o.toList).length < w) :
    ∃ y, ExecWithin w (outCode o) x y 2 ∧ y.regs rVal = BitString.lsbValue (l ++ o.toList) ∧
      y.regs rPow = 2 ^ (l ++ o.toList).length ∧
      (∀ r, r ≠ rVal → r ≠ rPow → y.regs r = x.regs r) ∧ y.mem = x.mem := by
  have hlt := BitString.lsbValue_lt l
  rcases o with _ | b
  · exact ⟨x, execWithin_skip.mono (by omega), by simpa using hv, by simpa using hp,
      fun _ _ _ => rfl, rfl⟩
  · simp only [Option.toList_some, List.length_append, List.length_singleton] at hfit ⊢
    have hpow : 2 ^ (l.length + 1) < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) hfit
    have hpp : x.regs rPow + x.regs rPow = 2 ^ (l.length + 1) := by rw [hp, pow_succ]; omega
    cases b with
    | false =>
      refine ⟨_, (execWithin_add (hpp ▸ hpow : Fits w _)).mono (by omega), ?_, ?_, ?_, rfl⟩
      · reg_simp; rw [hv, BitString.lsbValue_append]; simp
      · reg_simp; exact hpp
      · intro r h₁ h₂; reg_simp
    | true =>
      have hvp : x.regs rVal + x.regs rPow = BitString.lsbValue (l ++ [true]) := by
        rw [hv, hp, BitString.lsbValue_append]; simp
      have hvf : Fits w (x.regs rVal + x.regs rPow) := by
        unfold Fits; rw [hv, hp]; rw [pow_succ] at hpow; omega
      refine ⟨_, (execWithin_add hvf).seq (execWithin_add ?_), ?_, ?_, ?_, rfl⟩
      · unfold Fits; reg_simp; rw [hpp]; exact hpow
      · reg_simp; exact hvp
      · reg_simp; exact hpp
      · intro r h₁ h₂; reg_simp

private theorem stateCode_le (e : Q ≃ Fin m) (q : Option Q) : stateCode e q ≤ m := by
  cases q <;> simp [stateCode, Nat.le_of_lt]

private theorem apply_workTapes_eq (act : Action k Bool Q) {inp : List Bool}
    (c : Cfg k Bool Q inp) :
    (act.apply c).workTapes =
      fun i => newTape (c.workTapes i) (c.workTapePos i) (act.workTapes i).1 := by
  funext i
  simp only [Action.apply]
  cases (act.workTapes i).1 <;> rfl

/-- Applying an action. -/
private theorem actionCode_spec (act : Action k Bool Q) {inp : List Bool} {c : Cfg k Bool Q inp}
    {x : Data (regs k)} (hx : Sim e x c)
    (hfit : ∀ i, Fits w (tapeAddr k inp.length i ((act.apply c).workTapePos i)))
    (hbound : inp.length + 2 * k + m + 2 < 2 ^ w) (hout : (act.apply c).output.length < w) :
    ∃ y, ExecWithin w (actionCode e act) x y (8 * k + 7) ∧ Sim e y (act.apply c) := by
  have h2 : Fits w 2 := by unfold Fits; omega
  obtain ⟨y₁, h₁, hT₁, hr₁, hm₁⟩ := tapesCode_spec (n := inp.length) act (List.finRange k)
    (List.nodup_finRange k) hx.tapes hx.consts h2 (fun i _ => hfit i)
  simp only [List.mem_finRange, ite_true] at hT₁
  have hc₁ : Consts inp.length m y₁ := hx.consts.of_eq fun d hd _ _ ht _ _ _ => hr₁ d hd ht
  obtain ⟨y₂, h₂, hh₂, hr₂, hm₂⟩ := headCode_spec (w := w) hc₁ (p := c.inputPos)
    (by rw [hr₁ _ (by simp) (by reg_ne)]; exact hx.head) act.inputTape (by unfold Fits; omega)
  have hc₂ : Consts inp.length m y₂ := hc₁.of_eq fun d _ _ hh _ _ _ _ => hr₂ d hh
  obtain ⟨y₃, h₃, hv₃, hp₃, hr₃, hm₃⟩ := outCode_spec (x := y₂) (l := c.output)
    (by rw [hr₂ _ (by reg_ne), hr₁ _ (by simp) (by reg_ne)]; exact hx.val)
    (by rw [hr₂ _ (by reg_ne), hr₁ _ (by simp) (by reg_ne)]; exact hx.pow) act.output hout
  have hc₃ : Consts inp.length m y₃ := hc₂.of_eq fun d _ _ _ _ _ hv hp => hr₃ d hv hp
  have hst : Fits w (stateCode e act.state) := by
    have := stateCode_le e act.state; unfold Fits; omega
  refine ⟨y₃.set rState (stateCode e act.state),
    (h₁.seq (h₂.seq (h₃.seq (execWithin_const hst)))).mono
      (by simp only [List.length_finRange]; omega),
    { consts := hc₃.of_eq fun d _ hs _ _ _ _ _ => by reg_simp
      state := by reg_simp; rfl
      head := by reg_simp; rw [hr₃ _ (by reg_ne) (by reg_ne)]; exact hh₂
      val := by reg_simp; exact hv₃
      pow := by reg_simp; exact hp₃
      tapes := ?_
      input := fun j hj => ?_ }⟩
  · rw [apply_workTapes_eq]
    exact (((hT₁.of_eq (fun d hd => hr₂ d (by reg_ne)) hm₂).of_eq
      (fun d hd => hr₃ d (by reg_ne) (by reg_ne)) hm₃).set (by simp) _)
  · simp only [Data.set_mem]
    rw [hm₃, hm₂, hm₁ _ (by omega)]
    exact hx.input j hj

/-- Reading the symbols under the work heads. -/
private theorem tapesTree_spec {inp : List Bool} {c : Cfg k Bool Q inp}
    (next : (Fin k → Option Bool) → Code .additive (regs k)) {T : ℕ} {post : Data (regs k) → Prop}
    (hnext : ∀ x, Sim e x c → ∃ y, ExecWithin w (next c.workTapeSymbols) x y T ∧ post y) :
    ∀ rem, rem ≤ k → ∀ acc : Fin k → Option Bool,
      (∀ i : Fin k, rem ≤ i.val → acc i = c.workTapeSymbols i) →
      ∀ x, Sim e x c → ∃ y, ExecWithin w (tapesTree next rem acc) x y (T + 5 * rem) ∧ post y
  | 0, _, acc, hacc, x, hx => by
    have : acc = c.workTapeSymbols := funext fun i => hacc i (Nat.zero_le _)
    subst this
    simpa [tapesTree] using hnext x hx
  | rem + 1, hrem, acc, hacc, x, hx => by
    have h : rem < k := by omega
    have hcur : x.mem (x.regs (rAdr ⟨rem, h⟩)) = symCode (c.workTapeSymbols ⟨rem, h⟩) := by
      rw [hx.tapes.adr, hx.tapes.tape]; rfl
    have hx₁ : Sim e (x.set rCur (x.mem (x.regs (rAdr ⟨rem, h⟩)))) c :=
      hx.set_scratch (Or.inr rfl) _
    have hc1 : (x.set rCur (x.mem (x.regs (rAdr ⟨rem, h⟩)))).regs rCur =
        symCode (c.workTapeSymbols ⟨rem, h⟩) := by reg_simp; exact hcur
    have hz := hx₁.consts.zero
    have ho := hx₁.consts.one
    have hacc' (s : Option Bool) (hs : c.workTapeSymbols ⟨rem, h⟩ = s) :
        ∀ j : Fin k, rem ≤ j.val → Function.update acc ⟨rem, h⟩ s j = c.workTapeSymbols j := by
      intro j hj
      by_cases hji : j = ⟨rem, h⟩
      · subst hji; simp [hs]
      · rw [Function.update_of_ne hji]
        exact hacc j (by have : j.val ≠ rem := fun he => hji (Fin.ext he); omega)
    simp only [tapesTree, h, ↓reduceDIte]
    cases hs : c.workTapeSymbols ⟨rem, h⟩ with
    | none =>
      obtain ⟨y, hy, hQ⟩ := tapesTree_spec next hnext rem (by omega) _ (hacc' none hs) _ hx₁
      refine ⟨y, (ExecWithin.load.seq (ExecWithin.branch_pos ?_ hy)).mono (by omega), hQ⟩
      simp only [Cond.holds_eq, hc1, hz, hs, symCode]
    | some b =>
      cases b with
      | false =>
        obtain ⟨y, hy, hQ⟩ :=
          tapesTree_spec next hnext rem (by omega) _ (hacc' (some false) hs) _ hx₁
        refine ⟨y, (ExecWithin.load.seq (ExecWithin.branch_neg ?_
          (ExecWithin.branch_pos ?_ hy))).mono (by omega), hQ⟩
        · simp only [Cond.holds_eq, hc1, hz, hs, symCode]; decide
        · simp only [Cond.holds_eq, hc1, ho, hs, symCode]; decide
      | true =>
        obtain ⟨y, hy, hQ⟩ :=
          tapesTree_spec next hnext rem (by omega) _ (hacc' (some true) hs) _ hx₁
        refine ⟨y, (ExecWithin.load.seq (ExecWithin.branch_neg ?_
          (ExecWithin.branch_neg ?_ hy))).mono (by omega), hQ⟩
        · simp only [Cond.holds_eq, hc1, hz, hs, symCode]; decide
        · simp only [Cond.holds_eq, hc1, ho, hs, symCode]; decide

/-- Reading the input symbol. -/
private theorem inputTree_spec {inp : List Bool} {c : Cfg k Bool Q inp}
    (next : Option Bool → Code .additive (regs k)) {T : ℕ} {post : Data (regs k) → Prop}
    (hnext : ∀ x, Sim e x c → ∃ y, ExecWithin w (next c.inputSymbol) x y T ∧ post y)
    {x : Data (regs k)} (hx : Sim e x c) :
    ∃ y, ExecWithin w (inputTree next) x y (T + 7) ∧ post y := by
  have hh := hx.head
  have hz := hx.consts.zero
  have hf := hx.consts.fin
  have hpl := c.inputPos.isLt
  by_cases h0 : (c.inputPos : ℕ) = 0
  · obtain ⟨y, hy, hQ⟩ := hnext x hx
    rw [inputSymbol_eq_none_of_boundary (Or.inl h0)] at hy
    refine ⟨y, (ExecWithin.branch_pos ?_ hy).mono (by omega), hQ⟩
    simp only [Cond.holds_eq, hh, hz, h0]
  · by_cases hn : (c.inputPos : ℕ) = inp.length + 1
    · obtain ⟨y, hy, hQ⟩ := hnext x hx
      rw [inputSymbol_eq_none_of_boundary (Or.inr hn)] at hy
      refine ⟨y, (ExecWithin.branch_neg ?_ (ExecWithin.branch_pos ?_ hy)).mono (by omega), hQ⟩
      · simp only [Cond.holds_eq, hh, hz]; exact h0
      · simp only [Cond.holds_eq, hh, hf, hn]
    · have hj : (c.inputPos : ℕ) - 1 < inp.length := by omega
      have hsym : c.inputSymbol = some inp[(c.inputPos : ℕ) - 1] :=
        inputSymbolInner _ (by omega) hj
      have hmem : x.mem (x.regs rHead) = inp[(c.inputPos : ℕ) - 1].toNat := by
        rw [hh, ← hx.input _ hj]; congr 1; omega
      have hx₁ : Sim e (x.set rCur (x.mem (x.regs rHead))) c := hx.set_scratch (Or.inr rfl) _
      have hc1 : (x.set rCur (x.mem (x.regs rHead))).regs rCur =
          inp[(c.inputPos : ℕ) - 1].toNat := by reg_simp; exact hmem
      have hz₁ := hx₁.consts.zero
      obtain ⟨y, hy, hQ⟩ := hnext _ hx₁
      rw [hsym] at hy
      have hn0 : ¬(Cond.eq rHead rZero).Holds x := by simp only [Cond.holds_eq, hh, hz]; exact h0
      have hne : ¬(Cond.eq rHead rEnd).Holds x := by simp only [Cond.holds_eq, hh, hf]; exact hn
      cases hb : inp[(c.inputPos : ℕ) - 1] with
      | false =>
        rw [hb] at hy
        refine ⟨y, (ExecWithin.branch_neg hn0 (ExecWithin.branch_neg hne (ExecWithin.load.seq
          (ExecWithin.branch_pos ?_ hy)))).mono (by omega), hQ⟩
        simp only [Cond.holds_eq, hc1, hz₁, hb]; rfl
      | true =>
        rw [hb] at hy
        refine ⟨y, (ExecWithin.branch_neg hn0 (ExecWithin.branch_neg hne (ExecWithin.load.seq
          (ExecWithin.branch_neg ?_ hy)))).mono (by omega), hQ⟩
        simp only [Cond.holds_eq, hc1, hz₁, hb]; decide

/-- **One step.** The simulator's step code follows one step of a running configuration. -/
theorem stepCode_spec (δ : Q → Option Bool → (Fin k → Option Bool) → Action k Bool Q)
    {inp : List Bool} {c : Cfg k Bool Q inp} {q : Q} (hq : c.state = some q)
    {x : Data (regs k)} (hx : Sim e x c)
    (hfit : ∀ i, Fits w (tapeAddr k inp.length i
      (((δ q c.inputSymbol c.workTapeSymbols).apply c).workTapePos i)))
    (hbound : inp.length + 2 * k + m + 2 < 2 ^ w)
    (hout : ((δ q c.inputSymbol c.workTapeSymbols).apply c).output.length < w) :
    ∃ y, ExecWithin w (stepCode δ e) x y (stepCost k m) ∧
      Sim e y ((δ q c.inputSymbol c.workTapeSymbols).apply c) := by
  have hv : x.regs rState = e q := by rw [hx.state, hq]; rfl
  have hlt : (e q : ℕ) < m := (e q).isLt
  have he : e.symm ⟨(e q : ℕ), hlt⟩ = q := by simp
  have hx' := hx.set_scratch (Or.inl rfl) (e q)
  obtain ⟨y, hy, hS⟩ := inputTree_spec (c := c) (x := x.set rTmp (e q))
    (fun a => tapesTree (fun s => actionCode e (δ q a s)) k fun _ => none)
    (post := fun y => Sim e y ((δ q c.inputSymbol c.workTapeSymbols).apply c)) (T := 13 * k + 7)
    (fun x₁ hx₁ => (tapesTree_spec (T := 8 * k + 7) (fun s => actionCode e (δ q c.inputSymbol s))
      (fun x₂ hx₂ => actionCode_spec _ hx₂ hfit hbound hout) k le_rfl _
      (fun i hi => absurd i.isLt (by omega)) x₁ hx₁).imp fun y hy => ⟨hy.1.mono (by omega), hy.2⟩)
    hx'
  refine ⟨y, (dispatch_spec (reg := rState) (by reg_ne) (T := 13 * k + 14) (N := m) hv hlt ?_
    ?_).mono ?_, hS⟩
  · have : m < 2 ^ w := by omega
    omega
  · simp only [hlt, ↓reduceDIte, he]; exact hy
  · unfold stepCost; omega

/-- Placing the heads of the work tapes in a list without repetitions. -/
private theorem setupTapes_spec : ∀ (L : List (Fin k)), L.Nodup → ∀ {x : Data (regs k)},
    x.regs rEnd = n + 1 → n + 1 + 2 * k < 2 ^ w →
    ∃ y, ExecWithin w (setupTapes L) x y (2 * L.length + 1) ∧
      (∀ i, y.regs (rAdr i) = if i ∈ L then n + 1 + 2 * i else x.regs (rAdr i)) ∧
      (∀ d : Fin (regs k), (∀ i, d ≠ rAdr i) → d ≠ rTmp → y.regs d = x.regs d) ∧ y.mem = x.mem
  | [], _, x, _, _ => ⟨x, execWithin_skip, by simp, fun _ _ _ => rfl, rfl⟩
  | i :: L, hL, x, hx, hb => by
    obtain ⟨hiL, hL⟩ := List.nodup_cons.1 hL
    have hi := i.isLt
    have h₁ : Fits w (2 * i) := by unfold Fits; omega
    have h₂ : Fits w ((x.set rTmp (2 * i)).regs rEnd + (x.set rTmp (2 * i)).regs rTmp) := by
      unfold Fits; reg_simp; omega
    obtain ⟨y, hy, ha, hr, hm⟩ := setupTapes_spec L hL
      (x := (x.set rTmp (2 * i)).set (rAdr i)
        ((x.set rTmp (2 * i)).regs rEnd + (x.set rTmp (2 * i)).regs rTmp))
      (by reg_simp; exact hx) hb
    refine ⟨y, ((execWithin_const h₁).seq ((execWithin_add h₂).seq hy)).mono
      (by simp only [List.length_cons]; omega), fun j => ?_, fun d hd ht => ?_, ?_⟩
    · rw [ha j]
      by_cases hj : j ∈ L
      · simp [hj]
      · by_cases hji : j = i
        · subst hji; simpa [hj] using hx
        · simp only [hj, ↓reduceIte, List.mem_cons, hji, or_self]; reg_simp
    · rw [hr d hd ht, Data.set_regs, Function.update_of_ne (hd i)]; reg_simp
    · rw [hm]; rfl

/-- **Setup.** The simulator's setup reaches a representation of the initial configuration. -/
theorem setupCode_spec (q₀ : Q) (inp : List Bool) (hbound : inp.length + 2 * k + m + 2 < 2 ^ w) :
    ∃ y, ExecWithin w (setupCode q₀ e) (Data.init (inp.map Bool.toNat)) y (2 * k + 10) ∧
      Sim e y (Cfg.init q₀ inp : Cfg k Bool Q inp) := by
  set n := inp.length
  set x₀ : Data (regs k) := Data.init (inp.map Bool.toNat)
  have hr₀ : ∀ d, x₀.regs d = 0 := fun _ => rfl
  have hm₀ : x₀.mem 0 = n := by simp [x₀, n]
  have hq := (e q₀).isLt
  have f1 : Fits w 1 := by unfold Fits; omega
  set x₁ := x₀.set rEnd (x₀.mem (x₀.regs rZero))
  set x₂ := x₁.set rOne 1
  set x₃ := x₂.set rEnd (x₂.regs rEnd + x₂.regs rOne)
  set x₄ := x₃.set rHead 1
  set x₅ := x₄.set rStride (2 * k)
  set x₆ := x₅.set rLim (x₅.regs rEnd + x₅.regs rStride)
  set x₇ := x₆.set rStates m
  set x₈ := x₇.set rState (e q₀)
  set x₉ := x₈.set rPow 1
  have e₃ : x₃.regs rEnd = n + 1 := by simp only [x₃, x₂, x₁]; reg_simp; rw [hr₀, hm₀]
  have h₉ : x₉.regs rEnd = n + 1 := by simp only [x₉, x₈, x₇, x₆, x₅, x₄]; reg_simp; exact e₃
  obtain ⟨y, hy, ha, hr, hm⟩ := setupTapes_spec (n := n) (w := w) (List.finRange k)
    (List.nodup_finRange k) h₉ (by omega)
  have hexec : ExecWithin w (setupCode q₀ e) x₀ y (2 * k + 10) := by
    refine (ExecWithin.load.seq ((execWithin_const f1).seq ((execWithin_add ?_).seq
      ((execWithin_const f1).seq ((execWithin_const ?_).seq ((execWithin_add ?_).seq
      ((execWithin_const ?_).seq ((execWithin_const ?_).seq ((execWithin_const f1).seq
      hy))))))))).mono (by simp only [List.length_finRange]; omega)
    · unfold Fits; reg_simp; rw [hr₀, hm₀]; omega
    · unfold Fits; omega
    · unfold Fits; reg_simp; rw [hr₀, hm₀]; omega
    · unfold Fits; omega
    · unfold Fits; omega
  have hy : ∀ d : Fin (regs k), (∀ i, d ≠ rAdr i) → d ≠ rTmp → y.regs d = x₉.regs d := hr
  refine ⟨y, hexec, ?_⟩
  exact
    { consts :=
        { zero := by
            rw [hy _ (fun _ => by reg_ne) (by reg_ne)]
            simp only [x₉, x₈, x₇, x₆, x₅, x₄, x₃, x₂, x₁]; reg_simp; rfl
          one := by
            rw [hy _ (fun _ => by reg_ne) (by reg_ne)]
            simp only [x₉, x₈, x₇, x₆, x₅, x₄, x₃, x₂]; reg_simp
          fin := by rw [hy _ (fun _ => by reg_ne) (by reg_ne)]; exact h₉
          states := by
            rw [hy _ (fun _ => by reg_ne) (by reg_ne)]; simp only [x₉, x₈, x₇]; reg_simp
          stride := by
            rw [hy _ (fun _ => by reg_ne) (by reg_ne)]
            simp only [x₉, x₈, x₇, x₆, x₅]; reg_simp
          lim := by
            rw [hy _ (fun _ => by reg_ne) (by reg_ne)]
            simp only [x₉, x₈, x₇, x₆, x₅, x₄]; reg_simp
            rw [e₃] }
      state := by rw [hy _ (fun _ => by reg_ne) (by reg_ne)]; simp only [x₉, x₈]; reg_simp; rfl
      head := by
        rw [hy _ (fun _ => by reg_ne) (by reg_ne)]
        simp only [x₉, x₈, x₇, x₆, x₅, x₄]; reg_simp
        simp [Cfg.init]
      val := by
        rw [hy _ (fun _ => by reg_ne) (by reg_ne)]
        simp only [x₉, x₈, x₇, x₆, x₅, x₄, x₃, x₂, x₁]; reg_simp
        rfl
      pow := by rw [hy _ (fun _ => by reg_ne) (by reg_ne)]; simp only [x₉]; reg_simp; rfl
      tapes :=
        { sgn := fun i => by
            rw [hy _ (fun _ => by reg_ne) (by reg_ne)]
            simp only [x₉, x₈, x₇, x₆, x₅, x₄, x₃, x₂, x₁]; reg_simp; simp [x₀, sgnOf]
          adr := fun i => by
            rw [ha i]; simp [tapeAddr, magOf, sgnOf, n]
          tape := fun i z => by
            rw [hm]
            simp only [x₉, x₈, x₇, x₆, x₅, x₄, x₃, x₂, x₁, Data.set_mem, x₀]
            have hlt := lt_tapeAddr k n i z
            rw [show tapeAddr k n i z = (tapeAddr k n i z - 1) + 1 by omega, Data.init_mem_succ,
              List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by simp only [List.length_map, n] at hlt ⊢; omega)]
            rfl }
      input := fun j hj => by
        rw [hm]
        simp only [x₉, x₈, x₇, x₆, x₅, x₄, x₃, x₂, x₁, Data.set_mem, x₀, Data.init_mem_succ]
        simp [hj] }

end Pieces

/-! ## Runs -/

section Run

variable {tm : MultiTapeTM k Bool Q} {inp : List Bool}

/-- The output tape only grows. -/
private theorem length_output_runFrom_mono (c : Cfg k Bool Q inp) {j j' : ℕ} (h : j ≤ j') :
    (tm.runFrom c j).output.length ≤ (tm.runFrom c j').output.length := by
  induction h with
  | refl => exact le_rfl
  | @step j' _ ih =>
    rw [MultiTapeTM.runFrom_succ]
    refine ih.trans ?_
    cases hq : (tm.runFrom c j').state with
    | none => rw [MultiTapeTM.step_of_halt hq]
    | some q => rw [MultiTapeTM.step_of_state hq]; simp [Action.apply]

variable {δ : Q → Option Bool → (Fin k → Option Bool) → Action k Bool Q}

/-- **The loop.** From a representation of the configuration after `j` steps, the loop of the
simulator reaches a representation of the halting configuration after `t₀ = j + d` steps, within
`d (stepCost k m + 2) + 2` instructions. -/
theorem loop_spec (hδ : ∀ q a s, tm.tr q a s = δ q a s) (e : Q ≃ Fin m) {w t₀ : ℕ}
    (hrun : ∀ j < t₀, (tm.runFrom (tm.initCfg inp) j).state ≠ none)
    (hhalt : (tm.runFrom (tm.initCfg inp) t₀).state = none)
    (hfit : ∀ j ≤ t₀, ∀ i,
      Fits w (tapeAddr k inp.length i ((tm.runFrom (tm.initCfg inp) j).workTapePos i)))
    (hbound : inp.length + 2 * k + m + 2 < 2 ^ w)
    (hout : ∀ j ≤ t₀, (tm.runFrom (tm.initCfg inp) j).output.length < w) (d : ℕ) :
    ∀ j (x : Data (regs k)), j + d = t₀ → Sim e x (tm.runFrom (tm.initCfg inp) j) →
      ∃ y, ExecWithin w (.loop (.lt rState rStates) (stepCode δ e)) x y
        (d * (stepCost k m + 2) + 2) ∧ Sim e y (tm.runFrom (tm.initCfg inp) t₀) := by
  induction d with
  | zero =>
    intro j x hj hx
    simp only [Nat.add_zero] at hj
    subst hj
    refine ⟨x, (ExecWithin.loop_exit ?_).mono (by omega), hx⟩
    simp only [Cond.holds_lt, hx.state, hx.consts.states, hhalt, stateCode]; omega
  | succ d ih =>
    intro j x hj hx
    have hjt : j < t₀ := by omega
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 (hrun j hjt)
    have hstep : tm.runFrom (tm.initCfg inp) (j + 1) =
        (δ q (tm.runFrom (tm.initCfg inp) j).inputSymbol
          (tm.runFrom (tm.initCfg inp) j).workTapeSymbols).apply
          (tm.runFrom (tm.initCfg inp) j) := by
      rw [MultiTapeTM.runFrom_succ, MultiTapeTM.step_of_state hq, hδ]
    obtain ⟨y₁, h₁, hy₁⟩ := stepCode_spec δ hq hx
      (by rw [← hstep]; exact hfit (j + 1) (by omega)) hbound
      (by rw [← hstep]; exact hout (j + 1) (by omega))
    rw [← hstep] at hy₁
    obtain ⟨y, h₂, hy⟩ := ih (j + 1) y₁ (by omega) hy₁
    refine ⟨y, (ExecWithin.loop_iter ?_ h₁ h₂).mono (by rw [Nat.succ_mul]; omega), hy⟩
    simp only [Cond.holds_lt, hx.state, hx.consts.states, hq, stateCode]
    exact (e q).isLt

/-- **Turing machines on the word RAM.** Let `tm` be a machine with `k` work tapes and transition
function `δ`, whose states are numbered by `e`. If `tm` halts on `inp` within `t` steps, then at
every word size `w` whose words hold `simBound k m |inp| t` and the length of the output tape, the
simulator halts on `inp.map Bool.toNat` within `simTime k m t` instructions, returning the output
tape read as a little-endian binary number. -/
theorem executes_simProgram (hδ : ∀ q a s, tm.tr q a s = δ q a s) (e : Q ≃ Fin m) {t : ℕ}
    (ht : (tm.runFrom (tm.initCfg inp) t).state = none) {w : ℕ}
    (hw : simBound k m inp.length t < 2 ^ w)
    (hout : (tm.runFrom (tm.initCfg inp) t).output.length < w) :
    ∃ n ≤ simTime k m t, Executes w (simProgram δ tm.q₀ e) (State.init (inp.map Bool.toNat))
      (BitString.lsbValue (tm.runFrom (tm.initCfg inp) t).output) n := by
  obtain ⟨t₀, ht₀, hhalts⟩ := MultiTapeTM.exists_haltsAt ht
  have hhalt : (tm.runFrom (tm.initCfg inp) t₀).state = none := hhalts.halted
  have hrun : ∀ j < t₀, (tm.runFrom (tm.initCfg inp) j).state ≠ none :=
    fun j hj => hhalts.not_halted hj
  have hsame : tm.runFrom (tm.initCfg inp) t = tm.runFrom (tm.initCfg inp) t₀ :=
    hhalts.runFrom_eq ht₀
  have hk : 2 * k ≤ 2 * k * (t + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hbound : inp.length + 2 * k + m + 2 < 2 ^ w := by unfold simBound at hw; omega
  have hfit : ∀ j ≤ t₀, ∀ i,
      Fits w (tapeAddr k inp.length i ((tm.runFrom (tm.initCfg inp) j).workTapePos i)) := by
    intro j hj i
    have habs := abs_le.1 (MultiTapeTM.abs_workTapePos_runFrom_le (tm := tm) inp j i)
    have h1 := tapeAddr_lt (n := inp.length) i
      (z := (tm.runFrom (tm.initCfg inp) j).workTapePos i) (d := t) (by omega)
    unfold Fits; unfold simBound at hw; omega
  have hout' : ∀ j ≤ t₀, (tm.runFrom (tm.initCfg inp) j).output.length < w :=
    fun j hj => lt_of_le_of_lt (length_output_runFrom_mono _ (hj.trans ht₀)) hout
  obtain ⟨x, hx₁, hsx⟩ := setupCode_spec (e := e) (w := w) tm.q₀ inp hbound
  obtain ⟨y, hy₁, hsy⟩ := loop_spec (δ := δ) hδ e hrun hhalt hfit hbound hout' (t₀) 0 x
    (by omega) hsx
  obtain ⟨n, hn, hexec⟩ := hx₁.seq hy₁
  refine ⟨n + 1, ?_, ?_⟩
  · unfold simTime
    have := Nat.mul_le_mul_right (stepCost k m + 2) ht₀
    omega
  · have h := hexec.executes rVal
    rw [hsy.val, ← hsame] at h
    exact h

end Run

/-! ## Polynomial time -/

section PolyTime

variable {α β : Type*}

/-- At word size `logWidth (D + d) n`, words hold numbers below `D (n + 1) ^ d`. -/
theorem lt_two_pow_logWidth (D d n : ℕ) : D * (n + 1) ^ d < 2 ^ logWidth (D + d) n := by
  unfold logWidth
  have hn : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h1 : D < 2 ^ (D * (Nat.log 2 n + 1)) := Nat.lt_two_pow_self.trans_le
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (by omega)))
  have h2 : (n + 1) ^ d ≤ 2 ^ (d * (Nat.log 2 n + 1)) := by
    rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left hn d
  calc D * (n + 1) ^ d < 2 ^ (D * (Nat.log 2 n + 1)) * 2 ^ (d * (Nat.log 2 n + 1)) :=
        Nat.mul_lt_mul_of_lt_of_le h1 h2 (by positivity)
    _ = 2 ^ ((D + d) * (Nat.log 2 n + 1)) := by rw [← pow_add, add_mul]

/-- **Polynomial-time Turing machines on the word RAM.** A function computable in polynomial time
by a multi-tape Turing machine is computed by one fixed word-RAM program over `Basis.additive`, on
the input bits as words, within a polynomial number of instructions, at every word size above a
polynomial threshold. The program returns the encoded output read as a little-endian binary
number. The threshold is polynomial because one word holds the whole output. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.exists_wordRAM {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (h : Turing.MultiTapeTM.ComputableInPolyTime f encIn encOut) :
    ∃ (r : ℕ) (p : Program .additive r) (T W : ℕ → ℕ), PolynomiallyBounded T ∧
      PolynomiallyBounded W ∧ p.ComputesInTime (fun _ a => (encIn a).map Bool.toNat)
        (fun a _ => T (encIn a).length) (fun a w => W (encIn a).length ≤ w)
        (fun a => BitString.lsbValue (encOut (f a))) := by
  obtain ⟨t, s, ht, -, K, Q, hfin, tm, htm⟩ := h
  have := Fintype.ofFinite Q
  refine ⟨regs K, simProgram tm.tr tm.q₀ (Fintype.equivFin Q),
    fun n => simTime K (Fintype.card Q) (t n), fun n => simBound K (Fintype.card Q) n (t n) + t n,
    ?_, ?_, fun a w hw _ => ?_⟩
  · unfold simTime; exact (PolynomiallyBounded.const _).add (ht.mul (.const _))
  · unfold simBound
    obtain ⟨c, d, hc⟩ := polynomiallyBounded_iff_le.1 ht
    refine PolynomiallyBounded.of_forall_le (2 * K * c + c + 2 * K + Fintype.card Q + 4) (d + 1)
      fun n => ?_
    have hP1 : 1 ≤ (n + 1) ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
    have hPn : n + 1 ≤ (n + 1) ^ (d + 1) :=
      (pow_one (n + 1)).symm.le.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have ht' : t n ≤ c * (n + 1) ^ (d + 1) :=
      (hc n).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by omega) (by omega)))
    nlinarith
  · beta_reduce at hw
    obtain ⟨hhalt, hout⟩ := (htm a).runFrom_of_le le_rfl
    beta_reduce at hhalt hout
    have hlen := MultiTapeTM.length_output_runFrom_le tm (tm.initCfg (encIn a)) (t (encIn a).length)
    have h0 : (tm.initCfg (encIn a)).output.length = 0 := rfl
    have hb : simBound K (Fintype.card Q) (encIn a).length (t (encIn a).length) < 2 ^ w :=
      Nat.lt_two_pow_self.trans_le' (by omega)
    obtain ⟨n, hn, hex⟩ := executes_simProgram (fun _ _ _ => rfl) (Fintype.equivFin Q) hhalt hb
      (by unfold simBound at hw; omega)
    rw [hout] at hex
    exact ⟨n, hex, hn⟩

/-- **Polynomial-time Turing machines on the word RAM**, for binary outputs: the program returns
the value itself. -/
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.exists_wordRAM_nat {f : α → ℕ}
    {encIn : α ↪ List Bool}
    (h : Turing.MultiTapeTM.ComputableInPolyTime f encIn Turing.MultiTapeTM.encNat) :
    ∃ (r : ℕ) (p : Program .additive r) (T W : ℕ → ℕ), PolynomiallyBounded T ∧
      PolynomiallyBounded W ∧ p.ComputesInTime (fun _ a => (encIn a).map Bool.toNat)
        (fun a _ => T (encIn a).length) (fun a w => W (encIn a).length ≤ w) f := by
  obtain ⟨r, p, T, W, hT, hW, hp⟩ := h.exists_wordRAM
  have hf : (fun a => BitString.lsbValue (Turing.MultiTapeTM.encNat (f a))) = f :=
    funext fun a => by rw [Turing.MultiTapeTM.encNat_apply, BitString.lsbValue_bits]
  exact ⟨r, p, T, W, hT, hW, hf ▸ hp⟩

end PolyTime

end Cslib.WordRAM.OfTuring
