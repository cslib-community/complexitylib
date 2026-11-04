/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Function
public import Complexity.Computability.WordRAM.ListArray

/-!
# List-valued outputs of word-RAM programs

A word-RAM program returns one word with `halt`. A list is returned through memory: `halt`
returns an address `v`, and the output is the length-prefixed array
`[mem (v + 1), …, mem (v + mem v)]` in the memory just before the halting step (`outputList`).
This mirrors the input convention of `State.init`, with the length at address `0` and the words
at `1, …, n`. In particular, returning address `0` without writing outputs the input itself
(`outputList_init`).

`Program.parkHalts` replaces every `halt i` by a jump to a self-loop at label `p.length + i`.
A halting run of `p` becomes a run of `p.parkHalts` that reaches the *parked* state, which has
the pre-halt data and a control label recording the output register, and stays there
(`ExecutesList.runs_parkHalts`). A clocked simulator that only produces continuing states can
therefore read the output from its final state.

## Main definitions

* `Cslib.WordRAM.outputList`: the length-prefixed array at an address.
* `Cslib.WordRAM.ExecutesList`: a halting run returns the address of a given list.
* `Cslib.WordRAM.Program.ComputesListInTime`: a fixed program computes a list-valued function.
* `Cslib.WordRAM.UniformComputableListInPolyTime`: a fixed program computes it in polynomially
  many instructions at every fitting width above a logarithmic threshold.
* `Cslib.WordRAM.Program.parkHalts`: halts replaced by self-loops recording the output register.

## Main results

* `Cslib.WordRAM.outputList_eq_iff`: the convention in terms of `Block.HoldsList`.
* `Cslib.WordRAM.Exec.executesList`, `Cslib.WordRAM.Code.computesListInTime_program`:
  structured certificates, charging the final halt.
* `Cslib.WordRAM.ExecutesList.runs_parkHalts`: a halting run of `n ≤ N` instructions gives an
  `N`-step run of `p.parkHalts` to the parked pre-halt state.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ} {α : Type*}

/-! ## The output convention -/

/-- The length-prefixed array at address `v`: `[mem (v + 1), …, mem (v + mem v)]`. -/
def outputList (mem : ℕ → ℕ) (v : ℕ) : List ℕ :=
  (List.range (mem v)).map fun i => mem (v + 1 + i)

@[simp] theorem length_outputList (mem : ℕ → ℕ) (v : ℕ) :
    (outputList mem v).length = mem v := by
  simp [outputList]

theorem getElem_outputList (mem : ℕ → ℕ) (v i : ℕ) (hi : i < (outputList mem v).length) :
    (outputList mem v)[i] = mem (v + 1 + i) := by
  simp [outputList]

/-- The array at `v` is `l` exactly when `v` holds the length of `l` and the following cells hold
its entries. -/
theorem outputList_eq_iff {mem : ℕ → ℕ} {v : ℕ} {l : List ℕ} :
    outputList mem v = l ↔ mem v = l.length ∧ Block.HoldsList (v + 1) l mem := by
  constructor
  · rintro rfl
    refine ⟨(length_outputList mem v).symm, fun i => ?_⟩
    change mem (v + 1 + i.val) = (outputList mem v)[i.val]
    rw [getElem_outputList]
  · rintro ⟨hlen, hl⟩
    refine List.ext_getElem (by simp [hlen]) fun i hi _ => ?_
    rw [getElem_outputList]
    exact hl.get i (by simpa [hlen] using hi)

/-- Returning address `0` of the initial memory outputs the input. -/
theorem outputList_init (input : List ℕ) :
    outputList (Data.init input : Data r).mem 0 = input := by
  refine outputList_eq_iff.2 ⟨rfl, fun i => ?_⟩
  change (Data.init input : Data r).mem (0 + 1 + i.val) = input[i.val]
  rw [Nat.zero_add, Nat.add_comm, Data.init_mem_succ]
  simp [List.getD_eq_getElem?_getD]

/-- `ExecutesList w p s l n`: running `p` at word size `w` from `s` halts after exactly `n`
instructions, the final `halt` included, returning an address at which the memory just before
halting holds `l` as a length-prefixed array. -/
def ExecutesList (w : ℕ) (p : Program B r) (s : State r) (l : List ℕ) (n : ℕ) : Prop :=
  ∃ t m v, Runs w p s t m ∧ step w p t = .halt v ∧ outputList t.data.mem v = l ∧ n = m + 1

/-- A list-valued run is in particular a halting run, returning the address of the list. -/
theorem ExecutesList.executes {w : ℕ} {p : Program B r} {s : State r} {l : List ℕ} {n : ℕ}
    (h : ExecutesList w p s l n) : ∃ v, Executes w p s v n := by
  obtain ⟨t, m, v, hr, hh, -, rfl⟩ := h
  exact ⟨v, t, m, hr, hh, rfl⟩

/-- One program returns the list `f a` at every admitted fitting width within `time a w`
instructions. The final halt is counted; the mathematical input encoding is a convention. -/
def Program.ComputesListInTime (p : Program B r) (encode : ℕ → α → List ℕ)
    (time : α → ℕ → ℕ) (allowed : α → ℕ → Prop) (f : α → List ℕ) : Prop :=
  ∀ a w, allowed a w → InputFits w (encode w a) →
    ∃ n, ExecutesList w p (.init (encode w a)) (f a) n ∧ n ≤ time a w

/-- A fixed program computes a list-valued function in polynomially many instructions in
`size a`, at every fitting width above a positive logarithmic threshold. -/
def UniformComputableListInPolyTime (B : Basis) (f : α → List ℕ) (encode : ℕ → α → List ℕ)
    (size : α → ℕ) : Prop :=
  ∃ T, PolynomiallyBounded T ∧ ∃ k, 0 < k ∧ ∃ r, ∃ p : Program B r,
    p.ComputesListInTime encode (fun a _ => T (size a)) (fun a w => logWidth k (size a) ≤ w) f

/-- Increase a fixed program's time bound and restrict its admitted widths. -/
theorem Program.ComputesListInTime.mono {p : Program B r} {encode : ℕ → α → List ℕ}
    {time time' : α → ℕ → ℕ} {allowed allowed' : α → ℕ → Prop} {f : α → List ℕ}
    (h : p.ComputesListInTime encode time allowed f) (ht : ∀ a w, time a w ≤ time' a w)
    (ha : ∀ a w, allowed' a w → allowed a w) :
    p.ComputesListInTime encode time' allowed' f := by
  intro a w hw hi
  obtain ⟨n, he, hn⟩ := h a w (ha a w hw) hi
  exact ⟨n, he, hn.trans (ht a w)⟩

/-- A structured execution followed by `halt out` returns the array at the address in `out`,
with one more instruction. -/
theorem Exec.executesList {w : ℕ} {c : Code B r} {x y : Data r} {n : ℕ} (h : Exec w c x y n)
    (out : Fin r) :
    ExecutesList w (c.program out) ⟨0, x⟩ (outputList y.mem (y.regs out)) (n + 1) := by
  have hr := h.runs (pc := 0) (p := c.program out) (Program.Contains.self _).append_left
  have hh : step w (c.program out) ⟨0 + c.size, y⟩ = .halt (y.regs out) :=
    step_halt (by simp [Code.program])
  exact ⟨_, n, _, hr, hh, rfl, rfl⟩

/-- A structured certificate leaving the address of `f a` in register `out` computes `f`, with
one more instruction for the final halt. -/
theorem Code.computesListInTime_program {encode : ℕ → α → List ℕ} {time : α → ℕ → ℕ}
    {allowed : α → ℕ → Prop} {f : α → List ℕ} (c : Code B r) (out : Fin r)
    (h : ∀ a w, allowed a w → InputFits w (encode w a) →
      ∃ y, ExecWithin w c (.init (encode w a)) y (time a w) ∧
        outputList y.mem (y.regs out) = f a) :
    (c.program out).ComputesListInTime encode (fun a w => time a w + 1) allowed f := by
  intro a w hw hi
  obtain ⟨y, ⟨n, hn, he⟩, hy⟩ := h a w hw hi
  exact ⟨n + 1, hy ▸ he.executesList out, Nat.add_le_add_right hn 1⟩

/-! ## Parking the halts -/

/-- Replace `halt i` by a jump to label `L + i`; every other instruction is unchanged. -/
def Instr.parkHalt (L : ℕ) : Instr B r → Instr B r
  | .halt i => .jump (L + i)
  | i => i

/-- Replace every `halt i` of `p` by a jump to a self-loop at label `p.length + i`. Registers and
all non-halting steps are unchanged; the parked label records the output register. -/
def Program.parkHalts (p : Program B r) : Program B r :=
  p.map (Instr.parkHalt p.length) ++ List.ofFn fun i : Fin r => .jump (p.length + i)

namespace Program

variable {p : Program B r}

theorem length_parkHalts (p : Program B r) : p.parkHalts.length = p.length + r := by
  simp [parkHalts]

theorem getElem?_parkHalts_of_lt {pc : ℕ} (h : pc < p.length) :
    p.parkHalts[pc]? = p[pc]?.map (Instr.parkHalt p.length) := by
  rw [parkHalts, List.getElem?_append_left (by simpa using h), List.getElem?_map]

theorem getElem?_parkHalts_park (i : Fin r) :
    p.parkHalts[p.length + i]? = some (.jump (p.length + i)) := by
  rw [parkHalts, List.getElem?_append_right (by simp), List.length_map,
    Nat.add_sub_cancel_left, List.getElem?_ofFn]
  simp

/-- Every non-halting step of `p` is a step of `p.parkHalts`. -/
theorem next_parkHalts {w : ℕ} {s t : State r} (h : Next w p s t) : Next w p.parkHalts s t := by
  unfold Next step at h ⊢
  cases hp : p[s.pc]? with
  | none => simp [hp] at h
  | some i =>
    have hlt : s.pc < p.length := (List.getElem?_eq_some_iff.mp hp).1
    rw [getElem?_parkHalts_of_lt hlt, hp, Option.map_some]
    rw [hp] at h
    cases i with
    | halt => simp only at h; cases h
    | _ => exact h

/-- Every run of `p` is a run of `p.parkHalts`. -/
theorem runs_parkHalts {w : ℕ} {s t : State r} {m : ℕ} (h : Runs w p s t m) :
    Runs w p.parkHalts s t m :=
  h.map id fun _ _ => next_parkHalts

/-- A halting step of `p` becomes a step of `p.parkHalts` to the parked label of the output
register. -/
theorem next_parkHalts_of_halt {w v : ℕ} {s : State r} (h : step w p s = .halt v) :
    ∃ i : Fin r, s.data.regs i = v ∧ Next w p.parkHalts s ⟨p.length + i, s.data⟩ := by
  unfold step at h
  cases hp : p[s.pc]? with
  | none => simp [hp] at h
  | some ins =>
    have hlt : s.pc < p.length := (List.getElem?_eq_some_iff.mp hp).1
    rw [hp] at h
    cases ins with
    | halt i =>
      refine ⟨i, Outcome.halt.inj h, step_jump ?_⟩
      rw [getElem?_parkHalts_of_lt hlt, hp, Option.map_some]
      rfl
    | op o => simp only at h; split at h <;> cases h
    | jump => simp only at h; cases h
    | branch => simp only at h; cases h
    | rand => simp only at h; cases h

/-- A parked state steps to itself. -/
theorem next_parkHalts_park {w : ℕ} (i : Fin r) (x : Data r) :
    Next w p.parkHalts ⟨p.length + i, x⟩ ⟨p.length + i, x⟩ :=
  step_jump (getElem?_parkHalts_park i)

theorem runs_parkHalts_park {w : ℕ} (i : Fin r) (x : Data r) (j : ℕ) :
    Runs w p.parkHalts ⟨p.length + i, x⟩ ⟨p.length + i, x⟩ j := by
  induction j with
  | zero => exact .refl _
  | succ j ih => exact ih.tail _ _ _ _ (next_parkHalts_park i x)

end Program

/-- **A list-valued run, parked.** If `p` returns `l` within `n ≤ N` instructions, then
`p.parkHalts` runs for exactly `N` steps to a parked state: its label is `p.length + i` and its
data holds `l` at the address in register `i`. -/
theorem ExecutesList.runs_parkHalts {w : ℕ} {p : Program B r} {s : State r} {l : List ℕ} {n N : ℕ}
    (h : ExecutesList w p s l n) (hN : n ≤ N) :
    ∃ (i : Fin r) (x : Data r), Runs w p.parkHalts s ⟨p.length + i, x⟩ N ∧
      outputList x.mem (x.regs i) = l := by
  obtain ⟨t, m, v, hr, hh, hl, rfl⟩ := h
  obtain ⟨i, hv, hn⟩ := Program.next_parkHalts_of_halt hh
  refine ⟨i, t.data, ?_, hv ▸ hl⟩
  have h₁ := (Program.runs_parkHalts hr).tail _ _ _ _ hn
  have h₂ := h₁.trans (Program.runs_parkHalts_park i t.data (N - (m + 1)))
  rwa [Nat.add_sub_cancel' hN] at h₂

end Cslib.WordRAM
