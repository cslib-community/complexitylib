/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.Machines.ReadMachine.Tidy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Data.List.GetD
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain

/-!
# Writing circuits chunk by chunk in logarithmic space

A *writer* (`Cslib.Complexity.CircuitValue.WriterSpec`) is a read machine on a framed input `frame
w` that counts the length `n` of `w`, emitting a fixed word for each bit and another at the end,
then emits the chunks `chunk n 0, …, chunk n (N n - 1)` and a trailer, keeping only the number of
the current chunk, and finally emits a word for each bit of `w`
(`Cslib.Complexity.CircuitValue.WriterSpec.run_machine`). When the number of chunks is
polynomially bounded and the chunks and the trailer are computed within work space linear in the
binary lengths of `n` and of the number of the chunk, the writer runs in logarithmic space
(`Cslib.Complexity.CircuitValue.WriterSpec.computableInLogSpace`). This is how encoded instances of
circuit value problems built from uniform circuits, such as the tableau of a machine, are written
in logarithmic space.

## Main definitions

* `Cslib.Complexity.CircuitValue.WriterSpec`: what a writer emits.
* `Cslib.Complexity.CircuitValue.WriterSpec.machine`: the writer, as a read machine.
* `Cslib.Complexity.CircuitValue.WriterSpec.output`: the word it writes.

## Main results

* `Cslib.Complexity.CircuitValue.WriterSpec.run_machine`: the writer halts with its output.
* `Cslib.Complexity.CircuitValue.WriterSpec.computableInLogSpace`: a writer with chunks computed in
  linear space runs in logarithmic space.
-/

@[expose] public section

namespace Cslib.Complexity.CircuitValue

open Turing MultiTapeTM ComputableTidilyInSpace

/-- The read address of the writer: the markers `true` of the framed input while counting, the
input bits while copying. -/
def writerAddr (s : ℕ × ℕ × ℕ) : Option ℕ :=
  if s.1 = 0 then some (2 * s.2.2) else if s.1 = 2 then some (2 * s.2.2 + 1) else none

/-- The encoding of the states of the writer. -/
abbrev encWState : ℕ × ℕ × ℕ ↪ List Bool := encPair encNat (encPair encNat encNat)

/-- The space budget of a state of the writer: the length of its encoding. -/
def wBudget (s : ℕ × ℕ × ℕ) : ℕ := (encWState s).length + 1

private theorem writerAddr_inSpace :
    ComputableTidilyInSpace writerAddr encWState (encOption encNat) wBudget := by
  have hin : (fun s => (encWState s).length) ≼ wBudget := .of_le fun _ => by
    simp only [wBudget]; omega
  have hph := (ComputableTidilyInSpace.fst encNat (encPair encNat encNat)).weaken hin
  have hi := snd' ((ComputableTidilyInSpace.snd encNat (encPair encNat encNat)).weaken hin)
  have hsome {a : ℕ × ℕ × ℕ → ℕ} (ha : ComputableTidilyInSpace a encWState encNat wBudget) :
      ComputableTidilyInSpace (fun s => some (a s)) encWState (encOption encNat) wBudget :=
    budget_comp_linear (of_inO (ComputableTidilyInDegree.optionSome (enc₁ := encNat)).inO_one) ha
  have h2i := budget_natMul (budget_const (encB := encNat) 2 hin) hi
  refine (budget_ite (budget_natEq hph (budget_const (encB := encNat) 0 hin)) (hsome h2i)
    (budget_ite (budget_natEq hph (budget_const (encB := encNat) 2 hin))
      (hsome (budget_natAdd h2i (budget_const 1 hin)))
      (budget_const (encB := encOption encNat) none hin))).of_enc_eq fun s => ?_
  simp only [writerAddr, decide_eq_true_eq]

/-- The states of the writer on an input of length `n`, with `N` gates. -/
private def WInv (n N : ℕ) (s : ℕ × ℕ × ℕ) : Prop :=
  (s.1 = 0 ∧ s.2.1 = 0 ∧ s.2.2 ≤ n) ∨ (s.1 = 1 ∧ s.2.1 = n ∧ s.2.2 ≤ N) ∨
    (s.1 = 2 ∧ s.2.1 = n ∧ s.2.2 ≤ n) ∨ (s.1 = 3 ∧ s.2.1 = n ∧ s.2.2 = 0)

private theorem le_of_wInv {n N : ℕ} {s : ℕ × ℕ × ℕ} (h : WInv n N s) :
    s.1 ≤ 3 ∧ s.2.1 ≤ n ∧ s.2.2 ≤ n + N := by
  rcases h with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ <;> omega

/-- **What a writer emits**: a word for each bit of the input and a word at the end while it
counts the input, then `numChunks n` chunks and a trailer, then a word for each bit of the input
while it copies the input. -/
structure WriterSpec where
  /-- The word emitted for each bit of the input while counting. -/
  countUnit : List Bool
  /-- The word emitted at the end of the count. -/
  countEnd : List Bool
  /-- The number of chunks, for an input of length `n`. -/
  numChunks : ℕ → ℕ
  /-- Chunk `i`, for an input of length `n`. -/
  chunk : ℕ → ℕ → List Bool
  /-- The word emitted after the chunks, for an input of length `n`. -/
  trailer : ℕ → List Bool
  /-- The word emitted for each bit of the input while copying. -/
  copyBit : Bool → List Bool

namespace WriterSpec

variable (S : WriterSpec)

/-- The step of the writer. Its state is a phase, the length `n` of the input and a counter:
phase `0` counts the input, phase `1` writes the chunks, phase `2` copies the input, phase `3`
halts. -/
def step (s : ℕ × ℕ × ℕ) (b : Bool) : (ℕ × ℕ × ℕ) × List Bool :=
  if s.1 = 0 then
    if b then ((0, 0, s.2.2 + 1), S.countUnit) else ((1, s.2.2, 0), S.countEnd)
  else if s.1 = 1 then
    if s.2.2 < S.numChunks s.2.1 then ((1, s.2.1, s.2.2 + 1), S.chunk s.2.1 s.2.2)
    else ((2, s.2.1, 0), S.trailer s.2.1)
  else if s.1 = 2 then
    if s.2.2 < s.2.1 then ((2, s.2.1, s.2.2 + 1), S.copyBit b) else ((3, s.2.1, 0), [])
  else (s, [])

/-- **The writer**, as a read machine on the framed input. -/
def machine : ReadMachine (ℕ × ℕ × ℕ) where
  init := (0, 0, 0)
  halt s := decide (s.1 = 3)
  addr := writerAddr
  step := S.step

/-- **The word written** on the input `w`. -/
def output (w : List Bool) : List Bool :=
  (List.replicate w.length S.countUnit).flatten ++ S.countEnd ++
    ((List.range (S.numChunks w.length)).map (S.chunk w.length)).flatten ++
      S.trailer w.length ++ w.flatMap S.copyBit

/-- The number of steps of the writer on an input of length `n`. -/
def rounds (n : ℕ) : ℕ := (n + 1) + (S.numChunks n + 1) + (n + 1)

private theorem readBit_count (w : List Bool) (i : ℕ) :
    S.machine.readBit (frame w) (0, 0, i) = decide (i < w.length) := by
  simp only [ReadMachine.readBit, machine, writerAddr, ↓reduceIte]
  exact getD_frame_two_mul w i

private theorem readBit_copy (w : List Bool) (n i : ℕ) :
    S.machine.readBit (frame w) (2, n, i) = w.getD i false := by
  simp only [ReadMachine.readBit, machine, writerAddr, OfNat.ofNat_ne_zero, ↓reduceIte]
  exact getD_frame_two_mul_add_one w i

private theorem flatten_map_range_getD {β : Type*} (f : Bool → List β) (w : List Bool) :
    ((List.range w.length).map fun i => f (w.getD i false)).flatten = w.flatMap f := by
  have h : (List.range w.length).map (fun i => w.getD i false) = w := by
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simp [List.getElem?_eq_getElem h₂]
  conv_rhs => rw [← h]
  rw [List.flatMap, List.map_map]
  rfl

/-- **The writer halts with its output.** -/
theorem run_machine (w : List Bool) :
    S.machine.run (frame w) (S.rounds w.length) = ⟨(3, w.length, 0), S.output w⟩ := by
  have hstep (s : ℕ × ℕ × ℕ) (out : List Bool) (h : S.machine.halt s = false) :
      S.machine.next (frame w) ⟨s, out⟩ =
        ⟨(S.step s (S.machine.readBit (frame w) s)).1,
          out ++ (S.step s (S.machine.readBit (frame w) s)).2⟩ :=
    ReadMachine.next_of_not_halt _ _ h
  -- counting
  have h₀ := S.machine.runFrom_loop (frame w) (fun i => (0, 0, i)) (fun _ => S.countUnit)
    (M := w.length) (fun i hi => ⟨rfl, by
      rw [readBit_count, decide_eq_true hi]
      simp only [machine, step, ↓reduceIte]⟩) [] le_rfl
  have h₀' (out : List Bool) : S.machine.next (frame w) ⟨(0, 0, w.length), out⟩ =
      ⟨(1, w.length, 0), out ++ S.countEnd⟩ := by
    rw [hstep _ _ rfl, readBit_count]
    simp [step]
  -- the chunks
  have h₁ (out : List Bool) := S.machine.runFrom_loop (frame w) (fun j => (1, w.length, j))
    (S.chunk w.length) (M := S.numChunks w.length) (fun j hj => ⟨rfl, by
      change S.step (1, w.length, j) (S.machine.readBit (frame w) (1, w.length, j)) = _
      simp only [step, ↓reduceIte, hj, one_ne_zero]⟩) out le_rfl
  have h₁' (out : List Bool) : S.machine.next (frame w)
      ⟨(1, w.length, S.numChunks w.length), out⟩ =
      ⟨(2, w.length, 0), out ++ S.trailer w.length⟩ := by
    rw [hstep _ _ rfl]
    simp [step]
  -- copying
  have h₂ (out : List Bool) := S.machine.runFrom_loop (frame w) (fun i => (2, w.length, i))
    (fun i => S.copyBit (w.getD i false)) (M := w.length) (fun i hi => ⟨rfl, by
      rw [readBit_copy]
      change S.step (2, w.length, i) (w.getD i false) = _
      simp only [step, OfNat.ofNat_ne_zero, ↓reduceIte, hi, OfNat.ofNat_ne_one]⟩) out le_rfl
  have h₂' (out : List Bool) : S.machine.next (frame w) ⟨(2, w.length, w.length), out⟩ =
      ⟨(3, w.length, 0), out⟩ := by
    rw [hstep _ _ rfl]
    simp [step]
  set out₁ := [] ++ ((List.range w.length).map fun _ => S.countUnit).flatten ++ S.countEnd
  set out₂ := out₁ ++ ((List.range (S.numChunks w.length)).map (S.chunk w.length)).flatten ++
    S.trailer w.length
  have hA : S.machine.runFrom (frame w) ⟨(0, 0, 0), []⟩ (w.length + 1) =
      ⟨(1, w.length, 0), out₁⟩ := by
    rw [ReadMachine.runFrom_add, h₀, ReadMachine.runFrom_one, h₀']
  have hB : S.machine.runFrom (frame w) ⟨(1, w.length, 0), out₁⟩
      (S.numChunks w.length + 1) = ⟨(2, w.length, 0), out₂⟩ := by
    rw [ReadMachine.runFrom_add, h₁, ReadMachine.runFrom_one, h₁']
  have hC : S.machine.runFrom (frame w) ⟨(2, w.length, 0), out₂⟩ (w.length + 1) =
      ⟨(3, w.length, 0),
        out₂ ++ ((List.range w.length).map fun i => S.copyBit (w.getD i false)).flatten⟩ := by
    rw [ReadMachine.runFrom_add, h₂, ReadMachine.runFrom_one, h₂']
  rw [ReadMachine.run, rounds, show S.machine.init = (0, 0, 0) from rfl,
    S.machine.runFrom_add (frame w) _ (w.length + 1 + (S.numChunks w.length + 1)) (w.length + 1),
    S.machine.runFrom_add (frame w) _ (w.length + 1) (S.numChunks w.length + 1), hA, hB, hC,
    flatten_map_range_getD]
  simp [out₂, out₁, output, List.map_const']

/-- The states of the writer along its run. -/
private theorem wInv_run (w : List Bool) (j : ℕ) :
    WInv w.length (S.numChunks w.length) (S.machine.run (frame w) j).state := by
  induction j with
  | zero => exact Or.inl ⟨rfl, rfl, Nat.zero_le _⟩
  | succ j ih =>
    rw [ReadMachine.run, ReadMachine.runFrom, Function.iterate_succ_apply', ← ReadMachine.runFrom,
      ← ReadMachine.run]
    generalize S.machine.run (frame w) j = cfg at ih ⊢
    obtain ⟨⟨ph, nn, i⟩, out⟩ := cfg
    simp only [WInv] at ih
    rcases ih with ⟨rfl, rfl, hi⟩ | ⟨rfl, rfl, hi⟩ | ⟨rfl, rfl, hi⟩ | ⟨rfl, rfl, rfl⟩
    · rw [ReadMachine.next_of_not_halt _ _ rfl, readBit_count]
      change WInv _ _ (S.step (0, 0, i) (decide (i < w.length))).1
      rcases Nat.lt_or_ge i w.length with h | h
      · simp only [decide_eq_true h, step, ↓reduceIte]
        exact Or.inl ⟨rfl, rfl, h⟩
      · simp only [decide_eq_false (Nat.not_lt.2 h), step, ↓reduceIte, Bool.false_eq_true]
        exact Or.inr (Or.inl ⟨rfl, by simp only; omega, Nat.zero_le _⟩)
    · rw [ReadMachine.next_of_not_halt _ _ rfl]
      change WInv _ _ (S.step (1, w.length, i) (S.machine.readBit (frame w) (1, w.length, i))).1
      rcases Nat.lt_or_ge i (S.numChunks w.length) with h | h
      · simp only [step, one_ne_zero, ↓reduceIte, h]
        exact Or.inr (Or.inl ⟨rfl, rfl, h⟩)
      · simp only [step, one_ne_zero, ↓reduceIte, Nat.not_lt.2 h]
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Nat.zero_le _⟩))
    · rw [ReadMachine.next_of_not_halt _ _ rfl]
      change WInv _ _ (S.step (2, w.length, i) (S.machine.readBit (frame w) (2, w.length, i))).1
      rcases Nat.lt_or_ge i w.length with h | h
      · simp only [step, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, h]
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h⟩))
      · simp only [step, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, Nat.not_lt.2 h]
        exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
    · rw [show S.machine.next (frame w) ⟨(3, w.length, 0), out⟩ =
        ⟨(3, w.length, 0), out⟩ by simp [ReadMachine.next, machine]]
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))

/-! ### Logarithmic space -/

section Space

/-- The step input of the writer and its budget. -/
abbrev encStepIn : (ℕ × ℕ × ℕ) × Bool ↪ List Bool := encPair encWState encBool

/-- The halting test of the writer, within the budget of its states. -/
private theorem halt_inSpace :
    ComputableTidilyInSpace S.machine.halt encWState encBool wBudget := by
  have hin : (fun s => (encWState s).length) ≼ wBudget := .of_le fun _ => by
    simp only [wBudget]; omega
  have hph := (ComputableTidilyInSpace.fst encNat (encPair encNat encNat)).weaken hin
  exact budget_natEq hph (budget_const (encB := encNat) 3 hin)

variable {S}

/-- **The step of the writer**, within the budget of its states, when the number of chunks, the
chunks and the trailer are. -/
private theorem step_inSpace
    (hN : ComputableTidilyInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.numChunks p.1.2.1) encStepIn
      encNat fun p => wBudget p.1)
    (hC : ComputableTidilyInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.chunk p.1.2.1 p.1.2.2)
      encStepIn encBits fun p => wBudget p.1)
    (hT : ComputableTidilyInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.trailer p.1.2.1) encStepIn
      encBits fun p => wBudget p.1) :
    ComputableTidilyInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.step p.1 p.2) encStepIn
      (encPair encWState encBits) fun p => wBudget p.1 := by
  have hin : (fun p => (encStepIn p).length) ≼ fun p => wBudget p.1 :=
    .of_le_linear 2 0 fun p => by
      simp only [length_encPair, encBool_apply, wBudget]
      simp only [encNat_apply, List.length_cons, List.length_nil, zero_add, add_zero,
        Order.add_one_le_iff]
      omega
  have hs := (ComputableTidilyInSpace.fst encWState encBool).weaken hin
  have hb := (ComputableTidilyInSpace.snd encWState encBool).weaken hin
  have hph := fst' hs
  have hn := fst' (snd' hs)
  have hi := snd' (snd' hs)
  have hst {a b c : (ℕ × ℕ × ℕ) × Bool → ℕ}
      (ha : ComputableTidilyInSpace a encStepIn encNat fun p => wBudget p.1)
      (hb : ComputableTidilyInSpace b encStepIn encNat fun p => wBudget p.1)
      (hc : ComputableTidilyInSpace c encStepIn encNat fun p => wBudget p.1) :
      ComputableTidilyInSpace (fun p => (a p, b p, c p)) encStepIn encWState
        fun p => wBudget p.1 :=
    budget_prod ha (budget_prod hb hc)
  have hc (m : ℕ) := budget_const (encB := encNat) m hin
  have hw (l : List Bool) := budget_const (encB := encBits) l hin
  have hsucc := budget_natAdd hi (hc 1)
  have hcopy := budget_finite (encC := encBits) S.copyBit hb
  refine (budget_ite (budget_natEq hph (hc 0))
    (budget_ite hb (budget_prod (hst (hc 0) (hc 0) hsucc) (hw S.countUnit))
      (budget_prod (hst (hc 1) hi (hc 0)) (hw S.countEnd)))
    (budget_ite (budget_natEq hph (hc 1))
      (budget_ite (budget_natLt hi hN) (budget_prod (hst (hc 1) hn hsucc) hC)
        (budget_prod (hst (hc 2) hn (hc 0)) hT))
      (budget_ite (budget_natEq hph (hc 2))
        (budget_ite (budget_natLt hi hn) (budget_prod (hst (hc 2) hn hsucc) hcopy)
          (budget_prod (hst (hc 3) hn (hc 0)) (hw [])))
        (budget_prod hs (hw []))))).of_enc_eq fun p => ?_
  simp only [step, decide_eq_true_eq]

private theorem tidy_machine
    (hN : ComputableTidilyInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.numChunks p.1.2.1) encStepIn
      encNat fun p => wBudget p.1)
    (hC : ComputableTidilyInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.chunk p.1.2.1 p.1.2.2)
      encStepIn encBits fun p => wBudget p.1)
    (hT : ComputableTidilyInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.trailer p.1.2.1) encStepIn
      encBits fun p => wBudget p.1) :
    ∃ T, S.machine.toStepMachine.Tidy (encPair encWState encNat)
      (ReadMachine.stateT encWState T wBudget) (ReadMachine.stateS encWState wBudget) := by
  obtain ⟨T₁, h₁⟩ := S.halt_inSpace
  obtain ⟨T₂, h₂⟩ := writerAddr_inSpace
  obtain ⟨T₃, h₃⟩ := step_inSpace hN hC hT
  let T : ℕ × ℕ × ℕ → ℕ := fun s => T₁ s + T₂ s + T₃ (s, false) + T₃ (s, true)
  exact ⟨T, ReadMachine.tidy_toStepMachine
    (h₁.mono_le (fun s => by simp only [T]; omega) fun _ => le_rfl)
    (h₂.mono_le (fun s => by simp only [T]; omega) fun _ => le_rfl)
    (h₃.mono_le (fun p => by rcases p with ⟨s, _ | _⟩ <;> simp only [T] <;> omega)
      fun _ => le_rfl)⟩

variable (S) in
private theorem stateS_le (w : List Bool) {q : (ℕ × ℕ × ℕ) × ℕ}
    (hq : WInv w.length (S.numChunks w.length) q.1) (hpos : q.2 ≤ (frame w).length + 1) :
    ReadMachine.stateS encWState wBudget q ≤
      30 * ((encNat (S.numChunks w.length + 3 * w.length + 5)).length + 1) := by
  obtain ⟨h₁, h₂, h₃⟩ := le_of_wInv hq
  rw [length_frame] at hpos
  have hm (a : ℕ) (ha : a ≤ S.numChunks w.length + 3 * w.length + 5) :
      (encNat a).length ≤ (encNat (S.numChunks w.length + 3 * w.length + 5)).length :=
    ComputableTidilyInO.length_encNat_mono ha
  have e₁ := hm q.1.1 (by omega)
  have e₂ := hm q.1.2.1 (by omega)
  have e₃ := hm q.1.2.2 (by omega)
  have e₄ := hm q.2 (by omega)
  simp only [ReadMachine.stateS, wBudget, length_encPair]
  omega

/-- **A writer runs in logarithmic space** when it has polynomially many chunks and its chunks
and trailer are computed within the budget of its states. -/
theorem computableInLogSpace {β : Type} {encOut : β ↪ List Bool} {g : List Bool → β}
    (hg : ∀ w, encOut (g w) = S.output w)
    (hN : ComputableInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.numChunks p.1.2.1) encStepIn
      encNat fun p => wBudget p.1)
    (hC : ComputableInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.chunk p.1.2.1 p.1.2.2)
      encStepIn encBits fun p => wBudget p.1)
    (hT : ComputableInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.trailer p.1.2.1) encStepIn
      encBits fun p => wBudget p.1)
    (hpoly : PolynomiallyBounded S.numChunks) :
    ComputableInLogSpace g (encFramed encBits) encOut := by
  have hN : ComputableTidilyInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.numChunks p.1.2.1) encStepIn
      encNat fun p => wBudget p.1 := by simpa only [computableInSpace_iff_computableTidilyInSpace]
    using hN
  have hC : ComputableTidilyInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.chunk p.1.2.1 p.1.2.2)
      encStepIn encBits fun p => wBudget p.1 := by simpa only
    [computableInSpace_iff_computableTidilyInSpace] using hC
  have hT : ComputableTidilyInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => S.trailer p.1.2.1) encStepIn
      encBits fun p => wBudget p.1 := by simpa only [computableInSpace_iff_computableTidilyInSpace]
    using hT
  obtain ⟨T, hT'⟩ := tidy_machine hN hC hT
  have hc (w : List Bool) : S.machine.toStepMachine.Computes (encFramed encBits w)
      (encOut (g w)) := by
    have hrun := S.run_machine w
    have := ReadMachine.computes_toStepMachine (m := S.machine) (x := frame w)
      (n := S.rounds w.length) (by rw [hrun]; rfl)
    rwa [hrun, ← hg] at this
  choose rounds hr ho using hc
  have hpoly' : PolynomiallyBounded fun n => S.numChunks n + 3 * n + 5 := by fun_prop
  obtain ⟨A, D, hAD⟩ := polynomiallyBounded_iff_le.1 hpoly'
  let tS := ReadMachine.stateT encWState T wBudget
  let tMax (w : List Bool) : ℕ := ∑ i ∈ Finset.range (rounds w + 1),
    tS (S.machine.toStepMachine.run (encFramed encBits w) i).state
  have hbig := hT'.computableTidilyInTimeAndSpace g rounds hr (fun w => (ho w).symm)
    (tMax := tMax)
    (sMax := fun w => 30 * ((encNat (S.numChunks w.length + 3 * w.length + 5)).length + 1))
    fun w i hi => ⟨Finset.single_le_sum (f := fun i => tS (S.machine.toStepMachine.run
      (encFramed encBits w) i).state) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega)),
      by
        obtain ⟨j, hq, hpos⟩ := ReadMachine.exists_state_run (m := S.machine)
          (encFramed encBits w) i
        rw [hq]
        exact S.stateS_le w (S.wInv_run w j) (by simpa using hpos)⟩
  obtain ⟨c, hc⟩ := hbig
  refine ⟨_, c * (31 * (Nat.size A + 2 * D + 2)), hc.computableInTimeAndSpace.mono
    (fun _ => le_rfl) fun w => ?_⟩
  have hM : S.numChunks w.length + 3 * w.length + 5 ≤
      A * ((encFramed encBits w).length + 1) ^ D :=
    (hAD w.length).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
      simp only [encFramed_apply, encBits_apply, length_frame]; omega) D))
  have hl := length_encNat_le_of_le_mul_pow hM
  have hX : 1 ≤ Nat.log2 (encFramed encBits w).length + 1 := by omega
  beta_reduce
  generalize Nat.log2 (encFramed encBits w).length + 1 = X at hl hX ⊢
  generalize (encNat (S.numChunks w.length + 3 * w.length + 5)).length = L at hl ⊢
  generalize Nat.size A + 2 * D = B at hl ⊢
  rw [Nat.mul_assoc]
  refine Nat.mul_le_mul_left c ?_
  nlinarith

end Space

end WriterSpec

end Cslib.Complexity.CircuitValue
