/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Program

/-!
# Initialized flat programs with a fixed register layout

Choose the frontier, input bank and fresh scratch bank once, before every runtime width and
argument. Clients supply the same encoded-input, fit, domain and memory-history premises as
`Realizes.exists_init_program`, without proving register-placement conditions themselves.
The real `Data.init` prefix, native body and trailing halt are all charged. Its positive
next-free address must fit even for an empty input; this is not a width-zero initialization.

## Main results

* `Realizes.exists_standard_init_program_state_from_words`: one flat program for independent
  raw memory and register arguments, related by their input prefix.
* `Realizes.exists_standard_init_program_state`: the argument-indexed specialization, retaining
  the exact whole-memory, frontier and all encoded result words at its fixed halting location.
* `Realizes.exists_standard_init_program`: the scalar `Executes` projection of that same run.

The observed coordinate is static, as in the existing scalar export. Zero-output Unit clients
continue to use the separate charged Unit-observation API.

## References

This is original infrastructure over the existing realization certificate, charged input prefix
and native `Code.program` compiler. It introduces no execution model or client language.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

private abbrev registers (k l n : ℕ) : ℕ := 1 + (k + (l + n + 1))

private def standardFrontier {k l n : ℕ} : Fin (registers k l n) :=
  ⟨0, by unfold registers; omega⟩

private def standardInput {k l n : ℕ} (i : Fin k) : Fin (registers k l n) :=
  Fin.natAdd 1 (Fin.castAdd (l + n + 1) i)

private def standardScratch {k l n : ℕ} (i : Fin (l + n + 1)) : Fin (registers k l n) :=
  Fin.natAdd 1 (Fin.natAdd k i)

private theorem standardPlacement (k l n : ℕ) :
    Function.Injective (standardInput (k := k) (l := l) (n := n)) ∧
    Function.Injective (standardScratch (k := k) (l := l) (n := n)) ∧
    (∀ i j, standardInput (l := l) (n := n) i ≠ standardScratch (k := k) j) ∧
    (∀ j, standardScratch (k := k) (l := l) (n := n) j ≠ standardFrontier) ∧
    (∀ i, standardInput (k := k) (l := l) (n := n) i ≠ standardFrontier) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    simpa only [standardInput, Fin.val_natAdd, Fin.val_castAdd,
      Nat.add_left_cancel_iff] using this
  · intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    simp only [standardScratch, Fin.val_natAdd] at this
    omega
  · intro i j h
    have := congrArg Fin.val h
    simp only [standardInput, standardScratch, Fin.val_natAdd, Fin.val_castAdd] at this
    have := i.isLt
    omega
  · intro i h
    have := congrArg Fin.val h
    simp only [standardScratch, standardFrontier, Fin.val_natAdd] at this
    omega
  · intro i h
    have := congrArg Fin.val h
    simp only [standardInput, standardFrontier, Fin.val_natAdd, Fin.val_castAdd] at this
    omega

namespace Realizes

variable {k l : ℕ} {δ α : Type} {p : δ → Memory.Prog α}
  {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
  {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}

/-- One statically laid-out flat program includes charged input installation and its halt.
The witnessed native state is the actual final state of the flat run, retaining the entire
source memory and frontier and every result coordinate. The raw input words vary independently
of the register-encoded argument: only their input prefix must agree. All witnesses precede
both kinds of runtime data. -/
theorem exists_standard_init_program_state_from_words
    (h : Realizes .exact p input output safe work) (i : Fin l) :
    ∃ r C pc : ℕ, ∃ prog : Program .exact r,
      ∃ frontier : Fin r, ∃ out : Fin l → Fin r,
      ∀ w d words, (∀ j : Fin k, words.getD j.val 0 = input d j) →
        k ≤ words.length → Fits w (words.length + 1) → InputFits w words →
        safe w d (inputState words) →
        (Memory.spec w).ValidHistory (inputState words)
          ((Memory.spec w).clientHistory (inputState words) (p d)) →
        ∃ y n, Runs w prog (State.init words) ⟨pc, y⟩ n ∧
          step w prog ⟨pc, y⟩ =
            .halt (output ((Memory.spec w).clientResult (inputState words) (p d)) i) ∧
          memoryState frontier y = (Memory.spec w).clientState (inputState words) (p d) ∧
          (∀ j, y.regs (out j) =
            output ((Memory.spec w).clientResult (inputState words) (p d)) j) ∧
          n + 1 ≤ C * (memoryCost (p d) (inputState words) +
            work d (inputState words) + 1) + 1 := by
  obtain ⟨n, C, emit, he⟩ := h
  let r := registers k l n
  let frontier : Fin r := standardFrontier
  let src : Fin k → Fin r := standardInput
  let tmp : Fin (l + n + 1) → Fin r := standardScratch
  obtain ⟨hsrc, htmp, hd, hf, hs⟩ := standardPlacement k l n
  let code := Code.seq (inputPrefix frontier (tmp (Fin.last (l + n))) src)
    (emit frontier src tmp)
  let prog := code.program (tmp (Fin.castAdd (n + 1) i))
  refine ⟨r, C + (2 * k + 5), code.size, prog, frontier,
    (fun j => tmp (Fin.castAdd (n + 1) j)), ?_⟩
  intro w d words hlayout hk hw hin hsafe hv
  obtain ⟨x, ex, hx, hm, hwords, _⟩ := inputPrefix_exec frontier (tmp (Fin.last (l + n)))
    src words hsrc (hf _) (fun j => hd j _) hs hk hw hin
  have harg : x.regs ∘ src = input d := by
    funext j
    exact (hwords j).trans (hlayout j)
  obtain ⟨y, ey, hmem, hout, _⟩ := (he frontier src tmp htmp hd hf hs).2 w d x hx harg
    (hm.symm ▸ hsafe) (hm.symm ▸ hv)
  rw [hm] at ey hmem hout
  obtain ⟨steps, hsteps, erun⟩ := ex.seq ey
  have hr := erun.runs (pc := 0) (p := prog) (Program.Contains.self _).append_left
  refine ⟨y, steps, ?_, ?_, hmem, hout, ?_⟩
  · simpa only [Nat.zero_add, State.init, code] using hr
  · rw [← hout i]
    exact step_halt (by simp [prog, Code.program])
  · have hpos : 1 ≤ memoryCost (p d) (inputState words) +
        work d (inputState words) + 1 := by omega
    have hover := Nat.mul_le_mul_left (2 * k + 5) hpos
    simp only [Nat.mul_one] at hover
    rw [Nat.add_mul]
    omega

/-- One statically laid-out flat program includes charged input installation and its halt.
The witnessed native state is the actual final state of the flat run, retaining the entire
source memory and frontier and every result coordinate. All witnesses precede runtime data. -/
theorem exists_standard_init_program_state (h : Realizes .exact p input output safe work)
    (raw : δ → List ℕ) (hlayout : ∀ d (i : Fin k), (raw d).getD i.val 0 = input d i)
    (i : Fin l) :
    ∃ r C pc : ℕ, ∃ prog : Program .exact r,
      ∃ frontier : Fin r, ∃ out : Fin l → Fin r,
      ∀ w d, k ≤ (raw d).length → Fits w ((raw d).length + 1) → InputFits w (raw d) →
        safe w d (inputState (raw d)) →
        (Memory.spec w).ValidHistory (inputState (raw d))
          ((Memory.spec w).clientHistory (inputState (raw d)) (p d)) →
        ∃ y n, Runs w prog (State.init (raw d)) ⟨pc, y⟩ n ∧
          step w prog ⟨pc, y⟩ =
            .halt (output ((Memory.spec w).clientResult (inputState (raw d)) (p d)) i) ∧
          memoryState frontier y = (Memory.spec w).clientState (inputState (raw d)) (p d) ∧
          (∀ j, y.regs (out j) =
            output ((Memory.spec w).clientResult (inputState (raw d)) (p d)) j) ∧
          n + 1 ≤ C * (memoryCost (p d) (inputState (raw d)) +
            work d (inputState (raw d)) + 1) + 1 := by
  obtain ⟨r, C, pc, prog, frontier, out, he⟩ :=
    h.exists_standard_init_program_state_from_words i
  exact ⟨r, C, pc, prog, frontier, out, fun w d => he w d (raw d) (hlayout d)⟩

/-- The canonical initialized export requires no caller-written register layout. Its bound
includes the actual prefix, body and final halt, with code fixed before every width and input. -/
theorem exists_standard_init_program (h : Realizes .exact p input output safe work)
    (raw : δ → List ℕ) (hlayout : ∀ d (i : Fin k), (raw d).getD i.val 0 = input d i)
    (i : Fin l) :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ w d, k ≤ (raw d).length → Fits w ((raw d).length + 1) → InputFits w (raw d) →
        safe w d (inputState (raw d)) →
        (Memory.spec w).ValidHistory (inputState (raw d))
          ((Memory.spec w).clientHistory (inputState (raw d)) (p d)) →
        ∃ t, Executes w prog (State.init (raw d))
            (output ((Memory.spec w).clientResult (inputState (raw d)) (p d)) i) t ∧
          t ≤ C * (memoryCost (p d) (inputState (raw d)) +
            work d (inputState (raw d)) + 1) + 1 := by
  obtain ⟨r, C, pc, prog, _, _, he⟩ := h.exists_standard_init_program_state raw hlayout i
  refine ⟨r, C, prog, ?_⟩
  intro w d hk hw hin hsafe hv
  obtain ⟨y, n, hr, hh, _, _, hn⟩ := he w d hk hw hin hsafe hv
  exact ⟨n + 1, ⟨⟨pc, y⟩, n, hr, hh, rfl⟩, hn⟩

end Realizes
end Cslib.WordRAM.Realization
