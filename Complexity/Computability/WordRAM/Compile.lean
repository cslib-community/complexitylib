/-
Copyright (c) 2026 lean-trominoes contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate (based on edemaine/lean-trominoes @6d5b36c1)

public import Complexity.Computability.WordRAM.Structured
public import Complexity.Computability.WordRAM.Time

/-!
# Compiling structured word-RAM programs

A structured program (`Cslib.WordRAM.Code`) assembles into a flat program
(`Cslib.WordRAM.Code.assemble`) whose conditionals and loops become branches and jumps to
absolute instruction indices:

* `branch c pos neg` at `pc` becomes a branch on `c` to `pos`, then `neg`, then a jump past `pos`;
* `loop c body` at `pc` becomes a branch on `c` to `body`, a jump past the loop, `body`, and a
  jump back to the branch.

Every structured execution is a run of the assembled program with exactly the same number of
instructions (`Cslib.WordRAM.Exec.runs`). A complete program ends with a `halt`
(`Cslib.WordRAM.Code.program`), so a structured proof that a program answers a question
(`Cslib.WordRAM.Code.Answers`) gives a flat program that answers it with one more instruction
(`Cslib.WordRAM.Code.Answers.program`), and a uniform decision procedure
(`Cslib.WordRAM.Code.decidesInTime_program`, `Cslib.WordRAM.UniformDecidableInTime.of_code`).

## Main definitions

* `Cslib.WordRAM.Code.assemble`, `Cslib.WordRAM.Code.program`: assembly at a given position, and
  the complete program halting with a given register.
* `Cslib.WordRAM.Program.Contains`: a program contains another at a given position.
* `Cslib.WordRAM.Code.Answers`: a structured program answers a question in a register.

## Main results

* `Cslib.WordRAM.Exec.runs`: structured executions are runs of the assembled program with the
  same instruction count.
* `Cslib.WordRAM.Exec.executes`: a structured execution followed by `halt` is a halting run.
* `Cslib.WordRAM.Code.decidesInTime_program`, `Cslib.WordRAM.UniformDecidableInTime.of_code`:
  structured decision procedures are uniform deciders. Width-indexed code with a uniform size bound
  gives `Cslib.WordRAM.DecidableInTime.of_code`.
* `Cslib.WordRAM.Code.not_readsWidth_program`: a compiled program reads the word size only if the
  structured program does.

## References

* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]; the assembly
  and its exact-cost correctness are adapted from its accompanying Lean formalization.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ}

/-! ## Assembly -/

/-- Assemble a structured program to be placed at instruction index `pc`. -/
def Code.assemble : Code B r → ℕ → Program B r
  | .op o, _ => [.op o]
  | .seq c₁ c₂, pc => c₁.assemble pc ++ c₂.assemble (pc + c₁.size)
  | .branch c pos neg, pc =>
    .branch c (pc + neg.size + 2) :: neg.assemble (pc + 1) ++
      .jump (pc + neg.size + pos.size + 2) :: pos.assemble (pc + neg.size + 2)
  | .loop c body, pc =>
    .branch c (pc + 2) :: .jump (pc + body.size + 3) :: body.assemble (pc + 2) ++ [.jump pc]

@[simp]
theorem Code.length_assemble (c : Code B r) (pc : ℕ) : (c.assemble pc).length = c.size := by
  induction c generalizing pc with
  | branch _ _ _ ihp ihn =>
    simp only [Code.assemble, List.length_append, List.length_cons, ihp, ihn, Code.size]
    omega
  | _ => simp_all [Code.assemble]

/-- The complete program: the assembled structured program followed by `halt out`. -/
def Code.program (c : Code B r) (out : Fin r) : Program B r := c.assemble 0 ++ [.halt out]

/-- `p` contains the program `q` starting at instruction index `base`. -/
def Program.Contains (p : Program B r) (base : ℕ) (q : Program B r) : Prop :=
  ∃ pre post, p = pre ++ q ++ post ∧ pre.length = base

namespace Program.Contains

variable {p q q₁ q₂ : Program B r} {base : ℕ}

theorem self (p : Program B r) : p.Contains 0 p := ⟨[], [], by simp, rfl⟩

theorem append_left (h : p.Contains base (q₁ ++ q₂)) : p.Contains base q₁ :=
  let ⟨pre, post, hp, hl⟩ := h
  ⟨pre, q₂ ++ post, by simp [hp], hl⟩

theorem append_right (h : p.Contains base (q₁ ++ q₂)) : p.Contains (base + q₁.length) q₂ :=
  let ⟨pre, post, hp, hl⟩ := h
  ⟨pre ++ q₁, post, by simp [hp], by simp [hl]⟩

theorem cons_tail {i : Instr B r} (h : p.Contains base (i :: q)) : p.Contains (base + 1) q :=
  append_right (q₁ := [i]) h

theorem getElem? (h : p.Contains base q) {k : ℕ} (hk : k < q.length) :
    p[base + k]? = q[k]? := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk]

theorem head {i : Instr B r} (h : p.Contains base (i :: q)) : p[base]? = some i := by
  simpa using h.getElem? (k := 0) (by simp)

end Program.Contains

/-! ## Correctness of assembly -/

section Runs

variable {w : ℕ} {p : Program B r} {x : Data r} {pc : ℕ}

private theorem next_jump {t : ℕ} (h : p[pc]? = some (.jump t)) :
    Next w p ⟨pc, x⟩ ⟨t, x⟩ := step_jump h

private theorem next_branch_pos {c : Cond r} {t : ℕ} (h : p[pc]? = some (.branch c t))
    (hc : c.Holds x) : Next w p ⟨pc, x⟩ ⟨t, x⟩ := by
  simpa [Next, hc] using step_branch (w := w) (s := ⟨pc, x⟩) h

private theorem next_branch_neg {c : Cond r} {t : ℕ} (h : p[pc]? = some (.branch c t))
    (hc : ¬c.Holds x) : Next w p ⟨pc, x⟩ ⟨pc + 1, x⟩ := by
  simpa [Next, hc] using step_branch (w := w) (s := ⟨pc, x⟩) h

/-- **Assembly is correct.** A structured execution is a run of any program containing the
assembled structured program, from its first instruction to the instruction after it, with
exactly the same number of instructions. -/
theorem Exec.runs {c : Code B r} {y : Data r} {n : ℕ} (h : Exec w c x y n)
    (hp : p.Contains pc (c.assemble pc)) : Runs w p ⟨pc, x⟩ ⟨pc + c.size, y⟩ n := by
  induction h generalizing pc with
  | op ho =>
    exact .single (step_op (s := ⟨pc, _⟩) hp.head ho)
  | @seq c₁ c₂ x y z m n _ _ ih₁ ih₂ =>
    have h₁ := ih₁ hp.append_left
    have h₂ := ih₂ (pc := pc + c₁.size) (by simpa using hp.append_right)
    simpa [Code.size, Nat.add_assoc] using h₁.trans h₂
  | @branch_pos c pos neg x y n hc _ ih =>
    have hb := next_branch_pos (w := w) hp.head hc
    have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
    rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
    have hpos := ih hc'
    have := Relation.RelatesInSteps.head _ _ _ _ hb hpos
    simpa [Code.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  | @branch_neg c pos neg x y n hc _ ih =>
    have hb := next_branch_neg (w := w) hp.head hc
    have hneg := ih (pc := pc + 1) hp.cons_tail.append_left
    have hj : Next w p ⟨pc + 1 + neg.size, y⟩ ⟨pc + neg.size + pos.size + 2, y⟩ :=
      next_jump (by simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head)
    have := (Relation.RelatesInSteps.head _ _ _ _ hb hneg).tail _ _ _ _ hj
    simpa [Code.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  | @loop_exit c body x hc =>
    have hb := next_branch_neg (w := w) hp.head hc
    have hj : Next w p ⟨pc + 1, x⟩ ⟨pc + body.size + 3, x⟩ := next_jump hp.cons_tail.head
    simpa [Code.size, Nat.add_assoc] using (Relation.RelatesInSteps.single hb).tail _ _ _ _ hj
  | @loop_iter c body x y z m n hc _ _ ihb ihl =>
    have hb := next_branch_pos (w := w) hp.head hc
    have hbody := ihb (pc := pc + 2) (by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left)
    have hj : Next w p ⟨pc + 2 + body.size, y⟩ ⟨pc, y⟩ :=
      next_jump (by simpa using hp.cons_tail.cons_tail.append_right.head)
    have hrest := ihl hp
    have := ((Relation.RelatesInSteps.head _ _ _ _ hb hbody).tail _ _ _ _ hj).trans hrest
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- A structured execution followed by `halt out` is a halting run of the complete program, with
one more instruction. -/
theorem Exec.executes {c : Code B r} {y : Data r} {n : ℕ} (h : Exec w c x y n) (out : Fin r) :
    Executes w (c.program out) ⟨0, x⟩ (y.regs out) (n + 1) := by
  have hr := h.runs (pc := 0) (p := c.program out) (Program.Contains.self _).append_left
  have hh : step w (c.program out) ⟨0 + c.size, y⟩ = .halt (y.regs out) :=
    step_halt (by simp [Code.program])
  exact Executes.of_runs hr (Executes.halt hh)

end Runs

/-! ## Answering questions with structured programs -/

/-- The structured program `c`, run at word size `w` from the initial data on `input`, leaves
the answer to `b` in register `out` within `time` instructions: `1` if `b` holds and `0`
otherwise. -/
def Code.Answers (c : Code B r) (out : Fin r) (w : ℕ) (input : List ℕ) (b : Prop) (time : ℕ) :
    Prop :=
  ∃ y, ExecWithin w c (.init input) y time ∧ y.regs out ≤ 1 ∧ (y.regs out = 1 ↔ b)

/-- A structured program that answers a question gives a flat program that answers it, with one
more instruction for the final `halt`. -/
theorem Code.Answers.program {c : Code B r} {out : Fin r} {w : ℕ} {input : List ℕ} {b : Prop}
    {time : ℕ} (h : c.Answers out w input b time) : (c.program out).Answers w input b (time + 1) :=
  let ⟨y, ⟨n, hn, he⟩, hv⟩ := h
  ⟨y.regs out, n + 1, he.executes out, Nat.add_le_add_right hn 1, hv⟩

/-- Structured answers give a fixed-program decision certificate, charging the final halt. -/
theorem Code.decidesInTime_program {α : Type*} {encode : ℕ → α → List ℕ} {A : Set α}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} (c : Code B r) (out : Fin r)
    (h : ∀ a w, allowed a w → InputFits w (encode w a) →
      c.Answers out w (encode w a) (a ∈ A) (time a w)) :
    (c.program out).DecidesInTime encode A (fun a w => time a w + 1) allowed :=
  fun a w hw hi => (h a w hw hi).program

/-- Structured decision procedures are uniform deciders. -/
theorem UniformDecidableInTime.of_code {α : Type*} {encode : ℕ → α → List ℕ} {A : Set α}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} (c : Code B r) (out : Fin r)
    (h : ∀ a w, allowed a w → InputFits w (encode w a) →
      c.Answers out w (encode w a) (a ∈ A) (time a w)) :
    UniformDecidableInTime B A encode (fun a w => time a w + 1) allowed :=
  ⟨r, c.program out, c.decidesInTime_program out h⟩

/-- Structured families with bounded compiled code give nonuniform deciders. -/
theorem DecidableInTime.of_code {α : Type*} {encode : ℕ → α → List ℕ} {A : Set α}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop} (c : ℕ → Code B r) (out : Fin r)
    (hc : ∃ L, ∀ w, (c w).size ≤ L)
    (h : ∀ a w, allowed a w → InputFits w (encode w a) →
      (c w).Answers out w (encode w a) (a ∈ A) (time a w)) :
    DecidableInTime B A encode (fun a w => time a w + 1) allowed :=
  let ⟨L, hL⟩ := hc
  ⟨r, (fun w => (c w).program out), ⟨L + 1, fun w => by
    simpa only [Code.program, List.length_append, Code.length_assemble,
      List.length_cons, List.length_nil] using Nat.add_le_add_right (hL w) 1⟩,
    fun a w hw hi => (h a w hw hi).program⟩

/-! ## Reading the word size -/

/-- An assembled program reads the word size only if the structured program does. -/
private theorem Code.readsWidth_of_assemble {c : Code B r} {pc : ℕ}
    (h : (c.assemble pc).ReadsWidth) : c.ReadsWidth := by
  obtain ⟨i, hi, hr⟩ := h
  induction c generalizing pc with
  | op o =>
    simp only [Code.assemble, List.mem_singleton] at hi
    subst hi
    exact hr
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [Code.assemble, List.mem_append] at hi
    exact hi.elim (fun hi => .inl (ih₁ hi)) (fun hi => .inr (ih₂ hi))
  | branch c pos neg ihp ihn =>
    simp only [Code.assemble, List.mem_append, List.mem_cons] at hi
    rcases hi with (rfl | hi) | rfl | hi
    · exact (hr : False).elim
    · exact .inr (ihn hi)
    · exact (hr : False).elim
    · exact .inl (ihp hi)
  | loop c body ih =>
    simp only [Code.assemble, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | rfl | hi) | rfl
    · exact (hr : False).elim
    · exact (hr : False).elim
    · exact ih hi
    · exact (hr : False).elim

/-- A compiled program reads the word size only if the structured program does. -/
theorem Code.not_readsWidth_program {c : Code B r} (hc : ¬c.ReadsWidth) (out : Fin r) :
    ¬(c.program out).ReadsWidth := by
  rintro ⟨i, hi, hr⟩
  rcases List.mem_append.1 hi with hi | hi
  · exact hc (Code.readsWidth_of_assemble ⟨i, hi, hr⟩)
  · rw [List.mem_singleton] at hi
    subst hi
    exact (hr : False).elim

end Cslib.WordRAM

end
