/-
Copyright (c) 2026 lean-trominoes contributors, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate (based on edemaine/lean-trominoes @6d5b36c1)

public import Complexity.Computability.WordRAM.Defs
public import Mathlib.Logic.Function.Basic

/-!
# Structured word-RAM programs

Flat programs (`Cslib.WordRAM.Program`) are lists of instructions with numeric jump targets,
which is inconvenient to write and to reason about. A *structured program*
(`Cslib.WordRAM.Code`) is built from data instructions by sequencing, conditionals and while
loops on the comparisons of `Cslib.WordRAM.Cond`. It has a big-step semantics
(`Cslib.WordRAM.Exec`) that counts exactly the instructions of the flat program it compiles to
(`Cslib.WordRAM.Code.assemble`, `Cslib.WordRAM.Exec.runs`): a conditional costs one branch
instruction, plus a jump when the second alternative runs, and a loop costs a branch and a jump
per test. No rule executes a Lean function as one instruction.

Proofs about structured programs mostly need upper bounds on time rather than exact counts,
and `Cslib.WordRAM.ExecWithin` packages these. Its rules compose like Hoare logic, with time
bounds added along sequences:

* `Cslib.WordRAM.ExecWithin.const`, `….alu`, `….copy`, `….load`, `….store`: forward rules for
  the data instructions, with the resulting data in closed form, and `….bin`, `….width` for the
  operations of the standard basis;
* `Cslib.WordRAM.ExecWithin.seq`, `….branch_pos`, `….branch_neg`: sequencing and conditionals;
* `Cslib.WordRAM.ExecWithin.loop`: a loop through an explicit family of states, and
  `Cslib.WordRAM.ExecWithin.loop_invariant`: a loop with an invariant and a decreasing measure,
  whose iterations are counted by the measure.

Loop-free code can instead be executed symbolically: `Cslib.WordRAM.Code.eval` is a structurally
recursive interpreter, so `simp` and `decide` evaluate it, and `Cslib.WordRAM.Exec.of_eval` turns
its result into an execution.

Subprograms are reused through `Cslib.WordRAM.Code.rename`, which runs a program on any
injectively chosen registers of a larger register file and leaves the others untouched
(`Cslib.WordRAM.Exec.rename`).

## Main definitions

* `Cslib.WordRAM.Code`, `Cslib.WordRAM.Code.size`, `Cslib.WordRAM.Code.ReadsWidth`: structured
  programs over a basis, the length of the flat program they compile to, and whether a program
  reads the word size.
* `Cslib.WordRAM.Exec`, `Cslib.WordRAM.ExecWithin`: executions with an exact instruction count,
  and within a time bound.
* `Cslib.WordRAM.Code.evalLoop`, `Cslib.WordRAM.Code.eval`: an interpreter with a budget of loop
  iterations.
* `Cslib.WordRAM.Op.dest`, `Cslib.WordRAM.Code.Preserves`: written register of a data instruction
  and register preservation predicate.
* `Cslib.WordRAM.Data.comap`, `Cslib.WordRAM.Data.extend`, `Cslib.WordRAM.Op.rename`,
  `Cslib.WordRAM.Cond.rename`, `Cslib.WordRAM.Code.rename`: running a program on other registers.

## Main results

* `Cslib.WordRAM.Exec.unique`: executions are deterministic.
* `Cslib.WordRAM.Exec.of_eval`: the interpreter only finds executions.
* `Cslib.WordRAM.ExecWithin.loop_invariant`: the loop rule with an invariant and a measure.
* `Cslib.WordRAM.Exec.regs_eq`: registers that a program never writes keep their contents.
* `Cslib.WordRAM.Exec.rename`: renamed programs run on the chosen registers.
* `Cslib.WordRAM.Exec.mono_width`, `Cslib.WordRAM.Exec.bounded`: a program that does not read the
  word size runs in the same way at every larger word size, and executions keep data word-sized.

## References

* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]; the
  structured programs, their cost-exact semantics, register preservation and register embedding
  are adapted from its accompanying Lean formalization.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r r' : ℕ}

/-! ## Structured programs -/

/-- Structured programs: data instructions combined by sequencing, conditionals and loops. -/
inductive Code (B : Basis) (r : ℕ) where
  /-- A data instruction. -/
  | op (o : Op B r)
  /-- Run `c₁`, then `c₂`. -/
  | seq (c₁ c₂ : Code B r)
  /-- Run `pos` if `c` holds, and `neg` otherwise. -/
  | branch (c : Cond r) (pos neg : Code B r)
  /-- Run `body` while `c` holds. -/
  | loop (c : Cond r) (body : Code B r)
  deriving DecidableEq

namespace Code

/-- The length of the flat program a structured program compiles to. -/
@[simp]
def size : Code B r → ℕ
  | .op _ => 1
  | .seq c₁ c₂ => c₁.size + c₂.size
  | .branch _ pos neg => neg.size + pos.size + 2
  | .loop _ body => body.size + 3

/-- A structured program reads the word size if one of its instructions does. -/
def ReadsWidth : Code B r → Prop
  | .op o => o.ReadsWidth
  | .seq c₁ c₂ => c₁.ReadsWidth ∨ c₂.ReadsWidth
  | .branch _ pos neg => pos.ReadsWidth ∨ neg.ReadsWidth
  | .loop _ body => body.ReadsWidth

/-- Decidability of whether a structured program reads the word size. -/
instance decidableReadsWidth : (c : Code B r) → Decidable c.ReadsWidth
  | .op o => inferInstanceAs (Decidable o.ReadsWidth)
  | .seq c₁ c₂ =>
    have := c₁.decidableReadsWidth
    have := c₂.decidableReadsWidth
    inferInstanceAs (Decidable (_ ∨ _))
  | .branch _ pos neg =>
    have := pos.decidableReadsWidth
    have := neg.decidableReadsWidth
    inferInstanceAs (Decidable (_ ∨ _))
  | .loop _ body => body.decidableReadsWidth

end Code

/-! ## Executions -/

/-- `Exec w c x y n`: at word size `w`, the structured program `c` leads from data `x` to data `y`
executing exactly `n` instructions of the flat program it compiles to. -/
inductive Exec (w : ℕ) : Code B r → Data r → Data r → ℕ → Prop where
  /-- A data instruction is one instruction. -/
  | op {o : Op B r} {x y : Data r} : o.eval w x = some y → Exec w (.op o) x y 1
  /-- Sequencing adds the instruction counts. -/
  | seq {c₁ c₂ : Code B r} {x y z : Data r} {m n : ℕ} :
      Exec w c₁ x y m → Exec w c₂ y z n → Exec w (.seq c₁ c₂) x z (m + n)
  /-- The first alternative of a conditional costs one branch instruction. -/
  | branch_pos {c : Cond r} {pos neg : Code B r} {x y : Data r} {n : ℕ} :
      c.Holds x → Exec w pos x y n → Exec w (.branch c pos neg) x y (n + 1)
  /-- The second alternative of a conditional costs a branch and a jump. -/
  | branch_neg {c : Cond r} {pos neg : Code B r} {x y : Data r} {n : ℕ} :
      ¬c.Holds x → Exec w neg x y n → Exec w (.branch c pos neg) x y (n + 2)
  /-- Leaving a loop costs a branch and a jump. -/
  | loop_exit {c : Cond r} {body : Code B r} {x : Data r} :
      ¬c.Holds x → Exec w (.loop c body) x x 2
  /-- An iteration of a loop costs its body, a branch and a jump back. -/
  | loop_iter {c : Cond r} {body : Code B r} {x y z : Data r} {m n : ℕ} :
      c.Holds x → Exec w body x y m → Exec w (.loop c body) y z n →
      Exec w (.loop c body) x z (m + n + 2)

/-- `ExecWithin w c x y T`: at word size `w`, the structured program `c` leads from data `x` to
data `y` within `T` instructions. -/
def ExecWithin (w : ℕ) (c : Code B r) (x y : Data r) (T : ℕ) : Prop :=
  ∃ n ≤ T, Exec w c x y n

namespace Exec

variable {w : ℕ} {c c₁ c₂ : Code B r} {x y y' z : Data r} {n n' : ℕ}

/-- Executions are deterministic. -/
theorem unique (h : Exec w c x y n) (h' : Exec w c x y' n') : y = y' ∧ n = n' := by
  induction h generalizing y' n' with
  | op ho =>
    cases h' with
    | op ho' => rw [ho] at ho'; cases ho'; exact ⟨rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases h' with
    | seq h₁' h₂' =>
      obtain ⟨rfl, rfl⟩ := ih₁ h₁'
      obtain ⟨rfl, rfl⟩ := ih₂ h₂'
      exact ⟨rfl, rfl⟩
  | branch_pos hc _ ih =>
    cases h' with
    | branch_pos _ hp => obtain ⟨rfl, rfl⟩ := ih hp; exact ⟨rfl, rfl⟩
    | branch_neg hc' _ => exact absurd hc hc'
  | branch_neg hc _ ih =>
    cases h' with
    | branch_pos hc' _ => exact absurd hc' hc
    | branch_neg _ hn => obtain ⟨rfl, rfl⟩ := ih hn; exact ⟨rfl, rfl⟩
  | loop_exit hc =>
    cases h' with
    | loop_exit _ => exact ⟨rfl, rfl⟩
    | loop_iter hc' _ _ => exact absurd hc' hc
  | loop_iter hc _ _ ihb ihl =>
    cases h' with
    | loop_exit hc' => exact absurd hc hc'
    | loop_iter _ hb hl =>
      obtain ⟨rfl, rfl⟩ := ihb hb
      obtain ⟨rfl, rfl⟩ := ihl hl
      exact ⟨rfl, rfl⟩

/-- An exact execution of `n` instructions is also an execution within `n` instructions. -/
theorem within (h : Exec w c x y n) : ExecWithin w c x y n := ⟨n, le_rfl, h⟩

/-! ### Data instructions

Each data instruction leads to explicitly given data in one instruction. Only constants and
operations need the written number to fit a word. -/

section Ops

variable {d a s : Fin r}

/-- Setting register `d` to a fitting constant `v` takes one instruction. -/
theorem const {v : ℕ} (h : Fits w v) :
    Exec (B := B) w (.op (.const d v)) x (x.set d v) 1 :=
  .op (Data.put_of_fits h)

/-- An ALU operation whose result `v` fits in a word takes one instruction. -/
theorem alu {f : B.Op} {args : Fin (B.Arity f) → Fin r} {v : ℕ}
    (hf : B.interp w f (x.regs ∘ args) = some v) (h : Fits w v) :
    Exec w (.op (.alu f d args)) x (x.set d v) 1 :=
  .op (by rw [Op.eval_alu, hf]; exact Data.put_of_fits h)

/-- Copying register `s` into register `d` takes one instruction. -/
theorem copy : Exec (B := B) w (.op (.copy d s)) x (x.set d (x.regs s)) 1 := .op rfl

/-- Loading the memory cell at register `a` into register `d` takes one instruction. -/
theorem load : Exec (B := B) w (.op (.load d a)) x (x.set d (x.mem (x.regs a))) 1 := .op rfl

/-- Storing register `s` into the memory cell at register `a` takes one instruction. -/
theorem store : Exec (B := B) w (.op (.store a s)) x (x.write (x.regs a) (x.regs s)) 1 :=
  .op rfl

end Ops

section Standard

variable {d i j : Fin r}

/-- A standard binary operation whose result fits in a word takes one instruction. -/
theorem bin {f : BinOp} (h : Fits w (f.eval (x.regs i) (x.regs j))) :
    Exec w (.op (.bin f d i j)) x (x.set d (f.eval (x.regs i) (x.regs j))) 1 :=
  .op (Data.put_of_fits h)

/-- Reading the word size `w` into register `d` takes one instruction. -/
theorem width : Exec w (.op (.width d)) x (x.set d w) 1 := .op (Op.eval_width w d x)

end Standard

/-- A loop whose condition holds initially and fails after one body execution runs in `m + 4`
instructions. -/
theorem loop_once {c : Cond r} {body : Code B r} {x y : Data r} {m : ℕ}
    (hc : c.Holds x) (h : Exec w body x y m) (hy : ¬c.Holds y) :
    Exec w (.loop c body) x y (m + 4) :=
  loop_iter hc h (loop_exit hy)

/-- A loop through the states `xs 0, …, xs k`: the condition holds at the first `k` of them and
fails at the last, and the body leads from each to the next in `T` instructions. -/
theorem loop {cond : Cond r} {body : Code B r} (xs : ℕ → Data r) (k T : ℕ)
    (hc : ∀ i < k, cond.Holds (xs i)) (hk : ¬cond.Holds (xs k))
    (hbody : ∀ i < k, Exec w body (xs i) (xs (i + 1)) T) :
    Exec w (.loop cond body) (xs 0) (xs k) (k * (T + 2) + 2) := by
  induction k generalizing xs with
  | zero => simpa using loop_exit hk
  | succ k ih =>
    have := loop_iter (hc 0 (by omega)) (hbody 0 (by omega))
      (ih (fun i => xs (i + 1)) (fun i hi => hc (i + 1) (by omega)) hk
        (fun i hi => hbody (i + 1) (by omega)))
    convert this using 1
    rw [Nat.succ_mul]
    omega

end Exec

/-! ## Time bounds -/

namespace ExecWithin

variable {w : ℕ} {c c₁ c₂ pos neg body : Code B r} {cond : Cond r} {x y z : Data r}
  {d i j a s : Fin r} {T T₁ T₂ : ℕ}

/-- Monotonicity of `ExecWithin` in the instruction budget. -/
theorem mono (h : ExecWithin w c x y T) (hT : T ≤ T₂) : ExecWithin w c x y T₂ :=
  let ⟨n, hn, he⟩ := h
  ⟨n, hn.trans hT, he⟩

/-- A single data instruction executes within one instruction. -/
theorem op {o : Op B r} (h : o.eval w x = some y) : ExecWithin w (.op o) x y 1 := (Exec.op h).within

/-- Sequencing adds the instruction bounds of the two subprograms. -/
theorem seq (h₁ : ExecWithin w c₁ x y T₁) (h₂ : ExecWithin w c₂ y z T₂) :
    ExecWithin w (.seq c₁ c₂) x z (T₁ + T₂) :=
  let ⟨m, hm, he₁⟩ := h₁
  let ⟨n, hn, he₂⟩ := h₂
  ⟨m + n, Nat.add_le_add hm hn, .seq he₁ he₂⟩

/-- Taking the positive branch of a conditional adds one instruction to the bound. -/
theorem branch_pos (hc : cond.Holds x) (h : ExecWithin w pos x y T) :
    ExecWithin w (.branch cond pos neg) x y (T + 1) :=
  let ⟨n, hn, he⟩ := h
  ⟨n + 1, Nat.add_le_add_right hn 1, .branch_pos hc he⟩

/-- Taking the negative branch of a conditional adds two instructions to the bound. -/
theorem branch_neg (hc : ¬cond.Holds x) (h : ExecWithin w neg x y T) :
    ExecWithin w (.branch cond pos neg) x y (T + 2) :=
  let ⟨n, hn, he⟩ := h
  ⟨n + 2, Nat.add_le_add_right hn 2, .branch_neg hc he⟩

/-- A conditional, with one time bound for both alternatives. -/
theorem branch (hpos : cond.Holds x → ExecWithin w pos x y T)
    (hneg : ¬cond.Holds x → ExecWithin w neg x y T) :
    ExecWithin w (.branch cond pos neg) x y (T + 2) := by
  by_cases hc : cond.Holds x
  · exact (branch_pos hc (hpos hc)).mono (by omega)
  · exact branch_neg hc (hneg hc)

/-- Exiting a loop when the condition fails takes at most two instructions. -/
theorem loop_exit (hc : ¬cond.Holds x) : ExecWithin w (.loop cond body) x x 2 :=
  (Exec.loop_exit hc).within

/-- One loop iteration followed by the rest of the loop adds `T₁ + 2` instructions to the bound. -/
theorem loop_iter (hc : cond.Holds x) (h₁ : ExecWithin w body x y T₁)
    (h₂ : ExecWithin w (.loop cond body) y z T₂) :
    ExecWithin w (.loop cond body) x z (T₁ + T₂ + 2) :=
  let ⟨m, hm, he₁⟩ := h₁
  let ⟨n, hn, he₂⟩ := h₂
  ⟨m + n + 2, by omega, .loop_iter hc he₁ he₂⟩

/-- A loop whose condition holds initially and fails after one body execution runs within `T + 4`
instructions. -/
theorem loop_once (hc : cond.Holds x) (h : ExecWithin w body x y T) (hy : ¬cond.Holds y) :
    ExecWithin w (.loop cond body) x y (T + 4) :=
  loop_iter hc h (loop_exit hy)

/-- **Loop rule, explicit states.** If the condition holds at `xs 0, …, xs (k - 1)` and fails at
`xs k`, and the body leads from each state to the next within `T` instructions, the loop leads
from `xs 0` to `xs k` within `k (T + 2) + 2` instructions. -/
theorem loop (xs : ℕ → Data r) (k T : ℕ) (hc : ∀ i < k, cond.Holds (xs i))
    (hk : ¬cond.Holds (xs k)) (hbody : ∀ i < k, ExecWithin w body (xs i) (xs (i + 1)) T) :
    ExecWithin w (.loop cond body) (xs 0) (xs k) (k * (T + 2) + 2) := by
  induction k generalizing xs with
  | zero => simpa using loop_exit hk
  | succ k ih =>
    have := loop_iter (hc 0 (by omega)) (hbody 0 (by omega))
      (ih (fun i => xs (i + 1)) (fun i hi => hc (i + 1) (by omega)) hk
        (fun i hi => hbody (i + 1) (by omega)))
    exact this.mono (by rw [Nat.succ_mul]; omega)

/-- **Loop rule, invariant and measure.** If every state satisfying the invariant `I` and the
condition is led by the body, within `T` instructions, to a state satisfying `I` with a smaller
measure `μ`, then from a state satisfying `I` the loop terminates within `μ x (T + 2) + 2`
instructions, in a state satisfying `I` where the condition fails. -/
theorem loop_invariant (I : Data r → Prop) (μ : Data r → ℕ) {T : ℕ}
    (hbody : ∀ x, I x → cond.Holds x → ∃ y, ExecWithin w body x y T ∧ I y ∧ μ y < μ x)
    (hx : I x) :
    ∃ y, ExecWithin w (.loop cond body) x y (μ x * (T + 2) + 2) ∧ I y ∧ ¬cond.Holds y := by
  induction hm : μ x using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    subst hm
    by_cases hc : cond.Holds x
    · obtain ⟨y, hy, hIy, hμ⟩ := hbody x hx hc
      obtain ⟨z, hz, hIz, hcz⟩ := ih (μ y) hμ hIy rfl
      refine ⟨z, (loop_iter hc hy hz).mono ?_, hIz, hcz⟩
      have := Nat.mul_le_mul_right (T + 2) (Nat.succ_le_of_lt hμ)
      rw [Nat.succ_mul] at this
      omega
    · exact ⟨x, (loop_exit hc).mono (by omega), hx, hc⟩

/-! ### Data instructions -/

/-- Setting register `d` to a fitting constant `v` executes within one instruction. -/
theorem const {v : ℕ} (h : Fits w v) :
    ExecWithin (B := B) w (.op (.const d v)) x (x.set d v) 1 :=
  (Exec.const h).within

/-- An ALU operation whose result `v` fits in a word executes within one instruction. -/
theorem alu {f : B.Op} {args : Fin (B.Arity f) → Fin r} {v : ℕ}
    (hf : B.interp w f (x.regs ∘ args) = some v) (h : Fits w v) :
    ExecWithin w (.op (.alu f d args)) x (x.set d v) 1 :=
  (Exec.alu hf h).within

/-- Copying register `s` into register `d` executes within one instruction. -/
theorem copy : ExecWithin (B := B) w (.op (.copy d s)) x (x.set d (x.regs s)) 1 :=
  Exec.copy.within

/-- Loading the memory cell at register `a` into register `d` executes within one instruction. -/
theorem load : ExecWithin (B := B) w (.op (.load d a)) x (x.set d (x.mem (x.regs a))) 1 :=
  Exec.load.within

/-- Storing register `s` into the memory cell at register `a` executes within one instruction. -/
theorem store :
    ExecWithin (B := B) w (.op (.store a s)) x (x.write (x.regs a) (x.regs s)) 1 :=
  Exec.store.within

/-- A standard binary operation whose result fits in a word executes within one instruction. -/
theorem bin {f : BinOp} (h : Fits w (f.eval (x.regs i) (x.regs j))) :
    ExecWithin w (.op (.bin f d i j)) x (x.set d (f.eval (x.regs i) (x.regs j))) 1 :=
  (Exec.bin h).within

/-- Reading the word size `w` into register `d` executes within one instruction. -/
theorem width : ExecWithin w (.op (.width d)) x (x.set d w) 1 :=
  Exec.width.within

end ExecWithin

/-! ## Symbolic execution -/

/-- Run a loop with condition `c` and body semantics `body`, for at most `fuel` iterations. -/
def Code.evalLoop (c : Cond r) (body : Data r → Option (Data r × ℕ)) :
    ℕ → Data r → Option (Data r × ℕ)
  | 0, x => if c.Holds x then none else some (x, 2)
  | fuel + 1, x =>
    if c.Holds x then do
      let ym ← body x
      (evalLoop c body fuel ym.1).map fun zn => (zn.1, ym.2 + zn.2 + 2)
    else some (x, 2)

/-- Run a structured program at word size `w`, allowing each loop at most `fuel` iterations per
entry: `some (y, n)` if it leads to `y` executing `n` instructions, and `none` if it faults or
runs out of iterations. The definition is structurally recursive, so `simp` and `decide`
evaluate it. -/
def Code.eval (w fuel : ℕ) : Code B r → Data r → Option (Data r × ℕ)
  | .op o, x => (o.eval w x).map fun y => (y, 1)
  | .seq c₁ c₂, x => do
    let ym ← c₁.eval w fuel x
    (c₂.eval w fuel ym.1).map fun zn => (zn.1, ym.2 + zn.2)
  | .branch c pos neg, x =>
    if c.Holds x then (pos.eval w fuel x).map fun yn => (yn.1, yn.2 + 1)
    else (neg.eval w fuel x).map fun yn => (yn.1, yn.2 + 2)
  | .loop c body, x => evalLoop c (fun y => body.eval w fuel y) fuel x

private theorem Exec.of_evalLoop {w : ℕ} {c : Cond r} {body : Code B r}
    {f : Data r → Option (Data r × ℕ)}
    (hf : ∀ {x y : Data r} {n : ℕ}, f x = some (y, n) → Exec w body x y n) {fuel : ℕ}
    {x y : Data r} {n : ℕ} (h : Code.evalLoop c f fuel x = some (y, n)) :
    Exec w (.loop c body) x y n := by
  induction fuel generalizing x y n with
  | zero =>
    simp only [Code.evalLoop] at h
    split at h
    · cases h
    · next hc => cases h; exact .loop_exit hc
  | succ fuel ih =>
    simp only [Code.evalLoop] at h
    split at h
    · next hc =>
      obtain ⟨⟨x₁, m⟩, hb, hrest⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨x₂, k⟩, hl, he⟩ := Option.map_eq_some_iff.1 hrest
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .loop_iter hc (hf hb) (ih hl)
    · next hc => cases h; exact .loop_exit hc

/-- The interpreter only finds executions. -/
theorem Exec.of_eval {w fuel : ℕ} {c : Code B r} {x y : Data r} {n : ℕ}
    (h : c.eval w fuel x = some (y, n)) : Exec w c x y n := by
  induction c generalizing x y n with
  | op o =>
    obtain ⟨y', hy, he⟩ := Option.map_eq_some_iff.1 h
    cases he
    exact .op hy
  | seq c₁ c₂ ih₁ ih₂ =>
    obtain ⟨⟨x₁, m⟩, h₁, hrest⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨x₂, k⟩, h₂, he⟩ := Option.map_eq_some_iff.1 hrest
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .seq (ih₁ h₁) (ih₂ h₂)
  | branch c pos neg ihp ihn =>
    simp only [Code.eval] at h
    split at h
    · next hc =>
      obtain ⟨⟨x₁, m⟩, h₁, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .branch_pos hc (ihp h₁)
    · next hc =>
      obtain ⟨⟨x₁, m⟩, h₁, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .branch_neg hc (ihn h₁)
  | loop c body ih => exact Exec.of_evalLoop ih h

/-- If the bounded-fuel interpreter returns `(y, n)` with `n ≤ T`, then `c` executes within `T`
instructions. -/
theorem ExecWithin.of_eval {w fuel : ℕ} {c : Code B r} {x y : Data r} {n T : ℕ}
    (h : c.eval w fuel x = some (y, n)) (hn : n ≤ T) : ExecWithin w c x y T :=
  ⟨n, hn, .of_eval h⟩

/-! ## Registers a program does not write -/

/-- The register a data instruction writes, if any. -/
def Op.dest : Op B r → Option (Fin r)
  | .const d _ | .copy d _ | .alu _ d _ | .load d _ => some d
  | .store _ _ => none

/-- A binary operation writes its destination register `d`. -/
@[simp]
theorem Op.dest_bin (f : BinOp) (d i j : Fin r) : (Op.bin f d i j).dest = some d := rfl

/-- The word-size instruction writes its destination register `d`. -/
@[simp]
theorem Op.dest_width (d : Fin r) : (Op.width d).dest = some d := rfl

/-- No instruction of the program writes register `i`. -/
def Code.Preserves (i : Fin r) : Code B r → Prop
  | .op o => o.dest ≠ some i
  | .seq c₁ c₂ => c₁.Preserves i ∧ c₂.Preserves i
  | .branch _ pos neg => pos.Preserves i ∧ neg.Preserves i
  | .loop _ body => body.Preserves i

/-- Decidability of whether a structured program preserves register `i`. -/
instance Code.decidablePreserves (i : Fin r) : (c : Code B r) → Decidable (c.Preserves i)
  | .op o => inferInstanceAs (Decidable (o.dest ≠ some i))
  | .seq c₁ c₂ =>
    have := c₁.decidablePreserves i
    have := c₂.decidablePreserves i
    inferInstanceAs (Decidable (_ ∧ _))
  | .branch _ pos neg =>
    have := pos.decidablePreserves i
    have := neg.decidablePreserves i
    inferInstanceAs (Decidable (_ ∧ _))
  | .loop _ body => body.decidablePreserves i

private theorem Op.regs_eq {w : ℕ} {o : Op B r} {x y : Data r} {i : Fin r} (hi : o.dest ≠ some i)
    (h : o.eval w x = some y) : y.regs i = x.regs i := by
  have hne {d : Fin r} (hd : o.dest = some d) : i ≠ d := fun hid => hi (hid ▸ hd)
  cases o with
  | const d =>
    obtain ⟨-, rfl⟩ := Data.put_eq_some.1 h
    simp [Function.update_of_ne (hne rfl)]
  | alu _ d =>
    obtain ⟨_, -, -, rfl⟩ := Op.eval_alu_eq_some.1 h
    simp [Function.update_of_ne (hne rfl)]
  | copy d | load d => cases h; simp [Function.update_of_ne (hne rfl)]
  | store => cases h; rfl

/-- **Register preservation.** A register that no instruction of a program writes keeps its
contents. -/
theorem Exec.regs_eq {w : ℕ} {c : Code B r} {x y : Data r} {n : ℕ} {i : Fin r}
    (h : Exec w c x y n) (hi : c.Preserves i) : y.regs i = x.regs i := by
  induction h with
  | op ho => exact Op.regs_eq hi ho
  | seq _ _ ih₁ ih₂ => exact (ih₂ hi.2).trans (ih₁ hi.1)
  | branch_pos _ _ ih => exact ih hi.1
  | branch_neg _ _ ih => exact ih hi.2
  | loop_exit _ => rfl
  | loop_iter _ _ _ ihb ihl => exact (ihl hi).trans (ihb hi)

/-- Any register preserved by `c` retains its value across a bounded execution. -/
theorem ExecWithin.regs_eq {w T : ℕ} {c : Code B r} {x y : Data r} {i : Fin r}
    (h : ExecWithin w c x y T) (hi : c.Preserves i) : y.regs i = x.regs i :=
  let ⟨_, _, he⟩ := h
  he.regs_eq hi

/-! ## Running a program on other registers

A program over `r` registers runs on `r'` registers through an injective choice
`f : Fin r → Fin r'`: register `i` of the program is register `f i` of the larger file. The other
registers keep their contents, so a caller can keep its own state across the call. -/

/-- The data seen through the registers chosen by `f`. -/
def Data.comap (f : Fin r → Fin r') (x : Data r') : Data r := ⟨x.regs ∘ f, x.mem⟩

/-- Data `y` written back to the registers chosen by `f`, the other registers taken from `x`. -/
noncomputable def Data.extend (f : Fin r → Fin r') (y : Data r) (x : Data r') : Data r' :=
  ⟨Function.extend f y.regs x.regs, y.mem⟩

/-- Run the data instruction on the registers chosen by `f`. -/
def Op.rename (f : Fin r → Fin r') : Op B r → Op B r'
  | .const d v => .const (f d) v
  | .copy d s => .copy (f d) (f s)
  | .alu g d args => .alu g (f d) (f ∘ args)
  | .load d a => .load (f d) (f a)
  | .store a s => .store (f a) (f s)

/-- Renaming a binary operation renames its destination and operand registers. -/
@[simp]
theorem Op.rename_bin (f : Fin r → Fin r') (g : BinOp) (d i j : Fin r) :
    (Op.bin g d i j).rename f = Op.bin g (f d) (f i) (f j) := by
  simp only [Op.bin, Op.rename]
  congr 1
  funext k
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- Renaming the word-size instruction renames its destination register. -/
@[simp]
theorem Op.rename_width (f : Fin r → Fin r') (d : Fin r) :
    (Op.width d).rename f = Op.width (f d) := by
  simp only [Op.width, Op.rename]
  congr 1
  funext k
  exact k.elim0

/-- Test the condition on the registers chosen by `f`. -/
def Cond.rename (f : Fin r → Fin r') : Cond r → Cond r'
  | .eq i j => .eq (f i) (f j)
  | .lt i j => .lt (f i) (f j)

/-- Run the structured program on the registers chosen by `f`. -/
def Code.rename (f : Fin r → Fin r') : Code B r → Code B r'
  | .op o => .op (o.rename f)
  | .seq c₁ c₂ => .seq (c₁.rename f) (c₂.rename f)
  | .branch c pos neg => .branch (c.rename f) (pos.rename f) (neg.rename f)
  | .loop c body => .loop (c.rename f) (body.rename f)

/-- Register renaming preserves the compiled program size. -/
@[simp]
theorem Code.size_rename (f : Fin r → Fin r') (c : Code B r) : (c.rename f).size = c.size := by
  induction c <;> simp_all [Code.rename]

section Rename

variable {f : Fin r → Fin r'}

/-- Reading register `i` of `x.comap f` reads register `f i` of `x`. -/
@[simp]
theorem Data.comap_regs (x : Data r') (i : Fin r) : (x.comap f).regs i = x.regs (f i) := rfl

/-- `Data.comap` leaves memory unchanged. -/
@[simp]
theorem Data.comap_mem (x : Data r') : (x.comap f).mem = x.mem := rfl

private theorem Data.comap_extend (hf : f.Injective) (y : Data r) (x : Data r') :
    (y.extend f x).comap f = y := by
  ext i
  · exact hf.extend_apply _ _ i
  · rfl

private theorem Data.extend_extend (hf : f.Injective) (y z : Data r) (x : Data r') :
    z.extend f (y.extend f x) = z.extend f x := by
  ext j
  · simp only [Data.extend]
    by_cases hj : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := hj
      simp [hf.extend_apply]
    · simp [Function.extend_apply' _ _ _ hj]
  · rfl

private theorem Data.extend_comap (hf : f.Injective) (x : Data r') :
    (x.comap f).extend f x = x := by
  ext j
  · change Function.extend f (x.regs ∘ f) x.regs j = x.regs j
    by_cases hj : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := hj
      exact hf.extend_apply _ _ i
    · exact Function.extend_apply' _ _ _ hj
  · rfl

private theorem Data.extend_set (hf : f.Injective) (y : Data r) (x : Data r') (i : Fin r) (v : ℕ) :
    (y.set i v).extend f x = (y.extend f x).set (f i) v :=
  Data.ext (hf.extend_update _ _ _ _) rfl

private theorem Data.extend_write (y : Data r) (x : Data r') (a v : ℕ) :
    (y.write a v).extend f x = (y.extend f x).write a v := rfl

/-- A renamed condition holds on `x` if and only if the original condition holds on `x.comap f`. -/
theorem Cond.holds_rename (c : Cond r) (x : Data r') : (c.rename f).Holds x ↔ c.Holds (x.comap f) :=
  by cases c <;> rfl

/-- Evaluating a renamed instruction along an injective register map `f` commutes with `comap` and
`extend`. -/
theorem Op.eval_rename (hf : f.Injective) (o : Op B r) (w : ℕ) (x : Data r') :
    (o.rename f).eval w x = ((o.eval w (x.comap f)).map fun y => y.extend f x) := by
  have hput {d : Fin r} {v : ℕ} :
      x.put w (f d) v = ((x.comap f).put w d v).map fun y => y.extend f x := by
    unfold Data.put
    split <;> simp [Data.extend_set hf, Data.extend_comap hf]
  cases o with
  | const => exact hput
  | alu g d args =>
    change (B.interp w g ((x.comap f).regs ∘ args)).bind (x.put w (f d)) =
      ((B.interp w g ((x.comap f).regs ∘ args)).bind ((x.comap f).put w d)).map _
    cases B.interp w g ((x.comap f).regs ∘ args) with
    | none => rfl
    | some v => exact hput
  | copy | load =>
    simp [Op.rename, Op.eval, Data.extend_set hf, Data.extend_comap hf]
  | store a s =>
    simp [Op.rename, Op.eval, Data.extend_write, Data.extend_comap hf]

/-- **Renaming.** A program run on the registers chosen by an injective `f` does what it does on
its own registers, with the same instruction count, and leaves the other registers unchanged. -/
theorem Exec.rename (hf : f.Injective) {w : ℕ} {c : Code B r} {x : Data r'} {y : Data r} {n : ℕ}
    (h : Exec w c (x.comap f) y n) : Exec w (c.rename f) x (y.extend f x) n := by
  generalize hx : x.comap f = x₀ at h
  induction h generalizing x with
  | op ho =>
    subst hx
    exact .op (by rw [Op.eval_rename hf, ho]; rfl)
  | seq _ _ ih₁ ih₂ =>
    have h₁ := ih₁ hx
    have h₂ := ih₂ (Data.comap_extend hf _ x)
    rw [Data.extend_extend hf] at h₂
    exact .seq h₁ h₂
  | branch_pos hc _ ih =>
    subst hx
    exact .branch_pos ((Cond.holds_rename _ _).2 hc) (ih rfl)
  | branch_neg hc _ ih =>
    subst hx
    exact .branch_neg (fun h => hc ((Cond.holds_rename _ _).1 h)) (ih rfl)
  | loop_exit hc =>
    subst hx
    rw [Data.extend_comap hf]
    exact .loop_exit (fun h => hc ((Cond.holds_rename _ _).1 h))
  | loop_iter hc _ _ ihb ihl =>
    subst hx
    have h₁ := ihb rfl
    have h₂ := ihl (Data.comap_extend hf _ x)
    rw [Data.extend_extend hf] at h₂
    exact .loop_iter ((Cond.holds_rename _ _).2 hc) h₁ h₂

/-- Bounded-time execution of a program renamed along an injective register map `f`. -/
theorem ExecWithin.rename (hf : f.Injective) {w T : ℕ} {c : Code B r} {x : Data r'} {y : Data r}
    (h : ExecWithin w c (x.comap f) y T) : ExecWithin w (c.rename f) x (y.extend f x) T :=
  let ⟨n, hn, he⟩ := h
  ⟨n, hn, he.rename hf⟩

end Rename

/-! ## Word sizes and word bounds -/

/-- **Word-size monotonicity.** A program that does not read the word size runs in the same way
at every larger word size. -/
theorem Exec.mono_width {w w' : ℕ} {c : Code B r} {x y : Data r} {n : ℕ} (hc : ¬c.ReadsWidth)
    (h : Exec w c x y n) (hw : w ≤ w') : Exec w' c x y n := by
  induction h with
  | op ho => exact .op (Op.eval_mono_width hc ho hw)
  | seq _ _ ih₁ ih₂ => exact .seq (ih₁ fun h => hc (.inl h)) (ih₂ fun h => hc (.inr h))
  | branch_pos hp _ ih => exact .branch_pos hp (ih fun h => hc (.inl h))
  | branch_neg hn _ ih => exact .branch_neg hn (ih fun h => hc (.inr h))
  | loop_exit hn => exact .loop_exit hn
  | loop_iter hp _ _ ihb ihl => exact .loop_iter hp (ihb hc) (ihl hc)

/-- A program that does not read the word size executes within the same bound at any larger word
size. -/
theorem ExecWithin.mono_width {w w' T : ℕ} {c : Code B r} {x y : Data r} (hc : ¬c.ReadsWidth)
    (h : ExecWithin w c x y T) (hw : w ≤ w') : ExecWithin w' c x y T :=
  let ⟨n, hn, he⟩ := h
  ⟨n, hn, he.mono_width hc hw⟩

/-- Executions keep data word-sized. -/
theorem Exec.bounded {w : ℕ} {c : Code B r} {x y : Data r} {n : ℕ} (h : Exec w c x y n)
    (hx : x.Bounded w) : y.Bounded w := by
  induction h with
  | op ho => exact hx.op ho
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hx)
  | branch_pos _ _ ih | branch_neg _ _ ih => exact ih hx
  | loop_exit _ => exact hx
  | loop_iter _ _ _ ihb ihl => exact ihl (ihb hx)

/-- Bounded-time executions preserve word-sized data. -/
theorem ExecWithin.bounded {w T : ℕ} {c : Code B r} {x y : Data r} (h : ExecWithin w c x y T)
    (hx : x.Bounded w) : y.Bounded w :=
  let ⟨_, _, he⟩ := h
  he.bounded hx

end Cslib.WordRAM

end
