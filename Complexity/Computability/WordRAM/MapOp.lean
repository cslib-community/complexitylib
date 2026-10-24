/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Compile
public import Complexity.Computability.WordRAM.Time

/-!
# Running word-RAM programs over a larger basis

A map of bases `φ : B.Hom B'` (`Cslib.WordRAM.Basis.Hom`) sends every operation of `B` to an
operation of `B'` with the same meaning at every word size. Replacing each operation of a program
by its image (`Cslib.WordRAM.Program.mapOp`, `Cslib.WordRAM.Code.mapOp`) leaves every other
instruction in place, so the translated program takes exactly the same steps: the same states,
faults, outputs and instruction counts (`Cslib.WordRAM.step_mapOp`). Decision procedures and
the classes of `Cslib.WordRAM.LinearTime` and `Cslib.WordRAM.PolynomialTime` therefore grow with
the basis. This is the word-RAM analogue of translating circuits along a map of signatures
(`Cslib.Circuits.Circuit.mapOp`), with a budget of one instruction for every operation.

A result proved over a small basis thus holds over every basis containing it: over
`Cslib.WordRAM.Basis.standard`, and over any other basis that interprets the same operations in the
same way. The converse direction, simulating an operation by a program over a smaller basis with an
instruction budget, is not formalized here.

## Main definitions

* `Cslib.WordRAM.Op.mapOp`, `Cslib.WordRAM.Instr.mapOp`, `Cslib.WordRAM.Program.mapOp`,
  `Cslib.WordRAM.Code.mapOp`, `Cslib.WordRAM.WordSizeDependentProgram.mapOp`: translation along a
  map of bases.

## Main results

* `Cslib.WordRAM.Op.eval_mapOp`, `Cslib.WordRAM.step_mapOp`: translated instructions have the same
  effect.
* `Cslib.WordRAM.executes_mapOp_iff`, `Cslib.WordRAM.Exec.mapOp`: translated programs halt in the
  same way, with the same instruction count.
* `Cslib.WordRAM.Code.assemble_mapOp`: translation commutes with assembly.
* `Cslib.WordRAM.DecidableInTime.mapOp`, `Cslib.WordRAM.LinearTime.mapOp`,
  `Cslib.WordRAM.PolynomialTime.mapOp`: decision transfers to a larger basis with the same time
  bound and word-size threshold.

## References

* [T. Hagerup, *Sorting and searching on the word RAM*][Hagerup1998]
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B B' B'' : Basis} {r : ℕ} {α : Type*}

/-! ## Instructions -/

/-- The data instruction applying `φ f` in place of each operation `f`. -/
def Op.mapOp (φ : B.Hom B') : Op B r → Op B' r
  | .const d v => .const d v
  | .copy d s => .copy d s
  | .alu f d args => .alu (φ.map f) d fun a => args (Fin.cast (φ.arity_map f) a)
  | .load d a => .load d a
  | .store a s => .store a s

/-- The instruction applying `φ f` in place of each operation `f`. -/
def Instr.mapOp (φ : B.Hom B') : Instr B r → Instr B' r
  | .op o => .op (o.mapOp φ)
  | .jump t => .jump t
  | .branch c t => .branch c t
  | .halt i => .halt i

/-- The program applying `φ f` in place of each operation `f`, instruction for instruction. -/
def Program.mapOp (φ : B.Hom B') (p : Program B r) : Program B' r := p.map (Instr.mapOp φ)

/-- The structured program applying `φ f` in place of each operation `f`. -/
def Code.mapOp (φ : B.Hom B') : Code B r → Code B' r
  | .op o => .op (o.mapOp φ)
  | .seq c₁ c₂ => .seq (c₁.mapOp φ) (c₂.mapOp φ)
  | .branch c pos neg => .branch c (pos.mapOp φ) (neg.mapOp φ)
  | .loop c body => .loop c (body.mapOp φ)

variable (φ : B.Hom B')

/-- Translating a program along a basis homomorphism preserves its length. -/
@[simp]
theorem Program.length_mapOp (p : Program B r) : (p.mapOp φ).length = p.length :=
  List.length_map _

/-- Translating a structured program along a basis homomorphism preserves its size. -/
@[simp]
theorem Code.size_mapOp (c : Code B r) : (c.mapOp φ).size = c.size := by
  induction c <;> simp_all [Code.mapOp]

/-- A translated data instruction has the same effect. -/
@[simp]
theorem Op.eval_mapOp (o : Op B r) (w : ℕ) (x : Data r) : (o.mapOp φ).eval w x = o.eval w x := by
  cases o with
  | alu f d args => exact congrArg (·.bind (x.put w d)) (φ.interp_map w f (x.regs ∘ args))
  | _ => rfl

/-- A translated data instruction reads the word size only if the instruction does. -/
theorem Op.readsWidth_of_mapOp {o : Op B r} (h : (o.mapOp φ).ReadsWidth) : o.ReadsWidth := by
  cases o with
  | alu f d args => exact φ.readsWidth_of_map f h
  | _ => exact h

/-- A translated instruction reads the word size only if the instruction does. -/
theorem Instr.readsWidth_of_mapOp {i : Instr B r} (h : (i.mapOp φ).ReadsWidth) : i.ReadsWidth := by
  cases i with
  | op o => exact Op.readsWidth_of_mapOp φ h
  | _ => exact h

/-- A translated program reads the word size only if the program does. -/
theorem Program.readsWidth_of_mapOp {p : Program B r} (h : (p.mapOp φ).ReadsWidth) :
    p.ReadsWidth := by
  obtain ⟨i, hi, hr⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  exact ⟨j, hj, Instr.readsWidth_of_mapOp φ hr⟩

/-- A translated structured program reads the word size only if the program does. -/
theorem Code.readsWidth_of_mapOp {c : Code B r} (h : (c.mapOp φ).ReadsWidth) : c.ReadsWidth := by
  induction c with
  | op o => exact Op.readsWidth_of_mapOp φ h
  | seq _ _ ih₁ ih₂ => exact h.imp ih₁ ih₂
  | branch _ _ _ ihp ihn => exact h.imp ihp ihn
  | loop _ _ ih => exact ih h

/-! ## Runs -/

/-- **Translation preserves steps.** The translated program takes the same step from every state:
the same next state, output or fault. -/
@[simp]
theorem step_mapOp (w : ℕ) (p : Program B r) (s : State r) :
    step w (p.mapOp φ) s = step w p s := by
  unfold step Program.mapOp
  rw [List.getElem?_map]
  cases p[s.pc]? with
  | none => rfl
  | some i =>
    cases i with
    | op o => simp only [Option.map_some, Instr.mapOp, Op.eval_mapOp]
    | _ => rfl

private theorem next_mapOp (w : ℕ) (p : Program B r) : Next w (p.mapOp φ) = Next w p := by
  funext s t
  simp only [Next, step_mapOp]

private theorem runs_mapOp (w : ℕ) (p : Program B r) : Runs w (p.mapOp φ) = Runs w p := by
  rw [Runs, Runs, next_mapOp]

/-- **Translation preserves halting runs.** The translated program halts with the same output
after the same number of instructions. -/
@[simp]
theorem executes_mapOp_iff {w : ℕ} {p : Program B r} {s : State r} {v n : ℕ} :
    Executes w (p.mapOp φ) s v n ↔ Executes w p s v n := by
  simp only [Executes, runs_mapOp, step_mapOp]

/-- Fuel-bounded execution of a translated program agrees with the original program. -/
@[simp]
theorem run_mapOp (w : ℕ) (p : Program B r) (fuel : ℕ) (s : State r) :
    run w (p.mapOp φ) fuel s = run w p fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih => simp only [run_succ, step_mapOp, ih]

/-! ## Structured programs -/

/-- A translated structured program runs in the same way, with the same instruction count. -/
theorem Exec.mapOp {w : ℕ} {c : Code B r} {x y : Data r} {n : ℕ} (h : Exec w c x y n) :
    Exec w (c.mapOp φ) x y n := by
  induction h with
  | op ho => exact .op (by rw [Op.eval_mapOp]; exact ho)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_exit hc => exact .loop_exit hc
  | loop_iter hc _ _ ihb ihl => exact .loop_iter hc ihb ihl

/-- Bounded-step execution of a structured program transfers along a basis homomorphism. -/
theorem ExecWithin.mapOp {w T : ℕ} {c : Code B r} {x y : Data r} (h : ExecWithin w c x y T) :
    ExecWithin w (c.mapOp φ) x y T :=
  let ⟨n, hn, he⟩ := h
  ⟨n, hn, he.mapOp φ⟩

/-- Translation commutes with assembly. -/
theorem Code.assemble_mapOp (c : Code B r) (pc : ℕ) :
    (c.mapOp φ).assemble pc = (c.assemble pc).mapOp φ := by
  induction c generalizing pc with
  | op o => rfl
  | seq c₁ c₂ ih₁ ih₂ => simp [Code.mapOp, Code.assemble, Program.mapOp, ih₁, ih₂]
  | branch c pos neg ihp ihn =>
    simp [Code.mapOp, Code.assemble, Program.mapOp, ihp, ihn, Instr.mapOp]
  | loop c body ih => simp [Code.mapOp, Code.assemble, Program.mapOp, ih, Instr.mapOp]

/-- Translation commutes with compiling a structured program into a complete halting program. -/
theorem Code.program_mapOp (c : Code B r) (out : Fin r) :
    (c.mapOp φ).program out = (c.program out).mapOp φ := by
  simp [Code.program, Code.assemble_mapOp, Program.mapOp, Instr.mapOp]

/-- A structured program that answers a question continues to answer it after translation. -/
theorem Code.Answers.mapOp {c : Code B r} {out : Fin r} {w : ℕ} {input : List ℕ} {b : Prop}
    {time : ℕ} (h : c.Answers out w input b time) : (c.mapOp φ).Answers out w input b time :=
  let ⟨y, hy, hv⟩ := h
  ⟨y, hy.mapOp φ, hv⟩

/-! ## Decision -/

/-- A translated flat program answers a question within `time` steps if and only if the original
program does. -/
@[simp]
theorem Program.answers_mapOp_iff {p : Program B r} {w : ℕ} {input : List ℕ} {b : Prop}
    {time : ℕ} : (p.mapOp φ).Answers w input b time ↔ p.Answers w input b time := by
  simp only [Program.Answers, executes_mapOp_iff]

/-- A flat decision procedure transfers along a basis homomorphism with the same time bound. -/
theorem Program.DecidesInTime.mapOp {p : Program B r} {encode : ℕ → α → List ℕ} {A : Set α}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop}
    (h : p.DecidesInTime encode A time allowed) :
    (p.mapOp φ).DecidesInTime encode A time allowed :=
  fun a w hw hi => (answers_mapOp_iff φ).2 (h a w hw hi)

/-- Translate each member of a width-indexed family. -/
def WordSizeDependentProgram.mapOp (P : WordSizeDependentProgram B r) :
    WordSizeDependentProgram B' r :=
  fun w => (P w).mapOp φ

/-- Translation preserves the code-length bound. -/
theorem WordSizeDependentProgram.BoundedCode.mapOp {P : WordSizeDependentProgram B r}
    (h : P.BoundedCode) : (P.mapOp φ).BoundedCode :=
  let ⟨L, hL⟩ := h
  ⟨L, fun w => by
    simpa only [WordSizeDependentProgram.mapOp, Program.mapOp, List.length_map] using hL w⟩

/-- Translation preserves family decision at the same width and instruction count. -/
theorem WordSizeDependentProgram.DecidesInTime.mapOp {P : WordSizeDependentProgram B r}
    {encode : ℕ → α → List ℕ} {A : Set α} {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop}
    (h : P.DecidesInTime encode A time allowed) :
    (P.mapOp φ).DecidesInTime encode A time allowed :=
  fun a w hw hi => (Program.answers_mapOp_iff φ).2 (h a w hw hi)

/-- Nonuniform decision grows with the operation basis, preserving code length. -/
theorem DecidableInTime.mapOp {encode : ℕ → α → List ℕ} {A : Set α}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop}
    (φ : B.Hom B') (h : DecidableInTime B A encode time allowed) :
    DecidableInTime B' A encode time allowed :=
  let ⟨r, P, hP, hp⟩ := h
  ⟨r, P.mapOp φ, hP.mapOp φ, hp.mapOp φ⟩

/-- Uniform decision grows with the operation basis. -/
theorem UniformDecidableInTime.mapOp {encode : ℕ → α → List ℕ} {A : Set α}
    {time : α → ℕ → ℕ} {allowed : α → ℕ → Prop}
    (φ : B.Hom B') (h : UniformDecidableInTime B A encode time allowed) :
    UniformDecidableInTime B' A encode time allowed :=
  let ⟨r, p, hp⟩ := h
  ⟨r, p.mapOp φ, hp.mapOp φ⟩

/-- Linear time over a basis is linear time over every larger basis. -/
theorem LinearTime.mapOp {encode : ℕ → α → List ℕ} {A : Set α} {size : α → ℕ} (φ : B.Hom B')
    (h : LinearTime B A encode size) : LinearTime B' A encode size :=
  let ⟨c, k, hk, hd⟩ := h
  ⟨c, k, hk, hd.mapOp φ⟩

/-- Uniform linear time grows with the operation basis. -/
theorem UniformLinearTime.mapOp {encode : ℕ → α → List ℕ} {A : Set α} {size : α → ℕ}
    (φ : B.Hom B') (h : UniformLinearTime B A encode size) :
    UniformLinearTime B' A encode size :=
  let ⟨c, k, hk, hd⟩ := h
  ⟨c, k, hk, hd.mapOp φ⟩

/-- Polynomial time over a basis is polynomial time over every larger basis. -/
theorem PolynomialTime.mapOp {encode : ℕ → α → List ℕ} {A : Set α} {size : α → ℕ} (φ : B.Hom B')
    (h : PolynomialTime B A encode size) : PolynomialTime B' A encode size :=
  let ⟨T, hT, k, hk, hd⟩ := h
  ⟨T, hT, k, hk, hd.mapOp φ⟩

/-- Uniform polynomial time grows with the operation basis. -/
theorem UniformPolynomialTime.mapOp {encode : ℕ → α → List ℕ} {A : Set α} {size : α → ℕ}
    (φ : B.Hom B') (h : UniformPolynomialTime B A encode size) :
    UniformPolynomialTime B' A encode size :=
  let ⟨T, hT, k, hk, hd⟩ := h
  ⟨T, hT, k, hk, hd.mapOp φ⟩

/-! ## Functoriality -/

/-- Translating a data instruction along the identity basis homomorphism leaves it unchanged. -/
@[simp]
theorem Op.mapOp_id (o : Op B r) : o.mapOp (Basis.Hom.id B) = o := by
  cases o <;> rfl

/-- Translating a data instruction along a composition of basis homomorphisms composes the
translations. -/
theorem Op.mapOp_comp (ψ : B'.Hom B'') (φ : B.Hom B') (o : Op B r) :
    o.mapOp (ψ.comp φ) = (o.mapOp φ).mapOp ψ := by
  cases o <;> rfl

/-- Translating a program along the identity basis homomorphism leaves it unchanged. -/
@[simp]
theorem Program.mapOp_id (p : Program B r) : p.mapOp (Basis.Hom.id B) = p := by
  simp only [Program.mapOp]
  conv_rhs => rw [← List.map_id p]
  congr 1
  funext i
  cases i <;> simp [Instr.mapOp]

/-- Translating a program along a composition of basis homomorphisms composes the translations. -/
theorem Program.mapOp_comp (ψ : B'.Hom B'') (φ : B.Hom B') (p : Program B r) :
    p.mapOp (ψ.comp φ) = (p.mapOp φ).mapOp ψ := by
  simp only [Program.mapOp, List.map_map]
  congr 1
  funext i
  cases i <;> simp [Instr.mapOp, Op.mapOp_comp]

end Cslib.WordRAM

end
