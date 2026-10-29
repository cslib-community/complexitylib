/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import Complexity.Computability.WordRAM.Time

/-!
# Bridge for the word-RAM formal abstract (Pattern B: polymorphic presentation)

`WordRAMAbstract.lean` defines a word RAM from scratch, with fresh inductive types for its
operations, instructions, states and outcomes. This file proves, for every presentation `S` of
such a machine that satisfies `Laws S`, that it is `Cslib.WordRAM` over
`Cslib.WordRAM.Basis.exact`.

Each library instruction translates to an abstract one (`Presentation.instrOf`), and every
abstract instruction is a translation (`Presentation.instrOf_surjective`). One step of a library
program matches one step of its translation (`Presentation.step_matches`), so both halt with the
same output after the same number of instructions (`Presentation.halts_iff_executes`).

## Main results

* `runsAgree`: each abstract program runs alike with some library program over the exact
  basis, and conversely.
* `decidableInTime_iff`: abstract decidability in time `T` is
  `Cslib.WordRAM.UniformDecidableInTime .exact` for the word-size-independent encoding and time
  bound, on the word sizes from the threshold on.
* `haltsVia` and `Machine.runs_map`: multi-step non-halting runs (`Runs`) and halting steps over
  `Basis.exact` translate step-for-step to `Presentation.programOf`, shared by algorithm and
  data-structure bridges (`DijkstraBridge`, `FibonacciHeapBridge`).
-/

namespace ComplexityTests.Abstracts.WordRAMBridge

open Cslib.WordRAM

/-- Polymorphic signature of an abstract presentation of the exact word RAM. -/
structure Presentation where
  AluOp : Type
  add : AluOp
  sub : AluOp
  mul : AluOp
  div : AluOp
  mod : AluOp
  and : AluOp
  or : AluOp
  xor : AluOp
  shl : AluOp
  shr : AluOp
  aluOp_induction {P : AluOp → Prop} :
    P add → P sub → P mul → P div → P mod → P and → P or → P xor → P shl → P shr → ∀ f, P f
  eval : AluOp → ℕ → ℕ → Option ℕ
  Instr : ℕ → Type
  const {r : ℕ} : Fin r → ℕ → Instr r
  copy {r : ℕ} : Fin r → Fin r → Instr r
  alu {r : ℕ} : AluOp → Fin r → Fin r → Fin r → Instr r
  width {r : ℕ} : Fin r → Instr r
  load {r : ℕ} : Fin r → Fin r → Instr r
  store {r : ℕ} : Fin r → Fin r → Instr r
  jump {r : ℕ} : ℕ → Instr r
  branchEq {r : ℕ} : Fin r → Fin r → ℕ → Instr r
  branchLt {r : ℕ} : Fin r → Fin r → ℕ → Instr r
  halt {r : ℕ} : Fin r → Instr r
  instr_induction {r : ℕ} {P : Instr r → Prop} :
    (∀ d x, P (const d x)) → (∀ d i, P (copy d i)) → (∀ f d i j, P (alu f d i j)) →
    (∀ d, P (width d)) → (∀ d a, P (load d a)) → (∀ a i, P (store a i)) →
    (∀ t, P (jump t)) → (∀ i j t, P (branchEq i j t)) → (∀ i j t, P (branchLt i j t)) →
    (∀ i, P (halt i)) → ∀ i, P i
  State : ℕ → Type
  state {r : ℕ} : ℕ → (Fin r → ℕ) → (ℕ → ℕ) → State r
  Outcome : ℕ → Type
  next {r : ℕ} : State r → Outcome r
  halted {r : ℕ} : ℕ → Outcome r
  fault {r : ℕ} : Outcome r
  step {r : ℕ} : ℕ → List (Instr r) → State r → Outcome r
  Halts {r : ℕ} : ℕ → List (Instr r) → State r → ℕ → ℕ → Prop
  OutcomeAgrees {r : ℕ} : Outcome r → Cslib.WordRAM.Outcome r → Prop

/-- Equational specification for a word-RAM presentation: the values of the operations, one
step of each instruction, `Halts` by one step, and the agreeing outcomes. -/
structure Laws (S : Presentation) : Prop where
  eval_add : ∀ x y, S.eval S.add x y = some (x + y)
  eval_sub : ∀ x y, S.eval S.sub x y = if y ≤ x then some (x - y) else none
  eval_mul : ∀ x y, S.eval S.mul x y = some (x * y)
  eval_div : ∀ x y, S.eval S.div x y = if y = 0 then none else some (x / y)
  eval_mod : ∀ x y, S.eval S.mod x y = if y = 0 then none else some (x % y)
  eval_and : ∀ x y, S.eval S.and x y = some (x &&& y)
  eval_or : ∀ x y, S.eval S.or x y = some (x ||| y)
  eval_xor : ∀ x y, S.eval S.xor x y = some (x ^^^ y)
  eval_shl : ∀ x y, S.eval S.shl x y = some (x * 2 ^ y)
  eval_shr : ∀ x y, S.eval S.shr x y = some (x / 2 ^ y)
  step_none : ∀ {r w} {p : List (S.Instr r)} {pc reg mem}, p[pc]? = none →
    S.step w p (S.state pc reg mem) = S.fault
  step_const : ∀ {r w} {p : List (S.Instr r)} {pc reg mem d x}, p[pc]? = some (S.const d x) →
    S.step w p (S.state pc reg mem) =
      if x < 2 ^ w then S.next (S.state (pc + 1) (Function.update reg d x) mem) else S.fault
  step_copy : ∀ {r w} {p : List (S.Instr r)} {pc reg mem d i}, p[pc]? = some (S.copy d i) →
    S.step w p (S.state pc reg mem) = S.next (S.state (pc + 1) (Function.update reg d (reg i)) mem)
  step_alu_none : ∀ {r w} {p : List (S.Instr r)} {pc reg mem f d i j},
    p[pc]? = some (S.alu f d i j) → S.eval f (reg i) (reg j) = none →
    S.step w p (S.state pc reg mem) = S.fault
  step_alu_some : ∀ {r w} {p : List (S.Instr r)} {pc reg mem f d i j x},
    p[pc]? = some (S.alu f d i j) → S.eval f (reg i) (reg j) = some x →
    S.step w p (S.state pc reg mem) =
      if x < 2 ^ w then S.next (S.state (pc + 1) (Function.update reg d x) mem) else S.fault
  step_width : ∀ {r w} {p : List (S.Instr r)} {pc reg mem d}, p[pc]? = some (S.width d) →
    S.step w p (S.state pc reg mem) = S.next (S.state (pc + 1) (Function.update reg d w) mem)
  step_load : ∀ {r w} {p : List (S.Instr r)} {pc reg mem d a}, p[pc]? = some (S.load d a) →
    S.step w p (S.state pc reg mem) =
      S.next (S.state (pc + 1) (Function.update reg d (mem (reg a))) mem)
  step_store : ∀ {r w} {p : List (S.Instr r)} {pc reg mem a i}, p[pc]? = some (S.store a i) →
    S.step w p (S.state pc reg mem) =
      S.next (S.state (pc + 1) reg (Function.update mem (reg a) (reg i)))
  step_jump : ∀ {r w} {p : List (S.Instr r)} {pc reg mem t}, p[pc]? = some (S.jump t) →
    S.step w p (S.state pc reg mem) = S.next (S.state t reg mem)
  step_branchEq : ∀ {r w} {p : List (S.Instr r)} {pc reg mem i j t},
    p[pc]? = some (S.branchEq i j t) →
    S.step w p (S.state pc reg mem) = S.next (S.state (if reg i = reg j then t else pc + 1) reg mem)
  step_branchLt : ∀ {r w} {p : List (S.Instr r)} {pc reg mem i j t},
    p[pc]? = some (S.branchLt i j t) →
    S.step w p (S.state pc reg mem) = S.next (S.state (if reg i < reg j then t else pc + 1) reg mem)
  step_halt : ∀ {r w} {p : List (S.Instr r)} {pc reg mem i}, p[pc]? = some (S.halt i) →
    S.step w p (S.state pc reg mem) = S.halted (reg i)
  halts_zero : ∀ {r w} {p : List (S.Instr r)} {s v}, ¬S.Halts w p s v 0
  halts_next : ∀ {r w} {p : List (S.Instr r)} {s t v n}, S.step w p s = S.next t →
    (S.Halts w p s v (n + 1) ↔ S.Halts w p t v n)
  halts_halted : ∀ {r w} {p : List (S.Instr r)} {s x v n}, S.step w p s = S.halted x →
    (S.Halts w p s v (n + 1) ↔ x = v ∧ n = 0)
  halts_fault : ∀ {r w} {p : List (S.Instr r)} {s v n}, S.step w p s = S.fault →
    ¬S.Halts w p s v (n + 1)
  agrees_next : ∀ {r pc} {reg : Fin r → ℕ} {mem},
    S.OutcomeAgrees (S.next (S.state pc reg mem)) (.next ⟨pc, ⟨reg, mem⟩⟩)
  agrees_halted : ∀ {r v}, S.OutcomeAgrees (r := r) (S.halted v) (.halt v)
  agrees_fault : ∀ {r}, S.OutcomeAgrees (r := r) S.fault .fault

namespace Presentation

variable (S : Presentation) {r : ℕ}

/-! ## The definitions of the abstract that are not recursive -/

/-- The start state on an input, as in the abstract. -/
def init (input : List ℕ) : S.State r :=
  S.state 0 (fun _ => 0) (fun a => (input.length :: input).getD a 0)

/-- An input fits word size `w`, as in the abstract. -/
def InputFits (w : ℕ) (input : List ℕ) : Prop :=
  input.length < 2 ^ w ∧ ∀ x ∈ input, x < 2 ^ w

/-- Decision in time `T`, as in the abstract. -/
def Decides {α : Type*} (p : List (S.Instr r)) (A : Set α) (encode : α → List ℕ)
    (T bits : α → ℕ) : Prop :=
  ∀ a w, bits a ≤ w → InputFits w (encode a) →
    ∃ v n, S.Halts w p (S.init (encode a)) v n ∧ n ≤ T a ∧ (a ∈ A → v = 1) ∧ (a ∉ A → v = 0)

/-- Decidability in time `T`, as in the abstract. -/
def DecidableInTime {α : Type*} (A : Set α) (encode : α → List ℕ) (T bits : α → ℕ) : Prop :=
  ∃ r, ∃ p : List (S.Instr r), S.Decides p A encode T bits

/-- An abstract program and a library program run alike, as in the abstract. -/
def Same (p : List (S.Instr r)) (q : Program .exact r) : Prop :=
  ∀ w pc reg mem,
    S.OutcomeAgrees (S.step w p (S.state pc reg mem)) (Cslib.WordRAM.step w q ⟨pc, ⟨reg, mem⟩⟩) ∧
    ∀ v n, S.Halts w p (S.state pc reg mem) v n ↔ Executes w q ⟨pc, ⟨reg, mem⟩⟩ v n

/-! ## Translation -/

/-- A standard binary operation as an abstract one. -/
def aluOpOf : BinOp → S.AluOp
  | .add => S.add | .sub => S.sub | .mul => S.mul | .div => S.div | .mod => S.mod
  | .and => S.and | .or => S.or | .xor => S.xor | .shiftLeft => S.shl | .shiftRight => S.shr

theorem aluOpOf_surjective (f : S.AluOp) : ∃ g, S.aluOpOf g = f :=
  S.aluOp_induction (P := fun f => ∃ g, S.aluOpOf g = f) ⟨.add, rfl⟩ ⟨.sub, rfl⟩ ⟨.mul, rfl⟩
    ⟨.div, rfl⟩ ⟨.mod, rfl⟩ ⟨.and, rfl⟩ ⟨.or, rfl⟩ ⟨.xor, rfl⟩ ⟨.shiftLeft, rfl⟩
    ⟨.shiftRight, rfl⟩ f

/-- An abstract operation has the exact value of the standard one; shifts are multiplication and
division by powers of two. -/
theorem eval_aluOpOf {S : Presentation} (h : Laws S) (g : BinOp) (x y : ℕ) :
    S.eval (S.aluOpOf g) x y = g.evalExact x y := by
  cases g <;> simp [aluOpOf, h.eval_add, h.eval_sub, h.eval_mul, h.eval_div, h.eval_mod,
    h.eval_and, h.eval_or, h.eval_xor, h.eval_shl, h.eval_shr, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]

/-- An instruction of `Cslib.WordRAM` over the exact basis as an abstract instruction, mapping
`Instr.rand` (which faults deterministically) to an out-of-bounds jump `outOfBounds`. -/
def instrOf (outOfBounds : ℕ) : Cslib.WordRAM.Instr .exact r → S.Instr r
  | .op (.const d x) => S.const d x
  | .op (.copy d i) => S.copy d i
  | .op (.alu (.bin f) d args) => S.alu (S.aluOpOf f) d (args (0 : Fin 2)) (args (1 : Fin 2))
  | .op (.alu .width d _) => S.width d
  | .op (.load d a) => S.load d a
  | .op (.store a i) => S.store a i
  | .jump t => S.jump t
  | .branch (.eq i j) t => S.branchEq i j t
  | .branch (.lt i j) t => S.branchLt i j t
  | .halt i => S.halt i
  | .rand _ _ => S.jump outOfBounds

/-- Translate a library program to an abstract program of the same length. -/
def programOf (q : Program .exact r) : List (S.Instr r) :=
  q.map (S.instrOf q.length)

theorem instrOf_surjective (outOfBounds : ℕ) (i : S.Instr r) :
    ∃ j : Cslib.WordRAM.Instr .exact r, j.IsRandFree ∧ S.instrOf outOfBounds j = i := by
  refine S.instr_induction (P := fun i => ∃ j, j.IsRandFree ∧ S.instrOf outOfBounds j = i)
    (fun d x => ⟨.op (.const d x), trivial, rfl⟩)
    (fun d i => ⟨.op (.copy d i), trivial, rfl⟩) ?_
    (fun d => ⟨.op (.exactWidth d), trivial, rfl⟩)
    (fun d a => ⟨.op (.load d a), trivial, rfl⟩)
    (fun a i => ⟨.op (.store a i), trivial, rfl⟩)
    (fun t => ⟨.jump t, trivial, rfl⟩)
    (fun i j t => ⟨.branch (.eq i j) t, trivial, rfl⟩)
    (fun i j t => ⟨.branch (.lt i j) t, trivial, rfl⟩)
    (fun i => ⟨.halt i, trivial, rfl⟩) i
  intro f d i j
  obtain ⟨g, rfl⟩ := S.aluOpOf_surjective f
  exact ⟨.op (.exactBin g d i j), trivial, rfl⟩

/-- Every abstract program is the translation of a `rand`-free library program. -/
theorem program_surjective (p : List (S.Instr r)) :
    ∃ q : Program .exact r, q.IsRandFree ∧ S.programOf q = p := by
  choose f hf_rf hf_eq using S.instrOf_surjective p.length
  refine ⟨p.map f, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hj
    exact hf_rf i
  · simp only [programOf, List.length_map, List.map_map]
    conv_rhs => rw [← List.map_id p]
    congr 1
    funext i
    exact hf_eq i

/-! ## One step -/

/-- An abstract outcome and a library outcome *match* if both continue in the same state, both
halt with the same output, or both fault. -/
def Matches (o : S.Outcome r) (o' : Cslib.WordRAM.Outcome r) : Prop :=
  (∃ pc reg mem, o = S.next (S.state pc reg mem) ∧ o' = .next ⟨pc, ⟨reg, mem⟩⟩) ∨
    (∃ v, o = S.halted v ∧ o' = .halt v) ∨ (o = S.fault ∧ o' = .fault)

/-- **One step agrees** at every non-`rand` instruction. -/
theorem step_matches_at {S : Presentation} (h : Laws S) (w : ℕ) (q : Program .exact r) (pc : ℕ)
    (reg : Fin r → ℕ) (mem : ℕ → ℕ) (hnr : ∀ j, q[pc]? = some j → j.IsRandFree) :
    S.Matches (S.step w (S.programOf q) (S.state pc reg mem))
      (Cslib.WordRAM.step w q ⟨pc, ⟨reg, mem⟩⟩) := by
  have next {o : S.Outcome r} {o' : Cslib.WordRAM.Outcome r} (pc' : ℕ) (reg' : Fin r → ℕ)
      (mem' : ℕ → ℕ) (h₁ : o = S.next (S.state pc' reg' mem'))
      (h₂ : o' = .next ⟨pc', ⟨reg', mem'⟩⟩) : S.Matches o o' := Or.inl ⟨_, _, _, h₁, h₂⟩
  have fault {o : S.Outcome r} {o' : Cslib.WordRAM.Outcome r} (h₁ : o = S.fault)
      (h₂ : o' = .fault) : S.Matches o o' :=
    Or.inr (Or.inr ⟨h₁, h₂⟩)
  have hget := List.getElem?_map (f := S.instrOf q.length) (l := q) (i := pc)
  change (S.programOf q)[pc]? = _ at hget
  rcases hq : q[pc]? with _ | j
  · rw [hq, Option.map_none] at hget
    exact fault (h.step_none hget) (by simp [Cslib.WordRAM.step, hq])
  rw [hq, Option.map_some] at hget
  have hj := hnr j hq
  -- constants and operations fault on the same values, operations also where they are
  -- undefined; the word size is a word
  match j, hget, hj with
  | .op (.const d x), hget, _ =>
    by_cases hx : x < 2 ^ w
    · exact next (pc + 1) (Function.update reg d x) mem (by simp [h.step_const hget, hx])
        (by simp [Cslib.WordRAM.step, hq, Data.put, Fits, hx, Data.set])
    · exact fault (by simp [h.step_const hget, hx])
        (by simp [Cslib.WordRAM.step, hq, Data.put, Fits, hx])
  | .op (.copy d i), hget, _ =>
    exact next _ _ _ (h.step_copy hget) (by simp [Cslib.WordRAM.step, hq, Data.set])
  | .op (.alu (.bin g) d args), hget, _ =>
    have he := eval_aluOpOf h g (reg (args (0 : Fin 2))) (reg (args (1 : Fin 2)))
    have hlib : StandardOp.evalExact w (.bin g) (reg ∘ args) =
        g.evalExact (reg (args (0 : Fin 2))) (reg (args (1 : Fin 2))) := rfl
    cases hg : g.evalExact (reg (args (0 : Fin 2))) (reg (args (1 : Fin 2))) with
    | none =>
      rw [hg] at he
      exact fault (h.step_alu_none hget he) (by simp only [Cslib.WordRAM.step, hq, Op.eval,
        Basis.exact, hlib, hg, bind, Option.bind_none])
    | some x =>
      rw [hg] at he
      by_cases hx : x < 2 ^ w
      · exact next (pc + 1) (Function.update reg d x) mem
          (by simp [h.step_alu_some hget he, hx])
          (by simp only [Cslib.WordRAM.step, hq, Op.eval, Basis.exact, hlib, hg]
              simp [Data.put, Fits, hx, Data.set])
      · exact fault (by simp [h.step_alu_some hget he, hx])
          (by simp only [Cslib.WordRAM.step, hq, Op.eval, Basis.exact, hlib, hg]
              simp [Data.put, Fits, hx])
  | .op (.alu .width d args), hget, _ =>
    exact next _ _ _ (h.step_width hget)
      (by simp [Cslib.WordRAM.step, hq, StandardOp.evalExact, Data.put, Fits, Data.set,
        Nat.lt_two_pow_self])
  | .op (.load d a), hget, _ =>
    exact next _ _ _ (h.step_load hget) (by simp [Cslib.WordRAM.step, hq, Data.set])
  | .op (.store a i), hget, _ =>
    exact next _ _ _ (h.step_store hget) (by simp [Cslib.WordRAM.step, hq, Data.write])
  | .jump t, hget, _ => exact next _ _ _ (h.step_jump hget) (by simp [Cslib.WordRAM.step, hq])
  | .branch (.eq i j) t, hget, _ =>
    exact next _ _ _ (h.step_branchEq hget) (by simp [Cslib.WordRAM.step, hq])
  | .branch (.lt i j) t, hget, _ =>
    exact next _ _ _ (h.step_branchLt hget) (by simp [Cslib.WordRAM.step, hq])
  | .halt i, hget, _ =>
    exact Or.inr (Or.inl ⟨_, h.step_halt hget, by simp [Cslib.WordRAM.step, hq]⟩)
  | .rand _ _, _, hj => exact hj.elim

/-- **One step agrees** for every `rand`-free library program. -/
theorem step_matches {S : Presentation} (h : Laws S) (w : ℕ) {q : Program .exact r}
    (hq : q.IsRandFree) (pc : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ) :
    S.Matches (S.step w (S.programOf q) (S.state pc reg mem))
      (Cslib.WordRAM.step w q ⟨pc, ⟨reg, mem⟩⟩) :=
  S.step_matches_at h w q pc reg mem fun j hj => hq j (List.mem_of_getElem? hj)

/-! ## Runs -/

/-- `Cslib.WordRAM.Executes` unfolds by one step, as the abstract `Halts` is defined. -/
theorem executes_succ_iff {B : Basis} {w : ℕ} {q : Program B r} {s : Cslib.WordRAM.State r}
    {v n : ℕ} :
    Executes w q s v (n + 1) ↔
      match Cslib.WordRAM.step w q s with
      | .next t => Executes w q t v n
      | .halt x => x = v ∧ n = 0
      | .fault => False := by
  have hrun {t : Cslib.WordRAM.State r} {m : ℕ} : Executes w q t v m ↔ run w q m t = some (v, m) :=
    ⟨Executes.run_eq, Executes.of_run⟩
  rw [hrun, run_succ]
  rcases Cslib.WordRAM.step w q s with t | x | _ <;> dsimp only
  · rw [hrun]
    constructor
    · intro h
      obtain ⟨⟨v', k⟩, hk, hvk⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at hvk
      obtain ⟨rfl, rfl⟩ := hvk
      exact hk
    · intro h
      rw [h]
      rfl
  · simp [eq_comm]
  · simp

/-- **Halting runs agree.** The translation of a library program halts with output `v` after `n`
instructions exactly when the library program does (even if `q` contains `Instr.rand`, which
deterministically faults in `q` and jumps out of bounds in `programOf q`). -/
theorem halts_iff_executes {S : Presentation} (h : Laws S) {w : ℕ} {q : Program .exact r}
    {v n : ℕ} {pc : ℕ} {reg : Fin r → ℕ} {mem : ℕ → ℕ} :
    S.Halts w (S.programOf q) (S.state pc reg mem) v n ↔ Executes w q ⟨pc, ⟨reg, mem⟩⟩ v n := by
  induction n generalizing pc reg mem with
  | zero => exact ⟨fun hh => (h.halts_zero hh).elim, fun he => absurd he.pos (Nat.lt_irrefl 0)⟩
  | succ n ih =>
    rw [executes_succ_iff]
    by_cases hnr : ∀ j, q[pc]? = some j → j.IsRandFree
    · rcases S.step_matches_at h w q pc reg mem hnr with
        ⟨_, _, _, h₁, h₂⟩ | ⟨x, h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h.halts_next h₁, h₂]
        exact ih
      · rw [h.halts_halted h₁, h₂]
      · rw [h₂]
        exact iff_false_intro (h.halts_fault h₁)
    · rcases hq : q[pc]? with _ | j
      · exact absurd (fun _ hj => by simp [hq] at hj) hnr
      have hj : ¬j.IsRandFree := fun hj =>
        hnr fun _ hj' => Option.some.inj (hq.symm.trans hj') ▸ hj
      cases j with
      | op _ | jump _ | branch _ _ | halt _ => exact (hj trivial).elim
      | rand dst src =>
        have hget : (S.programOf q)[pc]? = some (S.jump q.length) := by
          simp [programOf, hq, instrOf]
        have hstep1 := h.step_jump (w := w) (reg := reg) (mem := mem) hget
        have hfault2 : Cslib.WordRAM.step w q ⟨pc, ⟨reg, mem⟩⟩ = .fault := by
          simp [Cslib.WordRAM.step, hq]
        rw [hfault2]
        refine iff_false_intro fun hh => ?_
        rw [h.halts_next hstep1] at hh
        cases n with
        | zero => exact h.halts_zero hh
        | succ k =>
          have hnone : (S.programOf q)[q.length]? = none :=
            List.getElem?_eq_none (by simp [programOf])
          exact h.halts_fault (h.step_none hnone) hh

/-- A `rand`-free library program and its translation run alike. -/
theorem same_map {S : Presentation} (h : Laws S) {q : Program .exact r} (hq : q.IsRandFree) :
    S.Same (S.programOf q) q := by
  refine fun w pc reg mem => ⟨?_, fun _ _ => halts_iff_executes h⟩
  rcases S.step_matches h w hq pc reg mem with ⟨_, _, _, h₁, h₂⟩ | ⟨_, h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    rw [h₁, h₂]
  exacts [h.agrees_next, h.agrees_halted, h.agrees_fault]

/-! ## Decision in time `T` -/

/-- The abstract start state on an input is the start state of `Cslib.WordRAM`: the input
length at address `0`, then the input words. -/
theorem init_eq (input : List ℕ) :
    (⟨0, ⟨fun _ => 0, fun a => (input.length :: input).getD a 0⟩⟩ : Cslib.WordRAM.State r) =
      Cslib.WordRAM.State.init input := by
  simp only [Cslib.WordRAM.State.init, Cslib.WordRAM.State.mk.injEq, true_and]
  ext a
  · rfl
  · rcases a with _ | a <;> simp [Data.init]

/-- An abstract program decides a problem exactly when a library program that runs alike does. -/
theorem decides_iff {S : Presentation} {α : Type*} {p : List (S.Instr r)} {q : Program .exact r}
    (hpq : S.Same p q) {A : Set α} {encode : α → List ℕ} {T bits : α → ℕ} :
    S.Decides p A encode T bits ↔
      q.DecidesInTime (fun _ => encode) A (fun a _ => T a) (fun a w => bits a ≤ w) := by
  -- outputs `1`/`0` on yes/no instances are outputs `v ≤ 1` with `v = 1 ↔ a ∈ A`
  have hans (a : α) (v : ℕ) :
      ((a ∈ A → v = 1) ∧ (a ∉ A → v = 0)) ↔ (v ≤ 1 ∧ (v = 1 ↔ a ∈ A)) := by
    by_cases ha : a ∈ A <;> simp only [ha, not_true, not_false_eq_true, forall_const,
      false_implies, iff_true, iff_false, true_and, and_true] <;> omega
  have hrun (w : ℕ) (input : List ℕ) (v n : ℕ) :
      S.Halts w p (S.init input) v n ↔ Executes w q (.init input) v n := by
    rw [← init_eq]
    exact (hpq w _ _ _).2 v n
  simp only [Decides, Program.DecidesInTime, WordSizeDependentProgram.DecidesInTime,
    WordSizeDependentProgram.const, Program.Answers, InputFits, Cslib.WordRAM.InputFits, Fits,
    hrun, hans]

end Presentation

open Presentation

/-- **Same machine.** Each abstract program runs alike with some `rand`-free program of
`Cslib.WordRAM` over `Basis.exact` with the same registers, and conversely every `rand`-free
library program runs alike with some abstract program. -/
theorem runsAgree (S : Presentation) (h : Laws S) (r : ℕ) :
    (∀ p : List (S.Instr r), ∃ q : Program .exact r, q.IsRandFree ∧ S.Same p q) ∧
      ∀ q : Program .exact r, q.IsRandFree → ∃ p : List (S.Instr r), S.Same p q := by
  refine ⟨fun p => ?_, fun q hq => ⟨_, same_map h hq⟩⟩
  obtain ⟨q, hq, rfl⟩ := S.program_surjective p
  exact ⟨q, hq, same_map h hq⟩

/-- **Same time classes.** A problem is decidable in time `T` on the abstract machine exactly
when one program of `Cslib.WordRAM` over `Basis.exact` decides it with the same encoding and
time bound at every word size from the threshold on. -/
theorem decidableInTime_iff (S : Presentation) (h : Laws S) {α : Type*} (A : Set α)
    (encode : α → List ℕ) (T bits : α → ℕ) :
    S.DecidableInTime A encode T bits ↔
      UniformDecidableInTime .exact A (fun _ => encode) (fun a _ => T a)
        (fun a w => bits a ≤ w) := by
  have hans (a : α) (v : ℕ) :
      ((a ∈ A → v = 1) ∧ (a ∉ A → v = 0)) ↔ (v ≤ 1 ∧ (v = 1 ↔ a ∈ A)) := by
    by_cases ha : a ∈ A <;> simp only [ha, not_true, not_false_eq_true, forall_const,
      false_implies, iff_true, iff_false, true_and, and_true] <;> omega
  constructor
  · rintro ⟨r, p, hp⟩
    obtain ⟨q, hq, rfl⟩ := S.program_surjective p
    exact ⟨r, q, (decides_iff (same_map h hq)).1 hp⟩
  · rintro ⟨r, q, hq⟩
    refine ⟨r, S.programOf q, fun a w hbw hfit => ?_⟩
    have hfit' : Cslib.WordRAM.InputFits w (encode a) := hfit
    obtain ⟨v, n, hex, hn, hv⟩ := hq a w hbw hfit'
    rw [← init_eq] at hex
    exact ⟨v, n, (halts_iff_executes h).2 hex, hn, (hans a v).2 hv⟩

/-! ## Multi-step run transfer (`Runs`) for algorithm and data-structure abstracts -/

/-- Halting runs defined from one step by cases on its outcome, as the abstract `Halts` of
`WordRAMAbstract` is: `cases f g a o` is `f t`, `g x` or `a` when `o` continues in state `t`,
halts with output `x` or faults. Algorithm and data-structure abstracts phrased in terms of `Runs`
use this definition to fill the `Halts` field of `Presentation`. -/
def haltsVia (Instr State Outcome : ℕ → Type)
    (step : ∀ {r : ℕ}, ℕ → List (Instr r) → State r → Outcome r)
    (cases : ∀ {r : ℕ}, (State r → Prop) → (ℕ → Prop) → Prop → Outcome r → Prop) {r : ℕ}
    (w : ℕ) (p : List (Instr r)) : State r → ℕ → ℕ → Prop
  | _, _, 0 => False
  | s, v, n + 1 =>
    cases (fun t => haltsVia Instr State Outcome step cases w p t v n) (fun x => x = v ∧ n = 0)
      False (step w p s)

namespace Machine

variable {S : Presentation} (h : Laws S) {r : ℕ}
include h

/-- The abstract state with the next instruction, registers and memory of a library state. -/
def stateOf (S : Presentation) (t : Cslib.WordRAM.State r) : S.State r :=
  S.state t.pc t.data.regs t.data.mem

omit h in
theorem stateOf_init (input : List ℕ) :
    stateOf S (.init input : Cslib.WordRAM.State r) = S.init input := by
  rw [← Presentation.init_eq]
  rfl

omit h in
/-- A step that does not fault is not at a `rand` instruction, which faults deterministically. -/
theorem isRandFree_of_step {w : ℕ} {q : Program .exact r} {t : Cslib.WordRAM.State r}
    (ht : Cslib.WordRAM.step w q t ≠ .fault) : ∀ j, q[t.pc]? = some j → j.IsRandFree := by
  rintro (_ | _ | _ | _ | _) hj <;> first | trivial | exact ht (step_rand hj)

/-- A step of a library program that continues is a step of its translation. -/
theorem step_next {w : ℕ} {q : Program .exact r} {t t' : Cslib.WordRAM.State r}
    (ht : Cslib.WordRAM.step w q t = .next t') :
    S.step w (S.programOf q) (stateOf S t) = S.next (stateOf S t') := by
  have hnr := isRandFree_of_step (w := w) (q := q) (t := t) (by simp [ht])
  obtain ⟨pc, reg, mem⟩ := t
  rcases S.step_matches_at h w q pc reg mem hnr with ⟨_, _, _, h₁, h₂⟩ | ⟨_, _, h₂⟩ | ⟨_, h₂⟩ <;>
    rw [ht] at h₂ <;> cases h₂
  exact h₁

/-- A step of a library program that halts is a step of its translation. -/
theorem step_halt {w : ℕ} {q : Program .exact r} {t : Cslib.WordRAM.State r} {v : ℕ}
    (ht : Cslib.WordRAM.step w q t = .halt v) :
    S.step w (S.programOf q) (stateOf S t) = S.halted v := by
  have hnr := isRandFree_of_step (w := w) (q := q) (t := t) (by simp [ht])
  obtain ⟨pc, reg, mem⟩ := t
  rcases S.step_matches_at h w q pc reg mem hnr with ⟨_, _, _, _, h₂⟩ | ⟨_, h₁, h₂⟩ | ⟨_, h₂⟩ <;>
    rw [ht] at h₂ <;> cases h₂
  exact h₁

/-- **Runs agree.** A run of `k` steps of a library program is a run of `k` steps of its
translation, between the corresponding states. -/
theorem runs_map {w : ℕ} {q : Program .exact r} {s t : Cslib.WordRAM.State r} {k : ℕ}
    (hr : Runs w q s t k) :
    Relation.RelatesInSteps (fun a b => S.step w (S.programOf q) a = S.next b) (stateOf S s)
      (stateOf S t) k := by
  induction hr with
  | refl => exact .refl _
  | tail _ _ _ _ hn ih => exact .tail _ _ _ _ ih (step_next h hn)

end Machine

end ComplexityTests.Abstracts.WordRAMBridge
