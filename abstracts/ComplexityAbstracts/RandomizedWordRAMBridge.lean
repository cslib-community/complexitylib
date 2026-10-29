/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import Complexity.Algorithms.WordRAM.Quicksort
import Complexity.Algorithms.WordRAM.Quickselect

/-!
# Bridge for the randomized word-RAM, quicksort, and quickselect formal abstract

`RandomizedWordRAMAbstract.lean` defines the randomized word RAM from scratch, with fresh inductive
types for its ALU operations, instructions (including `rand`), finite-depth uniform sampling trees,
states, configurations, clocked steps and runs, worst-case time and `rand`-call budgets, and
`ENNReal`-valued expected running time.

This bridge establishes two facts:

1. **Lifting randomized quicksort and quickselect from `Basis.standard` to `Basis.exact`:**
   `Cslib.Algorithms.WordRAM.Quicksort` and `Cslib.Algorithms.WordRAM.Quickselect` are written in
   `Code .standard 16` via `ram[...]` and `Allocation`, which type over `Basis.standard`. Neither
   uses `.div` or `.mod`, and every reached `.sub` instruction `a - b` (`gt ← gt - one` in
   `partStep`; `sp ← sp - one`, `tmp ← hi - lo`, `tmp ← tmp - one` in `Quicksort.popPrefix`; and
   `len ← len - one` in `Quickselect.loadHeader`, `tmp ← hi - lo1` in `Quickselect.samplePivot`)
   satisfies `b ≤ a` (no subtraction underflows). Translating every operation symbol identically to
   `Basis.exact` (`toExactCode`) therefore preserves the structured `ProbComp` execution trees on
   the nose, transferring all guarantees of `Quicksort` and `Quickselect` to `Program .exact 16`.
2. **Polymorphic presentation correspondence (Pattern B):**
   Every presentation `S` satisfying `Laws S` matches `Cslib.WordRAM` over `Basis.exact` step for
   step (`program_surjective`, `stepRand_matches`, `runRand_matches`, `evalRand_eq`,
   `haltsWithin_iff`, `randCallsBounded_iff`, and `expectedTime_eq`). Transporting the lifted
   `Basis.exact` theorems across this correspondence yields `quicksort` and `quickselect` in
   `RandomizedWordRAMAbstract.lean` with zero project-module allowlisting.
-/

namespace ComplexityAbstracts.RandomizedWordRAMBridge

open scoped ENNReal
open Cslib
open Cslib.WordRAM
open Cslib.Algorithms.WordRAM

/-! ## Part 1: Lifting `Quicksort` from `Basis.standard` to `Basis.exact` -/

/-- Translate a `Basis.standard` data operation to the identical `Basis.exact` operation symbol. -/
def toExactOp {r : ℕ} : Op .standard r → Op .exact r
  | .const d v => .const d v
  | .copy d s => .copy d s
  | .alu f d args => .alu f d args
  | .load d a => .load d a
  | .store a s => .store a s

/-- Translate a structured `Basis.standard` program to `Basis.exact`. -/
def toExactCode {r : ℕ} : Code .standard r → Code .exact r
  | .op o => .op (toExactOp o)
  | .seq c₁ c₂ => .seq (toExactCode c₁) (toExactCode c₂)
  | .branch c pos neg => .branch c (toExactCode pos) (toExactCode neg)
  | .loop c body => .loop c (toExactCode body)
  | .rand dst src => .rand dst src

/-- Operations whose `Basis.exact` semantics agrees unconditionally with `Basis.standard`. -/
def noSubDivModOp {r : ℕ} : Op .standard r → Bool
  | .alu (.bin .sub) _ _ => false
  | .alu (.bin .div) _ _ => false
  | .alu (.bin .mod) _ _ => false
  | _ => true

/-- Structured programs containing no `.sub`, `.div`, or `.mod` instructions. -/
def noSubDivMod {r : ℕ} : Code .standard r → Bool
  | .op o => noSubDivModOp o
  | .seq c₁ c₂ => noSubDivMod c₁ && noSubDivMod c₂
  | .branch _ pos neg => noSubDivMod pos && noSubDivMod neg
  | .loop _ body => noSubDivMod body
  | .rand _ _ => true

private theorem eval_toExactOp_of_noSubDivMod {r w : ℕ} {o : Op .standard r} {x : Data r}
    (hno : noSubDivModOp o = true) :
    (toExactOp o).eval w x = o.eval w x := by
  cases o with
  | const d v | copy d s | load d a | store a s => rfl
  | alu f d args =>
    cases f with
    | width => rfl
    | bin g =>
      cases g <;> first | contradiction | rfl

private theorem eval_toExactOp_sub {r w : ℕ} {d i j : Fin r} {x : Data r}
    (hle : x.regs j ≤ x.regs i) :
    (toExactOp (Op.bin .sub d i j)).eval w x = (Op.bin .sub d i j).eval w x := by
  change (Option.bind (BinOp.evalExact .sub (x.regs i) (x.regs j)) (x.put w d)) =
    x.put w d (BinOp.eval .sub (x.regs i) (x.regs j))
  simp [BinOp.evalExact, BinOp.eval, hle]

/-- Any `Exec` of a `.sub`/`.div`/`.mod`-free structured program lifts identically to
`Basis.exact`. -/
theorem Exec.toExact_of_noSubDivMod {r w : ℕ} {c : Code .standard r} {x y : Data r} {n : ℕ}
    (h : Exec w c x y n) (hno : noSubDivMod c = true) :
    Exec w (toExactCode c) x y n := by
  induction h with
  | op ho => exact .op (by rwa [eval_toExactOp_of_noSubDivMod hno])
  | seq h₁ h₂ ih₁ ih₂ =>
    rw [noSubDivMod, Bool.and_eq_true] at hno
    exact .seq (ih₁ hno.1) (ih₂ hno.2)
  | branch_pos hc hp ih =>
    rw [noSubDivMod, Bool.and_eq_true] at hno
    exact .branch_pos hc (ih hno.1)
  | branch_neg hc hn ih =>
    rw [noSubDivMod, Bool.and_eq_true] at hno
    exact .branch_neg hc (ih hno.2)
  | loop_exit hc => exact .loop_exit hc
  | loop_iter hc hb hl ihb ihl => exact .loop_iter hc (ihb hno) (ihl hno)

/-- Any `ExecRand` of a `.sub`/`.div`/`.mod`-free structured program lifts identically to
`Basis.exact`. -/
theorem ExecRand.toExact_of_noSubDivMod {r w : ℕ} {c : Code .standard r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) (hno : noSubDivMod c = true) :
    ExecRand w (toExactCode c) x m := by
  induction h with
  | op ho => exact .op (by rwa [eval_toExactOp_of_noSubDivMod hno])
  | rand hf => exact .rand hf
  | seq h₁ h₂ ih₁ ih₂ =>
    rw [noSubDivMod, Bool.and_eq_true] at hno
    exact .seq (ih₁ hno.1) fun z hz => ih₂ z hz hno.2
  | branch_pos hc hp ih =>
    rw [noSubDivMod, Bool.and_eq_true] at hno
    exact .branch_pos hc (ih hno.1)
  | branch_neg hc hn ih =>
    rw [noSubDivMod, Bool.and_eq_true] at hno
    exact .branch_neg hc (ih hno.2)
  | loop_exit hc => exact .loop_exit hc
  | loop_iter hc hb hl ihb ihl => exact .loop_iter hc (ihb hno) fun z hz => ihl z hz hno

private def preservesReg {B : Basis} {r : ℕ} (reg : Fin r) : Code B r → Bool
  | .op (.const d _) | .op (.copy d _) | .op (.alu _ d _) | .op (.load d _) | .rand d _ =>
    d != reg
  | .op (.store _ _) => true
  | .seq c₁ c₂ | .branch _ c₁ c₂ => preservesReg reg c₁ && preservesReg reg c₂
  | .loop _ body => preservesReg reg body

private theorem op_regs_eq_of_ne {B : Basis} {r w : ℕ} {o : Op B r} {x y : Data r} {reg : Fin r}
    (ho : o.eval w x = some y) (hp : preservesReg reg (Code.op o) = true) :
    y.regs reg = x.regs reg := by
  cases o with
  | store a s =>
    cases ho
    rfl
  | copy d s | load d a =>
    have hne : d ≠ reg := by simpa [preservesReg] using hp
    cases ho
    simp [Data.set, Function.update_of_ne hne.symm]
  | const d v =>
    have hne : d ≠ reg := by simpa [preservesReg] using hp
    simp only [Op.eval, Data.put] at ho
    split_ifs at ho with hf
    cases ho
    simp [Data.set, Function.update_of_ne hne.symm]
  | alu f d args =>
    have hne : d ≠ reg := by simpa [preservesReg] using hp
    simp only [Op.eval] at ho
    cases hi : B.interp w f (x.regs ∘ args) with
    | none => simp [hi] at ho
    | some val =>
      rw [hi] at ho
      dsimp only [bind, Option.bind, Data.put] at ho
      split_ifs at ho with hf
      cases ho
      simp [Data.set, Function.update_of_ne hne.symm]

private theorem ExecRand.regs_eq_of_preserves {B : Basis} {r w : ℕ} {c : Code B r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} {reg : Fin r} (h : ExecRand w c x m)
    (hp : preservesReg reg c = true) :
    ∀ z ∈ m.support, z.1.regs reg = x.regs reg := by
  induction h with
  | op ho =>
    intro z hz
    cases OracleComp.eq_of_mem_supportWith_pure hz
    exact op_regs_eq_of_ne ho hp
  | @rand dst src x hf =>
    intro z hz
    have hne : dst ≠ reg := by simpa [preservesReg] using hp
    obtain ⟨k, -, hz'⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hz'
    simp [Data.set, Function.update_of_ne hne.symm]
  | seq h₁ h₂ ih₁ ih₂ =>
    rw [preservesReg, Bool.and_eq_true] at hp
    intro z hz
    obtain ⟨z₁, hz₁, hz₂⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z₂, hz₂', hz_eq⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₂
    cases OracleComp.eq_of_mem_supportWith_pure hz_eq
    exact (ih₂ z₁ hz₁ hp.2 z₂ hz₂').trans (ih₁ hp.1 z₁ hz₁)
  | branch_pos _ hpos ih =>
    rw [preservesReg, Bool.and_eq_true] at hp
    intro z hz
    obtain ⟨z', hz', rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    exact ih hp.1 z' hz'
  | branch_neg _ hneg ih =>
    rw [preservesReg, Bool.and_eq_true] at hp
    intro z hz
    obtain ⟨z', hz', rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    exact ih hp.2 z' hz'
  | loop_exit _ =>
    intro z hz
    cases OracleComp.eq_of_mem_supportWith_pure hz
    rfl
  | loop_iter _ hb hl ihb ihl =>
    intro z hz
    obtain ⟨z₁, hz₁, hz₂⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z₂, hz₂', hz_eq⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₂
    cases OracleComp.eq_of_mem_supportWith_pure hz_eq
    exact (ihl z₁ hz₁ hp z₂ hz₂').trans (ihb hp z₁ hz₁)

private theorem ExecRand.toExact_partStep {w : ℕ} {x : Data 16} {m : ProbComp (Data 16 × ℕ)}
    (h : ExecRand w Quicksort.partStep x m) (hone : x.regs Quicksort.Reg.one = 1)
    (hcg : (Cond.lt Quicksort.Reg.cur Quicksort.Reg.gt).Holds x) :
    ExecRand w (toExactCode Quicksort.partStep) x m := by
  have hgt_ge : 1 ≤ x.regs Quicksort.Reg.gt := by
    have hlt : x.regs Quicksort.Reg.cur < x.regs Quicksort.Reg.gt := by
      simpa [Cond.holds_lt] using hcg
    omega
  change ExecRand w (Code.seq (.op (.load Quicksort.Reg.val Quicksort.Reg.cur)) _) x m at h
  cases h with
  | @seq _ _ _ m₁ m₂ h₁ h₂ =>
    cases h₁ with
    | op ho₁ =>
      have ho₁_ex :
          (toExactOp (Op.load Quicksort.Reg.val Quicksort.Reg.cur)).eval w x = _ := ho₁
      dsimp only [Op.eval] at ho₁
      cases ho₁
      refine ExecRand.seq (.op ho₁_ex) fun z hz => ?_
      cases OracleComp.eq_of_mem_supportWith_pure hz
      have hz_one :
          (x.set Quicksort.Reg.val (x.mem (x.regs Quicksort.Reg.cur))).regs Quicksort.Reg.one =
            1 := by simp [hone]
      have hz_gt :
          1 ≤ (x.set Quicksort.Reg.val (x.mem (x.regs Quicksort.Reg.cur))).regs Quicksort.Reg.gt :=
        by simpa using hgt_ge
      have hbr := h₂ _ rfl
      generalize
        m₂ (x.set Quicksort.Reg.val (x.mem (x.regs Quicksort.Reg.cur)), 1).1 = m_br at hbr ⊢
      cases hbr with
      | branch_pos hc hp =>
        exact .branch_pos hc (ExecRand.toExact_of_noSubDivMod hp rfl)
      | branch_neg hc hn =>
        cases hn with
        | branch_pos hc' hp' =>
          cases hp' with
          | seq hsub hswap =>
            cases hsub with
            | op ho_sub =>
              exact .branch_neg hc (.branch_pos hc'
                (.seq (.op (by rw [eval_toExactOp_sub (by dsimp only; omega)]; exact ho_sub))
                  fun z' hz' => ExecRand.toExact_of_noSubDivMod (hswap z' hz') rfl))
        | branch_neg hc' hn' =>
          exact .branch_neg hc (.branch_neg hc' (ExecRand.toExact_of_noSubDivMod hn' rfl))

private theorem ExecRand.toExact_loop_aux {r w : ℕ} {cond : Cond r} {body c : Code .standard r}
    {P : Data r → Prop}
    (hstep : ∀ {x m}, ExecRand w body x m → P x → cond.Holds x → ExecRand w (toExactCode body) x m)
    (hinv : ∀ {x m}, ExecRand w body x m → P x → cond.Holds x → ∀ z ∈ m.support, P z.1)
    {x : Data r} {m : ProbComp (Data r × ℕ)} (h : ExecRand w c x m) :
    c = .loop cond body → P x → ExecRand w (toExactCode c) x m := by
  induction h with
  | loop_exit hc =>
    rintro ⟨⟩ _
    exact .loop_exit hc
  | loop_iter hc hb _ _ ihl =>
    rintro ⟨⟩ hP
    exact .loop_iter hc (hstep hb hP hc) fun z hz => ihl z hz rfl (hinv hb hP hc z hz)
  | _ =>
    intro hc_eq
    cases hc_eq

private theorem ExecRand.toExact_loop {r w : ℕ} {cond : Cond r} {body : Code .standard r}
    {P : Data r → Prop}
    (hstep : ∀ {x m}, ExecRand w body x m → P x → cond.Holds x → ExecRand w (toExactCode body) x m)
    (hinv : ∀ {x m}, ExecRand w body x m → P x → cond.Holds x → ∀ z ∈ m.support, P z.1)
    {x : Data r} {m : ProbComp (Data r × ℕ)} (h : ExecRand w (.loop cond body) x m) (hP : P x) :
    ExecRand w (toExactCode (.loop cond body)) x m :=
  ExecRand.toExact_loop_aux hstep hinv h rfl hP

private theorem ExecRand.toExact_partLoop {w : ℕ} {x : Data 16} {m : ProbComp (Data 16 × ℕ)}
    (h : ExecRand w (.loop (.lt Quicksort.Reg.cur Quicksort.Reg.gt) Quicksort.partStep) x m)
    (hone : x.regs Quicksort.Reg.one = 1) :
    ExecRand w (toExactCode (.loop (.lt Quicksort.Reg.cur Quicksort.Reg.gt) Quicksort.partStep))
      x m :=
  ExecRand.toExact_loop (P := fun d => d.regs Quicksort.Reg.one = 1)
    (fun hb hP hc => ExecRand.toExact_partStep hb hP hc)
    (fun hb hP _ z hz => (ExecRand.regs_eq_of_preserves hb rfl z hz).trans hP)
    h hone

private theorem ExecRand.toExact_partLoopAndPush {w : ℕ} {x : Data 16}
    {m : ProbComp (Data 16 × ℕ)}
    (h : ExecRand w
      (.seq (.loop (.lt Quicksort.Reg.cur Quicksort.Reg.gt) Quicksort.partStep)
        (.seq (Quicksort.pushIfNonTrivial Quicksort.Reg.lo Quicksort.Reg.lt)
          (Quicksort.pushIfNonTrivial Quicksort.Reg.gt Quicksort.Reg.hi))) x m)
    (hone : x.regs Quicksort.Reg.one = 1) :
    ExecRand w
      (toExactCode (.seq (.loop (.lt Quicksort.Reg.cur Quicksort.Reg.gt) Quicksort.partStep)
        (.seq (Quicksort.pushIfNonTrivial Quicksort.Reg.lo Quicksort.Reg.lt)
          (Quicksort.pushIfNonTrivial Quicksort.Reg.gt Quicksort.Reg.hi)))) x m := by
  cases h with
  | seq hloop hpush =>
    exact .seq (ExecRand.toExact_partLoop hloop hone) fun z₂ hz₂ =>
      ExecRand.toExact_of_noSubDivMod (hpush z₂ hz₂) rfl

private theorem ExecRand.toExact_partitionAndPush {w : ℕ} {x : Data 16}
    {m : ProbComp (Data 16 × ℕ)} (h : ExecRand w Quicksort.partitionAndPush x m)
    (hone : x.regs Quicksort.Reg.one = 1) :
    ExecRand w (toExactCode Quicksort.partitionAndPush) x m := by
  change ExecRand w
    (.seq Quicksort.partInit
      (.seq (.loop (.lt Quicksort.Reg.cur Quicksort.Reg.gt) Quicksort.partStep)
        (.seq (Quicksort.pushIfNonTrivial Quicksort.Reg.lo Quicksort.Reg.lt)
          (Quicksort.pushIfNonTrivial Quicksort.Reg.gt Quicksort.Reg.hi)))) x m at h
  cases h with
  | seq h₁ h₂ =>
    refine .seq (ExecRand.toExact_of_noSubDivMod h₁ rfl) fun z₁ hz₁ => ?_
    have hz₁_one : z₁.1.regs Quicksort.Reg.one = 1 :=
      (ExecRand.regs_eq_of_preserves h₁ rfl z₁ hz₁).trans hone
    exact ExecRand.toExact_partLoopAndPush (h₂ z₁ hz₁) hz₁_one

private theorem Exec.toExact_popPrefix {w : ℕ} {input : List ℕ} {x : Data 16}
    (hI : Quicksort.OuterInv w input x)
    (hc : (Cond.lt Quicksort.Reg.zero Quicksort.Reg.sp).Holds x) :
    ∃ p₅, Exec w Quicksort.popPrefix x p₅ 7 ∧
      Exec w (toExactCode Quicksort.popPrefix) x p₅ 7 ∧
      p₅.regs Quicksort.Reg.one = 1 := by
  open Quicksort Quicksort.Reg in
  set n := input.length
  have hfit_all : Fits w (3 * n + 3) := fits_three_mul_add_three hI.hw
  have hsp_pos : 0 < x.regs sp := by simpa [Cond.holds_lt, hI.zero_eq] using hc
  set k_sp := x.regs sp - 1
  have hsp_succ : x.regs sp = k_sp + 1 := by omega
  set S₀ := (List.range k_sp).map fun i => (x.mem (n + 1 + i), x.mem (2 * n + 1 + i))
  set vlo := x.mem (n + 1 + k_sp)
  set vhi := x.mem (2 * n + 1 + k_sp)
  have hstack_eq : readStack n x = S₀ ++ [(vlo, vhi)] := by
    simp [readStack, hsp_succ, S₀, vlo, vhi, List.range_succ]
  have hVS : ValidStack n (S₀ ++ [(vlo, vhi)]) := hstack_eq ▸ hI.valid_stack
  have hp_hi := hVS.1 (vlo, vhi) (by simp)
  have hk_lt_n : k_sp < n := by
    have h2 := hVS.two_mul_length_le
    have hS₀_len : S₀.length = k_sp := by simp [S₀]
    rw [List.length_append, List.length_singleton, hS₀_len] at h2
    omega
  have hsp6 : x.regs 6 = k_sp + 1 := hsp_succ
  set p₁ := x.set sp k_sp
  have ep₁ : Exec w (.op (.bin .sub sp sp one)) x p₁ 1 := by
    simpa [p₁, k_sp, hI.one_eq, BinOp.eval] using Exec.bin (w := w) (f := .sub) (d := sp)
      (i := sp) (j := one) (x := x)
      (hfit_all.of_le (by simp [hI.one_eq, hsp6, BinOp.eval]; omega))
  have ep₁_ex : Exec w (toExactCode (.op (.bin .sub sp sp one))) x p₁ 1 := by
    cases ep₁ with
    | op ho => exact .op (by rw [eval_toExactOp_sub (by rw [hI.one_eq, hsp_succ]; omega)]; exact ho)
  have er₁ := readAt_exec (w := w) (tmp := tmp) (dst := lo) (ptr := stackLo) (idx := sp)
    (x := p₁) (hfit_all.of_le (by simp [p₁, hI.stackLo_eq]; omega))
  have er₁_ex := Exec.toExact_of_noSubDivMod er₁ rfl
  set p₂ := (p₁.set tmp (p₁.regs stackLo + p₁.regs sp)).set lo
    (p₁.mem (p₁.regs stackLo + p₁.regs sp))
  have er₂ := readAt_exec (w := w) (tmp := tmp) (dst := hi) (ptr := stackHi) (idx := sp)
    (x := p₂) (hfit_all.of_le (by simp [p₂, p₁, hI.stackHi_eq]; omega))
  have er₂_ex := Exec.toExact_of_noSubDivMod er₂ rfl
  set p₃ := (p₂.set tmp (p₂.regs stackHi + p₂.regs sp)).set hi
    (p₂.mem (p₂.regs stackHi + p₂.regs sp))
  have hlo₃ : p₃.regs lo = vlo := by simp [p₃, p₂, p₁, hI.stackLo_eq, vlo, n]
  have hhi₃ : p₃.regs hi = vhi := by simp [p₃, p₂, p₁, hI.stackHi_eq, vhi, n]
  have ep₄ : Exec w (.op (.bin .sub tmp hi lo)) p₃ (p₃.set tmp (vhi - vlo)) 1 := by
    simpa [hhi₃, hlo₃, BinOp.eval] using Exec.bin (w := w) (f := .sub) (d := tmp) (i := hi)
      (j := lo) (x := p₃) (hfit_all.of_le (by simp [hhi₃, hlo₃, BinOp.eval]; omega))
  have ep₄_ex : Exec w (toExactCode (.op (.bin .sub tmp hi lo))) p₃ (p₃.set tmp (vhi - vlo)) 1 := by
    cases ep₄ with
    | op ho => exact .op (by rw [eval_toExactOp_sub (by rw [hlo₃, hhi₃]; omega)]; exact ho)
  set p₄ := p₃.set tmp (vhi - vlo)
  have htmp₄ : p₄.regs tmp = vhi - vlo := by simp [p₄]
  have hone₄ : p₄.regs one = 1 := by simp [p₄, p₃, p₂, p₁, hI.one_eq]
  have ep₅ : Exec w (.op (.bin .sub tmp tmp one)) p₄ (p₄.set tmp (vhi - vlo - 1)) 1 := by
    simpa [htmp₄, hone₄, BinOp.eval] using Exec.bin (w := w) (f := .sub) (d := tmp) (i := tmp)
      (j := one) (x := p₄) (hfit_all.of_le (by simp [htmp₄, hone₄, BinOp.eval]; omega))
  have ep₅_ex : Exec w (toExactCode (.op (.bin .sub tmp tmp one)))
      p₄ (p₄.set tmp (vhi - vlo - 1)) 1 := by
    cases ep₅ with
    | op ho => exact .op (by rw [eval_toExactOp_sub (by rw [htmp₄, hone₄]; omega)]; exact ho)
  set p₅ := p₄.set tmp (vhi - vlo - 1)
  exact ⟨p₅,
    ep₁.seq (er₁.seq (er₂.seq (ep₄.seq ep₅))),
    ep₁_ex.seq (er₁_ex.seq (er₂_ex.seq (ep₄_ex.seq ep₅_ex))),
    by simp [p₅, hone₄]⟩

private theorem ExecRand.toExact_rand {r w : ℕ} {dst src : Fin r} {x : Data r}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand (B := .standard) w (.rand dst src) x m) :
    ExecRand (B := .exact) w (.rand dst src) x m := by
  cases h with
  | rand hf => exact .rand hf

private theorem ExecRand.toExact_outerBody {w : ℕ} {input : List ℕ} {x : Data 16}
    {m : ProbComp (Data 16 × ℕ)} (hI : Quicksort.OuterInv w input x)
    (hc : (Cond.lt Quicksort.Reg.zero Quicksort.Reg.sp).Holds x)
    (h : ExecRand w Quicksort.outerBody x m) :
    ExecRand w (toExactCode Quicksort.outerBody) x m := by
  obtain ⟨p₅, e_pre, e_pre_ex, hp₅_one⟩ := Exec.toExact_popPrefix hI hc
  change ExecRand w
    (.seq (.seq Quicksort.popPrefix (.rand Quicksort.Reg.tmp Quicksort.Reg.tmp))
      Quicksort.partitionAndPush) x m at h
  cases h with
  | seq h_pop h_part =>
    cases h_pop with
    | @seq _ _ _ m_pre m_rand h_pre h_rand =>
      obtain rfl := h_pre.unique e_pre.execRand
      have h_rand_ex : ∀ z ∈ (pure (p₅, 7) : ProbComp (Data 16 × ℕ)).support,
          ExecRand w (toExactCode (.rand Quicksort.Reg.tmp Quicksort.Reg.tmp)) z.1
            (m_rand z.1) := by
        intro z hz
        cases OracleComp.eq_of_mem_supportWith_pure hz
        exact ExecRand.toExact_rand (h_rand (p₅, 7) rfl)
      have h_pop_ex := ExecRand.seq e_pre_ex.execRand h_rand_ex
      refine ExecRand.seq h_pop_ex fun z₁ hz₁ => ?_
      obtain ⟨z₀, hz₀, hz_r⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁
      cases OracleComp.eq_of_mem_supportWith_pure hz₀
      obtain ⟨zr, hzr, hz_eq⟩ := OracleComp.mem_supportWith_bind_iff.mp hz_r
      cases OracleComp.eq_of_mem_supportWith_pure hz_eq
      have hzr_one : zr.1.regs Quicksort.Reg.one = 1 :=
        (ExecRand.regs_eq_of_preserves (h_rand (p₅, 7) rfl) rfl zr hzr).trans hp₅_one
      exact ExecRand.toExact_partitionAndPush (h_part _ hz₁) hzr_one

private theorem countP_lt_add_gt_le {u : List ℕ} {piv : ℕ} (hpiv : piv ∈ u) :
    u.countP (· < piv) + u.countP (piv < ·) + 1 ≤ u.length := by
  induction u with
  | nil => simp at hpiv
  | cons a tl ih =>
    simp only [List.length_cons, List.countP_cons]
    rcases List.mem_cons.mp hpiv with rfl | htl
    · simp only [Nat.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte, add_zero]
      have hdisj : tl.countP (· < piv) + tl.countP (piv < ·) ≤ tl.length := by
        clear hpiv ih
        induction tl with
        | nil => simp
        | cons b rest ihr =>
          simp only [List.length_cons, List.countP_cons]
          by_cases h1 : b < piv
          · have h2 : ¬piv < b := by omega
            simp [h1, h2]; omega
          · by_cases h2 : piv < b
            · simp [h1, h2]; omega
            · simp [h1, h2]; omega
      omega
    · have hih := ih htl
      by_cases h1 : a < piv
      · have h2 : ¬piv < a := by omega
        simp [h1, h2]; omega
      · by_cases h2 : piv < a
        · simp [h1, h2]; omega
        · simp [h1, h2]; omega

/-- From any valid outer-loop state `x`, the outer loop produces the exact same `ProbComp` tree
under `Basis.standard` and `Basis.exact`, with every path bounded by `stepPotential + 2` steps. -/
private theorem outerLoop_std_and_exact {w : ℕ} {input : List ℕ} :
    ∀ (K : ℕ) (x : Data 16),
      Quicksort.callPotential input.length x ≤ K →
      Quicksort.OuterInv w input x →
      ∃ m : ProbComp (Data 16 × ℕ),
        ExecRand w (.loop (.lt Quicksort.Reg.zero Quicksort.Reg.sp) Quicksort.outerBody) x m ∧
        ExecRand w
          (toExactCode (.loop (.lt Quicksort.Reg.zero Quicksort.Reg.sp) Quicksort.outerBody)) x m ∧
        (∀ z ∈ m.support, z.2 ≤ Quicksort.stepPotential input.length x + 2) := by
  open Quicksort Quicksort.Reg in
  set n := input.length
  intro K
  induction K with
  | zero =>
    intro x hK hI
    by_cases hc : (Cond.lt zero sp).Holds x
    · obtain ⟨S₀, vlo, vhi, hstack, hge2, -⟩ := outerBody_spec hI hc
      exfalso
      rw [callPotential, hstack, List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton] at hK
      omega
    · exact ⟨pure (x, 2), .loop_exit hc, .loop_exit hc, fun z hz => by
        cases OracleComp.eq_of_mem_supportWith_pure hz; omega⟩
  | succ K ih =>
    intro x hK hI
    by_cases hc : (Cond.lt zero sp).Holds x
    · obtain ⟨S₀, vlo, vhi, hstack, hge2, y, t, hexec, hspec⟩ := outerBody_spec hI hc
      have hexec_ex := ExecRand.toExact_outerBody hI hc hexec
      let m_sub := vhi - vlo
      have hm_def : m_sub = vhi - vlo := rfl
      have hbody_step : ∀ k : Fin (vhi - vlo - 1 + 1),
          callPotential n (y k) ≤ K ∧
          (8 + t k) + 2 + stepPotential n (y k) ≤ stepPotential n x := by
        intro k
        obtain ⟨ht_le, -, hread_yk⟩ := hspec k
        let u := memSlice vlo vhi x.mem
        let m₁ := u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))
        let m₂ := u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·)
        change readStack n (y k) =
          (if 2 ≤ m₂ then (if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀) ++ [(vhi - m₂, vhi)]
           else (if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀)) at hread_yk
        have hm12_le : m₁ + m₂ ≤ m_sub - 1 := by
          have hpiv_in : u[k.val]'(by have := k.isLt; simp [u]; omega) ∈ u := List.getElem_mem _
          have hc_le := countP_lt_add_gt_le hpiv_in
          have hlen_u : u.length = m_sub := length_memSlice vlo vhi x.mem
          omega
        refine ⟨?_, ?_⟩
        · have hcall : 1 + callPotential n (y k) ≤ callPotential n x := by
            rw [callPotential, hread_yk, callPotential, hstack]
            split_ifs <;> simp only [List.map_append, List.sum_append, List.map_singleton,
              List.sum_singleton] <;> omega
          omega
        · have hquad : 11 * m_sub + 33 + (20 * m₁ ^ 2 + 20 * m₂ ^ 2) ≤ 20 * m_sub ^ 2 := by
            have hsum_sq : m₁ ^ 2 + m₂ ^ 2 ≤ (m_sub - 1) ^ 2 := by
              have : (m₁ + m₂) ^ 2 ≤ (m_sub - 1) ^ 2 := Nat.pow_le_pow_left hm12_le 2
              nlinarith
            have hbase : 11 * m_sub + 33 + 20 * (m_sub - 1) ^ 2 ≤ 20 * m_sub ^ 2 := by
              obtain ⟨d, hd⟩ : ∃ d, m_sub = d + 2 := ⟨m_sub - 2, by omega⟩
              have hd1 : m_sub - 1 = d + 1 := by omega
              rw [hd1, hd]; nlinarith
            omega
          rw [stepPotential, hread_yk, stepPotential, hstack, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton, ← hm_def]
          split_ifs
          · have hsub2 : vhi - (vhi - m₂) = m₂ := by omega
            simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
              Nat.add_sub_cancel_left, hsub2]; omega
          · have hsub2 : vhi - (vhi - m₂) = m₂ := by omega
            simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
              hsub2]; omega
          · simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
              Nat.add_sub_cancel_left]; omega
          · omega
      have hnext : ∀ d : Data 16,
          (∃ k, d = y k) →
          ∃ ml_d, ExecRand w (.loop (.lt zero sp) outerBody) d ml_d ∧
            ExecRand w (toExactCode (.loop (.lt zero sp) outerBody)) d ml_d ∧
            ∀ z ∈ ml_d.support, z.2 ≤ stepPotential n d + 2 := by
        rintro _ ⟨k, rfl⟩
        exact ih (y k) (hbody_step k).1 (hspec k).2.1
      classical
      let ml : Data 16 → ProbComp (Data 16 × ℕ) := fun d =>
        if hd : ∃ k, d = y k then (hnext d hd).choose else pure (d, 0)
      have hml_std : ∀ z ∈ (((fun k => (y k, 8 + t k)) <$>
          ProbComp.unifFin (vhi - vlo - 1))).support,
          ExecRand w (.loop (.lt zero sp) outerBody) z.1 (ml z.1) := by
        intro z hz
        obtain ⟨k, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
        have hex : ∃ k', y k = y k' := ⟨k, rfl⟩
        simpa only [ml, hex, ↓reduceDIte] using (hnext (y k) hex).choose_spec.1
      have hml_ex : ∀ z ∈ (((fun k => (y k, 8 + t k)) <$>
          ProbComp.unifFin (vhi - vlo - 1))).support,
          ExecRand w (toExactCode (.loop (.lt zero sp) outerBody)) z.1 (ml z.1) := by
        intro z hz
        obtain ⟨k, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
        have hex : ∃ k', y k = y k' := ⟨k, rfl⟩
        simpa only [ml, hex, ↓reduceDIte] using (hnext (y k) hex).choose_spec.2.1
      refine ⟨_, .loop_iter hc hexec hml_std, .loop_iter hc hexec_ex hml_ex, ?_⟩
      intro z hz
      obtain ⟨z₁, hz₁, hz₂⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
      obtain ⟨k, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz₁
      obtain ⟨z₂, hz₂', hz_eq⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₂
      cases OracleComp.eq_of_mem_supportWith_pure hz_eq
      have hex : ∃ k', y k = y k' := ⟨k, rfl⟩
      have hz₂_le : z₂.2 ≤ stepPotential n (y k) + 2 := by
        have hsup : z₂ ∈ (hnext (y k) hex).choose.support := by
          simpa only [ml, hex, ↓reduceDIte] using hz₂'
        exact (hnext (y k) hex).choose_spec.2.2 z₂ hsup
      have hb := (hbody_step k).2
      dsimp only
      omega
    · exact ⟨pure (x, 2), .loop_exit hc, .loop_exit hc, fun z hz => by
        cases OracleComp.eq_of_mem_supportWith_pure hz; omega⟩

/-- Compiled `Basis.exact` quicksort program (`(toExactCode Quicksort.code).program Reg.zero`). -/
def quicksortExactProgram : Program .exact 16 :=
  (toExactCode Quicksort.code).program Quicksort.Reg.zero

/-- All four clauses of `Quicksort.quicksort_correct_and_bounds` hold identically for
`quicksortExactProgram : Program .exact 16`. -/
theorem quicksort_exact_correct_and_bounds {w : ℕ} {input : List ℕ}
    (hw : logWidth 3 input.length ≤ w) (hfit : InputFits w input) :
    RandHaltsWithin w quicksortExactProgram (.init input) (Quicksort.worstCaseTime input.length) ∧
    RandCallsBounded w quicksortExactProgram (.init input)
      (Quicksort.worstCaseTime input.length) (input.length - 1) ∧
    (∀ cfg ∈ (runRand w quicksortExactProgram (Quicksort.worstCaseTime input.length)
        (.running (.init input))).support,
      ∃ y : Data 16, cfg = .halted 0 y ∧
        y.Bounded w ∧
        (Quicksort.memSlice 1 (input.length + 1) y.mem).Perm input ∧
        (Quicksort.memSlice 1 (input.length + 1) y.mem).Pairwise (· ≤ ·) ∧
        Modifies (Finset.Ico 1 (3 * input.length + 1)) (Data.init (r := 16) input).mem y.mem) ∧
    expectedTime w quicksortExactProgram (.init input) ≤
      (Quicksort.expectedTimeBound input.length : ℝ≥0∞) := by
  obtain ⟨x_init, t_s, he_setup, hts_le, hI_init, hstack_init⟩ := Quicksort.setup_spec hw
  have he_setup_ex : Exec w (toExactCode Quicksort.setup) (Data.init input) x_init t_s :=
    Exec.toExact_of_noSubDivMod he_setup rfl
  obtain ⟨m_loop, hm_std, hm_ex, hm_steps⟩ := outerLoop_std_and_exact
    (Quicksort.callPotential input.length x_init) x_init le_rfl hI_init
  have hcode_std : ExecRand w Quicksort.code (Data.init input)
      ((fun z => (z.1, t_s + z.2)) <$> m_loop) := he_setup.seqRand hm_std
  have hcode_ex : ExecRand w (toExactCode Quicksort.code) (Data.init input)
      ((fun z => (z.1, t_s + z.2)) <$> m_loop) := he_setup_ex.seqRand hm_ex
  have hstep_init : Quicksort.stepPotential input.length x_init ≤ 20 * input.length ^ 2 := by
    rw [Quicksort.stepPotential, hstack_init]
    split_ifs <;> simp
  have hT_bound : ∀ z ∈ (((fun z : Data 16 × ℕ => (z.1, t_s + z.2)) <$> m_loop)).support,
      z.2 + 1 ≤ Quicksort.worstCaseTime input.length := by
    intro z hz
    obtain ⟨z', hz', rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    have hz'_le := hm_steps z' hz'
    simp only [Quicksort.worstCaseTime]
    omega
  have hrun_eq : runRand w quicksortExactProgram (Quicksort.worstCaseTime input.length)
      (.running (.init input)) =
      runRand w Quicksort.program (Quicksort.worstCaseTime input.length)
        (.running (.init input)) := by
    change runRand w ((toExactCode Quicksort.code).program Quicksort.Reg.zero)
        (Quicksort.worstCaseTime input.length) (.running ⟨0, Data.init input⟩) =
      runRand w (Quicksort.code.program Quicksort.Reg.zero)
        (Quicksort.worstCaseTime input.length) (.running ⟨0, Data.init input⟩)
    rw [hcode_ex.runRand_program Quicksort.Reg.zero hT_bound,
      hcode_std.runRand_program Quicksort.Reg.zero hT_bound]
  have hexp_eq : expectedTime w quicksortExactProgram (.init input) =
      expectedTime w Quicksort.program (.init input) := by
    change expectedTime w ((toExactCode Quicksort.code).program Quicksort.Reg.zero)
        ⟨0, Data.init input⟩ =
      expectedTime w (Quicksort.code.program Quicksort.Reg.zero) ⟨0, Data.init input⟩
    rw [hcode_ex.expectedTime_program Quicksort.Reg.zero,
      hcode_std.expectedTime_program Quicksort.Reg.zero]
  obtain ⟨hHalts, hCalls, hPost, hExp⟩ := Quicksort.quicksort_correct_and_bounds hw hfit
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold RandHaltsWithin at hHalts ⊢
    rwa [hrun_eq]
  · unfold RandCallsBounded at hCalls ⊢
    rwa [hrun_eq]
  · intro cfg hcfg
    rw [hrun_eq] at hcfg
    obtain ⟨y, hcfg_eq, hbnd, hperm, hsort, -, hmod⟩ := hPost cfg hcfg
    exact ⟨y, hcfg_eq, hbnd, hperm, hsort, hmod⟩
  · rwa [hexp_eq]

/-! ### Lifting `Quickselect` from `Basis.standard` to `Basis.exact` -/

private theorem ExecRand.toExact_partitionAndNarrow {w : ℕ} {x : Data 16}
    {m : ProbComp (Data 16 × ℕ)} (h : ExecRand w Quickselect.partitionAndNarrow x m)
    (hone : x.regs Quicksort.Reg.one = 1) :
    ExecRand w (toExactCode Quickselect.partitionAndNarrow) x m := by
  change ExecRand w
    (.seq Quicksort.partInit
      (.seq (.loop (.lt Quicksort.Reg.cur Quicksort.Reg.gt) Quicksort.partStep)
        Quickselect.narrowRange)) x m at h
  cases h with
  | @seq _ _ _ m₁ m₂ h₁ h₂ =>
    refine .seq (ExecRand.toExact_of_noSubDivMod h₁ rfl) fun z₁ hz₁ => ?_
    have hz₁_one : z₁.1.regs Quicksort.Reg.one = 1 :=
      (ExecRand.regs_eq_of_preserves h₁ rfl z₁ hz₁).trans hone
    have h₂z := h₂ z₁ hz₁
    generalize m₂ z₁.1 = m_rest at h₂z ⊢
    cases h₂z with
    | seq hloop hnr =>
      exact .seq (ExecRand.toExact_partLoop hloop hz₁_one) fun z₂ hz₂ =>
        ExecRand.toExact_of_noSubDivMod (hnr z₂ hz₂) rfl

private theorem ExecRand.toExact_selectStep {w : ℕ} {x : Data 16}
    {m : ProbComp (Data 16 × ℕ)} (h : ExecRand w Quickselect.selectStep x m)
    (hone : x.regs Quicksort.Reg.one = 1)
    (hc : (Cond.lt Quickselect.Reg.lo1 Quickselect.Reg.hi).Holds x) :
    ExecRand w (toExactCode Quickselect.selectStep) x m := by
  have hle : x.regs Quickselect.Reg.lo1 ≤ x.regs Quickselect.Reg.hi := by
    have hlt : x.regs Quickselect.Reg.lo1 < x.regs Quickselect.Reg.hi := by
      simpa [Cond.holds_lt] using hc
    omega
  change ExecRand w
    (.seq (.seq (.op (.bin .sub Quickselect.Reg.tmp Quickselect.Reg.hi Quickselect.Reg.lo1))
      (.rand Quickselect.Reg.tmp Quickselect.Reg.tmp))
      Quickselect.partitionAndNarrow) x m at h
  cases h with
  | @seq _ _ _ m_samp _ hsamp hpn =>
    have hsamp_ex : ExecRand w (toExactCode Quickselect.samplePivot) x m_samp := by
      cases hsamp with
      | seq hsub hrand =>
        cases hsub with
        | op ho_sub =>
          exact .seq (.op (by rw [eval_toExactOp_sub hle]; exact ho_sub)) fun z₀ hz₀ =>
            ExecRand.toExact_rand (hrand z₀ hz₀)
    refine .seq hsamp_ex fun z₁ hz₁ => ?_
    have hz₁_one : z₁.1.regs Quicksort.Reg.one = 1 :=
      (ExecRand.regs_eq_of_preserves hsamp rfl z₁ hz₁).trans hone
    exact ExecRand.toExact_partitionAndNarrow (hpn z₁ hz₁) hz₁_one

private theorem ExecRand.toExact_selectLoop {w : ℕ} {x : Data 16} {m : ProbComp (Data 16 × ℕ)}
    (h : ExecRand w
      (.loop (.lt Quickselect.Reg.lo1 Quickselect.Reg.hi) Quickselect.selectStep) x m)
    (hone : x.regs Quicksort.Reg.one = 1) :
    ExecRand w
      (toExactCode (.loop (.lt Quickselect.Reg.lo1 Quickselect.Reg.hi) Quickselect.selectStep))
      x m :=
  ExecRand.toExact_loop (P := fun d => d.regs Quicksort.Reg.one = 1)
    (fun hb hP hc => ExecRand.toExact_selectStep hb hP hc)
    (fun hb hP _ z hz => (ExecRand.regs_eq_of_preserves hb rfl z hz).trans hP)
    h hone

private theorem selectSetup_sets_one {w : ℕ} {x : Data 16} {m : ProbComp (Data 16 × ℕ)}
    (h : ExecRand w Quickselect.selectSetup x m) :
    ∀ z ∈ m.support, z.1.regs Quicksort.Reg.one = 1 := by
  change ExecRand w (.seq (.op (.const Quickselect.Reg.one 1)) _) x m at h
  cases h with
  | seq h₁ h₂ =>
    cases h₁ with
    | op ho =>
      simp only [Op.eval, Data.put] at ho
      split_ifs at ho with hf
      cases ho
      intro z hz
      obtain ⟨z₁, hz₁, hz₂⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
      cases OracleComp.eq_of_mem_supportWith_pure hz₁
      obtain ⟨z₂, hz₂', hz_eq⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₂
      cases OracleComp.eq_of_mem_supportWith_pure hz_eq
      exact ExecRand.regs_eq_of_preserves (h₂ _ rfl) rfl z₂ hz₂'

private theorem ExecRand.toExact_selectSlice {w : ℕ} {x : Data 16} {m : ProbComp (Data 16 × ℕ)}
    (h : ExecRand w Quickselect.selectSlice x m) :
    ExecRand w (toExactCode Quickselect.selectSlice) x m := by
  change ExecRand w
    (.seq Quickselect.selectSetup
      (.seq (.loop (.lt Quickselect.Reg.lo1 Quickselect.Reg.hi) Quickselect.selectStep)
        (.op (.load Quickselect.Reg.ans Quickselect.Reg.target)))) x m at h
  cases h with
  | @seq _ _ _ m₁ m₂ hsetup hrest =>
    refine .seq (ExecRand.toExact_of_noSubDivMod hsetup rfl) fun z₁ hz₁ => ?_
    have hz₁_one := selectSetup_sets_one hsetup z₁ hz₁
    have hrz := hrest z₁ hz₁
    generalize m₂ z₁.1 = m_rest at hrz ⊢
    cases hrz with
    | seq hloop hload =>
      exact .seq (ExecRand.toExact_selectLoop hloop hz₁_one) fun z₂ hz₂ =>
        ExecRand.toExact_of_noSubDivMod (hload z₂ hz₂) rfl

private theorem Exec.toExact_loadHeader {w k : ℕ} {input : List ℕ}
    (hfit : InputFits w (k :: input)) :
    ∃ x_hdr : Data 16,
      Exec w Quickselect.loadHeader (Data.init (k :: input)) x_hdr 4 ∧
      Exec w (toExactCode Quickselect.loadHeader) (Data.init (k :: input)) x_hdr 4 := by
  open Quickselect Quickselect.Reg in
  obtain ⟨x_hdr, e_hdr, -, hone_hdr, -, -⟩ := loadHeader_spec hfit
  refine ⟨x_hdr, e_hdr, ?_⟩
  generalize (4 : ℕ) = n_hdr at e_hdr ⊢
  cases e_hdr with
  | @seq _ _ _ s₁ _ _ _ e₁ e₂₃₄ =>
    cases e₂₃₄ with
    | seq e₂ e₃₄ =>
      cases e₃₄ with
      | @seq _ _ _ s₃ _ _ _ e₃ e₄ =>
        have hs₁_len : s₁.regs len = input.length + 1 := by
          cases e₁ with
          | op ho₁ =>
            simp only [Op.eval, Data.init_regs, Data.init_mem_zero, List.length_cons] at ho₁
            cases ho₁
            simp only [Data.set_regs, Function.update_self]
        have hs₃_len : s₃.regs len = input.length + 1 :=
          ((e₂.seq e₃).regs_eq (by decide)).trans hs₁_len
        have hs₃_one : s₃.regs one = 1 :=
          (e₄.regs_eq (by decide)).symm.trans hone_hdr
        cases e₄ with
        | op ho₄ =>
          exact (Exec.toExact_of_noSubDivMod e₁ rfl).seq
            ((Exec.toExact_of_noSubDivMod e₂ rfl).seq
              ((Exec.toExact_of_noSubDivMod e₃ rfl).seq
                (.op (by rw [eval_toExactOp_sub (by rw [hs₃_len, hs₃_one]; omega)]; exact ho₄))))

private theorem ExecRand.toExact_quickselectCode {w k : ℕ} {input : List ℕ}
    {m : ProbComp (Data 16 × ℕ)} (hfit : InputFits w (k :: input))
    (h : ExecRand w Quickselect.code (Data.init (k :: input)) m) :
    ExecRand w (toExactCode Quickselect.code) (Data.init (k :: input)) m := by
  obtain ⟨x_hdr, e_hdr, e_hdr_ex⟩ := Exec.toExact_loadHeader hfit
  change ExecRand w
    (.seq Quickselect.loadHeader
      (.branch (.lt Quickselect.Reg.rk Quickselect.Reg.len)
        (.seq (.op (.bin .add Quickselect.Reg.base Quickselect.Reg.one Quickselect.Reg.one))
          Quickselect.selectSlice)
        (.op (.const Quickselect.Reg.ans 0)))) (Data.init (k :: input)) m at h
  cases h with
  | @seq _ _ _ m_hdr m_br h_hdr h_br =>
    obtain rfl := h_hdr.unique e_hdr.execRand
    refine ExecRand.seq e_hdr_ex.execRand fun z hz => ?_
    cases OracleComp.eq_of_mem_supportWith_pure hz
    have hbr := h_br (x_hdr, 4) rfl
    generalize m_br (x_hdr, 4).1 = mbr at hbr ⊢
    cases hbr with
    | branch_pos hc hp =>
      cases hp with
      | seq hbase hslice =>
        exact .branch_pos hc (.seq (ExecRand.toExact_of_noSubDivMod hbase rfl) fun z₁ hz₁ =>
          ExecRand.toExact_selectSlice (hslice z₁ hz₁))
    | branch_neg hc hn =>
      exact .branch_neg hc (ExecRand.toExact_of_noSubDivMod hn rfl)

/-- Compiled `Basis.exact` quickselect program (`(toExactCode Quickselect.code).program ans`). -/
def quickselectExactProgram : Program .exact 16 :=
  (toExactCode Quickselect.code).program Quickselect.Reg.ans

/-- All four clauses of `Quickselect.quickselect_correct_and_bounds` hold identically for
`quickselectExactProgram : Program .exact 16`. -/
theorem quickselect_exact_correct_and_bounds {w k : ℕ} {input : List ℕ}
    (hk : k < input.length) (hw : logWidth 2 input.length ≤ w)
    (hfit : InputFits w (k :: input)) :
    RandHaltsWithin w quickselectExactProgram (.init (k :: input))
      (Quickselect.worstCaseTime input.length) ∧
    RandCallsBounded w quickselectExactProgram (.init (k :: input))
      (Quickselect.worstCaseTime input.length) (input.length - 1) ∧
    (∀ cfg ∈ (runRand w quickselectExactProgram (Quickselect.worstCaseTime input.length)
        (.running (.init (k :: input)))).support,
      ∃ y : Data 16,
        cfg = .halted (input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk)) y ∧
        y.Bounded w ∧
        (Quicksort.memSlice 2 (input.length + 2) y.mem).Perm input ∧
        y.mem (2 + k) = input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) ∧
        (∀ i < k, y.mem (2 + i) ≤ y.mem (2 + k)) ∧
        (∀ i, k < i → i < input.length → y.mem (2 + k) ≤ y.mem (2 + i)) ∧
        Modifies (Finset.Ico 2 (input.length + 2))
          (Data.init (r := 16) (k :: input)).mem y.mem) ∧
    expectedTime w quickselectExactProgram (.init (k :: input)) ≤
      (Quickselect.expectedTimeBound input.length : ℝ≥0∞) := by
  obtain ⟨⟨m_code, hcode_std, -, hT_raw⟩, -⟩ := Quickselect.code_spec hk hw hfit
  have hcode_ex := ExecRand.toExact_quickselectCode hfit hcode_std
  have hT_bound : ∀ z ∈ m_code.support, z.2 + 1 ≤ Quickselect.worstCaseTime input.length := by
    intro z hz
    have hz_le := (hT_raw z hz).2
    simp only [Quickselect.worstCaseTime]
    omega
  have hrun_eq : runRand w quickselectExactProgram (Quickselect.worstCaseTime input.length)
      (.running (.init (k :: input))) =
      runRand w Quickselect.program (Quickselect.worstCaseTime input.length)
        (.running (.init (k :: input))) := by
    change runRand w ((toExactCode Quickselect.code).program Quickselect.Reg.ans)
        (Quickselect.worstCaseTime input.length) (.running ⟨0, Data.init (k :: input)⟩) =
      runRand w (Quickselect.code.program Quickselect.Reg.ans)
        (Quickselect.worstCaseTime input.length) (.running ⟨0, Data.init (k :: input)⟩)
    rw [hcode_ex.runRand_program Quickselect.Reg.ans hT_bound,
      hcode_std.runRand_program Quickselect.Reg.ans hT_bound]
  have hexp_eq : expectedTime w quickselectExactProgram (.init (k :: input)) =
      expectedTime w Quickselect.program (.init (k :: input)) := by
    change expectedTime w ((toExactCode Quickselect.code).program Quickselect.Reg.ans)
        ⟨0, Data.init (k :: input)⟩ =
      expectedTime w (Quickselect.code.program Quickselect.Reg.ans) ⟨0, Data.init (k :: input)⟩
    rw [hcode_ex.expectedTime_program Quickselect.Reg.ans,
      hcode_std.expectedTime_program Quickselect.Reg.ans]
  obtain ⟨hHalts, hCalls, hPost, hExp⟩ := Quickselect.quickselect_correct_and_bounds hk hw hfit
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold RandHaltsWithin at hHalts ⊢
    rwa [hrun_eq]
  · unfold RandCallsBounded at hCalls ⊢
    rwa [hrun_eq]
  · intro cfg hcfg
    rw [hrun_eq] at hcfg
    exact hPost cfg hcfg
  · rwa [hexp_eq]

/-- Out-of-range (`input.length ≤ k`) deterministic `8`-step halting for
`quickselectExactProgram : Program .exact 16`. -/
theorem quickselect_exact_out_of_range {w k : ℕ} {input : List ℕ}
    (hk : input.length ≤ k) (hfit : InputFits w (k :: input)) :
    RandHaltsWithin w quickselectExactProgram (.init (k :: input)) 8 ∧
    RandCallsBounded w quickselectExactProgram (.init (k :: input)) 8 0 ∧
    (∀ cfg ∈ (runRand w quickselectExactProgram 8 (.running (.init (k :: input)))).support,
      ∃ y : Data 16, cfg = .halted 0 y ∧ y.Bounded w ∧
        y.mem = (Data.init (r := 16) (k :: input)).mem) ∧
    expectedTime w quickselectExactProgram (.init (k :: input)) = 8 := by
  obtain ⟨y_out, e_std, hy_ans, hmem_out⟩ := Quickselect.code_out_of_range_spec hk hfit
  have hm_std : ExecRand w Quickselect.code (Data.init (k :: input)) (pure (y_out, 7)) :=
    e_std.execRand
  have hm_ex : ExecRand w (toExactCode Quickselect.code) (Data.init (k :: input))
      (pure (y_out, 7)) :=
    ExecRand.toExact_quickselectCode hfit hm_std
  have hT_bound : ∀ z ∈ (pure (y_out, 7) : ProbComp (Data 16 × ℕ)).support, z.2 + 1 ≤ 8 := by
    intro z hz
    cases OracleComp.eq_of_mem_supportWith_pure hz
    omega
  have hrun_ex : runRand w quickselectExactProgram 8 (.running (.init (k :: input))) =
      pure (.halted 0 y_out) := by
    change runRand w ((toExactCode Quickselect.code).program Quickselect.Reg.ans) 8
      (.running ⟨0, Data.init (k :: input)⟩) = _
    rw [hm_ex.runRand_program Quickselect.Reg.ans hT_bound]
    simp only [map_pure, hy_ans]
  have hexp_eq : expectedTime w quickselectExactProgram (.init (k :: input)) =
      expectedTime w Quickselect.program (.init (k :: input)) := by
    change expectedTime w ((toExactCode Quickselect.code).program Quickselect.Reg.ans)
        ⟨0, Data.init (k :: input)⟩ =
      expectedTime w (Quickselect.code.program Quickselect.Reg.ans) ⟨0, Data.init (k :: input)⟩
    rw [hm_ex.expectedTime_program Quickselect.Reg.ans,
      hm_std.expectedTime_program Quickselect.Reg.ans]
  obtain ⟨-, -, -, -, hExp⟩ := Quickselect.quickselect_out_of_range hk hfit
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cfg hcfg
    rw [hrun_ex] at hcfg
    cases OracleComp.eq_of_mem_supportWith_pure hcfg
    exact ⟨0, y_out, rfl⟩
  · rw [RandCallsBounded, hrun_ex]
    exact .pure _ 0
  · intro cfg hcfg
    have hbnd := runRand_bounded_init hfit hcfg
    rw [hrun_ex] at hcfg
    cases OracleComp.eq_of_mem_supportWith_pure hcfg
    exact ⟨y_out, rfl, hbnd.2, hmem_out⟩
  · rwa [hexp_eq]

/-! ## Part 2: Polymorphic presentation correspondence (Pattern B) -/

/-- Polymorphic signature of an abstract presentation of the randomized exact word RAM. -/
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
  rand {r : ℕ} : Fin r → Fin r → Instr r
  instr_induction {r : ℕ} {P : Instr r → Prop} :
    (∀ d x, P (const d x)) → (∀ d i, P (copy d i)) → (∀ f d i j, P (alu f d i j)) →
    (∀ d, P (width d)) → (∀ d a, P (load d a)) → (∀ a i, P (store a i)) →
    (∀ t, P (jump t)) → (∀ i j t, P (branchEq i j t)) → (∀ i j t, P (branchLt i j t)) →
    (∀ i, P (halt i)) → (∀ d i, P (rand d i)) → ∀ i, P i
  Comp : Type → Type
  compPure {α : Type} : α → Comp α
  compSample {α : Type} : (n : ℕ) → (Fin (n + 1) → Comp α) → Comp α
  compBind {α β : Type} : Comp α → (α → Comp β) → Comp β
  compEval {α : Type} : Comp α → PMF α
  CallsAtMost {α : Type} : Comp α → ℕ → Prop
  State : ℕ → Type
  state {r : ℕ} : ℕ → (Fin r → ℕ) → (ℕ → ℕ) → State r
  Cfg : ℕ → Type
  running {r : ℕ} : State r → Cfg r
  halted {r : ℕ} : ℕ → (Fin r → ℕ) → (ℕ → ℕ) → Cfg r
  faulted {r : ℕ} : Cfg r
  stepRand {r : ℕ} : ℕ → List (Instr r) → Cfg r → Comp (Cfg r)
  runRand {r : ℕ} : ℕ → List (Instr r) → ℕ → Cfg r → Comp (Cfg r)

/-- Equational specification for a randomized word-RAM presentation. -/
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
  compBind_pure : ∀ {α β : Type} (a : α) (f : α → S.Comp β),
    S.compBind (S.compPure a) f = f a
  compBind_sample : ∀ {α β : Type} (n : ℕ) (next : Fin (n + 1) → S.Comp α) (f : α → S.Comp β),
    S.compBind (S.compSample n next) f = S.compSample n fun k => S.compBind (next k) f
  compEval_pure : ∀ {α : Type} (a : α), S.compEval (S.compPure a) = PMF.pure a
  compEval_sample : ∀ {α : Type} (n : ℕ) (next : Fin (n + 1) → S.Comp α),
    S.compEval (S.compSample n next) =
      (Cslib.Probability.PMF.uniformOfFintype (Fin (n + 1))).bind fun k => S.compEval (next k)
  callsAtMost_pure : ∀ {α : Type} (a : α) (R : ℕ), S.CallsAtMost (S.compPure a) R
  callsAtMost_sample_zero : ∀ {α : Type} (n : ℕ) (next : Fin (n + 1) → S.Comp α),
    ¬S.CallsAtMost (S.compSample n next) 0
  callsAtMost_sample_succ : ∀ {α : Type} (n : ℕ) (next : Fin (n + 1) → S.Comp α) (R : ℕ),
    S.CallsAtMost (S.compSample n next) (R + 1) ↔ ∀ k, S.CallsAtMost (next k) R
  running_ne_halted : ∀ {r : ℕ} {s : S.State r} {v : ℕ} {reg : Fin r → ℕ} {mem : ℕ → ℕ},
    S.running s ≠ S.halted v reg mem
  running_ne_faulted : ∀ {r : ℕ} {s : S.State r}, S.running s ≠ S.faulted
  halted_ne_faulted : ∀ {r : ℕ} {v : ℕ} {reg : Fin r → ℕ} {mem : ℕ → ℕ},
    S.halted v reg mem ≠ S.faulted
  stepRand_halted : ∀ {r w : ℕ} {p : List (S.Instr r)} {v : ℕ} {reg : Fin r → ℕ} {mem : ℕ → ℕ},
    S.stepRand w p (S.halted v reg mem) = S.compPure (S.halted v reg mem)
  stepRand_faulted : ∀ {r w : ℕ} {p : List (S.Instr r)},
    S.stepRand w p S.faulted = S.compPure S.faulted
  stepRand_none : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem}, p[pc]? = none →
    S.stepRand w p (S.running (S.state pc reg mem)) = S.compPure S.faulted
  stepRand_const : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem d x},
    p[pc]? = some (S.const d x) →
    S.stepRand w p (S.running (S.state pc reg mem)) =
      if x < 2 ^ w then S.compPure (S.running (S.state (pc + 1) (Function.update reg d x) mem))
      else S.compPure S.faulted
  stepRand_copy : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem d i},
    p[pc]? = some (S.copy d i) →
    S.stepRand w p (S.running (S.state pc reg mem)) =
      S.compPure (S.running (S.state (pc + 1) (Function.update reg d (reg i)) mem))
  stepRand_alu_none : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem f d i j},
    p[pc]? = some (S.alu f d i j) → S.eval f (reg i) (reg j) = none →
    S.stepRand w p (S.running (S.state pc reg mem)) = S.compPure S.faulted
  stepRand_alu_some : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem f d i j x},
    p[pc]? = some (S.alu f d i j) → S.eval f (reg i) (reg j) = some x →
    S.stepRand w p (S.running (S.state pc reg mem)) =
      if x < 2 ^ w then S.compPure (S.running (S.state (pc + 1) (Function.update reg d x) mem))
      else S.compPure S.faulted
  stepRand_width : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem d},
    p[pc]? = some (S.width d) →
    S.stepRand w p (S.running (S.state pc reg mem)) =
      S.compPure (S.running (S.state (pc + 1) (Function.update reg d w) mem))
  stepRand_load : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem d a},
    p[pc]? = some (S.load d a) →
    S.stepRand w p (S.running (S.state pc reg mem)) =
      S.compPure (S.running (S.state (pc + 1) (Function.update reg d (mem (reg a))) mem))
  stepRand_store : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem a i},
    p[pc]? = some (S.store a i) →
    S.stepRand w p (S.running (S.state pc reg mem)) =
      S.compPure (S.running (S.state (pc + 1) reg (Function.update mem (reg a) (reg i))))
  stepRand_jump : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem t},
    p[pc]? = some (S.jump t) →
    S.stepRand w p (S.running (S.state pc reg mem)) =
      S.compPure (S.running (S.state t reg mem))
  stepRand_branchEq : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem i j t},
    p[pc]? = some (S.branchEq i j t) →
    S.stepRand w p (S.running (S.state pc reg mem)) =
      S.compPure (S.running (S.state (if reg i = reg j then t else pc + 1) reg mem))
  stepRand_branchLt : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem i j t},
    p[pc]? = some (S.branchLt i j t) →
    S.stepRand w p (S.running (S.state pc reg mem)) =
      S.compPure (S.running (S.state (if reg i < reg j then t else pc + 1) reg mem))
  stepRand_halt : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem i},
    p[pc]? = some (S.halt i) →
    S.stepRand w p (S.running (S.state pc reg mem)) =
      S.compPure (S.halted (reg i) reg mem)
  stepRand_rand : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem d i},
    p[pc]? = some (S.rand d i) →
    S.stepRand w p (S.running (S.state pc reg mem)) =
      if reg i < 2 ^ w then
        S.compSample (reg i) fun k =>
          S.compPure (S.running (S.state (pc + 1) (Function.update reg d k.val) mem))
      else S.compPure S.faulted
  runRand_zero : ∀ {r w : ℕ} {p : List (S.Instr r)} {cfg : S.Cfg r},
    S.runRand w p 0 cfg = S.compPure cfg
  runRand_succ : ∀ {r w : ℕ} {p : List (S.Instr r)} {T : ℕ} {cfg : S.Cfg r},
    S.runRand w p (T + 1) cfg = S.compBind (S.stepRand w p cfg) (S.runRand w p T)

namespace Presentation

variable (S : Presentation) {r : ℕ}

/-- Initial memory on input `input`: `k, x₁, …, xₖ` at `0, 1, …, k`, then `0`. -/
def initMem (input : List ℕ) : ℕ → ℕ :=
  fun a => (input.length :: input).getD a 0

/-- Start state on input `input`, as in the abstract. -/
def init (input : List ℕ) : S.State r :=
  S.state 0 (fun _ => 0) (initMem input)

/-- Input fits word size `w`, as in the abstract. -/
def InputFits (w : ℕ) (input : List ℕ) : Prop :=
  input.length < 2 ^ w ∧ ∀ x ∈ input, x < 2 ^ w

/-- `T`-step configuration distribution from state `s`, as in the abstract. -/
noncomputable def evalRand (w : ℕ) (p : List (S.Instr r)) (T : ℕ) (s : S.State r) :
    PMF (S.Cfg r) :=
  S.compEval (S.runRand w p T (S.running s))

/-- Worst-case halting within `T` steps, as in the abstract. -/
def HaltsWithin (w : ℕ) (p : List (S.Instr r)) (s : S.State r) (T : ℕ) : Prop :=
  ∀ cfg ∈ (S.evalRand w p T s).support, ∃ v reg mem, cfg = S.halted v reg mem

/-- Worst-case `rand`-call bound within `T` steps, as in the abstract. -/
def RandCallsBounded (w : ℕ) (p : List (S.Instr r)) (s : S.State r) (T R : ℕ) : Prop :=
  S.CallsAtMost (S.runRand w p T (S.running s)) R

/-- Expected running time in `ENNReal`, as in the abstract. -/
noncomputable def expectedTime (w : ℕ) (p : List (S.Instr r)) (s : S.State r) : ℝ≥0∞ :=
  ∑' t : ℕ, (S.evalRand w p t s).toOuterMeasure {cfg | ∃ u, cfg = S.running u}

/-- Memory slice `mem[a .. b)`, as in the abstract. -/
def slice (a b : ℕ) (mem : ℕ → ℕ) : List ℕ :=
  (List.range (b - a)).map fun i => mem (a + i)

/-! ### Sampling-tree translation (`ProbComp` → `S.Comp`) -/

/-- Translate a `ProbComp α` computation tree to `S.Comp α`. -/
def compOf {α : Type} : ProbComp α → S.Comp α
  | .pure a => S.compPure a
  | .liftBind n cont => S.compSample n fun k => compOf (cont k)

@[simp]
theorem compOf_pure {α : Type} (a : α) :
    S.compOf (pure a : ProbComp α) = S.compPure a := rfl

@[simp]
theorem compOf_liftBind {α : Type} (n : ℕ) (cont : Fin (n + 1) → ProbComp α) :
    S.compOf (PFunctor.FreeM.liftBind n cont) =
      S.compSample n fun k => S.compOf (cont k) := rfl

@[simp]
theorem compOf_unifFin (n : ℕ) :
    S.compOf (ProbComp.unifFin n) = S.compSample n S.compPure := rfl

theorem compOf_bind {S : Presentation} (h : Laws S) {α β : Type} (m : ProbComp α)
    (f : α → ProbComp β) :
    S.compOf (m >>= f) = S.compBind (S.compOf m) (fun a => S.compOf (f a)) := by
  induction m with
  | pure a =>
    change S.compOf (f a) = S.compBind (S.compPure a) (fun a => S.compOf (f a))
    exact (h.compBind_pure a fun a => S.compOf (f a)).symm
  | liftBind n cont ih =>
    change S.compSample n (fun k => S.compOf (cont k >>= f)) =
      S.compBind (S.compSample n fun k => S.compOf (cont k)) (fun a => S.compOf (f a))
    rw [h.compBind_sample]
    exact congrArg (S.compSample n) (funext ih)

theorem compOf_map {S : Presentation} (h : Laws S) {α β : Type} (f : α → β) (m : ProbComp α) :
    S.compOf (f <$> m) = S.compBind (S.compOf m) (fun a => S.compPure (f a)) := by
  rw [← bind_pure_comp]
  exact S.compOf_bind h m (fun a => pure (f a))

theorem compEval_compOf {S : Presentation} (h : Laws S) {α : Type} (m : ProbComp α) :
    S.compEval (S.compOf m) = m.eval := by
  induction m with
  | pure a => exact h.compEval_pure a
  | liftBind n cont ih =>
    have hbind : (PFunctor.FreeM.liftBind n cont : ProbComp α) = ProbComp.unifFin n >>= cont := rfl
    rw [compOf_liftBind, hbind, h.compEval_sample, ProbComp.eval_bind, ProbComp.eval_unifFin]
    exact congrArg _ (funext ih)

theorem callsAtMost_compOf {S : Presentation} (h : Laws S) {α : Type} (m : ProbComp α) (R : ℕ) :
    S.CallsAtMost (S.compOf m) R ↔ m.IsQueryBounded R := by
  induction m generalizing R with
  | pure a =>
    exact ⟨fun _ => .pure a R, fun _ => h.callsAtMost_pure a R⟩
  | liftBind n cont ih =>
    rw [compOf_liftBind, OracleComp.IsQueryBounded, OracleComp.IsCostBounded.liftBind_iff]
    cases R with
    | zero =>
      exact ⟨fun hc => (h.callsAtMost_sample_zero n _ hc).elim, fun ⟨hle, _⟩ => by omega⟩
    | succ R =>
      rw [h.callsAtMost_sample_succ, Nat.add_sub_cancel]
      exact ⟨fun hc => ⟨by omega, fun k => (ih k R).mp (hc k)⟩,
        fun ⟨_, hcont⟩ k => (ih k R).mpr (hcont k)⟩

/-! ### Instruction, program, and configuration translation -/

/-- Translate a standard binary operation to an abstract ALU operation. -/
def aluOpOf : BinOp → S.AluOp
  | .add => S.add | .sub => S.sub | .mul => S.mul | .div => S.div | .mod => S.mod
  | .and => S.and | .or => S.or | .xor => S.xor | .shiftLeft => S.shl | .shiftRight => S.shr

theorem aluOpOf_surjective (f : S.AluOp) : ∃ g, S.aluOpOf g = f :=
  S.aluOp_induction (P := fun f => ∃ g, S.aluOpOf g = f) ⟨.add, rfl⟩ ⟨.sub, rfl⟩ ⟨.mul, rfl⟩
    ⟨.div, rfl⟩ ⟨.mod, rfl⟩ ⟨.and, rfl⟩ ⟨.or, rfl⟩ ⟨.xor, rfl⟩ ⟨.shiftLeft, rfl⟩
    ⟨.shiftRight, rfl⟩ f

theorem eval_aluOpOf {S : Presentation} (h : Laws S) (g : BinOp) (x y : ℕ) :
    S.eval (S.aluOpOf g) x y = g.evalExact x y := by
  cases g <;> simp [aluOpOf, h.eval_add, h.eval_sub, h.eval_mul, h.eval_div, h.eval_mod,
    h.eval_and, h.eval_or, h.eval_xor, h.eval_shl, h.eval_shr, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]

/-- Translate a `Cslib.WordRAM` instruction over `Basis.exact` to an abstract instruction. -/
def instrOf : Cslib.WordRAM.Instr .exact r → S.Instr r
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
  | .rand d i => S.rand d i

/-- Translate a library `Program .exact r` to an abstract program. -/
def programOf (q : Program .exact r) : List (S.Instr r) :=
  q.map S.instrOf

theorem instrOf_surjective (i : S.Instr r) :
    ∃ j : Cslib.WordRAM.Instr .exact r, S.instrOf j = i := by
  refine S.instr_induction (P := fun i => ∃ j, S.instrOf j = i)
    (fun d x => ⟨.op (.const d x), rfl⟩)
    (fun d i => ⟨.op (.copy d i), rfl⟩) ?_
    (fun d => ⟨.op (.exactWidth d), rfl⟩)
    (fun d a => ⟨.op (.load d a), rfl⟩)
    (fun a i => ⟨.op (.store a i), rfl⟩)
    (fun t => ⟨.jump t, rfl⟩)
    (fun i j t => ⟨.branch (.eq i j) t, rfl⟩)
    (fun i j t => ⟨.branch (.lt i j) t, rfl⟩)
    (fun i => ⟨.halt i, rfl⟩)
    (fun d i => ⟨.rand d i, rfl⟩) i
  intro f d i j
  obtain ⟨g, rfl⟩ := S.aluOpOf_surjective f
  exact ⟨.op (.exactBin g d i j), rfl⟩

/-- Every abstract program is the translation of a library `Program .exact r`. -/
theorem program_surjective (p : List (S.Instr r)) :
    ∃ q : Program .exact r, S.programOf q = p := by
  choose f hf using S.instrOf_surjective (r := r)
  refine ⟨p.map f, ?_⟩
  simp only [programOf, List.map_map]
  conv_rhs => rw [← List.map_id p]
  congr 1
  funext i
  exact hf i

/-- Translate a library randomized configuration `Cslib.WordRAM.RandCfg r` to `S.Cfg r`. -/
def cfgOf : Cslib.WordRAM.RandCfg r → S.Cfg r
  | .running ⟨pc, ⟨reg, mem⟩⟩ => S.running (S.state pc reg mem)
  | .halted v ⟨reg, mem⟩ => S.halted v reg mem
  | .faulted => S.faulted

/-! ### Step, run, distribution, budget, and expected-time agreement -/

/-- One randomized step of `S.programOf q` matches `Cslib.WordRAM.stepRand` up to `cfgOf` and
`compOf`. -/
theorem stepRand_matches {S : Presentation} (h : Laws S) (w : ℕ) (q : Program .exact r)
    (cfg : Cslib.WordRAM.RandCfg r) :
    S.stepRand w (S.programOf q) (S.cfgOf cfg) =
      S.compOf (S.cfgOf <$> Cslib.WordRAM.stepRand w q cfg) := by
  rcases cfg with ⟨pc, ⟨reg, mem⟩⟩ | ⟨v, ⟨reg, mem⟩⟩ | _
  · have hget := List.getElem?_map (f := S.instrOf) (l := q) (i := pc)
    change (S.programOf q)[pc]? = _ at hget
    rcases hq : q[pc]? with _ | j
    · rw [hq, Option.map_none] at hget
      change S.stepRand w (S.programOf q) (S.running (S.state pc reg mem)) = _
      rw [h.stepRand_none hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, cfgOf]
    rw [hq, Option.map_some] at hget
    change S.stepRand w (S.programOf q) (S.running (S.state pc reg mem)) = _
    match j, hget with
    | .op (.const d x), hget =>
      rw [h.stepRand_const hget]
      by_cases hx : x < 2 ^ w <;>
        simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval, Data.put,
          Fits, hx, Data.set, cfgOf]
    | .op (.copy d i), hget =>
      rw [h.stepRand_copy hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval, Data.set,
        cfgOf]
    | .op (.alu (.bin g) d args), hget =>
      have he := S.eval_aluOpOf h g (reg (args (0 : Fin 2))) (reg (args (1 : Fin 2)))
      have hlib : StandardOp.evalExact w (.bin g) (reg ∘ args) =
          g.evalExact (reg (args (0 : Fin 2))) (reg (args (1 : Fin 2))) := rfl
      cases hg : g.evalExact (reg (args (0 : Fin 2))) (reg (args (1 : Fin 2))) with
      | none =>
        rw [hg] at he
        rw [h.stepRand_alu_none hget he]
        simp only [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval,
          Basis.exact, hlib, hg, bind, Option.bind_none]
        rfl
      | some x =>
        rw [hg] at he
        rw [h.stepRand_alu_some hget he]
        by_cases hx : x < 2 ^ w
        · simp only [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval,
            Basis.exact, hlib, hg]
          simp [Data.put, Fits, hx, Data.set, cfgOf]
        · simp only [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval,
            Basis.exact, hlib, hg]
          simp [Data.put, Fits, hx, cfgOf]
    | .op (.alu .width d args), hget =>
      rw [h.stepRand_width hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval,
        Basis.exact, StandardOp.evalExact, Data.put, Fits, Data.set, Nat.lt_two_pow_self, cfgOf]
    | .op (.load d a), hget =>
      rw [h.stepRand_load hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval, Data.set,
        cfgOf]
    | .op (.store a i), hget =>
      rw [h.stepRand_store hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval,
        Data.write, cfgOf]
    | .jump t, hget =>
      rw [h.stepRand_jump hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, cfgOf]
    | .branch (.eq i j) t, hget =>
      rw [h.stepRand_branchEq hget]
      by_cases hij : reg i = reg j <;>
        simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Cond.Holds, hij,
          cfgOf]
    | .branch (.lt i j) t, hget =>
      rw [h.stepRand_branchLt hget]
      by_cases hij : reg i < reg j <;>
        simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Cond.Holds, hij,
          cfgOf]
    | .halt i, hget =>
      rw [h.stepRand_halt hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, cfgOf]
    | .rand d i, hget =>
      rw [h.stepRand_rand hget]
      by_cases hx : reg i < 2 ^ w
      · simp only [Cslib.WordRAM.stepRand, hq, Fits, hx, ↓reduceIte, Data.set]
        rw [S.compOf_map h, S.compOf_bind h]
        simp [compOf_unifFin, h.compBind_sample, h.compBind_pure, cfgOf]
      · simp [Cslib.WordRAM.stepRand, hq, Fits, hx, cfgOf]
  · change S.stepRand w (S.programOf q) (S.halted v reg mem) = _
    rw [h.stepRand_halted]
    rfl
  · change S.stepRand w (S.programOf q) S.faulted = _
    rw [h.stepRand_faulted]
    rfl

theorem compBind_compOf_map {S : Presentation} (h : Laws S) {α β γ : Type} (f : α → β)
    (m : ProbComp α) (g : β → S.Comp γ) :
    S.compBind (S.compOf (f <$> m)) g = S.compBind (S.compOf m) (fun a => g (f a)) := by
  rw [S.compOf_map h]
  induction m with
  | pure a => simp [compOf, h.compBind_pure]
  | liftBind n cont ih =>
    rw [compOf_liftBind, h.compBind_sample, h.compBind_sample, h.compBind_sample]
    exact congrArg (S.compSample n) (funext ih)

/-- Clocked `T`-step runs of `S.programOf q` match `Cslib.WordRAM.runRand` up to `cfgOf` and
`compOf`. -/
theorem runRand_matches {S : Presentation} (h : Laws S) (w : ℕ) (q : Program .exact r) (T : ℕ)
    (cfg : Cslib.WordRAM.RandCfg r) :
    S.runRand w (S.programOf q) T (S.cfgOf cfg) =
      S.compOf (S.cfgOf <$> Cslib.WordRAM.runRand w q T cfg) := by
  induction T generalizing cfg with
  | zero =>
    rw [h.runRand_zero, Cslib.WordRAM.runRand_zero]
    rfl
  | succ T ih =>
    rw [h.runRand_succ, S.stepRand_matches h w q cfg, S.compBind_compOf_map h,
      Cslib.WordRAM.runRand_succ, ← bind_pure_comp, bind_assoc, S.compOf_bind h]
    exact congrArg (S.compBind _) (funext fun cfg' => by rw [bind_pure_comp, ih cfg'])

/-- `T`-step output distribution of `S.programOf q` is the pushforward of `Cslib.WordRAM.evalRand`
along `cfgOf`. -/
theorem evalRand_eq {S : Presentation} (h : Laws S) (w : ℕ) (q : Program .exact r) (T : ℕ)
    (pc : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ) :
    S.evalRand w (S.programOf q) T (S.state pc reg mem) =
      (Cslib.WordRAM.evalRand w q T ⟨pc, ⟨reg, mem⟩⟩).map S.cfgOf := by
  change S.compEval (S.runRand w (S.programOf q) T (S.cfgOf (.running ⟨pc, ⟨reg, mem⟩⟩))) = _
  rw [S.runRand_matches h, S.compEval_compOf h, ProbComp.eval_map]
  rfl

/-- Worst-case halting within `T` steps agrees between `S.programOf q` and `q`. -/
theorem haltsWithin_iff {S : Presentation} (h : Laws S) (w : ℕ) (q : Program .exact r)
    (T : ℕ) (pc : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ) :
    S.HaltsWithin w (S.programOf q) (S.state pc reg mem) T ↔
      Cslib.WordRAM.RandHaltsWithin w q ⟨pc, ⟨reg, mem⟩⟩ T := by
  simp only [Presentation.HaltsWithin, Cslib.WordRAM.RandHaltsWithin, S.evalRand_eq h,
    PMF.mem_support_map_iff, ← Cslib.WordRAM.support_evalRand]
  constructor
  · intro hh cfg' hcfg'
    obtain ⟨v, reg', mem', heq⟩ := hh (S.cfgOf cfg') ⟨cfg', hcfg', rfl⟩
    rcases cfg' with ⟨pc'', ⟨reg'', mem''⟩⟩ | ⟨v'', ⟨reg'', mem''⟩⟩ | _
    · simp only [cfgOf] at heq
      exact (h.running_ne_halted heq).elim
    · exact ⟨v'', ⟨reg'', mem''⟩, rfl⟩
    · simp only [cfgOf] at heq
      exact (h.halted_ne_faulted heq.symm).elim
  · rintro hh _ ⟨cfg', hcfg', rfl⟩
    obtain ⟨v'', ⟨reg'', mem''⟩, rfl⟩ := hh cfg' hcfg'
    exact ⟨v'', reg'', mem'', rfl⟩

/-- Worst-case `rand`-call budget agrees between `S.programOf q` and `q`. -/
theorem randCallsBounded_iff {S : Presentation} (h : Laws S) (w : ℕ) (q : Program .exact r)
    (T R : ℕ) (pc : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ) :
    S.RandCallsBounded w (S.programOf q) (S.state pc reg mem) T R ↔
      Cslib.WordRAM.RandCallsBounded w q ⟨pc, ⟨reg, mem⟩⟩ T R := by
  change S.CallsAtMost (S.runRand w (S.programOf q) T (S.cfgOf (.running ⟨pc, ⟨reg, mem⟩⟩))) R ↔ _
  rw [S.runRand_matches h, S.callsAtMost_compOf h, OracleComp.IsQueryBounded,
    OracleComp.isCostBounded_map_iff]
  rfl

/-- Expected running time agrees between `S.programOf q` and `q`. -/
theorem expectedTime_eq {S : Presentation} (h : Laws S) (w : ℕ) (q : Program .exact r)
    (pc : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ) :
    S.expectedTime w (S.programOf q) (S.state pc reg mem) =
      Cslib.WordRAM.expectedTime w q ⟨pc, ⟨reg, mem⟩⟩ := by
  simp only [Presentation.expectedTime, Cslib.WordRAM.expectedTime]
  refine tsum_congr fun t => ?_
  rw [S.evalRand_eq h, PMF.toOuterMeasure_map_apply]
  congr 1
  ext cfg'
  change (∃ u, S.cfgOf cfg' = S.running u) ↔ ∃ u, cfg' = .running u
  rcases cfg' with ⟨pc', ⟨reg', mem'⟩⟩ | ⟨v', ⟨reg', mem'⟩⟩ | _
  · simp only [cfgOf]
    exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  · simp only [cfgOf]
    exact ⟨fun ⟨u, hu⟩ => (h.running_ne_halted hu.symm).elim,
      fun ⟨u, hu⟩ => by cases hu⟩
  · simp only [cfgOf]
    exact ⟨fun ⟨u, hu⟩ => (h.running_ne_faulted hu.symm).elim,
      fun ⟨u, hu⟩ => by cases hu⟩

theorem init_state_eq (input : List ℕ) :
    (Cslib.WordRAM.State.init (r := r) input) = ⟨0, ⟨fun _ => 0, initMem input⟩⟩ := by
  simp only [Cslib.WordRAM.State.init, Data.init]
  congr 2
  funext a
  rcases a with _ | a <;> simp [initMem]

end Presentation

/-- **In-place randomized quicksort** transported to any presentation `S` satisfying `Laws S`. -/
theorem quicksort (S : Presentation) (h : Laws S) :
    ∃ p : List (S.Instr 16),
      ∀ (w : ℕ) (input : List ℕ),
        3 * (Nat.log 2 input.length + 1) ≤ w →
        Presentation.InputFits w input →
        let n := input.length
        let T := 20 * n ^ 2 + 8 * n + 32
        S.HaltsWithin (r := 16) w p (S.init input) T ∧
        S.RandCallsBounded (r := 16) w p (S.init input) T (n - 1) ∧
        (∀ cfg ∈ (S.evalRand (r := 16) w p T (S.init input)).support,
          ∃ reg mem, cfg = S.halted 0 reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            (Presentation.slice 1 (n + 1) mem).Perm input ∧
            (Presentation.slice 1 (n + 1) mem).Pairwise (· ≤ ·) ∧
            (∀ a, a < 1 ∨ 3 * n + 1 ≤ a → mem a = Presentation.initMem input a)) ∧
        S.expectedTime (r := 16) w p (S.init input) ≤
          ((120 * n * (Nat.log 2 n + 1) + 32 : ℕ) : ℝ≥0∞) := by
  refine ⟨S.programOf quicksortExactProgram, fun w input hw hfit => ?_⟩
  have hw' : logWidth 3 input.length ≤ w := hw
  have hfit' : Cslib.WordRAM.InputFits w input := hfit
  obtain ⟨hHalts, hCalls, hPost, hExp⟩ := quicksort_exact_correct_and_bounds hw' hfit'
  have hinit := Presentation.init_state_eq (r := 16) input
  have hinit_mem : (Data.init (r := 16) input).mem = Presentation.initMem input := by
    funext a
    rcases a with _ | a <;> simp [Presentation.initMem, Data.init]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Presentation.init, S.haltsWithin_iff h, ← hinit]
    exact hHalts
  · rw [Presentation.init, S.randCallsBounded_iff h, ← hinit]
    exact hCalls
  · intro cfg hcfg
    rw [Presentation.init, S.evalRand_eq h, ← hinit, PMF.mem_support_map_iff] at hcfg
    obtain ⟨cfg', hcfg', rfl⟩ := hcfg
    rw [Cslib.WordRAM.support_evalRand] at hcfg'
    obtain ⟨y, rfl, hbnd, hperm, hsort, hmod⟩ := hPost cfg' hcfg'
    refine ⟨y.regs, y.mem, rfl, hbnd.1, hbnd.2, hperm, hsort, fun a ha => ?_⟩
    rw [← hinit_mem]
    exact hmod a (by rw [Finset.mem_Ico]; omega)
  · rw [Presentation.init, S.expectedTime_eq h, ← hinit]
    exact hExp

/-- **In-place randomized quickselect** transported to any presentation `S` satisfying `Laws S`. -/
theorem quickselect (S : Presentation) (h : Laws S) :
    ∃ p : List (S.Instr 16),
      (∀ (w k : ℕ) (input : List ℕ),
        k < input.length →
        2 * (Nat.log 2 input.length + 1) ≤ w →
        Presentation.InputFits w (k :: input) →
        let n := input.length
        let T := 10 * n ^ 2 + 15
        let ans := input.mergeSort.getD k 0
        S.HaltsWithin (r := 16) w p (S.init (k :: input)) T ∧
        S.RandCallsBounded (r := 16) w p (S.init (k :: input)) T (n - 1) ∧
        (∀ cfg ∈ (S.evalRand (r := 16) w p T (S.init (k :: input))).support,
          ∃ reg mem, cfg = S.halted ans reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            (Presentation.slice 2 (n + 2) mem).Perm input ∧
            mem (2 + k) = ans ∧
            (∀ i < k, mem (2 + i) ≤ ans) ∧
            (∀ i, k < i → i < n → ans ≤ mem (2 + i)) ∧
            (∀ a, a < 2 ∨ n + 2 ≤ a → mem a = Presentation.initMem (k :: input) a)) ∧
        S.expectedTime (r := 16) w p (S.init (k :: input)) ≤
          ((80 * n + 15 : ℕ) : ℝ≥0∞)) ∧
      (∀ (w k : ℕ) (input : List ℕ),
        input.length ≤ k →
        Presentation.InputFits w (k :: input) →
        S.HaltsWithin (r := 16) w p (S.init (k :: input)) 8 ∧
        S.RandCallsBounded (r := 16) w p (S.init (k :: input)) 8 0 ∧
        (∀ cfg ∈ (S.evalRand (r := 16) w p 8 (S.init (k :: input))).support,
          ∃ reg mem, cfg = S.halted 0 reg mem ∧
            (∀ i, reg i < 2 ^ w) ∧
            (∀ a, mem a < 2 ^ w) ∧
            mem = Presentation.initMem (k :: input)) ∧
        S.expectedTime (r := 16) w p (S.init (k :: input)) = 8) := by
  refine ⟨S.programOf quickselectExactProgram, ?_, ?_⟩
  · intro w k input hk hw hfit
    have hw' : logWidth 2 input.length ≤ w := hw
    have hfit' : Cslib.WordRAM.InputFits w (k :: input) := hfit
    obtain ⟨hHalts, hCalls, hPost, hExp⟩ := quickselect_exact_correct_and_bounds hk hw' hfit'
    have hinit := Presentation.init_state_eq (r := 16) (k :: input)
    have hinit_mem : (Data.init (r := 16) (k :: input)).mem =
        Presentation.initMem (k :: input) := by
      funext a
      rcases a with _ | a <;> simp [Presentation.initMem, Data.init]
    have hans_eq : input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) =
        input.mergeSort.getD k 0 := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [List.length_mergeSort]; exact hk), Option.getD_some]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Presentation.init, S.haltsWithin_iff h, ← hinit]
      exact hHalts
    · rw [Presentation.init, S.randCallsBounded_iff h, ← hinit]
      exact hCalls
    · intro cfg hcfg
      rw [Presentation.init, S.evalRand_eq h, ← hinit, PMF.mem_support_map_iff] at hcfg
      obtain ⟨cfg', hcfg', rfl⟩ := hcfg
      rw [Cslib.WordRAM.support_evalRand] at hcfg'
      obtain ⟨y, rfl, hbnd, hperm, hy_k, hleft, hright, hmod⟩ := hPost cfg' hcfg'
      rw [hans_eq] at hy_k ⊢
      refine ⟨y.regs, y.mem, rfl, hbnd.1, hbnd.2, hperm, hy_k,
        fun i hi => by rw [← hy_k]; exact hleft i hi,
        fun i hki hin => by rw [← hy_k]; exact hright i hki hin,
        fun a ha => ?_⟩
      rw [← hinit_mem]
      exact hmod a (by rw [Finset.mem_Ico]; omega)
    · rw [Presentation.init, S.expectedTime_eq h, ← hinit]
      exact hExp
  · intro w k input hk hfit
    have hfit' : Cslib.WordRAM.InputFits w (k :: input) := hfit
    obtain ⟨hHalts, hCalls, hPost, hExp⟩ := quickselect_exact_out_of_range hk hfit'
    have hinit := Presentation.init_state_eq (r := 16) (k :: input)
    have hinit_mem : (Data.init (r := 16) (k :: input)).mem =
        Presentation.initMem (k :: input) := by
      funext a
      rcases a with _ | a <;> simp [Presentation.initMem, Data.init]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Presentation.init, S.haltsWithin_iff h, ← hinit]
      exact hHalts
    · rw [Presentation.init, S.randCallsBounded_iff h, ← hinit]
      exact hCalls
    · intro cfg hcfg
      rw [Presentation.init, S.evalRand_eq h, ← hinit, PMF.mem_support_map_iff] at hcfg
      obtain ⟨cfg', hcfg', rfl⟩ := hcfg
      rw [Cslib.WordRAM.support_evalRand] at hcfg'
      obtain ⟨y, rfl, hbnd, hmem_eq⟩ := hPost cfg' hcfg'
      exact ⟨y.regs, y.mem, rfl, hbnd.1, hbnd.2, hmem_eq.trans hinit_mem⟩
    · rw [Presentation.init, S.expectedTime_eq h, ← hinit]
      exact hExp

end ComplexityAbstracts.RandomizedWordRAMBridge
