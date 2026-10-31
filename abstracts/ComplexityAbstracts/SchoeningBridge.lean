/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import Complexity.Algorithms.WordRAM.Schoening.Amplify
import ComplexityAbstracts.RandomizedWordRAMBridge

/-!
# Bridge for the Schöning formal abstract

`SchoeningAbstract.lean` states the randomized word RAM over the standard basis, CNF formulas on
`Fin n` with their word encoding, one trial of Schöning's algorithm, and the guarantees of the
amplified program `Cslib.Algorithms.WordRAM.Schoening.ampProgram` for 3-SAT. This bridge proves
three facts.

1. **The standard randomized word RAM.** `RandomizedWordRAMBridge` matches every presentation `S`
   of the randomized word RAM satisfying `RandomizedWordRAMBridge.Laws S` with `Cslib.WordRAM` over
   `Basis.exact`. Schöning's program is written over `Basis.standard`, where subtraction is
   truncated and division and remainder by zero follow Lean's conventions. `StdLaws S` replaces
   the exact operation laws by these, and adds that `halted` determines its output word. The
   correspondence `stepRand_matches`, `runRand_matches`, `evalRand_eq`, `haltsWithin_iff` and
   `randCallsBounded_iff` is proved here for `Basis.standard`, reusing the presentation signature
   `RandomizedWordRAMBridge.Presentation` and its translations `compOf`, `aluOpOf` and `cfgOf`.
2. **Schöning's trial.** The abstract writes a flip with `Function.update` and the local search
   as iterated steps. `trialSpec_eq` proves that this is `Cslib.Complexity.Schoening.trial`.
3. **The transfer.** `schoening` instantiates `ampProgram_spec`, `ampProgram_failure_eq` and
   `ampProgram_failure_le_exp` at `k = 3`, replaces the trial count `schoeningTrials 3 n c` by
   `⌈(3 n + 1) (4 / 3) ^ n⌉ c`, the word-size condition by an explicit polynomial one
   (`counterLen_le`), and the clock `ampTime` by `⌊900 (n + L + 4) ^ 3 (4 / 3) ^ n (c + 1)⌋`
   (`ampTime_le`), and transports the result to every presentation satisfying `StdLaws`.
-/

namespace ComplexityAbstracts.SchoeningBridge

open Cslib Cslib.WordRAM Cslib.Logic.PL
open ComplexityAbstracts.RandomizedWordRAMBridge (Presentation)

/-! ## Part 1: presentations of the standard randomized word RAM -/

/-- Equational specification of a presentation of the randomized word RAM over the standard
basis: truncated subtraction and Lean's division and remainder by zero, so that no operation is
undefined. Apart from these operation laws and `halted_inj`, these are the laws of
`RandomizedWordRAMBridge.Laws`. -/
structure StdLaws (S : Presentation) : Prop where
  eval_add : ∀ x y, S.eval S.add x y = some (x + y)
  eval_sub : ∀ x y, S.eval S.sub x y = some (x - y)
  eval_mul : ∀ x y, S.eval S.mul x y = some (x * y)
  eval_div : ∀ x y, S.eval S.div x y = some (x / y)
  eval_mod : ∀ x y, S.eval S.mod x y = some (x % y)
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
  halted_inj : ∀ {r : ℕ} {v v' : ℕ} {reg reg' : Fin r → ℕ} {mem mem' : ℕ → ℕ},
    S.halted v reg mem = S.halted v' reg' mem' → v = v'
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
  stepRand_alu : ∀ {r w : ℕ} {p : List (S.Instr r)} {pc reg mem f d i j x},
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

namespace StdLaws

variable {S : Presentation} (h : StdLaws S)
include h

theorem compOf_bind {α β : Type} (m : ProbComp α) (f : α → ProbComp β) :
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

theorem compOf_map {α β : Type} (f : α → β) (m : ProbComp α) :
    S.compOf (f <$> m) = S.compBind (S.compOf m) (fun a => S.compPure (f a)) := by
  rw [← bind_pure_comp]
  exact h.compOf_bind m (fun a => pure (f a))

theorem compEval_compOf {α : Type} (m : ProbComp α) : S.compEval (S.compOf m) = m.eval := by
  induction m with
  | pure a => exact h.compEval_pure a
  | liftBind n cont ih =>
    have hbind : (PFunctor.FreeM.liftBind n cont : ProbComp α) = ProbComp.unifFin n >>= cont := rfl
    rw [Presentation.compOf_liftBind, hbind, h.compEval_sample, ProbComp.eval_bind,
      ProbComp.eval_unifFin]
    exact congrArg _ (funext ih)

theorem callsAtMost_compOf {α : Type} (m : ProbComp α) (R : ℕ) :
    S.CallsAtMost (S.compOf m) R ↔ m.IsQueryBounded R := by
  induction m generalizing R with
  | pure a =>
    exact ⟨fun _ => .pure a R, fun _ => h.callsAtMost_pure a R⟩
  | liftBind n cont ih =>
    rw [Presentation.compOf_liftBind, OracleComp.IsQueryBounded,
      OracleComp.IsCostBounded.liftBind_iff]
    cases R with
    | zero =>
      exact ⟨fun hc => (h.callsAtMost_sample_zero n _ hc).elim, fun ⟨hle, _⟩ => by omega⟩
    | succ R =>
      rw [h.callsAtMost_sample_succ, Nat.add_sub_cancel]
      exact ⟨fun hc => ⟨by omega, fun k => (ih k R).mp (hc k)⟩,
        fun ⟨_, hcont⟩ k => (ih k R).mpr (hcont k)⟩

theorem compBind_compOf_map {α β γ : Type} (f : α → β) (m : ProbComp α) (g : β → S.Comp γ) :
    S.compBind (S.compOf (f <$> m)) g = S.compBind (S.compOf m) (fun a => g (f a)) := by
  rw [h.compOf_map]
  induction m with
  | pure a => simp [Presentation.compOf, h.compBind_pure]
  | liftBind n cont ih =>
    rw [Presentation.compOf_liftBind, h.compBind_sample, h.compBind_sample, h.compBind_sample]
    exact congrArg (S.compSample n) (funext ih)

/-- A standard binary operation has its truncated value in the presentation. -/
theorem eval_aluOpOf (g : BinOp) (x y : ℕ) : S.eval (S.aluOpOf g) x y = some (g.eval x y) := by
  cases g <;> simp [Presentation.aluOpOf, h.eval_add, h.eval_sub, h.eval_mul, h.eval_div,
    h.eval_mod, h.eval_and, h.eval_or, h.eval_xor, h.eval_shl, h.eval_shr, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]

end StdLaws

variable {r : ℕ}

/-- Translate a `Cslib.WordRAM` instruction over `Basis.standard` to an abstract instruction. -/
def instrOf (S : Presentation) : Cslib.WordRAM.Instr .standard r → S.Instr r
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

/-- Translate a library `Program .standard r` to an abstract program. -/
def programOf (S : Presentation) (q : Program .standard r) : List (S.Instr r) :=
  q.map (instrOf S)

/-- One randomized step of `programOf S q` matches `Cslib.WordRAM.stepRand` over `Basis.standard`
up to `cfgOf` and `compOf`. -/
theorem stepRand_matches {S : Presentation} (h : StdLaws S) (w : ℕ) (q : Program .standard r)
    (cfg : Cslib.WordRAM.RandCfg r) :
    S.stepRand w (programOf S q) (S.cfgOf cfg) =
      S.compOf (S.cfgOf <$> Cslib.WordRAM.stepRand w q cfg) := by
  rcases cfg with ⟨pc, ⟨reg, mem⟩⟩ | ⟨v, ⟨reg, mem⟩⟩ | _
  · have hget := List.getElem?_map (f := instrOf S) (l := q) (i := pc)
    change (programOf S q)[pc]? = _ at hget
    rcases hq : q[pc]? with _ | j
    · rw [hq, Option.map_none] at hget
      change S.stepRand w (programOf S q) (S.running (S.state pc reg mem)) = _
      rw [h.stepRand_none hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq,
        Presentation.cfgOf]
    rw [hq, Option.map_some] at hget
    change S.stepRand w (programOf S q) (S.running (S.state pc reg mem)) = _
    match j, hget with
    | .op (.const d x), hget =>
      rw [h.stepRand_const hget]
      by_cases hx : x < 2 ^ w <;>
        simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval, Data.put,
          Fits, hx, Data.set, Presentation.cfgOf]
    | .op (.copy d i), hget =>
      rw [h.stepRand_copy hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval, Data.set,
        Presentation.cfgOf]
    | .op (.alu (.bin g) d args), hget =>
      rw [h.stepRand_alu hget (h.eval_aluOpOf g _ _)]
      have hlib : StandardOp.eval w (.bin g) (reg ∘ args) =
          some (g.eval (reg (args (0 : Fin 2))) (reg (args (1 : Fin 2)))) := rfl
      simp only [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval,
        Basis.standard, hlib]
      by_cases hx : g.eval (reg (args (0 : Fin 2))) (reg (args (1 : Fin 2))) < 2 ^ w <;>
        simp [Data.put, Fits, hx, Data.set, Presentation.cfgOf, -BinOp.eval]
    | .op (.alu .width d args), hget =>
      rw [h.stepRand_width hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval, Data.put,
        Fits, Data.set, StandardOp.eval, Nat.lt_two_pow_self, Presentation.cfgOf]
    | .op (.load d a), hget =>
      rw [h.stepRand_load hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval, Data.set,
        Presentation.cfgOf]
    | .op (.store a i), hget =>
      rw [h.stepRand_store hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Op.eval,
        Data.write, Presentation.cfgOf]
    | .jump t, hget =>
      rw [h.stepRand_jump hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Presentation.cfgOf]
    | .branch (.eq i j) t, hget =>
      rw [h.stepRand_branchEq hget]
      by_cases hij : reg i = reg j <;>
        simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Cond.Holds, hij,
          Presentation.cfgOf]
    | .branch (.lt i j) t, hget =>
      rw [h.stepRand_branchLt hget]
      by_cases hij : reg i < reg j <;>
        simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Cond.Holds, hij,
          Presentation.cfgOf]
    | .halt i, hget =>
      rw [h.stepRand_halt hget]
      simp [Cslib.WordRAM.stepRand, Cslib.WordRAM.step, RandCfg.ofOutcome, hq, Presentation.cfgOf]
    | .rand d i, hget =>
      rw [h.stepRand_rand hget]
      by_cases hx : reg i < 2 ^ w
      · simp only [Cslib.WordRAM.stepRand, hq, Fits, hx, ↓reduceIte, Data.set]
        rw [h.compOf_map, h.compOf_bind]
        simp [Presentation.compOf_unifFin, h.compBind_sample, h.compBind_pure,
          Presentation.cfgOf]
      · simp [Cslib.WordRAM.stepRand, hq, Fits, hx, Presentation.cfgOf]
  · change S.stepRand w (programOf S q) (S.halted v reg mem) = _
    rw [h.stepRand_halted]
    rfl
  · change S.stepRand w (programOf S q) S.faulted = _
    rw [h.stepRand_faulted]
    rfl

/-- Clocked `T`-step runs of `programOf S q` match `Cslib.WordRAM.runRand`. -/
theorem runRand_matches {S : Presentation} (h : StdLaws S) (w : ℕ) (q : Program .standard r)
    (T : ℕ) (cfg : Cslib.WordRAM.RandCfg r) :
    S.runRand w (programOf S q) T (S.cfgOf cfg) =
      S.compOf (S.cfgOf <$> Cslib.WordRAM.runRand w q T cfg) := by
  induction T generalizing cfg with
  | zero =>
    rw [h.runRand_zero, Cslib.WordRAM.runRand_zero]
    rfl
  | succ T ih =>
    rw [h.runRand_succ, stepRand_matches h w q cfg, h.compBind_compOf_map,
      Cslib.WordRAM.runRand_succ, ← bind_pure_comp, bind_assoc, h.compOf_bind]
    exact congrArg (S.compBind _) (funext fun cfg' => by rw [bind_pure_comp, ih cfg'])

/-- The `T`-step distribution of `programOf S q` is the image of `Cslib.WordRAM.evalRand`. -/
theorem evalRand_eq {S : Presentation} (h : StdLaws S) (w : ℕ) (q : Program .standard r) (T : ℕ)
    (pc : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ) :
    S.evalRand w (programOf S q) T (S.state pc reg mem) =
      (Cslib.WordRAM.evalRand w q T ⟨pc, ⟨reg, mem⟩⟩).map S.cfgOf := by
  change S.compEval (S.runRand w (programOf S q) T (S.cfgOf (.running ⟨pc, ⟨reg, mem⟩⟩))) = _
  rw [runRand_matches h, h.compEval_compOf, ProbComp.eval_map]
  rfl

/-- Worst-case halting within `T` steps agrees between `programOf S q` and `q`. -/
theorem haltsWithin_iff {S : Presentation} (h : StdLaws S) (w : ℕ) (q : Program .standard r)
    (T : ℕ) (pc : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ) :
    S.HaltsWithin w (programOf S q) (S.state pc reg mem) T ↔
      Cslib.WordRAM.RandHaltsWithin w q ⟨pc, ⟨reg, mem⟩⟩ T := by
  simp only [Presentation.HaltsWithin, Cslib.WordRAM.RandHaltsWithin, evalRand_eq h,
    PMF.mem_support_map_iff, ← Cslib.WordRAM.support_evalRand]
  constructor
  · intro hh cfg' hcfg'
    obtain ⟨v, reg', mem', heq⟩ := hh (S.cfgOf cfg') ⟨cfg', hcfg', rfl⟩
    rcases cfg' with ⟨pc'', ⟨reg'', mem''⟩⟩ | ⟨v'', ⟨reg'', mem''⟩⟩ | _
    · exact (h.running_ne_halted heq).elim
    · exact ⟨v'', ⟨reg'', mem''⟩, rfl⟩
    · exact (h.halted_ne_faulted heq.symm).elim
  · rintro hh _ ⟨cfg', hcfg', rfl⟩
    obtain ⟨v'', ⟨reg'', mem''⟩, rfl⟩ := hh cfg' hcfg'
    exact ⟨v'', reg'', mem'', rfl⟩

/-- Worst-case `rand`-call budgets agree between `programOf S q` and `q`. -/
theorem randCallsBounded_iff {S : Presentation} (h : StdLaws S) (w : ℕ) (q : Program .standard r)
    (T R : ℕ) (pc : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ) :
    S.RandCallsBounded w (programOf S q) (S.state pc reg mem) T R ↔
      Cslib.WordRAM.RandCallsBounded w q ⟨pc, ⟨reg, mem⟩⟩ T R := by
  change S.CallsAtMost (S.runRand w (programOf S q) T (S.cfgOf (.running ⟨pc, ⟨reg, mem⟩⟩))) R ↔ _
  rw [runRand_matches h, h.callsAtMost_compOf, OracleComp.IsQueryBounded,
    OracleComp.isCostBounded_map_iff]
  rfl

/-- The configurations that do not halt with output `1` are the preimage of `cfgSuccess = false`. -/
theorem cfgOf_preimage_not_halted_one {S : Presentation} (h : StdLaws S) :
    S.cfgOf ⁻¹' {cfg : S.Cfg r | ¬∃ reg mem, cfg = S.halted 1 reg mem} =
      Algorithms.WordRAM.Schoening.cfgSuccess ⁻¹' {false} := by
  ext cfg
  rcases cfg with ⟨pc, ⟨reg, mem⟩⟩ | ⟨v, ⟨reg, mem⟩⟩ | _
  · simp only [Set.mem_preimage, Set.mem_ofPred_eq, Presentation.cfgOf,
      Algorithms.WordRAM.Schoening.cfgSuccess, Set.mem_singleton_iff, iff_true]
    exact fun ⟨_, _, he⟩ => h.running_ne_halted he
  · simp only [Set.mem_preimage, Set.mem_ofPred_eq, Presentation.cfgOf,
      Algorithms.WordRAM.Schoening.cfgSuccess, Set.mem_singleton_iff, decide_eq_false_iff_not]
    exact ⟨fun hne hv => hne ⟨reg, mem, by rw [hv]⟩, fun hne ⟨_, _, he⟩ => hne (h.halted_inj he)⟩
  · simp only [Set.mem_preimage, Set.mem_ofPred_eq, Presentation.cfgOf,
      Algorithms.WordRAM.Schoening.cfgSuccess, Set.mem_singleton_iff, iff_true]
    exact fun ⟨_, _, he⟩ => h.halted_ne_faulted he.symm

/-! ## Part 2: Schöning's trial, as written in the abstract -/

variable {n : ℕ}

/-- The first clause of `φ` that `σ` falsifies, as in the abstract. -/
def firstUnsat (φ : CNF (Fin n)) (σ : Fin n → Bool) : Option (Clause (Fin n)) :=
  φ.find? fun c => !c.any fun l => σ l.1 == l.2

/-- Flip the variable of a uniformly chosen literal occurrence of `c`, as in the abstract. -/
noncomputable def flipStep (c : Clause (Fin n)) (σ : Fin n → Bool) : PMF (Fin n → Bool) :=
  if h : c.length = 0 then PMF.pure σ else
    haveI : NeZero c.length := ⟨h⟩
    (Cslib.Probability.PMF.uniformOfFintype (Fin c.length)).map fun i =>
      Function.update σ (c.get i).1 (!σ (c.get i).1)

/-- One step of local search, as in the abstract. -/
noncomputable def walkStep (φ : CNF (Fin n)) (σ : Fin n → Bool) : PMF (Fin n → Bool) :=
  (firstUnsat φ σ).elim (PMF.pure σ) fun c => flipStep c σ

/-- `t` steps of local search from `σ`, as in the abstract. -/
noncomputable def walk (φ : CNF (Fin n)) (t : ℕ) (σ : Fin n → Bool) : PMF (Fin n → Bool) :=
  (fun μ : PMF (Fin n → Bool) => μ.bind (walkStep φ))^[t] (PMF.pure σ)

/-- One trial of Schöning's algorithm, as in the abstract. -/
noncomputable def trial (φ : CNF (Fin n)) : PMF (Fin n → Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin n → Bool)).bind (walk φ (3 * n))

theorem flipStep_eq (c : Clause (Fin n)) (σ : Fin n → Bool) :
    flipStep c σ = Complexity.Schoening.flipStep c σ := by
  unfold flipStep Complexity.Schoening.flipStep
  split_ifs with hc
  · rfl
  · congr 1
    funext i
    funext x
    rw [BitString.flipOn_apply, Function.update_apply]
    simp only [Finset.mem_singleton]
    split_ifs with hx
    · rw [hx]
    · rfl

/-- Iterating a Kleisli step on `μ` binds `μ` into the iterates from point masses. -/
private theorem iterate_bind {α : Type} (g : α → PMF α) :
    ∀ (t : ℕ) (μ : PMF α), (fun ν : PMF α => ν.bind g)^[t] μ =
      μ.bind fun a => (fun ν : PMF α => ν.bind g)^[t] (PMF.pure a)
  | 0, μ => by simp only [Function.iterate_zero, id_eq, PMF.bind_pure]
  | t + 1, μ => by
    simp only [Function.iterate_succ_apply, PMF.pure_bind]
    rw [iterate_bind g t (μ.bind g), PMF.bind_bind]
    exact congrArg μ.bind (funext fun a => (iterate_bind g t (g a)).symm)

theorem walk_eq (φ : CNF (Fin n)) : ∀ (t : ℕ) (σ : Fin n → Bool),
    walk φ t σ = Complexity.Schoening.walk φ t σ
  | 0, σ => rfl
  | t + 1, σ => by
    rw [Algorithms.WordRAM.Schoening.walk_succ_eq_bind, walk, Function.iterate_succ_apply,
      PMF.pure_bind, iterate_bind]
    have hstep : walkStep φ σ = Algorithms.WordRAM.Schoening.stepLaw φ σ := by
      have hfu : firstUnsat φ σ = Complexity.Schoening.firstUnsat φ σ := rfl
      unfold walkStep Algorithms.WordRAM.Schoening.stepLaw
      rw [hfu]
      rcases Complexity.Schoening.firstUnsat φ σ with _ | c
      · rfl
      · exact flipStep_eq c σ
    rw [hstep]
    exact congrArg _ (funext fun σ' => walk_eq φ t σ')

/-- **The abstract's trial is Schöning's trial.** -/
theorem trial_eq (φ : CNF (Fin n)) : trial φ = Complexity.Schoening.trial φ := by
  unfold trial Complexity.Schoening.trial
  rw [Fintype.card_fin]
  congr 1
  funext σ
  exact walk_eq φ (3 * n) σ

/-! ## Part 3: the transfer -/

open Algorithms.WordRAM.Schoening in
/-- The clock `ampTime` for `k = 3` is at most `⌊900 (n + L + 4) ^ 3 (4 / 3) ^ n (c + 1)⌋`. -/
theorem ampTime_three_le (n c L : ℕ) :
    ampTime 3 n c L ≤ 900 * (n + L + 4) ^ 3 * 4 ^ n * (c + 1) / 3 ^ n := by
  have h1 := ampTime_le (k := 3) le_rfl n c L
  rw [Nat.le_div_iff_mul_le (by positivity)]
  have h3 : (2 * (((3 : ℕ) : ℝ) - 1) / ((3 : ℕ) : ℝ)) = 4 / 3 := by norm_num
  have h4 : ((n + 3 + L + 1 : ℕ) : ℝ) = (n + L + 4 : ℝ) := by push_cast; ring
  rw [h3, h4] at h1
  have h2 : (ampTime 3 n c L : ℝ) * 3 ^ n ≤ 900 * (n + L + 4 : ℝ) ^ 3 * 4 ^ n * (c + 1) := by
    calc (ampTime 3 n c L : ℝ) * 3 ^ n
        ≤ 900 * (n + L + 4 : ℝ) ^ 3 * (4 / 3) ^ n * (c + 1) * 3 ^ n := by gcongr
      _ = 900 * (n + L + 4 : ℝ) ^ 3 * 4 ^ n * (c + 1) := by
        rw [div_pow]
        field_simp
  exact_mod_cast h2

open Algorithms.WordRAM.Schoening in
/-- The trial count for `k = 3` is `⌈(3 n + 1) (4 / 3) ^ n⌉ c`. -/
theorem schoeningTrials_three (n c : ℕ) :
    schoeningTrials 3 n c = ⌈(3 * n + 1 : ℝ) * (4 / 3) ^ n⌉₊ * c := by
  simp only [schoeningTrials]
  norm_num

open Algorithms.WordRAM.Schoening in
/-- **Schöning's algorithm for 3-SAT** on the standard randomized word RAM, transported to every
presentation `S` satisfying `StdLaws S`. The program is `programOf S ampProgram`. -/
theorem schoening (S : Presentation) (h : StdLaws S) :
    ∃ p : List (S.Instr 24), ∀ (n c w : ℕ) (φ : CNF (Fin n)),
      let input := 3 :: c :: encode φ
      let L := input.length
      let R := ⌈(3 * n + 1 : ℝ) * (4 / 3) ^ n⌉₊ * c
      let T := 900 * (n + L + 4) ^ 3 * 4 ^ n * (c + 1) / 3 ^ n
      L + 8 * (n + 3) ^ 2 + 3 * c < 2 ^ w →
      S.HaltsWithin (r := 24) w p (S.init input) T ∧
      S.RandCallsBounded (r := 24) w p (S.init input) T (R * (4 * n)) ∧
      (∀ cfg ∈ (S.evalRand (r := 24) w p T (S.init input)).support,
        ∃ v reg mem, cfg = S.halted v reg mem ∧
          (v = 0 ∨ (v = 1 ∧ φ.eval (fun i : Fin n => decide (mem (L + 1 + i) = 1)) = true))) ∧
      ((S.evalRand (r := 24) w p T (S.init input)).toOuterMeasure
          {cfg | ¬∃ reg mem, cfg = S.halted 1 reg mem}).toReal =
        (1 - ((SchoeningBridge.trial φ).toOuterMeasure {σ | φ.eval σ = true}).toReal) ^ R ∧
      (φ.Satisfiable → (∀ cl ∈ φ, cl.length ≤ 3) →
        ((S.evalRand (r := 24) w p T (S.init input)).toOuterMeasure
          {cfg | ¬∃ reg mem, cfg = S.halted 1 reg mem}).toReal ≤ Real.exp (-c)) := by
  refine ⟨programOf S ampProgram, fun n c w φ => ?_⟩
  intro input L R T hw
  -- the word size
  have hfit : Fits w (L + 6 * n + 4 * 3 + 2 * c + counterLen 3 n c + 2) := by
    have hℓ := counterLen_le 3 n c
    have hm : 6 * n + 14 ≤ 2 * (n + 3) ^ 2 := by nlinarith
    unfold Fits
    generalize (n + 3) ^ 2 = m at hm hℓ hw
    omega
  obtain ⟨hhalt, hcalls, hpost, hlaw⟩ := ampProgram_spec 3 c le_rfl φ hfit
  have hT : ampTime 3 n c L ≤ T := ampTime_three_le n c L
  have hR : schoeningTrials 3 n c = R := schoeningTrials_three n c
  have hinit := Presentation.init_state_eq (r := 24) input
  -- the distribution at `T` is the one at `ampTime`
  have hdist : S.evalRand (r := 24) w (programOf S ampProgram) T (S.init input) =
      (Cslib.WordRAM.evalRand w ampProgram (ampTime 3 n c L) (.init input)).map S.cfgOf := by
    rw [Presentation.init, evalRand_eq h, ← hinit, evalRand_eq_of_randHaltsWithin hhalt hT]
  have hfail : ((S.evalRand (r := 24) w (programOf S ampProgram) T (S.init input)).toOuterMeasure
      {cfg | ¬∃ reg mem, cfg = S.halted 1 reg mem}) =
      (Cslib.WordRAM.evalRand w ampProgram (ampTime 3 n c L) (.init input)).map cfgSuccess
        false := by
    rw [hdist, PMF.toOuterMeasure_map_apply, cfgOf_preimage_not_halted_one h,
      ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Presentation.init, haltsWithin_iff h, ← hinit]
    exact hhalt.mono hT
  · rw [Presentation.init, randCallsBounded_iff h, ← hinit, ← hR]
    exact hcalls.of_randHaltsWithin hhalt hT
  · intro cfg hcfg
    rw [hdist, PMF.mem_support_map_iff] at hcfg
    obtain ⟨cfg', hcfg', rfl⟩ := hcfg
    rw [Cslib.WordRAM.support_evalRand] at hcfg'
    obtain ⟨v, d, rfl, hv⟩ := hpost cfg' hcfg'
    exact ⟨v, d.regs, d.mem, rfl, hv⟩
  · rw [hfail, ampProgram_failure_eq 3 c le_rfl φ hfit, hR, trial_eq]
    rfl
  · intro hsat hlen
    rw [hfail]
    exact ampProgram_failure_le_exp le_rfl hsat hlen hfit

end ComplexityAbstracts.SchoeningBridge
