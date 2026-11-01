/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.Randomized.Structured
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Map

/-!
# Exact laws of structured randomized word-RAM programs

`Cslib.WordRAM.ExecRandLaw w c x P T R f μ` strengthens `Cslib.WordRAM.ExecRandWithin w c x P T R`
by the exact distribution `μ` of an observation `f : Data r → α` of the final data. Its rules
compose like those of `ExecRandWithin`. Along a sequence or a loop iteration, the observation of
the first part only has to determine the law of the rest, so the laws compose by `PMF.bind`
(`Cslib.WordRAM.ExecRandLaw.seq`, `Cslib.WordRAM.ExecRandLaw.loop_iter`). This lets a proof match
a program against a mathematical randomized process step by step, observing only the part of the
memory that the process describes.

A compiled program then halts on every path within the time bound, makes at most the given number
of `rand` calls, and has law `μ` for every observation of its halting configurations that agrees
with `f` (`Cslib.WordRAM.ExecRandLaw.program`).

## Main definitions

* `Cslib.WordRAM.ExecRandLaw`: pathwise postcondition, worst-case instruction and `rand`-call
  budgets, and the exact law of an observation of the final data.

## Main results

* `Cslib.WordRAM.ExecRandLaw.of_execWithin`, `Cslib.WordRAM.ExecRandLaw.rand`: deterministic code
  and a single `rand` instruction.
* `Cslib.WordRAM.ExecRandLaw.seq_det`, `Cslib.WordRAM.ExecRandLaw.seq_det_right`,
  `Cslib.WordRAM.ExecRandLaw.rand_seq`: deterministic prefixes and suffixes, and a draw followed
  by deterministic code.
* `Cslib.WordRAM.ExecRandLaw.seq`, `Cslib.WordRAM.ExecRandLaw.branch_pos`,
  `Cslib.WordRAM.ExecRandLaw.branch_neg`, `Cslib.WordRAM.ExecRandLaw.loop_exit`,
  `Cslib.WordRAM.ExecRandLaw.loop_iter`: composition rules.
* `Cslib.WordRAM.ExecRandLaw.execRandWithin`: forgetting the law.
* `Cslib.WordRAM.ExecRandLaw.program`: the compiled program halts within the bound, respects the
  call budget and the postcondition, and has the law `μ`.
-/

public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ} {α β : Type}

/-- `ExecRandLaw w c x P T R f μ`: at word size `w`, running `c` from `x` terminates cleanly on
every path, makes at most `R` `rand` calls on every path, every supported outcome `(y, n)`
satisfies `P y` and `n ≤ T`, and the observation `f y` of the final data has law `μ`. -/
def ExecRandLaw (w : ℕ) (c : Code B r) (x : Data r) (P : Data r → Prop) (T R : ℕ)
    (f : Data r → α) (μ : PMF α) : Prop :=
  ∃ m, ExecRand w c x m ∧ m.IsQueryBounded R ∧ (∀ z ∈ m.support, P z.1 ∧ z.2 ≤ T) ∧
    ((fun z => f z.1) <$> m).eval = μ

namespace ExecRandLaw

variable {w : ℕ} {c c₁ c₂ pos neg body : Code B r} {cond : Cond r} {x : Data r}
  {P Q : Data r → Prop} {T T' T₁ T₂ R R' R₁ R₂ : ℕ} {f : Data r → α} {μ : PMF α}

/-- Forgetting the law leaves an `ExecRandWithin` specification. -/
theorem execRandWithin (h : ExecRandLaw w c x P T R f μ) : ExecRandWithin w c x P T R := by
  obtain ⟨m, hm, hq, hsup, -⟩ := h
  exact ⟨m, hm, hq, hsup⟩

/-- Weakening the postcondition and the budgets. -/
theorem mono (h : ExecRandLaw w c x P T R f μ) (hPQ : ∀ y, P y → Q y) (hT : T ≤ T')
    (hR : R ≤ R') : ExecRandLaw w c x Q T' R' f μ := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := h
  exact ⟨m, hm, hq.mono hR, fun z hz => ⟨hPQ z.1 (hsup z hz).1, (hsup z hz).2.trans hT⟩, hlaw⟩

/-- Rewriting the law along an equality. -/
theorem congr_law {μ' : PMF α} (h : ExecRandLaw w c x P T R f μ) (hμ : μ = μ') :
    ExecRandLaw w c x P T R f μ' :=
  hμ ▸ h

/-- Strengthening the postcondition with a register that `c` never writes. -/
theorem withPreserves {i : Fin r} (h : ExecRandLaw w c x P T R f μ) (hi : c.Preserves i) :
    ExecRandLaw w c x (fun y => P y ∧ y.regs i = x.regs i) T R f μ := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := h
  exact ⟨m, hm, hq, fun z hz => ⟨⟨(hsup z hz).1, hm.regs_eq hi hz⟩, (hsup z hz).2⟩, hlaw⟩

/-- Deterministic code reaching `y` has the point law at the observation of `y`. -/
theorem of_execWithin {y : Data r} (h : ExecWithin w c x y T) (hy : P y) :
    ExecRandLaw w c x P T 0 f (PMF.pure (f y)) := by
  obtain ⟨n, hn, he⟩ := h
  refine ⟨pure (y, n), he.execRand, .pure _ 0, fun z hz => ?_, ?_⟩
  · cases OracleComp.eq_of_mem_supportWith_pure hz
    exact ⟨hy, hn⟩
  · rw [map_pure, ProbComp.eval_pure]

/-- `Code.rand dst src` draws `k` uniformly from `[0, x.regs src]` and observes `x.set dst k`. -/
theorem rand {dst src : Fin r} (hfit : Fits w (x.regs src))
    (hk : ∀ k : Fin (x.regs src + 1), P (x.set dst k.val)) :
    ExecRandLaw (B := B) w (.rand dst src) x P 1 1 f
      ((Probability.PMF.uniformOfFintype (Fin (x.regs src + 1))).map
        fun k => f (x.set dst k.val)) := by
  refine ⟨_, ExecRand.rand hfit, ?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using
      (ProbComp.isQueryBounded_unifFin (x.regs src)).bind fun _ => .pure _ 0
  · intro z hz
    obtain ⟨k, -, hz'⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hz'
    exact ⟨hk k, le_rfl⟩
  · simp only [map_bind, map_pure, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_unifFin]
    rfl

/-- **Sequencing.** If the observation `g` after `c₁` determines the law `κ (g y)` of the
observation `f` after `c₂`, the laws compose by `PMF.bind`. -/
theorem seq {g : Data r → β} {ν : PMF β} {κ : β → PMF α}
    (h₁ : ExecRandLaw w c₁ x P T₁ R₁ g ν)
    (h₂ : ∀ y, P y → ExecRandLaw w c₂ y Q T₂ R₂ f (κ (g y))) :
    ExecRandLaw w (.seq c₁ c₂) x Q (T₁ + T₂) (R₁ + R₂) f (ν.bind κ) := by
  obtain ⟨m₁, hm₁, hq₁, hsup₁, hlaw₁⟩ := h₁
  have hstep : ∀ z₁ ∈ m₁.support,
      ExecRand w c₂ z₁.1 (codeComp w c₂ z₁.1) ∧
      (codeComp w c₂ z₁.1).IsQueryBounded R₂ ∧
      (∀ z₂ ∈ (codeComp w c₂ z₁.1).support, Q z₂.1 ∧ z₂.2 ≤ T₂) ∧
      ((fun z => f z.1) <$> codeComp w c₂ z₁.1).eval = κ (g z₁.1) := by
    intro z₁ hz₁
    obtain ⟨m₂, hm₂, hq₂, hsup₂, hlaw₂⟩ := h₂ z₁.1 (hsup₁ z₁ hz₁).1
    rw [hm₂.codeComp_eq]
    exact ⟨hm₂, hq₂, hsup₂, hlaw₂⟩
  refine ⟨_, ExecRand.seq hm₁ fun z₁ hz₁ => (hstep z₁ hz₁).1, ?_, ?_, ?_⟩
  · refine OracleComp.IsCostBounded.bind_on_support hq₁ fun z₁ hz₁ => ?_
    simpa only [Nat.add_zero] using
      (hstep z₁ hz₁).2.1.bind fun _ => .pure _ 0
  · intro z hz
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z₂, hz₂, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hfinal
    exact ⟨((hstep z₁ hz₁).2.2.1 z₂ hz₂).1,
      Nat.add_le_add (hsup₁ z₁ hz₁).2 ((hstep z₁ hz₁).2.2.1 z₂ hz₂).2⟩
  · rw [← hlaw₁]
    simp only [map_bind, map_pure, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map,
      PMF.bind_map]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun z₁ hz₁ => ?_
    rw [ProbComp.support_eval] at hz₁
    rw [Function.comp_apply, ← (hstep z₁ hz₁).2.2.2, ProbComp.eval_map]
    rfl

/-- A deterministic prefix leading to `y` does not change the law of what follows. -/
theorem seq_det {y : Data r} (h₁ : ExecWithin w c₁ x y T₁) (h₂ : ExecRandLaw w c₂ y Q T₂ R f μ) :
    ExecRandLaw w (.seq c₁ c₂) x Q (T₁ + T₂) R f μ := by
  have h := seq (g := fun _ => ()) (ν := PMF.pure ()) (κ := fun _ => μ) (R₁ := 0) (P := (· = y))
    (of_execWithin h₁ rfl) (fun y' hy' => hy' ▸ h₂)
  simpa only [PMF.pure_bind, Nat.zero_add] using h

/-- A deterministic suffix that keeps the observation does not change the law. -/
theorem seq_det_right (h₁ : ExecRandLaw w c₁ x P T₁ R f μ)
    (h₂ : ∀ y, P y → ∃ y', ExecWithin w c₂ y y' T₂ ∧ Q y' ∧ f y' = f y) :
    ExecRandLaw w (.seq c₁ c₂) x Q (T₁ + T₂) R f μ := by
  have h := seq (g := f) (κ := PMF.pure) (R₂ := 0) h₁ fun y hy => by
    obtain ⟨y', hy', hQ, hf⟩ := h₂ y hy
    rw [← hf]
    exact of_execWithin hy' hQ
  simpa only [PMF.bind_pure, Nat.add_zero] using h

/-- A `rand` instruction followed by deterministic code: drawing `k` uniformly from
`[0, x.regs src]` leads to `y k`. -/
theorem rand_seq {dst src : Fin r} {y : Fin (x.regs src + 1) → Data r} (hfit : Fits w (x.regs src))
    (h₂ : ∀ k, ExecWithin w c₂ (x.set dst k.val) (y k) T₂) (hP : ∀ k, P (y k)) :
    ExecRandLaw w (.seq (.rand dst src) c₂) x P (1 + T₂) 1 f
      ((Probability.PMF.uniformOfFintype (Fin (x.regs src + 1))).map fun k => f (y k)) := by
  classical
  let κ : ℕ → PMF α := fun j =>
    if hj : j < x.regs src + 1 then PMF.pure (f (y ⟨j, hj⟩)) else PMF.pure (f x)
  have h := seq (g := fun d => d.regs dst) (κ := κ) (R₂ := 0)
    (P := fun d => ∃ k : Fin (x.regs src + 1), d = x.set dst k.val) (rand hfit fun k => ⟨k, rfl⟩)
    (fun d ⟨k, hk⟩ => by
      subst hk
      have hκ : κ ((x.set dst k.val).regs dst) = PMF.pure (f (y k)) := by
        simp only [κ, Data.set_regs, Function.update_self, k.isLt, ↓reduceDIte]
      rw [hκ]
      exact of_execWithin (h₂ k) (hP k))
  refine (h.congr_law ?_).mono (fun _ h => h) le_rfl le_rfl
  rw [PMF.bind_map, ← PMF.bind_pure_comp]
  congr 1
  funext k
  simp only [Function.comp_apply, κ, Data.set_regs, Function.update_self, k.isLt, ↓reduceDIte]

/-- Taking the positive branch adds one instruction and keeps the law. -/
theorem branch_pos (hc : cond.Holds x) (h : ExecRandLaw w pos x P T R f μ) :
    ExecRandLaw w (.branch cond pos neg) x P (T + 1) R f μ := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := h
  refine ⟨_, ExecRand.branch_pos hc hm, (OracleComp.isCostBounded_map_iff _ _ _).mpr hq, ?_, ?_⟩
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    exact ⟨(hsup z₀ hz₀).1, Nat.add_le_add_right (hsup z₀ hz₀).2 1⟩
  · rw [← hlaw, Functor.map_map]

/-- Taking the negative branch adds two instructions and keeps the law. -/
theorem branch_neg (hc : ¬cond.Holds x) (h : ExecRandLaw w neg x P T R f μ) :
    ExecRandLaw w (.branch cond pos neg) x P (T + 2) R f μ := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := h
  refine ⟨_, ExecRand.branch_neg hc hm, (OracleComp.isCostBounded_map_iff _ _ _).mpr hq, ?_, ?_⟩
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    exact ⟨(hsup z₀ hz₀).1, Nat.add_le_add_right (hsup z₀ hz₀).2 2⟩
  · rw [← hlaw, Functor.map_map]

/-- Exiting a loop takes two instructions and observes the current data. -/
theorem loop_exit (hc : ¬cond.Holds x) (hx : P x) :
    ExecRandLaw w (.loop cond body) x P 2 0 f (PMF.pure (f x)) :=
  of_execWithin (ExecWithin.loop_exit hc) hx

/-- **One loop iteration.** The body's observation `g` determines the law of the rest of the
loop, and the laws compose by `PMF.bind`. -/
theorem loop_iter {g : Data r → β} {ν : PMF β} {κ : β → PMF α} (hc : cond.Holds x)
    (hb : ExecRandLaw w body x P T₁ R₁ g ν)
    (hl : ∀ y, P y → ExecRandLaw w (.loop cond body) y Q T₂ R₂ f (κ (g y))) :
    ExecRandLaw w (.loop cond body) x Q (T₁ + T₂ + 2) (R₁ + R₂) f (ν.bind κ) := by
  obtain ⟨mb, hmb, hqb, hsupb, hlawb⟩ := hb
  have hstep : ∀ z₁ ∈ mb.support,
      ExecRand w (.loop cond body) z₁.1 (codeComp w (.loop cond body) z₁.1) ∧
      (codeComp w (.loop cond body) z₁.1).IsQueryBounded R₂ ∧
      (∀ z₂ ∈ (codeComp w (.loop cond body) z₁.1).support, Q z₂.1 ∧ z₂.2 ≤ T₂) ∧
      ((fun z => f z.1) <$> codeComp w (.loop cond body) z₁.1).eval = κ (g z₁.1) := by
    intro z₁ hz₁
    obtain ⟨ml, hml, hql, hsupl, hlawl⟩ := hl z₁.1 (hsupb z₁ hz₁).1
    rw [hml.codeComp_eq]
    exact ⟨hml, hql, hsupl, hlawl⟩
  refine ⟨_, ExecRand.loop_iter hc hmb fun z₁ hz₁ => (hstep z₁ hz₁).1, ?_, ?_, ?_⟩
  · refine OracleComp.IsCostBounded.bind_on_support hqb fun z₁ hz₁ => ?_
    simpa only [Nat.add_zero] using
      (hstep z₁ hz₁).2.1.bind fun _ => .pure _ 0
  · intro z hz
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z₂, hz₂, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hfinal
    have h₁' := hsupb z₁ hz₁
    have h₂' := (hstep z₁ hz₁).2.2.1 z₂ hz₂
    exact ⟨h₂'.1, by omega⟩
  · rw [← hlawb]
    simp only [map_bind, map_pure, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map,
      PMF.bind_map]
    refine Probability.PMF.bind_congr_on_support _ _ _ fun z₁ hz₁ => ?_
    rw [ProbComp.support_eval] at hz₁
    rw [Function.comp_apply, ← (hstep z₁ hz₁).2.2.2, ProbComp.eval_map]
    rfl

/-- **Compiled programs.** Compiling `c` with `Code.program out` halts on every path within any
fuel `T' ≥ T + 1`, makes at most `R` `rand` calls, satisfies the postcondition on the halting
data, and every observation `F` of halting configurations that agrees with `f` has law `μ`. -/
theorem program (h : ExecRandLaw w c x P T R f μ) (out : Fin r) (hT : T + 1 ≤ T')
    (F : RandCfg r → α) (hF : ∀ y, P y → F (.halted (y.regs out) y) = f y) :
    RandHaltsWithin w (c.program out) ⟨0, x⟩ T' ∧
    RandCallsBounded w (c.program out) ⟨0, x⟩ T' R ∧
    (∀ cfg ∈ (runRand w (c.program out) T' (.running ⟨0, x⟩)).support,
      ∃ y, cfg = .halted (y.regs out) y ∧ P y) ∧
    (evalRand w (c.program out) T' ⟨0, x⟩).map F = μ := by
  obtain ⟨hhalt, hcalls, hpost⟩ := h.execRandWithin.program out hT
  refine ⟨hhalt, hcalls, hpost, ?_⟩
  obtain ⟨m, hm, -, hsup, hlaw⟩ := h
  have hrun := hm.runRand_program out (T := T') fun z hz =>
    (Nat.add_le_add_right (hsup z hz).2 1).trans hT
  rw [evalRand, hrun, ← hlaw, ProbComp.eval_map, ProbComp.eval_map, PMF.map_comp]
  refine Probability.PMF.map_congr_on_support _ _ _ fun z hz => ?_
  rw [ProbComp.support_eval] at hz
  exact hF z.1 (hsup z hz).1

end ExecRandLaw

end Cslib.WordRAM

end
