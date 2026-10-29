/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.Randomized.Structured

/-!
# Compositional while-loop segments for structured randomized word-RAM programs

`Cslib.WordRAM.LoopSegment w cond body x m` represents executing zero or more active iterations of
`Code.loop cond body` starting at machine state `x : Data r` and producing the randomized
state-time distribution `m : ProbComp (Data r × ℕ)`, without yet performing the final loop-exit
condition check.

Whereas `ExecRand.loop_iter` and `ExecRand.loop_exit` require each iteration to continue all the
way to termination of the enclosing loop (`¬cond.Holds`), `LoopSegment` packages multi-iteration
sub-runs that may finish in states where `cond.Holds` still holds. This allows explicit call-stack
algorithms (such as Karger and Stein's recursive `FastCut` simulated inside a single `while sp > 0`
loop) to prove frame execution by structural induction on stack depth `sp = b + 1 → b`, compose
sibling recursive subtrees via `LoopSegment.trans`, and discharge the outer `while sp > 0` loop at
depth `b = 0` via `LoopSegment.finish`.

## Main definitions

* `Cslib.WordRAM.LoopSegment`: multi-iteration execution segments of `Code.loop cond body` before
  loop exit.

## Main results

* `Cslib.WordRAM.LoopSegment.single`, `Cslib.WordRAM.LoopSegment.detSingle`: single randomized or
  deterministic loop iteration (`+ 2` loop-header instructions).
* `Cslib.WordRAM.LoopSegment.trans`, `Cslib.WordRAM.LoopSegment.trans_exists`,
  `Cslib.WordRAM.LoopSegment.stepDet`: transitive and deterministic-prefix sequential composition of
  loop segments.
* `Cslib.WordRAM.LoopSegment.finish`: closes a `LoopSegment` into `ExecRand w (.loop cond body)`
  once every supported output violates `cond` (`+ 2` instructions for the final exit check).
* `Cslib.WordRAM.LoopSegment.regs_eq`, `Cslib.WordRAM.LoopSegment.bounded`: register preservation
  and word-bound invariance across a `LoopSegment`.
* `Cslib.WordRAM.execRand_seq_det`: appends a deterministic `ExecWithin` continuation onto a
  randomized `ExecRand` computation as a pure `Functor.map`.

## References

* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
-/

@[expose] public section

namespace Cslib.WordRAM

/-- `LoopSegment w cond body x m`: starting at data `x`, executing zero or more iterations of
`Code.loop cond body` (each verifying `cond.Holds`, running `body`, and charging `+ 2` for the loop
header test and back-jump) without yet taking the loop-exit check produces `m`.

Enables structural induction on explicit call-stack depth inside a single outer `while sp > 0`
loop, where popping a recursive frame lowers `sp` from `b + 1` to `b` without exiting the loop when
`b > 0`. -/
inductive LoopSegment {B : Basis} {r : ℕ} (w : ℕ) (cond : Cond r) (body : Code B r) :
    Data r → ProbComp (Data r × ℕ) → Prop where
  /-- Zero iterations, charging `0` instructions. -/
  | nil (x : Data r) : LoopSegment w cond body x (pure (x, 0))
  /-- One active loop iteration followed by a continuation segment. -/
  | step {x : Data r} {mb : ProbComp (Data r × ℕ)} {mr : Data r → ProbComp (Data r × ℕ)}
      (hc : cond.Holds x)
      (hb : ExecRand w body x mb)
      (hr : ∀ z ∈ mb.support, LoopSegment w cond body z.1 (mr z.1)) :
      LoopSegment w cond body x (do
        let z₁ ← mb
        let z₂ ← mr z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + 2))

namespace LoopSegment

variable {B : Basis} {r w : ℕ} {cond : Cond r} {body : Code B r}

/-- A single randomized loop iteration (`+ 2` loop-header instructions). -/
theorem single {x : Data r} {mb : ProbComp (Data r × ℕ)}
    (hc : cond.Holds x) (hb : ExecRand w body x mb) :
    LoopSegment w cond body x ((fun z => (z.1, z.2 + 2)) <$> mb) := by
  have h := LoopSegment.step hc hb (mr := fun d => pure (d, 0)) fun z _ => .nil z.1
  simpa only [pure_bind, Nat.add_zero, ← bind_pure_comp] using h

/-- A single deterministic loop iteration (`+ 2` loop-header instructions). -/
theorem detSingle {x y : Data r} {n : ℕ}
    (hc : cond.Holds x) (hb : Exec w body x y n) :
    LoopSegment w cond body x (pure (y, n + 2)) := by
  simpa only [map_pure] using single hc hb.execRand

/-- Sequential composition of two loop segments. -/
theorem trans {x : Data r} {m₁ : ProbComp (Data r × ℕ)} {m₂ : Data r → ProbComp (Data r × ℕ)}
    (h₁ : LoopSegment w cond body x m₁)
    (h₂ : ∀ z ∈ m₁.support, LoopSegment w cond body z.1 (m₂ z.1)) :
    LoopSegment w cond body x (do
      let z₁ ← m₁
      let z₂ ← m₂ z₁.1
      pure (z₂.1, z₁.2 + z₂.2)) := by
  induction h₁ with
  | nil x =>
    have hx : (x, 0) ∈ (pure (x, 0) : ProbComp (Data r × ℕ)).support := by simp
    have h₂x := h₂ (x, 0) hx
    have heq : (do
        let z₁ ← (pure (x, 0) : ProbComp (Data r × ℕ))
        let z₂ ← m₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2)) = m₂ x := by
      simp only [pure_bind, Nat.zero_add, Prod.mk.eta, bind_pure]
    rw [heq]
    exact h₂x
  | @step x mb mr hc hb hr ih =>
    let mr' : Data r → ProbComp (Data r × ℕ) := fun d => do
      let b ← mr d
      let c ← m₂ b.1
      pure (c.1, b.2 + c.2)
    have hnext : ∀ a ∈ mb.support, LoopSegment w cond body a.1 (mr' a.1) := by
      intro a ha
      refine ih a ha fun b hb_mem => h₂ (b.1, a.2 + b.2 + 2) ?_
      rw [OracleComp.mem_supportWith_bind_iff]
      refine ⟨a, ha, ?_⟩
      rw [OracleComp.mem_supportWith_bind_iff]
      exact ⟨b, hb_mem, by simp⟩
    have hstep := LoopSegment.step (mr := mr') hc hb hnext
    convert hstep using 1
    simp only [mr', bind_assoc, pure_bind, Nat.add_assoc]
    refine congrArg (mb >>= ·) (funext fun a => ?_)
    refine congrArg (mr a.1 >>= ·) (funext fun b => ?_)
    refine congrArg (m₂ b.1 >>= ·) (funext fun c => ?_)
    congr 2
    omega

/-- Existential sequential composition of two loop segments using `Classical.choose`. -/
theorem trans_exists {x : Data r} {m₁ : ProbComp (Data r × ℕ)}
    {Q : Data r → ProbComp (Data r × ℕ) → Prop}
    (h₁ : LoopSegment w cond body x m₁)
    (h₂ : ∀ z ∈ m₁.support, ∃ m', LoopSegment w cond body z.1 m' ∧ Q z.1 m') :
    ∃ m₂ : Data r → ProbComp (Data r × ℕ),
      LoopSegment w cond body x (do
        let z₁ ← m₁
        let z₂ ← m₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2)) ∧
      ∀ z ∈ m₁.support, LoopSegment w cond body z.1 (m₂ z.1) ∧ Q z.1 (m₂ z.1) := by
  classical
  let m₂ : Data r → ProbComp (Data r × ℕ) := fun d =>
    if h : ∃ m', LoopSegment w cond body d m' ∧ Q d m' then h.choose else pure (d, 0)
  have hm₂ : ∀ z ∈ m₁.support, LoopSegment w cond body z.1 (m₂ z.1) ∧ Q z.1 (m₂ z.1) := by
    intro z hz
    have hex := h₂ z hz
    simp only [m₂, hex, ↓reduceDIte]
    exact hex.choose_spec
  exact ⟨m₂, h₁.trans fun z hz => (hm₂ z hz).1, hm₂⟩

/-- Prepending a deterministic single iteration onto a continuation `LoopSegment`. -/
theorem stepDet {x y : Data r} {n₁ : ℕ} {m₂ : ProbComp (Data r × ℕ)}
    (hc : cond.Holds x) (hb : Exec w body x y n₁)
    (hr : LoopSegment w cond body y m₂) :
    LoopSegment w cond body x ((fun z => (z.1, n₁ + 2 + z.2)) <$> m₂) := by
  have h := (detSingle hc hb).trans (m₂ := fun _ => m₂) fun z hz => by
    cases OracleComp.eq_of_mem_supportWith_pure hz
    exact hr
  simpa only [pure_bind, ← bind_pure_comp] using h

/-- Closing a `LoopSegment` into `ExecRand w (.loop cond body)` once every supported state
violates `cond` (`+ 2` instructions for the final loop-exit check). -/
theorem finish {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : LoopSegment w cond body x m)
    (hexit : ∀ z ∈ m.support, ¬cond.Holds z.1) :
    ExecRand w (.loop cond body) x ((fun z => (z.1, z.2 + 2)) <$> m) := by
  induction h with
  | nil x =>
    have hx : ¬cond.Holds x := hexit (x, 0) (by simp)
    simpa only [map_pure] using ExecRand.loop_exit hx
  | @step x mb mr hc hb hr ih =>
    let ml' : Data r → ProbComp (Data r × ℕ) := fun d =>
      (fun b => (b.1, b.2 + 2)) <$> mr d
    have hcont : ∀ a ∈ mb.support,
        ExecRand w (.loop cond body) a.1 (ml' a.1) := by
      intro a ha
      refine ih a ha fun b hb_mem => hexit (b.1, a.2 + b.2 + 2) ?_
      rw [OracleComp.mem_supportWith_bind_iff]
      refine ⟨a, ha, ?_⟩
      rw [OracleComp.mem_supportWith_bind_iff]
      exact ⟨b, hb_mem, by simp⟩
    have hiter := ExecRand.loop_iter (ml := ml') hc hb hcont
    convert hiter using 1
    simp only [ml', ← bind_pure_comp, bind_assoc, pure_bind, Nat.add_assoc]

/-- Any register preserved by `body` is preserved along every `LoopSegment`. -/
theorem regs_eq {x : Data r} {m : ProbComp (Data r × ℕ)} {i : Fin r}
    (h : LoopSegment w cond body x m) (hi : body.Preserves i)
    {z : Data r × ℕ} (hz : z ∈ m.support) :
    z.1.regs i = x.regs i := by
  induction h generalizing z with
  | nil _ =>
    cases OracleComp.eq_of_mem_supportWith_pure hz
    rfl
  | step _ hb _ ih =>
    obtain ⟨a, ha, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨b, hb_mem, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hpure
    exact (ih a ha hb_mem).trans (hb.regs_eq hi ha)

private theorem bounded_aux {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : LoopSegment w cond body x m) (hx : x.Bounded w) :
    ∀ z : Data r × ℕ, z ∈ m.support → z.1.Bounded w := by
  induction h with
  | nil _ =>
    intro z hz
    cases OracleComp.eq_of_mem_supportWith_pure hz
    exact hx
  | step _ hb _ ih =>
    intro z hz
    obtain ⟨a, ha, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨b, hb_mem, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hpure
    exact ih a ha (hb.bounded hx ha) b hb_mem

/-- `LoopSegment` preserves `Data.Bounded w` on every supported path. -/
theorem bounded {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : LoopSegment w cond body x m) (hx : x.Bounded w)
    {z : Data r × ℕ} (hz : z ∈ m.support) :
    z.1.Bounded w :=
  bounded_aux h hx z hz

end LoopSegment

/-- Append a deterministic `ExecWithin` continuation onto a randomized `ExecRand` computation as a
pure `Functor.map`. -/
theorem execRand_seq_det {B : Basis} {r w T : ℕ} {c₁ c₂ : Code B r} {x : Data r}
    {m₁ : ProbComp (Data r × ℕ)} {Q : Data r → Data r → Prop}
    (h₁ : ExecRand w c₁ x m₁)
    (h₂ : ∀ z ∈ m₁.support, ∃ y, ExecWithin w c₂ z.1 y T ∧ Q z.1 y) :
    ∃ g : Data r → Data r × ℕ,
      ExecRand w (.seq c₁ c₂) x ((fun z => ((g z.1).1, z.2 + (g z.1).2)) <$> m₁) ∧
      ∀ z ∈ m₁.support, (g z.1).2 ≤ T ∧ Exec w c₂ z.1 (g z.1).1 (g z.1).2 ∧ Q z.1 (g z.1).1 := by
  classical
  let g : Data r → Data r × ℕ := fun d =>
    if h : ∃ y, ExecWithin w c₂ d y T ∧ Q d y then
      (h.choose, h.choose_spec.1.choose)
    else (d, 0)
  have hg : ∀ z ∈ m₁.support,
      (g z.1).2 ≤ T ∧ Exec w c₂ z.1 (g z.1).1 (g z.1).2 ∧ Q z.1 (g z.1).1 := by
    intro z hz
    have hex := h₂ z hz
    simp only [g, hex, ↓reduceDIte]
    exact ⟨hex.choose_spec.1.choose_spec.1, hex.choose_spec.1.choose_spec.2, hex.choose_spec.2⟩
  have hseq := ExecRand.seq h₁ (m₂ := fun d => pure (g d)) fun z hz => (hg z hz).2.1.execRand
  have heq : (do
      let z₁ ← m₁
      let z₂ ← (pure (g z₁.1) : ProbComp (Data r × ℕ))
      pure (z₂.1, z₁.2 + z₂.2)) =
      ((fun z => ((g z.1).1, z.2 + (g z.1).2)) <$> m₁) := by
    simp only [pure_bind, ← bind_pure_comp]
  rw [heq] at hseq
  exact ⟨g, hseq, hg⟩

end Cslib.WordRAM
