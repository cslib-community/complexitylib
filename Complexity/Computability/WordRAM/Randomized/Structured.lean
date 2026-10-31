/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.Compile
public import Complexity.Computability.WordRAM.Randomized.Defs

/-!
# Structured randomized word-RAM programs

`Cslib.WordRAM.ExecRand w c x m` is the randomized counterpart of `Cslib.WordRAM.Exec`: at word
size `w`, running the structured program `c : Code B r` from `x : Data r` terminates without
faulting on every path and yields the `ProbComp (Data r × ℕ)` computation `m`, pairing each final
machine data `y` with the exact number of compiled instructions `n` executed along that path.

`Cslib.WordRAM.ExecRandWithin w c x P T R` bundles `ExecRand` with a pathwise postcondition `P`, a
worst-case instruction budget `T`, and a worst-case `rand`-call budget `R` (`IsQueryBounded`),
supporting Hoare-style rules for data instructions, `rand`, sequencing, branches, and potential
loops (`ExecRandWithin.loop_potential`).

Every structured randomized execution refines `Code.assemble` (`ExecRand.runRand_assemble`) and
compiles via `Code.program out` to a flat `Program B r` establishing `RandHaltsWithin`,
`RandCallsBounded`, and the memory postcondition `P` directly on `RandCfg.halted`
(`ExecRandWithin.program`).

## Main definitions

* `Cslib.WordRAM.ExecRand`: exact randomized execution of `Code B r` into `ProbComp (Data r × ℕ)`.
* `Cslib.WordRAM.codeComp`: canonical `ProbComp (Data r × ℕ)` associated with `(w, c, x)`.
* `Cslib.WordRAM.ExecRandWithin`: pathwise postcondition, worst-case instruction bound, and
  `rand`-call budget on `Code B r`.

## Main results

* `Cslib.WordRAM.ExecRand.unique`: `m` is uniquely determined by `(w, c, x)`.
* `Cslib.WordRAM.Exec.execRand`, `Cslib.WordRAM.ExecWithin.execRandWithin`: deterministic
  structured executions lift with zero `rand` calls.
* `Cslib.WordRAM.ExecRandWithin.loop_potential`: potential-based termination, worst-case time, and
  `rand`-call rule for randomized loops.
* `Cslib.WordRAM.ExecRand.runRand_assemble`, `Cslib.WordRAM.ExecRand.runRand_program`,
  `Cslib.WordRAM.Exec.runRand_program`, `Cslib.WordRAM.ExecRandWithin.program`: assembly
  refinement into flat `runRand`, `RandHaltsWithin`, and `RandCallsBounded`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r r' : ℕ}

/-! ## Structured randomized executions -/

/-- `ExecRand w c x m`: at word size `w`, the structured program `c` runs from data `x` without
faulting on any path and induces the `ProbComp (Data r × ℕ)` computation `m` of `(finalData, steps)`
matching the exact instruction counts of `Code.assemble`. -/
inductive ExecRand (w : ℕ) : Code B r → Data r → ProbComp (Data r × ℕ) → Prop where
  /-- A data instruction executes in `1` instruction and issues `0` calls. -/
  | op {o : Op B r} {x y : Data r} (h : o.eval w x = some y) :
      ExecRand w (.op o) x (pure (y, 1))
  /-- `Code.rand dst src` draws uniformly from `[0, x.regs src]` in `1` instruction when the bound
  fits a word. -/
  | rand {dst src : Fin r} {x : Data r} (h : Fits w (x.regs src)) :
      ExecRand w (.rand dst src) x (do
        let k ← ProbComp.unifFin (x.regs src)
        pure (x.set dst k.val, 1))
  /-- Sequencing composes the two computations and adds their instruction counts. -/
  | seq {c₁ c₂ : Code B r} {x : Data r} {m₁ : ProbComp (Data r × ℕ)}
      {m₂ : Data r → ProbComp (Data r × ℕ)}
      (h₁ : ExecRand w c₁ x m₁)
      (h₂ : ∀ z ∈ m₁.support, ExecRand w c₂ z.1 (m₂ z.1)) :
      ExecRand w (.seq c₁ c₂) x (do
        let z₁ ← m₁
        let z₂ ← m₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2))
  /-- Taking the positive branch adds `1` instruction for the branch test. -/
  | branch_pos {c : Cond r} {pos neg : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
      (hc : c.Holds x) (h : ExecRand w pos x m) :
      ExecRand w (.branch c pos neg) x ((fun z => (z.1, z.2 + 1)) <$> m)
  /-- Taking the negative branch adds `2` instructions (branch test and jump past `pos`). -/
  | branch_neg {c : Cond r} {pos neg : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
      (hc : ¬c.Holds x) (h : ExecRand w neg x m) :
      ExecRand w (.branch c pos neg) x ((fun z => (z.1, z.2 + 2)) <$> m)
  /-- Exiting a loop when the condition fails takes `2` instructions (branch test and exit jump). -/
  | loop_exit {c : Cond r} {body : Code B r} {x : Data r} (hc : ¬c.Holds x) :
      ExecRand w (.loop c body) x (pure (x, 2))
  /-- Entering a loop executes `body`, jumps back to the header, and continues the loop, adding `2`
  instructions for the branch test and back-jump. -/
  | loop_iter {c : Cond r} {body : Code B r} {x : Data r} {mb : ProbComp (Data r × ℕ)}
      {ml : Data r → ProbComp (Data r × ℕ)}
      (hc : c.Holds x)
      (hb : ExecRand w body x mb)
      (hl : ∀ z ∈ mb.support, ExecRand w (.loop c body) z.1 (ml z.1)) :
      ExecRand w (.loop c body) x (do
        let z₁ ← mb
        let z₂ ← ml z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + 2))

namespace ExecRand

variable {w : ℕ}

/-- The `ProbComp` tree of a structured execution is uniquely determined by `(w, c, x)`. -/
theorem unique {c : Code B r} {x : Data r} {m m' : ProbComp (Data r × ℕ)}
    (h : ExecRand w c x m) (h' : ExecRand w c x m') : m = m' := by
  induction h generalizing m' with
  | op ho =>
    cases h' with
    | op ho' => rw [ho] at ho'; cases ho'; rfl
  | rand _ =>
    cases h' with
    | rand _ => rfl
  | seq _ _ ih₁ ih₂ =>
    cases h' with
    | seq h₁' h₂' =>
      obtain rfl := ih₁ h₁'
      refine OracleComp.bind_congr_on_support fun z₁ hz₁ => ?_
      rw [ih₂ z₁ hz₁ (h₂' z₁ hz₁)]
  | branch_pos hc _ ih =>
    cases h' with
    | branch_pos _ hp => rw [ih hp]
    | branch_neg hc' _ => exact absurd hc hc'
  | branch_neg hc _ ih =>
    cases h' with
    | branch_pos hc' _ => exact absurd hc' hc
    | branch_neg _ hn => rw [ih hn]
  | loop_exit hc =>
    cases h' with
    | loop_exit _ => rfl
    | loop_iter hc' _ _ => exact absurd hc' hc
  | loop_iter hc _ _ ihb ihl =>
    cases h' with
    | loop_exit hc' => exact absurd hc hc'
    | loop_iter _ hb' hl' =>
      obtain rfl := ihb hb'
      refine OracleComp.bind_congr_on_support fun z₁ hz₁ => ?_
      rw [ihl z₁ hz₁ (hl' z₁ hz₁)]

/-- Every structured execution takes at least `1` instruction on every path. -/
theorem pos {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : ExecRand w c x m) {z : Data r × ℕ} (hz : z ∈ m.support) : 1 ≤ z.2 := by
  induction h generalizing z with
  | op _ =>
    cases OracleComp.eq_of_mem_supportWith_pure hz
    omega
  | rand _ =>
    obtain ⟨_, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hk
    omega
  | seq _ _ ih₁ _ =>
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z₂, -, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hfinal
    have := ih₁ hz₁
    omega
  | branch_pos _ _ _ =>
    obtain ⟨z₀, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    omega
  | branch_neg _ _ _ =>
    obtain ⟨z₀, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    omega
  | loop_exit _ =>
    cases OracleComp.eq_of_mem_supportWith_pure hz
    omega
  | loop_iter _ _ _ _ _ =>
    obtain ⟨z₁, -, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z₂, -, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hfinal
    omega

/-- Structured randomized executions preserve word-boundedness on every supported path. -/
theorem bounded {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : ExecRand w c x m) (hx : x.Bounded w) {z : Data r × ℕ} (hz : z ∈ m.support) :
    z.1.Bounded w := by
  induction h generalizing z with
  | op ho =>
    cases OracleComp.eq_of_mem_supportWith_pure hz
    exact hx.op ho
  | rand hfit =>
    obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hk
    exact hx.set (hfit.of_le (Nat.le_of_lt_succ k.isLt))
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z₂, hz₂, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hfinal
    have hb₁ := ih₁ hx hz₁
    have hb₂ := ih₂ z₁ hz₁ hb₁ hz₂
    exact hb₂
  | branch_pos _ _ ih | branch_neg _ _ ih =>
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    have hb₀ := ih hx hz₀
    exact hb₀
  | loop_exit _ =>
    cases OracleComp.eq_of_mem_supportWith_pure hz
    exact hx
  | loop_iter _ _ _ ihb ihl =>
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z₂, hz₂, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hfinal
    have hb₁ := ihb hx hz₁
    have hb₂ := ihl z₁ hz₁ hb₁ hz₂
    exact hb₂

/-- A register that `c` does not write retains its value on every supported path. -/
theorem regs_eq {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)} {i : Fin r}
    (h : ExecRand w c x m) (hi : c.Preserves i) {z : Data r × ℕ} (hz : z ∈ m.support) :
    z.1.regs i = x.regs i := by
  induction h generalizing z with
  | op ho =>
    cases OracleComp.eq_of_mem_supportWith_pure hz
    exact (Exec.op ho).regs_eq hi
  | rand _ =>
    obtain ⟨k, -, hk⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hk
    simp only [Data.set_regs, Function.update_of_ne (Ne.symm hi)]
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z₂, hz₂, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hfinal
    have hr₁ := ih₁ hi.1 hz₁
    have hr₂ := ih₂ z₁ hz₁ hi.2 hz₂
    exact hr₂.trans hr₁
  | branch_pos _ _ ih =>
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    have hr₀ := ih hi.1 hz₀
    exact hr₀
  | branch_neg _ _ ih =>
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    have hr₀ := ih hi.2 hz₀
    exact hr₀
  | loop_exit _ =>
    cases OracleComp.eq_of_mem_supportWith_pure hz
    rfl
  | loop_iter _ _ _ ihb ihl =>
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z₂, hz₂, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hfinal
    have hr₁ := ihb hi hz₁
    have hr₂ := ihl z₁ hz₁ hi hz₂
    exact hr₂.trans hr₁

end ExecRand

/-- Canonical `ProbComp (Data r × ℕ)` of a structured program `c` from `x` when `ExecRand w c x m`
holds for some `m` (unique by `ExecRand.unique`), and `pure (x, 0)` otherwise. -/
noncomputable def codeComp (w : ℕ) (c : Code B r) (x : Data r) : ProbComp (Data r × ℕ) :=
  open Classical in
  if h : ∃ m, ExecRand w c x m then h.choose else pure (x, 0)

/-- When `ExecRand w c x m` holds, `codeComp w c x` equals `m`. -/
theorem ExecRand.codeComp_eq {w : ℕ} {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : ExecRand w c x m) : codeComp w c x = m := by
  classical
  have hex : ∃ m', ExecRand w c x m' := ⟨m, h⟩
  simp only [codeComp, hex, ↓reduceDIte]
  exact hex.choose_spec.unique h

/-- Every deterministic structured execution `Exec w c x y n` lifts to
`ExecRand w c x (pure (y, n))`. -/
theorem Exec.execRand {w : ℕ} {c : Code B r} {x y : Data r} {n : ℕ} (h : Exec w c x y n) :
    ExecRand w c x (pure (y, n)) := by
  induction h with
  | op ho => exact .op ho
  | @seq c₁ c₂ x y z m n _ _ ih₁ ih₂ =>
    have hseq := ExecRand.seq ih₁ (m₂ := fun _ => pure (z, n)) fun z' hz' => by
      cases OracleComp.eq_of_mem_supportWith_pure hz'
      exact ih₂
    simpa only [pure_bind] using hseq
  | branch_pos hc _ ih =>
    simpa only [map_pure] using ExecRand.branch_pos hc ih
  | branch_neg hc _ ih =>
    simpa only [map_pure] using ExecRand.branch_neg hc ih
  | loop_exit hc => exact .loop_exit hc
  | @loop_iter c body x y z m n hc _ _ ihb ihl =>
    have hiter := ExecRand.loop_iter hc ihb (ml := fun _ => pure (z, n)) fun z' hz' => by
      cases OracleComp.eq_of_mem_supportWith_pure hz'
      exact ihl
    simpa only [pure_bind] using hiter

/-- Prepending a deterministic `Exec` onto a randomized `ExecRand` shifts the instruction count by
`n₁`. -/
theorem Exec.seqRand {w : ℕ} {c₁ c₂ : Code B r} {x y : Data r} {n₁ : ℕ}
    {m₂ : ProbComp (Data r × ℕ)} (h₁ : Exec w c₁ x y n₁) (h₂ : ExecRand w c₂ y m₂) :
    ExecRand w (.seq c₁ c₂) x ((fun z => (z.1, n₁ + z.2)) <$> m₂) := by
  have hseq := ExecRand.seq h₁.execRand (m₂ := fun _ => m₂) fun z' hz' => by
    cases OracleComp.eq_of_mem_supportWith_pure hz'
    exact h₂
  simpa only [pure_bind, ← bind_pure_comp] using hseq

/-! ## Renaming registers in structured randomized executions -/

section Rename

variable {f : Fin r → Fin r'}

/-- Running a structured randomized program through an injective register map `f` transforms its
outputs via `Data.extend f x`, preserving instruction counts and untouched registers. -/
theorem ExecRand.rename (hf : f.Injective) {w : ℕ} {c : Code B r} {x : Data r'}
    {m : ProbComp (Data r × ℕ)} (h : ExecRand w c (x.comap f) m) :
    ExecRand w (c.rename f) x ((fun z => (z.1.extend f x, z.2)) <$> m) := by
  generalize hx : x.comap f = x₀ at h
  induction h generalizing x with
  | @op o _ y ho =>
    subst hx
    have ho' : (o.rename f).eval w x = some (y.extend f x) := by
      rw [Op.eval_rename hf, ho]
      rfl
    simpa only [Code.rename, map_pure] using ExecRand.op ho'
  | @rand dst src _ hfit =>
    subst hx
    have hfit' : Fits w (x.regs (f src)) := hfit
    have heq : ((fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> (do
        let k ← ProbComp.unifFin (x.regs (f src))
        pure ((x.comap f).set dst k.val, 1))) = (do
        let k ← ProbComp.unifFin (x.regs (f src))
        pure (x.set (f dst) k.val, 1)) := by
      rw [← bind_pure_comp, bind_assoc]
      refine congrArg (ProbComp.unifFin (x.regs (f src)) >>= ·) (funext fun k => ?_)
      simp only [pure_bind, Data.extend_set hf, Data.extend_comap hf]
    simp only [Code.rename, Data.comap_regs]
    rw [heq]
    exact ExecRand.rand hfit'
  | @seq c₁ c₂ _ m₁ m₂ _ h₂ ih₁ ih₂ =>
    subst hx
    have h₁' := ih₁ rfl
    have hseq := ExecRand.seq h₁'
      (m₂ := fun y' => (fun z => (z.1.extend f x, z.2)) <$> codeComp w c₂ (y'.comap f))
      fun z' hz' => by
        obtain ⟨z₁, hz₁, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz'
        have hm₂ : codeComp w c₂ ((z₁.1.extend f x).comap f) = m₂ z₁.1 := by
          rw [Data.comap_extend hf]
          exact (h₂ z₁ hz₁).codeComp_eq
        rw [hm₂]
        have h₂' := ih₂ z₁ hz₁ (x := z₁.1.extend f x) (Data.comap_extend hf z₁.1 x)
        simpa only [Data.extend_extend hf] using h₂'
    have heq : ((fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> (do
        let z₁ ← m₁
        let z₂ ← m₂ z₁.1
        pure (z₂.1, z₁.2 + z₂.2))) = (do
        let z₁ ← (fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> m₁
        let z₂ ← (fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> codeComp w c₂ (z₁.1.comap f)
        pure (z₂.1, z₁.2 + z₂.2)) := by
      simp only [← bind_pure_comp, bind_assoc, pure_bind]
      refine OracleComp.bind_congr_on_support fun z₁ hz₁ => ?_
      have hm₂ : codeComp w c₂ ((z₁.1.extend f x).comap f) = m₂ z₁.1 := by
        rw [Data.comap_extend hf]
        exact (h₂ z₁ hz₁).codeComp_eq
      rw [hm₂]
    simp only [Code.rename]
    rw [heq]
    exact hseq
  | @branch_pos cond pos neg _ m hc _ ih =>
    subst hx
    have h' := ExecRand.branch_pos (neg := neg.rename f) ((Cond.holds_rename _ _).2 hc) (ih rfl)
    simpa only [Code.rename, Functor.map_map] using h'
  | @branch_neg cond pos neg _ m hc _ ih =>
    subst hx
    have h' := ExecRand.branch_neg (pos := pos.rename f)
      (fun h => hc ((Cond.holds_rename _ _).1 h)) (ih rfl)
    simpa only [Code.rename, Functor.map_map] using h'
  | @loop_exit cond body _ hc =>
    subst hx
    simpa only [Code.rename, map_pure, Data.extend_comap hf] using
      ExecRand.loop_exit (body := body.rename f) (fun h => hc ((Cond.holds_rename _ _).1 h))
  | @loop_iter cond body _ mb ml hc _ hl ihb ihl =>
    subst hx
    have hb' := ihb rfl
    have hiter := ExecRand.loop_iter ((Cond.holds_rename _ _).2 hc) hb'
      (ml := fun y' =>
        (fun z => (z.1.extend f x, z.2)) <$> codeComp w (.loop cond body) (y'.comap f))
      fun z' hz' => by
        obtain ⟨z₁, hz₁, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz'
        have hml : codeComp w (.loop cond body) ((z₁.1.extend f x).comap f) = ml z₁.1 := by
          rw [Data.comap_extend hf]
          exact (hl z₁ hz₁).codeComp_eq
        rw [hml]
        have hl' := ihl z₁ hz₁ (x := z₁.1.extend f x) (Data.comap_extend hf z₁.1 x)
        change ExecRand w ((Code.loop cond body).rename f) (z₁.1.extend f x) _ at hl'
        simpa only [Code.rename, Data.extend_extend hf] using hl'
    have heq : ((fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> (do
        let z₁ ← mb
        let z₂ ← ml z₁.1
        pure (z₂.1, z₁.2 + z₂.2 + 2))) = (do
        let z₁ ← (fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$> mb
        let z₂ ← (fun z : Data r × ℕ => (z.1.extend f x, z.2)) <$>
          codeComp w (.loop cond body) (z₁.1.comap f)
        pure (z₂.1, z₁.2 + z₂.2 + 2)) := by
      simp only [← bind_pure_comp, bind_assoc, pure_bind]
      refine OracleComp.bind_congr_on_support fun z₁ hz₁ => ?_
      have hml : codeComp w (.loop cond body) ((z₁.1.extend f x).comap f) = ml z₁.1 := by
        rw [Data.comap_extend hf]
        exact (hl z₁ hz₁).codeComp_eq
      rw [hml]
    simp only [Code.rename]
    rw [heq]
    exact hiter

end Rename

/-! ## Hoare-style bounded structured execution (`ExecRandWithin`) -/

/-- `ExecRandWithin w c x P T R`: at word size `w`, running `c` from `x` terminates cleanly on every
path (`ExecRand`), makes at most `R` `rand` calls on every path, and every supported outcome
`(y, n)` satisfies `P y` and `n ≤ T`. -/
def ExecRandWithin (w : ℕ) (c : Code B r) (x : Data r) (P : Data r → Prop) (T R : ℕ) : Prop :=
  ∃ m, ExecRand w c x m ∧ m.IsQueryBounded R ∧ ∀ z ∈ m.support, P z.1 ∧ z.2 ≤ T

/-- Every deterministic `ExecWithin` lifts to `ExecRandWithin` with `0` `rand` calls. -/
theorem ExecWithin.execRandWithin {w T : ℕ} {c : Code B r} {x y : Data r} {P : Data r → Prop}
    (h : ExecWithin w c x y T) (hy : P y) :
    ExecRandWithin w c x P T 0 := by
  obtain ⟨n, hn, he⟩ := h
  refine ⟨pure (y, n), he.execRand, .pure _ 0, fun z hz => ?_⟩
  cases OracleComp.eq_of_mem_supportWith_pure hz
  exact ⟨hy, hn⟩

namespace ExecRandWithin

variable {w : ℕ} {c c₁ c₂ pos neg body : Code B r} {cond : Cond r} {x : Data r}
  {P Q : Data r → Prop} {T T' T₁ T₂ R R' R₁ R₂ : ℕ}

/-- Monotonicity / consequence rule for `ExecRandWithin`. -/
theorem mono (h : ExecRandWithin w c x P T R) (hPQ : ∀ y, P y → Q y)
    (hT : T ≤ T') (hR : R ≤ R') :
    ExecRandWithin w c x Q T' R' := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  exact ⟨m, hm, hq.mono hR, fun z hz => ⟨hPQ z.1 (hsup z hz).1, (hsup z hz).2.trans hT⟩⟩

/-- Strengthening `P` with `Data.Bounded w` when `x.Bounded w` holds initially. -/
theorem withBounded (h : ExecRandWithin w c x P T R) (hx : x.Bounded w) :
    ExecRandWithin w c x (fun y => P y ∧ y.Bounded w) T R := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  exact ⟨m, hm, hq, fun z hz => ⟨⟨(hsup z hz).1, hm.bounded hx hz⟩, (hsup z hz).2⟩⟩

/-- Strengthening `P` with preservation of a register `i` not written by `c`. -/
theorem withPreserves {i : Fin r} (h : ExecRandWithin w c x P T R) (hi : c.Preserves i) :
    ExecRandWithin w c x (fun y => P y ∧ y.regs i = x.regs i) T R := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  exact ⟨m, hm, hq, fun z hz => ⟨⟨(hsup z hz).1, hm.regs_eq hi hz⟩, (hsup z hz).2⟩⟩

/-- A single `op` instruction runs in `1` step and `0` `rand` calls. -/
theorem op {o : Op B r} {y : Data r} (ho : o.eval w x = some y) (hy : P y) :
    ExecRandWithin w (.op o) x P 1 0 :=
  (ExecWithin.op ho).execRandWithin hy

/-- `Code.rand dst src` runs in `1` step and `1` `rand` call when `x.regs src` fits a word. -/
theorem rand {dst src : Fin r} (hfit : Fits w (x.regs src))
    (hk : ∀ k : Fin (x.regs src + 1), P (x.set dst k.val)) :
    ExecRandWithin (B := B) w (.rand dst src) x P 1 1 := by
  refine ⟨_, ExecRand.rand hfit, ?_, ?_⟩
  · simpa only [Nat.add_zero] using
      (ProbComp.isQueryBounded_unifFin (x.regs src)).bind fun _ => .pure _ 0
  · intro z hz
    obtain ⟨k, -, hz'⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    cases OracleComp.eq_of_mem_supportWith_pure hz'
    exact ⟨hk k, le_rfl⟩

/-- Sequencing rule: composes `ExecRandWithin` specs and sums both step and call budgets. -/
theorem seq (h₁ : ExecRandWithin w c₁ x P T₁ R₁)
    (h₂ : ∀ y, P y → ExecRandWithin w c₂ y Q T₂ R₂) :
    ExecRandWithin w (.seq c₁ c₂) x Q (T₁ + T₂) (R₁ + R₂) := by
  obtain ⟨m₁, hm₁, hq₁, hsup₁⟩ := h₁
  have hstep : ∀ z₁ ∈ m₁.support,
      ExecRand w c₂ z₁.1 (codeComp w c₂ z₁.1) ∧
      (codeComp w c₂ z₁.1).IsQueryBounded R₂ ∧
      ∀ z₂ ∈ (codeComp w c₂ z₁.1).support, Q z₂.1 ∧ z₂.2 ≤ T₂ := by
    intro z₁ hz₁
    obtain ⟨m₂, hm₂, hq₂, hsup₂⟩ := h₂ z₁.1 (hsup₁ z₁ hz₁).1
    rw [hm₂.codeComp_eq]
    exact ⟨hm₂, hq₂, hsup₂⟩
  refine ⟨_, ExecRand.seq hm₁ fun z₁ hz₁ => (hstep z₁ hz₁).1, ?_, ?_⟩
  · refine OracleComp.IsCostBounded.bind_on_support hq₁ fun z₁ hz₁ => ?_
    simpa only [Nat.add_zero] using
      (hstep z₁ hz₁).2.1.bind fun _ => .pure _ 0
  · intro z hz
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z₂, hz₂, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hfinal
    have h₁' := hsup₁ z₁ hz₁
    have h₂' := (hstep z₁ hz₁).2.2 z₂ hz₂
    exact ⟨h₂'.1, Nat.add_le_add h₁'.2 h₂'.2⟩

/-- Positive branch rule (`+1` step, same call budget). -/
theorem branch_pos (hc : cond.Holds x) (h : ExecRandWithin w pos x P T R) :
    ExecRandWithin w (.branch cond pos neg) x P (T + 1) R := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  refine ⟨_, ExecRand.branch_pos hc hm, (OracleComp.isCostBounded_map_iff _ _ _).mpr hq, ?_⟩
  intro z hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  exact ⟨(hsup z₀ hz₀).1, Nat.add_le_add_right (hsup z₀ hz₀).2 1⟩

/-- Negative branch rule (`+2` steps, same call budget). -/
theorem branch_neg (hc : ¬cond.Holds x) (h : ExecRandWithin w neg x P T R) :
    ExecRandWithin w (.branch cond pos neg) x P (T + 2) R := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  refine ⟨_, ExecRand.branch_neg hc hm, (OracleComp.isCostBounded_map_iff _ _ _).mpr hq, ?_⟩
  intro z hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  exact ⟨(hsup z₀ hz₀).1, Nat.add_le_add_right (hsup z₀ hz₀).2 2⟩

/-- Combined branch rule with common budgets `(T + 2, R)`. -/
theorem branch (hpos : cond.Holds x → ExecRandWithin w pos x P T R)
    (hneg : ¬cond.Holds x → ExecRandWithin w neg x P T R) :
    ExecRandWithin w (.branch cond pos neg) x P (T + 2) R := by
  by_cases hc : cond.Holds x
  · exact (branch_pos hc (hpos hc)).mono (fun _ h => h) (by omega) le_rfl
  · exact branch_neg hc (hneg hc)

/-- Exiting a loop when the condition fails takes `2` steps and `0` `rand` calls. -/
theorem loop_exit (hc : ¬cond.Holds x) (hx : P x) :
    ExecRandWithin w (.loop cond body) x P 2 0 :=
  (ExecWithin.loop_exit hc).execRandWithin hx

/-- One iteration of a loop followed by the rest adds `T₁ + 2` steps and `R₁ + R₂` calls. -/
theorem loop_iter (hc : cond.Holds x)
    (hb : ExecRandWithin w body x P T₁ R₁)
    (hl : ∀ y, P y → ExecRandWithin w (.loop cond body) y Q T₂ R₂) :
    ExecRandWithin w (.loop cond body) x Q (T₁ + T₂ + 2) (R₁ + R₂) := by
  obtain ⟨mb, hmb, hqb, hsupb⟩ := hb
  have hstep : ∀ z₁ ∈ mb.support,
      ExecRand w (.loop cond body) z₁.1 (codeComp w (.loop cond body) z₁.1) ∧
      (codeComp w (.loop cond body) z₁.1).IsQueryBounded R₂ ∧
      ∀ z₂ ∈ (codeComp w (.loop cond body) z₁.1).support, Q z₂.1 ∧ z₂.2 ≤ T₂ := by
    intro z₁ hz₁
    obtain ⟨ml, hml, hql, hsupl⟩ := hl z₁.1 (hsupb z₁ hz₁).1
    rw [hml.codeComp_eq]
    exact ⟨hml, hql, hsupl⟩
  refine ⟨_, ExecRand.loop_iter hc hmb fun z₁ hz₁ => (hstep z₁ hz₁).1, ?_, ?_⟩
  · refine OracleComp.IsCostBounded.bind_on_support hqb fun z₁ hz₁ => ?_
    simpa only [Nat.add_zero] using
      (hstep z₁ hz₁).2.1.bind fun _ => .pure _ 0
  · intro z hz
    obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
    obtain ⟨z₂, hz₂, hfinal⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
    cases OracleComp.eq_of_mem_supportWith_pure hfinal
    have h₁' := hsupb z₁ hz₁
    have h₂' := (hstep z₁ hz₁).2.2 z₂ hz₂
    exact ⟨h₂'.1, by omega⟩

/-- **Potential rule for randomized loops.** Suppose every state `x` satisfying `I x` and
`cond.Holds x` runs `body` within some `T_b` instructions and `R_b` `rand` calls such that every
supported successor `y` satisfies `I y`, `T_b + 2 + Φ y ≤ Φ x`, and `R_b + Ψ y ≤ Ψ x`. Then from
any `x` satisfying `I x`, `.loop cond body` terminates within `Φ x + 2` instructions and `Ψ x`
`rand` calls, reaching a state `y` with `I y ∧ ¬cond.Holds y`. -/
theorem loop_potential (I : Data r → Prop) (Φ Ψ : Data r → ℕ)
    (hbody : ∀ x, I x → cond.Holds x → ∃ T_b R_b,
      ExecRandWithin w body x
        (fun y => I y ∧ T_b + 2 + Φ y ≤ Φ x ∧ R_b + Ψ y ≤ Ψ x) T_b R_b)
    (hx : I x) :
    ExecRandWithin w (.loop cond body) x (fun y => I y ∧ ¬cond.Holds y) (Φ x + 2) (Ψ x) := by
  induction hm : Φ x using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    subst hm
    by_cases hc : cond.Holds x
    · obtain ⟨T_b, R_b, hb⟩ := hbody x hx hc
      have hnonempty : ∃ y, I y ∧ T_b + 2 + Φ y ≤ Φ x ∧ R_b + Ψ y ≤ Ψ x := by
        obtain ⟨mb, -, -, hsupb⟩ := hb
        obtain ⟨z₀, hz₀⟩ := ProbComp.support_nonempty mb
        exact ⟨z₀.1, (hsupb z₀ hz₀).1⟩
      obtain ⟨y₀, -, hΦ₀, hΨ₀⟩ := hnonempty
      have hstep : ExecRandWithin w (.loop cond body) x (fun y => I y ∧ ¬cond.Holds y)
          (T_b + (Φ x - T_b - 2 + 2) + 2) (R_b + (Ψ x - R_b)) := by
        refine loop_iter hc hb ?_
        rintro y ⟨hIy, hΦy, hΨy⟩
        have hlt : Φ y < Φ x := by omega
        exact (ih (Φ y) hlt hIy rfl).mono (fun _ h => h) (by omega) (by omega)
      exact hstep.mono (fun _ h => h) (by omega) (by omega)
    · exact (loop_exit hc ⟨hx, hc⟩).mono (fun _ h => h) (by omega) (Nat.zero_le _)

/-- Renaming a `ExecRandWithin` specification along an injective register map `f`. -/
theorem rename {f : Fin r → Fin r'} (hf : f.Injective) {x : Data r'}
    (h : ExecRandWithin w c (x.comap f) P T R) :
    ExecRandWithin w (c.rename f) x (fun y' => ∃ y, P y ∧ y' = y.extend f x) T R := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  refine ⟨_, hm.rename hf, (OracleComp.isCostBounded_map_iff _ _ _).mpr hq, ?_⟩
  intro z hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  exact ⟨⟨z₀.1, (hsup z₀ hz₀).1, rfl⟩, (hsup z₀ hz₀).2⟩

end ExecRandWithin

/-! ## Compilation to flat `runRand`, `RandHaltsWithin`, and `RandCallsBounded` -/

section Compile

variable {w : ℕ} {p : Program B r}

private theorem runRand_step_jump {pc t k : ℕ} {x : Data r}
    (hp : p[pc]? = some (.jump t)) :
    runRand w p (k + 1) (.running ⟨pc, x⟩) = runRand w p k (.running ⟨t, x⟩) := by
  rw [runRand_succ, stepRand_jump (s := ⟨pc, x⟩) hp, pure_bind]

private theorem runRand_step_branch_pos {pc t k : ℕ} {c : Cond r} {x : Data r}
    (hp : p[pc]? = some (.branch c t)) (hc : c.Holds x) :
    runRand w p (k + 1) (.running ⟨pc, x⟩) = runRand w p k (.running ⟨t, x⟩) := by
  rw [runRand_succ, stepRand_branch (s := ⟨pc, x⟩) hp]
  simp only [hc, ↓reduceIte, pure_bind]

private theorem runRand_step_branch_neg {pc t k : ℕ} {c : Cond r} {x : Data r}
    (hp : p[pc]? = some (.branch c t)) (hc : ¬c.Holds x) :
    runRand w p (k + 1) (.running ⟨pc, x⟩) = runRand w p k (.running ⟨pc + 1, x⟩) := by
  rw [runRand_succ, stepRand_branch (s := ⟨pc, x⟩) hp]
  simp only [hc, ↓reduceIte, pure_bind]

/-- **Randomized assembly is exact.** Running a flat program `p` containing `c.assemble pc` at `pc`
for `T` steps (where every path of `m` uses at most `T` steps) is equal in `ProbComp` to sampling
`(y, n) ← m` and continuing from `⟨pc + c.size, y⟩` for the remaining `T - n` steps. -/
theorem ExecRand.runRand_assemble {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
    {pc T : ℕ} (h : ExecRand w c x m) (hp : p.Contains pc (c.assemble pc))
    (hT : ∀ z ∈ m.support, z.2 ≤ T) :
    runRand w p T (.running ⟨pc, x⟩) = (do
      let z ← m
      runRand w p (T - z.2) (.running ⟨pc + c.size, z.1⟩)) := by
  induction h generalizing pc T with
  | @op o x y ho =>
    have h1 : 1 ≤ T := hT (y, 1) rfl
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    rw [runRand_succ, stepRand_op (s := ⟨pc, x⟩) hp.head ho, pure_bind]
    simp only [Code.size, pure_bind, Nat.add_sub_cancel]
  | @rand dst src x hfit =>
    have h1 : 1 ≤ T := by
      refine hT (x.set dst 0, 1) ?_
      exact OracleComp.mem_supportWith_bind_iff.mpr ⟨0, ProbComp.mem_support_unifFin _ _, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    rw [runRand_succ, stepRand_rand_of_fits (s := ⟨pc, x⟩) hp.head hfit, bind_assoc, bind_assoc]
    refine congrArg (ProbComp.unifFin (x.regs src) >>= ·) (funext fun sample => ?_)
    simp only [Code.size, pure_bind, Nat.add_sub_cancel]
  | @seq c₁ c₂ x m₁ m₂ _ _ ih₁ ih₂ =>
    have hT₁ : ∀ z₁ ∈ m₁.support, z₁.2 ≤ T := by
      intro z₁ hz₁
      obtain ⟨z₂, hz₂⟩ := ProbComp.support_nonempty (m₂ z₁.1)
      have hmem : (z₂.1, z₁.2 + z₂.2) ∈
          (m₁ >>= fun z₁ => m₂ z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2)).support :=
        OracleComp.mem_supportWith_bind_iff.mpr
          ⟨z₁, hz₁, OracleComp.mem_supportWith_bind_iff.mpr ⟨z₂, hz₂, rfl⟩⟩
      have := hT _ hmem
      omega
    rw [ih₁ hp.append_left hT₁, bind_assoc]
    refine OracleComp.bind_congr_on_support fun z₁ hz₁ => ?_
    have hT₂ : ∀ z₂ ∈ (m₂ z₁.1).support, z₂.2 ≤ T - z₁.2 := by
      intro z₂ hz₂
      have hmem : (z₂.1, z₁.2 + z₂.2) ∈
          (m₁ >>= fun z₁ => m₂ z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2)).support :=
        OracleComp.mem_supportWith_bind_iff.mpr
          ⟨z₁, hz₁, OracleComp.mem_supportWith_bind_iff.mpr ⟨z₂, hz₂, rfl⟩⟩
      have := hT _ hmem
      omega
    have hc₂ : p.Contains (pc + c₁.size) (c₂.assemble (pc + c₁.size)) := by
      simpa using hp.append_right
    rw [ih₂ z₁ hz₁ hc₂ hT₂, bind_assoc]
    refine OracleComp.bind_congr_on_support fun z₂ _ => ?_
    simp only [pure_bind, Code.size, Nat.sub_sub, Nat.add_assoc]
  | @branch_pos cond pos neg x m hc _ ih =>
    obtain ⟨z₀, hz₀⟩ := ProbComp.support_nonempty m
    have h1 : 1 ≤ T := by
      have := hT (z₀.1, z₀.2 + 1) (OracleComp.mem_supportWith_map_iff.mpr ⟨z₀, hz₀, rfl⟩)
      omega
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    rw [runRand_step_branch_pos hp.head hc]
    have hc' := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
    rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc'
    have hTm : ∀ z ∈ m.support, z.2 ≤ k := by
      intro z hz
      have := hT (z.1, z.2 + 1) (OracleComp.mem_supportWith_map_iff.mpr ⟨z, hz, rfl⟩)
      omega
    rw [ih hc' hTm, ← bind_pure_comp, bind_assoc]
    refine OracleComp.bind_congr_on_support fun z _ => ?_
    simp only [pure_bind, Code.size, Nat.add_sub_add_right]
    rw [show pc + neg.size + 2 + pos.size = pc + (neg.size + pos.size + 2) by omega]
  | @branch_neg cond pos neg x m hc _ ih =>
    obtain ⟨z₀, hz₀⟩ := ProbComp.support_nonempty m
    have h2 : 2 ≤ T := by
      have := hT (z₀.1, z₀.2 + 2) (OracleComp.mem_supportWith_map_iff.mpr ⟨z₀, hz₀, rfl⟩)
      omega
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    rw [runRand_step_branch_neg hp.head hc]
    have hTm : ∀ z ∈ m.support, z.2 ≤ k := by
      intro z hz
      have := hT (z.1, z.2 + 2) (OracleComp.mem_supportWith_map_iff.mpr ⟨z, hz, rfl⟩)
      omega
    rw [ih hp.cons_tail.append_left hTm, ← bind_pure_comp, bind_assoc]
    refine OracleComp.bind_congr_on_support fun z hz => ?_
    have hk : 1 ≤ k - z.2 := by
      have := hT (z.1, z.2 + 2) (OracleComp.mem_supportWith_map_iff.mpr ⟨z, hz, rfl⟩)
      omega
    have hrem : k - z.2 = (k + 1 - (z.2 + 2)) + 1 := by omega
    have hj : p[pc + 1 + neg.size]? = some (.jump (pc + neg.size + pos.size + 2)) := by
      simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head
    simp only [pure_bind, Code.size]
    rw [hrem, runRand_step_jump hj]
    rw [show pc + neg.size + pos.size + 2 = pc + (neg.size + pos.size + 2) by omega]
  | @loop_exit cond body x hc =>
    have h2 : 2 ≤ T := hT (x, 2) rfl
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 2 := ⟨T - 2, by omega⟩
    rw [show k + 2 = (k + 1) + 1 by omega, runRand_step_branch_neg hp.head hc,
      runRand_step_jump hp.cons_tail.head]
    simp only [pure_bind, Code.size, show k + 1 + 1 - 2 = k by omega, Nat.add_assoc]
  | @loop_iter cond body x mb ml hc _ _ ihb ihl =>
    obtain ⟨z₁₀, hz₁₀⟩ := ProbComp.support_nonempty mb
    obtain ⟨z₂₀, hz₂₀⟩ := ProbComp.support_nonempty (ml z₁₀.1)
    have h2 : 2 ≤ T := by
      have hmem : (z₂₀.1, z₁₀.2 + z₂₀.2 + 2) ∈
          (mb >>= fun z₁ => ml z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2 + 2)).support :=
        OracleComp.mem_supportWith_bind_iff.mpr
          ⟨z₁₀, hz₁₀, OracleComp.mem_supportWith_bind_iff.mpr ⟨z₂₀, hz₂₀, rfl⟩⟩
      have := hT _ hmem
      omega
    obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
    rw [runRand_step_branch_pos hp.head hc]
    have hTb : ∀ z₁ ∈ mb.support, z₁.2 ≤ k := by
      intro z₁ hz₁
      obtain ⟨z₂, hz₂⟩ := ProbComp.support_nonempty (ml z₁.1)
      have hmem : (z₂.1, z₁.2 + z₂.2 + 2) ∈
          (mb >>= fun z₁ => ml z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2 + 2)).support :=
        OracleComp.mem_supportWith_bind_iff.mpr
          ⟨z₁, hz₁, OracleComp.mem_supportWith_bind_iff.mpr ⟨z₂, hz₂, rfl⟩⟩
      have := hT _ hmem
      omega
    have hbody_contains : p.Contains (pc + 2) (body.assemble (pc + 2)) := by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left
    rw [ihb hbody_contains hTb, bind_assoc]
    refine OracleComp.bind_congr_on_support fun z₁ hz₁ => ?_
    obtain ⟨z₂_any, hz₂_any⟩ := ProbComp.support_nonempty (ml z₁.1)
    have hk_rem : 1 ≤ k - z₁.2 := by
      have hmem : (z₂_any.1, z₁.2 + z₂_any.2 + 2) ∈
          (mb >>= fun z₁ => ml z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2 + 2)).support :=
        OracleComp.mem_supportWith_bind_iff.mpr
          ⟨z₁, hz₁, OracleComp.mem_supportWith_bind_iff.mpr ⟨z₂_any, hz₂_any, rfl⟩⟩
      have := hT _ hmem
      omega
    have hrem : k - z₁.2 = (k - z₁.2 - 1) + 1 := by omega
    have hj : p[pc + 2 + body.size]? = some (.jump pc) := by
      simpa using hp.cons_tail.cons_tail.append_right.head
    rw [hrem, runRand_step_jump hj]
    have hTl : ∀ z₂ ∈ (ml z₁.1).support, z₂.2 ≤ k - z₁.2 - 1 := by
      intro z₂ hz₂
      have hmem : (z₂.1, z₁.2 + z₂.2 + 2) ∈
          (mb >>= fun z₁ => ml z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2 + 2)).support :=
        OracleComp.mem_supportWith_bind_iff.mpr
          ⟨z₁, hz₁, OracleComp.mem_supportWith_bind_iff.mpr ⟨z₂, hz₂, rfl⟩⟩
      have := hT _ hmem
      omega
    rw [ihl z₁ hz₁ hp hTl, bind_assoc]
    refine OracleComp.bind_congr_on_support fun z₂ hz₂ => ?_
    have hmem : (z₂.1, z₁.2 + z₂.2 + 2) ∈
        (mb >>= fun z₁ => ml z₁.1 >>= fun z₂ => pure (z₂.1, z₁.2 + z₂.2 + 2)).support :=
      OracleComp.mem_supportWith_bind_iff.mpr
        ⟨z₁, hz₁, OracleComp.mem_supportWith_bind_iff.mpr ⟨z₂, hz₂, rfl⟩⟩
    have := hT _ hmem
    simp only [pure_bind, show k - z₁.2 - 1 - z₂.2 = k + 1 - (z₁.2 + z₂.2 + 2) by omega]

/-- Compiling `c` with `Code.program out` maps every `(y, n)` of `m` to `.halted (y.regs out) y`
once `T ≥ n + 1` on every path. -/
theorem ExecRand.runRand_program {c : Code B r} {x : Data r} {m : ProbComp (Data r × ℕ)}
    (h : ExecRand w c x m) (out : Fin r) {T : ℕ} (hT : ∀ z ∈ m.support, z.2 + 1 ≤ T) :
    runRand w (c.program out) T (.running ⟨0, x⟩) =
      (fun z => RandCfg.halted (z.1.regs out) z.1) <$> m := by
  have hT_le : ∀ z ∈ m.support, z.2 ≤ T := fun z hz => Nat.le_of_succ_le (hT z hz)
  rw [h.runRand_assemble (Program.Contains.self (c.program out)).append_left hT_le,
    ← bind_pure_comp]
  refine OracleComp.bind_congr_on_support fun z hz => ?_
  have h1 : 1 ≤ T - z.2 := by
    have := hT z hz
    omega
  obtain ⟨k, hk⟩ : ∃ k, T - z.2 = k + 1 := ⟨T - z.2 - 1, by omega⟩
  have hhalt : (c.program out)[0 + c.size]? = some (.halt out) := by
    simp [Code.program]
  rw [hk, runRand_succ, stepRand_halt (s := ⟨0 + c.size, z.1⟩) hhalt, pure_bind, runRand_halted]

/-- Structured deterministic corollary: a compiled `Exec w c x y n` halts cleanly under `runRand`
with output `y.regs out` and final machine data `y` at any fuel `T ≥ n + 1`. -/
theorem Exec.runRand_program {c : Code B r} {x y : Data r} {n T : ℕ}
    (h : Exec w c x y n) (out : Fin r) (hT : n + 1 ≤ T) :
    runRand w (c.program out) T (.running ⟨0, x⟩) = pure (.halted (y.regs out) y) := by
  rw [h.execRand.runRand_program out fun z hz => by
    cases OracleComp.eq_of_mem_supportWith_pure hz
    exact hT]
  rfl

/-- Compiling an `ExecRandWithin w c x P T R` certificate via `c.program out` yields
`RandHaltsWithin`, `RandCallsBounded`, and pathwise `P` on the halting data at any fuel
`T' ≥ T + 1`. -/
theorem ExecRandWithin.program {c : Code B r} {x : Data r} {P : Data r → Prop} {T T' R : ℕ}
    (h : ExecRandWithin w c x P T R) (out : Fin r) (hT : T + 1 ≤ T') :
    RandHaltsWithin w (c.program out) ⟨0, x⟩ T' ∧
    RandCallsBounded w (c.program out) ⟨0, x⟩ T' R ∧
    ∀ cfg ∈ (runRand w (c.program out) T' (.running ⟨0, x⟩)).support,
      ∃ y, cfg = .halted (y.regs out) y ∧ P y := by
  obtain ⟨m, hm, hq, hsup⟩ := h
  have hrun := hm.runRand_program out (T := T') fun z hz =>
    (Nat.add_le_add_right (hsup z hz).2 1).trans hT
  refine ⟨?_, ?_, ?_⟩
  · intro cfg hcfg
    rw [hrun] at hcfg
    obtain ⟨z, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    exact ⟨z.1.regs out, z.1, rfl⟩
  · rw [RandCallsBounded, hrun]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr hq
  · intro cfg hcfg
    rw [hrun] at hcfg
    obtain ⟨z, hz, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    exact ⟨z.1, rfl, (hsup z hz).1⟩

end Compile

end Cslib.WordRAM

end
