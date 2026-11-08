/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.RegisterParameters
public import Complexity.Computability.WordRAM.SupportTrace
import all Complexity.Computability.WordRAM.Structured

/-!
# Memory traces under native register parameterization

Register renaming and replacing selected immediate writes by copies preserve
the complete memory transcript, not just the result and instruction count.
-/

public section

namespace Cslib.WordRAM

/-- Register-bank embedding preserves the actual memory transcript. -/
theorem TraceExec.rename {B : Basis} {r r' W n : ℕ} {f : Fin r → Fin r'}
    (hf : Function.Injective f) {c : Code B r} {x : Data r'} {y : Data r} {ts : List Probe}
    (h : TraceExec W c (x.comap f) y n ts) :
    TraceExec W (c.rename f) x (y.extend f x) n ts := by
  generalize hx : x.comap f = x₀ at h
  induction h generalizing x with
  | @op o a b ho =>
    subst hx
    have he : (o.rename f).eval W x = some (b.extend f x) := by
      rw [Op.eval_rename hf, ho]; rfl
    have probes : (o.rename f).probes x = o.probes (x.comap f) := by cases o <;> rfl
    simpa only [Code.rename, probes] using TraceExec.op he
  | seq h₁ h₂ ih₁ ih₂ =>
    have ha := ih₁ hx
    have hb := ih₂ (Data.comap_extend hf _ x)
    rw [Data.extend_extend hf] at hb
    exact .seq ha hb
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
  | loop_iter hc h₁ h₂ ih₁ ih₂ =>
    subst hx
    have ha := ih₁ rfl
    have hb := ih₂ (Data.comap_extend hf _ x)
    rw [Data.extend_extend hf] at hb
    exact .loop_iter ((Cond.holds_rename _ _).2 hc) ha hb

/-- Substituting a preserved parameter register leaves every memory probe unchanged. -/
theorem Code.RegisterParameter.trace {B : Basis} {r W n : ℕ} {key : Fin r} {v : ℕ}
    {c c' : Code B r} (hp : Code.RegisterParameter key v c c') {x y : Data r} {ts : List Probe}
    (hk : x.regs key = v) (h : TraceExec W c x y n ts) : TraceExec W c' x y n ts := by
  induction hp generalizing x y n ts with
  | same _ _ => exact h
  | copy d _ =>
    cases h with
    | op he =>
      obtain ⟨_, hy⟩ := Data.put_eq_some.mp he
      exact .op (by simpa only [Op.eval_copy, hk] using congrArg some hy)
  | seq ha _ iha ihb =>
    cases h with
    | seq he₁ he₂ =>
      exact .seq (iha hk he₁) (ihb ((he₁.exec.regs_eq ha.preserves).trans hk) he₂)
  | branch _ _ _ iha ihb =>
    cases h with
    | branch_pos hc he => exact .branch_pos hc (iha hk he)
    | branch_neg hc he => exact .branch_neg hc (ihb hk he)

/-- A static absence of store instructions throughout a structured block. -/
@[expose] def Code.WriteFree {B : Basis} {r : ℕ} : Code B r → Prop
  | .op (.store _ _) => False
  | .op _ | .rand _ _ => True
  | .seq a b | .branch _ a b => a.WriteFree ∧ b.WriteFree
  | .loop _ a => a.WriteFree

instance instDecidableWriteFree {B : Basis} {r : ℕ} :
    (c : Code B r) → Decidable c.WriteFree
  | .op o => by cases o <;> first | exact isTrue trivial | exact isFalse id
  | .rand _ _ => isTrue trivial
  | .seq a b | .branch _ a b =>
      @instDecidableAnd _ _ (instDecidableWriteFree a) (instDecidableWriteFree b)
  | .loop _ a => instDecidableWriteFree a

/-- A write-free block has an empty write transcript along every actual run. -/
theorem TraceExec.writeCount_zero {B : Basis} {r W n : ℕ} {c : Code B r} {x y : Data r}
    {ts : List Probe} (h : TraceExec W c x y n ts) (hc : c.WriteFree) :
    Probe.writeCount ts = 0 := by
  induction h with
  | @op o a b he => cases o <;> first | rfl | exact hc.elim
  | seq _ _ iha ihb => rw [Probe.writeCount_append, iha hc.1, ihb hc.2]
  | branch_pos _ _ ih => exact ih hc.1
  | branch_neg _ _ ih => exact ih hc.2
  | loop_exit => rfl
  | loop_iter _ _ _ iha ihb => rw [Probe.writeCount_append, iha hc, ihb hc]

/-- Stores are bounded by the number of successful native instructions. -/
theorem TraceExec.writeCount_le {B : Basis} {r W n : ℕ} {c : Code B r} {x y : Data r}
    {ts : List Probe} (h : TraceExec W c x y n ts) : Probe.writeCount ts ≤ n := by
  have := Probe.readCount_add_writeCount ts
  have := h.length_le
  omega

/-- A successful native run with separate instruction and store budgets. -/
@[expose] def StoresWithin {B : Basis} {r : ℕ} (W : ℕ) (c : Code B r) (x y : Data r)
    (T S : ℕ) : Prop :=
  ∃ n ts, n ≤ T ∧ TraceExec W c x y n ts ∧ Probe.writeCount ts ≤ S

namespace StoresWithin

variable {B : Basis} {r W T T' S S' : ℕ} {c a b : Code B r} {x y z : Data r}

/-- Forgetting the store budget gives the ordinary native time certificate. -/
theorem execWithin (h : StoresWithin W c x y T S) : ExecWithin W c x y T :=
  let ⟨n, _, hn, ht, _⟩ := h
  ⟨n, hn, ht.exec⟩

/-- Weakening either budget leaves the execution unchanged. -/
theorem mono (h : StoresWithin W c x y T S) (hT : T ≤ T') (hS : S ≤ S') :
    StoresWithin W c x y T' S' :=
  let ⟨n, ts, hn, ht, hs⟩ := h
  ⟨n, ts, hn.trans hT, ht, hs.trans hS⟩

/-- Sequence adds actual instruction and store charges independently. -/
theorem seq (ha : StoresWithin W a x y T S) (hb : StoresWithin W b y z T' S') :
    StoresWithin W (.seq a b) x z (T + T') (S + S') := by
  obtain ⟨n, ts, hn, ht, hs⟩ := ha
  obtain ⟨n', ts', hn', ht', hs'⟩ := hb
  exact ⟨n + n', ts ++ ts', Nat.add_le_add hn hn', .seq ht ht',
    by rw [Probe.writeCount_append]; omega⟩

/-- Register embedding preserves both budgets. -/
theorem rename {r' : ℕ} {f : Fin r → Fin r'} (hf : Function.Injective f)
    {x : Data r'} (h : StoresWithin W c (x.comap f) y T S) :
    StoresWithin W (c.rename f) x (y.extend f x) T S :=
  let ⟨n, ts, hn, ht, hs⟩ := h
  ⟨n, ts, hn, ht.rename hf, hs⟩

/-- Parameter transfer preserves both budgets. -/
theorem parameter {key : Fin r} {v : ℕ} (hp : Code.RegisterParameter key v a b)
    (hk : x.regs key = v) (h : StoresWithin W a x y T S) :
    StoresWithin W b x y T S :=
  let ⟨n, ts, hn, ht, hs⟩ := h
  ⟨n, ts, hn, hp.trace hk ht, hs⟩

/-- Taking a positive branch has no memory charge for its control instruction. -/
theorem branch_pos {cond : Cond r} (hc : cond.Holds x)
    (h : StoresWithin W a x y T S) : StoresWithin W (.branch cond a b) x y (T + 1) S :=
  let ⟨n, ts, hn, ht, hs⟩ := h
  ⟨n + 1, ts, Nat.add_le_add_right hn 1, .branch_pos hc ht, hs⟩

/-- Taking a negative branch adds two instructions but no stores. -/
theorem branch_neg {cond : Cond r} (hc : ¬cond.Holds x)
    (h : StoresWithin W b x y T S) : StoresWithin W (.branch cond a b) x y (T + 2) S :=
  let ⟨n, ts, hn, ht, hs⟩ := h
  ⟨n + 2, ts, Nat.add_le_add_right hn 2, .branch_neg hc ht, hs⟩

/-- A lifetime's writes bound simultaneous support from its starting cover. -/
theorem space {D : ℕ} (h : StoresWithin W c x y T S) (hx : x.SupportLe D) :
    SpaceWithin W c x y T (D + S) := by
  obtain ⟨n, ts, hn, ht, hs⟩ := h
  obtain ⟨cover, hcard, hcover⟩ := hx
  exact ⟨n, hn, ht.exec, (ht.all_support cover hcover).mono
    (fun _ hz => hz.mono (Nat.add_le_add hcard hs))⟩

end StoresWithin

/-- A time certificate conservatively bounds stores by its instruction budget. -/
theorem ExecWithin.stores {B : Basis} {r W T : ℕ} {c : Code B r} {x y : Data r}
    (h : ExecWithin W c x y T) : StoresWithin W c x y T T := by
  obtain ⟨n, hn, he⟩ := h
  obtain ⟨ts, ht⟩ := he.exists_trace
  exact ⟨n, ts, hn, ht, ht.writeCount_le.trans hn⟩

/-- Streaming without stores charges no occupied cells regardless of duration. -/
theorem ExecWithin.withoutStores {B : Basis} {r W T : ℕ} {c : Code B r} {x y : Data r}
    (h : ExecWithin W c x y T) (hc : c.WriteFree) : StoresWithin W c x y T 0 := by
  obtain ⟨n, hn, he⟩ := h
  obtain ⟨ts, ht⟩ := he.exists_trace
  exact ⟨n, ts, hn, ht, (ht.writeCount_zero hc).le⟩

/-- Write-free native control preserves the existing support allowance. -/
theorem ExecWithin.space_writeFree {B : Basis} {r W T M : ℕ}
    {c : Code B r} {x y : Data r} (h : ExecWithin W c x y T)
    (hc : c.WriteFree) (hx : x.SupportLe M) : SpaceWithin W c x y T M := by
  simpa only [Nat.add_zero] using (h.withoutStores hc).space hx

end Cslib.WordRAM
