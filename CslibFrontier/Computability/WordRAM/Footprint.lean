/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Trace

/-!
# Footprints and replay for flat word-RAM runs

These results concern the actual deterministic `step` over any basis, including width-reading
operations and faults. Each continuing instruction reads at most one cell and writes at most one
cell. Replay changes initial memory outside the cells read by a particular run; it preserves
the control path, registers and instruction count. No restriction on arithmetic is needed.

## Main results

* `Runs.exists_footprints`: finite read/write footprints bounded by the continuing step count.
* `Executes.exists_readFootprint`: changing unread initial memory preserves the returned word
  and the charged halting time.
-/

public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ}

/-- The cells read by a memory transcript. -/
@[expose] def Probe.reads : List Probe → Finset ℕ
  | [] => ∅
  | .read a _ :: ts => {a} ∪ reads ts
  | .write _ _ :: ts => reads ts

/-- A flat instruction's memory transcript, before testing whether the instruction succeeds. -/
@[expose] def probes (p : Program B r) (s : State r) : List Probe :=
  match p[s.pc]? with
  | some (.op o) => o.probes s.data
  | _ => []

/-- The registers agree and memory agrees outside the specified finite set. -/
@[expose] def Data.AgreeOutside (D : Finset ℕ) (x y : Data r) : Prop :=
  x.regs = y.regs ∧ Modifies D x.mem y.mem

/-- Replaying one successful data instruction needs equality only at its read address. -/
theorem Op.eval_replay {w : ℕ} {o : Op B r} {x x' y : Data r} {D : Finset ℕ}
    (h : o.eval w x = some x') (ha : x.AgreeOutside D y)
    (hd : Disjoint (Probe.reads (o.probes x)) D) :
    ∃ y', o.eval w y = some y' ∧ x'.AgreeOutside D y' := by
  obtain ⟨hr, hm⟩ := ha
  cases o with
  | const d v =>
    obtain ⟨hv, rfl⟩ := Data.put_eq_some.mp h
    exact ⟨y.set d v, Data.put_of_fits hv, by simpa [Data.AgreeOutside, Data.set, hr]⟩
  | copy d s =>
    cases h
    exact ⟨_, rfl, by simpa [Data.AgreeOutside, Data.set, hr]⟩
  | alu f d args =>
    obtain ⟨v, hv, hfit, rfl⟩ := Op.eval_alu_eq_some.mp h
    refine ⟨y.set d v, ?_, ?_⟩
    · apply Op.eval_alu_eq_some.mpr
      exact ⟨v, by simpa only [hr] using hv, hfit, rfl⟩
    · simpa [Data.AgreeOutside, Data.set, hr]
  | load d a =>
    cases h
    have hnot : x.regs a ∉ D := by
      apply Finset.disjoint_left.mp hd
      simp [Op.probes, Probe.reads]
    have he := hm (x.regs a) hnot
    have he' : x.mem (y.regs a) = y.mem (y.regs a) := by rw [← hr]; exact he.symm
    exact ⟨_, rfl, by simpa [Data.AgreeOutside, Data.set, hr, he']⟩
  | store a s =>
    cases h
    refine ⟨_, rfl, hr, ?_⟩
    intro b hb
    simp only [Data.write_mem, hr]
    by_cases he : b = y.regs a
    · simp [he]
    · simpa only [Function.update_of_ne he] using hm b hb

/-- A continuing flat step executes a successful data operation, a jump or a branch. -/
private theorem Next.cases_instr {w : ℕ} {p : Program B r} {s t : State r} (h : Next w p s t) :
    (∃ o x, p[s.pc]? = some (.op o) ∧ o.eval w s.data = some x ∧ t = ⟨s.pc + 1, x⟩) ∨
    (∃ k, p[s.pc]? = some (.jump k) ∧ t = ⟨k, s.data⟩) ∨
    ∃ c k, p[s.pc]? = some (.branch c k) ∧
      t = ⟨if c.Holds s.data then k else s.pc + 1, s.data⟩ := by
  unfold Next step at h
  cases hp : p[s.pc]? with
  | none => simp [hp] at h
  | some i =>
    cases i with
    | op o =>
      cases ho : o.eval w s.data with
      | none => simp [hp, ho] at h
      | some x => exact Or.inl ⟨o, x, rfl, ho, by simpa [hp, ho] using h.symm⟩
    | jump k => exact Or.inr (Or.inl ⟨k, rfl, by simpa [hp] using h.symm⟩)
    | branch c k => exact Or.inr (Or.inr ⟨c, k, rfl, by simpa [hp] using h.symm⟩)
    | halt i => simp [hp] at h
    | rand d s => simp [hp] at h

/-- Replaying a continuing flat step preserves its control and register file. -/
theorem Next.replay {w : ℕ} {p : Program B r} {s t s' : State r} {D : Finset ℕ}
    (h : Next w p s t) (hpc : s.pc = s'.pc) (ha : s.data.AgreeOutside D s'.data)
    (hd : Disjoint (Probe.reads (probes p s)) D) :
    ∃ t', Next w p s' t' ∧ t.pc = t'.pc ∧ t.data.AgreeOutside D t'.data := by
  rcases h.cases_instr with ⟨o, x, hp, ho, rfl⟩ | ⟨k, hp, rfl⟩ | ⟨c, k, hp, rfl⟩
  · obtain ⟨y, hy, ha'⟩ := o.eval_replay ho ha (by simpa [probes, hp] using hd)
    exact ⟨_, step_op (hpc ▸ hp) hy, by simp [hpc], ha'⟩
  · exact ⟨_, step_jump (hpc ▸ hp), rfl, ha⟩
  · have hc : c.Holds s.data ↔ c.Holds s'.data := by
      cases c <;> simp only [Cond.Holds, ha.1]
    exact ⟨_, step_branch (hpc ▸ hp), by simp only [hc, hpc], ha⟩

/-- A continuing step changes memory only at its actual store address. -/
theorem Next.modifies {w : ℕ} {p : Program B r} {s t : State r}
    (h : Next w p s t) : Modifies (Probe.writes (probes p s)) s.data.mem t.data.mem := by
  rcases h.cases_instr with ⟨o, x, hp, ho, rfl⟩ | ⟨k, hp, rfl⟩ | ⟨c, k, hp, rfl⟩
  · simpa only [probes, hp] using o.eval_modifies ho
  · exact Modifies.refl _ _
  · exact Modifies.refl _ _

private theorem card_probes_le (p : Program B r) (s : State r) :
    (Probe.reads (probes p s)).card ≤ 1 ∧ (Probe.writes (probes p s)).card ≤ 1 := by
  unfold probes
  split
  · rename_i o _
    cases o <;> simp [Op.probes, Probe.reads, Probe.writes]
  · simp [Probe.reads, Probe.writes]

/-- Actual runs have at most one read and one write per continuing instruction. Any initial
memory perturbation outside the read footprint replays with identical control and registers. -/
theorem Runs.exists_footprints {w n : ℕ} {p : Program B r} {s t : State r}
    (h : Runs w p s t n) :
    ∃ R W : Finset ℕ, R.card ≤ n ∧ W.card ≤ n ∧ Modifies W s.data.mem t.data.mem ∧
      ∀ (D : Finset ℕ) (s' : State r), Disjoint R D → s.pc = s'.pc →
        s.data.AgreeOutside D s'.data →
        ∃ t', Runs w p s' t' n ∧ t.pc = t'.pc ∧ t.data.AgreeOutside D t'.data := by
  induction h with
  | refl =>
    exact ⟨∅, ∅, by simp, by simp, Modifies.refl _ _,
      fun _ s' _ hpc ha => ⟨s', .refl _, hpc, ha⟩⟩
  | @tail u t n h hu ih =>
    obtain ⟨R, W, hR, hW, hm, hr⟩ := ih
    refine ⟨R ∪ Probe.reads (probes p u), W ∪ Probe.writes (probes p u),
      (Finset.card_union_le _ _).trans ?_, (Finset.card_union_le _ _).trans ?_,
      hm.trans hu.modifies, ?_⟩
    · exact Nat.add_le_add hR (card_probes_le p u).1
    · exact Nat.add_le_add hW (card_probes_le p u).2
    · intro D s' hd hpc ha
      obtain ⟨u', hu', hpc', ha'⟩ := hr D s' (Finset.disjoint_union_left.mp hd).1 hpc ha
      obtain ⟨t', ht', hpc'', ha''⟩ := hu.replay hpc' ha' (Finset.disjoint_union_left.mp hd).2
      exact ⟨t', hu'.tail _ _ _ _ ht', hpc'', ha''⟩

/-- Every successful halting execution depends on at most `n - 1` read cells. The final
halt costs one instruction and reads only a register. -/
theorem Executes.exists_readFootprint {w n v : ℕ} {p : Program B r} {s : State r}
    (h : Executes w p s v n) :
    ∃ R : Finset ℕ, R.card < n ∧ ∀ (D : Finset ℕ) (s' : State r), Disjoint R D →
      s.pc = s'.pc → s.data.AgreeOutside D s'.data → Executes w p s' v n := by
  obtain ⟨t, m, hr, hh, rfl⟩ := h
  obtain ⟨R, _, hR, _, _, hreplay⟩ := hr.exists_footprints
  refine ⟨R, by omega, ?_⟩
  intro D s' hd hpc ha
  obtain ⟨t', ht', hpc', ha'⟩ := hreplay D s' hd hpc ha
  refine ⟨t', m, ht', ?_, rfl⟩
  unfold step at hh ⊢
  rw [← hpc']
  cases hp : p[t.pc]? with
  | none => simp [hp] at hh
  | some i =>
    cases i with
    | halt i => simpa only [hp, ha'.1] using hh
    | op o => cases ho : o.eval w t.data <;> simp [hp, ho] at hh
    | jump k => simp [hp] at hh
    | branch c k => simp [hp] at hh
    | rand d s => simp [hp] at hh

end Cslib.WordRAM
