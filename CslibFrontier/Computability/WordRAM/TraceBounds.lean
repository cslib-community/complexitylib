/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Footprint

/-!
# Address capacity of bounded native executions

Starting from word-bounded data, every address and value in an actual execution's
memory transcript fits the physical word width. Consequently the union of all
accessed cells, and therefore every prefix's accessed cells, has cardinality at
most `2^w`. This is a capacity bound, not a claim that a program uses every cell
or that its input encoding fits any particular width.
-/

public section

namespace Cslib.WordRAM

/-- Both addresses and values of every successful native probe fit the word width. -/
theorem TraceExec.probe_bounded {B : Basis} {r w n : ℕ} {c : Code B r}
    {x y : Data r} {ts : List Probe} (h : TraceExec w c x y n ts) (hx : x.Bounded w) :
    ∀ a v, Probe.read a v ∈ ts ∨ Probe.write a v ∈ ts → Fits w a ∧ Fits w v := by
  induction h with
  | @op o x y ho =>
    intro a v hp
    cases o <;> simp only [Op.probes, List.mem_singleton, List.not_mem_nil,
      or_self] at hp
    · rcases hp with he | he <;> cases he
      exact ⟨hx.1 _, hx.2 _⟩
    · rcases hp with he | he <;> cases he
      exact ⟨hx.1 _, hx.1 _⟩
  | seq h₁ h₂ ih₁ ih₂ =>
    intro a v hp
    simp only [List.mem_append] at hp
    rcases hp with (hp | hp) | (hp | hp)
    · exact ih₁ hx a v (Or.inl hp)
    · exact ih₂ (h₁.exec.bounded hx) a v (Or.inl hp)
    · exact ih₁ hx a v (Or.inr hp)
    · exact ih₂ (h₁.exec.bounded hx) a v (Or.inr hp)
  | branch_pos _ _ ih | branch_neg _ _ ih => exact ih hx
  | loop_exit => simp
  | loop_iter _ h₁ h₂ ih₁ ih₂ =>
    intro a v hp
    simp only [List.mem_append] at hp
    rcases hp with (hp | hp) | (hp | hp)
    · exact ih₁ hx a v (Or.inl hp)
    · exact ih₂ (h₁.exec.bounded hx) a v (Or.inl hp)
    · exact ih₁ hx a v (Or.inr hp)
    · exact ih₂ (h₁.exec.bounded hx) a v (Or.inr hp)

private theorem probe_footprint_subset {w : ℕ} (ts : List Probe)
    (h : ∀ a v, Probe.read a v ∈ ts ∨ Probe.write a v ∈ ts → Fits w a) :
    Probe.reads ts ∪ Probe.writes ts ⊆ Finset.range (2 ^ w) := by
  induction ts with
  | nil => simp [Probe.reads, Probe.writes]
  | cons p ts ih =>
    have ht : Probe.reads ts ∪ Probe.writes ts ⊆ Finset.range (2 ^ w) :=
      ih (fun a v hp => h a v (hp.elim (fun hp => Or.inl (List.mem_cons_of_mem _ hp))
        (fun hp => Or.inr (List.mem_cons_of_mem _ hp))))
    cases p with
    | read a v =>
      have ha : a ∈ Finset.range (2 ^ w) := Finset.mem_range.mpr (h a v (Or.inl List.mem_cons_self))
      simpa only [Probe.reads, Probe.writes, Finset.union_assoc] using
        Finset.union_subset (Finset.singleton_subset_iff.mpr ha) ht
    | write a v =>
      have ha : a ∈ Finset.range (2 ^ w) := Finset.mem_range.mpr (h a v (Or.inr List.mem_cons_self))
      simpa only [Probe.reads, Probe.writes, Finset.union_assoc, Finset.union_left_comm] using
        Finset.union_subset (Finset.singleton_subset_iff.mpr ha) ht

/-- A transcript accesses at most one new cell per recorded probe. -/
theorem Probe.footprint_le_length (ts : List Probe) :
    (Probe.reads ts ∪ Probe.writes ts).card ≤ ts.length := by
  induction ts with
  | nil => simp [Probe.reads, Probe.writes]
  | cons p ts ih =>
    cases p with
    | read a v =>
      simpa only [Probe.reads, Probe.writes, Finset.union_assoc, List.length_cons] using
        (Finset.card_union_le ({a} : Finset ℕ) (Probe.reads ts ∪ Probe.writes ts)).trans
          (by simp only [Finset.card_singleton]; omega)
    | write a v =>
      simpa only [Probe.reads, Probe.writes, Finset.union_assoc, Finset.union_left_comm,
        List.length_cons] using
        (Finset.card_union_le ({a} : Finset ℕ) (Probe.reads ts ∪ Probe.writes ts)).trans
          (by simp only [Finset.card_singleton]; omega)

/-- Actual structured execution bounds its complete accessed footprint by time,
even when counter values require many more bits than memory addresses. -/
theorem TraceExec.footprint_le {B : Basis} {r w n : ℕ} {c : Code B r}
    {x y : Data r} {ts : List Probe} (h : TraceExec w c x y n ts) :
    (Probe.reads ts ∪ Probe.writes ts).card ≤ n :=
  (Probe.footprint_le_length ts).trans h.length_le

/-- All accessed cells fit in the machine's finite address capacity. This bounds
peak distinct cells even when cells are repeatedly overwritten. -/
theorem TraceExec.address_footprint_le {B : Basis} {r w n : ℕ} {c : Code B r}
    {x y : Data r} {ts : List Probe} (h : TraceExec w c x y n ts) (hx : x.Bounded w) :
    (Probe.reads ts ∪ Probe.writes ts).card ≤ 2 ^ w := by
  have hs := probe_footprint_subset ts (fun a v hp => (h.probe_bounded hx a v hp).1)
  exact (Finset.card_le_card hs).trans_eq (Finset.card_range _)

/-- A run can create at most one newly nonzero memory cell per instruction.
The initial support is included, even for input cells the program never reads.
Applying this to each run prefix bounds simultaneous occupied memory, rather
than merely the largest address representable by a word. -/
theorem Runs.exists_memorySupport {B : Basis} {r w n : ℕ} {p : Program B r}
    {s t : State r} (h : Runs w p s t n) (S : Finset ℕ)
    (hS : ∀ a, s.data.mem a ≠ 0 → a ∈ S) :
    ∃ T : Finset ℕ, T.card ≤ S.card + n ∧ ∀ a, t.data.mem a ≠ 0 → a ∈ T := by
  obtain ⟨_, W, _, hW, hm, _⟩ := h.exists_footprints
  refine ⟨S ∪ W, (Finset.card_union_le _ _).trans (Nat.add_le_add_left hW _), ?_⟩
  intro a ha
  by_cases hw : a ∈ W
  · exact Finset.mem_union_right _ hw
  · exact Finset.mem_union_left _ (hS a (by simpa only [hm a hw] using ha))

end Cslib.WordRAM
