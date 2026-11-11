/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.ExecInvariant
public import CslibFrontier.Computability.WordRAM.TraceBounds

/-!
# Simultaneous memory support along actual executions

A transcript bounds newly occupied cells by writes, including writes to cells
never read. `Exec.All` transfers the resulting simultaneous support certificate
to every continuing prefix of the compiled program. Resetting support at lifetime
boundaries avoids summing all historical writes as global peak space.
-/

public section

namespace Cslib.WordRAM

variable {B : Basis} {r w n : ℕ} {c : Code B r} {x y : Data r} {ts : List Probe}

/-- A finite cover of the actual nonzero cells, with its cardinality bound. -/
@[expose] def Data.SupportLe (M : ℕ) (x : Data r) : Prop :=
  ∃ S : Finset ℕ, S.card ≤ M ∧ ∀ a, x.mem a ≠ 0 → a ∈ S

/-- A zero tail gives a finite initial support cover, including unread cells. -/
theorem Data.supportLe_of_zero_tail {r D : ℕ} (x : Data r)
    (hx : ∀ a, D ≤ a → x.mem a = 0) : x.SupportLe D := by
  refine ⟨Finset.range D, by simp, ?_⟩
  intro a ha
  exact Finset.mem_range.mpr (by by_contra h; exact ha (hx a (by omega)))

/-- An outside-memory frame holds at all intermediate states, not just at exit. -/
theorem TraceExec.all_frame (h : TraceExec w c x y n ts) (S : Finset ℕ) (mem : ℕ → ℕ)
    (hx : ∀ a, a ∉ S → x.mem a = mem a) (hs : Probe.writes ts ⊆ S) :
    h.exec.All (fun z => ∀ a, a ∉ S → z.mem a = mem a) := by
  induction h with
  | op he =>
    refine .op he hx ?_
    intro a ha
    exact ((Op.eval_modifies he) a (fun hw => ha (hs hw))).trans (hx a ha)
  | seq h₁ h₂ ih₁ ih₂ =>
    have hsub₁ : Probe.writes _ ⊆ S := fun a ha => hs (by
      rw [Probe.writes_append]; exact Finset.mem_union_left _ ha)
    have hsub₂ : Probe.writes _ ⊆ S := fun a ha => hs (by
      rw [Probe.writes_append]; exact Finset.mem_union_right _ ha)
    have first := ih₁ hx hsub₁
    exact .seq first (ih₂ first.finish hsub₂)
  | branch_pos hc _ ih => exact .branch_pos hc (ih hx hs)
  | branch_neg hc _ ih => exact .branch_neg hc (ih hx hs)
  | loop_exit hc => exact .loop_exit hc hx
  | loop_iter hc h₁ h₂ ih₁ ih₂ =>
    have hsub₁ : Probe.writes _ ⊆ S := fun a ha => hs (by
      rw [Probe.writes_append]; exact Finset.mem_union_left _ ha)
    have hsub₂ : Probe.writes _ ⊆ S := fun a ha => hs (by
      rw [Probe.writes_append]; exact Finset.mem_union_right _ ha)
    have first := ih₁ hx hsub₁
    exact .loop_iter hc first (ih₂ first.finish hsub₂)

/-- Distinct written addresses never outnumber actual store instructions. -/
theorem Probe.card_writes_le (ts : List Probe) : (Probe.writes ts).card ≤ Probe.writeCount ts := by
  induction ts with
  | nil => simp [Probe.writes, Probe.writeCount]
  | cons p ts ih =>
    cases p with
    | read => simpa only [Probe.writes, Probe.writeCount] using ih
    | write =>
      simp only [Probe.writes, Probe.writeCount]
      exact (Finset.card_union_le _ _).trans (by simp only [Finset.card_singleton]; omega)

/-- Actual writes bound occupied support at every state of the structured run. -/
theorem TraceExec.all_support (h : TraceExec w c x y n ts) (S : Finset ℕ)
    (hS : ∀ a, x.mem a ≠ 0 → a ∈ S) :
    h.exec.All (Data.SupportLe (S.card + Probe.writeCount ts)) := by
  let U := S ∪ Probe.writes ts
  have hf := h.all_frame U x.mem (fun _ _ => rfl) (Finset.subset_union_right)
  apply hf.mono
  intro z hz
  refine ⟨U, (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Probe.card_writes_le ts) _), ?_⟩
  intro a ha
  by_contra hn
  have hm := hz a hn
  exact hn (Finset.mem_union_left _ (hS a (by rwa [← hm])))

/-- Support bounds may be weakened without changing the actual memory. -/
theorem Data.SupportLe.mono {M N : ℕ} {x : Data r} (h : x.SupportLe M) (hm : M ≤ N) :
    x.SupportLe N :=
  let ⟨S, hs, hc⟩ := h
  ⟨S, hs.trans hm, hc⟩

/-- One actual run whose simultaneous occupied support is bounded at every state. -/
@[expose] def SpaceWithin (w : ℕ) (c : Code B r) (x y : Data r) (T M : ℕ) : Prop :=
  ∃ n, n ≤ T ∧ ∃ he : Exec w c x y n, he.All (Data.SupportLe M)

namespace SpaceWithin

variable {T T' M M' : ℕ} {a b : Code B r} {z : Data r}

/-- Forgetting the prefix annotation leaves an ordinary execution. -/
theorem execWithin (h : SpaceWithin w c x y T M) : ExecWithin w c x y T :=
  let ⟨n, hn, he, _⟩ := h
  ⟨n, hn, he⟩

/-- The annotated execution includes its final state. -/
theorem finish (h : SpaceWithin w c x y T M) : y.SupportLe M :=
  let ⟨_, _, _, hs⟩ := h
  hs.finish

/-- Both resource allowances may be weakened. -/
theorem mono (h : SpaceWithin w c x y T M) (hT : T ≤ T') (hM : M ≤ M') :
    SpaceWithin w c x y T' M' :=
  let ⟨n, hn, he, hs⟩ := h
  ⟨n, hn.trans hT, he, hs.mono (fun _ h => h.mono hM)⟩

/-- Sequential lifetimes reuse the same peak allowance. -/
theorem seq (ha : SpaceWithin w a x y T M) (hb : SpaceWithin w b y z T' M) :
    SpaceWithin w (.seq a b) x z (T + T') M :=
  let ⟨n, hn, he, hs⟩ := ha
  let ⟨n', hn', he', hs'⟩ := hb
  ⟨n + n', Nat.add_le_add hn hn', .seq he he', .seq hs hs'⟩

/-- The final native loop test preserves the existing support. -/
theorem loop_exit {cond : Cond r} {body : Code B r} (hc : ¬cond.Holds x)
    (hx : x.SupportLe M) : SpaceWithin w (.loop cond body) x x 2 M :=
  ⟨2, le_rfl, .loop_exit hc, .loop_exit hc hx⟩

/-- Loop control adds time and preserves the body's simultaneous support bound. -/
theorem loop_iter {cond : Cond r} {body : Code B r} (hc : cond.Holds x)
    (ha : SpaceWithin w body x y T M) (hb : SpaceWithin w (.loop cond body) y z T' M) :
    SpaceWithin w (.loop cond body) x z (T + T' + 2) M :=
  let ⟨n, hn, he, hs⟩ := ha
  let ⟨n', hn', he', hs'⟩ := hb
  ⟨n + n' + 2, by omega, .loop_iter hc he he', .loop_iter hc hs hs'⟩

end SpaceWithin

end Cslib.WordRAM
