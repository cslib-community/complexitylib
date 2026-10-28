/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Structured

/-!
# Width-independent native program prefixes

An execution that halts at one width identifies every successful prefix at a larger width when
the program does not read physical width. These rules apply to both complete native frontends
and programs that compose them.

## Main results

* `Code.readsWidth_rename`: register renaming does not change width observation.
* `Runs.prefix_at_smaller_width`: wider prefixes agree with an admitted smaller-width execution.

These determinism and representation lemmas are original.
-/

@[expose] public section

namespace Cslib.WordRAM

/-- Register renaming never changes whether a structured program observes physical width. -/
theorem Code.readsWidth_rename {B : Basis} {r r' : ℕ} (f : Fin r → Fin r')
    (c : Code B r) : (c.rename f).ReadsWidth ↔ c.ReadsWidth := by
  induction c with
  | op o => cases o <;> rfl
  | seq c d hc hd => simp only [Code.rename, Code.ReadsWidth, hc, hd]
  | branch b c d hc hd => simp only [Code.rename, Code.ReadsWidth, hc, hd]
  | loop b c hc => exact hc
  | rand => rfl

/-- Every wider prefix is the same smaller-width prefix if that smaller execution halts. -/
theorem Runs.prefix_at_smaller_width {B : Basis} {w w' r : ℕ} {p : Program B r}
    (hp : ¬p.ReadsWidth) (hw : w ≤ w') {s t : State r} {k v total : ℕ}
    (hwide : Runs w' p s t k) (hlow : Executes w p s v total) : Runs w p s t k := by
  induction hwide using Relation.RelatesInSteps.head_induction_on generalizing total with
  | hrefl => exact .refl _
  | @hhead a c k hstep hrest ih =>
    obtain ⟨z, m, hm, hz, _⟩ := hlow
    cases m with
    | zero =>
      have he := hm.zero
      subst z
      have hh : step w' p a = .halt v := step_halt_mono_width hz
      rw [show step w' p a = .next c from hstep] at hh
      cases hh
    | succ m =>
      obtain ⟨u, hu, htail⟩ := hm.succ'
      have he : u = c := by
        have hmono := hu.mono_width hp hw
        change step w' p a = .next u at hmono
        rw [show step w' p a = .next c from hstep] at hmono
        exact Outcome.next.inj hmono.symm
      subst u
      exact (ih (total := m + 1) ⟨z, m, htail, hz, rfl⟩).head a c t k hu

/-- A native instruction cannot write memory above the admitted address-word universe. -/
theorem Op.eval_mem_above {B : Basis} {r w a : ℕ} {o : Op B r} {x y : Data r}
    (h : o.eval w x = some y) (hx : x.Bounded w) (ha : 2 ^ w ≤ a) :
    y.mem a = x.mem a := by
  cases o with
  | const => obtain ⟨_, rfl⟩ := Data.put_eq_some.1 h; rfl
  | alu => obtain ⟨_, _, _, rfl⟩ := Op.eval_alu_eq_some.1 h; rfl
  | copy => cases h; rfl
  | load => cases h; rfl
  | store d s =>
    cases h
    change Function.update x.mem (x.regs d) (x.regs s) a = x.mem a
    exact Function.update_of_ne (by have := hx.1 d; dsimp only [Fits] at this; omega) _ _

/-- A complete native step preserves memory beyond the admitted address-word universe. -/
theorem Next.mem_above {B : Basis} {r w a : ℕ} {p : Program B r} {s t : State r}
    (h : Next w p s t) (hs : s.data.Bounded w) (ha : 2 ^ w ≤ a) :
    t.data.mem a = s.data.mem a := by
  unfold Next WordRAM.step at h
  split at h
  · cases h
  · next o _ =>
    split at h
    · next x hx => cases h; exact Op.eval_mem_above hx hs ha
    · cases h
  all_goals first | (cases h; rfl) | cases h

/-- A native run preserves every cell above its admitted address-word universe. -/
theorem Runs.mem_above {B : Basis} {r w a : ℕ} {p : Program B r} {s t : State r} {n : ℕ}
    (h : Runs w p s t n) (hs : s.data.Bounded w) (ha : 2 ^ w ≤ a) :
    t.data.mem a = s.data.mem a := by
  induction h with
  | refl => rfl
  | @tail t u n hpre hstep ih =>
    exact (hstep.mem_above (Runs.bounded hpre hs) ha).trans ih

end Cslib.WordRAM
