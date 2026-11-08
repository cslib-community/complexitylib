/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Compile
public import Complexity.Foundations.Relation.RelatesWithinSteps
import all Complexity.Computability.WordRAM.Compile

/-!
# State predicates along an existing structured execution

`Exec.All` annotates the existing execution derivation. It does not change the
program, machine or instruction costs. Compilation preserves the annotation at
every continuing prefix, including branch and loop control instructions.
-/

public section

namespace Cslib.WordRAM

variable {B : Basis} {r w : ℕ} {P Q : Data r → Prop}

/-- A state predicate holds throughout an actual execution derivation. -/
inductive Exec.All (P : Data r → Prop) :
    {c : Code B r} → {x y : Data r} → {n : ℕ} → Exec w c x y n → Prop where
  | op {o : Op B r} {x y : Data r} (h : o.eval w x = some y) :
      P x → P y → All P (.op h)
  | seq {a b : Code B r} {x y z : Data r} {m n : ℕ}
      {ha : Exec w a x y m} {hb : Exec w b y z n} :
      All P ha → All P hb → All P (.seq ha hb)
  | branch_pos {c : Cond r} {a b : Code B r} {x y : Data r} {n : ℕ}
      (hc : c.Holds x) {h : Exec w a x y n} : All P h → All P (.branch_pos (neg := b) hc h)
  | branch_neg {c : Cond r} {a b : Code B r} {x y : Data r} {n : ℕ}
      (hc : ¬c.Holds x) {h : Exec w b x y n} : All P h → All P (.branch_neg (pos := a) hc h)
  | loop_exit {c : Cond r} {a : Code B r} {x : Data r} (hc : ¬c.Holds x) :
      P x → All P (.loop_exit (body := a) hc)
  | loop_iter {c : Cond r} {a : Code B r} {x y z : Data r} {m n : ℕ}
      (hc : c.Holds x) {ha : Exec w a x y m} {hb : Exec w (.loop c a) y z n} :
      All P ha → All P hb → All P (.loop_iter hc ha hb)

/-- The initial state is included. -/
theorem Exec.All.start {c : Code B r} {x y : Data r} {n : ℕ} {h : Exec w c x y n}
    (hs : h.All P) : P x := by
  induction hs with
  | op _ hx _ | loop_exit _ hx => exact hx
  | seq _ _ ih _ | branch_pos _ _ ih | branch_neg _ _ ih | loop_iter _ _ _ ih _ => exact ih

/-- The final state is included. -/
theorem Exec.All.finish {c : Code B r} {x y : Data r} {n : ℕ} {h : Exec w c x y n}
    (hs : h.All P) : P y := by
  induction hs with
  | op _ _ hy | loop_exit _ hy => exact hy
  | seq _ _ _ ih | branch_pos _ _ ih | branch_neg _ _ ih | loop_iter _ _ _ _ ih => exact ih

/-- A pointwise weaker state predicate holds along the same run. -/
theorem Exec.All.mono {c : Code B r} {x y : Data r} {n : ℕ} {h : Exec w c x y n}
    (hs : h.All P) (hp : ∀ z, P z → Q z) : h.All Q := by
  induction hs with
  | op h hx hy => exact .op h (hp _ hx) (hp _ hy)
  | seq _ _ iha ihb => exact .seq iha ihb
  | branch_pos hc _ ih => exact .branch_pos hc ih
  | branch_neg hc _ ih => exact .branch_neg hc ih
  | loop_exit hc hx => exact .loop_exit hc (hp _ hx)
  | loop_iter hc _ _ iha ihb => exact .loop_iter hc iha ihb

/-- Compiled executions preserve the state annotation, including control steps. -/
theorem Exec.All.runs {c : Code B r} {x y : Data r} {n : ℕ} {h : Exec w c x y n}
    (hs : h.All P) {p : Program B r} {pc : ℕ} (hp : p.Contains pc (c.assemble pc)) :
    Relation.RelatesInSteps (fun a b : State r => Next w p a b ∧ P b.data)
      ⟨pc, x⟩ ⟨pc + c.size, y⟩ n := by
  induction hs generalizing pc with
  | op ho _ hy => exact .single ⟨step_op hp.head ho, hy⟩
  | @seq a b x y z m n ha hb hsa hsb iha ihb =>
    have h₁ := iha hp.append_left
    have h₂ := ihb (pc := pc + a.size) (by simpa using hp.append_right)
    simpa [Code.size, Nat.add_assoc] using h₁.trans h₂
  | @branch_pos cond pos neg x y n hc h hs ih =>
    have hb := next_branch_pos (w := w) hp.head hc
    have hcp := (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).cons_tail
    rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hcp
    have hpos := ih hcp
    have hr := Relation.RelatesInSteps.head _ _ _ _ ⟨hb, hs.start⟩ hpos
    simpa [Code.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr
  | @branch_neg cond pos neg x y n hc h hs ih =>
    have hb := next_branch_neg (w := w) hp.head hc
    have hneg := ih (pc := pc + 1) hp.cons_tail.append_left
    have hj : Next w p ⟨pc + 1 + neg.size, y⟩ ⟨pc + neg.size + pos.size + 2, y⟩ :=
      next_jump (by simpa using (hp.cons_tail.append_right (q₁ := neg.assemble (pc + 1))).head)
    have hr := (Relation.RelatesInSteps.head _ _ _ _ ⟨hb, hs.start⟩ hneg).tail _ _ _ _
      ⟨hj, hs.finish⟩
    simpa [Code.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr
  | @loop_exit cond body x hc hx =>
    have hb := next_branch_neg (w := w) hp.head hc
    have hj : Next w p ⟨pc + 1, x⟩ ⟨pc + body.size + 3, x⟩ := next_jump hp.cons_tail.head
    simpa [Code.size, Nat.add_assoc] using
      (Relation.RelatesInSteps.single ⟨hb, hx⟩).tail _ _ _ _ ⟨hj, hx⟩
  | @loop_iter cond body x y z m n hc ha hb hsa hsb iha ihb =>
    have htest := next_branch_pos (w := w) hp.head hc
    have hbody := iha (pc := pc + 2) (by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left)
    have hj : Next w p ⟨pc + 2 + body.size, y⟩ ⟨pc, y⟩ :=
      next_jump (by simpa using hp.cons_tail.cons_tail.append_right.head)
    have hrest := ihb hp
    have hr := ((Relation.RelatesInSteps.head _ _ _ _ ⟨htest, hsa.start⟩ hbody).tail
      _ _ _ _ ⟨hj, hsa.finish⟩).trans hrest
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

/-- Continuing runs from the same state have a unique state at each exact time. -/
theorem Runs.deterministic {p : Program B r} {x y z : State r} {n : ℕ}
    (h : Runs w p x y n) (h' : Runs w p x z n) : y = z := by
  induction h generalizing z with
  | refl => cases h'; rfl
  | @tail y t n h ht ih =>
    obtain ⟨z', hz, hzstep⟩ := h'.succ
    have he := ih hz
    subst z'
    exact Outcome.next.inj (ht.symm.trans hzstep)

/-- Every continuing prefix of the compiled program satisfies the annotation.
This is about simultaneous states, not the union of historical accesses. -/
theorem Exec.All.prefix {c : Code B r} {x y : Data r} {n : ℕ} {h : Exec w c x y n}
    (hs : h.All P) (out : Fin r) {k : ℕ} {u : State r}
    (hu : Runs w (c.program out) ⟨0, x⟩ u k) (hk : k ≤ n) : P u.data := by
  have hr := hs.runs (Program.Contains.self (c.program out)).append_left
  have hn : n = k + (n - k) := by omega
  rw [hn] at hr
  obtain ⟨v, hv, _⟩ := Relation.RelatesInSteps.add_iff.mp hr
  have hv' : Runs w (c.program out) ⟨0, x⟩ v k := hv.map id (fun _ _ h => h.1)
  have he : u = v := hu.deterministic hv'
  rw [he]
  induction hv with
  | refl => exact hs.start
  | @tail _ _ _ _ ht _ => exact ht.2

end Cslib.WordRAM
