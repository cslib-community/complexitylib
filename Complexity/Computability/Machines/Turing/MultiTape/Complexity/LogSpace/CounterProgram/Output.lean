/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram

/-!
# Counter programs with output

A counter program (`Turing.CounterProgram`) emits bits with its `emit` instructions. This file
records what a run emits: `P.ReachesOut w Q s s' out` says that the program reaches `s'` from `s`
on the input `w`, passing only through configurations satisfying `Q`, and emits `out` on the way.
Reachability without emissions (`Turing.CounterProgram.Reaches`) through assignments, comparisons
and reads emits nothing (`Turing.CounterProgram.Reaches.reachesOut`). A counting loop
(`Turing.CounterProgram.forCode`) emits, in order, what its body emits for each value of the
counter (`Turing.CounterProgram.reachesOut_forCode`). A program that reaches a halt, emitting the
encoding of the value of a function, computes the function in logarithmic space if its registers
stay polynomially bounded (`Turing.CounterProgram.computableInLogSpace_of_reachesOut`): this is the
form of a logarithmic-space transducer.

## Main definitions

* `Turing.CounterProgram.Active`: the configurations at instructions other than halts, with
  bounded registers.
* `Turing.CounterProgram.ReachesOut`: reachability, with the bits emitted on the way.
* `Turing.CounterProgram.forCode`: the code of a counting loop.
* `Turing.CounterProgram.blocksCode`: a fixed list of blocks at successive labels.

## Main results

* `Turing.CounterProgram.reachesOut_blocksCode`: sequence block outputs and preserve an invariant.
* `Turing.CounterProgram.reachesOut_forCode`: a counting loop emits what its body emits for each
  value of the counter.
* `Turing.CounterProgram.computableInLogSpace_of_reachesOut`: counter programs with output and
  polynomially bounded registers compute functions in logarithmic space.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.5][Sipser2013]
-/

@[expose] public section

namespace Turing

namespace CounterProgram

open Instr Expr

variable {P : CounterProgram} {w : List Bool}

variable (P) in
/-- The configurations at instructions other than halts, with all registers at most `B`. -/
def Active (B : ℕ) (s : Config) : Prop := (P.instr s.1).halts = false ∧ ∀ r ∈ s.2, r ≤ B

variable (P w) in
/-- `P.ReachesOut w Q s s' out`: from `s`, the program reaches `s'` on the input `w`, every
configuration before `s'` satisfies `Q`, and the bits emitted before `s'` are `out`. -/
def ReachesOut (Q : Config → Prop) (s s' : Config) (out : List Bool) : Prop :=
  ∃ t, (P.step w)^[t] s = s' ∧ (∀ t' < t, Q ((P.step w)^[t'] s)) ∧
    out = ((List.range t).map fun i => P.emitted ((P.step w)^[i] s)).flatten

variable {Q : Config → Prop} {s s' s'' : Config} {out out' : List Bool}

namespace ReachesOut

theorem refl (s : Config) : P.ReachesOut w Q s s [] :=
  ⟨0, rfl, fun _ h => absurd h (by omega), rfl⟩

theorem trans (h : P.ReachesOut w Q s s' out) (h' : P.ReachesOut w Q s' s'' out') :
    P.ReachesOut w Q s s'' (out ++ out') := by
  obtain ⟨t, rfl, ht, rfl⟩ := h
  obtain ⟨t', rfl, ht', rfl⟩ := h'
  refine ⟨t' + t, by rw [Function.iterate_add_apply], fun u hu => ?_, ?_⟩
  · rcases lt_or_ge u t with hlt | hge
    · exact ht u hlt
    · have := ht' (u - t) (by omega)
      rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hge] at this
  · rw [Nat.add_comm t' t, List.range_add, List.map_append, List.flatten_append, List.map_map]
    congr 2
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    rw [Nat.add_comm t i, Function.iterate_add_apply]

theorem head (hs : Q s) (h : P.ReachesOut w Q (P.step w s) s' out) :
    P.ReachesOut w Q s s' (P.emitted s ++ out) :=
  (show P.ReachesOut w Q s (P.step w s) (P.emitted s) from
    ⟨1, rfl, fun t ht => by rw [show t = 0 by omega]; exact hs, by simp⟩).trans h

theorem mono {Q' : Config → Prop} (h : P.ReachesOut w Q s s' out) (hQ : ∀ s, Q s → Q' s) :
    P.ReachesOut w Q' s s' out :=
  let ⟨t, ht, hQt, hout⟩ := h
  ⟨t, ht, fun u hu => hQ _ (hQt u hu), hout⟩

theorem of_eq (h : P.ReachesOut w Q s s' out) (h' : out = out') : P.ReachesOut w Q s s' out' :=
  h' ▸ h

end ReachesOut

/-- Concatenate fixed blocks, placing each after the declared lengths of its predecessors. -/
def blocksCode {α : Type*} (code : α → ℕ → List Instr) (len : α → ℕ) :
    ℕ → List α → List Instr
  | _, [] => []
  | b, x :: xs => code x b ++ blocksCode code len (b + len x) xs

/-- The length of a sequence of blocks is the sum of their declared lengths. -/
theorem length_blocksCode {α : Type*} (code : α → ℕ → List Instr) (len : α → ℕ)
    (hlen : ∀ x b, (code x b).length = len x) :
    ∀ b xs, (blocksCode code len b xs).length = (xs.map len).sum
  | _, [] => rfl
  | b, x :: xs => by
    rw [blocksCode, List.length_append, hlen, length_blocksCode code len hlen,
      List.map_cons, List.sum_cons]

/-- A fixed list of blocks emits their words in order and preserves a register invariant.
Each block's actual length must agree with its declared length at every starting label.
Sequencing inserts no transitions between the supplied block runs. The empty list has a
zero-step run; a zero-length block still requires its own reachability proof. -/
theorem reachesOut_blocksCode {α : Type*} (code : α → ℕ → List Instr) (len : α → ℕ)
    (hlen : ∀ x b, (code x b).length = len x) (out : α → List Bool)
    (Inv : List ℕ → Prop) {xs : List α}
    (hblock : ∀ x ∈ xs, ∀ b regs, P.CodeAt b (code x b) → Inv regs →
      ∃ regs', P.ReachesOut w Q (b, regs) (b + len x, regs') (out x) ∧ Inv regs')
    (b : ℕ) (regs : List ℕ) (hcode : P.CodeAt b (blocksCode code len b xs))
    (hInv : Inv regs) :
    ∃ regs', P.ReachesOut w Q (b, regs) (b + (xs.map len).sum, regs')
      (xs.flatMap out) ∧ Inv regs' := by
  induction xs generalizing b regs with
  | nil => exact ⟨regs, by simpa using ReachesOut.refl _, hInv⟩
  | cons x xs ih =>
    rw [blocksCode, codeAt_append, hlen] at hcode
    obtain ⟨regs₁, hr₁, hI₁⟩ := hblock x List.mem_cons_self b regs hcode.1 hInv
    obtain ⟨regs₂, hr₂, hI₂⟩ := ih
      (fun y hy => hblock y (List.mem_cons_of_mem _ hy)) _ regs₁ hcode.2 hI₁
    refine ⟨regs₂, ?_, hI₂⟩
    rw [List.map_cons, List.sum_cons, ← Nat.add_assoc, List.flatMap_cons]
    exact hr₁.trans hr₂

/-- Reachability through assignments, comparisons and reads emits nothing. -/
theorem Reaches.reachesOut {B : ℕ} (h : P.Reaches w (P.Running B) s s') :
    P.ReachesOut w (P.Active B) s s' [] := by
  obtain ⟨t, rfl, ht⟩ := h
  refine ⟨t, rfl, fun u hu => ⟨?_, (ht u hu).2⟩, ?_⟩
  · have := (ht u hu).1
    revert this
    cases P.instr ((P.step w)^[u] s).1 <;> simp [IsStep, Instr.halts]
  · symm
    simp only [List.flatten_eq_nil_iff, List.mem_map, List.mem_range]
    rintro _ ⟨i, hi, rfl⟩
    have := (ht i hi).1
    simp only [emitted]
    revert this
    cases P.instr ((P.step w)^[i] s).1 <;> simp [IsStep, Instr.emitted]

variable {B : ℕ} {regs : List ℕ}

theorem ReachesOut.assign {c i : ℕ} {e : Expr} {next : ℕ} (hc : P.instr c = .assign i e next)
    (hB : ∀ r ∈ regs, r ≤ B)
    (h : P.ReachesOut w (P.Active B) (next, regs.set i (e.eval regs)) s' out) :
    P.ReachesOut w (P.Active B) (c, regs) s' out := by
  have := ReachesOut.head (Q := P.Active B) (s := (c, regs)) ⟨by rw [hc]; rfl, hB⟩
    (by rwa [P.step_assign w hc])
  simpa [emitted, hc, Instr.emitted] using this

theorem ReachesOut.lt {c : ℕ} {x y : Expr} {yes no : ℕ} (hc : P.instr c = .lt x y yes no)
    (hB : ∀ r ∈ regs, r ≤ B)
    (h : P.ReachesOut w (P.Active B) (if x.eval regs < y.eval regs then yes else no, regs) s'
      out) :
    P.ReachesOut w (P.Active B) (c, regs) s' out := by
  have := ReachesOut.head (Q := P.Active B) (s := (c, regs)) ⟨by rw [hc]; rfl, hB⟩
    (by rwa [P.step_lt w hc])
  simpa [emitted, hc, Instr.emitted] using this

theorem ReachesOut.read {c : ℕ} {e : Expr} {onTrue onFalse onEnd : ℕ}
    (hc : P.instr c = .read e onTrue onFalse onEnd) (hB : ∀ r ∈ regs, r ≤ B)
    (h : P.ReachesOut w (P.Active B) (readLabel onTrue onFalse onEnd w[e.eval regs]?, regs) s'
      out) :
    P.ReachesOut w (P.Active B) (c, regs) s' out := by
  have := ReachesOut.head (Q := P.Active B) (s := (c, regs)) ⟨by rw [hc]; rfl, hB⟩
    (by rwa [P.step_read w hc])
  simpa [emitted, hc, Instr.emitted] using this

theorem step_emit {s : Config} {b : Bool} {next : ℕ} (h : P.instr s.1 = .emit b next) :
    P.step w s = (next, s.2) := by
  have : P.halted s = false := by simp [halted, h, Instr.halts]
  simp [step, QueryMachine.step, toQueryMachine, this, exec, h, Instr.exec]

theorem ReachesOut.emit {c : ℕ} {b : Bool} {next : ℕ} (hc : P.instr c = .emit b next)
    (hB : ∀ r ∈ regs, r ≤ B) (h : P.ReachesOut w (P.Active B) (next, regs) s' out) :
    P.ReachesOut w (P.Active B) (c, regs) s' (b :: out) := by
  have := ReachesOut.head (Q := P.Active B) (s := (c, regs)) ⟨by rw [hc]; rfl, hB⟩
    (by rwa [step_emit (s := (c, regs)) hc])
  simpa [emitted, hc, Instr.emitted] using this

/-! ### Counting loops -/

/-- The code of a counting loop, placed at the label `b`: register `u` counts from `0` while its
value is less than that of `bound`, running the body at `body` for each value; the body continues
at `b + 2`, and the loop exits to `exit`. -/
def forCode (b u : ℕ) (bound : Expr) (body exit : ℕ) : List Instr :=
  [.assign u (const 0) (b + 1),
   .lt (reg u) bound body exit,
   .assign u (add (reg u) (const 1)) (b + 1)]

/-- **A counting loop emits what its body emits for each value of the counter.** The invariant
`Inv k` holds of the registers when the counter has the value `k`; it fixes the value `N` of the
bound and keeps the registers at most `B`. If the body, run on registers satisfying `Inv k` for
`k < N`, continues at `b + 2` with the counter unchanged, emitting `o k`, and the incremented
registers satisfy `Inv (k + 1)`, then the loop exits with registers satisfying `Inv N`, emitting
`o 0 ++ ⋯ ++ o (N - 1)`. -/
theorem reachesOut_forCode {b u body exit N : ℕ} {bound : Expr}
    (hP : P.CodeAt b (forCode b u bound body exit)) (Inv : ℕ → List ℕ → Prop)
    (o : ℕ → List Bool) (hNB : N ≤ B)
    (hInv : ∀ k regs, Inv k regs →
      regs.getD u 0 = k ∧ bound.eval regs = N ∧ u < regs.length ∧ ∀ r ∈ regs, r ≤ B)
    (hbody : ∀ k < N, ∀ regs, Inv k regs → ∃ regs',
      P.ReachesOut w (P.Active B) (body, regs) (b + 2, regs') (o k) ∧ regs'.getD u 0 = k ∧
        (∀ r ∈ regs', r ≤ B) ∧ Inv (k + 1) (regs'.set u (k + 1)))
    (regs : List ℕ) (hB : ∀ r ∈ regs, r ≤ B) (h0 : Inv 0 (regs.set u 0)) :
    ∃ regs', P.ReachesOut w (P.Active B) (b, regs) (exit, regs') ((List.range N).flatMap o) ∧
      Inv N regs' := by
  simp only [forCode, codeAt_cons] at hP
  obtain ⟨h₀, h₁, h₂, -⟩ := hP
  rw [show b + 1 + 1 = b + 2 by omega] at h₂
  have loop : ∀ e k regs, N - k = e → k ≤ N → Inv k regs → ∃ regs',
      P.ReachesOut w (P.Active B) (b + 1, regs) (exit, regs')
        ((List.range' k (N - k)).flatMap o) ∧ Inv N regs' := by
    intro e
    induction e with
    | zero =>
      intro k regs he hk hinv
      obtain ⟨hu, hN, -, hB'⟩ := hInv k regs hinv
      have hkN : k = N := by omega
      subst hkN
      refine ⟨regs, ReachesOut.lt h₁ hB' ?_, hinv⟩
      simp only [eval_reg, hu, hN, lt_irrefl, ↓reduceIte, Nat.sub_self, List.range'_zero,
        List.flatMap_nil]
      exact ReachesOut.refl _
    | succ e ih =>
      intro k regs he hk hinv
      obtain ⟨hu, hN, hlen, hB'⟩ := hInv k regs hinv
      have hkN : k < N := by omega
      obtain ⟨regs₁, hreach₁, hu₁, hB₁, hinv₁⟩ := hbody k hkN regs hinv
      obtain ⟨regs₂, hreach₂, hinv₂⟩ := ih (k + 1) (regs₁.set u (k + 1)) (by omega) hkN hinv₁
      refine ⟨regs₂, ?_, hinv₂⟩
      rw [show N - k = (N - (k + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons]
      refine ReachesOut.lt h₁ hB' ?_
      simp only [eval_reg, hu, hN, hkN, ↓reduceIte]
      refine hreach₁.trans (ReachesOut.assign h₂ hB₁ ?_)
      simp only [eval_add, eval_reg, eval_const, hu₁]
      exact hreach₂
  obtain ⟨regs', hreach, hinv⟩ := loop N 0 (regs.set u 0) (by omega) (Nat.zero_le _) h0
  refine ⟨regs', ReachesOut.assign h₀ hB ?_, hinv⟩
  rw [List.range_eq_range']
  simpa using hreach

/-! ### Logarithmic space -/

/-- **Counter programs with output run in logarithmic space.** If on every encoded input `enc a`
the program reaches a halting instruction with final word `fin`, passing only through
configurations at other instructions with registers at most `(n + 1) ^ d`, where `n` is the
length of the input, if the bits emitted on the way followed by `fin` are `encOut (f a)`, and if
the registers of the halting configuration are at most `(n + 1) ^ d` too, then `f` is computable
in logarithmic space. -/
theorem computableInLogSpace_of_reachesOut (P : CounterProgram) {α β : Type}
    {enc : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} (d : ℕ)
    (h : ∀ a, ∃ s out fin, P.ReachesOut (enc a) (P.Active (((enc a).length + 1) ^ d)) P.init s out ∧
      P.instr s.1 = .halt fin ∧ encOut (f a) = out ++ fin ∧
      ∀ r ∈ s.2, r ≤ ((enc a).length + 1) ^ d) :
    MultiTapeTM.ComputableInLogSpace f enc encOut := by
  choose s out fin hs using h
  choose t ht hpre hout using fun a => (hs a).1
  have hrun (a : α) (u : ℕ) : P.run (enc a) u = (P.step (enc a))^[u] P.init := rfl
  refine P.computableInLogSpace t (fun a => ?_) (fun a u hu => ?_) (fun a => ?_)
    ⟨d, fun a u hu => ?_⟩
  · rw [hrun, ht, halted, (hs a).2.1]
    rfl
  · rw [hrun]
    exact (hpre a u hu).1
  · rw [(hs a).2.2.1,
      P.toQueryMachine.output_eq_of_not_halted _ (fun i hi => (hpre a i hi).1), hout a]
    change _ = _ ++ P.finish ((P.step (enc a))^[t a] P.init)
    rw [ht, finish, (hs a).2.1]
    rfl
  · rcases lt_or_eq_of_le hu with hlt | rfl
    · exact (hpre a u hlt).2
    · rw [hrun, ht]
      exact (hs a).2.2.2

end CounterProgram

end Turing
