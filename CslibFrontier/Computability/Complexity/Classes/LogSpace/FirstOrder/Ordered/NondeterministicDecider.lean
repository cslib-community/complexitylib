/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Decider
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Block
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Step

/-!
# Nondeterministic deciders of ordered queries

A nondeterministic decider of an ordered query on `encStructure` inputs keeps its choice bit in
register `0`. Above the choice it validates the input tables and rejects cardinalities below two,
then runs a nondeterministic block of counter code with a true exit, and accepts at that exit.
`nblockDecider` assembles such a program around any block, as `blockDecider` does in the
deterministic case. `mem_NL_of_soundCompleteBlock` reduces membership in `NL` to the
correctness of the block on well-formed inputs of cardinality at least two. Every branch must
reach the true exit only on members, or halt at the block's reject label. On members, some
branch must reach the true exit. Every register stays at most `(N + 1) ^ (d + k)` for input length
`N` and maximal input arity `d`.

FO(TC) model checking is the client.

## Main definitions

* `Cslib.Logic.FO.Ordered.nblockDecider`: the shape check, the size guard, the block, accept and
  reject, above the choice bit.

## Main results

* `Cslib.Logic.FO.Ordered.mem_NL_of_soundCompleteBlock`: a sound and complete block puts the
  query in `NL`.
-/

public section

universe u v

open FirstOrder Language Turing Turing.CounterProgram Turing.CounterProgram.Block Expr

namespace Cslib.Logic.FO.Ordered

open Vocabulary.ModelChecker

variable {L : Language.{u, v}} (v : Vocabulary L)

/-- The nondeterministic decider around a block `C b T F` of length `c`, placed at `b` with exits
`T` (accept) and `F` (reject): the shape check and the guard rejecting cardinalities below two,
shifted above the choice bit, then the block, accept, reject. Register `0` is the choice bit,
registers `1` to `3` are the shape check's, followed by `s` scratch registers for the block. -/
@[expose] def nblockDecider (C : ℕ → ℕ → ℕ → List Instr) (c s : ℕ) : CounterProgram where
  code :=
    (shapeCode v 0 (4 + 6 * v.count) (6 + 6 * v.count + c)).map Instr.shift ++
      [(Instr.lt (reg 0) (const 2) (6 + 6 * v.count + c) (5 + 6 * v.count)).shift] ++
      C (5 + 6 * v.count) (5 + 6 * v.count + c) (6 + 6 * v.count + c) ++ [.accept, .reject]
  registers := 4 + s

variable {v}

private theorem nblockDecider_layout {C : ℕ → ℕ → ℕ → List Instr} {c : ℕ}
    (hC : ∀ b T F, (C b T F).length = c) (s : ℕ) :
    (nblockDecider v C c s).CodeAt 0
      ((shapeCode v 0 (4 + 6 * v.count) (6 + 6 * v.count + c)).map Instr.shift) ∧
    (nblockDecider v C c s).instr (4 + 6 * v.count) =
      (Instr.lt (reg 0) (const 2) (6 + 6 * v.count + c) (5 + 6 * v.count)).shift ∧
    (nblockDecider v C c s).CodeAt (5 + 6 * v.count)
      (C (5 + 6 * v.count) (5 + 6 * v.count + c) (6 + 6 * v.count + c)) ∧
    (nblockDecider v C c s).instr (5 + 6 * v.count + c) = .accept ∧
    (nblockDecider v C c s).instr (6 + 6 * v.count + c) = .reject :=
  decider_layout rfl (by rw [List.length_map, length_shapeCode]) (hC ..)

private theorem init_nblockDecider (C : ℕ → ℕ → ℕ → List Instr) (c s : ℕ) :
    (nblockDecider v C c s).init = (0, (false : Bool).toNat :: List.replicate (3 + s) 0) := by
  simp only [init, nblockDecider, Bool.toNat_false]
  rw [show 4 + s = (3 + s) + 1 by omega, List.replicate_succ]

variable (v) in
/-- **A sound and complete block puts an ordered query in `NL`.** Let `S` contain only
well-formed inputs of cardinality at least two. Suppose that on every such input, the block
`C b T F`, run above the choice bit from the cardinality in register `0` and `s` registers after
the shape check's, with every register at most `(N + 1) ^ (d + k)`:

* is sound: every branch halts satisfying `Post` or reaches `T` only on members of `S`, keeping
  every register within the bound, whenever `F` is a halting label satisfying `Post`;
* is complete: on members of `S`, some branch reaches `T`.

Then `nblockDecider v C c s` decides `S` in nondeterministic logarithmic space. -/
theorem mem_NL_of_soundCompleteBlock {S : Set EncodedStructure} {C : ℕ → ℕ → ℕ → List Instr}
    {c s k : ℕ} (hC : ∀ b T F, (C b T F).length = c)
    (hS : ∀ a ∈ S, v.WellFormed a ∧ 2 ≤ a.1)
    (hblock : ∀ (a : EncodedStructure), v.WellFormed a → 2 ≤ a.1 → ∀ (P : CounterProgram)
      (Post : Config → Prop) (b T F : ℕ) (regs : List ℕ), P.CodeAt b (C b T F) →
      (P.instr F).halts = true → (∀ x : Config, x.1 = F → Post x) → regs.length = 3 + s →
      regs.getD 0 0 = a.1 → (∀ r ∈ regs, r ≤ ((encStructure a).length + 1) ^ (v.maxArity + k)) →
      Sound P (encStructure a) (((encStructure a).length + 1) ^ (v.maxArity + k)) Post b regs T
        (fun regs' => (∀ r ∈ regs', r ≤ ((encStructure a).length + 1) ^ (v.maxArity + k)) ∧
          a ∈ S) ∧
      (a ∈ S → Complete P (encStructure a) b regs T fun _ => True)) :
    S ∈ Complexity.NL encStructure := by
  refine exists_decidesInLogSpace_of_allBranches (nblockDecider v C c s) (v.maxArity + k)
    (fun a => ?_) fun a ha => ?_
  · obtain ⟨hshape, hguard, hcomp, hacc, hrej⟩ := nblockDecider_layout (v := v) hC s
    obtain ⟨hB1, -, -, hwB, hLB⟩ := decider_bounds v a k
    rw [init_nblockDecider]
    suffices h : Sound (nblockDecider v C c s) (encStructure a)
        (((encStructure a).length + 1) ^ (v.maxArity + k))
        (fun x => (nblockDecider v C c s).instr x.1 = .accept → a ∈ S) 0
        (List.replicate (3 + s) 0) 0 (fun _ => False) from
      (h false).mono fun _ ⟨_, _, _, h⟩ => h
    obtain ⟨regs₁, hreach₁, hlen₁, h0₁, hB₁⟩ :=
      reaches_shapeCode (P := padded 0 (shapeCode v 0 (4 + 6 * v.count) (6 + 6 * v.count + c)))
        (codeAt_padded 0 _) hLB hwB (List.replicate (3 + s) 0) (by simp) (by simp) (by simp)
    refine Sound.of_reaches hB1 hshape hreach₁ ?_
    have hreject : ∀ regs : List ℕ,
        (∀ r ∈ regs, r ≤ ((encStructure a).length + 1) ^ (v.maxArity + k)) →
        Sound (nblockDecider v C c s) (encStructure a)
          (((encStructure a).length + 1) ^ (v.maxArity + k))
          (fun x => (nblockDecider v C c s).instr x.1 = .accept → a ∈ S)
          (6 + 6 * v.count + c) regs 0 (fun _ => False) := fun regs hregs =>
      Sound.halt hB1 (by rw [hrej]; rfl) (fun _ h => by simp [hrej] at h) hregs
    by_cases hwf : v.WellFormed a
    · rw [ite_eq_left hwf]
      by_cases hn : 2 ≤ a.1
      · refine Sound.of_oblivious hB1 (l' := 5 + 6 * v.count) (regs' := regs₁) ?_ ?_
        · cp_step [h0₁ hwf]
        refine ((hblock a hwf hn _ _ _ _ _ regs₁ hcomp (by rw [hrej]; rfl)
          (fun x hx h => by simp [hx, hrej] at h) (by rw [hlen₁, List.length_replicate])
          (h0₁ hwf) hB₁).1).bind fun regs' ⟨hB', haS⟩ =>
            Sound.halt hB1 (by rw [hacc]; rfl) (fun _ _ => haS) hB'
      · refine Sound.of_oblivious hB1 (l' := 6 + 6 * v.count + c) (regs' := regs₁) ?_
          (hreject regs₁ hB₁)
        cp_step [h0₁ hwf]
    · rw [ite_eq_right hwf]
      exact hreject regs₁ hB₁
  · obtain ⟨hwf, hn⟩ := hS a ha
    obtain ⟨hshape, hguard, hcomp, hacc, hrej⟩ := nblockDecider_layout (v := v) hC s
    obtain ⟨hB1, -, -, hwB, hLB⟩ := decider_bounds v a k
    obtain ⟨regs₁, hreach₁, hlen₁, h0₁, hB₁⟩ :=
      reaches_shapeCode (P := padded 0 (shapeCode v 0 (4 + 6 * v.count) (6 + 6 * v.count + c)))
        (codeAt_padded 0 _) hLB hwB (List.replicate (3 + s) 0) (by simp) (by simp) (by simp)
    rw [ite_eq_left hwf] at hreach₁
    have hguardStep : (nblockDecider v C c s).Reaches (encStructure a)
        ((nblockDecider v C c s).Oblivious (((encStructure a).length + 1) ^ (v.maxArity + k)))
        (4 + 6 * v.count, 0 :: regs₁) (5 + 6 * v.count, 0 :: regs₁) := by
      cp_step [h0₁ hwf]
    obtain ⟨regs', -, hbr⟩ := Complete.of_reaches hshape hreach₁
      (Complete.of_oblivious hguardStep ((hblock a hwf hn _ (fun _ => True) _ _ _ regs₁ hcomp
        (by rw [hrej]; rfl) (fun _ _ => trivial) (by rw [hlen₁, List.length_replicate])
        (h0₁ hwf) hB₁).2 ha))
    obtain ⟨c', hc'⟩ := hbr false
    rw [init_nblockDecider]
    exact ⟨_, hc', hacc⟩

end Cslib.Logic.FO.Ordered
