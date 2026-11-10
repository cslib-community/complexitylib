/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder

/-!
# Deterministic deciders of ordered queries

A deterministic decider of an ordered query on `encStructure` inputs validates the input tables,
rejects cardinalities below two, runs a block of counter code with a true exit and a false exit,
and accepts or rejects at the exit the block takes. `blockDecider` assembles such a program
around any block. `mem_L_of_decidingBlock` reduces membership in `L` to the correctness of the
block on well-formed inputs of cardinality at least two, with every register bounded by
`(N + 1) ^ (d + k)` for input length `N` and maximal input arity `d`. The extra exponent `k` lets
the block hold `k`-tuples of universe elements in single registers.

Ordered first-order model checking and FO(DTC) model checking are the two clients. The FO(TC)
decider is nondeterministic, so it shares only `decider_bounds`.

## Main definitions

* `Cslib.Logic.FO.Ordered.blockDecider`: the shape check, the size guard, the block, accept and
  reject.

## Main results

* `Cslib.Logic.FO.Ordered.decider_bounds`: the register bound dominates the cardinality, its
  `k`-th power, the input length and the table sizes.
* `Cslib.Logic.FO.Ordered.mem_L_of_decidingBlock`: a correct block puts the query in `L`.
-/

public section

universe u v

open FirstOrder Language Turing Turing.CounterProgram Expr

namespace Cslib.Logic.FO.Ordered

open Vocabulary.ModelChecker

variable {L : Language.{u, v}} (v : Vocabulary L)

/-- The register bound `(N + 1) ^ (d + k)` of a decider, for input length `N` and maximal input
arity `d`, dominates `1`, the cardinality `n`, `n ^ k`, `N` and the size of every input table. -/
theorem decider_bounds (a : EncodedStructure) (k : ℕ) :
    1 ≤ ((encStructure a).length + 1) ^ (v.maxArity + k) ∧
    a.1 ≤ ((encStructure a).length + 1) ^ (v.maxArity + k) ∧
    a.1 ^ k ≤ ((encStructure a).length + 1) ^ (v.maxArity + k) ∧
    (encStructure a).length ≤ ((encStructure a).length + 1) ^ (v.maxArity + k) ∧
    ∀ i, a.1 ^ arityAt v i ≤ ((encStructure a).length + 1) ^ (v.maxArity + k) := by
  have hm0 : v.maxArity ≠ 0 := by simp [Vocabulary.maxArity]
  have hN : 1 ≤ (encStructure a).length + 1 := Nat.le_add_left 1 _
  have hmono : ((encStructure a).length + 1) ^ v.maxArity ≤
      ((encStructure a).length + 1) ^ (v.maxArity + k) := Nat.pow_le_pow_right hN (by omega)
  have hn : a.1 ≤ (encStructure a).length + 1 :=
    (card_le_length_encStructure a).trans (Nat.le_succ _)
  refine ⟨Nat.one_le_pow _ _ hN, ?_, ?_, (length_le_pow_maxArity v a).trans hmono,
    fun i => (pow_arityAt_le v a i).trans hmono⟩
  · exact hn.trans ((Nat.le_self_pow hm0 _).trans hmono)
  · exact (Nat.pow_le_pow_left hn k).trans (Nat.pow_le_pow_right hN (by omega))

/-- The deterministic decider around a block `C b T F` of length `c`, placed at `b` with exits
`T` (accept) and `F` (reject): the shape check, the guard rejecting cardinalities below two, the
block, accept, reject. Registers `0` to `2` are the shape check's, followed by `s` scratch
registers for the block. -/
@[expose] def blockDecider (C : ℕ → ℕ → ℕ → List Instr) (c s : ℕ) : CounterProgram where
  code :=
    shapeCode v 0 (4 + 6 * v.count) (6 + 6 * v.count + c) ++
      [.lt (reg 0) (const 2) (6 + 6 * v.count + c) (5 + 6 * v.count)] ++
      C (5 + 6 * v.count) (5 + 6 * v.count + c) (6 + 6 * v.count + c) ++ [.accept, .reject]
  registers := 3 + s

variable {v}

private theorem blockDecider_layout {C : ℕ → ℕ → ℕ → List Instr} {c : ℕ}
    (hC : ∀ b T F, (C b T F).length = c) (s : ℕ) :
    (blockDecider v C c s).CodeAt 0 (shapeCode v 0 (4 + 6 * v.count) (6 + 6 * v.count + c)) ∧
    (blockDecider v C c s).instr (4 + 6 * v.count) =
      .lt (reg 0) (const 2) (6 + 6 * v.count + c) (5 + 6 * v.count) ∧
    (blockDecider v C c s).CodeAt (5 + 6 * v.count)
      (C (5 + 6 * v.count) (5 + 6 * v.count + c) (6 + 6 * v.count + c)) ∧
    (blockDecider v C c s).instr (5 + 6 * v.count + c) = .accept ∧
    (blockDecider v C c s).instr (6 + 6 * v.count + c) = .reject := by
  have hcode : (blockDecider v C c s).CodeAt 0 (blockDecider v C c s).code :=
    codeAt_of_code_eq (pre := []) (post := []) (by simp)
  change (blockDecider v C c s).CodeAt 0 (shapeCode v 0 (4 + 6 * v.count) (6 + 6 * v.count + c) ++
    [.lt (reg 0) (const 2) (6 + 6 * v.count + c) (5 + 6 * v.count)] ++
    C (5 + 6 * v.count) (5 + 6 * v.count + c) (6 + 6 * v.count + c) ++ [.accept, .reject])
    at hcode
  rw [codeAt_append, codeAt_append, codeAt_append] at hcode
  obtain ⟨⟨⟨hshape, hguard⟩, hcomp⟩, hhalt⟩ := hcode
  simp only [List.length_append, length_shapeCode, hC, List.length_singleton, Nat.zero_add]
    at hguard hcomp hhalt
  obtain ⟨hacc, hrest⟩ := codeAt_cons.mp hhalt
  refine ⟨hshape, (codeAt_cons.mp hguard).1, ?_, ?_, ?_⟩
  · rwa [show 4 + 6 * v.count + 1 = 5 + 6 * v.count by omega] at hcomp
  · rwa [show 4 + 6 * v.count + 1 + c = 5 + 6 * v.count + c by omega] at hacc
  · have := (codeAt_cons.mp hrest).1
    rwa [show 4 + 6 * v.count + 1 + c + 1 = 6 + 6 * v.count + c by omega] at this

variable (v) in
/-- **A deciding block puts an ordered query in `L`.** Let `S` contain only well-formed inputs
of cardinality at least two. Suppose that on every such input, the block `C b T F`, run from the
cardinality in register `0` and `s` registers after the shape check's, exits to `T` exactly on
members of `S` and otherwise to `F`, with every register at most `(N + 1) ^ (d + k)`. Then
`blockDecider v C c s` decides `S` in logarithmic space. -/
theorem mem_L_of_decidingBlock {S : Set EncodedStructure} {C : ℕ → ℕ → ℕ → List Instr}
    {c s k : ℕ} (hC : ∀ b T F, (C b T F).length = c)
    (hS : ∀ a ∈ S, v.WellFormed a ∧ 2 ≤ a.1)
    (hblock : ∀ (a : EncodedStructure), v.WellFormed a → 2 ≤ a.1 → ∀ (P : CounterProgram)
      (b T F : ℕ) (regs : List ℕ), P.CodeAt b (C b T F) → regs.length = 3 + s →
      regs.getD 0 0 = a.1 → (∀ r ∈ regs, r ≤ ((encStructure a).length + 1) ^ (v.maxArity + k)) →
      ∃ (res : Bool) (regs' : List ℕ), (res = true ↔ a ∈ S) ∧
        P.Reaches (encStructure a) (P.Running (((encStructure a).length + 1) ^ (v.maxArity + k)))
          (b, regs) (if res then T else F, regs') ∧
        ∀ r ∈ regs', r ≤ ((encStructure a).length + 1) ^ (v.maxArity + k)) :
    S ∈ Complexity.L encStructure := by
  classical
  refine ⟨fun a => decide (a ∈ S), ?_, fun a => by simp⟩
  refine (blockDecider v C c s).computableInLogSpace_of_reaches (v.maxArity + k) fun a => ?_
  obtain ⟨hshape, hguard, hcomp, hacc, hrej⟩ := blockDecider_layout (v := v) hC s
  obtain ⟨-, -, -, hwB, hLB⟩ := decider_bounds v a k
  obtain ⟨regs₁, hreach₁, hlen₁, h0₁, hB₁⟩ :=
    reaches_shapeCode hshape hLB hwB (List.replicate (3 + s) 0) (by simp) (by simp) (by simp)
  by_cases hwf : v.WellFormed a
  · rw [ite_eq_left hwf] at hreach₁
    have hreachGuard : (blockDecider v C c s).Reaches (encStructure a)
        ((blockDecider v C c s).Running (((encStructure a).length + 1) ^ (v.maxArity + k)))
        (4 + 6 * v.count, regs₁)
        (if a.1 < 2 then 6 + 6 * v.count + c else 5 + 6 * v.count, regs₁) := by
      refine Reaches.lt hguard hB₁ ?_
      simp only [eval_reg, eval_const, h0₁ hwf]
      exact Reaches.refl _
    by_cases hn : 2 ≤ a.1
    · rw [ite_eq_right (Nat.not_lt.mpr hn)] at hreachGuard
      obtain ⟨res, regs₂, hres, hreach₂, hB₂⟩ := hblock a hwf hn _ _ _ _ regs₁ hcomp
        (by rw [hlen₁, List.length_replicate]) (h0₁ hwf) hB₁
      refine ⟨(if res then 5 + 6 * v.count + c else 6 + 6 * v.count + c, regs₂),
        (hreach₁.trans hreachGuard).trans hreach₂, ?_, hB₂⟩
      cases res
      · rw [ite_eq_right Bool.false_ne_true, hrej]
        simp [← hres]
      · rw [ite_eq_left rfl, hacc]
        simp [← hres]
    · rw [ite_eq_left (Nat.lt_of_not_ge hn)] at hreachGuard
      refine ⟨(6 + 6 * v.count + c, regs₁), hreach₁.trans hreachGuard, ?_, hB₁⟩
      have hnS : a ∉ S := fun h => hn (hS a h).2
      rw [hrej]
      simp [hnS]
  · rw [ite_eq_right hwf] at hreach₁
    refine ⟨(6 + 6 * v.count + c, regs₁), hreach₁, ?_, hB₁⟩
    have hnS : a ∉ S := fun h => hwf (hS a h).1
    rw [hrej]
    simp [hnS]

end Cslib.Logic.FO.Ordered
