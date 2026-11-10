/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.DeterministicTransitiveClosure.Compile
public import CslibFrontier.Logics.FirstOrder.Ordered.DeterministicTransitiveClosure
public import CslibFrontier.Computability.Complexity.Classes.LogSpace

/-!
# FO(DTC) model checking in logarithmic space

For each fixed sentence of FO(DTC) over a finite relational vocabulary expanded by the canonical
numeric symbols, the encoded query language belongs to the native class `L`. The input uses
`encStructure`, as for ordered first-order model checking in `L`; malformed table shapes and
cardinalities below two are rejected.

FO(DTC) sentences are FO(TC) syntax trees read with `DTC.interpretation`. The decider is one
deterministic counter program: it validates the input tables, rejects cardinalities below two,
runs the compiled code of the sentence, and accepts or rejects at the exit the code takes. It
halts with every register at most `(N + 1) ^ (d + w)` for input length `N`, maximal input arity
`d` and closure width `w`, so it runs in logarithmic space.

Each closure is evaluated by following unique successors for at most `n ^ k` steps, where the
successor is found by enumerating all candidate tuples and running the compiled body on each.
Every compiled block exits on both truth values, so closures under negation need nothing more
([Immerman1987], Theorem 4.2). The converse inclusion L ⊆ FO(DTC) remains open.

## Main definitions

* `Cslib.Logic.FO.Ordered.DTCModelChecker.decider`: the deterministic decider.

## Main results

* `Cslib.Logic.FO.Ordered.DTCModelChecker.encodedLanguage_mem_L`: a query defined by an FO(DTC)
  sentence is in native `L`.
* `Cslib.Logic.FO.Ordered.DTCDefinable.encodedLanguage_mem_L`: FO(DTC) ⊆ L on canonically ordered
  structures.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Theorem 4.2][Immerman1987]
-/

public section

universe u v

open FirstOrder Language

namespace Cslib.Logic.FO.Ordered.DTCModelChecker

open Turing Turing.CounterProgram Turing.CounterProgram.Block Expr Vocabulary.ModelChecker
open Operator (Formula RelEnv)
open TCModelChecker (decider_bounds)

variable {L : Language.{u, v}} [L.IsRelational] (v : Vocabulary L)

/-- The decider's code: the shape check, the size guard, the compiled sentence, accept, reject. -/
@[expose] def deciderCode (φ : Formula (language L) TC.shape [] Empty) : List Instr :=
  shapeCode v 0 (4 + 6 * v.count) (6 + 6 * v.count + len φ) ++
    [.lt (reg 0) (const 2) (6 + 6 * v.count + len φ) (5 + 6 * v.count)] ++
    compile v (fun e : Empty => e.elim) 3 φ (5 + 6 * v.count) (5 + 6 * v.count + len φ)
      (6 + 6 * v.count + len φ) ++ [.accept, .reject]

/-- The deterministic decider of an FO(DTC) sentence. -/
@[expose] def decider (φ : Formula (language L) TC.shape [] Empty) : CounterProgram where
  code := deciderCode v φ
  registers := 3 + scratch φ

variable {v}

private theorem decider_layout (φ : Formula (language L) TC.shape [] Empty) :
    (decider v φ).CodeAt 0 (shapeCode v 0 (4 + 6 * v.count) (6 + 6 * v.count + len φ)) ∧
    (decider v φ).instr (4 + 6 * v.count) =
      .lt (reg 0) (const 2) (6 + 6 * v.count + len φ) (5 + 6 * v.count) ∧
    (decider v φ).CodeAt (5 + 6 * v.count) (compile v (fun e : Empty => e.elim) 3 φ
      (5 + 6 * v.count) (5 + 6 * v.count + len φ) (6 + 6 * v.count + len φ)) ∧
    (decider v φ).instr (5 + 6 * v.count + len φ) = .accept ∧
    (decider v φ).instr (6 + 6 * v.count + len φ) = .reject := by
  have hcode : (decider v φ).CodeAt 0 (decider v φ).code :=
    codeAt_of_code_eq (pre := []) (post := []) (by simp)
  change (decider v φ).CodeAt 0 (deciderCode v φ) at hcode
  rw [deciderCode, codeAt_append, codeAt_append, codeAt_append] at hcode
  obtain ⟨⟨⟨hshape, hguard⟩, hcomp⟩, hhalt⟩ := hcode
  simp only [List.length_append, length_shapeCode, length_compile, List.length_singleton,
    Nat.zero_add] at hguard hcomp hhalt
  obtain ⟨hacc, hrest⟩ := codeAt_cons.mp hhalt
  refine ⟨hshape, (codeAt_cons.mp hguard).1, ?_, ?_, ?_⟩
  · rwa [show 4 + 6 * v.count + 1 = 5 + 6 * v.count by omega] at hcomp
  · rwa [show 4 + 6 * v.count + 1 + len φ = 5 + 6 * v.count + len φ by omega] at hacc
  · have := (codeAt_cons.mp hrest).1
    rwa [show 4 + 6 * v.count + 1 + len φ + 1 = 6 + 6 * v.count + len φ by omega] at this

variable (v) in
/-- **A query defined by an FO(DTC) sentence is in native `L`**: its source-only encoded language
is decided by one deterministic machine in logarithmic space. -/
theorem encodedLanguage_mem_L {φ : Formula (language L) TC.shape [] Empty} {K : Query L}
    (hφ : ∀ M : Ordered.Structure L,
      M ∈ K ↔ φ.Realize (M := M) DTC.interpretation RelEnv.empty Empty.elim) :
    K.encodedLanguage v ∈ Complexity.L encStructure := by
  classical
  refine ⟨fun a => decide (a ∈ K.encodedLanguage v), ?_, fun a => by simp⟩
  refine (decider v φ).computableInLogSpace_of_reaches (v.maxArity + TC.width φ) fun a => ?_
  obtain ⟨hshape, hguard, hcomp, hacc, hrej⟩ := decider_layout (v := v) φ
  obtain ⟨hB1, hnB, hwidth, hwB, hLB⟩ := decider_bounds v a (TC.width φ)
  obtain ⟨regs₁, hreach₁, hlen₁, h0₁, hB₁⟩ :=
    reaches_shapeCode hshape hLB hwB (List.replicate (3 + scratch φ) 0) (by simp) (by simp)
      (by simp)
  by_cases hwf : v.WellFormed a
  · rw [ite_eq_left hwf] at hreach₁
    have hreachGuard : (decider v φ).Reaches (encStructure a)
        ((decider v φ).Running (((encStructure a).length + 1) ^ (v.maxArity + TC.width φ)))
        (4 + 6 * v.count, regs₁)
        (if a.1 < 2 then 6 + 6 * v.count + len φ else 5 + 6 * v.count, regs₁) := by
      refine Reaches.lt hguard hB₁ ?_
      simp only [eval_reg, eval_const, h0₁ hwf]
      exact Reaches.refl _
    by_cases hn : 2 ≤ a.1
    · let _ : Fact (2 ≤ a.1) := ⟨hn⟩
      let _ := v.decode a
      rw [ite_eq_right (Nat.not_lt.mpr hn)] at hreachGuard
      have hE : Env v a (((encStructure a).length + 1) ^ (v.maxArity + TC.width φ)) :=
        ⟨fun fv base val => ModelChecker.atomicCompiler_correct hwf fv base val, hB1, hnB⟩
      obtain ⟨res, regs₂, hres, hreach₂, hk⟩ := correct hE φ rfl hwidth (fun e : Empty => e.elim)
        3 Empty.elim RelEnv.empty _ _ _ regs₁ hcomp (by decide) (fun e => e.elim)
        (by rw [hlen₁]; simp) (h0₁ hwf) (fun e => e.elim) hB₁
      refine ⟨(if res then 5 + 6 * v.count + len φ else 6 + 6 * v.count + len φ, regs₂),
        (hreach₁.trans hreachGuard).trans hreach₂, ?_, hk.2.2⟩
      have hmem : a ∈ K.encodedLanguage v ↔ res = true := by
        rw [hres]
        exact ⟨fun ⟨_, _, h⟩ => (hφ (decoded v a hn)).mp h,
          fun h => ⟨hwf, hn, (hφ (decoded v a hn)).mpr h⟩⟩
      cases res
      · rw [ite_eq_right Bool.false_ne_true, hrej]
        simp [hmem]
      · rw [ite_eq_left rfl, hacc]
        simp [hmem]
    · rw [ite_eq_left (Nat.lt_of_not_ge hn)] at hreachGuard
      refine ⟨(6 + 6 * v.count + len φ, regs₁), hreach₁.trans hreachGuard, ?_, hB₁⟩
      rw [hrej]
      simp [Query.not_mem_encodedLanguage_of_lt_two K v (Nat.lt_of_not_ge hn)]
  · rw [ite_eq_right hwf] at hreach₁
    refine ⟨(6 + 6 * v.count + len φ, regs₁), hreach₁, ?_, hB₁⟩
    rw [hrej]
    simp [Query.not_mem_encodedLanguage_of_not_wellFormed K v hwf]

end Cslib.Logic.FO.Ordered.DTCModelChecker

namespace Cslib.Logic.FO.Ordered

/-- **FO(DTC) ⊆ L** on canonically ordered structures: a query defined by one FO(DTC) sentence is
in native deterministic logarithmic space, at the source-only structure encoding
([Immerman1987], Theorem 4.2). -/
theorem DTCDefinable.encodedLanguage_mem_L {L : Language} [L.IsRelational] {K : Query L}
    (hK : DTCDefinable K) (v : Vocabulary L) :
    K.encodedLanguage v ∈ Complexity.L encStructure :=
  let ⟨_, hφ⟩ := hK
  DTCModelChecker.encodedLanguage_mem_L v hφ

end Cslib.Logic.FO.Ordered
