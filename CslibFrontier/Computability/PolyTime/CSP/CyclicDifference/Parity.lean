/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Table.ParityChain
public import CslibFrontier.Computability.PolyTime.CSP.Table
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native list-funded parity-chain construction

The actual recursive chain has an equivalent bounded map implementation. Every iteration count
and auxiliary offset is unary and funded by the supplied boundary list. Scope names and the
output use binary naturals. Only the four constant tables of widths zero through three occur;
no exponentially large white-face table is constructed.
-/

public section

namespace Cslib.Complexity.CSP.CyclicCompiler

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table Turing.MultiTapeTM

/-- Constant-size parity lookup, with a total width-three fallback. -/
@[expose] def smallEvenTable (n : ℕ) : Table :=
  if n = 0 then evenTable 0 else if n = 1 then evenTable 1
  else if n = 2 then evenTable 2 else evenTable 3

/-- Scope of one chain cell. The row index and fresh offset are internally unary. -/
@[expose] def chainScope (fresh first : ℕ) (rest : List ℕ) (i : ℕ) : List ℕ :=
  if rest.length ≤ 2 then first :: rest else
    [if i = 0 then first else fresh + (i - 1), rest.getD i 0,
      if i + 2 = rest.length then rest.getD (i + 1) 0 else fresh + i]

private theorem chainScope_step (fresh first b c d : ℕ) (rest : List ℕ) (i : ℕ)
    (hi : i < (c :: d :: rest).length - 1) :
    chainScope fresh first (b :: c :: d :: rest) (i + 1) =
      chainScope (fresh + 1) fresh (c :: d :: rest) i := by
  cases rest with
  | nil =>
    have hi0 : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
    subst i
    simp [chainScope]
  | cons e rest =>
    unfold chainScope
    simp only [List.length_cons] at hi ⊢
    simp only [show ¬ i + 1 = 0 by omega,
      show ¬ (rest.length + 1 + 1 + 1 + 1 ≤ 2) by omega,
      show ¬ (rest.length + 1 + 1 + 1 ≤ 2) by omega, ↓reduceIte,
      Nat.add_sub_cancel, List.getD_cons_succ]
    have hname : fresh + i = if i = 0 then fresh else fresh + 1 + (i - 1) := by
      split_ifs <;> omega
    rw [hname]
    have hcond : i + 1 + 2 = rest.length + 1 + 1 + 1 + 1 ↔
        i + 2 = rest.length + 1 + 1 + 1 := by omega
    simp only [hcond, Nat.add_assoc, Nat.add_comm 1 i]

/-- Exact bounded-map implementation of the recursive chain tail. -/
theorem parityChainTail_eq_map (fresh first : ℕ) (rest : List ℕ) :
    parityChainTail fresh first rest =
      (List.range (max 1 (rest.length - 1))).map fun i => Constraint.mk
        (smallEvenTable (min 3 (rest.length + 1))) (chainScope fresh first rest i) := by
  induction rest using List.twoStepInduction generalizing fresh first with
  | nil => simp [parityChainTail, smallEvenTable, chainScope]
  | singleton b => simp [parityChainTail, smallEvenTable, chainScope]
  | cons_cons b c rest _ ih =>
    cases rest with
    | nil => simp [parityChainTail, smallEvenTable, chainScope]
    | cons d rest =>
      have hlen : max 1 ((b :: c :: d :: rest).length - 1) =
          max 1 ((c :: d :: rest).length - 1) + 1 := by
        simp only [List.length_cons]; omega
      rw [parityChainTail, ih c, hlen, List.range_succ_eq_map, List.map_cons, List.map_map]
      rw [List.cons.injEq]
      constructor
      · simp [chainScope, smallEvenTable]
      · apply List.map_congr_left
        intro i hi
        have hb : i < (c :: d :: rest).length - 1 := by
          simp only [List.mem_range] at hi
          simp only [List.length_cons] at hi ⊢
          omega
        rw [show min 3 ((c :: d :: rest).length + 1) = 3 by
          simp only [List.length_cons]; omega,
          show min 3 ((b :: c :: d :: rest).length + 1) = 3 by
            simp only [List.length_cons]; omega]
        exact congrArg (Constraint.mk (smallEvenTable 3))
          (chainScope_step fresh first b c d rest i hb).symm

/-- Framed unary fresh offset, framed binary first name and binary remaining scope. -/
abbrev encParityTail := encPair encUnary (encPair encNat (encList encNat))

/-- Ordinary native polynomial-time construction of an arbitrary long parity chain tail. -/
theorem computableInPolyTime_parityChainTail :
    ComputableInPolyTime (fun p : ℕ × ℕ × List ℕ => parityChainTail p.1 p.2.1 p.2.2)
      encParityTail (encCSP encTable encNat) := by
  have hsmall : ComputableInPolyTime smallEvenTable encUnary encTable := by
    unfold smallEvenTable
    fun_prop
  have hscope : ComputableInPolyTime
      (fun p : (ℕ × ℕ × List ℕ) × ℕ => chainScope p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair encParityTail encUnary) (encList encNat) := by
    unfold chainScope encParityTail
    have hconv := ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_to_binary
    have hname : ComputableInPolyTime (fun p : (ℕ × ℕ × List ℕ) × ℕ =>
        if p.2 = 0 then p.1.2.1 else p.1.1 + (p.2 - 1))
        (encPair (encPair encUnary (encPair encNat (encList encNat))) encUnary) encNat := by
      apply ComputableInPolyTime.ite_decide
      · fun_prop
      · fun_prop
      · exact hconv.comp (by fun_prop)
    have hlast : ComputableInPolyTime (fun p : (ℕ × ℕ × List ℕ) × ℕ =>
        if p.2 + 2 = p.1.2.2.length then p.1.2.2.getD (p.2 + 1) 0 else p.1.1 + p.2)
        (encPair (encPair encUnary (encPair encNat (encList encNat))) encUnary) encNat := by
      apply ComputableInPolyTime.ite_decide
      · fun_prop
      · fun_prop
      · exact hconv.comp (by fun_prop)
    fun_prop
  simp only [parityChainTail_eq_map]
  unfold encCSP
  apply ComputableInPolyTime.mapWithInput (by unfold encParityTail; fun_prop)
  have htable := hsmall.comp (show ComputableInPolyTime
    (fun p : (ℕ × ℕ × List ℕ) × ℕ => min 3 (p.1.2.2.length + 1))
    (encPair encParityTail encUnary) encUnary by unfold encParityTail; fun_prop)
  exact encConstraint_mk_polyTime htable hscope

end Cslib.Complexity.CSP.CyclicCompiler
