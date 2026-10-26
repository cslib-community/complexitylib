/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Mathlib.Data.List.Fold

/-!
# Functional programs with polynomial-time certificates

Adapted from `CslibTests/ComputationalCryptoPrograms.lean` on the cslib `crypto` branch.
Programs use ordinary functional code; loop contracts mention values and encoded sizes.
-/

namespace ComplexityTests.PolyTimeTactic

open Turing.MultiTapeTM

-- Finite-domain lookup works with arbitrary fixed encodings and an infinite output type.
example {X Y : Type} [Finite X] (f : X → Y)
    (input : X ↪ List Bool) (output : Y ↪ List Bool) :
    ComputableTidilyInPolyTime f input output := by
  polytime

example (f : Bool → ℕ) : ComputableTidilyInPolyTime f encBool encUnary := by
  polytime

-- Fixed finite products also support lookup without a specialized callback certificate.
example (f : Fin 7 × Bool → ℕ) :
    ComputableTidilyInPolyTime f (encPair (encFinEnum (Fin 7)) encBool) encUnary := by
  polytime

-- A finite output alone does not certify an arbitrary function on an infinite input type.
example (_f : ℕ → Bool) : True := by
  fail_if_success
    have : ComputableTidilyInPolyTime _f encUnary encBool := by polytime
  trivial

example : ComputableTidilyInPolyTime
    (fun p : ℕ × List ℕ => (List.range p.1).flatMap fun i => p.2.map fun j => i + j)
    (encPair encUnary (encList encUnary)) (encList encUnary) := by
  polytime

example (f g : List Bool → List Bool)
    (hf : ComputableTidilyInPolyTime f encBits encBits)
    (hg : ComputableTidilyInPolyTime g encBits encBits) :
    ComputableTidilyInPolyTime (fun word => g (f word) ++ word) encBits encBits := by
  fail_if_success (clear hg; polytime)
  polytime

-- Projecting from an arbitrary representation still requires its conversion certificate.
example (encode : List Bool ↪ List Bool)
    (h : ComputableTidilyInPolyTime (fun word => word) encode encBits) :
    ComputableTidilyInPolyTime (fun p : List Bool × ℕ => p.1)
      (encPair encode encUnary) encBits := by
  fail_if_success (clear h; fun_prop)
  fail_if_success (clear h; polytime)
  polytime

example (encode : List Bool ↪ List Bool)
    (h : ComputableTidilyInPolyTime (fun word => word) encode encBits) :
    ComputableTidilyInPolyTime (fun p : ℕ × List Bool => p.2)
      (encPair encUnary encode) encBits := by
  fail_if_success (clear h; fun_prop)
  fail_if_success (clear h; polytime)
  polytime

example : ComputableTidilyInPolyTime
    (fun word : List Bool => word.foldl (fun reversed bit => bit :: reversed) [])
    encBits encBits := by
  polytime

example : ComputableTidilyInPolyTime (fun word : List Bool => word.tail.headD false)
    encBits encBool := by
  polytime

example (step : List Bool → Bool → List Bool) (growth : ℕ)
    (hstep : ComputableTidilyInPolyTime (fun pair : List Bool × Bool => step pair.1 pair.2)
      (encPair encBits encBool) encBits)
    (hgrowth : ∀ word bit, (step word bit).length ≤ word.length + growth) :
    ComputableTidilyInPolyTime (fun word : List Bool => word.foldl step word)
      encBits encBits := by
  fail_if_success (clear hstep; polytime)
  fail_if_success (clear hgrowth; polytime)
  polytime

-- No rule can replace a missing certificate or a missing state-growth argument.
example (_f : List Bool → List Bool) : True := by
  fail_if_success
    have : ComputableTidilyInPolyTime _f encBits encBits := by polytime
  fail_if_success
    have : ComputableTidilyInPolyTime
        (fun word : List Bool => word.foldl (fun current _ => current ++ current) [true])
        encBits encBits := by polytime
  fail_if_success
    have : ComputableTidilyInPolyTime (fun n : ℕ => 2 ^ n) encUnary encUnary := by polytime
  trivial

-- A supplied algorithm may take nested tuples assembled from captured data.
example (algorithm : (List Bool × ℕ) × List Bool → List Bool)
    (halgorithm : ComputableTidilyInPolyTime algorithm
      (encPair (encPair encBits encUnary) encBits) encBits) :
    ComputableTidilyInPolyTime
      (fun word : List Bool => algorithm ((word.reverse, word.length), word ++ word))
      encBits encBits := by
  polytime

-- A curried routine's sole remaining composition premise keeps its preparation name.
example (algorithm : ℕ → ℕ → List Bool → Bool)
    (h : ComputableTidilyInPolyTime
      (fun input : (ℕ × ℕ) × List Bool => algorithm input.1.1 input.1.2 input.2)
      (encPair (encPair encUnary encUnary) encBits) encBool) :
    ComputableTidilyInPolyTime (fun input : ℕ × List Bool =>
      algorithm input.1 input.2.length (input.2 ++ input.2))
      (encPair encUnary encBits) encBool := by
  fail_if_success (clear h; polytime)
  polytime

-- A locally supplied routine may have several certificates with different encodings.
example (f : ℕ → Bool)
    (_hfUnary : ComputableTidilyInPolyTime f encUnary encBool)
    (hfBinary : ComputableTidilyInPolyTime f encNat encBool) :
    ComputableTidilyInPolyTime (fun p : ℕ × Bool => f p.1)
      (encPair encNat encBool) encBool := by
  polytime

-- A complete expression's certificate need not supply certificates for its individual parts.
example (f g : List Bool → List Bool)
    (h : ComputableTidilyInPolyTime (fun word => f word ++ g word) encBits encBits) :
    ComputableTidilyInPolyTime (fun word => f word.reverse ++ g word.reverse)
      encBits encBits := by
  fail_if_success (clear h; polytime)
  polytime

example (f g : List Bool → List Bool)
    (h : ComputableTidilyInPolyTime (fun word => (f word, g word))
      encBits (encPair encBits encBits)) :
    ComputableTidilyInPolyTime (fun p : Bool × List Bool => let word := p.2; (f word, g word))
      (encPair encBool encBits) (encPair encBits encBits) := by polytime

example (f : List Bool → Bool) (g : List Bool → List Bool)
    (h : ComputableTidilyInPolyTime (fun word => f word :: g word) encBits encBits) :
    ComputableTidilyInPolyTime (fun word => f word.reverse :: g word.reverse)
      encBits encBits := by polytime

-- The same reuse works for whole loops without deriving a second step-growth contract.
example (step : List Bool → Bool → List Bool)
    (h : ComputableTidilyInPolyTime (fun word => word.foldl step []) encBits encBits) :
    ComputableTidilyInPolyTime (fun p : Bool × List Bool => p.2.foldl step [])
      (encPair encBool encBits) encBits := by polytime

example (step : List Bool → List Bool)
    (h : ComputableTidilyInPolyTime (fun word => step^[word.length] word) encBits encBits) :
    ComputableTidilyInPolyTime (fun p : Bool × List Bool => step^[p.2.length] p.2)
      (encPair encBool encBits) encBits := by polytime

-- Decomposition remains available when a whole certificate needs unavailable preprocessing.
example (f g : List Bool → List Bool) (other : List Bool ↪ List Bool)
    (_hwhole : ComputableTidilyInPolyTime (fun word => f word ++ g word) other encBits)
    (hf : ComputableTidilyInPolyTime f encBits encBits)
    (hg : ComputableTidilyInPolyTime g encBits encBits) :
    ComputableTidilyInPolyTime (fun word => f word.reverse ++ g word.reverse)
      encBits encBits := by polytime

-- The step's fixed additive growth is inferred from the constructor.
example : ComputableTidilyInPolyTime
    (fun n : ℕ => (fun word : List Bool => false :: word)^[n] []) encUnary encBits := by
  polytime

private def reverseCopy (word : List Bool) : List Bool := word.reverse ++ word

@[fun_prop, program_certificate]
private theorem reverseCopy_polytime : ComputableTidilyInPolyTime reverseCopy encBits encBits := by
  unfold reverseCopy
  polytime

open Lean Mathlib.Meta.FunProp in
private meta def checkFunctionRule (name : Name) (priority : Nat := eval_prio default) :
    MetaM Unit := do
  let .function thm ← getTheoremFromConst name
    | throwError "expected a function certificate"
  let entries ← getTheoremsForFunction thm.funOrigin.name thm.funPropName
  let entries := entries.filter (·.thmOrigin.name == name)
  unless entries.size == 1 && entries[0]!.priority == priority do
    throwError "expected one registration of {name} with priority {priority}"

-- The annotation reuses imported and same-file fun_prop entries without duplicating them.
run_meta
  checkFunctionRule ``reverseCopy_polytime
  checkFunctionRule ``ComputableTidilyInPolyTime.mapToBitsWithInput
  checkFunctionRule ``ComputableTidilyInPolyTime.bitsFoldlWithInput
  checkFunctionRule ``ComputableTidilyInPolyTime.bitsStrictMajorityWithInput

-- A different certificate for the same function keeps its own registration and priority.
private theorem reverseCopy_prioritized : ComputableTidilyInPolyTime reverseCopy encBits encBits :=
  reverseCopy_polytime

run_meta Mathlib.Meta.FunProp.addTheorem ``reverseCopy_prioritized .global 1234
attribute [program_certificate] reverseCopy_prioritized
run_meta
  checkFunctionRule ``reverseCopy_polytime
  checkFunctionRule ``reverseCopy_prioritized 1234

-- Local evidence cannot suppress a registration that must survive the section.
private theorem reverseCopy_local : ComputableTidilyInPolyTime reverseCopy encBits encBits :=
  reverseCopy_polytime

section
attribute [local fun_prop] reverseCopy_local
attribute [program_certificate] reverseCopy_local
end

run_meta checkFunctionRule ``reverseCopy_local

-- The same applies to an active scoped attribute after leaving that scope.
private theorem reverseCopy_scoped : ComputableTidilyInPolyTime reverseCopy encBits encBits :=
  reverseCopy_polytime

namespace Scoped
attribute [scoped fun_prop] reverseCopy_scoped
end Scoped

section
open scoped Scoped
attribute [program_certificate] reverseCopy_scoped
end

run_meta checkFunctionRule ``reverseCopy_scoped

-- Constant functions use fun_prop's separate lambda-theorem index.
@[fun_prop, program_certificate]
private theorem constantFalse_polytime :
    ComputableTidilyInPolyTime (fun _ : List Bool => false) encBits encBool := .const false

run_meta
  let .lam thm ← Mathlib.Meta.FunProp.getTheoremFromConst ``constantFalse_polytime
    | throwError "expected a constant-function certificate"
  let entries ← Mathlib.Meta.FunProp.getLambdaTheorems thm.funPropName thm.thmArgs.type
  unless (entries.filter (·.thmName == ``constantFalse_polytime)).size == 1 do
    throwError "expected one constant-function registration"

attribute [irreducible] reverseCopy

-- Registered routine certificates remain usable when the implementation is not unfolded.
example : ComputableTidilyInPolyTime reverseCopy encBits encBits := by polytime

example : ComputableTidilyInPolyTime (fun p : Bool × List Bool => reverseCopy p.2)
    (encPair encBool encBits) encBits := by polytime

example : ComputableTidilyInPolyTime (fun word => reverseCopy (reverseCopy word))
    encBits encBits := by polytime

private def appendFixed (n : ℕ) (word : List Bool) : List Bool :=
  List.replicate n false ++ word

@[program_certificate]
private theorem appendFixed_zero (n : ℕ) (h : n = 0) :
    ComputableTidilyInPolyTime (appendFixed n) encBits encBits := by
  subst n
  fun_prop [appendFixed]

@[program_certificate]
private theorem appendFixed_polytime (n : ℕ) :
    ComputableTidilyInPolyTime (appendFixed n) encBits encBits := by
  fun_prop [appendFixed]

attribute [irreducible] appendFixed

-- An inapplicable side condition must not hide a later, unconditional certificate.
example : ComputableTidilyInPolyTime (appendFixed 1) encBits encBits := by polytime

-- A captured parameter and a value invariant prove efficiency and the computed result together.
example : ComputableTidilyInPolyTime
      (fun n : ℕ => (fun total => total + n)^[n] 0) encUnary encUnary ∧
    ∀ n : ℕ, (fun total => total + n)^[n] 0 = n * n := by
  apply ComputableTidilyInPolyTime.iterateWith_spec (par := id)
    (count := id) (init := fun _ => 0) (step := fun n total => total + n)
    (invariant := fun n i total => total = i * n) (size := fun n => n * n)
  · polytime
  · polytime
  · polytime
  · polytime
  · simp
  · intro n i total _ htotal
    simp [htotal, Nat.add_mul]
  · exact ComputableTidilyInPolyTime.polyBounded (by polytime)
  · intro n i total hi htotal
    simpa [htotal] using Nat.mul_le_mul_right n hi

-- Prefix invariants certify both a fold's size and its postcondition.
example : ComputableTidilyInPolyTime
      (fun word : List Bool => word.foldl (fun reversed bit => bit :: reversed) [])
      encBits encBits ∧
    ∀ word : List Bool, word.foldl (fun reversed bit => bit :: reversed) [] = word.reverse := by
  apply ComputableTidilyInPolyTime.foldl_spec (encA := encBool) (encL := encBits)
    (invariant := fun _ consumed state => state = consumed.reverse) (size := List.length)
  · polytime
  · polytime
  · polytime
  · simp
  · intro word consumed state bit _ hstate
    simp [hstate]
  · exact ComputableTidilyInPolyTime.polyBounded (by polytime)
  · intro word consumed state hprefix hstate
    simpa [hstate] using hprefix.length_le

-- Optional lookup works at computed unary indices with both raw and framed bit encodings.
example : ComputableTidilyInPolyTime (fun p : List Bool × ℕ => p.1[p.2]?)
    (encPair encBits encUnary) (encOption encBool) := by fun_prop

example : ComputableTidilyInPolyTime (fun p : List Bool × ℕ => p.1[p.2]?)
    (encPair (encList encBool) encUnary) (encOption encBool) := by fun_prop

-- The same functional operation applies to non-bit element encodings.
example : ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => p.1[p.2]?)
    (encPair (encList encUnary) encUnary) (encOption encUnary) := by fun_prop

-- Equivalent lookup spellings compose with a default without exposing the option encoding.
example : ComputableTidilyInPolyTime (fun p : List Bool × ℕ => (p.1[p.2]?).getD false)
    (encPair encBits encUnary) encBool := by fun_prop

example : ComputableTidilyInPolyTime (fun p : List Bool × ℕ => (p.1[p.2]?).getD false)
    (encPair encBits encUnary) encBool := by polytime

example : ComputableTidilyInPolyTime (fun p : List Bool × ℕ => p.1.getD p.2 false)
    (encPair encBits encUnary) encBool := by polytime

-- Abstract list encodings retain the same default-lookup interface after tactic normalization.
example {α : Type} (encA : α ↪ List Bool) (encL : List α ↪ List Bool)
    [ListEncoding encA encL] [SizedListEncoding encA encL] (fallback : α) :
    ComputableTidilyInPolyTime (fun p : List α × ℕ => p.1.getD p.2 fallback)
      (encPair encL encUnary) encA := by polytime

-- Optional operations require no inhabitant of the element type, even with a custom encoding.
example {α : Type} (encA : α ↪ List Bool) (encL : List α ↪ List Bool)
    [ListEncoding encA encL] [SizedListEncoding encA encL] :
    ComputableTidilyInPolyTime (fun p : List α × ℕ => p.1[p.2]?)
      (encPair encL encUnary) (encOption encA) := by fun_prop

example {α : Type} (encA : α ↪ List Bool) (encL : List α ↪ List Bool)
    [ListEncoding encA encL] :
    ComputableTidilyInPolyTime (List.head? (α := α)) encL (encOption encA) := by fun_prop

-- Empty element types still have the empty list as a computational input.
example : ComputableTidilyInPolyTime (List.head? (α := Fin 0))
    (encList (encFinEnum (Fin 0))) (encOption (encFinEnum (Fin 0))) := by fun_prop

-- Nested range/map, Boolean folds and majority share the computation calculus.
example (call : List Bool → ℕ → ℕ → Bool)
    (hcall : ComputableTidilyInPolyTime
      (fun p : (List Bool × ℕ) × ℕ => call p.1.1 p.1.2 p.2)
      (encPair (encPair encBits encUnary) encUnary) encBool) :
    ComputableTidilyInPolyTime (fun p : (List Bool × ℕ) × ℕ =>
      Cslib.BitString.listStrictMajority ((List.range p.1.2).map fun i =>
        ((List.range p.2).map (call p.1.1 i)).foldl Bool.xor false))
      (encPair (encPair encBits encUnary) encUnary) encBool := by
  polytime

-- The input representation and the runtime dimensions are arbitrary certified data.
example {α : Type} (input : α ↪ List Bool) (N C : α → ℕ)
    (call : α → ℕ → ℕ → Bool)
    (hN : ComputableTidilyInPolyTime N input encUnary)
    (hC : ComputableTidilyInPolyTime C input encUnary)
    (hcall : ComputableTidilyInPolyTime
      (fun p : (α × ℕ) × ℕ => call p.1.1 p.1.2 p.2)
      (encPair (encPair input encUnary) encUnary) encBool) :
    ComputableTidilyInPolyTime (fun a =>
      Cslib.BitString.listStrictMajority ((List.range (N a)).map fun i =>
        ((List.range (C a)).map (call a i)).foldl Bool.xor false)) input encBool := by
  polytime

-- Uncurried List.map spelling supplies the same computation without definition unfolding.
example {α : Type} (input : α ↪ List Bool) (N C : α → ℕ)
    (call : α → ℕ → ℕ → Bool)
    (hN : ComputableTidilyInPolyTime N input encUnary)
    (hC : ComputableTidilyInPolyTime C input encUnary)
    (hcall : ComputableTidilyInPolyTime
      (fun p : (α × ℕ) × ℕ => call p.1.1 p.1.2 p.2)
      (encPair (encPair input encUnary) encUnary) encBool) :
    ComputableTidilyInPolyTime (fun a => Cslib.BitString.listStrictMajority
      (List.map (fun i => List.foldl Bool.xor false
        (List.map (fun j => call a i j) (List.range (C a)))) (List.range (N a))))
      input encBool := by
  polytime

-- Infinite runtime inputs still require the joint callback certificate.
example (_call : List Bool → ℕ → ℕ → Bool) : True := by
  fail_if_success
    have : ComputableTidilyInPolyTime (fun p : (List Bool × ℕ) × ℕ =>
      Cslib.BitString.listStrictMajority ((List.range p.1.2).map fun i =>
        ((List.range p.2).map (_call p.1.1 i)).foldl Bool.xor false))
      (encPair (encPair encBits encUnary) encUnary) encBool := by polytime
  trivial

-- A callback certificate does not make an arbitrary runtime loop count computable.
example (_C : List Bool → ℕ) (call : List Bool → ℕ → ℕ → Bool)
    (_hcall : ComputableTidilyInPolyTime
      (fun p : (List Bool × ℕ) × ℕ => call p.1.1 p.1.2 p.2)
      (encPair (encPair encBits encUnary) encUnary) encBool) : True := by
  fail_if_success
    have : ComputableTidilyInPolyTime (fun p : List Bool × ℕ =>
      Cslib.BitString.listStrictMajority ((List.range p.2).map fun i =>
        ((List.range (_C p.1)).map (call p.1 i)).foldl Bool.xor false))
      (encPair encBits encUnary) encBool := by polytime
  trivial

-- The legacy right-fold spelling uses the existing exact fold/reverse identity.
example {α : Type} (input : α ↪ List Bool) (N C : α → ℕ)
    (call : α → ℕ → ℕ → Bool)
    (hN : ComputableTidilyInPolyTime N input encUnary)
    (hC : ComputableTidilyInPolyTime C input encUnary)
    (hcall : ComputableTidilyInPolyTime
      (fun p : (α × ℕ) × ℕ => call p.1.1 p.1.2 p.2)
      (encPair (encPair input encUnary) encUnary) encBool) :
    ComputableTidilyInPolyTime (fun a =>
      Cslib.BitString.listStrictMajority ((List.range (N a)).map fun i =>
        ((List.range (C a)).map (call a i)).foldr Bool.xor false)) input encBool := by
  let : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩
  let : Std.Associative Bool.xor := ⟨Bool.xor_assoc⟩
  simp only [← List.foldl_eq_foldr (f := Bool.xor)]
  polytime

-- Every parameter below is runtime data, including L, C and the source word.
example {α : Type} (input : α ↪ List Bool) (L N C : α → ℕ)
    (source : α → List Bool) (call : ℕ → ℕ → List Bool → ℕ → ℕ → Bool)
    (hL : ComputableTidilyInPolyTime L input encUnary)
    (hN : ComputableTidilyInPolyTime N input encUnary)
    (hC : ComputableTidilyInPolyTime C input encUnary)
    (hsource : ComputableTidilyInPolyTime source input encBits)
    (hcall : ComputableTidilyInPolyTime
      (fun p : (((ℕ × ℕ) × List Bool) × ℕ) × ℕ =>
        call p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair (encPair encUnary encUnary) encBits) encUnary) encUnary)
      encBool) :
    ComputableTidilyInPolyTime (fun a =>
      Cslib.BitString.listStrictMajority ((List.range (N a)).map fun i =>
        ((List.range (C a)).map (call (L a) (C a) (source a) i)).foldl Bool.xor false))
      input encBool := by
  have prepared : ComputableTidilyInPolyTime
      (fun p : (α × ℕ) × ℕ => call (L p.1.1) (C p.1.1) (source p.1.1) p.1.2 p.2)
      (encPair (encPair input encUnary) encUnary) encBool := by
    exact hcall.comp (g := fun p : (α × ℕ) × ℕ =>
      ((((L p.1.1, C p.1.1), source p.1.1), p.1.2), p.2)) (by fun_prop)
  polytime

-- Membership and its negation, written as on paper, need no rewriting into Boolean operations.
example : ComputableInPolyTime (fun l : List ℕ => decide (3 ∈ l)) (encList encNat) encBool := by
  polytime

example : ComputableInPolyTime (fun p : List ℕ × List ℕ => p.1.filter fun x => x ∉ p.2)
    (encPair (encList encNat) (encList encNat)) (encList encNat) := by
  polytime

-- The complement of an edge list on its vertices, as a reduction map writes it.
example : ComputableInPolyTime
    (fun G : List ℕ × List (ℕ × ℕ) => G.1.flatMap fun u =>
      (G.1.filter fun v => decide (u ≠ v ∧ (u, v) ∉ G.2 ∧ (v, u) ∉ G.2)).map fun v => (u, v))
    (encPair (encList encNat) (encList (encPair encNat encNat)))
    (encList (encPair encNat encNat)) := by
  polytime

-- Binary list length is reached from `Complexity.Tactic.PolyTime`.
example : ComputableInPolyTime (fun l : List ℕ => l.length)
    (encList encNat) encNat := by
  polytime

example : ComputableInPolyTime (fun l : List ℕ => l.length)
    (encList encNat) encNat := by
  fun_prop

example : ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.length)
    (encPair (encList encNat) encNat) encNat := by
  fun_prop

end ComplexityTests.PolyTimeTactic
