/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.IndexedSignature
public import Complexity.Probability.BitString
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Tactic.PolyTime

/-!
# Seeded deterministic algorithms of an indexed signature scheme

Stateless tree signatures ([BonehShoup2023], Section 14.6.3) derive the key pair of every tree
node, and every signature of an internal node, from pseudorandom coins, so that repeated
invocations of the signer reproduce the same keys and signatures. This needs the key generation
and signing algorithms of the underlying indexed scheme as deterministic functions of explicit
coins. `IndexedSignatureScheme.Seeded` packages such evaluators with their coin budgets: every coin
word yields a supported result, and uniform coins of at least the budget reproduce the algorithm's
distribution exactly. `IndexedSignatureScheme.seeded` provides one for every indexed scheme from the
strict-PPT certificates (`IsPPTOn.exists_total_seeded_evaluator`); a scheme with naturally
deterministic algorithms may supply a simpler one.

## Main definitions

* `Cslib.Crypto.IndexedSignatureScheme.Seeded`: seeded key generation and signing with budgets.
* `Cslib.Crypto.IndexedSignatureScheme.seeded`: the seeded algorithms of any indexed scheme.

## Main results

* `Cslib.Crypto.IndexedSignatureScheme.exists_keyGenWith`,
  `Cslib.Crypto.IndexedSignatureScheme.exists_signWith`: seeded evaluators with polynomial-time
  budgets exist for every indexed scheme.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.6.2, "Generating internal keys using a PRF", and Exercise 13.6.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace IndexedSignatureScheme

/-- Deterministic key generation and signing of the indexed scheme `S` on explicit coins. Every
coin word gives a supported result, and uniform coins of at least the budget's length reproduce
the algorithm's law exactly. -/
structure Seeded (S : IndexedSignatureScheme) where
  /-- Key generation at parameter `n` from the coin word. -/
  keyGenWith : ℕ → List Bool → List Bool × List Bool
  /-- The number of coins key generation at parameter `n` needs. -/
  keyGenBudget : ℕ → ℕ
  /-- Signing `msg` at index `u` under `sk` from the coin word. -/
  signWith : List Bool → ℕ → List Bool → List Bool → List Bool
  /-- The number of coins signing `msg` at index `u` under `sk` needs. -/
  signBudget : List Bool → ℕ → List Bool → ℕ
  keyGenWith_polyTime : ComputableInPolyTime (fun p : ℕ × List Bool => keyGenWith p.1 p.2)
    (encPair encUnary encBits) (encPair encBits encBits)
  keyGenBudget_polyTime : ComputableInPolyTime keyGenBudget encUnary encUnary
  keyGenWith_mem_support : ∀ n coins, keyGenWith n coins ∈ (ProbComp.eval (S.keyGen n)).support
  eval_keyGen : ∀ n length, keyGenBudget n ≤ length →
    ProbComp.eval (S.keyGen n) = (BitString.uniformList length).map (keyGenWith n)
  signWith_polyTime : ComputableInPolyTime
    (fun p : (List Bool × ℕ × List Bool) × List Bool => signWith p.1.1 p.1.2.1 p.1.2.2 p.2)
    (encPair (encPair encBits (encPair encUnary encBits)) encBits) encBits
  signBudget_polyTime : ComputableInPolyTime
    (fun p : List Bool × ℕ × List Bool => signBudget p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encUnary encBits)) encUnary
  signWith_mem_support : ∀ sk u msg coins,
    signWith sk u msg coins ∈ (ProbComp.eval (S.sign sk u msg)).support
  eval_sign : ∀ sk u msg length, signBudget sk u msg ≤ length →
    ProbComp.eval (S.sign sk u msg) = (BitString.uniformList length).map (signWith sk u msg)

attribute [program_certificate] Seeded.keyGenWith_polyTime Seeded.keyGenBudget_polyTime
  Seeded.signWith_polyTime Seeded.signBudget_polyTime

/-- The coin budget `c * (size + 1) ^ d` of a seeded evaluator is polynomial time in the encoded
input. -/
theorem computableInPolyTime_coinBudget {α : Type} (enc : α ↪ List Bool) (c d : ℕ) :
    ComputableInPolyTime (fun a => c * ((enc a).length + 1) ^ d) enc encUnary := by
  have hlen : ComputableInPolyTime (fun a => (enc a).length) enc encUnary :=
    .of_tidy ((ComputableTidilyInPolyTime.length encBool).comp
      (ComputableTidilyInPolyTime.encode enc))
  polytime

/-- Every indexed scheme has seeded key generation with a polynomial-time budget. -/
theorem exists_keyGenWith (S : IndexedSignatureScheme) :
    ∃ (keyGenWith : ℕ → List Bool → List Bool × List Bool) (budget : ℕ → ℕ),
      ComputableInPolyTime (fun p : ℕ × List Bool => keyGenWith p.1 p.2)
        (encPair encUnary encBits) (encPair encBits encBits) ∧
      ComputableInPolyTime budget encUnary encUnary ∧
      (∀ n coins, keyGenWith n coins ∈ (ProbComp.eval (S.keyGen n)).support) ∧
      ∀ n length, budget n ≤ length →
        ProbComp.eval (S.keyGen n) = (BitString.uniformList length).map (keyGenWith n) := by
  obtain ⟨c, d, evaluate, hpoly, hsupport, hlaw⟩ :=
    IsPPTOn.exists_total_seeded_evaluator S.keyGen_ppt
  exact ⟨evaluate, fun n => c * ((encUnary n).length + 1) ^ d, .of_tidy hpoly,
    computableInPolyTime_coinBudget encUnary c d, hsupport, hlaw⟩

/-- Every indexed scheme has seeded signing with a polynomial-time budget. -/
theorem exists_signWith (S : IndexedSignatureScheme) :
    ∃ (signWith : List Bool × ℕ × List Bool → List Bool → List Bool)
      (budget : List Bool × ℕ × List Bool → ℕ),
      ComputableInPolyTime (fun p : (List Bool × ℕ × List Bool) × List Bool => signWith p.1 p.2)
        (encPair (encPair encBits (encPair encUnary encBits)) encBits) encBits ∧
      ComputableInPolyTime budget (encPair encBits (encPair encUnary encBits)) encUnary ∧
      (∀ a coins, signWith a coins ∈ (ProbComp.eval (S.sign a.1 a.2.1 a.2.2)).support) ∧
      ∀ a length, budget a ≤ length →
        ProbComp.eval (S.sign a.1 a.2.1 a.2.2) =
          (BitString.uniformList length).map (signWith a) := by
  obtain ⟨c, d, evaluate, hpoly, hsupport, hlaw⟩ :=
    IsPPTOn.exists_total_seeded_evaluator S.sign_ppt
  exact ⟨evaluate, fun a => c * ((encPair encBits (encPair encUnary encBits) a).length + 1) ^ d,
    .of_tidy hpoly, computableInPolyTime_coinBudget _ c d, hsupport, hlaw⟩

/-- The seeded algorithms of any indexed scheme, read off its strict-PPT certificates. -/
noncomputable def seeded (S : IndexedSignatureScheme) : S.Seeded :=
  let hk := S.exists_keyGenWith
  let hs := S.exists_signWith
  { keyGenWith := hk.choose
    keyGenBudget := hk.choose_spec.choose
    signWith := fun sk u msg coins => hs.choose (sk, u, msg) coins
    signBudget := fun sk u msg => hs.choose_spec.choose (sk, u, msg)
    keyGenWith_polyTime := hk.choose_spec.choose_spec.1
    keyGenBudget_polyTime := hk.choose_spec.choose_spec.2.1
    keyGenWith_mem_support := hk.choose_spec.choose_spec.2.2.1
    eval_keyGen := hk.choose_spec.choose_spec.2.2.2
    signWith_polyTime := hs.choose_spec.choose_spec.1
    signBudget_polyTime := hs.choose_spec.choose_spec.2.1
    signWith_mem_support := fun sk u msg coins =>
      hs.choose_spec.choose_spec.2.2.1 (sk, u, msg) coins
    eval_sign := fun sk u msg length h =>
      hs.choose_spec.choose_spec.2.2.2 (sk, u, msg) length h }

end IndexedSignatureScheme

end Cslib.Crypto
