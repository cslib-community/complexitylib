/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Computability.PolyTime.CNF.GreedyParityContext
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

public section

open Finset Cslib.BitString Cslib.GenericRAM Cslib.Logic.PL Cslib.Logic.PL.CNF Turing.MultiTapeTM

namespace ComplexityTests.CNFGreedyParityContext

-- The first context component chooses a unit clause or a tautology; the remaining bits are
-- retained runtime data. The same native counter handles both choices and all payload lengths.
private abbrev Context := Bool × List Bool
private def encContext : Context ↪ List Bool := encPair encBool encBits

private def count (p : Context × List (List Bool)) : ℕ :=
  if p.1.1 then 2 else if p.2.flatten.count true = 0 then 2 else 1

private theorem count_polyTime :
    ComputableInPolyTime count (encPair encContext (encList encBits)) encNat := by
  refine .of_tidy ?_
  unfold count encContext
  fun_prop

private noncomputable def cert := NativeCertificate.ofPolyTime count_polyTime

private def unitContext : Context := (false, [])
private def tautContext : Context := (true, [true, false])

-- Context changes actual execution, including the final count. Enumeration ties still retain
-- the first row after the unit clause has been enforced.
example :
    selectBestTestRow (fun r => count (unitContext, r)) 1 1 [] = [true] ∧
    selectBestTestRow (fun r => count (tautContext, r)) 1 1 [] = [false] ∧
    greedyParityRows (fun r => count (unitContext, r)) 1 1 1 [] =
      [[true], [false], [false]] ∧
    greedyParityRows (fun r => count (tautContext, r)) 1 1 1 [] =
      [[false], [false], [false]] ∧
    (count (unitContext, greedyParityRows (fun r => count (unitContext, r)) 1 1 1 []) = 1 ∧
      count (tautContext, greedyParityRows (fun r => count (tautContext, r)) 1 1 1 []) = 2) := by
  decide

-- The joint runtime encoding charges every captured payload bit even with no outer rounds.
theorem context_encoding_charges_payload (payload : List Bool) :
    (GreedyContext.encGreedyInput (encPair encBool encBits)
      ((false, payload), 0, 1, 1, [])).length =
    (GreedyContext.encGreedyInput (encPair encBool encBits)
      ((false, []), 0, 1, 1, [])).length + 2 * payload.length := by
  simp only [GreedyContext.encGreedyInput, length_encPair, encBits_apply, List.length_nil]
  omega

-- Arbitrarily long captured payloads remain in the encoded joint input even at zero rounds, and
-- the empty tuple space has a zero-row fallback while P = 0 has one empty tuple.
example :
    (GreedyContext.encGreedyInput encContext
      ((false, List.replicate 11 true), 0, 1, 1, [])).length =
      (GreedyContext.encGreedyInput encContext (unitContext, 0, 1, 1, [])).length + 22 ∧
    greedyParityRows (fun r => count ((false, List.replicate 11 true), r)) 0 1 1 [[true]] =
      [[true]] ∧
    selectBestTestRow (fun r => count (unitContext, r)) 0 1 [[true]] = [] ∧
    selectBestTestRow (fun r => count (tautContext, r)) 3 0 [] = [false, false, false] := by
  decide

-- This is one joint-input certificate, not a separate certificate selected for each context.
example : ComputableInPolySpace
    (fun a : Context × ℕ × ℕ × ℕ × List (List Bool) =>
      greedyParityRows (fun r => count (a.1, r)) a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    (GreedyContext.encGreedyInput encContext) (encList encBits) :=
  GreedyContext.computableInPolySpace_greedy cert
    (NativeCertificate.ofPolyTime_isPolynomial count_polyTime).2

private def formula (c : Context) : CNF (Fin 1) :=
  if c.1 then [[(0, true), (0, false)]] else [[(0, true)]]

-- A finite bounded-candidate agreement check, including all retained-row prefixes of this run.
private theorem count_agrees (c : Context) (rows : List (List Bool))
    (hwidth : ∀ r ∈ rows, r.length = (formula c).length) (hlen : rows.length ≤ 3) :
    count (c, rows) = numPassing (formula c).violations (rows.map (ofList (formula c).length)) := by
  rcases c with ⟨b, payload⟩
  cases b <;> simp only [formula, Bool.false_eq_true, ↓reduceIte, List.length_cons,
    List.length_nil, Nat.zero_add] at hwidth ⊢
  all_goals
    have hrow (r : List Bool) (hr : r ∈ rows) : r = [false] ∨ r = [true] := by
      have h := hwidth r hr
      rcases r with _ | ⟨x, r⟩
      · simp only [List.length_nil] at h; omega
      · have hrnil : r = [] := List.eq_nil_of_length_eq_zero (by simpa using Nat.succ.inj h)
        subst r
        cases x <;> simp
    clear hwidth
    rcases rows with _ | ⟨r₁, rows⟩
    · dsimp only [count]; rfl
    · rcases hrow r₁ (by simp) with rfl | rfl
      all_goals
        rcases rows with _ | ⟨r₂, rows⟩
        · dsimp only [count]; rfl
        · rcases hrow r₂ (by simp) with rfl | rfl
          all_goals
            rcases rows with _ | ⟨r₃, rows⟩
            · dsimp only [count]; rfl
            · rcases hrow r₃ (by simp) with rfl | rfl
              all_goals
                have : rows = [] := List.eq_nil_of_length_eq_zero (by
                  simp only [List.length_cons] at hlen
                  omega)
                subst rows
                dsimp only [count]
                rfl

private theorem support (c : Context) (σ : Fin 1 → Bool) (heval : (formula c).eval σ = false) :
    (formula c).length ≤ 1 * weight ((formula c).violations σ) := by
  have hne : (formula c).violations σ ≠ 0 := fun h =>
    Bool.false_ne_true (heval.symm.trans ((CNF.violations_eq_zero_iff _ _).mp h))
  have hw : weight ((formula c).violations σ) ≠ 0 := by
    rw [weight_eq_hammingNorm, ne_eq, hammingNorm_eq_zero]
    exact hne
  have hlen : (formula c).length = 1 := by unfold formula; split <;> rfl
  omega

-- Pointwise correctness is reused on both formulas, with the same executable counter.
example (c : Context) :
    count (c, greedyParityRows (fun r => count (c, r)) 1 (formula c).length 1 []) =
      #{σ : Fin 1 → Bool | (formula c).eval σ = true} := by
  exact GreedyContext.count_greedy_eq_card_sat count c (formula c) (by decide) (by decide)
    (fun _ h => nomatch h) (fun rows hw hl _ => count_agrees c rows hw (by simpa using hl))
    (fun σ _ he => support c σ he)

-- Counterexamples when the counter is mismatched, `P = 0`, or `|V| = 0`.
example :
    (let bad := fun _ : Context × List (List Bool) => 9;
      bad (unitContext, greedyParityRows (fun r => bad (unitContext, r)) 1 1 1 []) = 9 ∧
        #{σ : Fin 1 → Bool | (formula unitContext).eval σ = true} = 1) ∧
    (count (unitContext, greedyParityRows (fun r => count (unitContext, r)) 1 1 0 []) = 2 ∧
      #{σ : Fin 1 → Bool | (formula unitContext).eval σ = true} = 1) ∧
    (let φ : CNF (Fin 0) := [[]];
      let ctr := fun rows : List (List Bool) =>
        numPassing φ.violations (rows.map (ofList φ.length));
      ctr (greedyParityRows ctr 0 1 1 []) = 1 ∧
        #{σ : Fin 0 → Bool | φ.eval σ = true} = 0) := by
  decide

end ComplexityTests.CNFGreedyParityContext
