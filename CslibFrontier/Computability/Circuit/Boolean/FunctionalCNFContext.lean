/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.FunctionalCNF
import Mathlib.Logic.Equiv.Prod

/-!
# Functional CNF counts with retained free context

An unchanged context can constrain original circuit inputs without introducing extra gate traces.
Apply the existing unique-extension count separately in each context fiber. Upper domination uses
this with its private-neighbor mark word, keeping the cardinality circuit on selection bits only.

## Main results

* `count_extensions_context`: unique gate extensions preserve predicates coupling original inputs
  to arbitrary finite context.
* `count_extensions_appended`: the context may follow all gate wires in the declared assignment.
-/

public section

namespace Cslib.Circuits.Boolean.FunctionalCNF

open Cslib.Logic.PL

open Classical in
/-- Count original input/context pairs exactly once, retaining arbitrary context constraints. -/
theorem count_extensions_context {C : Type} [Fintype C] {n m : ℕ}
    (c : Circuit signature n m) (bs : Fin m → Bool)
    (P : C → (Fin n → Bool) → Prop) :
    Fintype.card {p : C × (Fin (n + c.size) → Bool) //
      (write (ofCircuit c bs)).eval (Function.extend Fin.val p.2 (fun _ => false)) = true ∧
        P p.1 (fun i => p.2 (Fin.castAdd c.size i))} =
      Fintype.card {p : C × (Fin n → Bool) // c.eval interpretation p.2 = bs ∧ P p.1 p.2} := by
  calc
    _ = Fintype.card (Σ ctx : C, {y : Fin (n + c.size) → Bool //
        (write (ofCircuit c bs)).eval (Function.extend Fin.val y (fun _ => false)) = true ∧
          P ctx (fun i => y (Fin.castAdd c.size i))}) :=
      Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype _)
    _ = Fintype.card (Σ ctx : C, {x : Fin n → Bool //
        c.eval interpretation x = bs ∧ P ctx x}) := by
      rw [Fintype.card_sigma, Fintype.card_sigma]
      exact Finset.sum_congr rfl fun ctx _ => count_extensions c bs (P ctx)
    _ = _ := (Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype _)).symm

open Classical in
/-- A free Boolean context can follow the circuit's gate wires in the actual declared assignment.
Splitting that declared word and applying the existing context theorem preserves counts. -/
theorem count_extensions_appended {n m : ℕ} (c : Circuit signature n m) (bs : Fin m → Bool)
    (r : ℕ) (P : (Fin r → Bool) → (Fin n → Bool) → Prop) :
    Nat.card {y : Fin ((n + c.size) + r) → Bool //
      (write (ofCircuit c bs)).eval (Function.extend Fin.val
        (fun j => y (Fin.castAdd r j)) (fun _ => false)) = true ∧
      P (fun w => y (Fin.natAdd (n + c.size) w))
        (fun u => y (Fin.castAdd r (Fin.castAdd c.size u)))} =
      Nat.card {p : (Fin r → Bool) × (Fin n → Bool) //
        c.eval interpretation p.2 = bs ∧ P p.1 p.2} := by
  let e : (Fin ((n + c.size) + r) → Bool) ≃
      (Fin r → Bool) × (Fin (n + c.size) → Bool) :=
    ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow (Fin (n + c.size)) (Fin r) Bool)).trans
        (Equiv.prodComm _ _)
  calc
    _ = Nat.card {p : (Fin r → Bool) × (Fin (n + c.size) → Bool) //
        (write (ofCircuit c bs)).eval (Function.extend Fin.val p.2 (fun _ => false)) = true ∧
          P p.1 (fun u => p.2 (Fin.castAdd c.size u))} :=
      Nat.card_congr (e.subtypeEquiv fun _ => Iff.rfl)
    _ = _ := by
      simpa only [← Nat.card_eq_fintype_card] using count_extensions_context c bs P

end Cslib.Circuits.Boolean.FunctionalCNF
