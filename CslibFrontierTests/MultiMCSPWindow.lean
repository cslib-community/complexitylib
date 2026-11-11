/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.MultiNPHard.WindowCount
import Cslib.Computability.Circuit.Boolean.Basic
import Mathlib.Tactic.FinCases

/-!
# Tests for window templates

Concrete instances of `CslibFrontier.Computability.MCSP.MultiNPHard.Window` and `WindowCount`:

1. The layout: two inputs and one window give `2 + 1 + 8 + 4 = 15` gates, numbered as stated.
2. Gate values: a prefix conjunction, a window gate and the window identity, on concrete inputs.
3. Locality: changing `T` outside window `i` leaves the gates of window `i` unchanged.
4. Exact cost and completeness, over the constant-free basis and cslib's basis.
5. Both directions for the set system `{{0}, {1}}` on two elements, lifted to `2^6` inputs: the
   cover by both sets gives cost at most the count plus one for every table, while no single set
   covers, so at most a third of the tables cost at most the count plus zero.
6. Soundness at `ℓ = 1`: the singletons `{0}, {1}, {2}` lifted to `2^9` inputs, where no two sets
   cover and `p (5ℓ + 5) = 90 ≤ 170 = 2^9 / 3`.
-/

namespace CslibFrontierTests.MultiMCSPWindow

open Cslib Cslib.Circuits Cslib.MultiMCSP.Window Finset

/-! ### Layout -/

example : gateCount 2 1 = 15 := by
  rw [gateCount_eq]
  norm_num

example : (Gate.equivFin 2 1 (.window 0 3) : ℕ) = 14 := by
  rw [Gate.val_equivFin_window]
  rfl

example : (Gate.equivFin 2 1 (.grid 1 1) : ℕ) = 6 := by
  rw [Gate.val_equivFin_grid]
  rfl

/-! ### Gate values -/

/-- Two windows on four inputs: the even inputs and the odd inputs. -/
private def A : Fin 2 → Finset (Fin (2 ^ 2)) := ![{0, 2}, {1, 3}]

/-- The table accepting the inputs `1` and `2`. -/
private def T : Fin (2 ^ 2) → Bool := ![false, true, true, false]

/-- The prefix conjunction `grid 2 1` recognizes the input `2 = 0b10`, read least significant bit
first. -/
example : value A T (.grid 2 1) ![false, true] = true := by
  rw [value_grid]
  decide

example : value A T (.grid 2 1) ![true, true] = false := by
  rw [value_grid]
  decide

/-- The input `2` is in window `0`, at most `3` and accepted by `T`. -/
example : value A T (.window 0 3) ((BitString.equivFin 2).symm 2) = true := by
  rw [value_window, Equiv.apply_symm_apply]
  decide

/-- The input `2` is not at most `1`. -/
example : value A T (.window 0 1) ((BitString.equivFin 2).symm 2) = false := by
  rw [value_window, Equiv.apply_symm_apply]
  decide

/-- The input `1` is accepted by `T` but lies outside window `0`. -/
example : value A T (.window 0 (lastIdx 2)) ((BitString.equivFin 2).symm 1) = false := by
  rw [value_window_last, Equiv.apply_symm_apply]
  decide

/-! ### Locality -/

/-- Flipping `T` at the odd inputs does not change the gates of the even window. -/
example (κ : Gate 2 2) (hκ : κ.set = some 0) :
    value A T κ = value A ![false, false, true, true] κ := by
  refine value_congr A κ fun i hi y hy => ?_
  rw [hκ, Option.some_inj] at hi
  subst hi
  revert y
  decide

/-! ### Exact cost and completeness -/

example : ecomplexity Boolean.DeMorgan.interpretation (template A T) =
    #(nonInputComponents (template A T)) :=
  ecomplexity_template A T

/-- The two windows cover the four inputs, so `T` costs one OR gate beyond the template. -/
example : ecomplexity Boolean.interpretation
      (fun x => Fin.append (template A T x) (single (tableFun T) x)) ≤
      ((#(nonInputComponents (template A T)) + 1 : ℕ) : ℕ∞) :=
  ecomplexity_append_le A T univ (by decide)

/-! ### Both directions for lifted windows -/

/-- The set system `{{0}, {1}}` on the residues modulo two. -/
private def S : Fin 2 → Finset ℕ := ![{0}, {1}]

example : lift 2 2 (S 0) = {0, 2} := by
  decide

/-- Completeness: both sets cover the residues, so every table costs at most the count plus one. -/
example (T : Fin (2 ^ 6) → Bool) :
    ecomplexity Boolean.DeMorgan.interpretation
      (fun x => Fin.append (template (fun i => lift 6 2 (S i)) T x) (single (tableFun T) x)) ≤
      ((#(nonInputComponents (template (fun i => lift 6 2 (S i)) T)) + 1 : ℕ) : ℕ∞) :=
  ecomplexity_append_le _ T univ (lift_cover (by norm_num) S univ (by decide))

/-- Soundness: no single set covers the residues, so at most a third of the tables cost at most
the count plus zero. -/
example : 3 * #{T : Fin (2 ^ 6) → Bool |
      ecomplexity Boolean.DeMorgan.interpretation
        (fun x => Fin.append (template (fun i => lift 6 2 (S i)) T x) (single (tableFun T) x)) ≤
        ((#(nonInputComponents (template (fun i => lift 6 2 (S i)) T)) + 0 : ℕ) : ℕ∞)} ≤
      2 ^ (2 ^ 6) := by
  classical
  convert three_mul_card_cheap_lift_le (I := Boolean.DeMorgan.interpretation) (p := 6) (N := 2)
    (by norm_num) S 0 (fun B hB => ?_) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- A set of at most one of the two sets misses some residue.
  rcases card_le_one_iff_subset_singleton.mp hB with ⟨i, hi⟩
  refine ⟨1 - (i : ℕ), by omega, fun j hj => ?_⟩
  rw [mem_singleton.mp (hi hj)]
  fin_cases i <;> decide

/-- The singletons `{0}, {1}, {2}` on the residues modulo three. -/
private def S₃ : Fin 3 → Finset ℕ := ![{0}, {1}, {2}]

/-- Soundness at `ℓ = 1`: no two singletons cover the three residues, so at most a third of the
tables cost at most the count plus one. -/
example : 3 * #{T : Fin (2 ^ 9) → Bool |
      ecomplexity Boolean.DeMorgan.interpretation
        (fun x => Fin.append (template (fun i => lift 9 3 (S₃ i)) T x) (single (tableFun T) x)) ≤
        ((#(nonInputComponents (template (fun i => lift 9 3 (S₃ i)) T)) + 1 : ℕ) : ℕ∞)} ≤
      2 ^ (2 ^ 9) :=
  three_mul_card_cheap_lift_le (I := Boolean.DeMorgan.interpretation) (by norm_num) S₃ 1
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end CslibFrontierTests.MultiMCSPWindow
