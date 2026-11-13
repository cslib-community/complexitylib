/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Permanent.ZeroOne.Basic
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks
public import Mathlib.Data.ZMod.Basic

/-!
# From integer tables to 0/1 tables

The first step of Goldreich's proof of Proposition 6.22 [Goldreich2007Draft]: an integer table `A`
is reduced modulo `Q = 2 · n! · S ^ n + 1` (`permanentModulus`) to a table of natural numbers
(`reduceIntTable`), whose permanent agrees with that of `A` modulo `Q`. Since
`|perm A| ≤ n! · S ^ n < Q / 2`, the permanent of `A` is the representative of that residue in
`(-Q/2, Q/2)` (`recoverPermanent`). Composed with the nonnegative step `natTableToZeroOne`, the
integer permanent is recovered from a 0/1 permanent (`intPermanent_eq_recoverPermanent`).

Goldreich takes `S` to be the largest absolute value of an entry; here `S` is the sum of the
absolute values of the entries of the `n × n` square read by `tableMatrix`, which is at least as
large, so the same bound holds and `Q` still has polynomially many bits.

## Main definitions

* `Cslib.Complexity.permanentModulus`, `Cslib.Complexity.reduceIntTable`,
  `Cslib.Complexity.recoverPermanent`.

## Main results

* `Cslib.Complexity.abs_intPermanent_le`: `|perm A| ≤ n! · S ^ n`.
* `Cslib.Complexity.intPermanent_eq_recoverPermanent`: the integer permanent is recovered from
  the 0/1 permanent of `natTableToZeroOne (reduceIntTable A)`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
-/

@[expose] public section

namespace Cslib.Complexity

/-- Entry `(i, j)` of an integer table, `0` when missing. -/
def intTableEntry (A : List (List ℤ)) (i j : ℕ) : ℤ :=
  (A.getD i []).getD j 0

/-- The sum of the absolute values of the entries of the `n × n` square of an integer table. -/
def intTableAbsSum (A : List (List ℤ)) : ℕ :=
  ((List.range A.length).flatMap fun i =>
    (List.range A.length).map fun j => (intTableEntry A i j).natAbs).sum

/-- The modulus `Q = 2 · n! · S ^ n + 1`, more than twice any possible absolute value of the
permanent. -/
def permanentModulus (A : List (List ℤ)) : ℕ :=
  2 * A.length.factorial * intTableAbsSum A ^ A.length + 1

/-- The `n × n` table of the residues of the entries modulo `permanentModulus A`. -/
def reduceIntTable (A : List (List ℤ)) : List (List ℕ) :=
  (List.range A.length).map fun i => (List.range A.length).map fun j =>
    (intTableEntry A i j % (permanentModulus A : ℤ)).toNat

/-- The representative in `(-Q/2, Q/2)` of the residue of `p` modulo `Q = permanentModulus A`. -/
def recoverPermanent (x : List (List ℤ) × ℕ) : ℤ :=
  if 2 * (x.2 % permanentModulus x.1) < permanentModulus x.1 then
    ((x.2 % permanentModulus x.1 : ℕ) : ℤ)
  else ((x.2 % permanentModulus x.1 : ℕ) : ℤ) - permanentModulus x.1

theorem tableMatrix_eq_intTableEntry (A : List (List ℤ)) (i j : Fin A.length) :
    tableMatrix A i j = intTableEntry A i j := by
  simp [tableMatrix_apply, intTableEntry, List.getD_eq_getElem?_getD]

theorem natAbs_intTableEntry_le {A : List (List ℤ)} {i j : ℕ} (hi : i < A.length)
    (hj : j < A.length) : (intTableEntry A i j).natAbs ≤ intTableAbsSum A := by
  refine List.le_sum_of_mem ?_
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨i, hi, j, hj, rfl⟩

/-- **The permanent is at most `n! · S ^ n` in absolute value.** -/
theorem abs_intPermanent_le (A : List (List ℤ)) :
    |IntPermanent A| ≤ (A.length.factorial * intTableAbsSum A ^ A.length : ℕ) := by
  rw [IntPermanent, Matrix.permanent]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ σ : Equiv.Perm (Fin A.length),
      |∏ i, tableMatrix A (σ i) i| ≤ (intTableAbsSum A : ℤ) ^ A.length := by
    intro σ
    rw [Finset.abs_prod]
    calc ∏ i, |tableMatrix A (σ i) i| ≤ ∏ _i : Fin A.length, (intTableAbsSum A : ℤ) :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => by
            rw [tableMatrix_eq_intTableEntry, Int.abs_eq_natAbs]
            exact_mod_cast natAbs_intTableEntry_le (σ i).isLt i.isLt)
      _ = (intTableAbsSum A : ℤ) ^ A.length := by simp
  calc ∑ σ : Equiv.Perm (Fin A.length), |∏ i, tableMatrix A (σ i) i|
      ≤ ∑ _σ : Equiv.Perm (Fin A.length), (intTableAbsSum A : ℤ) ^ A.length :=
        Finset.sum_le_sum fun σ _ => hterm σ
    _ = (A.length.factorial * intTableAbsSum A ^ A.length : ℕ) := by
        simp [Finset.card_univ, Fintype.card_perm]

theorem length_reduceIntTable (A : List (List ℤ)) : (reduceIntTable A).length = A.length := by
  simp [reduceIntTable]

theorem getD_reduceIntTable {A : List (List ℤ)} {i j : ℕ} (hi : i < (reduceIntTable A).length)
    (hj : j < A.length) :
    (reduceIntTable A)[i].getD j 0 = (intTableEntry A i j % (permanentModulus A : ℤ)).toNat := by
  simp [reduceIntTable, List.getD_eq_getElem?_getD, hj]

/-- The permanent of the reduced table agrees with the integer permanent modulo `Q`. -/
theorem permanent_reduceIntTable_modEq (A : List (List ℤ)) :
    ((tableMatrix (reduceIntTable A)).permanent : ℤ) ≡ IntPermanent A
      [ZMOD (permanentModulus A : ℤ)] := by
  have hQ : (0 : ℤ) < permanentModulus A := by exact_mod_cast Nat.succ_pos _
  have hl := length_reduceIntTable A
  rw [← ZMod.intCast_eq_intCast_iff, IntPermanent]
  have hcast : (((tableMatrix (reduceIntTable A)).permanent : ℕ) : ℤ) =
      ((tableMatrix (reduceIntTable A)).map (Nat.cast : ℕ → ℤ)).permanent :=
    (Nat.castRingHom ℤ).map_permanent _
  have hmap : ∀ M : Matrix (Fin A.length) (Fin A.length) ℤ,
      ((M.permanent : ℤ) : ZMod (permanentModulus A)) =
        (M.map (Int.castRingHom (ZMod (permanentModulus A)))).permanent := fun M => by
    simpa using (Int.castRingHom (ZMod (permanentModulus A))).map_permanent M
  have hmap' : ∀ M : Matrix (Fin (reduceIntTable A).length) (Fin (reduceIntTable A).length) ℤ,
      ((M.permanent : ℤ) : ZMod (permanentModulus A)) =
        (M.map (Int.castRingHom (ZMod (permanentModulus A)))).permanent := fun M => by
    simpa using (Int.castRingHom (ZMod (permanentModulus A))).map_permanent M
  rw [hcast, hmap, hmap', ← Matrix.permanent_submatrix_equiv_equiv (finCongr hl.symm)
    (finCongr hl.symm)]
  refine congrArg Matrix.permanent ?_
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply, eq_intCast,
    tableMatrix_eq_intTableEntry]
  rw [tableMatrix_apply]
  simp only [Fin.getElem_fin, Fin.val_cast]
  rw [getD_reduceIntTable _ j.isLt]
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hQ.ne'), ZMod.intCast_mod]

/-- Recovering an integer from its residue modulo `Q = 2T + 1` when its absolute value is at most
`T`. -/
theorem recover_of_modEq {Q T p : ℕ} {P : ℤ} (hQ : Q = 2 * T + 1) (hP : |P| ≤ T)
    (hp : (p : ℤ) ≡ P [ZMOD (Q : ℤ)]) :
    (if 2 * (p % Q) < Q then ((p % Q : ℕ) : ℤ) else ((p % Q : ℕ) : ℤ) - Q) = P := by
  have hQpos : (0 : ℤ) < Q := by omega
  have hmod : ((p % Q : ℕ) : ℤ) = P % Q := by
    rw [Int.natCast_mod]; exact hp
  rw [abs_le] at hP
  rcases le_or_gt 0 P with h | h
  · have hPQ : P % Q = P := Int.emod_eq_of_lt h (by omega)
    rw [hPQ] at hmod
    have : 2 * (p % Q) < Q := by omega
    simp [this, hmod]
  · have hPQ : P % Q = P + Q := by
      rw [← Int.add_emod_right]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hPQ] at hmod
    have : ¬ 2 * (p % Q) < Q := by omega
    simp only [this, ite_false, hmod]
    ring

/-- **The integer step of Goldreich's Proposition 6.22**: the integer permanent of `A` is
recovered from `A` and the 0/1 permanent of `natTableToZeroOne (reduceIntTable A)`. -/
theorem intPermanent_eq_recoverPermanent (A : List (List ℤ)) :
    IntPermanent A =
      recoverPermanent (A, ZeroOnePermanent (natTableToZeroOne (reduceIntTable A))) := by
  rw [zeroOnePermanent_natTableToZeroOne, recoverPermanent]
  exact (recover_of_modEq (T := A.length.factorial * intTableAbsSum A ^ A.length)
    (by simp [permanentModulus]; ring) (abs_intPermanent_le A)
    (permanent_reduceIntTable_modEq A)).symm

end Cslib.Complexity
