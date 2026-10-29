/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.Splitting
public import Complexity.Algorithms.WordRAM.ExactTriangle.Instances
public import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationInput
public import Complexity.Algorithms.WordRAM.ExactTriangle.QuerySpec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Summing the native ExactTriangle preparation costs

The initialized preparation program computes the catalogue and writes every instance's record
and two matrices within `690n²Dg` charged instructions, including halt, in the source's admissible
parameter regime. The bound uses the existing finite instance count. Prime selection and solving
the prepared instances belong to the outer ExactTriangle host.

## Main results

* `PreparationBounds.matrix_writing_total_le`: both native matrix writers over all actual
  instances, including an explicit per-instance overhead.
* `PreparationBounds.residue_class_parameter_time_le`: signed residues, class scans and
  parameter arithmetic fit the preparation scale in the source's admitted regime.
* `PreparationBounds.catalogue_time_le`: descriptor enumeration, including empty-class costs.
* `PreparationBounds.timeBound_le`: the complete budget summed over the existing actual
  finite instance indices.
* `PreparationBounds.runs_input`: actual initialized execution with the complete output
  contract and the `690n²Dg` bound.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PreparationBounds

open Cslib.Algorithms.ExactTriangle

/-- Sum the two `20nD+6` matrix-writer bounds over the existing actual instance set. An explicit
additional `c` instructions per instance accounts for caller overhead separately. -/
theorem matrix_writing_total_le {n D g p : ℕ} (wAB : Fin n → Fin n → ℤ) (c : ℕ)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow D) :
    (∑ _ι ∈ instanceIndices wAB D g p, (2 * (20 * (n * D) + 6) + c)) ≤
      (208 + 4 * c) * (n * n) * D * g := by
  have hcard : (instanceIndices wAB D g p).card ≤ 4 * n * g := by
    exact_mod_cast card_instanceIndices_le wAB hD hDn hg hp
  have hpos : 1 ≤ n * D := Nat.mul_pos (by omega) (by omega)
  have hc : c ≤ c * (n * D) := Nat.le_mul_of_pos_right c hpos
  have h12 : 12 ≤ 12 * (n * D) := by omega
  have hstep : 2 * (20 * (n * D) + 6) + c ≤ (52 + c) * (n * D) := by
    nlinarith
  calc
    _ = (instanceIndices wAB D g p).card * (2 * (20 * (n * D) + 6) + c) := by
      simp only [Finset.sum_const, smul_eq_mul]
    _ ≤ (4 * n * g) * ((52 + c) * (n * D)) := Nat.mul_le_mul hcard hstep
    _ = (208 + 4 * c) * (n * n) * D * g := by ring

private theorem queryCap_le_sq (n D : ℕ) : queryCap n D ≤ n * n := by
  calc
    queryCap n D ≤ Nat.sqrt ((n ^ 2) ^ 2) := Nat.sqrt_le_sqrt (Nat.div_le_self ..)
    _ = n * n := by rw [Nat.sqrt_eq', pow_two]

/-- The exact signed-residue/class prefix bound and the parameter-kernel bound are charged
separately. Their sum is at most a fixed multiple of `n² D g` when `p ≤ D`; the prime-window
caller supplies that inequality. This includes all per-class scan overhead. -/
theorem residue_class_parameter_time_le {n D g p : ℕ}
    (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ≤ D) :
    69 * (n * n) + p * (14 * (n * n) + 14) + 30 +
        (5 * sOf D + 5 * queryCap n D + 27) ≤ 164 * (n * n) * D * g := by
  have hn : 1 ≤ n := hD.trans hDn
  have hN : 1 ≤ n * n := Nat.mul_pos hn hn
  have hnN : n ≤ n * n := Nat.le_mul_of_pos_right n hn
  have hs : sOf D ≤ n * n := (Nat.sqrt_le_self D).trans (hDn.trans hnN)
  have hq := queryCap_le_sq n D
  have hscan : p * (14 * (n * n) + 14) ≤ D * (28 * (n * n)) :=
    Nat.mul_le_mul hp (by omega)
  have hbase : n * n ≤ (n * n) * D := Nat.le_mul_of_pos_right _ hD
  have hfinal : (n * n) * D ≤ (n * n) * D * g := Nat.le_mul_of_pos_right _ hg
  nlinarith

/-- The actual concatenation loop scans all `p` class counts, but writes only their actual
chunks. Its conservative charged bound still lies on the `n² D g` preparation scale. -/
theorem catalogue_time_le {n D g p : ℕ}
    (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ≤ D) :
    p * (17 * (n * n) + 20) + 9 ≤ 46 * (n * n) * D * g := by
  have hN : 1 ≤ n * n := Nat.mul_pos (hD.trans hDn) (hD.trans hDn)
  have hstep : 17 * (n * n) + 20 ≤ 37 * (n * n) := by omega
  have hscan := Nat.mul_le_mul hp hstep
  have hbase : 1 ≤ (n * n) * D := Nat.mul_pos hN hD
  have hfinal : (n * n) * D ≤ (n * n) * D * g := Nat.le_mul_of_pos_right _ hg
  nlinarith only [hscan, hbase, hfinal]

/-- The complete prefix cost includes both argument-delivery stages in addition to residue,
class, parameter and descriptor enumeration. -/
theorem prefix_time_le {n D g p : ℕ}
    (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ≤ D) :
    Catalogue.cost n D p ≤ 229 * (n * n) * D * g := by
  have hprefix := residue_class_parameter_time_le hD hDn hg hp
  have hcatalogue := catalogue_time_le hD hDn hg hp
  have hbase : 1 ≤ (n * n) * D * g :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hD.trans hDn) (hD.trans hDn)) hD) hg
  have heq : Catalogue.cost n D p =
      69 * (n * n) + p * (14 * (n * n) + 14) + 30 +
        (5 * sOf D + 5 * queryCap n D + 27) + (p * (17 * (n * n) + 20) + 9) + 19 := by
    dsimp [Catalogue.cost]
    ring
  rw [heq]
  nlinarith only [hprefix, hcatalogue, hbase]

/-- Substitute the existing actual chunk and piece counts into the native budget. The
`690n²Dg` bound includes all catalogue work, selection, record stores, both matrix calls,
argument delivery, loop control and halt. `runs_input` applies this bound to actual execution. -/
theorem timeBound_le {n D g p : ℕ} (wAB : Fin n → Fin n → ℤ)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow D) :
    Instances.timeBound n D p (totalChunks wAB D p) (numPieces n D g) ≤
      690 * (n * n) * D * g := by
  have hpD : p ≤ D := (Nat.le_self_pow two_ne_zero p).trans
    ((Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).2.2.le)
  have hprefix := prefix_time_le (by omega : 1 ≤ D) hDn hg hpD
  have hmat := matrix_writing_total_le wAB 56 hD hDn hg hp
  have hvisit : (instanceIndices wAB D g p).card * (40 * (n * D) + 68) ≤
      432 * (n * n) * D * g := by
    simp only [Finset.sum_const, smul_eq_mul] at hmat
    convert hmat using 1
    ring
  have hbase : 1 ≤ (n * n) * D * g :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) hg
  rw [Instances.timeBound, ← card_instanceIndices wAB]
  nlinarith only [hprefix, hvisit, hbase]

/-- The native count in the initialized theorem is the existing finite chunk count. Thus its
actual charged execution budget, not an assumed matrix-write contract, has the preparation
bound in the source's admissible regime. -/
theorem computed_timeBound_le {n D g p : ℕ} (values : List ℤ)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow D) :
    let C := fun rho => Nat.count (fun q => (values.getD q 0 % (p : ℤ)).toNat = rho) (n * n)
    Instances.timeBound n D p (ChunkCatalogue.before C (queryCap n D) p)
      (numPieces n D g) ≤ 690 * (n * n) * D * g := by
  let wAB (a b : Fin n) := values.getD (Cslib.Matrix.pairIndex (a, b)) 0
  have hp0 : p ≠ 0 := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.ne_zero
  dsimp only
  rw [QuerySpec.before_eq_totalChunks wAB hp0
    (fun q => (values.getD q 0 % (p : ℤ)).toNat) (by intro q; rfl) D]
  exact timeBound_le wAB hD hDn hg hp

/-- The entire real initialized preparation, including halt, costs at most `690n²Dg` under
the existing finite splitting hypotheses. All output assertions refer to its same pre-halt
state. The supplied prime has not been chosen by this component. -/
theorem runs_input {n D g p A W : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n))
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow D)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hw : PreparationInput.width n D g p A ≤ W) :
    ∃ y t, t ≤ 690 * (n * n) * D * g ∧
      Cslib.WordRAM.Runs W PreparationInput.flatProgram
        (Cslib.WordRAM.State.init (PreparationInput.input n D g p values))
        ⟨Instances.program.size, y⟩ (t - 1) ∧
      Cslib.WordRAM.Executes W PreparationInput.flatProgram
        (Cslib.WordRAM.State.init (PreparationInput.input n D g p values))
        (y.regs Instances.output) t ∧
      Instances.Output n D g p (fun q => values.getD q 0)
        (.init (PreparationInput.input n D g p values)) y ∧
      Cslib.WordRAM.InputFits W (PreparationInput.input n D g p values) ∧ y.Bounded W := by
  obtain ⟨y, t, ht, hr, he, hout, hi, hb⟩ := PreparationInput.runs_input values hlen
    (by omega) hDn hg (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.pos hv hw
  exact ⟨y, t, ht.trans (computed_timeBound_le values hD hDn hg hp), hr, he, hout, hi, hb⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.PreparationBounds
