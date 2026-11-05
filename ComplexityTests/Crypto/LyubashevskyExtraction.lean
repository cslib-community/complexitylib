/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.Extraction
import Complexity.Probability.PMF.Bind

public section

open Cslib Cslib.Probability Cslib.Probability.PMF
open Cslib.Crypto Cslib.Crypto.Protocols.SigmaProtocol
open scoped ENNReal _root_.Matrix

namespace LyubashevskyExtractionTests

private def A : Matrix (Fin 1) (Fin 8) (ZMod 17) := Matrix.of fun _ j => if j = 0 then 1 else 0

private def response (T : Matrix (Fin 1) (Fin 1) (ZMod 17)) : Fin 8 → ℤ :=
  fun j => if j = 0 then (T 0 0).valMinAbs else 0

private noncomputable def kernel (T : Matrix (Fin 1) (Fin 1) (ZMod 17)) : PMF (Fin 8 → ℤ) :=
  PMF.pure (response T)

example : A 0 0 = 1 ∧ A 0 1 = 0 := by decide

private theorem public_response (S : Matrix (Fin 8) (Fin 1) ℤ)
    (hS : ∀ i j, |S i j| ≤ 1) :
    response (A * S.map Int.cast) = fun i => if i = 0 then S 0 0 else 0 := by
  have h : ((S 0 0 : ℤ) : ZMod 17).valMinAbs = S 0 0 := by
    rw [ZMod.valMinAbs_spec]
    have hb := abs_le.mp (hS 0 0)
    exact ⟨rfl, by omega, by omega⟩
  have hT : (A * S.map (Int.cast : ℤ → ZMod 17) :
      Matrix (Fin 1) (Fin 1) (ZMod 17)) 0 0 = (S 0 0 : ZMod 17) := by
    simp [A, Matrix.mul_apply]
  unfold response
  rw [hT, h]

private theorem accepting (S : Matrix (Fin 8) (Fin 1) ℤ)
    (hS : ∀ i j, |S i j| ≤ 1) :
    (lyubashevsky 1 8 1 17 3 1).Accepts (A, A * S.map Int.cast) 0
      (fun _ => false) (some 0) ∧
    (lyubashevsky 1 8 1 17 3 1).Accepts (A, A * S.map Int.cast) 0
      (fun _ => true) (some (response (A * S.map Int.cast))) := by
  rw [lyubashevsky_accepts_some_iff, lyubashevsky_accepts_some_iff]
  constructor
  · have hc : (Int.cast ∘ lyubashevskyChallenge (fun _ : Fin 1 => false) :
        Fin 1 → ZMod 17) = 0 := by funext i; rfl
    simp [hc]
  · constructor
    · rw [public_response S hS, mem_intBox]
      intro i
      split_ifs
      · exact (hS 0 0).trans (by norm_num)
      · norm_num
    · rw [public_response S hS]
      ext i
      simp [A, Matrix.mulVec, dotProduct, Matrix.mul_apply, lyubashevskyChallenge]

/-- This concrete kernel accepts with probability one, while its folded vector succeeds as
homogeneous SIS with positive probability. It only reads T, and A is nonzero. -/
example :
    0 < ((iid (uniformOfFinset (intBox (Fin 8) 1) (intBox_nonempty 1)) 1).bind fun cols =>
      let S : Matrix (Fin 8) (Fin 1) ℤ := Matrix.of fun i j => cols j i
      (kernel (A * S.map Int.cast)).map fun z => decide
        (SIS.IsSolution A 5 (0 - z - S *ᵥ
          (lyubashevskyChallenge (fun _ => false) - lyubashevskyChallenge (fun _ => true)))))
        true := by
  have h := lyubashevsky_fork_success_le_sis_add (η := 1) (γ := 3) (β := 1)
    A kernel (fun _ => 0) (fun _ _ => false) (fun _ _ => true) (fun _ => 0) id
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def, id_eq] at h
  have hleft : ((iid (uniformOfFinset (intBox (Fin 8) 1) (intBox_nonempty 1)) 1).bind
      fun cols =>
        let S : Matrix (Fin 8) (Fin 1) ℤ := Matrix.of fun i j => cols j i
        (kernel (A * S.map Int.cast)).map fun z => decide
          ((fun _ : Fin 1 => false) ≠ (fun _ : Fin 1 => true) ∧
            (lyubashevsky 1 8 1 17 3 1).Accepts (A, A * S.map Int.cast) 0
              (fun _ => false) (some 0) ∧
            (lyubashevsky 1 8 1 17 3 1).Accepts (A, A * S.map Int.cast) 0
              (fun _ => true) (some z))) true = 1 := by
    apply le_antisymm (PMF.coe_le_one _ _) (le_bind_apply_on_support _ ?_)
    intro cols hcols
    have hS (i : Fin 8) (j : Fin 1) : |cols j i| ≤ 1 :=
      mem_intBox.mp ((mem_support_uniformOfFinset_iff _ _).mp
        ((mem_support_iid_iff _ _).mp hcols j)) i
    have ha := accepting (Matrix.of fun i j => cols j i) hS
    simp only [kernel, PMF.pure_map, ha.1, ha.2]
    norm_num [funext_iff]
  simp only [PMF.map, Function.comp_def] at hleft
  rw [hleft] at h
  by_contra hn
  have hz := le_antisymm (not_lt.mp hn) (zero_le)
  simp only [PMF.map, Function.comp_def] at hz
  norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd] at h
  rw [hz] at h
  norm_num at h
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)] at h
  norm_num at h

/-- Empty challenges never form a distinct fork, regardless of the public-key kernel. -/
theorem empty_challenge_prediction_eq_zero {n m q η : ℕ} [NeZero q] {Ω : Type}
    (A : Matrix (Fin n) (Fin m) (ZMod q))
    (K : Matrix (Fin n) (Fin 0) (ZMod q) → PMF Ω)
    (c c' : Ω → BitString 0) (d : Ω → Fin m → ℤ) :
    ((iid (uniformOfFinset (intBox (Fin m) η) (intBox_nonempty η)) 0).bind fun cols =>
      let S : Matrix (Fin m) (Fin 0) ℤ := Matrix.of fun i j => cols j i
      (K (A * S.map Int.cast)).map fun out => decide
        (c out ≠ c' out ∧ d out = S *ᵥ
          (lyubashevskyChallenge (c out) - lyubashevskyChallenge (c' out)))) true = 0 := by
  apply le_antisymm _ zero_le
  simpa using lyubashevsky_predict_difference_le (η := η) A K c c' d

/-- Radius zero really loses all secret uncertainty: distinct-challenge prediction is certain. -/
example :
    ((iid (uniformOfFinset (intBox (Fin 8) 0) (intBox_nonempty 0)) 1).bind fun cols =>
      let S : Matrix (Fin 8) (Fin 1) ℤ := Matrix.of fun i j => cols j i
      (PMF.pure ()).map fun _ => decide
        ((fun _ : Fin 1 => false) ≠ (fun _ : Fin 1 => true) ∧
          (0 : Fin 8 → ℤ) = S *ᵥ (lyubashevskyChallenge (fun _ => false) -
            lyubashevskyChallenge (fun _ => true)))) true = 1 := by
  apply le_antisymm (PMF.coe_le_one _ _) (le_bind_apply_on_support _ ?_)
  intro cols hcols
  have hs : (Matrix.of fun i j => cols j i : Matrix (Fin 8) (Fin 1) ℤ) = 0 := by
    ext i j
    have hb := abs_le.mp (mem_intBox.mp ((mem_support_uniformOfFinset_iff _ _).mp
      ((mem_support_iid_iff _ _).mp hcols j)) i)
    change cols j i = 0
    omega
  simp only [hs, Matrix.zero_mulVec, PMF.pure_map]
  norm_num [funext_iff]

example : 2 * (2 * (3 - 1) + 1 * 1) < (17 : ℕ) := by decide

end LyubashevskyExtractionTests
