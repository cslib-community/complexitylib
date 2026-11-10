/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature
public import CslibFrontier.Probability.Guessing.Leakage
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool

/-!
# Nonzero SIS extraction from public-key-only lattice forks

Uniform bounded secret columns retain uncertainty after their public images are revealed.
A randomized kernel receiving only the public key predicts the secret's response difference
at distinct binary challenges with probability at most `k * q^n / (2η+1)^m`.
This is a finite counting argument, not an assumed entropy or simulation property.

The information restriction is essential: honest signing transcripts or shared signing coins
must not be supplied to the kernel without proving the required simulation bridge. This module
does not establish random-oracle EUF-CMA security.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevsky_predict_difference_le`: prediction bound.
* `Cslib.Crypto.Protocols.SigmaProtocol.lyubashevsky_fork_success_le_sis_add`: accepting-fork
  probability is at most actual SIS success plus the prediction loss.

## References

The explicit finite bound below is original. Its role is motivated by [Lyubashevsky2012],
conference version, Lemmas 4.2 and 4.4, pp. 748–750. That source uses Gaussian masks and sparse
ternary challenges; the present statement concerns this library's box secrets and binary challenges.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF
open scoped ENNReal _root_.Matrix

/-- A public-key-only randomized kernel predicts the difference of two secret responses at
unequal binary challenges with probability at most `k * q^n / (2η+1)^m`. The matrix is arbitrary;
no rank, primality, entropy, or simulator premise is required. -/
theorem lyubashevsky_predict_difference_le {n m k q η : ℕ} [NeZero q] {Ω : Type}
    (A : Matrix (Fin n) (Fin m) (ZMod q))
    (kernel : Matrix (Fin n) (Fin k) (ZMod q) → PMF Ω)
    (c c' : Ω → BitString k) (difference : Ω → Fin m → ℤ) :
    ((iid (uniformOfFinset (intBox (Fin m) η) (intBox_nonempty η)) k).bind fun cols =>
      let S : Matrix (Fin m) (Fin k) ℤ := Matrix.of fun i j => cols j i
      (kernel (A * S.map Int.cast)).map fun out =>
        decide (c out ≠ c' out ∧
          difference out = S *ᵥ (lyubashevskyChallenge (c out) -
            lyubashevskyChallenge (c' out)))) true ≤
      k * (q : ℝ≥0∞) ^ n / (2 * η + 1) ^ m := by
  classical
  let Box := ↥(intBox (Fin m) η)
  let _ : Nonempty Box := (intBox_nonempty η).to_subtype
  let secrets (values : Fin k → Box) : Matrix (Fin m) (Fin k) ℤ :=
    Matrix.of fun i j => (values j).val i
  let observe (x : Box) := A *ᵥ (Int.cast ∘ x.val)
  let publicKey (values : Fin k → Fin n → ZMod q) : Matrix (Fin n) (Fin k) (ZMod q) :=
    Matrix.of fun i j => values j i
  let delta (out : Ω) := lyubashevskyChallenge (c out) - lyubashevskyChallenge (c' out)
  let joint : PMF ((Fin k → Box) × Ω) := do
    let values ← uniformOfFintype (Fin k → Box)
    let out ← kernel (publicKey (observe ∘ values))
    return (values, out)
  have hsource : iid (uniformOfFinset (intBox (Fin m) η) (intBox_nonempty η)) k =
      (uniformOfFintype (Fin k → Box)).map (fun values j => (values j).val) := by
    rw [← uniformOfFintype_finset_map_val (intBox (Fin m) η), iid_map,
      iid_uniformOfFintype]
  have hkey (values : Fin k → Box) :
      A * (secrets values).map Int.cast = publicKey (observe ∘ values) := rfl
  have hcoord (j : Fin k) :
      (joint.map fun pair => decide (c pair.2 j ≠ c' pair.2 j ∧
        difference pair.2 = secrets pair.1 *ᵥ delta pair.2)) true ≤
        (q : ℝ≥0∞) ^ n / (2 * η + 1) ^ m := by
    have h := uniform_bind_le_div_of_coordinate_subsingleton observe
      (fun values => kernel (publicKey values))
      (fun values out => c out j ≠ c' out j ∧ difference out = secrets values *ᵥ delta out)
      j (fun values out a ha b hb => ?_)
    · simpa [joint, PMF.monad_bind_eq_bind, PMF.map_bind, PMF.bind_map, PMF.map_comp,
        Function.comp_def, Box, Fintype.card_pi, card_intBox] using h
    apply Subtype.ext
    funext i
    have heq : (secrets (Function.update values j a) -
        secrets (Function.update values j b)) *ᵥ delta out = 0 := by
      rw [Matrix.sub_mulVec, ← ha.2, ← hb.2, sub_self]
    have hi := congrFun heq i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi
    rw [Finset.sum_eq_single j] at hi
    · have hd : delta out j ≠ 0 := by
        cases hc : c out j <;> cases hc' : c' out j <;>
          simp_all [delta, lyubashevskyChallenge]
      have hab : (a.val i - b.val i) * delta out j = 0 := by
        change ((Function.update values j a j).val i -
          (Function.update values j b j).val i) * delta out j = 0 at hi
        simpa only [Function.update_self] using hi
      exact sub_eq_zero.mp ((mul_eq_zero.mp hab).resolve_right hd)
    · intro j' _ hj'
      change ((Function.update values j a j').val i -
        (Function.update values j b j').val i) * delta out j' = 0
      simp [Function.update_of_ne hj']
    · simp
  rw [hsource, PMF.bind_map]
  change ((uniformOfFintype (Fin k → Box)).bind fun values =>
    (kernel (A * (secrets values).map Int.cast)).map fun out =>
      decide (c out ≠ c' out ∧ difference out = secrets values *ᵥ delta out)) true ≤ _
  simp only [hkey]
  suffices h : (joint.map fun pair => decide (c pair.2 ≠ c' pair.2 ∧
      difference pair.2 = secrets pair.1 *ᵥ delta pair.2)) true ≤
        k * (q : ℝ≥0∞) ^ n / (2 * η + 1) ^ m by
    simpa only [joint, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind,
      PMF.pure_map, PMF.bind_pure, PMF.map_comp, PMF.map, PMF.bind_bind, PMF.pure_bind,
      Function.comp_def] using h
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hcover : {pair : (Fin k → Box) × Ω | c pair.2 ≠ c' pair.2 ∧
      difference pair.2 = secrets pair.1 *ᵥ delta pair.2} ⊆
      ⋃ j : Fin k, {pair | c pair.2 j ≠ c' pair.2 j ∧
        difference pair.2 = secrets pair.1 *ᵥ delta pair.2} := by
    intro pair hp
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hp.1
    exact Set.mem_iUnion.mpr ⟨j, hj, hp.2⟩
  calc
    _ ≤ joint.toOuterMeasure (⋃ j : Fin k, {pair | c pair.2 j ≠ c' pair.2 j ∧
        difference pair.2 = secrets pair.1 *ᵥ delta pair.2}) := by
      apply MeasureTheory.measure_mono
      intro pair hp
      exact hcover (of_decide_eq_true hp)
    _ ≤ ∑' j : Fin k, joint.toOuterMeasure {pair | c pair.2 j ≠ c' pair.2 j ∧
        difference pair.2 = secrets pair.1 *ᵥ delta pair.2} := MeasureTheory.measure_iUnion_le _
    _ = ∑ j : Fin k, (joint.map fun pair => decide (c pair.2 j ≠ c' pair.2 j ∧
        difference pair.2 = secrets pair.1 *ᵥ delta pair.2)) true := by
      simp only [tsum_fintype]
      apply Finset.sum_congr rfl
      intro j _
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
      congr 1
      ext pair
      simp
    _ ≤ ∑ _j : Fin k, (q : ℝ≥0∞) ^ n / (2 * η + 1) ^ m :=
      Finset.sum_le_sum fun j _ => hcoord j
    _ = _ := by simp [div_eq_mul_inv, mul_assoc]

/-- Accepting public-key-only forks give nonzero homogeneous SIS solutions except for the
explicit secret-prediction loss. The experiment samples the actual independent box secret
columns, runs the kernel on their public images, and folds its responses through that secret.
This is a probability bound, not a computational or EUF-CMA security claim. -/
theorem lyubashevsky_fork_success_le_sis_add {n m k q η γ β : ℕ} [NeZero q] {Ω : Type}
    (A : Matrix (Fin n) (Fin m) (ZMod q))
    (kernel : Matrix (Fin n) (Fin k) (ZMod q) → PMF Ω)
    (w : Ω → Fin n → ZMod q) (c c' : Ω → BitString k) (z z' : Ω → Fin m → ℤ) :
    let experiment : PMF (Matrix (Fin m) (Fin k) ℤ × Ω) := do
      let cols ← iid (uniformOfFinset (intBox (Fin m) η) (intBox_nonempty η)) k
      let S : Matrix (Fin m) (Fin k) ℤ := Matrix.of fun i j => cols j i
      let out ← kernel (A * S.map Int.cast)
      return (S, out)
    (experiment.map fun (S, out) => decide (c out ≠ c' out ∧
      (lyubashevsky n m k q γ β).Accepts (A, A * S.map Int.cast) (w out) (c out) (some (z out)) ∧
      (lyubashevsky n m k q γ β).Accepts (A, A * S.map Int.cast)
        (w out) (c' out) (some (z' out)))) true ≤
    (experiment.map fun (S, out) => decide (SIS.IsSolution A (2 * (γ - β) + k * η)
      (z out - z' out - S *ᵥ (lyubashevskyChallenge (c out) -
        lyubashevskyChallenge (c' out))))) true + k * (q : ℝ≥0∞) ^ n / (2 * η + 1) ^ m := by
  classical
  let experiment : PMF (Matrix (Fin m) (Fin k) ℤ × Ω) := do
    let cols ← iid (uniformOfFinset (intBox (Fin m) η) (intBox_nonempty η)) k
    let S : Matrix (Fin m) (Fin k) ℤ := Matrix.of fun i j => cols j i
    let out ← kernel (A * S.map Int.cast)
    return (S, out)
  have hsecret (pair) (hpair : pair ∈ experiment.support) :
      lyubashevskyRelation η pair.1 (A, A * pair.1.map Int.cast) := by
    simp only [experiment, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hpair
    obtain ⟨cols, hcols, out, _, rfl⟩ := hpair
    refine ⟨rfl, fun i j => ?_⟩
    have hj := (mem_support_iid_iff _ _).mp hcols j
    exact mem_intBox.mp ((mem_support_uniformOfFinset_iff _ _).mp hj) i
  have hbad : (experiment.map fun (S, out) => decide (c out ≠ c' out ∧
      z out - z' out = S *ᵥ (lyubashevskyChallenge (c out) -
        lyubashevskyChallenge (c' out)))) true ≤
        k * (q : ℝ≥0∞) ^ n / (2 * η + 1) ^ m := by
    simpa only [experiment, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map_bind, PMF.pure_map, PMF.bind_pure, PMF.map, PMF.bind_bind, PMF.pure_bind,
      Function.comp_def] using
      lyubashevsky_predict_difference_le (η := η) A kernel c c' (fun out => z out - z' out)
  refine (map_true_le_add experiment
    (A := fun (S, out) => decide (SIS.IsSolution A (2 * (γ - β) + k * η)
      (z out - z' out - S *ᵥ (lyubashevskyChallenge (c out) -
        lyubashevskyChallenge (c' out)))))
    (B := fun (S, out) => decide (c out ≠ c' out ∧
    z out - z' out = S *ᵥ (lyubashevskyChallenge (c out) -
      lyubashevskyChallenge (c' out)))) ?_).trans (add_le_add le_rfl hbad)
  rintro ⟨S, out⟩ hpair hgood
  obtain ⟨hc, hz, hz'⟩ := of_decide_eq_true hgood
  by_cases heq : z out - z' out = S *ᵥ
      (lyubashevskyChallenge (c out) - lyubashevskyChallenge (c' out))
  · exact Or.inr (decide_eq_true ⟨hc, heq⟩)
  · apply Or.inl
    apply decide_eq_true
    simpa only [extractSISFromTwoTranscripts_eq_sub, Option.getD_some] using
      lyubashevskyForkToSIS (hsecret (S, out) hpair) hz hz' heq

end Cslib.Crypto.Protocols.SigmaProtocol
