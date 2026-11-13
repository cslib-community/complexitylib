/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.LWE.Module.Seeded
public import CslibFrontier.Crypto.Computational.SIS.MLKEM.KPKE
import CslibFrontier.Probability.Uniform

/-! Seeded Module-LWE clients: the augmented public view, CBD noise, orientation and correlation.
The ideal CBD samplers below are the existing ML-KEM samplers by Karn Seth. These tests do not
identify independent ideal samples with the outputs of a seeded PRF. -/

public section

namespace CslibFrontierTests.SeededModuleLWE

open Cslib Cslib.Crypto Cslib.Probability
open scoped ENNReal

/-- The public seed and the independent extra row in the augmented hashed experiment. -/
structure PublicSeed (Seed : Type) (k n q : ℕ) where
  /-- The retained input to the deterministic matrix expander. -/
  seed : Seed
  /-- The independent uniform row used for the extra scalar product. -/
  row : Fin k → Fin n → ZMod q

/-- The independently sampled public row is retained alongside the matrix seed. -/
@[expose] noncomputable def publicSeedLaw {Seed : Type} (k n q : ℕ) [NeZero q]
    (seedLaw : PMF Seed) : PMF (PublicSeed Seed k n q) := do
  let seed ← seedLaw
  let row ← PMF.uniformOfFintype (Fin k → Fin n → ZMod q)
  return ⟨seed, row⟩

/-- Put the extra row first, followed by either orientation of the square matrix. -/
@[expose] def augmentedMatrix {Seed : Type} {k n q : ℕ}
    (expand : Seed → Matrix (Fin k) (Fin k) (Fin n → ZMod q)) (transpose : Bool)
    (s : PublicSeed Seed k n q) : Matrix (Fin (k + 1)) (Fin k) (Fin n → ZMod q) :=
  Fin.cons s.row (if transpose then (expand s.seed).transpose else expand s.seed)

/-- Independent CBD secret and error widths remain separate parameters. The first target
coordinate is the extra scalar product; the rest are the module target. Setting the two widths
equal gives the source's single short distribution. -/
@[expose] noncomputable def cbdLaw {Seed : Type} {k n q : ℕ} [NeZero q]
    (seedLaw : PMF Seed) (expand : Seed → Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    (transpose : Bool) (secretWidth errorWidth : ℕ) :=
  ModuleLWE.seededSampleLaw (publicSeedLaw k n q seedLaw) (augmentedMatrix expand transpose)
    (ProbComp.eval (MLKEM.sampleVecCBD k n q secretWidth))
    (ProbComp.eval (MLKEM.sampleVecCBD (k + 1) n q errorWidth))

-- Both pieces use the very same secret, including the extra scalar product.
example {Seed : Type} {k n q : ℕ}
    (expand : Seed → Matrix (Fin k) (Fin k) (Fin n → ZMod q)) (transpose : Bool)
    (sd : PublicSeed Seed k n q) (s : Fin k → Fin n → ZMod q)
    (e : Fin (k + 1) → Fin n → ZMod q) :
    ModuleLWE.sample (augmentedMatrix expand transpose sd) s e 0 =
      (∑ j, negacyclicMul (sd.row j) (s j)) + e 0 := rfl

example {Seed : Type} {k n q : ℕ}
    (expand : Seed → Matrix (Fin k) (Fin k) (Fin n → ZMod q)) (transpose : Bool)
    (sd : PublicSeed Seed k n q) (s : Fin k → Fin n → ZMod q)
    (e : Fin (k + 1) → Fin n → ZMod q) (i : Fin k) :
    ModuleLWE.sample (augmentedMatrix expand transpose sd) s e i.succ =
      ModuleLWE.sample (if transpose then (expand sd.seed).transpose else expand sd.seed)
        s (fun j => e j.succ) i := rfl

/-- The augmented law is the source-shaped joint `(v,u)` experiment with one shared secret.
The two error draws and the public row are independent; the order of the target coordinates
places the extra scalar product first. -/
theorem cbdLaw_eq {Seed : Type} {k n q : ℕ} [NeZero q]
    (seedLaw : PMF Seed) (expand : Seed → Matrix (Fin k) (Fin k) (Fin n → ZMod q))
    (transpose : Bool) (secretWidth errorWidth : ℕ) :
    cbdLaw seedLaw expand transpose secretWidth errorWidth = (do
      let seed ← seedLaw
      let row ← PMF.uniformOfFintype (Fin k → Fin n → ZMod q)
      let secret ← ProbComp.eval (MLKEM.sampleVecCBD k n q secretWidth)
      let scalarError ← ProbComp.eval (MLKEM.samplePolyCBD n q errorWidth)
      let error ← ProbComp.eval (MLKEM.sampleVecCBD k n q errorWidth)
      return (⟨seed, row⟩,
        Fin.cons ((∑ j, negacyclicMul (row j) (secret j)) + scalarError)
          (ModuleLWE.sample (if transpose then (expand seed).transpose else expand seed)
            secret error))) := by
  have hs (sd : PublicSeed Seed k n q) (secret : Fin k → Fin n → ZMod q)
      (scalarError : Fin n → ZMod q) (error : Fin k → Fin n → ZMod q) :
      ModuleLWE.sample (augmentedMatrix expand transpose sd) secret
          (Fin.cons scalarError error) =
        Fin.cons ((∑ j, negacyclicMul (sd.row j) (secret j)) + scalarError)
          (ModuleLWE.sample (if transpose then (expand sd.seed).transpose else expand sd.seed)
            secret error) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simp only [cbdLaw, ModuleLWE.seededSampleLaw, publicSeedLaw,
    MLKEM.sampleVecCBD, OracleComp.replicateFin_succ, ProbComp.eval_bind,
    ProbComp.eval_map, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_map, Function.comp_def, hs]

-- Uniformity of the augmented target is exactly independent uniform scalar and vector targets.
example (k n q : ℕ) [NeZero q] :
    PMF.uniformOfFintype (Fin (k + 1) → Fin n → ZMod q) = (do
      let scalar ← PMF.uniformOfFintype (Fin n → ZMod q)
      let vector ← PMF.uniformOfFintype (Fin k → Fin n → ZMod q)
      return Fin.cons scalar vector) := by
  rw [← PMF.pi_uniformOfFintype, PMF.pi_fin_succ, PMF.pi_uniformOfFintype]
  rfl

-- Existing concrete game advantage is recovered without a second continuation abstraction.
example (secretLaw errorLaw : PMF (Fin 1 → Fin 1 → ZMod 3))
    (D : Matrix (Fin 1) (Fin 1) (Fin 1 → ZMod 3) →
      (Fin 1 → Fin 1 → ZMod 3) → ProbComp Bool) :
    Game.advantage
      ((ModuleLWE.seededSampleLaw (PMF.uniformOfFintype _) id secretLaw errorLaw).bind
        (fun (A, b) => ProbComp.eval (D A b)))
      ((do
        let A ← PMF.uniformOfFintype (Matrix (Fin 1) (Fin 1) (Fin 1 → ZMod 3))
        let b ← PMF.uniformOfFintype (Fin 1 → Fin 1 → ZMod 3)
        return (A, b)).bind (fun (A, b) => ProbComp.eval (D A b))) =
      ModuleLWE.advantage secretLaw errorLaw D := by
  rw [ModuleLWE.seededSampleLaw_bind_eq_realGame, ModuleLWE.advantage,
    ModuleLWE.randomGame_eq, ← PMF.uniformOfFintype_prod]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind, PMF.bind_map, Function.comp_def]

private theorem cbd_one_mod_two :
    (ProbComp.eval (ProbComp.sampleCenteredBinomial 1)).map (fun z : ℤ => (z : ZMod 2)) =
      PMF.uniformOfFintype (ZMod 2) := by
  rw [ProbComp.eval_sampleCenteredBinomial]
  simp only [BitString.uniformList_succ, BitString.uniformList_zero,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map, PMF.bind_bind, PMF.pure_bind]
  apply PMF.ext
  intro z
  simp only [PMF.bind_apply, tsum_bool, PMF.uniformOfFintype_apply, PMF.pure_apply]
  have hf : ([false].count true : ℤ) = 0 := rfl
  have ht : ([true].count true : ℤ) = 1 := rfl
  simp only [hf, ht]
  have hz : z = 0 ∨ z = 1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hm : (-1 : ZMod 2) = 1 := rfl
  have hh : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ + 2⁻¹ * 2⁻¹ = 2⁻¹ := by
    rw [← add_mul, ← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]
  rcases hz with rfl | rfl <;> norm_num
  · exact hh
  · rw [ite_eq_left hm.symm]
    exact hh

private theorem polyCBD_one_mod_two (n : ℕ) :
    ProbComp.eval (MLKEM.samplePolyCBD n 2 1) =
      PMF.uniformOfFintype (Fin n → ZMod 2) := by
  unfold MLKEM.samplePolyCBD
  simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  change (ProbComp.eval (OracleComp.replicateFin n (ProbComp.sampleCenteredBinomial 1))).map
    (fun coeffs i => (coeffs i : ZMod 2)) = _
  rw [← ProbComp.eval_replicateFin_map_coords,
    ProbComp.eval_replicateFin]
  simp only [ProbComp.eval_map]
  change (PMF.pi fun _ : Fin n =>
    (ProbComp.eval (ProbComp.sampleCenteredBinomial 1)).map (fun z : ℤ => (z : ZMod 2))) = _
  rw [cbd_one_mod_two, PMF.pi_uniformOfFintype]

private theorem vecCBD_one_mod_two (k n : ℕ) :
    ProbComp.eval (MLKEM.sampleVecCBD k n 2 1) =
      PMF.uniformOfFintype (Fin k → Fin n → ZMod 2) := by
  simp only [MLKEM.sampleVecCBD, ProbComp.eval_replicateFin, polyCBD_one_mod_two,
    PMF.pi_uniformOfFintype]

-- A nonzero CBD width gives exact ideality here, for either orientation and every secret width.
example {Seed : Type} {k n : ℕ} (seedLaw : PMF Seed)
    (expand : Seed → Matrix (Fin k) (Fin k) (Fin n → ZMod 2))
    (transpose : Bool) (secretWidth : ℕ) :
    cbdLaw seedLaw expand transpose secretWidth 1 = (do
      let sd ← publicSeedLaw k n 2 seedLaw
      let target ← PMF.uniformOfFintype (Fin (k + 1) → Fin n → ZMod 2)
      return (sd, target)) := by
  rw [cbdLaw, vecCBD_one_mod_two, ModuleLWE.seededSampleLaw_uniform_error]

-- A deterministic expander need not be invariant under transposition.
example : ModuleLWE.sample (!![![0], ![1]; ![0], ![0]] :
    Matrix (Fin 2) (Fin 2) (Fin 1 → ZMod 5)) ![![1], ![0]] 0 = ![![0], ![0]] := by decide

example : ModuleLWE.sample (!![![0], ![1]; ![0], ![0]] :
    Matrix (Fin 2) (Fin 2) (Fin 1 → ZMod 5)).transpose ![![1], ![0]] 0 =
      ![![0], ![1]] := by decide

/-- At width zero the existing CBD samplers supply zero vectors, including empty shapes. -/
theorem vecCBD_zero (k n q : ℕ) :
    ProbComp.eval (MLKEM.sampleVecCBD k n q 0) = PMF.pure 0 := by
  have hp : ProbComp.eval (MLKEM.samplePolyCBD n q 0) = PMF.pure 0 := by
    simp only [MLKEM.samplePolyCBD, ProbComp.sampleCenteredBinomial_zero,
      OracleComp.replicateFin_eq_pi, ProbComp.eval_bind, ProbComp.eval_pi_pure,
      ProbComp.eval_pure, PMF.pure_bind, Int.cast_zero]
    rfl
  rw [MLKEM.sampleVecCBD, OracleComp.replicateFin_eq_pi]
  calc
    _ = ProbComp.eval (OracleComp.pi (fun _ : Fin k => (pure 0 : ProbComp (Fin n → ZMod q)))) :=
      ProbComp.eval_pi_congr fun _ => by simpa using hp
    _ = _ := by rw [ProbComp.eval_pi_pure]; rfl

/-- A fair secret bit embedded as a rank-one, degree-one residue vector. -/
@[expose] noncomputable def bitSecretLaw : PMF (Fin 1 → Fin 1 → ZMod 2) :=
  (PMF.uniformOfFintype Bool).map (fun b : Bool => fun _ _ => if b then 1 else 0)

/-- The public matrix and extra row are both one, with no noise: both targets equal the secret. -/
@[expose] noncomputable def correlatedLaw :=
  ModuleLWE.seededSampleLaw (PMF.pure (⟨(), 1⟩ : PublicSeed Unit 1 1 2))
    (augmentedMatrix (fun _ => 1) false) bitSecretLaw (PMF.pure 0)

private theorem correlatedTarget (b : Bool) :
    ModuleLWE.sample (augmentedMatrix (fun _ : Unit => 1) false
        (⟨(), 1⟩ : PublicSeed Unit 1 1 2)) (fun _ _ => if b then 1 else 0) 0 =
      fun _ _ => if b then 1 else 0 := by
  cases b <;> decide

-- This test would fail if the extra scalar product sampled another secret.
example : correlatedLaw.map (fun view => decide (view.2 0 0 = view.2 1 0)) =
    PMF.pure true := by
  simp only [correlatedLaw, ModuleLWE.seededSampleLaw, bitSecretLaw,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind,
    PMF.bind_map, Function.comp_def, PMF.map_bind, PMF.pure_map,
    correlatedTarget, decide_true, PMF.bind_const]

-- Resampling the second secret destroys that certainty: equality then holds with mass 1/2.
example : ((do
    let first ← correlatedLaw
    let second ← correlatedLaw
    return decide (first.2 0 0 = second.2 1 0)) : Game) true = (2 : ℝ≥0∞)⁻¹ := by
  simp only [correlatedLaw, ModuleLWE.seededSampleLaw, bitSecretLaw,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind,
    PMF.bind_bind, PMF.bind_map, Function.comp_def, correlatedTarget]
  norm_num [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_apply, tsum_bool, PMF.uniformOfFintype_apply, PMF.pure_apply]
  rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]

end CslibFrontierTests.SeededModuleLWE
