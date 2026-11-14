/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.Ajtai
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Tactic.PPT

/-!
# Checked client and nonvacuity tests for Ajtai's hash function under SIS

Exercises `CslibFrontier/Crypto/Computational/SIS/Ajtai.lean` through ordinary imports:
* concrete `ajtaiFamilyValid` acceptance of canonical `[0, P.β κ]^m` encodings and rejection of
  wrong-parameter, wrong-length, out-of-range and non-canonical input words;
* concrete `ajtaiFamilyHash` evaluation, collision detection and extracted short integer solution;
* polynomial-time certificates (`computableInPolyTime_ajtaiFamilyValid`,
  `computableInPolyTime_ajtaiFamilyHash`) and asymptotic security instantiation
  (`isPPT_collisionToSIS`, `ajtaiAdvantage_negligible_of_sis`, `SIS.collisionResistantForOn_ajtai`)
  on a composite-modulus parameter family;
* nonvacuity on `zeroRowSIS` (`n = 0`), refuting both `CollisionResistantForOn` for Ajtai's
  hash family and `SIS zeroRowSIS`.
-/

namespace CslibFrontierTests.Crypto.Ajtai

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM
open scoped _root_.Matrix NNReal

/-! ### Composite-modulus concrete client -/

/-- A toy `SISParams` instance with composite modulus `q = 4`, infinity-norm bound `β = 1`,
and linear dimensions `n κ = κ + 1`, `m κ = 2 * (κ + 1)`. -/
def toySIS : SISParams where
  n κ := κ + 1
  m κ := 2 * (κ + 1)
  q _ := 4
  β _ := 1
  hq _ := ⟨by decide⟩

private def toyMatrix : Matrix (Fin (toySIS.n 0)) (Fin (toySIS.m 0)) (ZMod (toySIS.q 0)) :=
  fun _ _ => (2 : ZMod 4)

private def toyInput : toySIS.Input := ⟨0, toyMatrix⟩

/-- Canonical `SIS.encodeVec` words in `[0, 1]^2` are accepted by `ajtaiFamilyValid`. -/
example : ajtaiFamilyValid toySIS 0 toyInput (SIS.encodeVec ![0, 1]) = true :=
  ajtaiFamilyValid_encodeVec toyMatrix fun i => by fin_cases i <;> decide

example : ajtaiFamilyValid toySIS 0 toyInput (SIS.encodeVec ![1, 0]) = true :=
  ajtaiFamilyValid_encodeVec toyMatrix fun i => by fin_cases i <;> decide

/-- Out-of-range coordinates (`2` or `-1` when `β = 1`) are rejected. -/
example : ajtaiFamilyValid toySIS 0 toyInput (SIS.encodeVec ![2, 0]) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [ajtaiFamilyValid_eq_true_iff] at h
  obtain ⟨_, x, hx, hbounds⟩ := h
  dsimp only [toyInput, toySIS] at x hx hbounds
  have h0 := congrFun (SIS.encodeVec_injective hx) 0
  have hb := hbounds 0
  simp only [Matrix.cons_val_zero] at h0
  omega

example : ajtaiFamilyValid toySIS 0 toyInput (SIS.encodeVec ![-1, 0]) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [ajtaiFamilyValid_eq_true_iff] at h
  obtain ⟨_, x, hx, hbounds⟩ := h
  dsimp only [toyInput, toySIS] at x hx hbounds
  have h0 := congrFun (SIS.encodeVec_injective hx) 0
  have hb := hbounds 0
  simp only [Matrix.cons_val_zero] at h0
  omega

/-- Wrong-length vectors are rejected. -/
example : ajtaiFamilyValid toySIS 0 toyInput (encList encIntBin [0]) = false := by
  simp only [ajtaiFamilyValid, (Decoder.list Decoder.intBin).decode_enc]
  decide

example : ajtaiFamilyValid toySIS 0 toyInput (encList encIntBin [0, 0, 0]) = false := by
  simp only [ajtaiFamilyValid, (Decoder.list Decoder.intBin).decode_enc]
  decide

private theorem encodeVec_toyInput_mem {w : List Bool}
    (h : ajtaiFamilyValid toySIS 0 toyInput w = true) :
    w = SIS.encodeVec ![0, 0] ∨ w = SIS.encodeVec ![0, 1] ∨
      w = SIS.encodeVec ![1, 0] ∨ w = SIS.encodeVec ![1, 1] := by
  rw [ajtaiFamilyValid_eq_true_iff] at h
  obtain ⟨_, x, rfl, hbounds⟩ := h
  have h0 : 0 ≤ x ⟨0, by decide⟩ ∧ x ⟨0, by decide⟩ ≤ 1 := hbounds ⟨0, by decide⟩
  have h1 : 0 ≤ x ⟨1, by decide⟩ ∧ x ⟨1, by decide⟩ ≤ 1 := hbounds ⟨1, by decide⟩
  have hx0 : x ⟨0, by decide⟩ = 0 ∨ x ⟨0, by decide⟩ = 1 := by omega
  have hx1 : x ⟨1, by decide⟩ = 0 ∨ x ⟨1, by decide⟩ = 1 := by omega
  have hvec (a b : ℤ) (ha : x ⟨0, by decide⟩ = a) (hb : x ⟨1, by decide⟩ = b) :
      SIS.encodeVec x = SIS.encodeVec ![a, b] := by
    congr 1
    ext i
    fin_cases i
    · exact ha
    · exact hb
  rcases hx0 with ha | ha <;> rcases hx1 with hb | hb
  · exact Or.inl (hvec 0 0 ha hb)
  · exact Or.inr (Or.inl (hvec 0 1 ha hb))
  · exact Or.inr (Or.inr (Or.inl (hvec 1 0 ha hb)))
  · exact Or.inr (Or.inr (Or.inr (hvec 1 1 ha hb)))

/-- Malformed or non-canonical words (empty word, trailing junk bits) are rejected. -/
example : ajtaiFamilyValid toySIS 0 toyInput [] = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hmem := encodeVec_toyInput_mem h
  revert hmem
  decide

example : ajtaiFamilyValid toySIS 0 toyInput (SIS.encodeVec ![0, 1] ++ [true]) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hmem := encodeVec_toyInput_mem h
  revert hmem
  decide

/-- An input whose `secParam` disagrees with `κ` is rejected. -/
example : ajtaiFamilyValid toySIS 1 toyInput (SIS.encodeVec ![0, 1]) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [ajtaiFamilyValid_eq_true_iff] at h
  exact Nat.noConfusion h.1

/-- Concrete evaluation of `ajtaiFamilyHash` and collision in `[0, 1]^2` yielding a SIS solution
for `toyMatrix`. -/
example :
    ajtaiFamilyHash toySIS toyInput (SIS.encodeVec ![1, 0]) ⟨0, Nat.zero_lt_succ 0⟩ =
      (2 : ZMod 4) := by
  change ajtaiHash toyMatrix (ajtaiDecodeVec 2 (SIS.encodeVec ![1, 0]))
      ⟨0, Nat.zero_lt_succ 0⟩ = 2
  rw [ajtaiDecodeVec_encodeVec]
  decide

private theorem isCollisionFor_toy :
    isCollisionFor (ajtaiFamilyHash toySIS) (ajtaiFamilyValid toySIS) 0 toyInput
      (SIS.encodeVec ![1, 0]) (SIS.encodeVec ![0, 1]) = true := by
  rw [isCollisionFor_eq_true_iff]
  refine ⟨ajtaiFamilyValid_encodeVec toyMatrix fun i => by fin_cases i <;> decide,
    ajtaiFamilyValid_encodeVec toyMatrix fun i => by fin_cases i <;> decide, ?_, ?_⟩
  · intro h
    have h0 := congrFun (SIS.encodeVec_injective h) 0
    simp only [Matrix.cons_val_zero] at h0
    exact one_ne_zero h0
  · ext i
    change ajtaiHash toyMatrix (ajtaiDecodeVec 2 (SIS.encodeVec ![1, 0])) i =
      ajtaiHash toyMatrix (ajtaiDecodeVec 2 (SIS.encodeVec ![0, 1])) i
    rw [ajtaiDecodeVec_encodeVec, ajtaiDecodeVec_encodeVec]
    fin_cases i
    decide

example :
    SIS.IsSolution toyMatrix 1
      (ajtaiDecodeVec 2 (SIS.encodeVec ![1, 0]) - ajtaiDecodeVec 2 (SIS.encodeVec ![0, 1])) :=
  (isAjtaiCollision_of_isCollisionFor_ajtai isCollisionFor_toy).isSolution_sub

/-! ### Asymptotic efficiency and security instantiation -/

theorem toySIS_m_poly : ComputableInPolyTime toySIS.m encUnary encUnary := by
  refine ComputableInPolyTime.of_tidy ?_
  change ComputableTidilyInPolyTime (fun κ => 2 * (κ + 1)) encUnary encUnary
  exact ComputableTidilyInPolyTime.unary_mul.comp
    ((ComputableTidilyInPolyTime.const 2).prod
      (ComputableTidilyInPolyTime.unary_add.comp
        (ComputableTidilyInPolyTime.id'.prod (ComputableTidilyInPolyTime.const 1))))

theorem toySIS_q_poly : ComputableInPolyTime toySIS.q encUnary encNat :=
  ComputableInPolyTime.const 4

theorem toySIS_β_poly : ComputableInPolyTime toySIS.β encUnary encNat :=
  ComputableInPolyTime.const 1

example :
    ComputableInPolyTime (fun ((κ, d), w) => ajtaiFamilyValid toySIS κ d w)
      (encPair (encPair encUnary toySIS.encInput) encBits) encBool :=
  computableInPolyTime_ajtaiFamilyValid toySIS toySIS_m_poly toySIS_β_poly

example :
    ComputableInPolyTime
      (fun (d, w) =>
        List.ofFn fun i : Fin (toySIS.n d.secParam) => (ajtaiFamilyHash toySIS d w i).val)
      (encPair toySIS.encInput encBits) (encList encNat) :=
  computableInPolyTime_ajtaiFamilyHash toySIS toySIS_q_poly

example {F : toySIS.AjtaiFinder} (hSIS : SIS toySIS) (hF : F.IsPPT) :
    SISParams.Solver.IsPPT (P := toySIS) (fun κ => collisionToSIS (F κ)) ∧
      Negligible fun κ => ajtaiAdvantage (toySIS.q κ) (toySIS.β κ) (F κ) :=
  ⟨isPPT_collisionToSIS toySIS hF, ajtaiAdvantage_negligible_of_sis toySIS hSIS hF⟩

example (hSIS : SIS toySIS) :
    CollisionResistantForOn toySIS.encInput (ajtaiSetup toySIS) (ajtaiFamilyHash toySIS)
      (ajtaiFamilyValid toySIS) :=
  SIS.collisionResistantForOn_ajtai toySIS toySIS_m_poly hSIS

/-! ### Nonvacuity on `zeroRowSIS` -/

/-- Degenerate `SISParams` with zero rows (`n = 0`), single coordinate (`m = 1`), modulus `q = 2`
and bound `β = 1`. Every matrix has zero rows, so any two distinct inputs collide. -/
def zeroRowSIS : SISParams where
  n _ := 0
  m _ := 1
  q _ := 2
  β _ := 1
  hq _ := ⟨by decide⟩

/-- Constant collision finder returning encoded `0` and `1` coordinates in `Fin 1 → ℤ`. -/
noncomputable def zeroRowFinder : CollisionFinderFor zeroRowSIS.Input :=
  fun _ _ => pure
    (SIS.encodeVec (fun _ : Fin 1 => (0 : ℤ)), SIS.encodeVec (fun _ : Fin 1 => (1 : ℤ)))

theorem zeroRowFinder_isPPT :
    IsPPTOn (encPair encUnary zeroRowSIS.encInput) (encPair encBits encBits)
      fun p => zeroRowFinder p.1 p.2 :=
  (ComputableInPolyTime.const _).isPPTOn

private theorem isCollisionFor_zeroRow (κ : ℕ)
    (A : Matrix (Fin (zeroRowSIS.n κ)) (Fin (zeroRowSIS.m κ)) (ZMod (zeroRowSIS.q κ))) :
    isCollisionFor (ajtaiFamilyHash zeroRowSIS) (ajtaiFamilyValid zeroRowSIS) κ ⟨κ, A⟩
      (SIS.encodeVec (fun _ : Fin 1 => (0 : ℤ)))
      (SIS.encodeVec (fun _ : Fin 1 => (1 : ℤ))) = true := by
  rw [isCollisionFor_eq_true_iff]
  refine ⟨ajtaiFamilyValid_encodeVec A (fun _ => ⟨le_rfl, by simp [zeroRowSIS]⟩),
    ajtaiFamilyValid_encodeVec A (fun _ => ⟨zero_le_one, by simp [zeroRowSIS]⟩),
    ?_, funext fun i => i.elim0⟩
  intro h
  have h0 := congrFun (SIS.encodeVec_injective h) 0
  omega

theorem succProbability_collisionGameFor_zeroRow (κ : ℕ) :
    Game.succProbability
      (collisionGameFor (ajtaiSetup zeroRowSIS) (ajtaiFamilyHash zeroRowSIS)
        (ajtaiFamilyValid zeroRowSIS) zeroRowFinder κ) = 1 := by
  simp only [Game.succProbability, collisionGameFor, Game.withSetup, collisionExperiment,
    ajtaiSetup, zeroRowFinder, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_map,
    PMF.pure_bind, Function.comp_def]
  have hconst :
      (fun A : Matrix (Fin (zeroRowSIS.n κ)) (Fin (zeroRowSIS.m κ)) (ZMod (zeroRowSIS.q κ)) =>
        (PMF.pure
          (isCollisionFor (ajtaiFamilyHash zeroRowSIS) (ajtaiFamilyValid zeroRowSIS) κ ⟨κ, A⟩
            (SIS.encodeVec (fun _ : Fin 1 => (0 : ℤ)))
            (SIS.encodeVec (fun _ : Fin 1 => (1 : ℤ)))) : PMF Bool)) =
      fun _ => PMF.pure true := by
    funext A
    rw [isCollisionFor_zeroRow κ A]
  simp only [hconst, PMF.bind_const, PMF.pure_apply, ↓reduceIte, ENNReal.toNNReal_one]

/-- `CollisionResistantForOn` for Ajtai's hash family fails on `zeroRowSIS`. -/
theorem not_collisionResistantForOn_ajtai_zeroRow :
    ¬ CollisionResistantForOn zeroRowSIS.encInput (ajtaiSetup zeroRowSIS)
      (ajtaiFamilyHash zeroRowSIS) (ajtaiFamilyValid zeroRowSIS) :=
  not_collisionResistantForOn_of_le_succProbability one_ne_zero zeroRowFinder zeroRowFinder_isPPT
    fun κ => (succProbability_collisionGameFor_zeroRow κ).ge

/-- Hence `SIS zeroRowSIS` also fails (and `SIS.collisionResistantForOn_ajtai` is nonvacuous). -/
theorem not_sis_zeroRowSIS : ¬ SIS zeroRowSIS := by
  intro hSIS
  exact not_collisionResistantForOn_ajtai_zeroRow
    (SIS.collisionResistantForOn_ajtai zeroRowSIS (ComputableInPolyTime.const 1) hSIS)

end CslibFrontierTests.Crypto.Ajtai
