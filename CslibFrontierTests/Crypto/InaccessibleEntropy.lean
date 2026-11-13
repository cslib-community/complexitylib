/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.InaccessibleEntropy.Amplify
import CslibFrontier.Probability.Collision
import CslibFrontier.Tactic.PPT

/-!
# Tests for 3-wise Boolean affine hashes and inaccessible average max-entropy

Checks concrete unconditional instances of:
1. `3`-wise independence and prefix-collision seed adjustment (`affineHash`, `prefixProj`,
   `adjustAffineSeed`).
2. Real sample entropy vs. accessible set expectation on a concrete `2`-to-`1` projection,
   verifying a strict `1 / 2`-bit entropy gap when only `{x}` is accessible and verifying that
   declaring the full fiber accessible collapses the gap to `0` (so `InaccessibleEntropyFamily`
   cannot be trivially satisfied by taking `accSet = fiberSet`).
3. Concrete unconditional instantiations of `isPPT_rompelBaseInverter`,
   `rompelBase_escape_le_mul_inversion` (at `c = 0` and `c = 2`), and
   `rompelBase_accessible_le_conditionalEntropy_sub` on `g = id` both at `c = 0, n = 2` (`1 / 192`
   gap) and at `c = 1, n = 8` (`1 / 144` gap, four times the `c = 0` bound `1 / 576` via the four
   separating truncation lengths), plus the explicit `bind_with` and `IsPPT.preprocess` composition
   that certifies such inverters.
4. Parallel repetition (`repHashFin`, `repAccessibleSet`, `repEscapeInverter`), two-universal
   input/output entropy reduction (`shrunkHashOutLen_add_one`, `card_image_inputHashFin_le`,
   `shrunkHashFin_false_positive_le`, `shrunkHash_randomCollision_le`), and the Theorem 4.5 /
   candidate-grid endpoints (`OneWay.exists_rompelBase_logGap`,
   `OneWay.exists_inaccessibleEntropyFamily_logGap`, `OneWay.exists_inaccessibleEntropyFamily`,
   `InaccessibleEntropyFamily.exists_shrinkingCollisionGrid`,
   `OneWay.exists_shrinkingCollisionGrid`).
-/

namespace CslibFrontierTests.Crypto.InaccessibleEntropy

open Cslib Cslib.BitString.LinearHash Cslib.Crypto Cslib.Probability Finset Turing.MultiTapeTM

/-! ### 1. Three-wise independence and prefix-collision conditioning -/

example (k n : ℕ) : IsKWiseIndependentHash 3 (BitString.LinearHash.affineHash (k := k) (n := n)) :=
  isThreeWiseIndependentHash_affineHash k n

example (k n r : ℕ) :
    IsKWiseIndependentHash 3
      (fun s x => prefixProj k r (BitString.LinearHash.affineHash (k := k) (n := n) s x)) :=
  isThreeWiseIndependentHash_prefixProj_affineHash k n r

/-- Concrete check of `toReal_map_adjustAffineSeed_eq` on `y = 11`, `y₀ = 00`, `s₀ = 0` at
`k = 2, n = 2, r = 1`: projecting onto the prefix-colliding seed subgroup doubles the uniform mass
of `s₀ = 0`. -/
theorem toReal_map_adjustAffineSeed_allOnes_zero :
    (((PMF.uniformOfFintype ((Fin 2 → BitString 2) × BitString 2)).map
      (adjustAffineSeed 1 ((fun _ : Fin 2 => true) + 0))) 0).toReal =
      2 * ((PMF.uniformOfFintype ((Fin 2 → BitString 2) × BitString 2)) 0).toReal := by
  have hy : (fun _ : Fin 2 => true) ≠ (0 : BitString 2) := by
    intro h
    cases congrFun h 0
  have hs₀ :
      prefixProj 2 1
        (BitString.LinearHash.affineHash (0 : (Fin 2 → BitString 2) × BitString 2)
          (fun _ => true)) =
      prefixProj 2 1
        (BitString.LinearHash.affineHash (0 : (Fin 2 → BitString 2) × BitString 2) 0) := by
    decide
  simpa only [Nat.min_eq_left (by decide : 1 ≤ 2), pow_one] using
    toReal_map_adjustAffineSeed_eq (k := 2) (n := 2) 1 hy hs₀

/-! ### 2. Real vs. accessible entropy on a concrete 2-to-1 map -/

/-- Two-to-one projection dropping the second bit of `BitString 2`. -/
def firstBitProj (x : BitString 2) : BitString 1 := fun _ => x 0

example (A : BitString 2 → PMF (BitString 2)) :
    IsCollisionFinder firstBitProj (sanitizeCollisionFinder firstBitProj A) :=
  isCollisionFinder_sanitizeCollisionFinder firstBitProj A

/-- On `firstBitProj : BitString 2 → BitString 1` with singleton accessible sets `L x = {x}`,
every fiber has size `2`, so `conditionalEntropy_sub_accessibleSetExpectation_ge` witnesses an
unconditional `1 / 2`-bit gap. -/
theorem firstBitProj_singleton_gap_ge_half :
    (1 / 2 : ℝ) ≤
      PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString 2)).map fun x =>
        (firstBitProj x, x)) -
        accessibleSetExpectation (fun x : BitString 2 => ({x} : Finset (BitString 2))) := by
  have hbound := conditionalEntropy_sub_accessibleSetExpectation_ge firstBitProj
    (fun x => ({x} : Finset (BitString 2)))
    (fun x => mem_singleton_self x)
    (fun x z hz => by
      rw [mem_singleton.mp hz]
      exact self_mem_fiberSet firstBitProj x)
  have hfib (x : BitString 2) : #(fiberSet firstBitProj (firstBitProj x)) = 2 := by
    let flip1 : BitString 2 := Function.update x 1 (!x 1)
    have hne : x ≠ flip1 := by
      intro h
      have h1 := congrFun h 1
      simp only [flip1, Function.update_self] at h1
      cases x 1 <;> simp_all
    have hset : fiberSet firstBitProj (firstBitProj x) = {x, flip1} := by
      ext z
      simp only [fiberSet, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · intro hz0
        have hz0' : z 0 = x 0 := congrFun hz0 0
        by_cases hz1 : z 1 = x 1
        · left
          funext i
          fin_cases i
          · exact hz0'
          · exact hz1
        · right
          funext i
          fin_cases i
          · change z 0 = flip1 0
            simpa only [flip1, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)] using hz0'
          · change z 1 = flip1 1
            simp only [flip1, Function.update_self]
            cases hx1 : x 1 <;> cases hzv : z 1 <;> simp_all
      · rintro (rfl | rfl)
        · rfl
        · funext i
          simp only [firstBitProj, flip1, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    rw [hset, card_pair hne]
  have hsdiff (x : BitString 2) :
      #(fiberSet firstBitProj (firstBitProj x) \ ({x} : Finset (BitString 2))) = 1 := by
    have hsub : ({x} : Finset (BitString 2)) ⊆ fiberSet firstBitProj (firstBitProj x) := by
      intro z hz
      rw [mem_singleton.mp hz]
      exact self_mem_fiberSet firstBitProj x
    rw [card_sdiff_of_subset hsub, hfib x, card_singleton]
  have hlhs : (∑ x : BitString 2, ((PMF.uniformOfFintype (BitString 2)) x).toReal *
      ((#(fiberSet firstBitProj (firstBitProj x) \ ({x} : Finset (BitString 2))) : ℝ) /
        #(fiberSet firstBitProj (firstBitProj x)))) = 1 / 2 := by
    simp only [hsdiff, hfib, Nat.cast_one, Nat.cast_ofNat, PMF.uniformOfFintype_apply,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ENNReal.toReal_inv, sum_const,
      card_univ, nsmul_eq_mul]
    norm_num
  linarith

/-- Declaring the entire fiber accessible (`L x = fiberSet F (F x)`) makes accessible expectation
equal to real conditional entropy, confirming that
`InaccessibleEntropyFamily.eventually_entropy_gap` (`1 / denom n > 0`) rejects the trivial
full-fiber choice. -/
theorem fullFiber_accessibleSetExpectation_eq_conditionalEntropy {α β : Type*}
    [Fintype α] [Nonempty α] [Finite β] [DecidableEq β] (F : α → β) :
    accessibleSetExpectation (fun x => fiberSet F (F x)) =
      PMF.conditionalEntropy ((PMF.uniformOfFintype α).map fun x => (F x, x)) :=
  expected_realSampleEntropy_eq_conditionalEntropy F

/-! ### 3. Unconditional checks on the Rompel–HHRVW base construction for `g = id` -/

example :
    IsPPT encBits
      (rompelBaseInverter id id (fun n _ => pure (List.replicate n false))) :=
  isPPT_rompelBaseInverter .id' .id' (by ppt)

/-- The explicit composition behind `isPPT_rompelBaseInverter`, on a smaller inverter: sample,
call a parameterized adversary on prepared inputs, then post-process its answer. -/
example {A : ℕ → List Bool → ProbComp (List Bool)} (hA : IsPPT encBits A) :
    IsPPT encBits (fun n y => do
      let pad ← Cslib.BitString.sampleList n
      let raw ← A n (y ++ pad)
      return raw.take n) := by
  apply IsPPTOn.isPPT
  refine (ComputableInPolyTime.sampleList (by fun_prop)).bind_with ?_
  exact (hA.preprocess (ComputableInPolyTime.tidy (by fun_prop))
    (ComputableInPolyTime.tidy (by fun_prop))).bind_with
    (ComputableInPolyTime.isPPTOn (by fun_prop))

example (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame (rompelBaseEvalWord id id)
        (fun k => rompelBaseInLen k k) (rompelAccessibleSet 0 id id) A n)) : ℝ) ≤
      4 * (Game.succProbability (ProbComp.eval
        (inversionGame id (rompelBaseInverter id id A) n)) : ℝ) := by
  simpa only [pow_zero, mul_one, id_eq] using
    rompelBase_escape_le_mul_inversion 0 id id A n (fun _ hw => hw)

example (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame (rompelBaseEvalWord id id)
        (fun k => rompelBaseInLen k k) (rompelAccessibleSet 2 id id) A n)) : ℝ) ≤
      (4 * (n + 1 : ℝ) ^ 2) * (Game.succProbability (ProbComp.eval
        (inversionGame id (rompelBaseInverter id id A) n)) : ℝ) :=
  rompelBase_escape_le_mul_inversion 2 id id A n (fun _ hw => hw)

/-- Unconditional concrete check of `rompelBase_accessible_le_conditionalEntropy_sub` at `c = 0` on
`g = id` at `n = 2`: since `collisionProbability (uniformList 2) = 1 / 4 ≤ 1 / 2`, the Rompel base
hash has an unconditional real-vs-accessible entropy gap of at least `1 / 192` bits. -/
theorem rompelBase_id_two_entropy_gap :
    accessibleSetExpectation (rompelAccessibleSet 0 id id 2) ≤
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (BitString (rompelBaseInLen 2 2))).map fun b =>
          (wordToFinMap (rompelBaseInLen 2 2) (rompelBaseOutLen 2 2)
            (rompelBaseEvalWord id id 2) b, b)) -
        1 / 192 := by
  have hcoll : (4 * (2 : ℝ) ^ (0 * Nat.log 2 2) - 3) *
      PMF.collisionProbability ((Cslib.BitString.uniformList 2).map id) ≤ 1 / 2 := by
    rw [PMF.map_id, Cslib.BitString.uniformList,
      PMF.collisionProbability_map_of_injective _ _ List.ofFn_injective,
      PMF.collisionProbability_uniform]
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    norm_num
  have hgap := rompelBase_accessible_le_conditionalEntropy_sub 0 id id 2 (by decide)
    (fun _ hw => hw) hcoll
  norm_num at hgap ⊢
  exact hgap

/-- Unconditional concrete check of `rompelBase_accessible_le_conditionalEntropy_sub` with
polynomial light-image threshold `c = 1` on `g = id` at `n = 8`: since `Nat.log 2 8 = 3 ≤ 8` and
`(4 * 2 ^ 3 - 3) * (1 / 256) = 29 / 256 ≤ 1 / 2`, all `4` separating truncation lengths contribute,
giving an unconditional `(3 + 1) / (64 * 9) = 1 / 144`-bit entropy gap (`4` times the `c = 0`
constant-threshold bound `1 / 576`). -/
theorem rompelBase_id_eight_polyThreshold_entropy_gap :
    accessibleSetExpectation (rompelAccessibleSet 1 id id 8) ≤
      PMF.conditionalEntropy
        ((PMF.uniformOfFintype (BitString (rompelBaseInLen 8 8))).map fun b =>
          (wordToFinMap (rompelBaseInLen 8 8) (rompelBaseOutLen 8 8)
            (rompelBaseEvalWord id id 8) b, b)) -
        1 / 144 := by
  have hlog : Nat.log 2 8 = 3 := by decide
  have hcoll : (4 * (2 : ℝ) ^ (1 * Nat.log 2 8) - 3) *
      PMF.collisionProbability ((Cslib.BitString.uniformList 8).map id) ≤ 1 / 2 := by
    rw [hlog, PMF.map_id, Cslib.BitString.uniformList,
      PMF.collisionProbability_map_of_injective _ _ List.ofFn_injective,
      PMF.collisionProbability_uniform]
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
    norm_num
  have hgap := rompelBase_accessible_le_conditionalEntropy_sub 1 id id 8
    (by rw [hlog]; decide) (fun _ hw => hw) hcoll
  rw [hlog] at hgap
  norm_num at hgap ⊢
  exact hgap

/-! ### 4. Parallel repetition, entropy reduction, and candidate-grid endpoints -/

/-- At `t = 2` repetitions of `firstBitProj`, `realSampleEntropy` of `0` doubles from `1` bit to
`2` bits while singleton accessible log-cardinality remains `0`. -/
theorem repHashFin_two_firstBitProj_gap :
    realSampleEntropy (repHashFin 2 firstBitProj) (fun _ => (0 : BitString 2)) = 2 ∧
      Real.logb 2 #(repAccessibleSet 2 (fun x : BitString 2 => ({x} : Finset (BitString 2)))
        (fun _ => 0)) = 0 := by
  have hfib0 : #(fiberSet firstBitProj (firstBitProj 0)) = 2 := by decide
  constructor
  · rw [realSampleEntropy_repHashFin, Fin.sum_univ_two]
    simp only [realSampleEntropy, hfib0, Nat.cast_ofNat,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  · rw [logb_card_repAccessibleSet 2 (fun x => singleton_nonempty x), Fin.sum_univ_two]
    simp only [card_singleton, Nat.cast_one, Real.logb_one, add_zero]

example :
    IsPPT encBits
      (repEscapeInverter id id (fun n _ => pure (List.replicate (n * n) false))) :=
  isPPT_repEscapeInverter .id' .id' (by ppt)

example (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) :
    (Game.succProbability (ProbComp.eval
      (accessibleEscapeGame
        (fun k => repEvalWord k k id)
        (fun k => k * k)
        (fun k => repBitAccessibleSet k k (fun z => {z})) A n)) : ℝ) ≤
      (dyadicSize n : ℝ) *
        (Game.succProbability (ProbComp.eval
          (accessibleEscapeGame (fun _ => id) id (fun _ z => {z})
            (repEscapeInverter id id A) n)) : ℝ) :=
  repEscape_le_dyadicSize_mul_escape id id id (fun _ => id) (fun _ z => {z}) A n (fun _ hw => hw)

/-- Concrete `1`-bit shrinkage check on `shrunkHashOutLen 4 2`: `4 + 16 = 20` inner input bits,
`19` outer hash rows of width `2 + 16 + 4 = 22`, giving `19 * 22 + 19 = 437` output bits vs.
`20 + 19 * 22 = 438` input bits. -/
example : shrunkHashOutLen 4 2 + 1 = shrunkHashInLen 4 2 ∧ shrunkHashOutLen 4 2 = 437 :=
  ⟨shrunkHashOutLen_add_one (by decide : 1 ≤ 4) 2, rfl⟩

example :
    IsPPT encBits
      (shrunkHashEscapeInverter (fun n => n + 1) id (fun _ _ => pure [])) :=
  isPPT_shrunkHashEscapeInverter (by fun_prop) .id' (by ppt)

example (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) :
    let f₁ := wordToFinMap (n + 1) (n + 1) id
    (Game.succProbability (ProbComp.eval
      (randomCollisionGame
        (fun k => shrunkHashEvalWord (k + 1) (k + 1) id 1)
        (fun k => shrunkHashInLen (k + 1) (k + 1)) A n)) : ℝ) ≤
      (Game.succProbability (ProbComp.eval
        (accessibleEscapeGame (fun _ => id) (fun k => k + 1) (fun _ z => {z})
          (shrunkHashEscapeInverter (fun k => k + 1) (fun k => k + 1) A) n)) : ℝ) +
      ((PMF.uniformOfFintype (BitString (n + 1))).toOuterMeasure
        {z | (0 : ℝ) ≤ Real.logb 2 #({z} : Finset (BitString (n + 1)))}).toReal +
      (2 : ℝ) ^ ((0 : ℝ) - min ((1 : ℕ) : ℝ) ((n + 1 : ℕ) : ℝ)) +
      2 * (((PMF.uniformOfFintype (BitString (n + 1))).toOuterMeasure
          {z | realSampleEntropy f₁ z ≤ 0}).toReal +
        (2 : ℝ) ^ (min ((1 : ℕ) : ℝ) ((n + 1 : ℕ) : ℝ) - 0)) :=
  shrunkHash_randomCollision_le (fun k => k + 1) (fun k => k + 1) (fun _ => 1)
    (fun _ => id) (fun _ z => {z}) A n (by omega) (fun _ hw => hw) 0 0

example (G : ShrinkingCollisionGrid) (n q : ℕ) (raw : List Bool) :
    G.outLen n + 1 = G.inLen n ∧ n + 1 ≤ G.outLen n ∧ 1 ≤ G.gridCount n ∧
      (G.evalGrid n q raw).length = G.outLen n :=
  ⟨G.outLen_add_one n, G.le_outLen n, G.gridCount_pos n, G.length_evalGrid n q raw⟩

example (F : InaccessibleEntropyFamily) : Nonempty ShrinkingCollisionGrid :=
  F.exists_shrinkingCollisionGrid

example {f : List Bool → List Bool} (hf : OneWay f) :
    Nonempty InaccessibleEntropyFamily ∧ Nonempty ShrinkingCollisionGrid :=
  ⟨hf.exists_inaccessibleEntropyFamily, hf.exists_shrinkingCollisionGrid⟩

/-- Client check of `OneWay.exists_rompelBase_logGap`: one fixed family `(inLen, outLen, evalWord)`
simultaneously achieves eventual entropy gap `1 * log₂ n / n` and `(7 / 2) * log₂ n / n` via two
accessible-set families against all uniform strict-PPT adversaries. -/
example {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ (inLen outLen : ℕ → ℕ) (evalWord : ℕ → List Bool → List Bool),
      ComputableInPolyTime inLen encUnary encUnary ∧
      ComputableInPolyTime outLen encUnary encUnary ∧
      (∃ accSet₁ : (n : ℕ) → BitString (inLen n) → Finset (BitString (inLen n)),
        ∃ N₁ : ℕ, ∀ n, N₁ ≤ n →
          accessibleSetExpectation (accSet₁ n) ≤
            PMF.conditionalEntropy
              ((PMF.uniformOfFintype (BitString (inLen n))).map fun z =>
                (wordToFinMap (inLen n) (outLen n) (evalWord n) z, z)) -
              Real.logb 2 n / n) ∧
      (∃ accSet₂ : (n : ℕ) → BitString (inLen n) → Finset (BitString (inLen n)),
        ∃ N₂ : ℕ, ∀ n, N₂ ≤ n →
          accessibleSetExpectation (accSet₂ n) ≤
            PMF.conditionalEntropy
              ((PMF.uniformOfFintype (BitString (inLen n))).map fun z =>
                (wordToFinMap (inLen n) (outLen n) (evalWord n) z, z)) -
              (7 / 2 : ℝ) * Real.logb 2 n / n) := by
  obtain ⟨inLen, outLen, evalWord, hIn, hOut, _, _, hall⟩ := hf.exists_rompelBase_logGap
  obtain ⟨accSet₁, _, _, ⟨N₁, hN₁⟩, _⟩ := hall 1 one_pos
  obtain ⟨accSet₂, _, _, ⟨N₂, hN₂⟩, _⟩ := hall (7 / 2) (by norm_num)
  exact ⟨inLen, outLen, evalWord, hIn, hOut,
    ⟨accSet₁, N₁, fun n hn => by simpa only [one_mul] using hN₁ n hn⟩,
    ⟨accSet₂, N₂, hN₂⟩⟩

example {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ F : InaccessibleEntropyFamily,
      ∀ᶠ n : ℕ in Filter.atTop, 3 * Real.logb 2 n / n ≤ 1 / (F.denom n : ℝ) :=
  hf.exists_inaccessibleEntropyFamily_logGap (by norm_num)

/-! ### 5. Definition 3.9: word sanitization and adversary-dependent accessible sets -/

/-- `badEmptyAdv` outputs `[]` regardless of the `(n + 1)`-bit input, so it is not an
`IsWordCollisionFinder`, yet `sanitizeWordCollisionFinder` turns it into one while preserving
strict-PPT admissibility and `accessibleEscapeGame`. -/
def badEmptyAdv : ℕ → List Bool → ProbComp (List Bool) := fun _ _ => pure []

theorem not_isWordCollisionFinder_badEmptyAdv :
    ¬ IsWordCollisionFinder (fun n => n + 1) (fun _ w => w) badEmptyAdv := by
  intro h
  have h0 := h 0 [false] rfl [] (by simp [badEmptyAdv])
  exact absurd h0.1 (by decide)

example (n : ℕ) :
    IsWordCollisionFinder (fun k => k + 1) (fun _ w => w.take 1)
      (sanitizeWordCollisionFinder (fun k => k + 1) (fun _ w => w.take 1) badEmptyAdv) ∧
    IsCollisionFinder (wordToFinMap (n + 1) 1 (fun w => w.take 1))
      (fun z => (ProbComp.eval
        (sanitizeWordCollisionFinder (fun k => k + 1) (fun _ w => w.take 1) badEmptyAdv n
          (List.ofFn z))).map (BitString.ofList (n + 1))) ∧
    IsPPT encBits
      (sanitizeWordCollisionFinder (fun k => k + 1) (fun _ w => w.take 1) badEmptyAdv) ∧
    accessibleEscapeGame (fun _ w => w.take 1) (fun k => k + 1) (fun _ z => {z})
      (sanitizeWordCollisionFinder (fun k => k + 1) (fun _ w => w.take 1) badEmptyAdv) n =
      accessibleEscapeGame (fun _ w => w.take 1) (fun k => k + 1) (fun _ z => {z}) badEmptyAdv n :=
  ⟨isWordCollisionFinder_sanitizeWordCollisionFinder _ _ _,
    (isWordCollisionFinder_sanitizeWordCollisionFinder _ _ _).isCollisionFinder
      (outLen := fun _ => 1) n,
    isPPT_sanitizeWordCollisionFinder (by fun_prop)
      ((ComputableInPolyTime.snd encUnary encBits).bitsTakeWithInput (.const 1))
      (ComputableInPolyTime.const []).isPPT,
    accessibleEscapeGame_sanitizeWordCollisionFinder _ _ _ _ n fun _ => mem_singleton_self _⟩

/-- Two-bit conjunction `z 0 && z 1` has a `3`-element `false`-fiber, separating adversary-dependent
accessible sets ($\forall f, \exists L_f$ of size $\le 2$ with zero escape) from fixed accessible
sets ($\neg \exists L$ of size $\le 2$ with zero escape against all deterministic collision
finders). -/
def andTwoBits (z : BitString 2) : Bool := z 0 && z 1

theorem adversary_dependent_vs_fixed_accSet_andTwoBits :
    (∀ f : BitString 2 → BitString 2,
      ∃ L : BitString 2 → Finset (BitString 2),
        (∀ z, z ∈ L z) ∧ (∀ z, L z ⊆ fiberSet andTwoBits (andTwoBits z)) ∧
        (∀ z, #(L z) ≤ 2) ∧ (∀ z, andTwoBits (f z) = andTwoBits z → f z ∈ L z)) ∧
    ¬ ∃ L : BitString 2 → Finset (BitString 2),
        (∀ z, #(L z) ≤ 2) ∧
        ∀ f : BitString 2 → BitString 2,
          (∀ z, andTwoBits (f z) = andTwoBits z) → ∀ z, f z ∈ L z := by
  constructor
  · intro f
    refine ⟨fun z => insert z ((fiberSet andTwoBits (andTwoBits z)).filter (· = f z)),
      fun z => mem_insert_self _ _, fun z x hx => ?_, fun z => ?_, fun z hcol => ?_⟩
    · rcases mem_insert.mp hx with rfl | hmem
      · exact self_mem_fiberSet andTwoBits x
      · exact (mem_filter.mp hmem).1
    · refine (card_insert_le _ _).trans (Nat.succ_le_succ ?_)
      have hsub : (fiberSet andTwoBits (andTwoBits z)).filter (· = f z) ⊆ {f z} :=
        fun u hu => mem_singleton.mpr (mem_filter.mp hu).2
      exact (card_le_card hsub).trans (by simp)
    · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_fiberSet _ _ _ |>.mpr hcol, rfl⟩)
  · rintro ⟨L, hcard, hall⟩
    have hfib : #(fiberSet andTwoBits (andTwoBits 0)) = 3 := by decide
    have hlt : #(L 0) < #(fiberSet andTwoBits (andTwoBits 0)) := by
      have := hcard 0
      omega
    obtain ⟨w, hw_fib, hw_notMem⟩ := exists_mem_notMem_of_card_lt_card hlt
    have hw_eq : andTwoBits w = andTwoBits 0 := (mem_fiberSet _ _ _).mp hw_fib
    let f : BitString 2 → BitString 2 := fun z => if z = 0 then w else z
    have hf_col : ∀ z, andTwoBits (f z) = andTwoBits z := fun z => by
      dsimp only [f]
      split_ifs with hz
      · subst hz; exact hw_eq
      · rfl
    have hmem := hall f hf_col 0
    simp only [f, ↓reduceIte] at hmem
    exact hw_notMem hmem

example (F : AdversaryInaccessibleEntropyFamily) : Nonempty ShrinkingCollisionGrid :=
  F.exists_shrinkingCollisionGrid

example (F : InaccessibleEntropyFamily) : Nonempty ShrinkingCollisionGrid :=
  F.toAdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid

end CslibFrontierTests.Crypto.InaccessibleEntropy
