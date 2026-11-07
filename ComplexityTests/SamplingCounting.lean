/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.FPAUS.FPRAS
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Probability.BitString

/-! Checks of the sampling-to-counting reduction: a concrete self-reducible family with an
exact sampler, giving a checked instance of `mem_FPRAS_of_mem_FPAUS`, its zero-count instances,
the witness length `0`, and a sampler that is not almost uniform. -/

namespace ComplexityTests.SamplingCounting

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-- All words of length `n`. -/
private noncomputable def allWords (n : ℕ) : Finset (List Bool) :=
  Finset.univ.map ⟨List.ofFn (n := n), List.ofFn_injective⟩

private theorem mem_allWords {n : ℕ} {w : List Bool} : w ∈ allWords n ↔ w.length = n := by
  simp only [allWords, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨f, rfl⟩
    exact List.length_ofFn
  · rintro rfl
    exact ⟨w.get, List.ofFn_get w⟩

private theorem card_allWords (n : ℕ) : (allWords n).card = 2 ^ n := by
  simp [allWords]

private theorem allWords_nonempty (n : ℕ) : (allWords n).Nonempty :=
  ⟨List.replicate n false, mem_allWords.2 List.length_replicate⟩

/-- The instance `(n, b)` has as witnesses all words of length `n` if `b`, and none otherwise. -/
private noncomputable def W (x : ℕ × Bool) : Finset (List Bool) :=
  if x.2 then allWords x.1 else ∅

private theorem mem_W {x : ℕ × Bool} {w : List Bool} : w ∈ W x ↔ x.2 = true ∧ w.length = x.1 := by
  rcases x with ⟨n, _ | _⟩ <;> simp [W, mem_allWords]

/-- Fixing the first bit leaves all words of one bit fewer. -/
private noncomputable def R : SelfReducible (encPair encUnary encBool) W where
  len x := x.1
  child x _ := (x.1 - 1, x.2)
  length_eq x w hw := (mem_W.1 hw).2
  cons_mem_iff x hx b w := by
    simp only [mem_W, List.length_cons]
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h, by omega⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, by omega⟩
  len_child x _ _ := rfl
  length_child_le x _ _ := by
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    omega
  len_polytime := ComputableInPolyTime.fst _ _
  child_polytime := by fun_prop
  nil_mem_polytime := by
    have heq : (fun x : ℕ × Bool => decide ([] ∈ W x)) = fun x => x.2 && !decide (0 < x.1) := by
      funext x
      rcases x with ⟨_ | n, _ | _⟩ <;> simp [mem_W]
    rw [heq]
    fun_prop

/-- The exact sampler: a uniform word of length `n` if `b`, and `none` otherwise. -/
private noncomputable def S (x : ℕ × Bool) (_ : ℕ) : ProbComp (Option (List Bool)) :=
  if x.2 then some <$> BitString.sampleList x.1 else pure none

private theorem uniformList_eq (n : ℕ) :
    BitString.uniformList n = PMF.uniformOfFinset (allWords n) (allWords_nonempty n) := by
  classical
  ext w
  rw [BitString.uniformList, PMF.map_apply, tsum_fintype, PMF.uniformOfFinset_apply]
  by_cases hw : w ∈ allWords n
  · obtain ⟨a₀, -, rfl⟩ := Finset.mem_map.1 hw
    have hw' : List.ofFn a₀ ∈ allWords n := hw
    simp only [hw', Function.Embedding.coeFn_mk, List.ofFn_inj, PMF.uniformOfFintype_apply,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, card_allWords, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  · simp only [hw, ite_false]
    refine Finset.sum_eq_zero fun a _ => ?_
    have hne : w ≠ List.ofFn a := fun h => hw (h ▸ mem_allWords.2 List.length_ofFn)
    simp [hne]

private theorem eval_S (x : ℕ × Bool) (q : ℕ) : ProbComp.eval (S x q) = uniformWitness (W x) := by
  rcases x with ⟨n, _ | _⟩
  · simp [S, W, uniformWitness_empty]
  · simp only [S, W, ite_true]
    rw [uniformWitness_of_nonempty (allWords_nonempty n), ProbComp.eval_map,
      BitString.eval_sampleList, uniformList_eq]

private theorem isPPTOn_S :
    IsPPTOn (encPair (encPair encUnary encBool) encUnary) (encOption encBits)
      (Function.uncurry S) := by
  have hcond : ComputableInPolyTime (fun a : (ℕ × Bool) × ℕ => a.1.2)
      (encPair (encPair encUnary encBool) encUnary) encBool := by fun_prop
  have hsome : ComputableInPolyTime (some (α := List Bool)) encBits (encOption encBits) := by
    fun_prop
  have hyes : IsPPTOn (encPair (encPair encUnary encBool) encUnary) (encOption encBits)
      (fun a : (ℕ × Bool) × ℕ => some <$> BitString.sampleList a.1.1) :=
    (isPPTOn_sampleList.preprocess (by fun_prop)).map hsome
  have hno : IsPPTOn (encPair (encPair encUnary encBool) encUnary) (encOption encBits)
      (fun _ : (ℕ × Bool) × ℕ => (pure none : ProbComp (Option (List Bool)))) :=
    (ComputableInPolyTime.const none).isPPTOn
  exact IsPPTOn.cond' hcond hyes hno

private theorem isFPAUS_S : IsFPAUS (encPair encUnary encBool) W S :=
  ⟨isPPTOn_S, fun x q => by
    rw [eval_S]
    exact TVWithin.refl _ (by positivity)⟩

/-! ### A checked instance of the theorem -/

/-- The witness counts of the family have an FPRAS, obtained from its exact sampler. -/
example : (fun x => (W x).card) ∈ FPRAS (encPair encUnary encBool) :=
  R.mem_FPRAS_of_mem_FPAUS ⟨S, isFPAUS_S⟩

example : IsFPRAS (encPair encUnary encBool) (fun x => (W x).card) (R.estimate S) :=
  R.isFPRAS_of_isFPAUS isFPAUS_S

/-! ### Counts, zero counts and witness length `0` -/

example : (W (3, true)).card = 8 := by
  simp [W, card_allWords]

example : (W (3, false)).card = 0 := by
  simp [W]

/-- A zero-count instance is estimated exactly as `0`, with positive denominator. -/
example (n p t : ℕ) :
    ∀ out ∈ (ProbComp.eval (R.estimate S (n, false) p t)).support, out.1 = 0 ∧ 0 < out.2 :=
  R.estimate_eq_zero S (by simp [W]) p t

/-- With witness length `0` no samples are drawn: the estimate is `1 / 1`. -/
example (p t : ℕ) : R.estimate S (0, true) p t = pure (1, 1) := by
  simp [SelfReducible.estimate, R, mem_W]

/-! ### A sampler that is not almost uniform -/

/-- The sampler that always reports no witness is not an almost uniform sampler for the family:
on `(1, true)` the event `{none}` has probability `1` instead of `0`. -/
example : ¬ IsFPAUS (encPair encUnary encBool) W (fun _ _ => pure none) := by
  rintro ⟨-, h⟩
  have hW : (W (1, true)).Nonempty := ⟨[true], mem_W.2 ⟨rfl, rfl⟩⟩
  have h1 := h (1, true) 1 {none}
  have hpre : (some : List Bool → Option (List Bool)) ⁻¹' {none} = ∅ := by
    ext
    simp
  rw [uniformWitness_of_nonempty hW, PMF.toOuterMeasure_map_apply, hpre,
    MeasureTheory.measure_empty] at h1
  norm_num at h1

end ComplexityTests.SamplingCounting
