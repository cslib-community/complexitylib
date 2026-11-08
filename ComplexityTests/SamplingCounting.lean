/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.FPAUS.FPRAS
import Complexity.Computability.Complexity.Classes.FPAUS.Sampler
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Probability.BitString

/-! Checks of the reductions between sampling and counting. The family below has as witnesses of
`(m, r, true)` the words of length `m + r` whose first `m` bits are `false`. Fixing a `true` bit
inside that prefix leads to a dead instance without witnesses, so the estimator must avoid empty
branches. An exact sampler gives a checked instance of `mem_FPRAS_of_mem_FPAUS`; the tests also
cover zero-count instances, witness length `0`, and a sampler that is not almost uniform. In the
other direction, the exact counter and the FPRAS obtained from the exact sampler give checked
instances of `closeTo_sampler` and `closeTo_sampler_of_isFPRAS`, with checks of good estimates,
the branching coin, the acceptance bound of a trial, and a counter that misses the accuracy
hypothesis. -/

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

/-- Prefixing `m` false bits. -/
private def pad (m : ℕ) : List Bool ↪ List Bool :=
  ⟨fun w => List.replicate m false ++ w, List.append_right_injective _⟩

/-- The instance `(m, r, alive)`: if `alive`, the words `false^m ++ v` with `|v| = r`; otherwise
none. -/
private noncomputable def W (x : ℕ × ℕ × Bool) : Finset (List Bool) :=
  if x.2.2 then (allWords x.2.1).map (pad x.1) else ∅

private theorem mem_W {x : ℕ × ℕ × Bool} {w : List Bool} :
    w ∈ W x ↔ x.2.2 = true ∧ ∃ v, v.length = x.2.1 ∧ w = List.replicate x.1 false ++ v := by
  rcases x with ⟨m, r, _ | _⟩
  · simp [W]
  · simp only [W, ite_true, Finset.mem_map, mem_allWords, pad, Function.Embedding.coeFn_mk,
      true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩

private theorem card_W (m r : ℕ) : (W (m, r, true)).card = 2 ^ r := by
  simp [W, card_allWords]

/-- Fixing a bit: inside the prefix the bit must be `false`, and a `true` bit kills the instance;
after the prefix every bit is free. -/
private def child (x : ℕ × ℕ × Bool) (b : Bool) : ℕ × ℕ × Bool :=
  if 0 < x.1 then (x.1 - 1, x.2.1, x.2.2 && !b) else (x.1, x.2.1 - 1, x.2.2)

private theorem cons_mem_W {x : ℕ × ℕ × Bool} (hx : 0 < x.1 + x.2.1) (b : Bool)
    (w : List Bool) : b :: w ∈ W x ↔ w ∈ W (child x b) := by
  rcases x with ⟨_ | m, r, alive⟩
  · simp only [mem_W, child, lt_irrefl, ite_false, List.replicate_zero, List.nil_append]
    constructor
    · rintro ⟨ha, v, hv, rfl⟩
      rw [List.length_cons] at hv
      exact ⟨ha, w, by omega, rfl⟩
    · rintro ⟨ha, v, hv, hw⟩
      have hr : 0 < r := by simpa using hx
      refine ⟨ha, b :: v, ?_, by rw [hw]⟩
      rw [List.length_cons]
      omega
  · simp only [mem_W, child, Nat.succ_pos, ite_true, Nat.add_sub_cancel, List.replicate_succ,
      List.cons_append, List.cons.injEq, Bool.and_eq_true, Bool.not_eq_true']
    constructor
    · rintro ⟨ha, v, hv, hb, hw⟩
      exact ⟨⟨ha, hb⟩, v, hv, hw⟩
    · rintro ⟨⟨ha, hb⟩, v, hv, hw⟩
      exact ⟨ha, v, hv, hb, hw⟩

private theorem length_W {x : ℕ × ℕ × Bool} {w : List Bool} (hw : w ∈ W x) :
    w.length = x.1 + x.2.1 := by
  obtain ⟨-, v, hv, rfl⟩ := mem_W.1 hw
  simp [hv]

private noncomputable def R :
    SelfReducible (encPair encUnary (encPair encUnary encBool)) W where
  len x := x.1 + x.2.1
  child := child
  length_eq _ _ := length_W
  cons_mem_iff _ hx b w := cons_mem_W hx b w
  len_child x _ b := by
    rcases x with ⟨m, r, a⟩
    unfold child
    split_ifs with hm
    · change m - 1 + r = m + r - 1
      have hm' : 0 < m := hm
      omega
    · change m + (r - 1) = m + r - 1
      have hm' : ¬ 0 < m := hm
      omega
  length_child_le x _ b := by
    have h (y : ℕ × ℕ × Bool) : (encPair encUnary (encPair encUnary encBool) y).length =
        2 * y.1 + 1 + (2 * y.2.1 + 1 + 1) := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBool_apply,
        List.length_singleton]
    rcases x with ⟨m, r, a⟩
    rw [h, h]
    unfold child
    split_ifs with hm
    · change 2 * (m - 1) + 1 + (2 * r + 1 + 1) ≤ 2 * m + 1 + (2 * r + 1 + 1)
      omega
    · change 2 * m + 1 + (2 * (r - 1) + 1 + 1) ≤ 2 * m + 1 + (2 * r + 1 + 1)
      omega
  len_polytime := by fun_prop
  child_polytime := by
    unfold child
    fun_prop
  nil_mem_polytime := by
    have hiff (m r : ℕ) (a : Bool) : [] ∈ W (m, r, a) ↔ a = true ∧ m + r = 0 := by
      rw [mem_W]
      constructor
      · rintro ⟨ha, v, hv, hnil⟩
        have := congrArg List.length hnil
        rw [List.length_nil, List.length_append, List.length_replicate, hv] at this
        exact ⟨ha, this.symm⟩
      · rintro ⟨ha, hlen⟩
        obtain ⟨rfl, rfl⟩ : m = 0 ∧ r = 0 := by omega
        exact ⟨ha, [], rfl, rfl⟩
    have heq : (fun x : ℕ × ℕ × Bool => decide ([] ∈ W x)) =
        fun x => x.2.2 && !decide (0 < x.1 + x.2.1) := by
      funext x
      rcases x with ⟨m, r, a⟩
      rw [Bool.eq_iff_iff, decide_eq_true_iff, hiff]
      cases a <;> simp
    rw [heq]
    fun_prop

/-- The exact sampler: if alive, `m` false bits followed by `r` uniform bits; otherwise
`none`. -/
private noncomputable def S (x : ℕ × ℕ × Bool) (_ : ℕ) : ProbComp (Option (List Bool)) :=
  if x.2.2 then (fun v => some (List.replicate x.1 false ++ v)) <$> BitString.sampleList x.2.1
  else pure none

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

/-- Mapping a uniform law along an embedding gives the uniform law on the image. -/
private theorem map_uniformOfFinset (s : Finset (List Bool)) (hs : s.Nonempty)
    (f : List Bool ↪ List Bool) :
    (PMF.uniformOfFinset s hs).map f = PMF.uniformOfFinset (s.map f) (hs.map) := by
  classical
  ext w
  rw [PMF.map_apply, PMF.uniformOfFinset_apply, Finset.card_map]
  by_cases hw : w ∈ s.map f
  · obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_map.1 hw
    rw [ite_eq_left hw, tsum_eq_single a₀]
    · simp [ha₀]
    · intro a ha
      have : f a₀ ≠ f a := fun h => ha (f.injective h).symm
      simp [this]
  · rw [ite_eq_right hw]
    refine tsum_eq_zero_iff.2 fun a => ?_
    by_cases ha : a ∈ s
    · have : w ≠ f a := fun h => hw (h ▸ Finset.mem_map_of_mem f ha)
      simp [this]
    · simp [ha]

private theorem eval_S (x : ℕ × ℕ × Bool) (q : ℕ) :
    ProbComp.eval (S x q) = uniformWitness (W x) := by
  rcases x with ⟨m, r, _ | _⟩
  · simp [S, W, uniformWitness_empty]
  · have hne : (W (m, r, true)).Nonempty :=
      ⟨List.replicate m false ++ List.replicate r false,
        mem_W.2 ⟨rfl, List.replicate r false, List.length_replicate, rfl⟩⟩
    rw [uniformWitness_of_nonempty hne]
    simp only [S, ite_true, ProbComp.eval_map, BitString.eval_sampleList, uniformList_eq]
    have hcomp : (fun v => some (List.replicate m false ++ v)) = some ∘ pad m := rfl
    rw [hcomp, ← PMF.map_comp, map_uniformOfFinset]
    rfl

private theorem isPPTOn_S :
    IsPPTOn (encPair (encPair encUnary (encPair encUnary encBool)) encUnary) (encOption encBits)
      (Function.uncurry S) := by
  have hcond : ComputableInPolyTime (fun a : (ℕ × ℕ × Bool) × ℕ => a.1.2.2)
      (encPair (encPair encUnary (encPair encUnary encBool)) encUnary) encBool := by fun_prop
  have hout : ComputableInPolyTime
      (fun u : ((ℕ × ℕ × Bool) × ℕ) × List Bool => some (List.replicate u.1.1.1 false ++ u.2))
      (encPair (encPair (encPair encUnary (encPair encUnary encBool)) encUnary) encBits)
      (encOption encBits) := by
    fun_prop
  have hyes : IsPPTOn (encPair (encPair encUnary (encPair encUnary encBool)) encUnary)
      (encOption encBits) (fun a : (ℕ × ℕ × Bool) × ℕ =>
        (fun v => some (List.replicate a.1.1 false ++ v)) <$> BitString.sampleList a.1.2.1) :=
    IsPPTOn.of_seeded (count := fun a : (ℕ × ℕ × Bool) × ℕ => a.1.2.1)
      (f := fun u : ((ℕ × ℕ × Bool) × ℕ) × List Bool =>
        some (List.replicate u.1.1.1 false ++ u.2)) (by fun_prop) hout
  have hno : IsPPTOn (encPair (encPair encUnary (encPair encUnary encBool)) encUnary)
      (encOption encBits)
      (fun _ : (ℕ × ℕ × Bool) × ℕ => (pure none : ProbComp (Option (List Bool)))) :=
    (ComputableInPolyTime.const none).isPPTOn
  exact IsPPTOn.cond' hcond hyes hno

private theorem isFPAUS_S : IsFPAUS (encPair encUnary (encPair encUnary encBool)) W S :=
  ⟨isPPTOn_S, fun x q => by
    rw [eval_S]
    exact (Interactive.CloseTo.refl _).mono (by positivity)⟩

/-! ### A checked instance of the theorem -/

/-- The witness counts of the family have an FPRAS, obtained from its exact sampler. -/
example : (fun x => (W x).card) ∈ FPRAS (encPair encUnary (encPair encUnary encBool)) :=
  R.mem_FPRAS_of_mem_FPAUS ⟨S, isFPAUS_S⟩

example : IsFPRAS (encPair encUnary (encPair encUnary encBool)) (fun x => (W x).card)
    (R.estimate S) :=
  R.isFPRAS_of_isFPAUS isFPAUS_S

/-! ### Counts, empty branches, zero counts and witness length `0` -/

example : (W (2, 3, true)).card = 8 := card_W 2 3

/-- Fixing `true` inside the prefix leaves no witnesses, while fixing `false` keeps all of them:
the estimator has to choose the nonempty branch. -/
example : (W (child (2, 3, true) true)).card = 0 ∧ (W (child (2, 3, true) false)).card = 8 := by
  refine ⟨?_, card_W 1 3⟩
  simp [child, W]

example : (W (2, 3, false)).card = 0 := by
  simp [W]

/-- A zero-count instance is estimated exactly as `0`, with positive denominator. -/
example (m r p t : ℕ) :
    ∀ out ∈ (ProbComp.eval (R.estimate S (m, r, false) p t)).support, out.1 = 0 ∧ 0 < out.2 :=
  R.estimate_eq_zero S (by simp [W]) p t

/-- With witness length `0` no samples are drawn: the estimate is `1 / 1`. -/
example (p t : ℕ) : R.estimate S (0, 0, true) p t = pure (1, 1) := by
  simp [SelfReducible.estimate, R, mem_W]

/-! ### A sampler that is not almost uniform -/

/-- The sampler that always reports no witness is not an almost uniform sampler for the family:
on `(0, 1, true)` the event `{none}` has probability `1` instead of `0`. -/
example : ¬ IsFPAUS (encPair encUnary (encPair encUnary encBool)) W (fun _ _ => pure none) := by
  rintro ⟨-, h⟩
  have hW : (W (0, 1, true)).Nonempty := ⟨[true], mem_W.2 ⟨rfl, [true], rfl, rfl⟩⟩
  have h1 := (h (0, 1, true) 1).abs_toReal_sub_le (by norm_num) {none}
  have hpre : (some : List Bool → Option (List Bool)) ⁻¹' {none} = ∅ := by
    ext
    simp
  rw [uniformWitness_of_nonempty hW, PMF.toOuterMeasure_map_apply, hpre,
    MeasureTheory.measure_empty] at h1
  norm_num at h1

/-! ### Approximate counting gives almost uniform sampling -/

/-- The exact counter: the number of witnesses, over `1`. -/
private noncomputable def exactCounter (x : ℕ × ℕ × Bool) (_ _ : ℕ) : ProbComp (ℕ × ℕ) :=
  pure ((W x).card, 1)

private theorem approxWithin_exact (c p : ℕ) : ApproxWithin c p c 1 :=
  ⟨one_pos, by simp only [Nat.cast_one, div_one, sub_self, abs_zero]; positivity⟩

private theorem exactCounter_approx (x : ℕ × ℕ × Bool) (p t : ℕ) :
    1 - (1 / 2 : ℝ) ^ t ≤ ((ProbComp.eval (exactCounter x p t)).toOuterMeasure
      {out | ApproxWithin (W x).card p out.1 out.2}).toReal := by
  simp only [exactCounter, ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq,
    approxWithin_exact, ↓reduceIte, ENNReal.toReal_one]
  have : (0 : ℝ) ≤ (1 / 2) ^ t := by positivity
  linarith

private theorem goodEstimate_exact (p : ℕ) (x : ℕ × ℕ × Bool) :
    R.GoodEstimate p x ((W x).card, 1) :=
  ⟨approxWithin_exact _ _, fun _ => by simp⟩

/-- The sampler built from the exact counter is almost uniform, for every instance and accuracy. -/
example (x : ℕ × ℕ × Bool) (q : ℕ) :
    Interactive.CloseTo (ProbComp.eval (R.sampler exactCounter x q)) (uniformWitness (W x))
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ q)) :=
  R.closeTo_sampler (fun p t _ y => exactCounter_approx y p t) x q

/-- The round trip: the FPRAS obtained from the exact sampler gives back a sampler with the output
law of an almost uniform sampler. -/
example (x : ℕ × ℕ × Bool) (q : ℕ) :
    Interactive.CloseTo (ProbComp.eval (R.sampler (R.estimate S) x q)) (uniformWitness (W x))
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ q)) :=
  R.closeTo_sampler_of_isFPRAS (R.isFPRAS_of_isFPAUS isFPAUS_S) x q

/-- On a dead instance the target law is the point mass at `none`. -/
example (q : ℕ) :
    Interactive.CloseTo (ProbComp.eval (R.sampler exactCounter (2, 3, false) q)) (PMF.pure none)
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ q)) := by
  have h := R.closeTo_sampler (fun p t _ y => exactCounter_approx y p t) (2, 3, false) q
  rwa [show W (2, 3, false) = ∅ by simp [W], uniformWitness_empty] at h

/-- At the exact root estimate `4 / 1` of `(1, 2, true)`, a trial rejects with probability at most
`7 / 8`. -/
example (q : ℕ) : ProbComp.eval (R.trial exactCounter (1, 2, true) q (4, 1)) none ≤ 7 / 8 := by
  have he := goodEstimate_exact (SelfReducible.counterAccuracy (R.len (1, 2, true))) (1, 2, true)
  rw [card_W] at he
  exact R.eval_trial_none_le (fun y => exactCounter_approx y _ _) he
    ⟨[false, false, false], mem_W.2 ⟨rfl, [false, false], rfl, rfl⟩⟩

/-- The estimate `0 / 1` of the four witnesses of `(1, 2, true)` is not within relative error
`1 / 2`. -/
example : ¬ R.GoodEstimate 2 (1, 2, true) (0, 1) := by
  rintro ⟨⟨-, h⟩, -⟩
  rw [card_W] at h
  norm_num at h

/-- At witness length `0` a good estimate must be exact: `1 / 2` is within relative error `1` of
the single witness of `(0, 0, true)`, but it is not good. -/
example : ApproxWithin (W (0, 0, true)).card 1 1 2 ∧ ¬ R.GoodEstimate 1 (0, 0, true) (1, 2) := by
  rw [card_W]
  refine ⟨⟨by norm_num, by norm_num⟩, fun h => ?_⟩
  have h2 := h.2 rfl
  rw [card_W] at h2
  norm_num at h2

/-- The branching coin with two fair bits and thresholds `g₀ = 1`, `g₁ = 2` picks `true` with
probability `2 / 4`. -/
example : ProbComp.eval (SelfReducible.branch 2 1 2) (some true) = 2 / 4 := by
  rw [SelfReducible.eval_branch_eq (by norm_num) true]
  norm_num

/-- The counter that always answers `0` misses the accuracy hypothesis of `closeTo_sampler`. -/
example : ¬ SelfReducible.CounterAccurate W (fun _ _ _ => pure (0, 1)) 2 1 := by
  intro h
  have h1 := h (0, 1, true)
  have hn : ¬ ApproxWithin (W (0, 1, true)).card 2 0 1 := by
    rw [card_W]
    rintro ⟨-, h⟩
    norm_num at h
  simp only [ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq, hn,
    ↓reduceIte, ENNReal.toReal_zero] at h1
  norm_num at h1

end ComplexityTests.SamplingCounting
