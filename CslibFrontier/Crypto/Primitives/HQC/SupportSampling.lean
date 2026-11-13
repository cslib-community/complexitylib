/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.UniformNat
public import CslibFrontier.Languages.Probabilistic.Vector
public import CslibFrontier.Probability.PMF.UniformCollisionInsert
public import CslibFrontier.Probability.PMF.MultiplyHigh
public import CslibFrontier.Probability.PMF.DensityBounds
public import CslibFrontier.Foundations.Data.List.CollisionReplace
import Mathlib.Order.Interval.Finset.Nat

/-!
# HQC support sampling

`SampleSupport2` first draws independent fixed-width words, scales each word by multiply-high
into a shrinking interval, then processes the candidates in descending index order. A candidate
already present among the corrected later entries is replaced by its index.

The word source here consists of independent fair bits. Relating an XOF to that ideal source is
a separate cryptographic obligation. This module does not analyze decryption failure or security.

## Main definitions

* `Cslib.Crypto.HQC.resolveSupport`: the descending collision-replacement pass.
* `Cslib.Crypto.HQC.sampleSupportFrom`: draw every candidate before resolving collisions.
* `Cslib.Crypto.HQC.sampleSupport2`: the finite-bit algorithm, with a generalized word width.

## Main results

* `Cslib.Crypto.HQC.toFinset_scanSupport`: the source array pass agrees with the set resolver.
* `Cslib.Crypto.HQC.sampleSupport2_mem_powersetCard`: actual outputs have exactly the given weight.
* `Cslib.Crypto.HQC.eval_idealSupport`: ideal interval draws give uniform fixed-weight supports.
* `Cslib.Crypto.HQC.eval_sampleSupport2`: the exact actual law as a map of uniform word arrays.

## References

* [HQC specification, version 5.1][HQC2026], `SampleSupport2`, p. 19, and §6.2.3,
  Proposition 6.2.1, p. 65. The expression on algorithm line 5 is multiply-high, despite the
  accompanying comment mentioning reduction modulo the interval length.
-/

public section

namespace Cslib.Crypto.HQC

open Finset Probability
open scoped ENNReal

/-- Process candidates in descending index order. The recursive tail contains the already
corrected later entries when the current candidate is tested for collision. -/
@[expose] def resolveSupport (offset : ℕ) : {count : ℕ} → (Fin count → ℕ) → Finset ℕ
  | 0, _ => ∅
  | _ + 1, candidates =>
    (resolveSupport (offset + 1) (Fin.tail candidates)).collisionInsert offset (candidates 0)

/-- The source array pass, including the complete increasing scan through corrected later
entries. This retains the ordered array, whereas `resolveSupport` retains its support set. -/
@[expose] def scanSupport (offset : ℕ) : {count : ℕ} → (Fin count → ℕ) → (Fin count → ℕ)
  | 0, _ => Fin.elim0
  | _ + 1, candidates =>
    let later := scanSupport (offset + 1) (Fin.tail candidates)
    Fin.cons ((List.ofFn later).foldl
      (fun current x => if current = x then offset else current) (candidates 0)) later

/-- The source's nested array scan and membership-based descending resolver have exactly
the same output support, even for candidates outside the sampling range. -/
theorem toFinset_scanSupport {offset count : ℕ} (candidates : Fin count → ℕ) :
    (List.ofFn (scanSupport offset candidates)).toFinset = resolveSupport offset candidates := by
  induction count generalizing offset with
  | zero => simp [scanSupport, resolveSupport]
  | succ count ih =>
    simp only [scanSupport, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.toFinset_cons,
      List.foldl_replaceOnCollision]
    simp only [← List.mem_toFinset, ih]
    rfl

/-- In-range candidates produce exactly `count` distinct positions in the interval. -/
theorem resolveSupport_mem_powersetCard {n offset count : ℕ} (candidates : Fin count → ℕ)
    (h : ∀ j, offset + j.val ≤ candidates j ∧ candidates j < n) :
    resolveSupport offset candidates ∈ (Ico offset n).powersetCard count := by
  induction count generalizing offset with
  | zero => simp [resolveSupport]
  | succ count ih =>
    have ht := ih (Fin.tail candidates) (offset := offset + 1) (fun j => by
      simpa only [Fin.tail, Fin.val_succ, Nat.add_right_comm, Nat.add_assoc] using h j.succ)
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp ht
    have hp : offset ∉ resolveSupport (offset + 1) (Fin.tail candidates) := by
      intro hm
      have := (mem_Ico.mp (hsub hm)).1
      omega
    apply mem_powersetCard.mpr
    constructor
    · intro x hx
      have hx' := collisionInsert_subset hsub offset
        (show candidates 0 ∈ insert offset (Ico (offset + 1) n) from by
          simp only [mem_insert, mem_Ico]
          have := h 0
          simp only [Fin.val_zero, Nat.add_zero] at this
          omega) hx
      simp only [mem_insert, mem_Ico] at hx' ⊢
      have h0 := h 0
      simp only [Fin.val_zero, Nat.add_zero] at h0
      omega
    · rw [resolveSupport, card_collisionInsert hp, hcard]

/-- Draw the whole candidate array in increasing order, then resolve collisions in reverse.
The offset form permits induction on a suffix of the source array. -/
@[expose] def sampleSupportFrom (draw : ℕ → ProbComp ℕ) (offset count : ℕ) :
    ProbComp (Finset ℕ) :=
  resolveSupport offset <$> OracleComp.pi (fun j : Fin count => draw (offset + j.val))

/-- One step of the candidate array followed by the recursive suffix and reverse resolution. -/
theorem eval_sampleSupportFrom_succ (draw : ℕ → ProbComp ℕ) (offset count : ℕ) :
    ProbComp.eval (sampleSupportFrom draw offset (count + 1)) =
      (ProbComp.eval (draw offset)).bind fun r =>
        (ProbComp.eval (sampleSupportFrom draw (offset + 1) count)).map
          fun tail => tail.collisionInsert offset r := by
  simp only [sampleSupportFrom, ProbComp.eval_map, OracleComp.pi_succ,
    ProbComp.eval_bind, ProbComp.eval_map, Fin.val_zero, Nat.add_zero,
    PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1 with r : 1
  have hshift : (fun j : Fin count => draw (offset + j.succ.val)) =
      (fun j : Fin count => draw (offset + 1 + j.val)) := by
    funext j
    congr 1
    simp only [Fin.val_succ, Nat.add_right_comm, Nat.add_assoc]
  rw [hshift]
  rfl

/-- The source's line 5, using independent fair bits in place of the XOF words. -/
@[expose] noncomputable def sampleCandidate (width n offset : ℕ) : ProbComp ℕ := do
  let word ← ProbComp.sampleBinaryNat width
  return offset + word * (n - offset) / 2 ^ width

/-- `SampleSupport2` with `count` output positions. HQC uses `width = 32`. -/
@[expose] noncomputable def sampleSupport2 (width n count : ℕ) : ProbComp (Finset ℕ) :=
  sampleSupportFrom (sampleCandidate width n) 0 count

/-- Ideal uniform selection from the shrinking interval. The value outside a nonempty interval
is only a totality convention; all uniformity theorems require `offset + count ≤ n`. -/
@[expose] noncomputable def idealCandidate (n offset : ℕ) : ProbComp ℕ :=
  if h : offset < n then
    letI : NeZero (n - offset) := ⟨by omega⟩
    (fun j : Fin (n - offset) => offset + j.val) <$> ProbComp.uniform (Fin (n - offset))
  else pure offset

private def intervalEquiv {offset n : ℕ} (h : offset < n) :
    Fin (n - offset) ≃ ↥(Ico offset n) where
  toFun j := ⟨offset + j.val, mem_Ico.mpr ⟨by omega, by omega⟩⟩
  invFun j := ⟨j.val - offset, by have := mem_Ico.mp j.property; omega⟩
  left_inv j := by apply Fin.ext; dsimp; omega
  right_inv j := by apply Subtype.ext; dsimp; have := mem_Ico.mp j.property; omega

/-- The ideal candidate is uniform on the complete shrinking interval. -/
theorem eval_idealCandidate {n offset : ℕ} (h : offset < n) :
    ProbComp.eval (idealCandidate n offset) =
      PMF.uniformOfFinset (Ico offset n) (by exact ⟨offset, mem_Ico.mpr ⟨le_rfl, h⟩⟩) := by
  let : NeZero (n - offset) := ⟨by omega⟩
  let : Nonempty ↥(Ico offset n) := ⟨⟨offset, mem_Ico.mpr ⟨le_rfl, h⟩⟩⟩
  simp only [idealCandidate, dite_eq_left h, ProbComp.eval_map, ProbComp.eval_uniform]
  rw [← PMF.uniformOfFintype_finset_map_val]
  rw [← PMF.uniformOfFintype_map_equiv (intervalEquiv h), PMF.map_comp]
  rfl

/-- Independent exact uniform candidates give an exact uniform fixed-cardinality support. -/
theorem eval_idealSupport {n offset count : ℕ} (h : offset + count ≤ n) :
    ProbComp.eval (sampleSupportFrom (idealCandidate n) offset count) =
      PMF.uniformOfFinset ((Ico offset n).powersetCard count)
        (powersetCard_nonempty.mpr (by rw [Nat.card_Ico]; omega)) := by
  induction count generalizing offset with
  | zero =>
    ext S
    simp [sampleSupportFrom, resolveSupport, PMF.uniformOfFinset_apply, PMF.pure_apply]
  | succ count ih =>
    have hoff : offset < n := by omega
    have hrange : insert offset (Ico (offset + 1) n) = Ico offset n := by
      ext j
      simp only [mem_insert, mem_Ico]
      omega
    rw [eval_sampleSupportFrom_succ, ih (by omega), eval_idealCandidate hoff]
    change ((PMF.uniformOfFinset (Ico offset n) _).bind fun r =>
      (PMF.uniformOfFinset ((Ico (offset + 1) n).powersetCard count) _).bind
        fun U => _root_.PMF.pure (U.collisionInsert offset r)) = _
    rw [_root_.PMF.bind_comm]
    simpa only [hrange, PMF.map, Function.comp_def] using PMF.uniformOfFinset_collisionInsert
      (S := Ico (offset + 1) n) (p := offset) (k := count)
      (by simp) (by rw [Nat.card_Ico]; omega)

/-- A word consists of exactly `width` fair bits, and line 5 uses multiply-high. -/
theorem eval_sampleCandidate (width n offset : ℕ) :
    ProbComp.eval (sampleCandidate width n offset) =
      (PMF.uniformOfFintype (Fin (2 ^ width))).map
        (fun u => offset + u.val * (n - offset) / 2 ^ width) := by
  simp only [sampleCandidate, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_sampleBinaryNat, PMF.bind_map]
  rfl

/-- Every actual candidate is in its shrinking interval. -/
theorem sampleCandidate_mem_Ico {width n offset r : ℕ} (h : offset < n)
    (hr : r ∈ (ProbComp.eval (sampleCandidate width n offset)).support) :
    r ∈ Ico offset n := by
  rw [eval_sampleCandidate, PMF.mem_support_map_iff] at hr
  obtain ⟨u, _, rfl⟩ := hr
  have := Nat.mul_div_lt_of_lt (M := 2 ^ width) (d := n - offset)
    (by positivity) (by omega) u.isLt
  exact mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩

/-- The actual finite-bit sampler always returns exactly the requested number of positions. -/
theorem sampleSupport2_mem_powersetCard {width n count : ℕ} (h : count ≤ n)
    {S : Finset ℕ} (hS : S ∈ (ProbComp.eval (sampleSupport2 width n count)).support) :
    S ∈ (range n).powersetCard count := by
  rw [sampleSupport2, sampleSupportFrom, ProbComp.eval_map, PMF.mem_support_map_iff] at hS
  obtain ⟨candidates, hc, rfl⟩ := hS
  rw [ProbComp.mem_support_pi_iff] at hc
  have hr := resolveSupport_mem_powersetCard (n := n) (offset := 0) candidates fun j => by
    simpa only [Nat.zero_add, mem_Ico] using
      sampleCandidate_mem_Ico (by have := j.isLt; omega) (hc j)
  simpa only [Nat.Ico_zero_eq_range] using hr

/-- The deterministic output from a fixed array of bounded words. This is the formula on
line 5 followed by the descending collision pass, without any distributional idealization. -/
@[expose] def supportFromWords (width n : ℕ) {count : ℕ}
    (words : Fin count → Fin (2 ^ width)) : Finset ℕ :=
  resolveSupport 0 (fun j => j.val + (words j).val * (n - j.val) / 2 ^ width)

/-- Correctness holds for every bounded word array, independently of its distribution. -/
theorem supportFromWords_mem_powersetCard {width n count : ℕ} (h : count ≤ n)
    (words : Fin count → Fin (2 ^ width)) :
    supportFromWords width n words ∈ (range n).powersetCard count := by
  have hc (j : Fin count) : j.val < n := j.isLt.trans_le h
  have hr := resolveSupport_mem_powersetCard (n := n) (offset := 0)
    (fun j => j.val + (words j).val * (n - j.val) / 2 ^ width) fun j => by
      have hm := Nat.mul_div_lt_of_lt (M := 2 ^ width) (d := n - j.val)
        (by positivity) (by have := hc j; omega) (words j).isLt
      simp only [Nat.zero_add]
      exact ⟨Nat.le_add_right _ _, by have := hc j; omega⟩
  simpa only [supportFromWords, Nat.Ico_zero_eq_range] using hr

/-- At full weight every word array produces the entire support. -/
theorem supportFromWords_full (width n : ℕ) (words : Fin n → Fin (2 ^ width)) :
    supportFromWords width n words = range n := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp (supportFromWords_mem_powersetCard le_rfl words)
  exact eq_of_subset_of_card_le hsub (by simpa only [card_range, hcard] using (le_refl n))

/-- At weight zero the program makes no random choices and returns the empty support. -/
theorem sampleSupport2_zero (width n : ℕ) :
    sampleSupport2 width n 0 = pure ∅ := by
  simp [sampleSupport2, sampleSupportFrom, resolveSupport]

/-- The actual algorithm is exactly its deterministic word-array map under independent
uniform words. In particular, this law retains the multiply-high bias. -/
theorem eval_sampleSupport2 (width n count : ℕ) :
    ProbComp.eval (sampleSupport2 width n count) =
      (PMF.uniformOfFintype (Fin count → Fin (2 ^ width))).map (supportFromWords width n) := by
  rw [sampleSupport2, sampleSupportFrom, ProbComp.eval_map]
  have hc : ProbComp.eval (OracleComp.pi
      (fun j : Fin count => sampleCandidate width n (0 + j.val))) =
      ProbComp.eval (OracleComp.pi (fun j : Fin count =>
        (fun u : Fin (2 ^ width) => j.val + u.val * (n - j.val) / 2 ^ width) <$>
          ProbComp.uniform (Fin (2 ^ width)))) := by
    apply ProbComp.eval_pi_congr
    intro j
    simp only [eval_sampleCandidate, ProbComp.eval_map, ProbComp.eval_uniform, Nat.zero_add]
  rw [hc, ProbComp.eval_pi_map, ProbComp.eval_pi_uniform, PMF.map_comp]
  rfl

end Cslib.Crypto.HQC
