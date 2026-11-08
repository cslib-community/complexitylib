/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Probability.BitString
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Complexity.Probability.PMF.Bind
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Discrete distribution generating trees

A discrete distribution generating (DDG) tree reads independent fair bits and eventually commits to
an outcome. Following [KnuthYao1976] and [CoverThomas2006], Section 5.11, it is a possibly infinite
complete binary tree whose leaves carry outcomes. Here such a tree is presented by its prefix
labelling `output : List Bool → Option α`: `output w = some a` means that the walk along `w` has
reached a leaf labelled `a`, and `none` means it is still at an internal node. Leaves are absorbing.

Running on `n` fair bits gives `run T n : PMF (Option α)`. `run T n none` is the probability
`P(T > n)` that more than `n` flips are needed. The output law is the monotone limit
`outputProb T a = ⨆ n, run T n (some a)`. The expected number of flips is the tail sum
`expectedFlips T = ∑ₙ P(T > n)`. `expectedFlips_eq_tsum_mul` identifies it with
`∑ₖ (k + 1) P(T = k + 1)` whenever the tree halts almost surely, as every tree generating a finite
distribution does (`tendsto_run_none_of_generates`). `expectedFlips_eq_top` covers trees that
fail to halt with positive probability.

## Main definitions

* `Cslib.Probability.DDGTree`: binary decision trees over fair bits with outcome-labelled leaves.
* `Cslib.Probability.DDGTree.run`: the outcome after reading `n` fair bits, or `none`.
* `Cslib.Probability.DDGTree.outputProb`, `.Generates`: the distribution of the eventual output.
* `Cslib.Probability.DDGTree.expectedFlips`: the expected number of fair bits read.
* `Cslib.Probability.DDGTree.ofCounts`: a tree with prescribed numbers of leaves at each depth.

## Main results

* `Cslib.Probability.DDGTree.run_ofCounts`: `ofCounts t` stops with outcome `a` within `n` flips
  with probability `t n a / 2 ^ n`, under the Kraft-type budget `∑ₐ t n a ≤ 2 ^ n`.
* `Cslib.Probability.DDGTree.expectedFlips_eq_tsum_mul`: tail-sum formula for the expected
  stopping time.
* `Cslib.Probability.DDGTree.tendsto_run_none_of_generates`: generators of finite distributions halt
  almost surely.

## References

* [D. E. Knuth, A. C. Yao, *The complexity of nonuniform random number generation*][KnuthYao1976].
* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], Section 5.11.
-/

public section

open scoped ENNReal
open Filter Topology

namespace Cslib.Probability

/-- A discrete distribution generating tree, given by its prefix labelling. `output w = some a`
when reading the bits `w` reaches a leaf labelled `a`, and `output w = none` while the walk is at an
internal node. Leaves are absorbing: further bits do not change the outcome. The tree may be
infinite. -/
@[ext] structure DDGTree (α : Type*) where
  /-- The outcome reached after reading a finite bit string, if any. -/
  output : List Bool → Option α
  /-- Once a leaf is reached, later bits are ignored. -/
  output_append_singleton : ∀ (w : List Bool) (a : α) (b : Bool),
    output w = some a → output (w ++ [b]) = some a

namespace DDGTree

variable {α : Type*}

/-- The result of running the tree on `n` independent fair bits: `some a` if it has reached a leaf
labelled `a`, and `none` if it needs more than `n` bits. -/
@[expose] noncomputable def run (T : DDGTree α) (n : ℕ) : PMF (Option α) :=
  (BitString.uniformList n).map T.output

/-- Probability that the tree eventually outputs `a`. -/
@[expose] noncomputable def outputProb (T : DDGTree α) (a : α) : ℝ≥0∞ :=
  ⨆ n, T.run n (some a)

/-- The tree generates `p` when its eventual output has law `p`. -/
@[expose] def Generates (T : DDGTree α) (p : PMF α) : Prop :=
  ∀ a, T.outputProb a = p a

/-- Expected number of fair bits read before a leaf is reached: the tail sum `∑ₙ P(T > n)` of the
stopping time `T`. It is `⊤` when the tree fails to halt with positive probability. -/
@[expose] noncomputable def expectedFlips (T : DDGTree α) : ℝ≥0∞ :=
  ∑' n, T.run n none

/-- A leaf is never left. -/
theorem output_append {T : DDGTree α} {w : List Bool} {a : α} (h : T.output w = some a)
    (v : List Bool) : T.output (w ++ v) = some a := by
  induction v using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton v b ih =>
    rw [← List.append_assoc]
    exact T.output_append_singleton _ a b ih

/-- If the root is a leaf, every bit string reaches it. -/
theorem output_eq_of_output_nil {T : DDGTree α} {a : α} (h : T.output [] = some a)
    (w : List Bool) : T.output w = some a := by
  simpa using output_append h w

/-- The subtree reached after reading `b` first. -/
@[expose] def child (T : DDGTree α) (b : Bool) : DDGTree α where
  output w := T.output (b :: w)
  output_append_singleton w a c h := by
    simpa using T.output_append_singleton (b :: w) a c h

@[simp] theorem child_output (T : DDGTree α) (b : Bool) (w : List Bool) :
    (T.child b).output w = T.output (b :: w) := rfl

/-- With no bits, the tree reports its root. -/
@[simp] theorem run_zero (T : DDGTree α) : T.run 0 = PMF.pure (T.output []) := by
  simp [run]

/-- One more bit: flip a fair coin, then run the chosen subtree. -/
theorem run_succ (T : DDGTree α) (n : ℕ) :
    T.run (n + 1) = (PMF.uniformOfFintype Bool).bind (fun b => (T.child b).run n) := by
  simp only [run, BitString.uniformList_succ, PMF.map_bind, PMF.map_comp]
  rfl

/-- A tree whose root is a leaf labelled `a` outputs `a` without reading any bit. -/
theorem run_eq_pure_of_output_nil {T : DDGTree α} {a : α} (h : T.output [] = some a) (n : ℕ) :
    T.run n = PMF.pure (some a) := by
  have hT : T.output = Function.const (List Bool) (some a) := funext (output_eq_of_output_nil h)
  rw [run, hT, PMF.map_const]

/-- Probabilities of a fixed outcome increase with the number of bits. -/
theorem run_le_run_succ (T : DDGTree α) (n : ℕ) (a : α) :
    T.run n (some a) ≤ T.run (n + 1) (some a) := by
  rw [run, run, BitString.uniformList_snoc, PMF.map_bind, PMF.map_apply, PMF.bind_apply]
  refine tsum_le_tsum fun w => ?_
  split_ifs with hw
  · rw [PMF.map_comp, PMF.map_apply]
    have h : ∀ b : Bool, some a = T.output (w ++ [b]) := fun b =>
      (T.output_append_singleton w a b hw.symm).symm
    simp only [Function.comp_apply, tsum_fintype, PMF.uniformOfFintype_apply,
      Fintype.card_bool, Fintype.sum_bool]
    rw [ite_eq_left (h true), ite_eq_left (h false), Nat.cast_ofNat, ENNReal.inv_two_add_inv_two,
      mul_one]
  · exact bot_le

theorem monotone_run (T : DDGTree α) (a : α) : Monotone fun n => T.run n (some a) :=
  monotone_nat_of_le_succ fun n => T.run_le_run_succ n a

theorem run_le_outputProb (T : DDGTree α) (n : ℕ) (a : α) : T.run n (some a) ≤ T.outputProb a :=
  le_iSup (fun n => T.run n (some a)) n

theorem tendsto_run_outputProb (T : DDGTree α) (a : α) :
    Tendsto (fun n => T.run n (some a)) atTop (𝓝 (T.outputProb a)) :=
  tendsto_atTop_iSup (T.monotone_run a)

/-- After `n` fair bits every event has dyadic probability `c / 2 ^ n`. -/
theorem exists_run_eq_div (T : DDGTree α) (n : ℕ) (o : Option α) :
    ∃ c : ℕ, T.run n o = c / 2 ^ n := by
  classical
  exact ⟨_, BitString.uniformList_map_apply T.output n o⟩

theorem run_none_add_sum [Fintype α] (T : DDGTree α) (n : ℕ) :
    T.run n none + ∑ a, T.run n (some a) = 1 := by
  rw [← Fintype.sum_option (fun o => T.run n o),
    ← tsum_fintype (L := SummationFilter.unconditional _), PMF.tsum_coe]

/-- The probability `P(T > n)` of needing more than `n` bits is nonincreasing in `n`. -/
theorem run_succ_none_le (T : DDGTree α) (n : ℕ) : T.run (n + 1) none ≤ T.run n none := by
  rw [run, run, BitString.uniformList_snoc, PMF.map_bind, PMF.map_apply, PMF.bind_apply]
  refine tsum_le_tsum fun w => ?_
  split_ifs with hw
  · refine mul_le_of_le_one_right' ?_
    rw [PMF.map_comp, PMF.map_apply]
    exact (tsum_le_tsum (g := fun b => PMF.uniformOfFintype Bool b) fun b => by
      split_ifs <;> simp).trans (PMF.tsum_coe (PMF.uniformOfFintype Bool)).le
  · rw [PMF.map_comp, PMF.map_apply]
    have h : ∀ b : Bool, ¬ none = (T.output ∘ fun bit => w ++ [bit]) b := by
      intro b hb
      cases hw' : T.output w with
      | none => exact hw hw'.symm
      | some a =>
        rw [Function.comp_apply, T.output_append_singleton w a b hw'] at hb
        simp at hb
    simp only [h, ite_false, tsum_zero, mul_zero, le_refl]

theorem antitone_run_none (T : DDGTree α) : Antitone fun n => T.run n none :=
  antitone_nat_of_succ_le T.run_succ_none_le

/-- A tree generating a distribution on a finite type halts almost surely. -/
theorem tendsto_run_none_of_generates [Finite α] {T : DDGTree α} {p : PMF α}
    (hT : T.Generates p) : Tendsto (fun n => T.run n none) atTop (𝓝 0) := by
  have := Fintype.ofFinite α
  have hsum : Tendsto (fun n => ∑ a, T.run n (some a)) atTop (𝓝 1) := by
    have h := tendsto_finsetSum (Finset.univ : Finset α) fun a _ => T.tendsto_run_outputProb a
    have hT' : ∀ a, T.outputProb a = p a := hT
    simp only [hT'] at h
    rwa [← tsum_fintype (L := SummationFilter.unconditional _), PMF.tsum_coe] at h
  have hfin : ∀ n, ∑ a, T.run n (some a) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top ENNReal.one_ne_top ((T.run_none_add_sum n) ▸ le_add_self)
  have heq : (fun n => T.run n none) = fun n => 1 - ∑ a, T.run n (some a) := funext fun n =>
    ENNReal.eq_sub_of_add_eq (hfin n) (T.run_none_add_sum n)
  rw [heq, ← tsub_self (1 : ℝ≥0∞)]
  exact ENNReal.Tendsto.sub tendsto_const_nhds hsum (Or.inl ENNReal.one_ne_top)

/-! ## The tail-sum formula -/

section TailSum

variable {f : ℕ → ℝ≥0∞}

private theorem tsum_tsub_succ (hf : Antitone f) (h0 : Tendsto f atTop (𝓝 0)) (n : ℕ) :
    ∑' k, (f (n + k) - f (n + k + 1)) = f n := by
  have hsum : ∀ m, ∑ k ∈ Finset.range m, (f (n + k) - f (n + k + 1)) = f n - f (n + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, ← add_assoc n m 1,
        tsub_add_tsub_cancel (hf (show n ≤ n + m by omega)) (hf (show n + m ≤ n + m + 1 by omega))]
  have hlim : Tendsto (fun m => f n - f (n + m)) atTop (𝓝 (f n - 0)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds ((h0.comp (tendsto_add_atTop_nat n)).congr fun m => by
      rw [Function.comp_apply, add_comm]) (Or.inr ENNReal.zero_ne_top)
  rw [tsub_zero] at hlim
  refine tendsto_nhds_unique ?_ hlim
  simp only [← hsum]
  exact ENNReal.tendsto_nat_tsum _

private theorem tsum_eq_tsum_mul_tsub (hf : Antitone f) (h0 : Tendsto f atTop (𝓝 0)) :
    ∑' n, f n = ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * (f k - f (k + 1)) := by
  set d := fun k => f k - f (k + 1) with hd
  calc ∑' n, f n = ∑' n, ∑' k, d (n + k) := by
        refine tsum_congr fun n => (tsum_tsub_succ hf h0 n).symm
    _ = ∑' p : ℕ × ℕ, d (p.1 + p.2) := tsum_prod.symm
    _ = ∑' x : Σ j : ℕ, Finset.antidiagonal j, d (x.2.1.1 + x.2.1.2) :=
        (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
          (fun p : ℕ × ℕ => d (p.1 + p.2))).symm
    _ = ∑' j, ∑' y : Finset.antidiagonal j, d (y.1.1 + y.1.2) := tsum_sigma' _
    _ = ∑' j : ℕ, ((j : ℝ≥0∞) + 1) * d j := by
        refine tsum_congr fun j => ?_
        rw [Finset.tsum_subtype (Finset.antidiagonal j) (fun y : ℕ × ℕ => d (y.1 + y.2)),
          Finset.sum_congr rfl fun y hy => by rw [Finset.mem_antidiagonal.mp hy],
          Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
        push_cast
        ring

end TailSum

/-- For a tree that halts almost surely, `expectedFlips` is the expectation
`∑ₖ (k + 1) P(T = k + 1)` of the stopping time, where
`P(T = k + 1) = P(T > k) - P(T > k + 1)`. -/
theorem expectedFlips_eq_tsum_mul (T : DDGTree α)
    (h : Tendsto (fun n => T.run n none) atTop (𝓝 0)) :
    T.expectedFlips = ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * (T.run k none - T.run (k + 1) none) :=
  tsum_eq_tsum_mul_tsub T.antitone_run_none h

/-- A tree that fails to halt with positive probability reads infinitely many bits in
expectation. -/
theorem expectedFlips_eq_top (T : DDGTree α) (h : ⨅ n, T.run n none ≠ 0) :
    T.expectedFlips = ⊤ :=
  top_unique <| (ENNReal.tsum_const_eq_top_of_ne_zero h).symm.le.trans <|
    tsum_le_tsum fun n => iInf_le (fun n => T.run n none) n

/-! ## Realizing a depth profile -/

/-- Assign the first `d a₁` indices to `a₁`, the next `d a₂` to `a₂`, and so on. -/
private def pick (d : α → ℕ) : List α → ℕ → Option α
  | [], _ => none
  | a :: l, i => if i < d a then some a else pick d l (i - d a)

private theorem pick_lt {d : α → ℕ} {l : List α} {i : ℕ} {a : α} (h : pick d l i = some a) :
    i < (l.map d).sum := by
  induction l generalizing i with
  | nil => simp [pick] at h
  | cons b l ih =>
    simp only [pick] at h
    simp only [List.map_cons, List.sum_cons]
    split_ifs at h with hi
    · omega
    · have := ih h; omega

private theorem sum_pick [DecidableEq α] (d : α → ℕ) {l : List α} (hl : l.Nodup) (a : α) {N : ℕ}
    (hN : (l.map d).sum ≤ N) :
    ∑ i ∈ Finset.range N, (if pick d l i = some a then 1 else 0) = if a ∈ l then d a else 0 := by
  induction l generalizing N with
  | nil => simp [pick]
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons] at hN
    rw [List.nodup_cons] at hl
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show d b ≤ N by omega)
    rw [Finset.sum_range_add]
    have h1 : ∑ i ∈ Finset.range (d b), (if pick d (b :: l) i = some a then 1 else 0) =
        if b = a then d b else 0 := by
      split_ifs with hba
      · subst hba
        rw [Finset.sum_congr rfl (g := fun _ => 1) fun i hi => by
          simp [pick, Finset.mem_range.mp hi]]
        simp
      · rw [Finset.sum_eq_zero]
        intro i hi
        simp [pick, Finset.mem_range.mp hi, hba]
    have h2 : ∑ i ∈ Finset.range k, (if pick d (b :: l) (d b + i) = some a then 1 else 0) =
        if a ∈ l then d a else 0 := by
      rw [← ih hl.2 (N := k) (by omega)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [pick]
    rw [h1, h2]
    by_cases hba : b = a
    · subst hba; simp [hl.1]
    · simp [hba, Ne.symm hba]

/-- Total number of leaves at depth `k`. -/
private def total [Fintype α] (t : ℕ → α → ℕ) (k : ℕ) : ℕ := ∑ a, t k a

/-- Label of position `y` at depth `k`: `none` for an internal node. Depth `k` lists the old leaves
(each duplicated from depth `k - 1`), then the new leaves, then the internal nodes. -/
private noncomputable def label [Fintype α] (t : ℕ → α → ℕ) : ℕ → ℕ → Option α
  | 0, y => pick (t 0) Finset.univ.toList y
  | k + 1, y =>
    if y < 2 * total t k then label t k (y / 2)
    else pick (fun a => t (k + 1) a - 2 * t k a) Finset.univ.toList (y - 2 * total t k)

section Profile

variable [Fintype α] {t : ℕ → α → ℕ}

private theorem total_succ (hmono : ∀ k a, 2 * t k a ≤ t (k + 1) a) (k : ℕ) :
    total t (k + 1) = 2 * total t k + ∑ a, (t (k + 1) a - 2 * t k a) := by
  simp only [total, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := hmono k a
  omega

private theorem label_lt (hmono : ∀ k a, 2 * t k a ≤ t (k + 1) a) {k y : ℕ} {a : α}
    (h : label t k y = some a) : y < total t k := by
  induction k generalizing y with
  | zero =>
    have := pick_lt h
    rwa [Finset.sum_map_toList] at this
  | succ k ih =>
    simp only [label] at h
    rw [total_succ hmono]
    split_ifs at h with hy
    · omega
    · have := pick_lt h
      rw [Finset.sum_map_toList] at this
      omega

private theorem sum_range_two_mul_div (f : ℕ → ℕ) (M : ℕ) :
    ∑ i ∈ Finset.range (2 * M), f (i / 2) = 2 * ∑ i ∈ Finset.range M, f i := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    have h1 : (2 * M + 1) / 2 = M := by omega
    have h2 : 2 * M / 2 = M := by omega
    rw [h1, h2]
    ring

private theorem label_succ_add (k i : ℕ) :
    label t (k + 1) (2 * total t k + i) =
      pick (fun a => t (k + 1) a - 2 * t k a) Finset.univ.toList i := by
  simp [label]

private theorem label_succ_of_lt {k y : ℕ} (hy : y < 2 * total t k) :
    label t (k + 1) y = label t k (y / 2) := by
  simp [label, hy]

private theorem sum_label [DecidableEq α] (hmono : ∀ k a, 2 * t k a ≤ t (k + 1) a) (k : ℕ)
    (a : α) :
    ∑ y ∈ Finset.range (total t k), (if label t k y = some a then 1 else 0) = t k a := by
  induction k with
  | zero =>
    change ∑ y ∈ Finset.range (total t 0),
      (if pick (t 0) Finset.univ.toList y = some a then 1 else 0) = t 0 a
    rw [sum_pick _ (Finset.nodup_toList _) a (by rw [Finset.sum_map_toList]; exact le_rfl)]
    simp
  | succ k ih =>
    rw [total_succ hmono, Finset.sum_range_add]
    have h1 : ∑ y ∈ Finset.range (2 * total t k), (if label t (k + 1) y = some a then 1 else 0) =
        2 * t k a := by
      rw [← ih, ← sum_range_two_mul_div]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [label_succ_of_lt (Finset.mem_range.mp hy)]
    have h2 : ∑ i ∈ Finset.range (∑ a, (t (k + 1) a - 2 * t k a)),
        (if label t (k + 1) (2 * total t k + i) = some a then 1 else 0) =
        t (k + 1) a - 2 * t k a := by
      simp only [label_succ_add]
      rw [sum_pick (fun a => t (k + 1) a - 2 * t k a) (Finset.nodup_toList _) a
        (by rw [Finset.sum_map_toList])]
      simp
    rw [h1, h2]
    have := hmono k a
    omega

private theorem label_succ_of_eq_some (hmono : ∀ k a, 2 * t k a ≤ t (k + 1) a) {k x : ℕ} {a : α}
    (h : label t k x = some a) (b : Bool) : label t (k + 1) (2 * x + b.toNat) = some a := by
  have hx := label_lt hmono h
  have hlt : 2 * x + b.toNat < 2 * total t k := by
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  rw [label_succ_of_lt hlt]
  have : (2 * x + b.toNat) / 2 = x := by
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  rwa [this]

/-- Walk from position `x` at depth `k`, reading bits. -/
private noncomputable def walk (t : ℕ → α → ℕ) : ℕ → ℕ → List Bool → Option α
  | k, x, [] => label t k x
  | k, x, b :: w => (label t k x).or (walk t (k + 1) (2 * x + b.toNat) w)

private theorem walk_of_label_eq_some {k x : ℕ} {a : α} (h : label t k x = some a)
    (w : List Bool) : walk t k x w = some a := by
  cases w with
  | nil => exact h
  | cons b w => simp [walk, h]

private theorem walk_append_singleton {k x : ℕ} {w : List Bool} {a : α}
    (h : walk t k x w = some a) (b : Bool) : walk t k x (w ++ [b]) = some a := by
  induction w generalizing k x with
  | nil =>
    simp only [walk] at h
    simp [walk, h]
  | cons c w ih =>
    simp only [walk] at h
    cases hl : label t k x with
    | some a' =>
      rw [hl, Option.some_or] at h
      rw [List.cons_append, walk_of_label_eq_some hl, h]
    | none =>
      rw [hl, Option.none_or] at h
      simp [walk, hl, ih h]

/-- The subtree at position `x` of depth `k`. -/
private noncomputable def node (t : ℕ → α → ℕ) (k x : ℕ) : DDGTree α where
  output := walk t k x
  output_append_singleton _ _ b h := walk_append_singleton h b

private theorem walk_cons (hmono : ∀ k a, 2 * t k a ≤ t (k + 1) a) (k x : ℕ) (b : Bool)
    (w : List Bool) : walk t k x (b :: w) = walk t (k + 1) (2 * x + b.toNat) w := by
  cases hl : label t k x with
  | some a =>
    rw [walk_of_label_eq_some hl, walk_of_label_eq_some (label_succ_of_eq_some hmono hl b)]
  | none => simp [walk, hl]

private theorem child_node (hmono : ∀ k a, 2 * t k a ≤ t (k + 1) a) (k x : ℕ) (b : Bool) :
    (node t k x).child b = node t (k + 1) (2 * x + b.toNat) := by
  ext1
  funext w
  exact walk_cons hmono k x b w

private theorem run_node [DecidableEq α] (hmono : ∀ k a, 2 * t k a ≤ t (k + 1) a) (n k x : ℕ)
    (a : α) :
    (node t k x).run n (some a) =
      (∑ i ∈ Finset.range (2 ^ n),
        (if label t (k + n) (x * 2 ^ n + i) = some a then 1 else 0) : ℕ) * 2⁻¹ ^ n := by
  induction n generalizing k x with
  | zero =>
    simp only [run_zero, PMF.pure_apply, pow_zero, mul_one, Finset.range_one,
      Finset.sum_singleton, add_zero]
    have hout : (node t k x).output [] = label t k x := rfl
    rw [hout]
    by_cases h : label t k x = some a
    · simp [h]
    · simp [h, Ne.symm h]
  | succ n ih =>
    rw [run_succ, PMF.bind_apply, tsum_fintype (L := SummationFilter.unconditional _),
      Fintype.sum_bool, child_node hmono, child_node hmono, ih, ih]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Bool.toNat_true,
      Bool.toNat_false, add_zero]
    rw [show 2 ^ (n + 1) = 2 ^ n + 2 ^ n by ring, Finset.sum_range_add, Nat.cast_add]
    have e1 : k + 1 + n = k + (n + 1) := by ring
    have e2 : ∀ i, (2 * x + 1) * 2 ^ n + i = x * (2 ^ n + 2 ^ n) + (2 ^ n + i) := fun i => by
      ring
    have e3 : ∀ i, 2 * x * 2 ^ n + i = x * (2 ^ n + 2 ^ n) + i := fun i => by ring
    simp only [e1, e2, e3, Nat.cast_ofNat]
    ring

/-- A tree with `t k a` leaves labelled `a` at depth at most `k`. The depth-`k` positions are
ordered so that leaves inherited from depth `k - 1` come first, then new leaves, then internal
nodes. -/
noncomputable def ofCounts (t : ℕ → α → ℕ) : DDGTree α := node t 0 0

/-- If the counts double along each level (`2 * t k a ≤ t (k + 1) a`, i.e. leaves are inherited)
and fit at every depth (`∑ₐ t k a ≤ 2 ^ k`, a Kraft-type budget), then `ofCounts t` reaches a leaf
labelled `a` within `n` flips with probability exactly `t n a / 2 ^ n`. -/
theorem run_ofCounts (hmono : ∀ k a, 2 * t k a ≤ t (k + 1) a)
    (hkraft : ∀ k, ∑ a, t k a ≤ 2 ^ k) (n : ℕ) (a : α) :
    (ofCounts t).run n (some a) = t n a / 2 ^ n := by
  classical
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (show total t n ≤ 2 ^ n from hkraft n)
  rw [ofCounts, run_node hmono, hr, Finset.sum_range_add]
  simp only [zero_add, zero_mul]
  rw [sum_label hmono, Finset.sum_eq_zero, add_zero, ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow,
    mul_comm]
  · intro i _
    rw [ite_eq_right]
    intro h
    have := label_lt hmono h
    omega

end Profile

end DDGTree

end Cslib.Probability
