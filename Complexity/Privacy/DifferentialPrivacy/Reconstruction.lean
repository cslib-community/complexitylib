/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Privacy.DifferentialPrivacy.Hamming
import Complexity.Foundations.Data.BitString.Flip

/-!
# Reconstruction attacks

A database holds one secret bit per person, `d : ι → Bool`. A subset-count query asks for the
number of ones among the rows in a set `S` (`subsetCount d S`). Answers `r S` have distortion at
most `E` when `|r S - subsetCount d S| ≤ E` for every `S` (`SubsetCountsWithin r d E`).

**Theorem ([DworkRoth2014, Theorem 8.1]).** Answers to all subset-count queries with distortion
at most `E` let an adversary reconstruct the database in all but `4 E` positions. The adversary
(`reconstruct`) outputs any database whose subset counts are all within `E` of the answers; the
true database is a candidate, so one exists. Two databases consistent with the same answers
differ in at most `4 E` rows (`hammingDist_le_of_subsetCountsWithin`). Dwork and Roth credit this
attack to Dinur and Nissim [DworkRoth2014, §8.3].

The consequence for differential privacy is a standard derivation, following Dwork and Roth's
remark that lower bounds for preventing blatant non-privacy apply to every differentially private
mechanism [DworkRoth2014, §8.1]. Let `G` be `(ε, δ)`-private for Hamming adjacency with outputs
in `ι → Bool`. Flipping the secret bit of row `i` gives an adjacent database, so `G` guesses that
bit correctly with probability at most `(exp ε + δ) / (1 + exp ε)` on average over a uniformly
random database. Summed over the rows, the expected number of correct bits is at most
`n (exp ε + δ) / (1 + exp ε)` on average (`DifferentiallyPrivate.mul_sum_sum_toOuterMeasure_le`),
for `n` rows. If `G` lands within Hamming distance `t` of the truth with probability at least
`q` on every database, then `(1 + exp ε) (n - t) q ≤ n (exp ε + δ)`
(`DifferentiallyPrivate.mul_card_sub_mul_le`).

Applied to the reconstruction adversary: if an `(ε, δ)`-private mechanism answers all `2 ^ n`
subset-count queries with distortion at most `E` with probability at least `q` on every database,
then `(1 + exp ε) (n - 4 E) q ≤ n (exp ε + δ)`
(`DifferentiallyPrivate.mul_card_sub_mul_le_of_subsetCountsWithin`). If the answers have
distortion at most `E` with probability one on every database, then
`E ≥ n (1 - δ) / (4 (1 + exp ε))`
(`DifferentiallyPrivate.card_mul_one_sub_le_of_subsetCountsWithin`), which is linear in `n`.
This bounds the distortion that can be guaranteed uniformly over all databases, not the distortion
on a particular one: a constant mechanism is `(0, 0)`-private and answers exactly on the database
it was built from. In particular, exact answers on every database are not `(ε, δ)`-private for any
`δ < 1` once `n ≥ 1`.

## Main definitions

* `Cslib.Privacy.subsetCount`: the true answer to a subset-count query.
* `Cslib.Privacy.SubsetCountsWithin`: answers to all subset-count queries with distortion at most
  `E`.
* `Cslib.Privacy.reconstruct`: the reconstruction adversary of [DworkRoth2014, Theorem 8.1].

## Main results

* `Cslib.Privacy.hammingDist_le_of_subsetCountsWithin`,
  `Cslib.Privacy.hammingDist_reconstruct_le`: reconstruction to within `4 E` positions
  [DworkRoth2014, Theorem 8.1].
* `Cslib.Privacy.DifferentiallyPrivate.mul_sum_sum_toOuterMeasure_le`: a private mechanism
  guesses few secret bits on average.
* `Cslib.Privacy.DifferentiallyPrivate.mul_card_sub_mul_le`: a private mechanism cannot reconstruct
  a database to within `t` positions with high probability.
* `Cslib.Privacy.DifferentiallyPrivate.mul_card_sub_mul_le_of_subsetCountsWithin`,
  `Cslib.Privacy.DifferentiallyPrivate.card_mul_one_sub_le_of_subsetCountsWithin`: private answers
  to all subset-count queries have distortion linear in the number of rows.

## References

* [DworkRoth2014]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

universe v

variable {ι : Type*}

/-- The answer to the subset-count query `S` on the database `d`: the number of rows in `S`
whose secret bit is set [DworkRoth2014, §8.1]. -/
def subsetCount (d : ι → Bool) (S : Finset ι) : ℕ :=
  (S.filter fun i => d i = true).card

/-- Unfolding `subsetCount`. -/
theorem subsetCount_apply (d : ι → Bool) (S : Finset ι) :
    subsetCount d S = (S.filter fun i => d i = true).card := by
  rw [subsetCount]

/-- The answers `r` give every subset count of `d` with distortion at most `E`. -/
def SubsetCountsWithin (r : Finset ι → ℝ) (d : ι → Bool) (E : ℝ) : Prop :=
  ∀ S, |r S - subsetCount d S| ≤ E

/-- Unfolding `SubsetCountsWithin`. -/
theorem subsetCountsWithin_iff {r : Finset ι → ℝ} {d : ι → Bool} {E : ℝ} :
    SubsetCountsWithin r d E ↔ ∀ S, |r S - subsetCount d S| ≤ E :=
  Iff.rfl

/-- Exact answers have distortion `0`. -/
theorem subsetCountsWithin_subsetCount (d : ι → Bool) :
    SubsetCountsWithin (fun S => (subsetCount d S : ℝ)) d 0 := fun S => by simp

/-- Distortion bounds are nonnegative. -/
theorem SubsetCountsWithin.nonneg {r : Finset ι → ℝ} {d : ι → Bool} {E : ℝ}
    (h : SubsetCountsWithin r d E) : 0 ≤ E :=
  (abs_nonneg _).trans (h ∅)

variable [Fintype ι]

/-- **[DworkRoth2014, Theorem 8.1].** Two databases whose subset counts are both within `E` of
the same answers differ in at most `4 E` rows. -/
theorem hammingDist_le_of_subsetCountsWithin {r : Finset ι → ℝ} {c d : ι → Bool} {E : ℝ}
    (hc : SubsetCountsWithin r c E) (hd : SubsetCountsWithin r d E) :
    (hammingDist c d : ℝ) ≤ 4 * E := by
  classical
  set P := Finset.univ.filter fun i => c i = true ∧ d i = false
  set N := Finset.univ.filter fun i => c i = false ∧ d i = true
  have hdist : hammingDist c d = P.card + N.card := by
    rw [hammingDist, ← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, P, N]
      cases c i <;> cases d i <;> decide
    · refine Finset.disjoint_filter.mpr fun i _ h1 h2 => ?_
      rw [h1.1] at h2
      exact Bool.false_ne_true h2.1.symm
  -- On `P`, `c` counts every row and `d` none; on `N`, the reverse.
  have hP : subsetCount c P = P.card ∧ subsetCount d P = 0 := by
    refine ⟨congrArg Finset.card (Finset.filter_true_of_mem fun i hi => ?_), ?_⟩
    · exact (Finset.mem_filter.mp hi).2.1
    · refine Finset.card_eq_zero.mpr (Finset.filter_false_of_mem fun i hi => ?_)
      simp only [(Finset.mem_filter.mp hi).2.2, Bool.false_eq_true, not_false_eq_true]
  have hN : subsetCount c N = 0 ∧ subsetCount d N = N.card := by
    refine ⟨Finset.card_eq_zero.mpr (Finset.filter_false_of_mem fun i hi => ?_),
      congrArg Finset.card (Finset.filter_true_of_mem fun i hi => ?_)⟩
    · simp only [(Finset.mem_filter.mp hi).2.1, Bool.false_eq_true, not_false_eq_true]
    · exact (Finset.mem_filter.mp hi).2.2
  have h1 := hc P
  have h2 := hd P
  have h3 := hc N
  have h4 := hd N
  rw [hP.1] at h1
  rw [hP.2] at h2
  rw [hN.1] at h3
  rw [hN.2] at h4
  rw [hdist]
  push_cast
  rw [abs_le] at h1 h2 h3 h4
  push_cast at h1 h2 h3 h4
  linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]

open Classical in
/-- The reconstruction adversary of [DworkRoth2014, Theorem 8.1]: given answers `r` to all
subset-count queries, output a database whose subset counts are all within `E` of `r`, if there
is one (and the all-`false` database otherwise). It is not efficient: it searches all
databases. -/
noncomputable def reconstruct (E : ℝ) (r : Finset ι → ℝ) : ι → Bool :=
  if h : ∃ c, SubsetCountsWithin r c E then h.choose else fun _ => false

/-- The reconstruction adversary errs in at most `4 E` positions when the answers have
distortion at most `E` [DworkRoth2014, Theorem 8.1]. -/
theorem hammingDist_reconstruct_le {r : Finset ι → ℝ} {d : ι → Bool} {E : ℝ}
    (hd : SubsetCountsWithin r d E) : (hammingDist (reconstruct E r) d : ℝ) ≤ 4 * E := by
  have hex : ∃ c, SubsetCountsWithin r c E := ⟨d, hd⟩
  rw [reconstruct, dite_eq_left hex]
  exact hammingDist_le_of_subsetCountsWithin hex.choose_spec hd

namespace DifferentiallyPrivate

variable {G : (ι → Bool) → PMF (ι → Bool)} {ε : ℝ} {δ : ℝ≥0∞}

/-- **A private mechanism guesses few secret bits.** If `G` is `(ε, δ)`-private for Hamming
adjacency, then summed over all databases `d`, the probability that `G d` guesses the bit of row
`i` correctly is at most `2 ^ n (exp ε + δ) / (1 + exp ε)`, `n` being the number of rows. The
proof pairs each database with the one whose bit `i` is flipped. -/
theorem mul_sum_toOuterMeasure_apply_eq_le [DecidableEq ι]
    (h : DifferentiallyPrivate HammingAdjacent G ε δ) (i : ι) :
    (1 + ENNReal.ofReal (Real.exp ε)) * ∑ d, (G d).toOuterMeasure {c | c i = d i} ≤
      2 ^ Fintype.card ι * (ENNReal.ofReal (Real.exp ε) + δ) := by
  set f := BitString.flipOn {i}
  have hf : Function.Involutive f := BitString.flipOn_involutive {i}
  set a : (ι → Bool) → ℝ≥0∞ := fun d => (G d).toOuterMeasure {c | c i = d i}
  set e := ENNReal.ofReal (Real.exp ε)
  -- The event of a wrong guess on `d` is the event of a right guess on `f d`.
  have hcompl : ∀ d, {c : ι → Bool | c i = d i}ᶜ = {c | c i = f d i} := by
    intro d
    ext c
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, f, BitString.flipOn_singleton_self]
    cases c i <;> cases d i <;> decide
  have hadj : ∀ d, HammingAdjacent d (f d) := by
    intro d
    rw [show f d = Function.update d i (!d i) from BitString.flipOn_singleton i d]
    exact hammingAdjacent_update d i _
  -- Privacy on the pair `(d, f d)` for the event `{c | c i = d i}`.
  have hpair : ∀ d, a d + e * a (f d) ≤ e + δ := by
    intro d
    have hdp := h (hadj d) {c | c i = d i}
    have hsum := Probability.PMF.toOuterMeasure_add_compl_ennreal (G (f d)) {c | c i = d i}
    rw [hcompl d] at hsum
    calc a d + e * a (f d) ≤ e * (G (f d)).toOuterMeasure {c | c i = d i} + δ + e * a (f d) := by
          gcongr
      _ = e * ((G (f d)).toOuterMeasure {c | c i = d i} + a (f d)) + δ := by ring
      _ = e + δ := by rw [hsum, mul_one]
  have hsum_f : ∑ d, a (f d) = ∑ d, a d := Equiv.sum_comp (hf.toPerm f) a
  calc (1 + e) * ∑ d, a d = ∑ d, (a d + e * a (f d)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum_f]
        ring
    _ ≤ ∑ _d : ι → Bool, (e + δ) := Finset.sum_le_sum fun d _ => hpair d
    _ = 2 ^ Fintype.card ι * (e + δ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        rfl

/-- **A private mechanism guesses few secret bits on average.** If `G` is `(ε, δ)`-private for
Hamming adjacency on databases of `n` rows, then over a uniformly random database the expected
number of rows whose bit `G` guesses correctly is at most `n (exp ε + δ) / (1 + exp ε)`; in
unnormalized form, `(1 + exp ε) ∑ d ∑ i Pr[(G d) i = d i] ≤ 2 ^ n n (exp ε + δ)`. -/
theorem mul_sum_sum_toOuterMeasure_le [DecidableEq ι]
    (h : DifferentiallyPrivate HammingAdjacent G ε δ) :
    (1 + ENNReal.ofReal (Real.exp ε)) * ∑ d, ∑ i, (G d).toOuterMeasure {c | c i = d i} ≤
      2 ^ Fintype.card ι * Fintype.card ι * (ENNReal.ofReal (Real.exp ε) + δ) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  calc ∑ i, (1 + ENNReal.ofReal (Real.exp ε)) * ∑ d, (G d).toOuterMeasure {c | c i = d i}
      ≤ ∑ _i : ι, 2 ^ Fintype.card ι * (ENNReal.ofReal (Real.exp ε) + δ) :=
        Finset.sum_le_sum fun i _ => h.mul_sum_toOuterMeasure_apply_eq_le i
    _ = 2 ^ Fintype.card ι * Fintype.card ι * (ENNReal.ofReal (Real.exp ε) + δ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- On the event that `G d` is within Hamming distance `t` of `d`, at least `n - t` bits are
correct. -/
private theorem card_sub_mul_le_sum (P : PMF (ι → Bool)) (d : ι → Bool) (t : ℕ) :
    ((Fintype.card ι - t : ℕ) : ℝ≥0∞) * P.toOuterMeasure {c | hammingDist c d ≤ t} ≤
      ∑ i, P.toOuterMeasure {c | c i = d i} := by
  classical
  simp only [PMF.toOuterMeasure_apply_fintype]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  by_cases hc : hammingDist c d ≤ t
  · have hagree : Fintype.card ι - t ≤ (Finset.univ.filter fun i => c i = d i).card := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => c i = d i)
      rw [Finset.card_univ] at this
      have hd : (Finset.univ.filter fun i => ¬ c i = d i).card = hammingDist c d := rfl
      omega
    have hsum : ∑ i, {c' : ι → Bool | c' i = d i}.indicator P c =
        (Finset.univ.filter fun i => c i = d i).card * P c := by
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [Set.indicator_of_mem (show c ∈ {c | hammingDist c d ≤ t} from hc), hsum]
    gcongr
  · rw [Set.indicator_of_notMem (show c ∉ {c | hammingDist c d ≤ t} from hc), mul_zero]
    exact bot_le

/-- **A private mechanism cannot reconstruct.** If `G` is `(ε, δ)`-private for Hamming adjacency
on databases of `n` rows and, on every database `d`, `G d` is within Hamming distance `t` of `d`
with probability at least `q`, then `(1 + exp ε) (n - t) q ≤ n (exp ε + δ)`. -/
theorem mul_card_sub_mul_le (h : DifferentiallyPrivate HammingAdjacent G ε δ) {t : ℕ} {q : ℝ≥0∞}
    (hq : ∀ d, q ≤ (G d).toOuterMeasure {c | hammingDist c d ≤ t}) :
    (1 + ENNReal.ofReal (Real.exp ε)) * (Fintype.card ι - t : ℕ) * q ≤
      Fintype.card ι * (ENNReal.ofReal (Real.exp ε) + δ) := by
  classical
  have hN : (2 : ℝ≥0∞) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ two_ne_zero
  have hN' : (2 : ℝ≥0∞) ^ Fintype.card ι ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  refine (ENNReal.mul_le_mul_iff_right hN hN').mp ?_
  calc 2 ^ Fintype.card ι * ((1 + ENNReal.ofReal (Real.exp ε)) * (Fintype.card ι - t : ℕ) * q)
      = (1 + ENNReal.ofReal (Real.exp ε)) *
          ∑ _d : ι → Bool, ((Fintype.card ι - t : ℕ) : ℝ≥0∞) * q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (1 + ENNReal.ofReal (Real.exp ε)) * ∑ d, ∑ i, (G d).toOuterMeasure {c | c i = d i} := by
        gcongr with d
        exact (mul_le_mul_right (hq d) _).trans (card_sub_mul_le_sum (G d) d t)
    _ ≤ 2 ^ Fintype.card ι * Fintype.card ι * (ENNReal.ofReal (Real.exp ε) + δ) :=
        h.mul_sum_sum_toOuterMeasure_le
    _ = 2 ^ Fintype.card ι * (Fintype.card ι * (ENNReal.ofReal (Real.exp ε) + δ)) := by ring

variable {R : Type v} {M : (ι → Bool) → PMF R}

/-- **Private answers to all subset-count queries are inaccurate.** Let `M` be `(ε, δ)`-private
for Hamming adjacency on databases of `n` rows, with outputs from which `ans` reads answers to
all subset-count queries. If on every database the answers have distortion at most `E` with
probability at least `q`, then `(1 + exp ε) (n - 4 E) q ≤ n (exp ε + δ)`. This combines the
reconstruction attack [DworkRoth2014, Theorem 8.1] with `DifferentiallyPrivate.mul_card_sub_mul_le`
(a standard derivation; see [DworkRoth2014, §8.1]). -/
theorem mul_card_sub_mul_le_of_subsetCountsWithin (h : DifferentiallyPrivate HammingAdjacent M ε δ)
    (hδ : δ ≠ ⊤) (ans : R → Finset ι → ℝ) {E q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ d, ENNReal.ofReal q ≤ (M d).toOuterMeasure {o | SubsetCountsWithin (ans o) d E}) :
    (1 + Real.exp ε) * (Fintype.card ι - 4 * E) * q ≤
      Fintype.card ι * (Real.exp ε + δ.toReal) := by
  classical
  rcases lt_or_ge E 0 with hE | hE
  · -- No answers have negative distortion, so `q = 0`.
    obtain ⟨d⟩ : Nonempty (ι → Bool) := inferInstance
    have hq' := hq d
    have hempty : {o | SubsetCountsWithin (ans o) d E} = ∅ :=
      Set.eq_empty_of_forall_notMem fun o ho => (lt_irrefl _ (hE.trans_le ho.nonneg))
    rw [hempty, MeasureTheory.measure_empty, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hq'
    have hq'' : q = 0 := le_antisymm hq' hq0
    rw [hq'', mul_zero]
    positivity
  set t := ⌊4 * E⌋₊
  have hG := (h.map fun o => reconstruct E (ans o)).mul_card_sub_mul_le (t := t)
    (q := ENNReal.ofReal q)
    fun d => (hq d).trans (by
      rw [PMF.toOuterMeasure_map_apply]
      refine (M d).toOuterMeasure.mono fun o ho => ?_
      have := hammingDist_reconstruct_le ho
      exact Nat.le_floor this)
  have hfin : ENNReal.ofReal (Real.exp ε) + δ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨by simp, hδ⟩
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfin) hG
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_add (by simp)
    ENNReal.ofReal_ne_top, ENNReal.toReal_add (by simp) hδ, ENNReal.toReal_ofReal hq0,
    ENNReal.toReal_ofReal (Real.exp_pos ε).le, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_one] at hreal
  refine le_trans ?_ hreal
  have hsub : (Fintype.card ι : ℝ) - 4 * E ≤ ((Fintype.card ι - t : ℕ) : ℝ) := by
    have ht : (t : ℝ) ≤ 4 * E := Nat.floor_le (by linarith)
    rcases le_total t (Fintype.card ι) with htn | htn
    · rw [Nat.cast_sub htn]
      linarith
    · rw [Nat.sub_eq_zero_of_le htn, Nat.cast_zero]
      have : (Fintype.card ι : ℝ) ≤ t := by exact_mod_cast htn
      linarith
  have h1 : (0 : ℝ) ≤ 1 + Real.exp ε := by positivity
  gcongr

/-- **Private answers to all subset-count queries have linear distortion.** If an
`(ε, δ)`-private mechanism for Hamming adjacency on databases of `n` rows answers all subset-count
queries with distortion at most `E` with probability one on every database, then
`n (1 - δ) ≤ 4 E (1 + exp ε)`, that is, `E ≥ n (1 - δ) / (4 (1 + exp ε))`. For `ε = δ = 0` this
forces `E ≥ n / 8`. The bound is on a distortion guaranteed uniformly over all databases: on a
single database a constant mechanism, which is `(0, 0)`-private, can answer exactly. Exact answers
on every database (`E = 0`) are not `(ε, δ)`-private for `δ < 1` once `n ≥ 1`. -/
theorem card_mul_one_sub_le_of_subsetCountsWithin (h : DifferentiallyPrivate HammingAdjacent M ε δ)
    (hδ : δ ≠ ⊤) (ans : R → Finset ι → ℝ) {E : ℝ}
    (hE : ∀ d, (M d).toOuterMeasure {o | SubsetCountsWithin (ans o) d E} = 1) :
    Fintype.card ι * (1 - δ.toReal) ≤ 4 * E * (1 + Real.exp ε) := by
  have := h.mul_card_sub_mul_le_of_subsetCountsWithin hδ ans zero_le_one fun d => by
    rw [hE d, ENNReal.ofReal_one]
  nlinarith

end DifferentiallyPrivate

end Cslib.Privacy
