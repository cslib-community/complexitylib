/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Randomized
public import CslibFrontier.Computability.MCSP.Multi
public import CslibFrontier.Computability.MCSP.MultiNPHard.WindowCount
public import CslibFrontier.Computability.PCP.Approximation.SetCover.ApproxReduction
import CslibFrontier.Foundations.Data.BitString.WordCount
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size

/-!
# The reduction from Set Cover to Multi-MCSP

The reduction of Ilango, Loff and Oliveira [IlangoLoffOliveira2020, §4.2, pp. 22:20–22:21], from the
constant-gap Set Cover problem `GapSetCover 3` to Multi-output MCSP, as a function of the Set Cover
instance and a random string, with its correctness for every outcome of the randomness. The source
reduces from Trevisan's `r`-bounded Set Cover; here the source problem is the library's
`GapSetCover 3`, which `GapSetCover_npHard` shows `NP`-hard.

**This file does not prove that the reduction runs in polynomial time, nor that Multi-MCSP is
`NP`-hard.** `rpReducible_of_computableInPolyTime` derives the randomized reduction from that
running-time hypothesis.

Given `(S, k)`, write `N` for the length of `S.ground` and `t` for the number of sets.

* **Positions.** The elements to cover are the positions `j < N` of the ground list: `residues S i`
  holds the positions whose element lies in set `i`. Repeated ground elements only repeat a covering
  obligation, and set elements outside the ground list give no position and are ignored, as they
  are by `SetSystem.IsCover`; so the sets covering the positions are exactly the covers
  (`forall_residues_iff`).
* **Parameters.** The arity is `p = 6 · size (N + t + 4)` (`arity`), so `2^p` is polynomial in the
  input yet exceeds `(N + t + 4)^6` (`bound_pow_six_lt`, `two_pow_arity_le`).
* **The instance** (`ofTable`). For a table `T : Fin (2^p) → Bool`, the outputs are the window
  template of the lifted sets `Window.lift p N (residues S i)` followed by `T`, with threshold
  `K + min k t`, where `K` is the template's number of distinct non-input gate functions. The table
  is the first `2^p` bits of the random string (`reduce`). An empty ground list gives a fixed
  yes-instance (`fallback`).
* **Completeness** (`reduce_mem_of_yes`): a cover of size at most `k` gives a yes-instance for every
  random string, by `Window.ecomplexity_append_le`. The reduction has one-sided error, as in the
  source [p. 22:21].
* **Soundness** (`three_mul_card_ofTable_mem_le`): on a no-instance, at most a third of the tables
  give a yes-instance, by the union bound `Window.three_mul_card_cheap_lift_le` (the library route,
  in place of the compression argument of Lemma 16).
* **Positivity** (`reduce_positive`): every output has positive arity, number of outputs and
  threshold, as Definition 1 asks.

## Main definitions

* `Cslib.MultiMCSP.Reduction.residues`: the positions of the ground list in each set.
* `Cslib.MultiMCSP.Reduction.arity`: the arity of the output instances.
* `Cslib.MultiMCSP.Reduction.ofTable`, `Cslib.MultiMCSP.Reduction.reduce`: the output instance,
  for a table and for a random string.

## Main results

* `Cslib.MultiMCSP.Reduction.mem_yes_iff`, `Cslib.MultiMCSP.Reduction.mem_no_iff`: the yes- and
  no-instances of `GapSetCover 3`, over `ℕ`.
* `Cslib.MultiMCSP.Reduction.forall_residues_iff`: covers of the positions are covers.
* `Cslib.MultiMCSP.Reduction.reduce_positive`: every output satisfies Definition 1's positivity.
* `Cslib.MultiMCSP.Reduction.reduce_mem_of_yes`: completeness, for every random string.
* `Cslib.MultiMCSP.Reduction.three_mul_card_ofTable_mem_le`,
  `Cslib.MultiMCSP.Reduction.three_mul_card_reduce_mem_le`: soundness, as a count of tables and of
  random strings.
* `Cslib.MultiMCSP.Window.truthTable_tableFun`: the truth table of `Window.tableFun T` is `T`.
* `Cslib.MultiMCSP.Reduction.rpReducible_of_computableInPolyTime`: the randomized reduction, given
  that `reduce` runs in polynomial time.

## References

* [R. Ilango, B. Loff, I. C. Oliveira, *NP-Hardness of Circuit Minimization for Multi-Output
  Functions*][IlangoLoffOliveira2020]
-/

public section

namespace Cslib

open Circuits Finset Complexity Turing.MultiTapeTM

namespace MultiMCSP

universe v

variable {σ : Signature.{v}} {I : Interpretation σ Bool}

/-- `Window.tableFun T` is the function whose truth table is `T`. -/
theorem Window.tableFun_eq {p : ℕ} (T : Fin (2 ^ p) → Bool) :
    Window.tableFun T = (MCSP.truthTable p).symm T :=
  funext fun x => by simp

/-- The truth table of `Window.tableFun T` is `T`. -/
theorem Window.truthTable_tableFun {p : ℕ} (T : Fin (2 ^ p) → Bool) :
    MCSP.truthTable p (Window.tableFun T) = T := by
  rw [Window.tableFun_eq, Equiv.apply_symm_apply]

namespace Reduction

/-! ### Yes- and no-instances of `GapSetCover 3` -/

/-- A yes-instance of `GapSetCover 3` is a coverable system with optimum at most `k`. -/
theorem mem_yes_iff {S : SetSystem} {k : ℕ} :
    (S, k) ∈ (GapSetCover 3).yes ↔ S.Coverable ∧ S.optCoverSize ≤ k :=
  mem_yes_GapSetCoverFn

/-- A no-instance of `GapSetCover 3` is a coverable system with optimum at least `3k`, for a
positive `k`. -/
theorem mem_no_iff {S : SetSystem} {k : ℕ} :
    (S, k) ∈ (GapSetCover 3).no ↔ S.Coverable ∧ 3 * k ≤ S.optCoverSize ∧ 0 < k := by
  rw [GapSetCover, mem_no_GapSetCoverFn]
  refine and_congr_right fun _ => and_congr (by exact_mod_cast Iff.rfl) ?_
  constructor
  · intro h
    by_contra hk
    rw [show k = 0 by omega] at h
    norm_num at h
  · intro hk
    have : (0 : ℝ) < k := by exact_mod_cast hk
    linarith

/-- The optimum of a coverable system is at most its number of sets. -/
private theorem optCoverSize_le_length {S : SetSystem} (hS : S.Coverable) :
    S.optCoverSize ≤ S.sets.length := by
  obtain ⟨C, hC⟩ := hS
  refine (SetSystem.optCoverSize_le (C := univ) fun u hu => ?_).trans_eq
    (card_univ.trans (Fintype.card_fin _))
  obtain ⟨i, -, hi⟩ := hC u hu
  exact ⟨i, mem_univ _, hi⟩

/-- A no-instance of `GapSetCover 3` has a nonempty ground list: the empty family covers an empty
one at cost `0 < 3k`. -/
theorem ground_ne_nil_of_mem_no {S : SetSystem} {k : ℕ} (hno : (S, k) ∈ (GapSetCover 3).no) :
    S.ground ≠ [] := by
  obtain ⟨-, hopt, hk⟩ := mem_no_iff.mp hno
  intro hS
  have hnil : S.IsCover ∅ := fun u hu => by simp [hS] at hu
  have h0 := SetSystem.optCoverSize_le hnil
  simp only [card_empty] at h0
  omega

/-! ### Positions and parameters -/

/-- The positions `j` of the ground list whose element lies in set `i`. Elements of the set that
are not in the ground list give no position, so they are ignored. -/
@[expose] def residues (S : SetSystem) (i : Fin S.sets.length) : Finset ℕ :=
  (range S.ground.length).filter fun j => S.ground.getD j 0 ∈ S.sets[i]

theorem mem_residues {S : SetSystem} {i : Fin S.sets.length} {j : ℕ} :
    j ∈ residues S i ↔ ∃ h : j < S.ground.length, S.ground[j] ∈ S.sets[i] := by
  simp only [residues, mem_filter, mem_range]
  constructor
  · rintro ⟨h, hj⟩
    exact ⟨h, by rwa [List.getD_eq_getElem _ _ h] at hj⟩
  · rintro ⟨h, hj⟩
    exact ⟨h, by rwa [List.getD_eq_getElem _ _ h]⟩

/-- **Relabelling.** The sets `C` cover every position of the ground list exactly when they cover
`S`. A repeated ground element repeats a covering obligation, and set elements outside the ground
list play no part on either side. -/
theorem forall_residues_iff (S : SetSystem) (C : Finset (Fin S.sets.length)) :
    (∀ u < S.ground.length, ∃ i ∈ C, u ∈ residues S i) ↔ S.IsCover C := by
  constructor
  · intro h u hu
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hu
    obtain ⟨i, hi, hji⟩ := h j hj
    exact ⟨i, hi, (mem_residues.mp hji).2⟩
  · intro h u hu
    obtain ⟨i, hi, hui⟩ := h _ (List.getElem_mem hu)
    exact ⟨i, hi, mem_residues.mpr ⟨hu, hui⟩⟩

/-- `N + t + 4`, for `N` ground positions and `t` sets. -/
@[expose] def bound (S : SetSystem) : ℕ :=
  S.ground.length + S.sets.length + 4

/-- The arity `6 · size (N + t + 4)` of the output instances. -/
@[expose] def arity (S : SetSystem) : ℕ :=
  6 * Nat.size (bound S)

private theorem three_le_size (S : SetSystem) : 3 ≤ Nat.size (bound S) :=
  Nat.lt_size.mpr (by simp only [bound]; omega)

theorem eighteen_le_arity (S : SetSystem) : 18 ≤ arity S := by
  have := three_le_size S
  simp only [arity]
  omega

instance (S : SetSystem) : NeZero (arity S) :=
  ⟨by have := eighteen_le_arity S; omega⟩

theorem arity_le (S : SetSystem) : arity S ≤ 6 * bound S := by
  simp only [arity]
  have := (Nat.size_le).mpr (Nat.lt_two_pow_self (n := bound S))
  omega

/-- `2^p` exceeds `(N + t + 4)^6`. -/
theorem bound_pow_six_lt (S : SetSystem) : bound S ^ 6 < 2 ^ arity S := by
  rw [arity, Nat.mul_comm, pow_mul]
  exact Nat.pow_lt_pow_left (Nat.lt_size_self _) (by norm_num)

/-- `2^p` is at most `64 (N + t + 4)^6`. -/
theorem two_pow_arity_le (S : SetSystem) : 2 ^ arity S ≤ 64 * bound S ^ 6 := by
  have h3 := three_le_size S
  have hle : 2 ^ (Nat.size (bound S) - 1) ≤ bound S := Nat.lt_size.mp (by omega)
  have h2 : 2 ^ Nat.size (bound S) ≤ 2 * bound S := by
    calc 2 ^ Nat.size (bound S) = 2 * 2 ^ (Nat.size (bound S) - 1) := by
          rw [← pow_succ']
          congr 1
          omega
      _ ≤ 2 * bound S := Nat.mul_le_mul_left 2 hle
  calc 2 ^ arity S = (2 ^ Nat.size (bound S)) ^ 6 := by rw [arity, Nat.mul_comm, pow_mul]
    _ ≤ (2 * bound S) ^ 6 := Nat.pow_le_pow_left h2 6
    _ = 64 * bound S ^ 6 := by ring

/-! ### The output instances -/

/-- The output instance for the table `T`: the window template of the lifted position sets followed
by `T`, with threshold the template's number of distinct non-input gate functions plus
`min k t`. The clamp keeps the threshold, written in unary, polynomial in the binary `k`; it
changes nothing that matters, since a cover never needs more than the `t` sets. -/
@[expose] noncomputable def ofTable (S : SetSystem) (k : ℕ) (T : Fin (2 ^ arity S) → Bool) :
    Instance :=
  Instance.ofFunction (arity S) (Window.gateCount (arity S) S.sets.length + 1)
    (#(nonInputComponents
        (Window.template (fun i => Window.lift (arity S) S.ground.length (residues S i)) T)) +
      min k S.sets.length)
    fun x => Fin.append
      (Window.template (fun i => Window.lift (arity S) S.ground.length (residues S i)) T x)
      (single (Window.tableFun T) x)

/-- The output for an empty ground list: one input, one output `x₀` and threshold one. -/
@[expose] def fallback : Instance :=
  Instance.ofFunction 1 1 1 fun x _ => x 0

/-- **The reduction**, as a function of the instance `(S, k)` and the random string `r`: for a
nonempty ground list, `ofTable` of the first `2^p` bits of `r`, read as `false` past its end. -/
@[expose] noncomputable def reduce : (SetSystem × ℕ) × List Bool → Instance
  | ((S, k), r) => if S.ground = [] then fallback else ofTable S k fun y => r.getD y false

theorem reduce_of_ground_eq_nil {S : SetSystem} (h : S.ground = []) (k : ℕ) (r : List Bool) :
    reduce ((S, k), r) = fallback := by
  simp [reduce, h]

theorem reduce_of_ground_ne_nil {S : SetSystem} (h : S.ground ≠ []) (k : ℕ) (r : List Bool) :
    reduce ((S, k), r) = ofTable S k fun y => r.getD y false := by
  simp [reduce, h]

theorem ofTable_mem_iff {S : SetSystem} {k : ℕ} {T : Fin (2 ^ arity S) → Bool} :
    ofTable S k T ∈ MultiMCSP I ↔
      ecomplexity I (fun x => Fin.append
        (Window.template (fun i => Window.lift (arity S) S.ground.length (residues S i)) T x)
        (single (Window.tableFun T) x)) ≤
      ((#(nonInputComponents
          (Window.template (fun i => Window.lift (arity S) S.ground.length (residues S i)) T)) +
        min k S.sets.length : ℕ) : ℕ∞) :=
  ofFunction_mem_iff

/-- **Positivity.** Every output instance has positive arity, number of outputs and threshold, as
Definition 1 asks: the template has the non-input gate function `¬x₀`. -/
theorem reduce_positive (x : (SetSystem × ℕ) × List Bool) : (reduce x).Positive := by
  obtain ⟨⟨S, k⟩, r⟩ := x
  by_cases hS : S.ground = []
  · rw [reduce_of_ground_eq_nil hS]
    exact ⟨Nat.one_pos, Nat.one_pos, Nat.one_pos⟩
  rw [reduce_of_ground_ne_nil hS]
  have hmem : (fun x => Window.template
      (fun i => Window.lift (arity S) S.ground.length (residues S i)) (fun y => r.getD y false) x
        (Window.Gate.equivFin _ _ (.neg 0))) ∈ nonInputComponents
      (Window.template (fun i => Window.lift (arity S) S.ground.length (residues S i))
        (fun y => r.getD y false)) := by
    refine mem_nonInputComponents.mpr ⟨⟨_, rfl⟩, fun i h => ?_⟩
    have := congrFun h fun _ => false
    simp [Window.template_equivFin] at this
  have hpos := card_pos.mpr ⟨_, hmem⟩
  refine ⟨(eighteen_le_arity S).trans_lt' (by norm_num), Nat.succ_pos _, ?_⟩
  change 0 < _ + _
  omega

/-! ### Correctness -/

variable [Boolean.DeMorganBasis I]

/-- **Completeness**, for every random string. A yes-instance of `GapSetCover 3` maps to a
yes-instance of Multi-MCSP: the at most `min k t` sets of an optimal cover give `T` as an OR of
windows. -/
theorem reduce_mem_of_yes {S : SetSystem} {k : ℕ} (hyes : (S, k) ∈ (GapSetCover 3).yes)
    (r : List Bool) : reduce ((S, k), r) ∈ MultiMCSP I := by
  obtain ⟨hcov, hopt⟩ := mem_yes_iff.mp hyes
  by_cases hS : S.ground = []
  · rw [reduce_of_ground_eq_nil hS, fallback, ofFunction_mem_iff]
    have h := ecomplexity_wiring (I := I) (fun _ : Fin 1 => (0 : Fin 1))
    exact h.le.trans zero_le
  rw [reduce_of_ground_ne_nil hS, ofTable_mem_iff]
  obtain ⟨C, hC, hcard⟩ := SetSystem.exists_isCover_optCoverSize hcov
  have hCt : #C ≤ S.sets.length := (card_le_univ C).trans_eq (Fintype.card_fin _)
  refine (Window.ecomplexity_append_le _ _ C (Window.lift_cover (List.length_pos_iff.mpr hS) _ C
    ((forall_residues_iff S C).mpr hC))).trans (Nat.cast_le.mpr ?_)
  have : #C - 1 ≤ min k S.sets.length := (Nat.sub_le _ _).trans (le_min (hcard ▸ hopt) hCt)
  omega

open scoped Classical in
/-- **Soundness, as a count of tables.** For a no-instance of `GapSetCover 3`, at most a third of
the tables give a yes-instance of Multi-MCSP. -/
theorem three_mul_card_ofTable_mem_le {S : SetSystem} {k : ℕ}
    (hno : (S, k) ∈ (GapSetCover 3).no) :
    3 * #{T : Fin (2 ^ arity S) → Bool | ofTable S k T ∈ MultiMCSP I} ≤ 2 ^ 2 ^ arity S := by
  obtain ⟨hcov, hopt', hk1⟩ := mem_no_iff.mp hno
  -- The optimum is at most the number of sets, so `min k t = k`.
  have hoptt := optCoverSize_le_length hcov
  have hmin : min k S.sets.length = k := min_eq_left (by omega)
  have hN : 0 < S.ground.length := List.length_pos_iff.mpr (ground_ne_nil_of_mem_no hno)
  -- Every set of at most `k + 1` sets misses a position.
  have hmiss : ∀ B : Finset (Fin S.sets.length), #B ≤ k + 1 →
      ∃ u < S.ground.length, ∀ i ∈ B, u ∉ residues S i := by
    intro B hB
    by_contra h
    push Not at h
    have := SetSystem.optCoverSize_le ((forall_residues_iff S B).mp h)
    omega
  have hM := bound_pow_six_lt S
  have hb : 4 ≤ bound S := by simp only [bound]; omega
  have hNb : S.ground.length ≤ bound S := by simp only [bound]; omega
  have htb : S.sets.length ≤ bound S := by simp only [bound]; omega
  have hb2 : bound S ≤ bound S ^ 6 := Nat.le_self_pow (by norm_num) _
  have ht : S.sets.length ≤ 2 ^ arity S := by omega
  have h64 : 64 ≤ 2 ^ arity S :=
    (Nat.pow_le_pow_right (by norm_num) (eighteen_le_arity S)).trans' (by norm_num)
  have hd : arity S * (5 * k + 5) ≤ 2 ^ arity S / S.ground.length := by
    rw [Nat.le_div_iff_mul_le hN]
    have hkb : 5 * k + 5 ≤ 5 * bound S := by omega
    calc arity S * (5 * k + 5) * S.ground.length
        ≤ (6 * bound S) * (5 * bound S) * bound S :=
          Nat.mul_le_mul (Nat.mul_le_mul (arity_le S) hkb) hNb
      _ = 30 * bound S ^ 3 := by ring
      _ ≤ bound S ^ 6 := by
          have : 30 ≤ bound S ^ 3 := by
            calc 30 ≤ 4 ^ 3 := by norm_num
              _ ≤ bound S ^ 3 := Nat.pow_le_pow_left hb 3
          calc 30 * bound S ^ 3 ≤ bound S ^ 3 * bound S ^ 3 := Nat.mul_le_mul_right _ this
            _ = bound S ^ 6 := by ring
      _ ≤ 2 ^ arity S := hM.le
  have hcount := Window.three_mul_card_cheap_lift_le (I := I) hN (residues S) k hmiss ht
    (by omega) h64 hd
  refine (Nat.mul_le_mul_left 3 (card_le_card fun T hT => ?_)).trans hcount
  rw [mem_filter] at hT ⊢
  refine ⟨mem_univ _, ?_⟩
  have := ofTable_mem_iff.mp hT.2
  rwa [hmin] at this

/-! ### The randomized reduction -/

/-- The length `64 (n + 4)^6` of the random string, for an input of length `n`. -/
noncomputable def seedLength : Polynomial ℕ :=
  64 * (Polynomial.X + 4) ^ 6

theorem seedLength_eval (n : ℕ) : seedLength.eval n = 64 * (n + 4) ^ 6 := by
  simp [seedLength]

/-- The random string covers the table: `2^p ≤ 64 (n + 4)^6` for an input of length `n`. -/
theorem two_pow_arity_le_seedLength (S : SetSystem) (k : ℕ) :
    2 ^ arity S ≤ seedLength.eval (encSetCover (S, k)).length := by
  rw [seedLength_eval]
  have hN := length_le_length_encList encNat S.ground
  have ht := length_le_length_encList (encList encNat) S.sets
  have hS : S.ground.length + S.sets.length ≤ (encSetSystem S).length := by
    rw [encSetSystem_apply, encSetSystemFields, length_encPair]
    simp only [encNatSetList] at ht ⊢
    omega
  have henc : S.ground.length + S.sets.length ≤ (encSetCover (S, k)).length :=
    hS.trans (length_le_encPair_left _ _ (S, k))
  refine (two_pow_arity_le S).trans (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left ?_ 6))
  simp only [bound]
  omega

open scoped Classical in
/-- At most a third of the random strings give a yes-instance on a no-instance. -/
theorem three_mul_card_reduce_mem_le {S : SetSystem} {k : ℕ} (hno : (S, k) ∈ (GapSetCover 3).no)
    {q : ℕ} (hq : 2 ^ arity S ≤ q) :
    3 * #{r : Fin q → Bool | reduce ((S, k), List.ofFn r) ∈ MultiMCSP I} ≤ 2 ^ q := by
  have hS := ground_ne_nil_of_mem_no hno
  -- The table is the first `2^p` bits of the random string.
  have htable (l : List Bool) :
      (fun y : Fin (2 ^ arity S) => l.getD y false) =
        fun y : Fin (2 ^ arity S) => (l.take (2 ^ arity S)).getD y false :=
    funext fun y => by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt y.isLt]
  let g : List Bool → Prop := fun l => ofTable S k (fun y => l.getD y false) ∈ MultiMCSP I
  have hcard : #{r : Fin q → Bool | reduce ((S, k), List.ofFn r) ∈ MultiMCSP I} =
      2 ^ (q - 2 ^ arity S) * #{T : Fin (2 ^ arity S) → Bool | g (List.ofFn T)} := by
    refine Eq.trans ?_ (BitString.card_filter_take hq g)
    congr 1
    ext r
    simp only [mem_filter, mem_univ, true_and, g, reduce_of_ground_ne_nil hS]
    rw [htable (List.ofFn r)]
  have hofFn : #{T : Fin (2 ^ arity S) → Bool | g (List.ofFn T)} =
      #{T : Fin (2 ^ arity S) → Bool | ofTable S k T ∈ MultiMCSP I} := by
    congr 1
    ext T
    have hT : (fun y : Fin (2 ^ arity S) => (List.ofFn T).getD y false) = T :=
      funext fun y => by rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp only [mem_filter, mem_univ, true_and, g, hT]
  rw [hcard, hofFn]
  calc 3 * (2 ^ (q - 2 ^ arity S) * #{T : Fin (2 ^ arity S) → Bool | ofTable S k T ∈ MultiMCSP I})
      = 2 ^ (q - 2 ^ arity S) * (3 * #{T : Fin (2 ^ arity S) → Bool |
          ofTable S k T ∈ MultiMCSP I}) := by ring
    _ ≤ 2 ^ (q - 2 ^ arity S) * 2 ^ 2 ^ arity S :=
        Nat.mul_le_mul_left _ (three_mul_card_ofTable_mem_le hno)
    _ = 2 ^ q := by rw [← pow_add, Nat.sub_add_cancel hq]

/-- **The randomized reduction, given its running time.** If `reduce` runs in polynomial time,
`GapSetCover 3` reduces to Multi-MCSP, restricted to Definition 1's positive instances, by a
randomized reduction with one-sided error: yes-instances always map to yes-instances, and
no-instances to no-instances with probability at least `2/3` [IlangoLoffOliveira2020, §4.2,
pp. 22:20–22:21]. The basis is any `Boolean.DeMorganBasis`: `Boolean.DeMorgan.interpretation` is
the source's constant-free basis of Definition 1, `Boolean.interpretation` the library variant with
constants. Soundness uses the library's union bound in place of the source's Lemma 16. The
running-time hypothesis is not yet proved. -/
theorem rpReducible_of_computableInPolyTime
    (hpoly : Turing.MultiTapeTM.ComputableInPolyTime reduce
      (Turing.MultiTapeTM.encPair encSetCover Turing.MultiTapeTM.encBits) encInstance) :
    PromiseProblem.RPReducible encSetCover encInstance (GapSetCover 3)
      ((PromiseProblem.ofSet (MultiMCSP I)).restrict {x | x.Positive}) := by
  classical
  refine PromiseProblem.rpReducible_iff_exists_seeded.mpr
    ⟨seedLength, reduce, hpoly, fun ⟨S, k⟩ hyes r => ?_, fun ⟨S, k⟩ hno => ?_⟩
  · exact Set.mem_inter (reduce_mem_of_yes hyes _) (reduce_positive _)
  · set q := seedLength.eval (encSetCover (S, k)).length
    have hbad : 3 * #{r : Fin q → Bool | reduce ((S, k), List.ofFn r) ∈ MultiMCSP I} ≤ 2 ^ q :=
      three_mul_card_reduce_mem_le hno (two_pow_arity_le_seedLength S k)
    have hsplit : #{r : Fin q → Bool | reduce ((S, k), List.ofFn r) ∈ MultiMCSP I} +
        #{r : Fin q → Bool | reduce ((S, k), List.ofFn r) ∉ MultiMCSP I} = 2 ^ q := by
      rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin]
    have hgood : #{r : Fin q → Bool | reduce ((S, k), List.ofFn r) ∉ MultiMCSP I} ≤
        #{r : Fin q → Bool | reduce ((S, k), List.ofFn r) ∈
          ((PromiseProblem.ofSet (MultiMCSP I)).restrict {x | x.Positive}).no} :=
      card_le_card fun r hr => by
        rw [mem_filter] at hr ⊢
        exact ⟨hr.1, Set.mem_inter hr.2 (reduce_positive _)⟩
    omega

end Reduction

end MultiMCSP

end Cslib
