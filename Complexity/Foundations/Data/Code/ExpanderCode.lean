/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Bipartite
public import Complexity.Foundations.Data.Code.Basic
public import Complexity.Foundations.Data.BitString.Parity
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Complexity.Foundations.Data.BitString.Parity.DotProduct
import Complexity.Foundations.Data.Code.Linear

/-!
# Expander codes: rate and distance

The *expander code* of a bipartite graph `G : ι → κ → Prop` [SipserSpielman1996] has a bit for
every left vertex (*variable*) and a parity check for every right vertex (*check*). A word
`x : ι → Bool` is a codeword when every check sees an even number of ones among its neighbours,
i.e. when it lies in the kernel of the `0/1` incidence matrix
(`Cslib.BitString.ExpanderCode.checkMatrix`). This is the code `C(G)` of
[GuruswamiRudraSudan2025, Definition 11.3.1], a binary linear code given as a
`Submodule Bool (ι → Bool)`; when `G` has small degrees it is a low-density parity-check code.

* **Rate** [GuruswamiRudraSudan2025, Proposition 11.3.5]: the code has at least
  `2 ^ (n - m)` codewords, where `n = |ι|` and `m = |κ|`
  (`Cslib.BitString.ExpanderCode.two_pow_sub_le_card_code`), so its rate
  `log₂ |C(G)| / n` is at least `1 - m / n`, and at least `1 - c / d` when `G` is
  `(c, d)`-biregular (`Cslib.BitString.ExpanderCode.one_sub_div_le_rate_of_isBiregular`).
* **Distance** [GuruswamiRudraSudan2025, Theorem 11.3.6]: if left degrees are at most `c` and all
  sets of at most `k` variables expand by a factor `α > c / 2`, distinct codewords differ in more
  than `k` positions (`Cslib.BitString.ExpanderCode.lt_hammingDist`). The set `S` where they
  differ would have a unique neighbour, a check seeing exactly one difference, which a codeword
  cannot violate. Refining the argument on a `k`-subset of `S` gives
  `2 α k ≤ c · d(x, w)` (`Cslib.BitString.ExpanderCode.two_mul_mul_le_hammingDist`), i.e.
  distance at least `2 γ (1 - ε) n` for `α = c (1 - ε)` and `k = γ n`
  [GuruswamiRudraSudan2025, Theorem 11.3.8] [GuruswamiSharma2010, Theorem 4].

The source states these for `c`-left-regular graphs with `k = γ n`; here left degrees need only be
at most `c` (`Cslib.Bipartite.IsLeftBounded`) and `k` is any natural number. Flip decoding is in
`Complexity.Foundations.Data.Code.FlipDecoding`.

## Main definitions

* `Cslib.BitString.ExpanderCode.checkMatrix`: the incidence matrix of the checks.
* `Cslib.BitString.ExpanderCode.code`: the expander (parity-check) code of a bipartite graph.
* `Cslib.BitString.ExpanderCode.syndrome`, `Cslib.BitString.ExpanderCode.unsat`: the values of
  the checks on a word, and the set of violated checks.

## Main results

* `Cslib.BitString.ExpanderCode.mem_unsat_iff`: a check is violated iff it sees an odd number of
  errors.
* `Cslib.BitString.ExpanderCode.card_unsat_le`: at most `c · d(y, w)` checks are violated.
* `Cslib.BitString.ExpanderCode.two_pow_sub_le_card_code`,
  `Cslib.BitString.ExpanderCode.one_sub_card_div_card_le_rate`,
  `Cslib.BitString.ExpanderCode.one_sub_div_le_rate_of_isBiregular`: the rate.
* `Cslib.BitString.ExpanderCode.lt_hammingDist`, `Cslib.BitString.ExpanderCode.lt_minDist`,
  `Cslib.BitString.ExpanderCode.two_mul_mul_le_hammingDist`: the distance.

## References

* [M. Sipser, D. A. Spielman, *Expander codes*][SipserSpielman1996]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2025], §11.3
* [V. Guruswami, A. Sharma, *Expander codes and their decoding*][GuruswamiSharma2010], §1
-/

@[expose] public section

namespace Cslib.BitString.ExpanderCode

open Finset Matrix Cslib.Bipartite

variable {ι κ : Type*} [Fintype ι] [Fintype κ] (G : ι → κ → Prop) [∀ i j, Decidable (G i j)]

/-- The check matrix of a bipartite graph: entry `(j, i)` is `true` iff variable `i` is adjacent
to check `j`. -/
def checkMatrix : Matrix κ ι Bool :=
  Matrix.of fun j i => decide (G i j)

/-- The **expander code** of a bipartite graph [SipserSpielman1996]
[GuruswamiRudraSudan2025, Definition 11.3.1]: the words on which every check, the sum of the
bits of its neighbours, vanishes. -/
def code : Submodule Bool (ι → Bool) :=
  LinearMap.ker (checkMatrix G).mulVecLin

/-- The syndrome of a word: the value of every check. -/
def syndrome (x : ι → Bool) : κ → Bool :=
  checkMatrix G *ᵥ x

/-- The checks violated by a word. -/
def unsat (x : ι → Bool) : Finset κ :=
  {j | syndrome G x j = true}

variable {G}

omit [Fintype κ] in
/-- Check `j` is the parity of the bits of its neighbours. -/
theorem syndrome_apply (x : ι → Bool) (j : κ) :
    syndrome G x j = parityOn {i | G i j} x := by
  rw [syndrome, mulVec, dotProduct_comm, BitString.dotProduct_eq_parityOn]
  congr 1

omit [Fintype κ] in
theorem mem_code {x : ι → Bool} : x ∈ code G ↔ syndrome G x = 0 :=
  LinearMap.mem_ker

omit [Fintype κ] in
theorem syndrome_add (x y : ι → Bool) : syndrome G (x + y) = syndrome G x + syndrome G y :=
  mulVec_add _ _ _

omit [Fintype κ] in
/-- Adding a codeword does not change the syndrome. -/
theorem syndrome_add_of_mem {x w : ι → Bool} (hw : w ∈ code G) :
    syndrome G (x + w) = syndrome G x := by
  rw [syndrome_add, mem_code.1 hw, add_zero]

/-- A word is a codeword iff it violates no check. -/
theorem mem_code_iff_unsat_eq_empty {x : ι → Bool} : x ∈ code G ↔ unsat G x = ∅ := by
  rw [mem_code, unsat, filter_eq_empty_iff, funext_iff]
  refine forall_congr' fun j => ?_
  simp only [Pi.zero_apply, mem_univ, true_implies, Bool.not_eq_true]
  rfl

omit [Fintype ι] in
private theorem add_apply_eq_true {x y : ι → Bool} {i : ι} :
    (x + y) i = true ↔ x i ≠ y i := by
  rw [Pi.add_apply]
  cases x i <;> cases y i <;> decide

/-- A check is violated by `y` iff it sees an odd number of errors, the positions where `y`
differs from a codeword `w`. -/
theorem mem_unsat_iff {y w : ι → Bool} (hw : w ∈ code G) {j : κ} :
    j ∈ unsat G y ↔ Odd #(({i | y i ≠ w i} : Finset ι).bipartiteBelow G j) := by
  rw [unsat, mem_filter, ← syndrome_add_of_mem hw, syndrome_apply, parityOn, decide_eq_true_iff,
    ← Nat.odd_iff]
  simp only [mem_univ, true_and]
  congr! 2
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_bipartiteBelow, add_apply_eq_true]
  exact and_comm

/-- The unique neighbours of the errors are violated checks. -/
theorem uniqueNbhd_subset_unsat {y w : ι → Bool} (hw : w ∈ code G) :
    uniqueNbhd G {i | y i ≠ w i} ⊆ unsat G y := by
  intro j hj
  rw [mem_unsat_iff hw, mem_uniqueNbhd.1 hj]
  exact odd_one

/-- Violated checks are neighbours of the errors. -/
theorem unsat_subset_nbhd {y w : ι → Bool} (hw : w ∈ code G) :
    unsat G y ⊆ nbhd G {i | y i ≠ w i} := by
  intro j hj
  obtain ⟨i, hi⟩ := card_pos.1 (mem_unsat_iff hw |>.1 hj).pos
  rw [mem_bipartiteBelow] at hi
  exact mem_nbhd.2 ⟨i, hi⟩

/-- If left degrees are at most `c`, a word at distance `e` from a codeword violates at most
`c e` checks. -/
theorem card_unsat_le {c : ℕ} (hG : IsLeftBounded G c) {y w : ι → Bool} (hw : w ∈ code G) :
    #(unsat G y) ≤ c * hammingDist y w :=
  (card_le_card (unsat_subset_nbhd hw)).trans (card_nbhd_le hG _)

/-! ### Rate -/

/-- `2 ^ n ≤ |C(G)| · 2 ^ m`: the code is the kernel of a linear map into `2 ^ m` words. -/
theorem two_pow_card_le :
    2 ^ Fintype.card ι ≤ Nat.card (code G) * 2 ^ Fintype.card κ := by
  have h := AddSubgroup.card_ker_mul_card_range (checkMatrix G).mulVecLin.toAddMonoidHom
  have hker : Nat.card ((checkMatrix G).mulVecLin.toAddMonoidHom.ker) = Nat.card (code G) := rfl
  have hrange : Nat.card ((checkMatrix G).mulVecLin.toAddMonoidHom.range) ≤
      2 ^ Fintype.card κ := by
    refine (Nat.card_le_card_of_injective _ Subtype.val_injective).trans ?_
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
      Nat.card_eq_fintype_card (α := κ)]
  rw [hker, Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
    Nat.card_eq_fintype_card (α := ι)] at h
  rw [← h]
  exact Nat.mul_le_mul_left _ hrange

/-- **Rate** [GuruswamiRudraSudan2025, Proposition 11.3.5]: with `n` variables and `m` checks the
code has dimension at least `n - m`, i.e. at least `2 ^ (n - m)` codewords. -/
theorem two_pow_sub_le_card_code :
    2 ^ (Fintype.card ι - Fintype.card κ) ≤ Nat.card (code G) := by
  rcases le_total (Fintype.card κ) (Fintype.card ι) with hle | hle
  · have h2 : 2 ^ (Fintype.card ι - Fintype.card κ) * 2 ^ Fintype.card κ =
        2 ^ Fintype.card ι := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    exact le_of_mul_le_mul_right (h2.le.trans two_pow_card_le) (by positivity)
  · rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    exact Nat.card_pos

/-- **Rate** in real form: `log₂ |C(G)| / n ≥ 1 - m / n`. -/
theorem one_sub_card_div_card_le_rate (hι : 0 < Fintype.card ι) :
    1 - (Fintype.card κ : ℝ) / Fintype.card ι ≤
      Real.logb 2 (Nat.card (code G)) / Fintype.card ι := by
  have hpos : (0 : ℝ) < Nat.card (code G) := by
    exact_mod_cast Nat.card_pos (α := code G)
  have h : (2 : ℝ) ^ (Fintype.card ι : ℝ) ≤
      (Nat.card (code G) : ℝ) * (2 : ℝ) ^ (Fintype.card κ : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact_mod_cast two_pow_card_le (G := G)
  have hlog : (Fintype.card ι : ℝ) ≤ Real.logb 2 (Nat.card (code G)) + Fintype.card κ := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h
    rwa [Real.logb_mul hpos.ne' (by positivity), Real.logb_rpow (by norm_num) (by norm_num),
      Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hι' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
  rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hι', one_mul]
  linarith

/-- **Rate of a biregular expander code**: if `G` is `(c, d)`-biregular, the rate
`log₂ |C(G)| / n` is at least `1 - c / d`. -/
theorem one_sub_div_le_rate_of_isBiregular {c d : ℕ} (hG : IsBiregular G c d) (hd : 0 < d)
    (hι : 0 < Fintype.card ι) :
    1 - (c : ℝ) / d ≤ Real.logb 2 (Nat.card (code G)) / Fintype.card ι := by
  have h : c * Fintype.card ι = Fintype.card κ * d := (Nat.mul_comm _ _).trans hG.card_mul_eq
  have hcd : (c : ℝ) / d = Fintype.card κ / Fintype.card ι := by
    have hι' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hι.ne'
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [div_eq_div_iff hd' hι']
    exact_mod_cast h
  rw [hcd]
  exact one_sub_card_div_card_le_rate hι

/-! ### Distance -/

/-- The set where two codewords differ has no unique neighbour. -/
theorem uniqueNbhd_eq_empty {x w : ι → Bool} (hx : x ∈ code G) (hw : w ∈ code G) :
    uniqueNbhd G {i | x i ≠ w i} = ∅ := by
  refine eq_empty_of_forall_notMem fun j hj => ?_
  have := uniqueNbhd_subset_unsat hw hj
  rw [mem_code_iff_unsat_eq_empty.1 hx] at this
  exact notMem_empty j this

/-- **Distance of expander codes** [GuruswamiRudraSudan2025, Theorem 11.3.6]. If left degrees are
at most `c` and sets of at most `k` variables expand by a factor `α > c / 2`, distinct codewords
differ in more than `k` positions. -/
theorem lt_hammingDist {c k : ℕ} {α : ℝ} (hG : IsLeftBounded G c) (hE : IsVertexExpander G k α)
    (hα : c < 2 * α) {x w : ι → Bool} (hx : x ∈ code G) (hw : w ∈ code G) (hxw : x ≠ w) :
    k < hammingDist x w := by
  by_contra hk
  push Not at hk
  have h := hE.le_card_uniqueNbhd hG hk
  rw [uniqueNbhd_eq_empty hx hw, card_empty, Nat.cast_zero] at h
  have hpos : 0 < #({i | x i ≠ w i} : Finset ι) := hammingDist_pos.2 hxw
  have hpos' : (0 : ℝ) < #({i | x i ≠ w i} : Finset ι) := by exact_mod_cast hpos
  have : (0 : ℝ) < (2 * α - c) * #({i | x i ≠ w i} : Finset ι) := mul_pos (by linarith) hpos'
  linarith

/-- The minimum distance of the expander code exceeds `k`. -/
theorem lt_minDist {c k : ℕ} {α : ℝ} (hG : IsLeftBounded G c) (hE : IsVertexExpander G k α)
    (hα : c < 2 * α) : (k : ℕ∞) < Code.minDist (code G : Set (ι → Bool)) :=
  Code.natCast_lt_minDist_iff.2 fun _ hx _ hw hxw => lt_hammingDist hG hE hα hx hw hxw

/-- **Improved distance of expander codes** [GuruswamiRudraSudan2025, Theorem 11.3.8]
[GuruswamiSharma2010, Theorem 4]. Under the hypotheses of `lt_hammingDist`, distinct codewords
satisfy `2 α k ≤ c · d(x, w)`. With `α = c (1 - ε)` and `k = γ n` this is the source's distance
bound `2 γ (1 - ε) n`. -/
theorem two_mul_mul_le_hammingDist {c k : ℕ} {α : ℝ} (hG : IsLeftBounded G c)
    (hE : IsVertexExpander G k α) (hα : c < 2 * α) {x w : ι → Bool} (hx : x ∈ code G)
    (hw : w ∈ code G) (hxw : x ≠ w) :
    2 * α * k ≤ c * hammingDist x w := by
  classical
  set E : Finset ι := {i | x i ≠ w i}
  have hEk : k ≤ #E := (lt_hammingDist hG hE hα hx hw hxw).le
  obtain ⟨T, hTE, hT⟩ := exists_subset_card_eq hEk
  have hsub : uniqueNbhd G T ⊆ nbhd G (E \ T) := by
    intro j hj
    by_contra hj'
    have hU : j ∈ uniqueNbhd G E := by
      rw [mem_uniqueNbhd, ← mem_uniqueNbhd.1 hj]
      congr 1
      ext i
      simp only [mem_bipartiteBelow]
      refine ⟨fun h => ⟨?_, h.2⟩, fun h => ⟨hTE h.1, h.2⟩⟩
      by_contra hiT
      exact hj' (mem_nbhd.2 ⟨i, mem_sdiff.2 ⟨h.1, hiT⟩, h.2⟩)
    rw [uniqueNbhd_eq_empty hx hw] at hU
    exact notMem_empty j hU
  have h1 := hE.le_card_uniqueNbhd hG hT.le
  have h2 : #(uniqueNbhd G T) ≤ c * (#E - k) := by
    refine (card_le_card hsub).trans ((card_nbhd_le hG _).trans ?_)
    rw [card_sdiff_of_subset hTE, hT]
  have h3 : (#(uniqueNbhd G T) : ℝ) ≤ c * (#E - k) := by
    have : ((#E - k : ℕ) : ℝ) = #E - k := by push_cast [hEk]; ring
    rw [← this]
    exact_mod_cast h2
  rw [hT] at h1
  change 2 * α * k ≤ c * (#E : ℝ)
  nlinarith

end Cslib.BitString.ExpanderCode
