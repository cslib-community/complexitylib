/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceNetwork
public import Complexity.Foundations.Data.Nat.Choose.Vandermonde
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Degrees and the wire bound (D.3) of the incidence network

Bounds on the incidence network of Lemma D.2 of [OpenAI2026ETH]
(`Cslib.Circuits.Frontier.IncidenceNetwork.network`), in terms of the system: the degrees of the
group vertices (pp. 55–56) and the number of index wires (D.3) (p. 56).

**Degrees.** The pair `(g, h)` has at most as many index wires as incidences, since
`C(N, d) ≤ 2 ^ N` (`IncidenceNetwork.width_le`). So a test group has at most as many ports as the
incidences of its tests, at most `(a / J + 1) S` if every scope has at most `S` variables
(`IncidenceNetwork.length_rowPorts_le`), and a variable group at most `(n / J + 1) D` if every
variable lies in at most `D` scopes (`IncidenceNetwork.length_colPorts_le`). These are the
paper's bounds `n ^ (3/4) λ ^ O(1)` at `J = ⌈n ^ (1/4)⌉`.

**Wires** (D.3). With `N` incidences in all (`IncidenceNetwork.numInc`), a live array has
`2 ^ M ≤ 2 ^ (J²) C(N + K, K)` for its `M` index wires (`IncidenceNetwork.two_pow_numWires_le`):
`⌈log₂ C⌉ < log₂ C + 1`, and the subsets of the pairs together form one subset of size at most
`K` of the `N` incidences, which the paper bounds by stars and bars. When `N + K ≤ R K`,
`C(N + K, K) ≤ (3 R) ^ K` (`IncidenceNetwork.choose_add_le_pow`, from `K ^ K ≤ 3 ^ K K!`), so
`M ≤ J² + K ⌈log₂ (3 R)⌉` (`IncidenceNetwork.numWires_le`). This is (D.3) in the form
`J² + K log₂ (e (N + K) / K)` with `e` replaced by `3`.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.numInc`: the number of incidences.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.length_rowPorts_le`,
  `Cslib.Circuits.Frontier.IncidenceNetwork.length_colPorts_le`: the degrees.
* `Cslib.Circuits.Frontier.IncidenceNetwork.two_pow_numWires_le`,
  `Cslib.Circuits.Frontier.IncidenceNetwork.numWires_le`: the wire bound (D.3).

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma D.2 (pp. 54–56).
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.Complexity Finset

/-- **The number of incidences** of a system: the sum of the sizes of the scopes. -/
@[expose] def numInc (sys : List (List (List ℕ))) : ℕ :=
  (sys.map fun eq => (equationVars eq).length).sum

/-! ### Incidences -/

variable {J : ℕ} {sys : List (List (List ℕ))} {d : List ℕ}

/-- **A pair has at most as many index wires as incidences**: `C(N, d) ≤ 2 ^ N`. -/
theorem width_le (g h : ℕ) : width J sys d g h ≤ (pairInc J sys g h).length :=
  Nat.clog_le_of_le_pow (Nat.choose_le_two_pow _ _)

/-- The incidences of a pair, test by test. -/
theorem length_pairInc (g h : ℕ) :
    (pairInc J sys g h).length = ((List.residueClass J sys.length g).map fun i =>
      ((equationVars (sys.getD i [])).filter (· % J = h)).length).sum := by
  rw [pairInc, List.length_flatMap]
  conv_rhs => rw [← List.zipIdx_map_fst 0 (List.residueClass J sys.length g), List.map_map]
  simp [Function.comp_def]

/-- **The incidences of a test group** are those of its tests. -/
theorem sum_length_pairInc_row (hJ : 0 < J) (g : ℕ) :
    ∑ h ∈ range J, (pairInc J sys g h).length =
      ((List.residueClass J sys.length g).map fun i =>
        (equationVars (sys.getD i [])).length).sum := by
  simp only [length_pairInc]
  rw [Finset.sum_list_sum_comm]
  simp only [List.sum_length_filter_mod hJ]


/-- **The incidences of all pairs** are the incidences of the system. -/
theorem sum_sum_length_pairInc (hJ : 0 < J) :
    ∑ g ∈ range J, ∑ h ∈ range J, (pairInc J sys g h).length = numInc sys := by
  rw [Finset.sum_congr rfl fun g _ => sum_length_pairInc_row hJ g, List.sum_residueClass hJ, numInc]
  conv_rhs => rw [← List.map_getD_range sys []]
  rw [List.map_map]
  rfl

/-- **The incidences of a variable group**, test by test. -/
theorem sum_length_pairInc_col (hJ : 0 < J) (h : ℕ) :
    ∑ g ∈ range J, (pairInc J sys g h).length = ((List.range sys.length).map fun i =>
      ((equationVars (sys.getD i [])).filter (· % J = h)).length).sum := by
  simp only [length_pairInc]
  exact List.sum_residueClass hJ _ _

/-! ### Degrees -/

/-- **The degree of a test group**: at most `(a / J + 1) S` for `a` tests, if every scope has at
most `S` variables. -/
theorem length_rowPorts_le (hJ : 0 < J) (g : ℕ) {S : ℕ}
    (hS : ∀ eq ∈ sys, (equationVars eq).length ≤ S) :
    (rowPorts J sys d g).length ≤ (sys.length / J + 1) * S := by
  rw [length_rowPorts]
  calc ∑ h ∈ range J, width J sys d g h ≤ ∑ h ∈ range J, (pairInc J sys g h).length :=
        Finset.sum_le_sum fun h _ => width_le g h
    _ = ((List.residueClass J sys.length g).map fun i =>
          (equationVars (sys.getD i [])).length).sum :=
        sum_length_pairInc_row hJ g
    _ ≤ (List.residueClass J sys.length g).length * S := by
        refine (List.sum_le_length_nsmul _ S fun x hx => ?_).trans (by simp)
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        have hi' : i < sys.length := List.mem_range.mp (List.mem_filter.mp hi).1
        rw [List.getD_eq_getElem _ _ hi']
        exact hS _ (List.getElem_mem hi')
    _ ≤ (sys.length / J + 1) * S :=
        Nat.mul_le_mul_right _ (List.length_residueClass_le J sys.length g)

/-- The number of scopes containing a variable, as a sum over the tests. -/
theorem varDegree_eq_sum (v : ℕ) :
    varDegree v sys = ((List.range sys.length).map fun i =>
      if v ∈ equationVars (sys.getD i []) then 1 else 0).sum := by
  rw [varDegree]
  conv_lhs => rw [← List.map_getD_range sys []]
  rw [List.countP_map, List.countP_eq_length_filter, List.length_filter_eq_sum]
  simp

/-- **The degree of a variable group** `h < J`: at most `(n / J + 1) D` if every variable is
below `n` and lies in at most `D` scopes. -/
theorem length_colPorts_le (hJ : 0 < J) {h : ℕ} (hh : h < J) {n D : ℕ}
    (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) (hD : ∀ v < n, varDegree v sys ≤ D) :
    (colPorts J sys d h).length ≤ (n / J + 1) * D := by
  rw [length_colPorts h hh]
  -- Per test, the scope variables in group `h` are the variables of group `h` in the scope.
  have hper : ∀ i < sys.length, ((equationVars (sys.getD i [])).filter (· % J = h)).length =
      ((List.residueClass J n h).filter fun v => v ∈ equationVars (sys.getD i [])).length := by
    intro i hi
    refine List.Perm.length_eq ((List.perm_ext_iff_of_nodup ((nodup_sortDedup _).filter _)
      (((List.nodup_range).filter _).filter _)).mpr fun v => ?_)
    have hm : v ∈ equationVars (sys.getD i []) → v < n := fun hv => by
      obtain ⟨m, hm, hvm⟩ := mem_equationVars.mp hv
      rw [List.getD_eq_getElem _ _ hi] at hm
      exact hvars _ (List.getElem_mem hi) m hm v hvm
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨hv, hJv⟩
      exact ⟨⟨hm hv, hJv⟩, hv⟩
    · rintro ⟨⟨_, hJv⟩, hv⟩
      exact ⟨hv, hJv⟩
  calc ∑ g ∈ range J, width J sys d g h ≤ ∑ g ∈ range J, (pairInc J sys g h).length :=
        Finset.sum_le_sum fun g _ => width_le g h
    _ = ((List.range sys.length).map fun i =>
          ((equationVars (sys.getD i [])).filter (· % J = h)).length).sum :=
        sum_length_pairInc_col hJ h
    _ = ((List.residueClass J n h).map fun v => varDegree v sys).sum := by
        rw [List.map_congr_left fun i hi => hper i (List.mem_range.mp hi)]
        simp only [List.length_filter_eq_sum, decide_eq_true_eq]
        rw [List.sum_map_range_eq_sum_range, Finset.sum_list_sum_comm]
        simp only [varDegree_eq_sum, List.sum_map_range_eq_sum_range]
    _ ≤ (List.residueClass J n h).length * D := by
        refine (List.sum_le_length_nsmul _ D fun x hx => ?_).trans (by simp)
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
        exact hD v (List.mem_range.mp (List.mem_filter.mp hv).1)
    _ ≤ (n / J + 1) * D := Nat.mul_le_mul_right _ (List.length_residueClass_le J n h)

/-! ### The wire bound (D.3) -/

/-- **The index wires of one pair**: `2 ^ ⌈log₂ C(N, d)⌉ ≤ 2 C(N, d')`, where `d' = d` if
`d ≤ N` and `d' = 0` otherwise. -/
theorem two_pow_clog_choose_le (N d : ℕ) :
    2 ^ Nat.clog 2 (N.choose d) ≤ 2 * N.choose (if d ≤ N then d else 0) := by
  split_ifs with hd
  · have hC := Nat.choose_pos hd
    rcases Nat.lt_or_ge 1 (N.choose d) with h1 | h1
    · have h2 := Nat.pow_pred_clog_lt_self one_lt_two h1
      have h3 : 1 ≤ Nat.clog 2 (N.choose d) := Nat.succ_le_of_lt (Nat.clog_pos one_lt_two h1)
      calc 2 ^ Nat.clog 2 (N.choose d) = 2 * 2 ^ (Nat.clog 2 (N.choose d)).pred := by
            conv_lhs => rw [← Nat.succ_pred_eq_of_pos h3]
            rw [pow_succ']
        _ ≤ 2 * N.choose d := by omega
    · have : N.choose d = 1 := by omega
      rw [this]
      simp
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- The entries of the array below `J²`, pair by pair. -/
theorem sum_getD_eq (J : ℕ) (d : List ℕ) :
    ∑ g ∈ range J, ∑ h ∈ range J, d.getD (g * J + h) 0 =
      ((List.range (J * J)).map (d.getD · 0)).sum := by
  rw [← List.flatMap_range_mul, List.sum_map_flatMap, List.sum_map_range_eq_sum_range]
  simp only [List.map_map, List.sum_map_range_eq_sum_range, Function.comp_def]

/-- **The wire bound (D.3), exponential form**: a live array has `2 ^ M ≤ 2 ^ (J²) C(N + K, K)`
for its `M` index wires and the `N` incidences of the system. -/
theorem two_pow_numWires_le (hJ : 0 < J) {K : ℕ} (hlive : live J K d = true) :
    2 ^ numWires J sys d ≤ 2 ^ (J * J) * (numInc sys + K).choose K := by
  set D' : ℕ → ℕ → ℕ := fun g h =>
    if d.getD (g * J + h) 0 ≤ (pairInc J sys g h).length then d.getD (g * J + h) 0 else 0
  have hD' : ∑ g ∈ range J, ∑ h ∈ range J, D' g h ≤ K := by
    have hK : ((List.range (J * J)).map (d.getD · 0)).sum ≤ K := by
      simpa [live] using hlive
    refine le_trans (Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun h _ => ?_)
      ((sum_getD_eq J d).le.trans hK)
    simp only [D']
    split_ifs <;> omega
  calc 2 ^ numWires J sys d
      = ∏ g ∈ range J, ∏ h ∈ range J, 2 ^ width J sys d g h := by
        rw [numWires_eq, ← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_congr rfl fun g _ => (Finset.prod_pow_eq_pow_sum _ _ _).symm
    _ ≤ ∏ g ∈ range J, ∏ h ∈ range J, (2 * (pairInc J sys g h).length.choose (D' g h)) :=
        Finset.prod_le_prod fun g _ => Finset.prod_le_prod fun h _ => two_pow_clog_choose_le _ _
    _ = 2 ^ (J * J) * ∏ g ∈ range J, ∏ h ∈ range J, (pairInc J sys g h).length.choose (D' g h) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
    _ ≤ 2 ^ (J * J) * (numInc sys).choose (∑ g ∈ range J, ∑ h ∈ range J, D' g h) := by
        refine Nat.mul_le_mul_left _ ?_
        rw [← sum_sum_length_pairInc hJ]
        exact (Finset.prod_le_prod fun g _ => Nat.prod_choose_le_choose_sum _ _ _).trans
          (Nat.prod_choose_le_choose_sum _ _ _)
    _ ≤ 2 ^ (J * J) * (numInc sys + K).choose K :=
        Nat.mul_le_mul_left _ (Nat.choose_le_add_choose_of_le hD')

/-- **The wire bound (D.3)**: if `N + K ≤ R K` for the `N` incidences of the system, a live array
has at most `J² + K ⌈log₂ (3 R)⌉` index wires. -/
theorem numWires_le (hJ : 0 < J) {K R : ℕ} (hlive : live J K d = true)
    (hR : numInc sys + K ≤ R * K) :
    numWires J sys d ≤ J * J + K * Nat.clog 2 (3 * R) := by
  have h1 := two_pow_numWires_le (sys := sys) hJ hlive
  have h2 : (numInc sys + K).choose K ≤ 2 ^ (K * Nat.clog 2 (3 * R)) :=
    (Nat.add_choose_le_three_mul_pow hR).trans (by
      rw [pow_mul']
      exact Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two _) _)
  have h3 : 2 ^ numWires J sys d ≤ 2 ^ (J * J + K * Nat.clog 2 (3 * R)) := by
    rw [pow_add]
    exact h1.trans (Nat.mul_le_mul_left _ h2)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3

end Cslib.Circuits.Frontier.IncidenceNetwork
