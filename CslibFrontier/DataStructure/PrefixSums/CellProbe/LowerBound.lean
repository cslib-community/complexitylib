/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.CellProbe.Chronogram
public import Mathlib.Data.ZMod.Defs
import CslibFrontier.Foundations.Data.Code.HammingBound
import CslibFrontier.Foundations.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic

/-!
# Fredman–Saks lower bound for dynamic prefix parity

Dynamic prefix parity maintains an array `A : Fin n → ZMod 2`, initially zero, under the operations
`update i b` (set `A i` to `b`) and `query i` (return `A 0 + ⋯ + A i`). This is the partial-sums
problem of [PatrascuDemaine2006], §2.1, over `ZMod 2`. Section 3.1 (p. 5) of that paper credits
Fredman and Saks [FredmanSaks1989] with the first dynamic cell-probe lower bounds for this problem,
via the chronogram method, including the trade-off `t_q = Ω(lg n / (lg b + lg t_u))` for word size
`b`, update time `t_u` and query time `t_q`.

This file proves that trade-off for deterministic step-indexed cell-probe schemes
`D : Cslib.CellProbe.IndexedScheme (Op n) Result S w`, with worst-case depth bounds `t_u` on updates
and `t_q` on queries. If `S ≤ 2 ^ w`, then `log_β n ≤ 128 t_q + 1` for
`β = max 4 (8 t_u (2 w + 1))`, i.e. `t_q = Ω(log n / log (t_u (w + 1)))`.

## Proof outline

The hard instance has `L` epochs. Epoch `j < L` writes `β ^ (L - j)` bits `X j k` at positions
`k β ^ j L + j`, and query `q < β ^ L` at position `q L + L - 1` then answers
`Σ_j (X j 0 + ⋯ + X j (q / β ^ j))` (`prefixParity_hardUpdates`). Fix every epoch except `j`.

* A query whose probes avoid the cells last probed by epoch `j`
  (`Cslib.CellProbe.IndexedScheme.lastCells`) answers identically on the *overlay*: the memory
  before epoch `j`, overwritten with the final contents of the cells probed by later epochs.
* The later epochs perform at most `t_u · 2 β ^ (L - j - 1)` probes, so the overlay ranges over at
  most `(S 2 ^ w + 1) ^ (2 t_u β ^ (L - j - 1))` memories. This is at most `2 ^ (β ^ (L - j) / 4)`
  when `(S 2 ^ w + 1) ^ (8 t_u) ≤ 2 ^ β`.
* If two values of epoch `j` each leave fewer than `β ^ L / 32` queries *bad* (meeting the
  last-probed cells), and they have the same overlay, then their prefix-sum vectors differ in at
  most `β ^ (L - j) / 16` places. A volume bound then shows that at most half of the
  `2 ^ β ^ (L - j)` values are of this kind, so on average `β ^ L / 64` queries are bad for epoch
  `j`.
* The last-probed sets of distinct epochs are disjoint, so a query that is bad for `e` epochs
  makes at least `e` probes. Summing over the `L` epochs, the average query makes at least
  `L / 64` probes.

## Scope

* The schemes are deterministic and the update bound `t_u` is worst-case. Amortized update times
  and Las Vegas randomization, which [PatrascuDemaine2006], Theorem 2.1, handles for its stronger
  `Ω(lg n)` trade-offs, are not covered.
* Updates assign a bit, as in [PatrascuDemaine2006], §2.1. The scheme sees the global step index
  (`IndexedScheme`), so the bound also applies to time-invariant schemes via
  `Cslib.CellProbe.Scheme.toIndexed`.
* The constants `64`, `128` and `8 t_u (2 w + 1)` are not optimized. The hard-instance forms
  `card_mul_le_sum_probes`, `exists_le_mul_probes` and `le_mul_of_answersQueries` need only
  `(S 2 ^ w + 1) ^ (8 t_u) ≤ 2 ^ β`, with no relation between `S` and `w`.

## Main definitions

* `Cslib.DataStructure.PrefixSums.CellProbe.Op`, `Cslib.DataStructure.PrefixSums.CellProbe.Result`,
  `Cslib.DataStructure.PrefixSums.CellProbe.applyOp`,
  `Cslib.DataStructure.PrefixSums.CellProbe.arrayOf`,
  `Cslib.DataStructure.PrefixSums.CellProbe.prefixParity`: dynamic prefix parity.
* `Cslib.DataStructure.PrefixSums.CellProbe.AnswersQueries`: correctness of a cell-probe scheme.
* `Cslib.DataStructure.PrefixSums.CellProbe.hardPos`,
  `Cslib.DataStructure.PrefixSums.CellProbe.hardQueryPos`: the positions of the hard instance.
* `Cslib.DataStructure.PrefixSums.CellProbe.HardInput`,
  `Cslib.DataStructure.PrefixSums.CellProbe.hardSeg`,
  `Cslib.DataStructure.PrefixSums.CellProbe.hardUpdates`,
  `Cslib.DataStructure.PrefixSums.CellProbe.hardTime`,
  `Cslib.DataStructure.PrefixSums.CellProbe.hardQueryIdx`: the inputs, epochs, update sequence,
  its length, and the queries of the hard instance.
* `Cslib.DataStructure.PrefixSums.CellProbe.hardAnswer`: the answer formula on the hard instance.

## Main results

* `Cslib.DataStructure.PrefixSums.CellProbe.prefixParity_hardUpdates`: the answers on the hard
  instance.
* `Cslib.DataStructure.PrefixSums.CellProbe.card_mul_le_sum_probes`: on the hard distribution, the
  average query makes at least `L / 64` probes.
* `Cslib.DataStructure.PrefixSums.CellProbe.exists_le_mul_probes`: some hard input and query force
  `L / 64` probes.
* `Cslib.DataStructure.PrefixSums.CellProbe.le_mul_of_answersQueries`: `L ≤ 64 t_q`.
* `Cslib.DataStructure.PrefixSums.CellProbe.log_le_of_answersQueries`: the Fredman–Saks bound
  `log_β n ≤ 128 t_q + 1` for `β = max 4 (8 t_u (2 w + 1))` and `S ≤ 2 ^ w`.

## References

* [M. L. Fredman and M. E. Saks, *The cell probe complexity of dynamic data
  structures*][FredmanSaks1989]
* [M. Pătraşcu and E. D. Demaine, *Logarithmic Lower Bounds in the Cell-Probe
  Model*][PatrascuDemaine2006]
-/

public section

namespace Cslib.DataStructure.PrefixSums.CellProbe

open Finset Cslib.CellProbe

/-! ### Dynamic prefix parity -/

/-- Operations of dynamic prefix parity on an array of `n` bits: `update i b` sets bit `i` to `b`,
and `query i` asks for the parity of bits `0, …, i`. -/
inductive Op (n : ℕ) : Type where
  | update (i : Fin n) (b : ZMod 2)
  | query (i : Fin n)
  deriving DecidableEq

/-- `update` returns nothing and `query` returns a bit. -/
abbrev Result {n : ℕ} : Op n → Type
  | .update _ _ => PUnit
  | .query _ => ZMod 2

/-- The effect of one operation on the array. -/
@[expose] def applyOp {n : ℕ} (A : Fin n → ZMod 2) : Op n → Fin n → ZMod 2
  | .update i b => Function.update A i b
  | .query _ => A

/-- The array after the operations `ops`, starting from the all-zero array. -/
@[expose] def arrayOf {n : ℕ} (ops : List (Op n)) : Fin n → ZMod 2 :=
  ops.foldl applyOp 0

/-- The prefix parity `A 0 + ⋯ + A i`. -/
@[expose] def prefixParity {n : ℕ} (A : Fin n → ZMod 2) (i : Fin n) : ZMod 2 :=
  ∑ k ∈ Iic i, A k

/-- The prefix parity as a sum over the natural numbers `k ≤ i`. -/
theorem prefixParity_eq_sum_range {n : ℕ} (A : Fin n → ZMod 2) (i : Fin n) :
    prefixParity A i = ∑ k ∈ range (i + 1), if h : k < n then A ⟨k, h⟩ else 0 := by
  refine sum_bij (fun k _ => (k : ℕ)) (fun k hk => ?_) (fun k _ k' _ h => Fin.ext h)
    (fun k hk => ?_) (fun k _ => ?_)
  · exact mem_range.mpr (Nat.lt_succ_of_le (Fin.le_def.mp (mem_Iic.mp hk)))
  · have hk' : k < i + 1 := mem_range.mp hk
    exact ⟨⟨k, by omega⟩, mem_Iic.mpr (Fin.le_def.mpr (by simp only; omega)), rfl⟩
  · rw [dite_eq_left k.2]

/-- A bit vector is determined by its prefix parities. -/
theorem prefixParity_injective {n : ℕ} : Function.Injective (prefixParity (n := n)) := by
  intro x y hxy
  funext ⟨k, hk⟩
  have hP : ∀ r : Fin n, prefixParity x r = prefixParity y r := fun r => congrFun hxy r
  cases k with
  | zero =>
    have := hP ⟨0, hk⟩
    simpa [prefixParity_eq_sum_range, hk] using this
  | succ k =>
    have h1 := hP ⟨k + 1, hk⟩
    have h0 := hP ⟨k, by omega⟩
    simp only [prefixParity_eq_sum_range] at h1 h0
    rw [sum_range_succ, h0, sum_range_succ _ (k + 1)] at h1
    simpa [hk] using h1

/-- A cell-probe scheme answers prefix-parity queries correctly: after any operation sequence
`ops`, a query at `i` returns the prefix parity of the current array. -/
@[expose] def AnswersQueries {n S w : ℕ} (D : IndexedScheme (Op n) Result S w) : Prop :=
  ∀ (ops : List (Op n)) (i : Fin n),
    ((D.step ops.length (.query i)).run (D.runSeq ops).2).1 = prefixParity (arrayOf ops) i

/-- If every update of `ops` to bit `i` writes `v`, then after `ops` bit `i` is `v` if some update
wrote it, and unchanged otherwise. -/
theorem foldl_applyOp_apply {n : ℕ} (ops : List (Op n)) (A : Fin n → ZMod 2) (i : Fin n)
    (v : ZMod 2) (hv : ∀ b, Op.update i b ∈ ops → b = v) :
    ops.foldl applyOp A i = if ∃ b, Op.update i b ∈ ops then v else A i := by
  induction ops generalizing A with
  | nil => simp
  | cons o rest ih =>
    rw [List.foldl_cons, ih _ fun b hb => hv b (List.mem_cons_of_mem _ hb)]
    cases o with
    | update i' b' =>
      by_cases hi : i' = i
      · subst hi
        have hb' : b' = v := hv b' List.mem_cons_self
        simp [applyOp, hb']
      · have hne : ∀ b, Op.update i b ≠ Op.update i' b' := fun b h => hi (Op.update.inj h).1.symm
        simp [applyOp, Function.update_of_ne (Ne.symm hi), hne]
    | query i' =>
      simp [applyOp]

/-! ### The hard instance

Epoch `j < L` writes `β ^ (L - j)` bits `X j k` at positions `hardPos β L j k = k β ^ j L + j`,
and the query `q < β ^ L` asks for the prefix parity up to `hardQueryPos L q = q L + (L - 1)`.
Bit `k` of epoch `j` lies in the prefix of query `q` iff `k β ^ j ≤ q`, so the answer of query
`q` is the sum over epochs of the prefix parities of `X j` up to `q / β ^ j`. -/

/-- Position of bit `k` of epoch `j`. -/
@[expose] def hardPos (β L j k : ℕ) : ℕ := k * β ^ j * L + j

/-- Position queried by query `q`. -/
@[expose] def hardQueryPos (L q : ℕ) : ℕ := q * L + (L - 1)

/-- Every bit of the hard instance lies inside the array. -/
theorem hardPos_lt {β L n j k : ℕ} (hn : L * β ^ L ≤ n) (hj : j < L) (hk : k < β ^ (L - j)) :
    hardPos β L j k < n := by
  have hβ : β ^ L = β ^ (L - j) * β ^ j := by rw [← pow_add, Nat.sub_add_cancel hj.le]
  have h1 : (k + 1) * β ^ j ≤ β ^ (L - j) * β ^ j := Nat.mul_le_mul_right _ hk
  have h2 : 1 ≤ β ^ j := by
    rcases Nat.eq_zero_or_pos β with h0 | h0
    · subst h0; rw [zero_pow (by omega)] at hk; omega
    · exact Nat.one_le_pow _ _ h0
  have h3 : (k + 1) * β ^ j * L ≤ β ^ L * L := by rw [hβ]; exact Nat.mul_le_mul_right _ h1
  have h4 : (k + 1) * β ^ j * L = k * β ^ j * L + β ^ j * L := by ring
  have h5 : L ≤ β ^ j * L := Nat.le_mul_of_pos_left _ h2
  unfold hardPos
  rw [mul_comm] at hn
  omega

/-- Every query of the hard instance lies inside the array. -/
theorem hardQueryPos_lt {β L n q : ℕ} (hn : L * β ^ L ≤ n) (hL : 0 < L) (hq : q < β ^ L) :
    hardQueryPos L q < n := by
  have h1 : (q + 1) * L ≤ β ^ L * L := Nat.mul_le_mul_right _ hq
  have h2 : (q + 1) * L = q * L + L := by ring
  unfold hardQueryPos
  rw [mul_comm] at hn
  omega

/-- Bit `k` of epoch `j` lies in the prefix of query `q` iff `k β ^ j ≤ q`. -/
theorem hardPos_le_hardQueryPos_iff {β L j k q : ℕ} (hj : j < L) :
    hardPos β L j k ≤ hardQueryPos L q ↔ k * β ^ j ≤ q := by
  unfold hardPos hardQueryPos
  generalize k * β ^ j = a
  constructor
  · intro h
    by_contra hlt
    have h1 : (q + 1) * L ≤ a * L := Nat.mul_le_mul_right _ (by omega)
    have h2 : (q + 1) * L = q * L + L := by ring
    omega
  · intro h
    have := Nat.mul_le_mul_right L h
    omega

/-- Distinct bits of the hard instance sit at distinct positions. -/
theorem hardPos_inj {β L j j' k k' : ℕ} (hβ : 0 < β) (hj : j < L) (hj' : j' < L)
    (h : hardPos β L j k = hardPos β L j' k') : j = j' ∧ k = k' := by
  unfold hardPos at h
  have hjj : j = j' := by
    have := congrArg (· % L) h
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] using this
  subst hjj
  refine ⟨rfl, ?_⟩
  have hL : 0 < L := by omega
  have := Nat.eq_of_mul_eq_mul_right hL (Nat.add_right_cancel h)
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hβ j) this

/-- Inputs of the hard instance: epoch `j < L` carries `β ^ (L - j)` bits. -/
abbrev HardInput (β L : ℕ) : Type := (j : Fin L) → Fin (β ^ (L - (j : ℕ))) → ZMod 2

/-! ### Arithmetic -/

/-- The epochs after `j` write at most twice as many bits as epoch `j + 1`. -/
private theorem sum_Ioo_pow_sub_le {β : ℕ} (hβ : 2 ≤ β) (j M : ℕ) :
    ∑ k ∈ Ioo j (j + 1 + M), β ^ (j + 1 + M - k) ≤ 2 * β ^ M := by
  induction M generalizing j with
  | zero =>
    have h : Ioo j (j + 1 + 0) = ∅ := by ext k; simp
    rw [h, sum_empty]
    exact Nat.zero_le _
  | succ M ih =>
    rw [← Ico_add_one_left_eq_Ioo, sum_eq_sum_Ico_succ_bot (by omega),
      Ico_add_one_left_eq_Ioo]
    have h := ih (j + 1)
    have he : j + 1 + (M + 1) - (j + 1) = M + 1 := by omega
    have hr : j + 1 + (M + 1) = j + 1 + 1 + M := by omega
    rw [he, hr]
    have hp : β ^ (M + 1) = β ^ M * β := pow_succ β M
    have hb : 2 * β ^ M ≤ β ^ M * β := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hβ
    omega

private theorem sum_Ioo_pow_sub_le' {β L j : ℕ} (hβ : 2 ≤ β) (hj : j < L) :
    ∑ k ∈ Ioo j L, β ^ (L - k) ≤ 2 * β ^ (L - j - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, L = j + 1 + M := ⟨L - j - 1, by omega⟩
  have he : j + 1 + M - j - 1 = M := by omega
  rw [he]
  exact sum_Ioo_pow_sub_le hβ j M

/-- `2 V N ≤ 2 ^ K` when `V = Σ_{i ≤ K / 16} (K choose i)`, `N ^ 4 ≤ 2 ^ K` and `K ≥ 4`. -/
private theorem two_mul_sum_choose_mul_le {K N : ℕ} (hK : 4 ≤ K) (hN : N ^ 4 ≤ 2 ^ K) :
    2 * ((∑ i ∈ range (K / 16 + 1), K.choose i) * N) ≤ 2 ^ K := by
  set e := K / 16 with he
  set V := ∑ i ∈ range (e + 1), K.choose i
  have hV : V * 16 ^ K ≤ 17 ^ K * 16 ^ e := by
    simpa [mul_comm] using sum_range_choose_mul_pow_le 16 K e
  have he4 : (16 ^ e) ^ 4 ≤ 2 ^ K := by
    rw [← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h17 : (17 ^ K) ^ 4 ≤ (2 ^ K) ^ 17 := by
    rw [← pow_mul, ← pow_mul, mul_comm K 4, mul_comm K 17, pow_mul, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) K
  have h16 : 16 ≤ 2 ^ K :=
    (show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hK
  have h4 : (2 * (V * N)) ^ 4 * (2 ^ K) ^ 16 ≤ (2 ^ K) ^ 4 * (2 ^ K) ^ 16 := by
    have h16K : (16 : ℕ) ^ K = (2 ^ K) ^ 4 := by
      rw [← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, mul_comm]
    calc (2 * (V * N)) ^ 4 * (2 ^ K) ^ 16 = 16 * (V * 16 ^ K) ^ 4 * N ^ 4 := by
          rw [h16K]; ring
      _ ≤ 16 * (17 ^ K * 16 ^ e) ^ 4 * 2 ^ K :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hV 4)) hN
      _ = 16 * (17 ^ K) ^ 4 * (16 ^ e) ^ 4 * 2 ^ K := by ring
      _ ≤ 2 ^ K * (2 ^ K) ^ 17 * 2 ^ K * 2 ^ K :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul h16 h17) he4)
      _ = (2 ^ K) ^ 4 * (2 ^ K) ^ 16 := by ring
  have h4' := Nat.le_of_mul_le_mul_right h4 (by positivity)
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h4'

/-- Updating coordinate `j` with every value and summing over all inputs counts each input
`Fintype.card (α j)` times. -/
private theorem sum_sum_update {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (g : (∀ i, α i) → ℕ) (j : ι) :
    ∑ X : ∀ i, α i, ∑ x : α j, g (Function.update X j x) =
      Fintype.card (α j) * ∑ X : ∀ i, α i, g X := by
  let e : (∀ i, α i) × α j ≃ (∀ i, α i) × α j :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  calc ∑ X : ∀ i, α i, ∑ x : α j, g (Function.update X j x)
      = ∑ p : (∀ i, α i) × α j, g (Function.update p.1 j p.2) :=
        (Fintype.sum_prod_type' _).symm
    _ = ∑ p : (∀ i, α i) × α j, g p.1 := Fintype.sum_equiv e _ _ fun p => rfl
    _ = Fintype.card (α j) * ∑ X : ∀ i, α i, g X := by
        rw [Fintype.sum_prod_type]
        simp only [sum_const, card_univ, smul_eq_mul, mul_sum, mul_comm]

section HardInstance

variable {β L n : ℕ} (hn : L * β ^ L ≤ n)

/-- Epoch `j` of the hard update sequence: write `X j k` at `hardPos β L j k` for all
`k < β ^ (L - j)`; empty for `j ≥ L`. -/
def hardSeg (X : HardInput β L) (j : ℕ) : List (Op n) :=
  if hj : j < L then
    List.ofFn fun k : Fin (β ^ (L - j)) =>
      Op.update ⟨hardPos β L j k, hardPos_lt hn hj k.2⟩ (X ⟨j, hj⟩ k)
  else []

/-- The hard update sequence: epochs `0, …, L - 1` in order. -/
def hardUpdates (X : HardInput β L) : List (Op n) :=
  (List.range L).flatMap (hardSeg hn X)

/-- The position asked by query `q < β ^ L`. -/
def hardQueryIdx (hL : 0 < L) (q : Fin (β ^ L)) : Fin n :=
  ⟨hardQueryPos L q, hardQueryPos_lt hn hL q.2⟩

/-- The number of updates of the hard sequence. -/
@[expose] def hardTime (β L : ℕ) : ℕ := ∑ k ∈ range L, β ^ (L - k)

/-- Query `q < β ^ L` falls in block `q / β ^ j < β ^ (L - j)` of epoch `j`. -/
theorem hardBlock_lt {q j : ℕ} (hj : j < L) (hq : q < β ^ L) : q / β ^ j < β ^ (L - j) :=
  Nat.div_lt_of_lt_mul (by rwa [← pow_add, Nat.add_sub_of_le hj.le])

/-- The answer of query `q` on the hard input `X`: the sum over epochs `j` of the prefix parity of
`X j` up to `q / β ^ j`. -/
@[expose] def hardAnswer (X : HardInput β L) (q : Fin (β ^ L)) : ZMod 2 :=
  ∑ j : Fin L, prefixParity (X j) ⟨q / β ^ (j : ℕ), hardBlock_lt j.2 q.2⟩

/-- The hard update sequence consists of updates only. -/
theorem mem_hardSeg {X : HardInput β L} {j : ℕ} {o : Op n} (ho : o ∈ hardSeg hn X j) :
    ∃ i b, o = Op.update i b := by
  unfold hardSeg at ho
  split_ifs at ho with hj
  · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ho
    exact ⟨_, _, rfl⟩
  · simp at ho

theorem length_hardSeg (X : HardInput β L) (j : ℕ) :
    (hardSeg hn X j).length = if j < L then β ^ (L - j) else 0 := by
  unfold hardSeg
  split_ifs <;> simp

/-- Every update of the hard sequence writes `X j k` at `hardPos β L j k`. -/
theorem update_mem_hardUpdates {X : HardInput β L} {i : Fin n} {b : ZMod 2}
    (h : Op.update i b ∈ hardUpdates hn X) :
    ∃ (j : Fin L) (k : Fin (β ^ (L - (j : ℕ)))), i.val = hardPos β L j k ∧ b = X j k := by
  unfold hardUpdates at h
  obtain ⟨j, hj, h⟩ := List.mem_flatMap.mp h
  have hjL : j < L := List.mem_range.mp hj
  unfold hardSeg at h
  rw [dite_eq_left hjL] at h
  obtain ⟨k, hk⟩ := List.mem_ofFn.mp h
  obtain ⟨hi, hb⟩ := Op.update.inj hk
  exact ⟨⟨j, hjL⟩, k, by rw [← hi], hb.symm⟩

theorem hardPos_mem_hardUpdates (X : HardInput β L) (j : Fin L) (k : Fin (β ^ (L - (j : ℕ)))) :
    Op.update ⟨hardPos β L j k, hardPos_lt hn j.2 k.2⟩ (X j k) ∈ hardUpdates hn X := by
  unfold hardUpdates
  refine List.mem_flatMap.mpr ⟨j, List.mem_range.mpr j.2, ?_⟩
  unfold hardSeg
  rw [dite_eq_left j.2]
  exact List.mem_ofFn.mpr ⟨k, rfl⟩

/-- After the hard updates, bit `k` of epoch `j` holds `X j k`. -/
theorem arrayOf_hardUpdates_hardPos (hβ : 0 < β) (X : HardInput β L) (j : Fin L)
    (k : Fin (β ^ (L - (j : ℕ)))) :
    arrayOf (hardUpdates hn X) ⟨hardPos β L j k, hardPos_lt hn j.2 k.2⟩ = X j k := by
  unfold arrayOf
  rw [foldl_applyOp_apply _ _ _ (X j k)]
  · rw [ite_eq_left ⟨_, hardPos_mem_hardUpdates hn X j k⟩]
  · intro b hb
    obtain ⟨j', k', hpos, rfl⟩ := update_mem_hardUpdates hn hb
    obtain ⟨hjj, hkk⟩ := hardPos_inj hβ j.2 j'.2 hpos
    obtain rfl : j = j' := Fin.ext hjj
    obtain rfl : k = k' := Fin.ext hkk
    rfl

/-- After the hard updates, the positions not written by any epoch hold `0`. -/
theorem arrayOf_hardUpdates_eq_zero (X : HardInput β L) {i : Fin n}
    (hi : ∀ (j : Fin L) (k : Fin (β ^ (L - (j : ℕ)))), i.val ≠ hardPos β L j k) :
    arrayOf (hardUpdates hn X) i = 0 := by
  have hno : ∀ b, Op.update i b ∉ hardUpdates hn X := fun b hb => by
    obtain ⟨j, k, hpos, -⟩ := update_mem_hardUpdates hn hb
    exact hi j k hpos
  unfold arrayOf
  rw [foldl_applyOp_apply _ _ _ 0 fun b hb => absurd hb (hno b)]
  simp [hno]

/-- **Answer formula**: the correct answer to query `q` after the hard updates of `X`. -/
theorem prefixParity_hardUpdates (hβ : 0 < β) (hL : 0 < L) (X : HardInput β L)
    (q : Fin (β ^ L)) :
    prefixParity (arrayOf (hardUpdates hn X)) (hardQueryIdx hn hL q) = hardAnswer X q := by
  rw [prefixParity, hardAnswer]
  simp only [prefixParity_eq_sum_range]
  rw [sum_sigma']
  symm
  refine sum_bij_ne_zero
    (fun x hx _ => ⟨hardPos β L x.1 x.2, hardPos_lt hn x.1.2 (by
      have h1 : x.2 < q / β ^ (x.1 : ℕ) + 1 := mem_range.mp (mem_sigma.mp hx).2
      have h2 := hardBlock_lt x.1.2 q.2
      omega)⟩) ?_ ?_ ?_ ?_
  · intro x hx _
    have h1 : x.2 < q / β ^ (x.1 : ℕ) + 1 := mem_range.mp (mem_sigma.mp hx).2
    refine mem_Iic.mpr (Fin.mk_le_mk.mpr ((hardPos_le_hardQueryPos_iff x.1.2).mpr ?_))
    exact (Nat.le_div_iff_mul_le (pow_pos hβ _)).mp (by omega)
  · intro x hx _ y hy _ hxy
    obtain ⟨hj, hk⟩ := hardPos_inj hβ x.1.2 y.1.2 (Fin.mk.inj hxy)
    exact Sigma.ext (Fin.ext hj) (heq_of_eq hk)
  · intro i hi hne
    have hex : ∃ (j : Fin L) (k : Fin (β ^ (L - (j : ℕ)))), i.val = hardPos β L j k := by
      by_contra hcon
      push Not at hcon
      exact hne (arrayOf_hardUpdates_eq_zero hn X hcon)
    obtain ⟨j, k, hpos⟩ := hex
    have hle : hardPos β L j k ≤ hardQueryPos L q := by
      rw [← hpos]; exact Fin.le_iff_val_le_val.mp (mem_Iic.mp hi)
    have hkq := (hardPos_le_hardQueryPos_iff j.2).mp hle
    have hkr : (k : ℕ) < q / β ^ (j : ℕ) + 1 :=
      Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (pow_pos hβ _)).mpr hkq)
    have hik : (⟨hardPos β L j k, hardPos_lt hn j.2 k.2⟩ : Fin n) = i := Fin.ext hpos.symm
    refine ⟨⟨j, k⟩, mem_sigma.mpr ⟨mem_univ _, mem_range.mpr hkr⟩, ?_, hik⟩
    rw [dite_eq_left k.2]
    rw [← hik, arrayOf_hardUpdates_hardPos hn hβ X j k] at hne
    exact hne
  · intro x hx _
    have h1 : x.2 < q / β ^ (x.1 : ℕ) + 1 := mem_range.mp (mem_sigma.mp hx).2
    have h2 := hardBlock_lt x.1.2 q.2
    have hk : x.2 < β ^ (L - x.1) := by omega
    rw [dite_eq_left hk]
    exact (arrayOf_hardUpdates_hardPos hn hβ X x.1 ⟨x.2, hk⟩).symm

/-- The first `L'` epochs together have `Σ_{k < L'} |hardSeg k|` operations. -/
theorem length_flatMap_hardSeg (X : HardInput β L) (L' : ℕ) :
    ((List.range L').flatMap (hardSeg hn X)).length =
      ∑ k ∈ range L', (hardSeg hn X k).length := by
  induction L' with
  | zero => simp
  | succ L' ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append, ih,
      sum_range_succ]

/-- The hard update sequence has `hardTime β L` operations, whatever the input. -/
theorem length_hardUpdates (X : HardInput β L) : (hardUpdates hn X).length = hardTime β L := by
  rw [hardUpdates, length_flatMap_hardSeg, hardTime]
  exact sum_congr rfl fun k hk => by rw [length_hardSeg, ite_eq_left (mem_range.mp hk)]

/-- Changing the bits of epoch `j` leaves the other epochs unchanged. -/
theorem hardSeg_update_of_ne (X : HardInput β L) {j : Fin L}
    (x : Fin (β ^ (L - (j : ℕ))) → ZMod 2) {k : ℕ} (hk : k ≠ j) :
    hardSeg hn (Function.update X j x) k = hardSeg hn X k := by
  unfold hardSeg
  split_ifs with hkL
  · have hne : (⟨k, hkL⟩ : Fin L) ≠ j := fun h => hk (congrArg Fin.val h)
    simp only [Function.update_of_ne hne]
  · rfl

/-- Changing the bits of epoch `j` changes only the `j`-th summand of the answer. -/
theorem hardAnswer_update (X : HardInput β L) (j : Fin L)
    (x : Fin (β ^ (L - (j : ℕ))) → ZMod 2) (q : Fin (β ^ L)) :
    hardAnswer (Function.update X j x) q =
      prefixParity x ⟨q / β ^ (j : ℕ), hardBlock_lt j.2 q.2⟩ +
        ∑ k ∈ univ.erase j, prefixParity (X k) ⟨q / β ^ (k : ℕ), hardBlock_lt k.2 q.2⟩ := by
  unfold hardAnswer
  rw [← add_sum_erase _ _ (mem_univ j), Function.update_self]
  congr 1
  exact sum_congr rfl fun k hk => by rw [Function.update_of_ne (ne_of_mem_erase hk)]

/-! ### The encoding argument -/

section Encoding

variable {S w : ℕ} (D : IndexedScheme (Op n) Result S w)

/-- The memory before epoch `j` of the hard update sequence of `X`. -/
private def hardMem (X : HardInput β L) (j : ℕ) : Mem S w :=
  D.segMem (hardSeg hn X) 0 D.init j

/-- The probe tree of query `q` after the hard update sequence. -/
private def hardQuery (hL : 0 < L) (q : Fin (β ^ L)) : ProbeTree S w (ZMod 2) :=
  D.step (hardTime β L) (.query (hardQueryIdx hn hL q))

/-- The overlay of epoch `j`: the final contents of the cells probed after epoch `j`, over the
memory before epoch `j`. -/
private def hardOverlay (X : HardInput β L) (j : ℕ) : Mem S w :=
  D.overlayMem (hardSeg hn X) 0 D.init L j

/-- The queries whose probes meet the cells last touched by epoch `j`. -/
private def badSet (hL : 0 < L) (X : HardInput β L) (j : ℕ) : Finset (Fin (β ^ L)) :=
  {q | ((hardQuery hn D hL q).probedCells (hardMem hn D X L) ∩
    D.lastCells (hardSeg hn X) 0 D.init L j).Nonempty}

private theorem runSeq_hardUpdates (X : HardInput β L) :
    (D.runSeq (hardUpdates hn X)).2 = hardMem hn D X L :=
  (D.runInterval_flatMap_range (hardSeg hn X) 0 D.init L).1

private theorem run_hardQuery (hD : AnswersQueries D) (hβ : 0 < β) (hL : 0 < L)
    (X : HardInput β L) (q : Fin (β ^ L)) :
    ((hardQuery hn D hL q).run (hardMem hn D X L)).1 = hardAnswer X q := by
  have h := hD (hardUpdates hn X) (hardQueryIdx hn hL q)
  rw [length_hardUpdates, runSeq_hardUpdates, prefixParity_hardUpdates hn hβ hL] at h
  exact h

/-- **Query replay**: a query that avoids the cells last touched by epoch `j` answers correctly on
the overlay. -/
private theorem run_hardOverlay (hD : AnswersQueries D) (hβ : 0 < β) (hL : 0 < L)
    (X : HardInput β L) {j : ℕ} (hj : j < L) {q : Fin (β ^ L)} (hq : q ∉ badSet hn D hL X j) :
    ((hardQuery hn D hL q).run (hardOverlay hn D X j)).1 = hardAnswer X q := by
  rw [← run_hardQuery hn D hD hβ hL X q]
  refine (D.run_overlayMem_eq _ 0 D.init hj _ ?_).1
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  exact fun hne => hq (mem_filter.mpr ⟨mem_univ _, hne⟩)

private theorem hardMem_update (X : HardInput β L) (j : Fin L)
    (x : Fin (β ^ (L - (j : ℕ))) → ZMod 2) :
    hardMem hn D (Function.update X j x) j = hardMem hn D X j :=
  D.segMem_congr 0 D.init fun k hk => hardSeg_update_of_ne hn X x (by omega)

/-- **Fibre**: two values of epoch `j` with the same overlay have the same prefix sums at every
block `q / β ^ j` of a query that is good for both. -/
private theorem prefixParity_eq_of_hardOverlay_eq (hD : AnswersQueries D) (hβ : 0 < β) (hL : 0 < L)
    (X : HardInput β L) (j : Fin L) {x x' : Fin (β ^ (L - (j : ℕ))) → ZMod 2}
    (hov : hardOverlay hn D (Function.update X j x) j =
      hardOverlay hn D (Function.update X j x') j)
    {q : Fin (β ^ L)} (hq : q ∉ badSet hn D hL (Function.update X j x) j)
    (hq' : q ∉ badSet hn D hL (Function.update X j x') j) :
    prefixParity x ⟨q / β ^ (j : ℕ), hardBlock_lt j.2 q.2⟩ =
      prefixParity x' ⟨q / β ^ (j : ℕ), hardBlock_lt j.2 q.2⟩ := by
  have h := run_hardOverlay hn D hD hβ hL _ j.2 hq
  have h' := run_hardOverlay hn D hD hβ hL _ j.2 hq'
  rw [hov, h', hardAnswer_update, hardAnswer_update] at h
  exact (add_right_cancel h).symm

private theorem mul_pow_add_lt {β L j r s : ℕ} (hj : j ≤ L) (hr : r < β ^ (L - j))
    (hs : s < β ^ j) : r * β ^ j + s < β ^ L := by
  have h1 : (r + 1) * β ^ j ≤ β ^ (L - j) * β ^ j := Nat.mul_le_mul_right _ hr
  rw [← pow_add, Nat.sub_add_cancel hj] at h1
  have h2 : (r + 1) * β ^ j = r * β ^ j + β ^ j := by ring
  omega

/-- If two values of epoch `j` have the same overlay, their prefix-sum vectors differ in at most
`(#bad + #bad') / β ^ j` places: each differing block of `β ^ j` queries is bad for one of them. -/
private theorem hammingDist_mul_le (hD : AnswersQueries D) (hβ : 0 < β) (hL : 0 < L)
    (X : HardInput β L) (j : Fin L) {x x' : Fin (β ^ (L - (j : ℕ))) → ZMod 2}
    (hov : hardOverlay hn D (Function.update X j x) j =
      hardOverlay hn D (Function.update X j x') j) :
    hammingDist (prefixParity x) (prefixParity x') * β ^ (j : ℕ) ≤
      #(badSet hn D hL (Function.update X j x) j) +
        #(badSet hn D hL (Function.update X j x') j) := by
  have hpos : 0 < β ^ (j : ℕ) := pow_pos hβ _
  have hdiv : ∀ (r : Fin (β ^ (L - (j : ℕ)))) (s : Fin (β ^ (j : ℕ))),
      (r * β ^ (j : ℕ) + s) / β ^ (j : ℕ) = r := fun r s => by
    rw [add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt s.2, zero_add]
  let f : Fin (β ^ (L - (j : ℕ))) × Fin (β ^ (j : ℕ)) → Fin (β ^ L) := fun p =>
    ⟨p.1 * β ^ (j : ℕ) + p.2, mul_pow_add_lt j.2.le p.1.2 p.2.2⟩
  calc hammingDist (prefixParity x) (prefixParity x') * β ^ (j : ℕ)
      = #(({r | prefixParity x r ≠ prefixParity x' r} : Finset (Fin (β ^ (L - (j : ℕ))))) ×ˢ
          (univ : Finset (Fin (β ^ (j : ℕ))))) := by
        rw [card_product, card_univ, Fintype.card_fin]
        rfl
    _ ≤ #(badSet hn D hL (Function.update X j x) j ∪
          badSet hn D hL (Function.update X j x') j) := by
        refine card_le_card_of_injOn f (fun p hp => ?_) (fun p _ p' _ hpp => ?_)
        · have hne : prefixParity x p.1 ≠ prefixParity x' p.1 :=
            (mem_filter.mp (mem_product.mp hp).1).2
          by_contra hq
          rw [coe_union, Set.mem_union, not_or] at hq
          apply hne
          have h := prefixParity_eq_of_hardOverlay_eq hn D hD hβ hL X j hov hq.1 hq.2
          have hp1 : (⟨(f p : ℕ) / β ^ (j : ℕ), hardBlock_lt j.2 (f p).2⟩ :
              Fin (β ^ (L - (j : ℕ)))) = p.1 := Fin.ext (hdiv p.1 p.2)
          rwa [hp1] at h
        · have h := congrArg Fin.val hpp
          have h1 : p.1 = p'.1 := Fin.ext <| by
            have := congrArg (· / β ^ (j : ℕ)) h
            simpa only [f, hdiv] using this
          have h2 : (p.2 : ℕ) = p'.2 := by
            simp only [f, h1] at h
            omega
          exact Prod.ext h1 (Fin.ext h2)
    _ ≤ _ := card_union_le _ _

/-- **Counting the good values**: fewer than half of the values `x` of epoch `j` make fewer than
`β ^ L / 32` queries bad, since such values are determined by their overlay up to a small
Hamming ball, and few overlays exist. -/
private theorem two_mul_card_good_le (hD : AnswersQueries D) (hβ : 4 ≤ β) (hL : 0 < L)
    {tu : ℕ} (htu : ∀ t i b, (D.step t (.update i b)).depth ≤ tu)
    (hH : (S * 2 ^ w + 1) ^ (8 * tu) ≤ 2 ^ β) (X : HardInput β L) (j : Fin L) :
    2 * #{x : Fin (β ^ (L - (j : ℕ))) → ZMod 2 |
      32 * #(badSet hn D hL (Function.update X j x) j) < β ^ L} ≤ 2 ^ β ^ (L - (j : ℕ)) := by
  have hβ0 : 0 < β := by omega
  have hβj : β ^ L = β ^ (L - (j : ℕ)) * β ^ (j : ℕ) := by
    rw [← pow_add, Nat.sub_add_cancel j.2.le]
  have hK : β ^ (L - (j : ℕ)) = β ^ (L - (j : ℕ) - 1) * β := by
    rw [← pow_succ]; congr 1; omega
  have hK4 : 4 ≤ β ^ (L - (j : ℕ)) :=
    hβ.trans (le_self_pow (by omega) (by omega))
  set G := ({x : Fin (β ^ (L - (j : ℕ))) → ZMod 2 |
      32 * #(badSet hn D hL (Function.update X j x) j) < β ^ L} : Finset _) with hG
  set ov := fun x : Fin (β ^ (L - (j : ℕ))) → ZMod 2 =>
    hardOverlay hn D (Function.update X j x) j with hov
  set R := tu * (2 * β ^ (L - (j : ℕ) - 1)) with hR
  -- two good values with the same overlay have close prefix-sum vectors
  have hfib : ∀ x ∈ G, ∀ x' ∈ G, ov x = ov x' →
      hammingDist (prefixParity x) (prefixParity x') ≤ β ^ (L - (j : ℕ)) / 16 := by
    intro x hx x' hx' hxx
    have h := hammingDist_mul_le hn D hD hβ0 hL X j hxx
    have hb := (mem_filter.mp hx).2
    have hb' := (mem_filter.mp hx').2
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have h32 : 32 * (hammingDist (prefixParity x) (prefixParity x') * β ^ (j : ℕ)) <
        2 * (β ^ (L - (j : ℕ)) * β ^ (j : ℕ)) := by
      rw [← hβj]; omega
    have h16 : hammingDist (prefixParity x) (prefixParity x') * 16 * β ^ (j : ℕ) <
        β ^ (L - (j : ℕ)) * β ^ (j : ℕ) := by
      have : 32 * (hammingDist (prefixParity x) (prefixParity x') * β ^ (j : ℕ)) =
          2 * (hammingDist (prefixParity x) (prefixParity x') * 16 * β ^ (j : ℕ)) := by ring
      omega
    exact (Nat.lt_of_mul_lt_mul_right h16).le
  -- every overlay lies close to the memory before epoch `j`
  have himage : #(G.image ov) ≤ (S * 2 ^ w + 1) ^ R := by
    have hsub : G.image ov ⊆
        ({m : Mem S w | hammingDist (hardMem hn D X j) m ≤ R} : Finset (Mem S w)) := by
      intro m hm
      obtain ⟨x, -, rfl⟩ := mem_image.mp hm
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      rw [← hardMem_update hn D X j x]
      refine (D.hammingDist_overlayMem_le _ 0 D.init L j).trans
        ((D.card_laterCells_le _ 0 D.init (d := tu) fun k _ t o ho => ?_).trans ?_)
      · obtain ⟨i, b, rfl⟩ := mem_hardSeg hn ho
        exact htu t i b
      · refine Nat.mul_le_mul_left _ ((sum_le_sum fun k hk => ?_).trans
          (sum_Ioo_pow_sub_le' (by omega) j.2))
        rw [length_hardSeg, ite_eq_left (mem_Ioo.mp hk).2]
    refine (card_le_card hsub).trans ((card_filter_hammingDist_le_le_pow _ R).trans ?_)
    exact Nat.pow_le_pow_left (by have := Nat.sub_le (2 ^ w) 1; nlinarith) R
  -- each fibre of the overlay map lies in a Hamming ball of radius `K / 16`
  have hfibre : ∀ m ∈ G.image ov, #{x ∈ G | ov x = m} ≤
      ∑ i ∈ range (β ^ (L - (j : ℕ)) / 16 + 1), (β ^ (L - (j : ℕ))).choose i := by
    intro m hm
    obtain ⟨x₀, hx₀, rfl⟩ := mem_image.mp hm
    have hball : #{y : Fin (β ^ (L - (j : ℕ))) → ZMod 2 |
        hammingDist (prefixParity x₀) y ≤ β ^ (L - (j : ℕ)) / 16} =
        ∑ i ∈ range (β ^ (L - (j : ℕ)) / 16 + 1), (β ^ (L - (j : ℕ))).choose i := by
      rw [Code.card_filter_hammingDist_le_eq_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [Code.card_filter_hammingDist_eq_choose_mul_pow (q := 2) (fun _ => ZMod.card 2)]
      simp
    rw [← hball]
    refine card_le_card_of_injOn prefixParity (fun x hx => ?_)
      (fun x _ x' _ h => prefixParity_injective h)
    have hx := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_univ _, hfib x₀ hx₀ x hx.1 hx.2.symm⟩
  have hN : ((S * 2 ^ w + 1) ^ R) ^ 4 ≤ 2 ^ β ^ (L - (j : ℕ)) := by
    calc ((S * 2 ^ w + 1) ^ R) ^ 4 = ((S * 2 ^ w + 1) ^ (8 * tu)) ^ β ^ (L - (j : ℕ) - 1) := by
          rw [← pow_mul, ← pow_mul, hR]; ring_nf
      _ ≤ (2 ^ β) ^ β ^ (L - (j : ℕ) - 1) := Nat.pow_le_pow_left hH _
      _ = 2 ^ β ^ (L - (j : ℕ)) := by rw [← pow_mul, mul_comm, ← hK]
  calc 2 * #G ≤ 2 * ((∑ i ∈ range (β ^ (L - (j : ℕ)) / 16 + 1), (β ^ (L - (j : ℕ))).choose i) *
        #(G.image ov)) := Nat.mul_le_mul_left _ ((card_le_mul_card_image G _ hfibre).trans
          (by rw [mul_comm]))
    _ ≤ 2 * ((∑ i ∈ range (β ^ (L - (j : ℕ)) / 16 + 1), (β ^ (L - (j : ℕ))).choose i) *
        (S * 2 ^ w + 1) ^ R) := by gcongr
    _ ≤ 2 ^ β ^ (L - (j : ℕ)) := two_mul_sum_choose_mul_le hK4 hN

/-- **Averaging over epoch `j`**: on average over the values `x` of epoch `j`, at least
`β ^ L / 64` queries are bad. -/
private theorem pow_mul_le_sum_card_badSet (hD : AnswersQueries D) (hβ : 4 ≤ β) (hL : 0 < L)
    {tu : ℕ} (htu : ∀ t i b, (D.step t (.update i b)).depth ≤ tu)
    (hH : (S * 2 ^ w + 1) ^ (8 * tu) ≤ 2 ^ β) (X : HardInput β L) (j : Fin L) :
    2 ^ β ^ (L - (j : ℕ)) * β ^ L ≤
      64 * ∑ x : Fin (β ^ (L - (j : ℕ))) → ZMod 2,
        #(badSet hn D hL (Function.update X j x) j) := by
  have hG := two_mul_card_good_le hn D hD hβ hL htu hH X j
  have hsplit := card_filter_add_card_filter_not (s := univ)
    (fun x : Fin (β ^ (L - (j : ℕ))) → ZMod 2 =>
      32 * #(badSet hn D hL (Function.update X j x) j) < β ^ L)
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card] at hsplit
  set B := fun x : Fin (β ^ (L - (j : ℕ))) → ZMod 2 =>
    #(badSet hn D hL (Function.update X j x) j) with hB
  set Gc := ({x | ¬ 32 * B x < β ^ L} : Finset (Fin (β ^ (L - (j : ℕ))) → ZMod 2))
  have hGc : #Gc * β ^ L ≤ 32 * ∑ x ∈ Gc, B x := by
    rw [mul_sum, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun x hx => le_of_not_gt (mem_filter.mp hx).2
  have hsub : ∑ x ∈ Gc, B x ≤ ∑ x, B x := sum_le_sum_of_subset (subset_univ _)
  have h2 : 2 ^ β ^ (L - (j : ℕ)) ≤ 2 * #Gc := by omega
  calc 2 ^ β ^ (L - (j : ℕ)) * β ^ L ≤ 2 * #Gc * β ^ L := Nat.mul_le_mul_right _ h2
    _ = 2 * (#Gc * β ^ L) := by ring
    _ ≤ 64 * ∑ x, B x := by omega

/-- **Epoch counting**: the bad sets of the `L` epochs are charged to distinct probed cells. -/
private theorem sum_card_badSet_le (hL : 0 < L) (X : HardInput β L) :
    ∑ j : Fin L, #(badSet hn D hL X j) ≤
      ∑ q : Fin (β ^ L), (hardQuery hn D hL q).probes (hardMem hn D X L) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => #(badSet hn D hL X j))]
  calc ∑ j ∈ range L, #(badSet hn D hL X j)
      = ∑ q : Fin (β ^ L), #{j ∈ range L | ((hardQuery hn D hL q).probedCells
          (hardMem hn D X L) ∩ D.lastCells (hardSeg hn X) 0 D.init L j).Nonempty} := by
        simp only [badSet, card_filter]
        exact sum_comm
    _ ≤ ∑ q : Fin (β ^ L), (hardQuery hn D hL q).probes (hardMem hn D X L) :=
        sum_le_sum fun q _ => (D.card_filter_lastCells_le _ 0 D.init L _).trans
          ((hardQuery hn D hL q).card_probedCells_le_probes _)

end Encoding

end HardInstance

/-! ### The lower bound -/

variable {n S w : ℕ}

/-- **Fredman–Saks lower bound, average form.** Let `D` be a deterministic step-indexed cell-probe
scheme for dynamic prefix parity on `n` bits with `S` cells of `w` bits, every update of which has
depth at most `tu`. If `L β ^ L ≤ n`, `β ≥ 4` and `(S 2 ^ w + 1) ^ (8 tu) ≤ 2 ^ β`, then over a
uniformly random input `X` of the hard instance and a uniformly random query `q < β ^ L`, the query
after the hard update sequence of `X` makes at least `L / 64` probes on average. -/
theorem card_mul_le_sum_probes {β L : ℕ} (hn : L * β ^ L ≤ n) (hL : 0 < L)
    (D : IndexedScheme (Op n) Result S w) (hD : AnswersQueries D) (hβ : 4 ≤ β) {tu : ℕ}
    (htu : ∀ t i b, (D.step t (.update i b)).depth ≤ tu)
    (hH : (S * 2 ^ w + 1) ^ (8 * tu) ≤ 2 ^ β) :
    Fintype.card (HardInput β L) * β ^ L * L ≤
      64 * ∑ X : HardInput β L, ∑ q : Fin (β ^ L),
        (D.step (hardUpdates hn X).length (.query (hardQueryIdx hn hL q))).probes
          (D.runSeq (hardUpdates hn X)).2 := by
  have hcol : ∀ j : Fin L, Fintype.card (HardInput β L) * β ^ L ≤
      ∑ X : HardInput β L, #(badSet hn D hL X j) * 64 := by
    intro j
    have hcard : Fintype.card (Fin (β ^ (L - (j : ℕ))) → ZMod 2) = 2 ^ β ^ (L - (j : ℕ)) := by
      rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    refine Nat.le_of_mul_le_mul_left (c := 2 ^ β ^ (L - (j : ℕ))) ?_ (by positivity)
    calc 2 ^ β ^ (L - (j : ℕ)) * (Fintype.card (HardInput β L) * β ^ L)
        = ∑ X : HardInput β L, 2 ^ β ^ (L - (j : ℕ)) * β ^ L := by
          rw [sum_const, card_univ, smul_eq_mul]; ring
      _ ≤ ∑ X : HardInput β L, ∑ x : Fin (β ^ (L - (j : ℕ))) → ZMod 2,
            #(badSet hn D hL (Function.update X j x) j) * 64 :=
          sum_le_sum fun X _ => by
            rw [← sum_mul, mul_comm _ 64]
            exact pow_mul_le_sum_card_badSet hn D hD hβ hL htu hH X j
      _ = 2 ^ β ^ (L - (j : ℕ)) * ∑ X : HardInput β L, #(badSet hn D hL X j) * 64 := by
          rw [sum_sum_update (fun X => #(badSet hn D hL X j) * 64) j, hcard]
  have hsum : Fintype.card (HardInput β L) * (L * β ^ L) ≤
      ∑ X : HardInput β L, ∑ j : Fin L, #(badSet hn D hL X j) * 64 := by
    rw [sum_comm]
    calc Fintype.card (HardInput β L) * (L * β ^ L)
        = ∑ _j : Fin L, Fintype.card (HardInput β L) * β ^ L := by
          rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; ring
      _ ≤ _ := sum_le_sum fun j _ => hcol j
  calc Fintype.card (HardInput β L) * β ^ L * L
      = Fintype.card (HardInput β L) * (L * β ^ L) := by ring
    _ ≤ ∑ X : HardInput β L, ∑ j : Fin L, #(badSet hn D hL X j) * 64 := hsum
    _ = 64 * ∑ X : HardInput β L, ∑ j : Fin L, #(badSet hn D hL X j) := by
        rw [mul_sum]
        refine sum_congr rfl fun X _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun j _ => mul_comm _ _
    _ ≤ 64 * ∑ X : HardInput β L, ∑ q : Fin (β ^ L),
          (hardQuery hn D hL q).probes (hardMem hn D X L) :=
        Nat.mul_le_mul_left _ (sum_le_sum fun X _ => sum_card_badSet_le hn D hL X)
    _ = _ := by
        refine congrArg (64 * ·) (sum_congr rfl fun X _ => sum_congr rfl fun q _ => ?_)
        rw [length_hardUpdates, runSeq_hardUpdates]
        rfl

/-- **Fredman–Saks lower bound, hard-instance form.** Under the hypotheses of
`card_mul_le_sum_probes`, for some input `X` of the hard instance and some query `q`, the query
after the hard update sequence of `X` makes at least `L / 64` probes. -/
theorem exists_le_mul_probes {β L : ℕ} (hn : L * β ^ L ≤ n) (hL : 0 < L)
    (D : IndexedScheme (Op n) Result S w) (hD : AnswersQueries D) (hβ : 4 ≤ β) {tu : ℕ}
    (htu : ∀ t i b, (D.step t (.update i b)).depth ≤ tu)
    (hH : (S * 2 ^ w + 1) ^ (8 * tu) ≤ 2 ^ β) :
    ∃ (X : HardInput β L) (q : Fin (β ^ L)),
      L ≤ 64 * (D.step (hardUpdates hn X).length (.query (hardQueryIdx hn hL q))).probes
        (D.runSeq (hardUpdates hn X)).2 := by
  have hle : ∑ _p : HardInput β L × Fin (β ^ L), L ≤
      ∑ p : HardInput β L × Fin (β ^ L), 64 *
        (D.step (hardUpdates hn p.1).length (.query (hardQueryIdx hn hL p.2))).probes
          (D.runSeq (hardUpdates hn p.1)).2 := by
    rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul, ← mul_sum,
      Fintype.sum_prod_type]
    exact card_mul_le_sum_probes hn hL D hD hβ htu hH
  have : Nonempty (Fin (β ^ L)) := ⟨⟨0, pow_pos (by omega) L⟩⟩
  obtain ⟨⟨X, q⟩, -, hXq⟩ := exists_le_of_sum_le univ_nonempty hle
  exact ⟨X, q, hXq⟩

/-- **Fredman–Saks lower bound, depth form.** Under the hypotheses of `exists_le_mul_probes`, if
every query has depth at most `tq` then `L ≤ 64 tq`. -/
theorem le_mul_of_answersQueries {β L : ℕ} (hn : L * β ^ L ≤ n)
    (D : IndexedScheme (Op n) Result S w) (hD : AnswersQueries D) (hβ : 4 ≤ β) {tu tq : ℕ}
    (htu : ∀ t i b, (D.step t (.update i b)).depth ≤ tu)
    (htq : ∀ t i, (D.step t (.query i)).depth ≤ tq)
    (hH : (S * 2 ^ w + 1) ^ (8 * tu) ≤ 2 ^ β) : L ≤ 64 * tq := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exact Nat.zero_le _
  obtain ⟨X, q, h⟩ := exists_le_mul_probes hn hL D hD hβ htu hH
  exact h.trans (Nat.mul_le_mul_left _ (((D.step _ _).probes_le_depth _).trans (htq _ _)))

/-- **Fredman–Saks lower bound** [FredmanSaks1989] for dynamic prefix parity, in the form
`t_q = Ω(log n / log (t_u (w + 1)))`: a deterministic step-indexed cell-probe scheme with
`S ≤ 2 ^ w` cells of `w` bits whose updates have depth at most `t_u` and whose queries have depth at
most `t_q` satisfies `log_β n ≤ 128 t_q + 1` for `β = max 4 (8 t_u (2 w + 1))`. -/
theorem log_le_of_answersQueries (D : IndexedScheme (Op n) Result S w) (hD : AnswersQueries D)
    (hS : S ≤ 2 ^ w) {tu tq : ℕ} (htu : ∀ t i b, (D.step t (.update i b)).depth ≤ tu)
    (htq : ∀ t i, (D.step t (.query i)).depth ≤ tq) :
    Nat.log (max 4 (8 * tu * (2 * w + 1))) n ≤ 128 * tq + 1 := by
  set β := max 4 (8 * tu * (2 * w + 1)) with hβdef
  have hβ : 4 ≤ β := le_max_left _ _
  set L := Nat.log β n / 2 with hLdef
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  have hpow : β ^ (2 * L) ≤ n :=
    (Nat.pow_le_pow_right (by omega) (by omega)).trans (Nat.pow_log_le_self β hn0.ne')
  have hn : L * β ^ L ≤ n := by
    refine le_trans ?_ hpow
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul_right _ (Nat.lt_pow_self (by omega)).le
  have hH : (S * 2 ^ w + 1) ^ (8 * tu) ≤ 2 ^ β := by
    have h1 : S * 2 ^ w + 1 ≤ 2 ^ (2 * w + 1) := by
      have : S * 2 ^ w ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_right _ hS
      rw [pow_succ, two_mul, pow_add]
      have : 1 ≤ 2 ^ w * 2 ^ w := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    calc (S * 2 ^ w + 1) ^ (8 * tu) ≤ (2 ^ (2 * w + 1)) ^ (8 * tu) := Nat.pow_le_pow_left h1 _
      _ = 2 ^ (8 * tu * (2 * w + 1)) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ β := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  have := le_mul_of_answersQueries hn D hD hβ htu htq hH
  omega

end Cslib.DataStructure.PrefixSums.CellProbe
