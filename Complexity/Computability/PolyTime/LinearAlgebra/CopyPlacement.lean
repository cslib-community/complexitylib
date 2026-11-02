/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.PolyTime.JetArray
public import Complexity.Foundations.Data.Polynomial.CoeffList
public import Complexity.Foundations.LinearAlgebra.VariableCopyPlacement
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial-time variable copy placement and replacement-row pullback

Given a bounded-occurrence incidence family with auxiliary block-label indices `u_e < D` and
variable indices `v_e < n`, Section 4.5 (p. 32) and Lemma 4.7 (pp. 33–34) of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] assign each incidence a copy
index `c_e < h` so that all pairs `(c_e, u_e)` are distinct, partition the variables into schedule
groups `S_{t,g}` at step `t`, and pull back the `{0, 1, -1}` block measurement rows and
cleared-denominator block replacement rows along `ι : K^n → K^{h × D}`. Parameterized over any
`blockMeas : List (List ℤ)` and `blockRepl : List (List (List ℤ))`, this module proves all
combinatorial, linear-algebraic, and `ℓ₁`-norm invariants and bridges to
`Complexity.Foundations.LinearAlgebra.VariableCopyPlacement`. Generic `copyEmbedExec` over
arbitrary `K` and `x : ℕ → K` serves as an unencoded semantic helper for the linear-map pullback
and refinement bridges (with no tape encoding or complexity certificate), while plain
`Turing.MultiTapeTM.ComputableInPolyTime` certificates cover the seven concrete integer/list
routines (`fiberRanks`, `flatPlacement`, `varGroupList`, `pullbackMeasurementRow`,
`pullbackMeasurementMatrix`, `restrictGroupColumns`, and `pullbackReplacementRow`).

## Main definitions

* `Cslib.LinearAlgebra.CopyPlacement.fiberRanks`, `Cslib.LinearAlgebra.CopyPlacement.flatPlacement`,
  `Cslib.LinearAlgebra.CopyPlacement.varGroupList`,
  `Cslib.LinearAlgebra.CopyPlacement.copyEmbedExec`,
  `Cslib.LinearAlgebra.CopyPlacement.pullbackMeasurementRow`,
  `Cslib.LinearAlgebra.CopyPlacement.pullbackMeasurementMatrix`,
  `Cslib.LinearAlgebra.CopyPlacement.restrictGroupColumns`,
  `Cslib.LinearAlgebra.CopyPlacement.pullbackReplacementRow`.

## Main results

* `Cslib.LinearAlgebra.CopyPlacement.nodup_zip_fiberRanks`,
  `Cslib.LinearAlgebra.CopyPlacement.lt_of_mem_fiberRanks`,
  `Cslib.LinearAlgebra.CopyPlacement.biUnion_toFinset_varGroupList`,
  `Cslib.LinearAlgebra.CopyPlacement.isTableShape_pullbackReplacementRow`,
  `Cslib.LinearAlgebra.CopyPlacement.zipWith_mul_sum_pullbackMeasurementRow`,
  `Cslib.LinearAlgebra.CopyPlacement.sum_evalCoeffList_pullbackReplacementRow`,
  `Cslib.LinearAlgebra.CopyPlacement.getD_zero_pullbackReplacementRow`,
  `Cslib.LinearAlgebra.CopyPlacement.abs_zipWith_mul_sum_pullbackMeasurementRow_le`,
  `Cslib.LinearAlgebra.CopyPlacement.jetL1Norm_pullbackReplacementRow_le`,
  `Cslib.LinearAlgebra.CopyPlacement.sum_evalCoeffList_pullbackReplacementRow_eq_zero_of_kernel`,
  `Cslib.LinearAlgebra.CopyPlacement.getElem_fiberRanks_eq_fiberRank`,
  `Cslib.LinearAlgebra.CopyPlacement.getD_pullbackMeasurementRow_ofFn_eq_varMeasurementMatrix`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.LinearAlgebra.CopyPlacement

open Turing.MultiTapeTM

/-! ### Deterministic copy-index assignment (`fiberRanks` and `flatPlacement`) -/

/-- Assign each incidence `e < labels.length` the number of earlier incidences `< e` carrying the
same auxiliary block label `labels[e]`, deterministically realizing `e ↦ (c_e, u_e)` from
Section 4.5 (p. 32) and Lemma 4.7 of [OpenAI2026ETH]. -/
def fiberRanks (labels : List ℕ) : List ℕ :=
  (List.range labels.length).map fun e => (labels.take e).count (labels.getD e 0)

/-- Flat slot index `c_e * D + u_e` pairing each copy index from `fiberRanks labels` with its
auxiliary block-label index `< D`. -/
def flatPlacement (D : ℕ) (labels : List ℕ) : List ℕ :=
  ((fiberRanks labels).zip labels).map fun p => p.1 * D + p.2

/-- `fiberRanks` preserves the number of incidences. -/
@[simp] theorem length_fiberRanks (labels : List ℕ) :
    (fiberRanks labels).length = labels.length := by simp [fiberRanks]

/-- Entry `e` of `fiberRanks labels` counts occurrences of `labels[e]` in `labels.take e`. -/
theorem getElem_fiberRanks (labels : List ℕ) {e : ℕ} (he : e < (fiberRanks labels).length) :
    (fiberRanks labels)[e] =
      (labels.take e).count (labels[e]'(by simpa only [length_fiberRanks] using he)) := by
  have he' : e < labels.length := by simpa only [length_fiberRanks] using he
  simp only [fiberRanks, List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ he']

/-- Defaulted lookup of `fiberRanks labels` at a valid incidence index `e`. -/
theorem getD_fiberRanks (labels : List ℕ) {e : ℕ} (he : e < labels.length) (d : ℕ) :
    (fiberRanks labels).getD e d = (labels.take e).count (labels.getD e 0) := by
  rw [fiberRanks, List.getD_map_range _ d he]

private theorem count_take_eq_card_fin (labels : List ℕ) :
    ∀ {k : ℕ} (_ : k ≤ labels.length) (y : ℕ),
      (labels.take k).count y =
        (Finset.univ.filter fun i : Fin labels.length => labels[i] = y ∧ i.1 < k).card
  | 0, _, _ => by simp
  | k + 1, hk, y => by
    have hk' : k < labels.length := Nat.lt_of_succ_le hk
    rw [List.take_succ_eq_append_getElem hk', List.count_append, List.count_singleton,
      count_take_eq_card_fin labels hk'.le y]
    by_cases hy : labels[k] = y
    · subst hy
      let f := fun m =>
        Finset.univ.filter fun i : Fin labels.length => labels[i] = labels[k] ∧ i.1 < m
      have hsplit : f (k + 1) = insert ⟨k, hk'⟩ (f k) := by
        ext ⟨i, hi⟩; simp only [f, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff]
        by_cases hik : i = k
        · subst hik; simp
        · exact ⟨fun ⟨h1, h2⟩ => Or.inr ⟨h1, by omega⟩,
            fun h => h.elim (fun h => absurd h hik) fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩
      change (f k).card + _ = (f (k + 1)).card
      rw [hsplit, Finset.card_insert_of_notMem (by simp [f])]; simp
    · rw [beq_false_of_ne hy]; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      congr 1; ext ⟨i, hi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.getElem_fin]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩,
        fun ⟨h1, h2⟩ => ⟨h1, by have : i ≠ k := fun h => hy (h ▸ h1); omega⟩⟩

/-- Entry `e` of `fiberRanks labels` agrees with `Cslib.LinearAlgebra.fiberRank` on
`Fin labels.length`. -/
theorem getElem_fiberRanks_eq_fiberRank (labels : List ℕ) (e : Fin labels.length) :
    (fiberRanks labels)[e.1]'(by simp [e.2]) =
      Cslib.LinearAlgebra.fiberRank (fun i : Fin labels.length => labels[i]) e := by
  rw [getElem_fiberRanks, count_take_eq_card_fin labels e.2.le, Cslib.LinearAlgebra.fiberRank]
  congr 1

/-- **Unconditional injectivity of `(fiberRanks labels).zip labels`.** Distinct incidence
positions always receive distinct `(copyIdx, blockLabel)` pairs. -/
theorem nodup_zip_fiberRanks (labels : List ℕ) : ((fiberRanks labels).zip labels).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]; intro e₁ e₂ he₁ he₂ hlt heq
  have hl₁ : e₁ < labels.length := by
    simpa only [List.length_zip, length_fiberRanks, min_self] using he₁
  have hl₂ : e₂ < labels.length := by
    simpa only [List.length_zip, length_fiberRanks, min_self] using he₂
  refine hlt.ne (congrArg Fin.val (Cslib.LinearAlgebra.injective_fiberRank_prod
    (fun i : Fin labels.length => labels[i]) (a₁ := ⟨e₁, hl₁⟩) (a₂ := ⟨e₂, hl₂⟩) ?_))
  simp only [List.getElem_zip] at heq
  rwa [getElem_fiberRanks_eq_fiberRank labels ⟨e₁, hl₁⟩,
    getElem_fiberRanks_eq_fiberRank labels ⟨e₂, hl₂⟩] at heq

/-- Distinct valid incidence indices receive distinct `(copyIdx, blockLabel)` pairs. -/
theorem fiberRanks_pair_ne_of_ne {labels : List ℕ} {e₁ e₂ : ℕ}
    (he₁ : e₁ < labels.length) (he₂ : e₂ < labels.length) (hne : e₁ ≠ e₂) :
    ((fiberRanks labels).getD e₁ 0, labels.getD e₁ 0) ≠
      ((fiberRanks labels).getD e₂ 0, labels.getD e₂ 0) := by
  have hz₁ : e₁ < ((fiberRanks labels).zip labels).length := by
    simpa only [List.length_zip, length_fiberRanks, Nat.min_self] using he₁
  have hz₂ : e₂ < ((fiberRanks labels).zip labels).length := by
    simpa only [List.length_zip, length_fiberRanks, Nat.min_self] using he₂
  have hf₁ : e₁ < (fiberRanks labels).length := by simpa only [length_fiberRanks] using he₁
  have hf₂ : e₂ < (fiberRanks labels).length := by simpa only [length_fiberRanks] using he₂
  refine fun heq =>
    hne (((nodup_zip_fiberRanks labels).getElem_inj_iff (hi := hz₁) (hj := hz₂)).mp ?_)
  simpa only [List.getElem_zip, List.getD_eq_getElem _ _ hf₁, List.getD_eq_getElem _ _ hf₂,
    List.getD_eq_getElem _ _ he₁, List.getD_eq_getElem _ _ he₂] using heq

/-- **Copy-multiplicity bound.** If every block label occurs at most `h` times in `labels`, then
every copy index produced by `fiberRanks labels` is strictly less than `h`. -/
theorem lt_of_mem_fiberRanks {labels : List ℕ} {h : ℕ} (hbound : ∀ y, labels.count y ≤ h)
    {c : ℕ} (hc : c ∈ fiberRanks labels) : c < h := by
  obtain ⟨e, he, rfl⟩ := List.mem_iff_getElem.mp hc
  have hl : e < labels.length := by simpa only [length_fiberRanks] using he
  rw [getElem_fiberRanks_eq_fiberRank labels ⟨e, hl⟩]
  refine (Cslib.LinearAlgebra.fiberRank_lt_card_fiber
    (fun i : Fin labels.length => labels[i]) ⟨e, hl⟩).trans_le ?_
  have hcnt := count_take_eq_card_fin labels le_rfl labels[e]; simp only [List.take_length] at hcnt
  have hcard : (Finset.univ.filter fun i : Fin labels.length => labels[i] = labels[e]).card =
      labels.count labels[e] := by rw [hcnt]; congr 1; ext i; simp
  exact hcard ▸ hbound labels[e]

/-- `flatPlacement` preserves the number of incidences. -/
@[simp] theorem length_flatPlacement (D : ℕ) (labels : List ℕ) :
    (flatPlacement D labels).length = labels.length := by simp [flatPlacement]

/-- When all labels in `labels` lie below `D`, `flatPlacement D labels` is duplicate-free. -/
theorem nodup_flatPlacement {D : ℕ} {labels : List ℕ} (hD : ∀ u ∈ labels, u < D) :
    (flatPlacement D labels).Nodup := by
  refine (nodup_zip_fiberRanks labels).map_on ?_
  rintro ⟨c₁, u₁⟩ hp₁ ⟨c₂, u₂⟩ hp₂ heq
  have hu₁ := hD u₁ (List.of_mem_zip hp₁).2; have hu₂ := hD u₂ (List.of_mem_zip hp₂).2
  have hmod := congrArg (· % D) heq
  simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hu₁, Nat.mod_eq_of_lt hu₂] at hmod
  subst hmod; exact Prod.ext
    (Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_of_lt hu₁) (Nat.add_right_cancel heq)) rfl

/-- When all labels lie below `D` and each occurs at most `h` times, flat slots lie below
`h * D`. -/
theorem lt_mul_of_mem_flatPlacement {D h : ℕ} {labels : List ℕ}
    (hD : ∀ u ∈ labels, u < D) (hbound : ∀ y, labels.count y ≤ h)
    {s : ℕ} (hs : s ∈ flatPlacement D labels) : s < h * D := by
  simp only [flatPlacement, List.mem_map] at hs; obtain ⟨⟨c, u⟩, hp, rfl⟩ := hs
  have hc : c + 1 ≤ h := lt_of_mem_fiberRanks hbound (List.of_mem_zip hp).1
  have hu : u < D := hD u (List.of_mem_zip hp).2; nlinarith

/-! ### Executable variable-group partition (`varGroupList`) -/

/-- Sorted list of variable indices `v < varSchedules.length` whose group index at evaluation step
`t` equals `g` (`S_{t,g} = {v ∈ [n] : a_v(t) = g}` in Section 4.5, p. 32 of [OpenAI2026ETH]).
Schedule lists shorter than `t + 1` default to group `0` via `List.getD`. -/
def varGroupList (varSchedules : List (List ℕ)) (t g : ℕ) : List ℕ :=
  (List.range varSchedules.length).filter fun v => decide ((varSchedules.getD v []).getD t 0 = g)

/-- Membership in `varGroupList varSchedules t g`. -/
@[simp] theorem mem_varGroupList {varSchedules : List (List ℕ)} {t g v : ℕ} :
    v ∈ varGroupList varSchedules t g ↔
      v < varSchedules.length ∧ (varSchedules.getD v []).getD t 0 = g := by simp [varGroupList]

/-- `varGroupList` is strictly increasing. -/
theorem pairwise_lt_varGroupList (varSchedules : List (List ℕ)) (t g : ℕ) :
    (varGroupList varSchedules t g).Pairwise (· < ·) := List.pairwise_lt_range.filter _

/-- `varGroupList` contains no duplicate variable indices. -/
theorem nodup_varGroupList (varSchedules : List (List ℕ)) (t g : ℕ) :
    (varGroupList varSchedules t g).Nodup :=
  (pairwise_lt_varGroupList varSchedules t g).imp ne_of_lt

/-- Distinct groups `g₁ ≠ g₂` at step `t` yield disjoint variable sets. -/
theorem disjoint_toFinset_varGroupList (varSchedules : List (List ℕ)) (t : ℕ) {g₁ g₂ : ℕ}
    (hne : g₁ ≠ g₂) :
    Disjoint (varGroupList varSchedules t g₁).toFinset
      (varGroupList varSchedules t g₂).toFinset := by
  rw [Finset.disjoint_left]; intro v hv₁ hv₂
  simp only [List.mem_toFinset, mem_varGroupList] at hv₁ hv₂; exact hne (hv₁.2.symm.trans hv₂.2)

/-- When every variable's schedule value at step `t` lies in `0, …, r - 1`, the groups
`varGroupList varSchedules t g` for `g < r` partition `Finset.range varSchedules.length`. -/
theorem biUnion_toFinset_varGroupList {varSchedules : List (List ℕ)} {t r : ℕ}
    (hsched : ∀ v < varSchedules.length, (varSchedules.getD v []).getD t 0 < r) :
    (Finset.range r).biUnion (fun g => (varGroupList varSchedules t g).toFinset) =
      Finset.range varSchedules.length := by
  ext v; simp only [Finset.mem_biUnion, Finset.mem_range, List.mem_toFinset, mem_varGroupList]
  exact ⟨fun ⟨_, _, hv, _⟩ => hv, fun hv => ⟨_, hsched v hv, hv, rfl⟩⟩

/-- Exact cardinality partition: the lengths of `varGroupList varSchedules t g` across `g < r` sum
to `varSchedules.length`. -/
theorem sum_length_varGroupList {varSchedules : List (List ℕ)} {t r : ℕ}
    (hsched : ∀ v < varSchedules.length, (varSchedules.getD v []).getD t 0 < r) :
    ∑ g ∈ Finset.range r, (varGroupList varSchedules t g).length = varSchedules.length := by
  have hcard : ∀ g ∈ Finset.range r,
      (varGroupList varSchedules t g).length = (varGroupList varSchedules t g).toFinset.card :=
    fun g _ => (List.toFinset_card_of_nodup (nodup_varGroupList varSchedules t g)).symm
  rw [Finset.sum_congr rfl hcard, ← Finset.card_biUnion
    (fun _ _ _ _ hne => disjoint_toFinset_varGroupList varSchedules t hne),
    biUnion_toFinset_varGroupList hsched, Finset.card_range]

/-- `varGroupList` agrees with `Cslib.LinearAlgebra.varGroup` whenever `varSchedules` encodes
`a : Fin n → Fin Q → Fin r`. -/
theorem mem_varGroupList_iff_mem_varGroup {n Q r : ℕ} {varSchedules : List (List ℕ)}
    {a : Fin n → Fin Q → Fin r} (hlen : varSchedules.length = n)
    (ha : ∀ (v : Fin n) (t : Fin Q), (varSchedules.getD v.1 []).getD t.1 0 = (a v t).1)
    (t : Fin Q) (g : Fin r) (v : Fin n) :
    v.1 ∈ varGroupList varSchedules t.1 g.1 ↔ v ∈ Cslib.LinearAlgebra.varGroup a t g := by
  simp only [mem_varGroupList, Cslib.LinearAlgebra.mem_varGroup, hlen, v.2, true_and, ha,
    Fin.ext_iff]

/-! ### Executable copy-embedding and pullback of measurement and replacement rows -/

/-- Executable copy-embedding coordinate `(ι x)_{copyIdx, y}` from Section 4.5 (p. 32) of
[OpenAI2026ETH], pairing `placements` with `incVars` via `List.zip` (truncating to
`min placements.length incVars.length`) and summing `x v` over records `((c_e, u_e), v_e)` with
`c_e = copyIdx` and `u_e = y`. -/
def copyEmbedExec {K : Type*} [AddCommMonoid K] (placements : List (ℕ × ℕ)) (incVars : List ℕ)
    (x : ℕ → K) (copyIdx y : ℕ) : K :=
  ((placements.zip incVars).map fun ((c, u), v) =>
    if c = copyIdx ∧ u = y then x v else 0).sum

/-- Pull back a single auxiliary measurement row `auxRow : List ℤ` in copy `copyIdx` to a length-`n`
integer row over the original variables (`(π_{copyIdx} ι)^⊤ auxRow`), pairing `placements` with
`incVars` via `List.zip` and defaulting out-of-range block indices `u_e ≥ auxRow.length` to `0`. -/
def pullbackMeasurementRow (n : ℕ) (placements : List (ℕ × ℕ)) (incVars : List ℕ)
    (copyIdx : ℕ) (auxRow : List ℤ) : List ℤ :=
  (List.range n).map fun v =>
    ((placements.zip incVars).map fun ((c, u), v') =>
      if c = copyIdx ∧ v' = v then auxRow.getD u 0 else 0).sum

/-- Pull back a block measurement matrix `blockMeas : List (List ℤ)` across `h` copies to form the
`(h * blockMeas.length) × n` integer matrix `Ĉ = C̃ ι` of equation `(4.15)` in [OpenAI2026ETH]. -/
def pullbackMeasurementMatrix (n h : ℕ) (placements : List (ℕ × ℕ)) (incVars : List ℕ)
    (blockMeas : List (List ℤ)) : List (List ℤ) :=
  (List.range h).flatMap fun copyIdx =>
    blockMeas.map fun auxRow => pullbackMeasurementRow n placements incVars copyIdx auxRow

/-- Restrict each row of an integer matrix `mat` to the columns indexed by `groupVars`, forming the
submatrix `C_{t,g} = Ĉ|_{S_{t,g}}` of equation `(4.15)` in [OpenAI2026ETH]; out-of-range column
indices `v ≥ row.length` default to `0`. -/
def restrictGroupColumns (groupVars : List ℕ) (mat : List (List ℤ)) : List (List ℤ) :=
  mat.map fun row => groupVars.map fun v => row.getD v 0

/-- Pull back the cleared-denominator replacement row of incidence `e` (`(c_e, u_e)` in
`placements`) from a `D × D × R` integer polynomial table `blockRepl` to an `n × R` table via
`Cslib.tabulateTable` computing `d_den • P⃗_{f,v}(T) = d_den • P⃗_{u_{f,v}}(T) π_{c(f,v)} ι`
(equation `(4.14)`, p. 32 and Lemmas 4.6–4.7, pp. 33–34 of [OpenAI2026ETH]). Pairs `placements`
with `incVars` via `List.zip`, defaulting missing `e`, `u_e`, or `(y, k)` lookups to `(0, 0)`,
`[]`, and `0` (`Cslib.rowEntry`). -/
def pullbackReplacementRow (n R : ℕ) (placements : List (ℕ × ℕ)) (incVars : List ℕ)
    (e : ℕ) (blockRepl : List (List (List ℤ))) : List (List ℤ) :=
  let pe := placements.getD e (0, 0)
  let uRow := blockRepl.getD pe.2 []
  Cslib.tabulateTable n R fun v k =>
    ((placements.zip incVars).map fun ((c, u), v') =>
      if c = pe.1 ∧ v' = v then Cslib.rowEntry uRow u k else 0).sum

/-! ### Dimensions, `IsTableShape` certificates, slices, and sum-over-zip helpers -/

/-- `pullbackMeasurementRow` produces a row of length `n`. -/
@[simp] theorem length_pullbackMeasurementRow (n : ℕ) (placements : List (ℕ × ℕ))
    (incVars : List ℕ) (copyIdx : ℕ) (auxRow : List ℤ) :
    (pullbackMeasurementRow n placements incVars copyIdx auxRow).length = n := by
  simp [pullbackMeasurementRow]

/-- `pullbackMeasurementMatrix` produces `h * blockMeas.length` rows. -/
@[simp] theorem length_pullbackMeasurementMatrix (n h : ℕ) (placements : List (ℕ × ℕ))
    (incVars : List ℕ) (blockMeas : List (List ℤ)) :
    (pullbackMeasurementMatrix n h placements incVars blockMeas).length = h * blockMeas.length := by
  induction h with
  | zero => simp [pullbackMeasurementMatrix]
  | succ h ih =>
    simp only [pullbackMeasurementMatrix, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.length_append, List.length_map] at ih ⊢
    rw [ih]; ring

/-- Every row of `pullbackMeasurementMatrix` has length `n`. -/
theorem length_row_of_mem_pullbackMeasurementMatrix {n h : ℕ} {placements : List (ℕ × ℕ)}
    {incVars : List ℕ} {blockMeas : List (List ℤ)} {row : List ℤ}
    (hrow : row ∈ pullbackMeasurementMatrix n h placements incVars blockMeas) : row.length = n := by
  simp only [pullbackMeasurementMatrix, List.mem_flatMap, List.mem_range, List.mem_map] at hrow
  obtain ⟨_, _, _, _, rfl⟩ := hrow; exact length_pullbackMeasurementRow _ _ _ _ _

/-- `pullbackMeasurementMatrix` has rectangular table shape `(h * blockMeas.length) × n`. -/
theorem isTableShape_pullbackMeasurementMatrix (n h : ℕ) (placements : List (ℕ × ℕ))
    (incVars : List ℕ) (blockMeas : List (List ℤ)) :
    Cslib.IsTableShape (h * blockMeas.length) n
      (pullbackMeasurementMatrix n h placements incVars blockMeas) :=
  ⟨length_pullbackMeasurementMatrix .., fun _ => length_row_of_mem_pullbackMeasurementMatrix⟩

/-- `restrictGroupColumns` preserves the number of rows. -/
@[simp] theorem length_restrictGroupColumns (groupVars : List ℕ) (mat : List (List ℤ)) :
    (restrictGroupColumns groupVars mat).length = mat.length := by simp [restrictGroupColumns]

/-- Every row of `restrictGroupColumns groupVars mat` has length `groupVars.length`. -/
theorem length_row_of_mem_restrictGroupColumns {groupVars : List ℕ} {mat : List (List ℤ)}
    {row : List ℤ} (hrow : row ∈ restrictGroupColumns groupVars mat) :
    row.length = groupVars.length := by
  simp only [restrictGroupColumns, List.mem_map] at hrow; obtain ⟨_, _, rfl⟩ := hrow; simp

/-- `restrictGroupColumns groupVars mat` has rectangular table shape
`mat.length × groupVars.length`. -/
theorem isTableShape_restrictGroupColumns (groupVars : List ℕ) (mat : List (List ℤ)) :
    Cslib.IsTableShape mat.length groupVars.length (restrictGroupColumns groupVars mat) :=
  ⟨length_restrictGroupColumns .., fun _ => length_row_of_mem_restrictGroupColumns⟩

/-- `pullbackReplacementRow` produces `n` polynomial entries. -/
@[simp] theorem length_pullbackReplacementRow (n R : ℕ) (placements : List (ℕ × ℕ))
    (incVars : List ℕ) (e : ℕ) (blockRepl : List (List (List ℤ))) :
    (pullbackReplacementRow n R placements incVars e blockRepl).length = n :=
  Cslib.length_tabulateTable n R _

/-- Every polynomial entry in `pullbackReplacementRow` has length `R`. -/
theorem length_coeff_of_mem_pullbackReplacementRow {n R : ℕ} {placements : List (ℕ × ℕ)}
    {incVars : List ℕ} {e : ℕ} {blockRepl : List (List (List ℤ))} {poly : List ℤ}
    (hpoly : poly ∈ pullbackReplacementRow n R placements incVars e blockRepl) : poly.length = R :=
  Cslib.length_of_mem_tabulateTable hpoly

/-- `pullbackReplacementRow` has rectangular table shape `n × R`. -/
theorem isTableShape_pullbackReplacementRow (n R : ℕ) (placements : List (ℕ × ℕ))
    (incVars : List ℕ) (e : ℕ) (blockRepl : List (List (List ℤ))) :
    Cslib.IsTableShape n R (pullbackReplacementRow n R placements incVars e blockRepl) :=
  Cslib.isTableShape_tabulateTable n R _

private theorem getD_mem_of_lt {α : Type*} (d : α) {l : List α} {i : ℕ} (hi : i < l.length) :
    l.getD i d ∈ l := by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

/-- Extracting degree-`k` coefficients (`k < R`) across `pullbackReplacementRow` coincides with
`pullbackMeasurementRow` applied to the degree-`k` coefficient slice of `blockRepl[u_e]`. -/
theorem map_coeff_pullbackReplacementRow (n R : ℕ) (placements : List (ℕ × ℕ)) (incVars : List ℕ)
    (e : ℕ) (blockRepl : List (List (List ℤ))) {k : ℕ} (hk : k < R) :
    (pullbackReplacementRow n R placements incVars e blockRepl).map (fun poly => poly.getD k 0) =
      pullbackMeasurementRow n placements incVars (placements.getD e (0, 0)).1
        ((blockRepl.getD (placements.getD e (0, 0)).2 []).map fun poly => poly.getD k 0) := by
  simp only [pullbackReplacementRow, Cslib.tabulateTable, pullbackMeasurementRow, List.map_map,
    Function.comp_def]
  refine List.map_congr_left fun v _ => ?_
  rw [List.getD_map_range _ 0 hk]; refine congrArg List.sum (List.map_congr_left fun _ _ => ?_)
  rw [Cslib.rowEntry, ← List.getD_map _ ([] : List ℤ) (fun poly : List ℤ => poly.getD k 0)]; rfl

private theorem sum_map_zip {M : Type*} [AddCommMonoid M] {α β : Type*} (da : α) (db : β)
    (la : List α) (lb : List β) (f : α × β → M) :
    ((la.zip lb).map f).sum =
      ∑ e ∈ Finset.range (min la.length lb.length), f (la.getD e da, lb.getD e db) := by
  have hzip : la.zip lb =
      (List.range (min la.length lb.length)).map fun e => (la.getD e da, lb.getD e db) := by
    refine List.ext_getElem (by simp) fun e he _ => ?_
    have ha : e < la.length := (Nat.lt_min.mp (by simpa only [List.length_zip] using he)).1
    have hb : e < lb.length := (Nat.lt_min.mp (by simpa only [List.length_zip] using he)).2
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb]
  rw [hzip, List.map_map, Function.comp_def, List.sum_map_range,
    Fin.sum_univ_eq_sum_range (fun e => f (la.getD e da, lb.getD e db)) _]

private theorem sum_zipWith_mul (u w : List ℤ) :
    (List.zipWith (· * ·) u w).sum =
      ∑ i ∈ Finset.range (min u.length w.length), u.getD i 0 * w.getD i 0 := by
  have hzw : List.zipWith (· * ·) u w =
      (List.range (min u.length w.length)).map fun i => u.getD i 0 * w.getD i 0 := by
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    have hu : i < u.length := (Nat.lt_min.mp (by simpa only [List.length_zipWith] using hi)).1
    have hw : i < w.length := (Nat.lt_min.mp (by simpa only [List.length_zipWith] using hi)).2
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem _ _ hu, List.getD_eq_getElem _ _ hw]
  rw [hzw, List.sum_map_range, Fin.sum_univ_eq_sum_range (fun i => u.getD i 0 * w.getD i 0) _]

private theorem sum_range_groupVars_eq_toFinset {M : Type*} [AddCommMonoid M]
    {groupVars : List ℕ} (hnodup : groupVars.Nodup) (g : ℕ → M) :
    (∑ j ∈ Finset.range groupVars.length, g (groupVars.getD j 0)) =
      ∑ v ∈ groupVars.toFinset, g v := by
  refine Finset.sum_bij (fun j _ => groupVars.getD j 0)
    (fun j hj => List.mem_toFinset.mpr (getD_mem_of_lt 0 (Finset.mem_range.mp hj))) ?_ ?_
    fun _ _ => rfl
  · intro j₁ hj₁ j₂ hj₂ heq
    have h₁ := Finset.mem_range.mp hj₁; have h₂ := Finset.mem_range.mp hj₂
    rw [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂] at heq
    exact (hnodup.getElem_inj_iff (hi := h₁) (hj := h₂)).mp heq
  · intro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hv)
    exact ⟨j, Finset.mem_range.mpr hj, List.getD_eq_getElem _ _ hj⟩

/-- When `placements.Nodup`, the copy-embedding at an occupied slot `placements[e]` equals
`x (incVars[e])`, matching the piecewise definition on p. 32 of [OpenAI2026ETH]. -/
theorem copyEmbedExec_eq_of_nodup {K : Type*} [AddCommMonoid K] {placements : List (ℕ × ℕ)}
    {incVars : List ℕ} (hnodup : placements.Nodup) (x : ℕ → K) {e : ℕ}
    (he : e < min placements.length incVars.length) :
    copyEmbedExec placements incVars x
        (placements.getD e (0, 0)).1 (placements.getD e (0, 0)).2 = x (incVars.getD e 0) := by
  rw [copyEmbedExec, sum_map_zip (0, 0) 0, Finset.sum_eq_single e]
  · simp
  · intro i hi hne
    have hi_pl := (Nat.lt_min.mp (Finset.mem_range.mp hi)).1; have he_pl := (Nat.lt_min.mp he).1
    refine ite_eq_right fun ⟨h1, h2⟩ => hne ?_
    have heq : placements.getD i (0, 0) = placements.getD e (0, 0) := Prod.ext h1 h2
    rw [List.getD_eq_getElem _ _ hi_pl, List.getD_eq_getElem _ _ he_pl] at heq
    exact (hnodup.getElem_inj_iff (hi := hi_pl) (hj := he_pl)).mp heq
  · exact fun hmem => absurd (Finset.mem_range.mpr he) hmem

/-- At any unoccupied slot `(copyIdx, y) ∉ placements`, `copyEmbedExec` vanishes. -/
theorem copyEmbedExec_eq_zero_of_forall_ne {K : Type*} [AddCommMonoid K]
    {placements : List (ℕ × ℕ)} {incVars : List ℕ} (x : ℕ → K) {copyIdx y : ℕ}
    (hunocc : ∀ p ∈ placements, p ≠ (copyIdx, y)) :
    copyEmbedExec placements incVars x copyIdx y = 0 := by
  rw [copyEmbedExec, sum_map_zip (0, 0) 0]
  refine Finset.sum_eq_zero fun e he => ite_eq_right fun ⟨h1, h2⟩ => ?_
  exact hunocc _ (getD_mem_of_lt (0, 0) (Nat.lt_min.mp (Finset.mem_range.mp he)).1) (Prod.ext h1 h2)

/-! ### Exact linear-map pullback semantics -/

/-- **Linear-map pullback semantics over any commutative ring.** When all incidence variables lie
below `n` (`∀ v ∈ incVars, v < n`) and all placed block labels lie below `D`
(`∀ p ∈ placements, p.2 < D`), evaluating `pullbackMeasurementRow` against `x : ℕ → K` on
`0, …, n - 1` equals evaluating `auxRow` against `copyEmbedExec placements incVars x copyIdx` on
`0, …, D - 1`. -/
theorem sum_pullbackMeasurementRow_mul {K : Type*} [CommRing K]
    {n D : ℕ} {placements : List (ℕ × ℕ)} {incVars : List ℕ}
    (hvars : ∀ v ∈ incVars, v < n) (hD : ∀ p ∈ placements, p.2 < D)
    (copyIdx : ℕ) (auxRow : List ℤ) (x : ℕ → K) :
    (∑ v ∈ Finset.range n,
      ((pullbackMeasurementRow n placements incVars copyIdx auxRow).getD v 0 : K) * x v) =
      ∑ y ∈ Finset.range D,
        (auxRow.getD y 0 : K) * copyEmbedExec placements incVars x copyIdx y := by
  set m := min placements.length incVars.length
  have hlhs : (∑ v ∈ Finset.range n,
        ((pullbackMeasurementRow n placements incVars copyIdx auxRow).getD v 0 : K) * x v) =
      ∑ e ∈ Finset.range m, if (placements.getD e (0, 0)).1 = copyIdx then
        (auxRow.getD (placements.getD e (0, 0)).2 0 : K) * x (incVars.getD e 0) else 0 := by
    have hterm (v : ℕ) (hv : v ∈ Finset.range n) :
        ((pullbackMeasurementRow n placements incVars copyIdx auxRow).getD v 0 : K) * x v =
          ∑ e ∈ Finset.range m, if (placements.getD e (0, 0)).1 = copyIdx ∧ incVars.getD e 0 = v
            then (auxRow.getD (placements.getD e (0, 0)).2 0 : K) * x v else 0 := by
      rw [pullbackMeasurementRow, List.getD_map_range _ 0 (Finset.mem_range.mp hv),
        Int.cast_list_sum, List.map_map, Function.comp_def, sum_map_zip (0, 0) 0, Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by dsimp only; split_ifs <;> simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]; refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.sum_eq_single (incVars.getD e 0)
      (fun _ _ hne => ite_eq_right fun ⟨_, hv_eq⟩ => hne hv_eq.symm)
      (fun hnot => absurd (Finset.mem_range.mpr
        (hvars _ (getD_mem_of_lt 0 (Nat.lt_min.mp (Finset.mem_range.mp he)).2))) hnot)]; simp
  have hrhs : (∑ y ∈ Finset.range D,
        (auxRow.getD y 0 : K) * copyEmbedExec placements incVars x copyIdx y) =
      ∑ e ∈ Finset.range m, if (placements.getD e (0, 0)).1 = copyIdx then
        (auxRow.getD (placements.getD e (0, 0)).2 0 : K) * x (incVars.getD e 0) else 0 := by
    have hterm (y : ℕ) (_ : y ∈ Finset.range D) :
        (auxRow.getD y 0 : K) * copyEmbedExec placements incVars x copyIdx y =
          ∑ e ∈ Finset.range m, if (placements.getD e (0, 0)).1 = copyIdx ∧
            (placements.getD e (0, 0)).2 = y then
            (auxRow.getD y 0 : K) * x (incVars.getD e 0) else 0 := by
      rw [copyEmbedExec, sum_map_zip (0, 0) 0, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by dsimp only; split_ifs <;> simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm]; refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.sum_eq_single (placements.getD e (0, 0)).2
      (fun _ _ hne => ite_eq_right fun ⟨_, hy_eq⟩ => hne hy_eq.symm)
      (fun hnot => absurd (Finset.mem_range.mpr
        (hD _ (getD_mem_of_lt (0, 0) (Nat.lt_min.mp (Finset.mem_range.mp he)).1))) hnot)]; simp
  exact hlhs.trans hrhs.symm

private theorem zipWith_mul_sum_map_range {row : List ℤ} {k : ℕ} (hlen : row.length ≤ k)
    (x : ℕ → ℤ) :
    (List.zipWith (· * ·) row ((List.range k).map x)).sum =
      ∑ i ∈ Finset.range row.length, row.getD i 0 * x i := by
  have hmin : min row.length ((List.range k).map x).length = row.length := by
    simp only [List.length_map, List.length_range]; exact Nat.min_eq_left hlen
  rw [sum_zipWith_mul, hmin]
  exact Finset.sum_congr rfl fun i hi => by
    rw [List.getD_map_range _ 0 ((Finset.mem_range.mp hi).trans_le hlen)]

/-- **Integer dot-product pullback semantics.** When `∀ v ∈ incVars, v < n` and
`∀ p ∈ placements, p.2 < D`, for any `x : ℕ → ℤ`, the dot product of `pullbackMeasurementRow` with
`(List.range n).map x` equals the dot product of `auxRow` with
`(List.range D).map (copyEmbedExec placements incVars x copyIdx)`. -/
theorem zipWith_mul_sum_pullbackMeasurementRow {n D : ℕ} {placements : List (ℕ × ℕ)}
    {incVars : List ℕ} (hvars : ∀ v ∈ incVars, v < n) (hD : ∀ p ∈ placements, p.2 < D)
    (copyIdx : ℕ) (auxRow : List ℤ) (x : ℕ → ℤ) :
    (List.zipWith (· * ·) (pullbackMeasurementRow n placements incVars copyIdx auxRow)
        ((List.range n).map x)).sum =
      (List.zipWith (· * ·) auxRow
        ((List.range D).map (copyEmbedExec placements incVars x copyIdx))).sum := by
  rw [zipWith_mul_sum_map_range (by simp), length_pullbackMeasurementRow]
  have hlhs := sum_pullbackMeasurementRow_mul (K := ℤ) hvars hD copyIdx auxRow x
  simp only [Int.cast_id] at hlhs
  rw [hlhs, sum_zipWith_mul, List.length_map, List.length_range]
  have hcongr : (∑ y ∈ Finset.range (min auxRow.length D),
        auxRow.getD y 0 *
          ((List.range D).map (copyEmbedExec placements incVars x copyIdx)).getD y 0) =
      ∑ y ∈ Finset.range (min auxRow.length D),
        auxRow.getD y 0 * copyEmbedExec placements incVars x copyIdx y :=
    Finset.sum_congr rfl fun y hy => by
      rw [List.getD_map_range _ 0 (Nat.lt_min.mp (Finset.mem_range.mp hy)).2]
  rw [hcongr]
  rcases le_total auxRow.length D with hle | hge
  · rw [Nat.min_eq_left hle]; symm
    refine Finset.sum_subset (Finset.range_mono hle) fun y _ hy_not => ?_
    rw [List.getD_eq_default _ _ (not_lt.mp (mt Finset.mem_range.mpr hy_not)), zero_mul]
  · rw [Nat.min_eq_right hge]

private theorem evalCoeffList_map_intCast_eq_sum_range {K : Type*} [CommRing K]
    (t : K) (coeffs : List ℤ) {R : ℕ} (hlen : coeffs.length ≤ R) :
    Polynomial.evalCoeffList t (coeffs.map Int.cast) =
      ∑ k ∈ Finset.range R, (coeffs.getD k 0 : K) * t ^ k := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)]
  · have hdeg : (Polynomial.ofCoeffList (coeffs.map (Int.cast : ℤ → K))).natDegree < R := by
      have h := Polynomial.natDegree_ofCoeffList_le (coeffs.map (Int.cast : ℤ → K))
      rw [List.length_map] at h; omega
    rw [← Polynomial.eval_ofCoeffList, Polynomial.eval_eq_sum_range' hdeg]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.coeff_ofCoeffList, ← Int.cast_zero, List.getD_map coeffs 0 Int.cast]

/-- **Replacement-row polynomial pullback semantics.** When `∀ v ∈ incVars, v < n`,
`∀ p ∈ placements, p.2 < D`, and every polynomial coefficient list in row `u_e` of `blockRepl` has
length `≤ R`, evaluating `pullbackReplacementRow` at `t` via `Polynomial.evalCoeffList` against
`x : ℕ → K` equals evaluating row `u_e` of `blockRepl` at `t` against
`copyEmbedExec placements incVars x c_e`. -/
theorem sum_evalCoeffList_pullbackReplacementRow {K : Type*} [CommRing K]
    {n R D : ℕ} {placements : List (ℕ × ℕ)} {incVars : List ℕ} {e : ℕ}
    {blockRepl : List (List (List ℤ))}
    (hvars : ∀ v ∈ incVars, v < n) (hD : ∀ p ∈ placements, p.2 < D)
    (hdeg : ∀ poly ∈ blockRepl.getD (placements.getD e (0, 0)).2 [], poly.length ≤ R)
    (t : K) (x : ℕ → K) :
    (∑ v ∈ Finset.range n,
      Polynomial.evalCoeffList t
        (((pullbackReplacementRow n R placements incVars e blockRepl).getD v []).map Int.cast) *
        x v) =
      ∑ y ∈ Finset.range D,
        Polynomial.evalCoeffList t
          (((blockRepl.getD (placements.getD e (0, 0)).2 []).getD y []).map Int.cast) *
          copyEmbedExec placements incVars x (placements.getD e (0, 0)).1 y := by
  set row := pullbackReplacementRow n R placements incVars e blockRepl
  set pe := placements.getD e (0, 0); set uRow := blockRepl.getD pe.2 []
  have hslice (l : List (List ℤ)) (i k : ℕ) :
      (l.map fun poly => poly.getD k 0).getD i 0 = (l.getD i []).getD k 0 :=
    List.getD_map l ([] : List ℤ) (fun poly : List ℤ => poly.getD k 0)
  have hlhs : (∑ v ∈ Finset.range n,
        Polynomial.evalCoeffList t ((row.getD v []).map Int.cast) * x v) =
      ∑ k ∈ Finset.range R, t ^ k *
        ∑ v ∈ Finset.range n, (((row.map fun poly => poly.getD k 0).getD v 0 : ℤ) : K) * x v := by
    have hv_eq (v : ℕ) (hv : v ∈ Finset.range n) :
        Polynomial.evalCoeffList t ((row.getD v []).map Int.cast) * x v =
          ∑ k ∈ Finset.range R, ((row.getD v []).getD k 0 : K) * t ^ k * x v := by
      have hv_lt : v < row.length := by
        simpa only [row, length_pullbackReplacementRow] using Finset.mem_range.mp hv
      rw [evalCoeffList_map_intCast_eq_sum_range t _
        (length_coeff_of_mem_pullbackReplacementRow (getD_mem_of_lt [] hv_lt)).le, Finset.sum_mul]
    rw [Finset.sum_congr rfl hv_eq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => ?_
    rw [hslice row v k]; ring
  have hk_step (k : ℕ) (hk : k ∈ Finset.range R) :
      t ^ k * (∑ v ∈ Finset.range n,
          (((row.map fun poly => poly.getD k 0).getD v 0 : ℤ) : K) * x v) =
        ∑ y ∈ Finset.range D,
          ((uRow.getD y []).getD k 0 : K) * t ^ k * copyEmbedExec placements incVars x pe.1 y := by
    dsimp only [row]
    rw [map_coeff_pullbackReplacementRow n R placements incVars e blockRepl
      (Finset.mem_range.mp hk), sum_pullbackMeasurementRow_mul hvars hD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hslice _ y k]; ring
  rw [hlhs, Finset.sum_congr rfl hk_step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hlen_y : (uRow.getD y []).length ≤ R :=
    (List.getD_mem_or uRow y []).elim (hdeg _) fun hnil => by rw [hnil]; simp
  rw [evalCoeffList_map_intCast_eq_sum_range t _ hlen_y, Finset.sum_mul]

/-! ### Exact `T = 0` variable-restoration theorem -/

/-- **Constant-term (`T = 0`) variable restoration.** When `0 < R`, `placements.Nodup`,
`e < min placements.length incVars.length`, and row `u_e` of `blockRepl` has constant coefficient
(`Cslib.rowEntry _ p.2 0`) equal to `d_den • δ_{u_e, p.2}` at every placed label `p ∈ placements`,
the constant coefficient `Cslib.rowEntry (pullbackReplacementRow ...) v 0` at variable `v < n`
equals `d_den • δ_{v, incVars[e]}`. -/
theorem getD_zero_pullbackReplacementRow {n R : ℕ} {placements : List (ℕ × ℕ)} {incVars : List ℕ}
    {e : ℕ} {blockRepl : List (List (List ℤ))} {d_den : ℤ}
    (hR : 0 < R) (hnodup : placements.Nodup) (he : e < min placements.length incVars.length)
    (hzero : ∀ p ∈ placements,
      Cslib.rowEntry (blockRepl.getD (placements.getD e (0, 0)).2 []) p.2 0 =
        if (placements.getD e (0, 0)).2 = p.2 then d_den else 0)
    {v : ℕ} (hv : v < n) :
    Cslib.rowEntry (pullbackReplacementRow n R placements incVars e blockRepl) v 0 =
      if v = incVars.getD e 0 then d_den else 0 := by
  rw [pullbackReplacementRow, Cslib.rowEntry_tabulateTable_of_lt _ hv hR, sum_map_zip (0, 0) 0,
    Finset.sum_eq_single e]
  · dsimp only; rw [hzero _ (getD_mem_of_lt (0, 0) (Nat.lt_min.mp he).1)]
    by_cases hv_eq : v = incVars.getD e 0
    · subst hv_eq; simp
    · rw [ite_eq_right (fun h => hv_eq h.2.symm), ite_eq_right hv_eq]
  · intro i hi hne
    have hi_pl := (Nat.lt_min.mp (Finset.mem_range.mp hi)).1; have he_pl := (Nat.lt_min.mp he).1
    dsimp only; rw [hzero _ (getD_mem_of_lt (0, 0) hi_pl)]
    split_ifs with hc hu
    · have heq_p : placements.getD i (0, 0) = placements.getD e (0, 0) := Prod.ext hc.1 hu.symm
      rw [List.getD_eq_getElem _ _ hi_pl, List.getD_eq_getElem _ _ he_pl] at heq_p
      exact absurd ((hnodup.getElem_inj_iff (hi := hi_pl) (hj := he_pl)).mp heq_p) hne
    all_goals rfl
  · exact fun hnot => absurd (Finset.mem_range.mpr he) hnot

/-- When `0 < R`, `placements.Nodup`, `e < min placements.length incVars.length`,
`∀ v ∈ incVars, v < n`, and `hzero` holds on `placements`, evaluating `pullbackReplacementRow` at
`T = 0` restores `(d_den : K) * x (incVars.getD e 0)`. -/
theorem sum_evalCoeffList_pullbackReplacementRow_zero {K : Type*} [CommRing K]
    {n R : ℕ} {placements : List (ℕ × ℕ)} {incVars : List ℕ} {e : ℕ}
    {blockRepl : List (List (List ℤ))} {d_den : ℤ}
    (hR : 0 < R) (hnodup : placements.Nodup) (he : e < min placements.length incVars.length)
    (hvars : ∀ v ∈ incVars, v < n)
    (hzero : ∀ p ∈ placements,
      Cslib.rowEntry (blockRepl.getD (placements.getD e (0, 0)).2 []) p.2 0 =
        if (placements.getD e (0, 0)).2 = p.2 then d_den else 0)
    (x : ℕ → K) :
    (∑ v ∈ Finset.range n,
      Polynomial.evalCoeffList (0 : K)
        (((pullbackReplacementRow n R placements incVars e blockRepl).getD v []).map Int.cast) *
        x v) = (d_den : K) * x (incVars.getD e 0) := by
  set row := pullbackReplacementRow n R placements incVars e blockRepl
  have hve_lt : incVars.getD e 0 < n := hvars _ (getD_mem_of_lt 0 (Nat.lt_min.mp he).2)
  have hv_zero (v : ℕ) (hv : v ∈ Finset.range n) :
      Polynomial.evalCoeffList (0 : K) ((row.getD v []).map Int.cast) * x v =
        (if v = incVars.getD e 0 then (d_den : K) else 0) * x v := by
    have hv_lt : v < row.length := by
      simpa only [row, length_pullbackReplacementRow] using Finset.mem_range.mp hv
    rw [evalCoeffList_map_intCast_eq_sum_range (0 : K) _
      (length_coeff_of_mem_pullbackReplacementRow (getD_mem_of_lt [] hv_lt)).le,
      Finset.sum_eq_single 0
        (fun k _ hk => by rw [zero_pow hk, mul_zero])
        (fun hnot => absurd (Finset.mem_range.mpr hR) hnot)]
    simp only [pow_zero, mul_one]; change (Cslib.rowEntry row v 0 : K) * x v = _
    rw [getD_zero_pullbackReplacementRow hR hnodup he hzero (Finset.mem_range.mp hv)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hv_zero, Finset.sum_eq_single (incVars.getD e 0)
    (fun _ _ hne => by rw [ite_eq_right hne, zero_mul])
    (fun hnot => absurd (Finset.mem_range.mpr hve_lt) hnot), ite_eq_left rfl]

/-! ### Row `ℓ₁`-norm preservation and Boolean evaluation bounds -/

/-- **Row `ℓ₁`-norm preservation (`§4.5`, eq. `(4.15)` and Lemma 4.6).** When `placements.Nodup`
and every placed block label lies below `D`, pulling back `auxRow` does not increase its `ℓ₁`-norm:
`∑_{v < n} |row[v]| ≤ ∑_{y < D} |auxRow[y]|`. -/
theorem sum_abs_pullbackMeasurementRow_le {n D : ℕ} {placements : List (ℕ × ℕ)}
    {incVars : List ℕ} (hnodup : placements.Nodup) (hD : ∀ p ∈ placements, p.2 < D)
    (copyIdx : ℕ) (auxRow : List ℤ) :
    (∑ v ∈ Finset.range n,
      |(pullbackMeasurementRow n placements incVars copyIdx auxRow).getD v 0|) ≤
      ∑ y ∈ Finset.range D, |auxRow.getD y 0| := by
  set m := min placements.length incVars.length
  have hstep1 : (∑ v ∈ Finset.range n,
        |(pullbackMeasurementRow n placements incVars copyIdx auxRow).getD v 0|) ≤
      ∑ e ∈ Finset.range m, if (placements.getD e (0, 0)).1 = copyIdx then
        |auxRow.getD (placements.getD e (0, 0)).2 0| else 0 := by
    have hv_le (v : ℕ) (hv : v ∈ Finset.range n) :
        |(pullbackMeasurementRow n placements incVars copyIdx auxRow).getD v 0| ≤
          ∑ e ∈ Finset.range m, if (placements.getD e (0, 0)).1 = copyIdx ∧ incVars.getD e 0 = v
            then |auxRow.getD (placements.getD e (0, 0)).2 0| else 0 := by
      rw [pullbackMeasurementRow, List.getD_map_range _ 0 (Finset.mem_range.mp hv),
        sum_map_zip (0, 0) 0]
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (le_of_eq (Finset.sum_congr rfl fun _ _ => by dsimp only; split_ifs <;> simp))
    refine (Finset.sum_le_sum hv_le).trans ?_; rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun e _ => ?_
    rcases lt_or_ge (incVars.getD e 0) n with hv_lt | hv_ge
    · rw [Finset.sum_eq_single (incVars.getD e 0)
        (fun _ _ hne => ite_eq_right fun ⟨_, heq⟩ => hne heq.symm)
        (fun hnot => absurd (Finset.mem_range.mpr hv_lt) hnot)]; simp
    · rw [Finset.sum_eq_zero fun v hv => ite_eq_right fun ⟨_, heq⟩ =>
        absurd (heq.trans_lt (Finset.mem_range.mp hv)) (not_lt.mpr hv_ge)]
      split_ifs <;> [exact abs_nonneg _; exact le_rfl]
  refine hstep1.trans ?_
  have hexpand (e : ℕ) (he : e ∈ Finset.range m) :
      (if (placements.getD e (0, 0)).1 = copyIdx then
          |auxRow.getD (placements.getD e (0, 0)).2 0| else 0) =
        ∑ y ∈ Finset.range D,
          if (placements.getD e (0, 0)).1 = copyIdx ∧ (placements.getD e (0, 0)).2 = y then
            |auxRow.getD y 0| else 0 := by
    have hy_lt := hD _ (getD_mem_of_lt (0, 0) (Nat.lt_min.mp (Finset.mem_range.mp he)).1)
    symm; rw [Finset.sum_eq_single (placements.getD e (0, 0)).2
      (fun _ _ hne => ite_eq_right fun ⟨_, hy_eq⟩ => hne hy_eq.symm)
      (fun hnot => absurd (Finset.mem_range.mpr hy_lt) hnot)]; simp
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]; refine Finset.sum_le_sum fun y _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.range m).filter fun e =>
      (placements.getD e (0, 0)).1 = copyIdx ∧ (placements.getD e (0, 0)).2 = y).card ≤ 1 := by
    rw [Finset.card_le_one]; intro e₁ he₁ e₂ he₂
    simp only [Finset.mem_filter, Finset.mem_range] at he₁ he₂
    have hp₁ := (Nat.lt_min.mp he₁.1).1; have hp₂ := (Nat.lt_min.mp he₂.1).1
    have heq : placements.getD e₁ (0, 0) = placements.getD e₂ (0, 0) :=
      Prod.ext (he₁.2.1.trans he₂.2.1.symm) (he₁.2.2.trans he₂.2.2.symm)
    rw [List.getD_eq_getElem _ _ hp₁, List.getD_eq_getElem _ _ hp₂] at heq
    exact (hnodup.getElem_inj_iff (hi := hp₁) (hj := hp₂)).mp heq
  have hcard_z : ((((Finset.range m).filter fun e => (placements.getD e (0, 0)).1 = copyIdx ∧
      (placements.getD e (0, 0)).2 = y).card : ℕ) : ℤ) ≤ 1 := by exact_mod_cast hcard
  have hnn : (0 : ℤ) ≤ |auxRow.getD y 0| := abs_nonneg _; nlinarith

private theorem sum_map_natAbs_eq_sum_abs (row : List ℤ) :
    (((row.map Int.natAbs).sum : ℕ) : ℤ) = ∑ i ∈ Finset.range row.length, |row.getD i 0| := by
  have hmap : row.map Int.natAbs = (List.range row.length).map fun i => (row.getD i 0).natAbs := by
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    have hi' : i < row.length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ hi']
  rw [hmap, List.sum_map_range,
    Fin.sum_univ_eq_sum_range (fun i => (row.getD i 0).natAbs) _, Nat.cast_sum]
  exact Finset.sum_congr rfl fun _ _ => Int.natCast_natAbs _

/-- Executable `Int.natAbs`-sum form of `sum_abs_pullbackMeasurementRow_le` when `placements.Nodup`
and `∀ p ∈ placements, p.2 < auxRow.length`. -/
theorem sum_natAbs_pullbackMeasurementRow_le {n : ℕ} {placements : List (ℕ × ℕ)}
    {incVars : List ℕ} {auxRow : List ℤ} (hnodup : placements.Nodup)
    (hD : ∀ p ∈ placements, p.2 < auxRow.length) (copyIdx : ℕ) :
    ((pullbackMeasurementRow n placements incVars copyIdx auxRow).map Int.natAbs).sum ≤
      (auxRow.map Int.natAbs).sum := by
  have h := sum_abs_pullbackMeasurementRow_le (n := n) (D := auxRow.length) (incVars := incVars)
    hnodup hD copyIdx auxRow
  have hlhs := sum_map_natAbs_eq_sum_abs
    (pullbackMeasurementRow n placements incVars copyIdx auxRow)
  rw [length_pullbackMeasurementRow] at hlhs
  rw [← hlhs, ← sum_map_natAbs_eq_sum_abs auxRow] at h; exact_mod_cast h

/-- When `placements.Nodup`, `∀ p ∈ placements, p.2 < D`, and every entry of `auxRow` lies in
`[-1, 1]` (in particular `{0, 1, -1}`), the `ℓ₁`-norm of `pullbackMeasurementRow` is at most
`D`. -/
theorem sum_abs_pullbackMeasurementRow_le_of_abs_le_one {n D : ℕ} {placements : List (ℕ × ℕ)}
    {incVars : List ℕ} (hnodup : placements.Nodup) (hD : ∀ p ∈ placements, p.2 < D)
    {auxRow : List ℤ} (haux : ∀ z ∈ auxRow, |z| ≤ 1) (copyIdx : ℕ) :
    (∑ v ∈ Finset.range n,
      |(pullbackMeasurementRow n placements incVars copyIdx auxRow).getD v 0|) ≤ D := by
  refine (sum_abs_pullbackMeasurementRow_le (incVars := incVars) hnodup hD copyIdx auxRow).trans ?_
  have hbound : ∀ y ∈ Finset.range D, |auxRow.getD y 0| ≤ (1 : ℤ) := fun y _ =>
    (List.getD_mem_or auxRow y 0).elim (haux _) fun hzero => by rw [hzero]; simp
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using
    Finset.sum_le_sum hbound

/-- **Boolean evaluation bound in `[-D, D]` (equation `(4.15)` of [OpenAI2026ETH]).** When
`placements.Nodup`, `∀ p ∈ placements, p.2 < D`, `∀ z ∈ auxRow, |z| ≤ 1`, and `∀ v < n, |x v| ≤ 1`
(in particular any Boolean vector `x ∈ {0, 1}^n`), the inner product of `pullbackMeasurementRow`
with `x` lies in `[-D, D]`. -/
theorem abs_zipWith_mul_sum_pullbackMeasurementRow_le {n D : ℕ} {placements : List (ℕ × ℕ)}
    {incVars : List ℕ} (hnodup : placements.Nodup) (hD : ∀ p ∈ placements, p.2 < D)
    {auxRow : List ℤ} (haux : ∀ z ∈ auxRow, |z| ≤ 1) (copyIdx : ℕ)
    {x : ℕ → ℤ} (hx : ∀ v < n, |x v| ≤ 1) :
    |(List.zipWith (· * ·) (pullbackMeasurementRow n placements incVars copyIdx auxRow)
        ((List.range n).map x)).sum| ≤ D := by
  set row := pullbackMeasurementRow n placements incVars copyIdx auxRow
  rw [zipWith_mul_sum_map_range (by simp [row]), length_pullbackMeasurementRow]
  have hstep : (∑ v ∈ Finset.range n, |row.getD v 0 * x v|) ≤
      ∑ v ∈ Finset.range n, |row.getD v 0| :=
    Finset.sum_le_sum fun v hv => by
      rw [abs_mul]
      have hxv := hx v (Finset.mem_range.mp hv); have hr := abs_nonneg (row.getD v 0); nlinarith
  exact (Finset.abs_sum_le_sum_abs _ _).trans (hstep.trans
    (sum_abs_pullbackMeasurementRow_le_of_abs_le_one (incVars := incVars) hnodup hD haux copyIdx))

/-- Column restriction to a duplicate-free subset `groupVars` does not increase row `ℓ₁`-norm. -/
theorem sum_natAbs_restrictGroupRow_le {groupVars : List ℕ} (hnodup : groupVars.Nodup)
    (row : List ℤ) :
    (((groupVars.map fun v => row.getD v 0).map Int.natAbs).sum) ≤ (row.map Int.natAbs).sum := by
  have hlhs : ((((groupVars.map fun v => row.getD v 0).map Int.natAbs).sum : ℕ) : ℤ) =
      ∑ v ∈ groupVars.toFinset, |row.getD v 0| := by
    rw [sum_map_natAbs_eq_sum_abs, List.length_map, ← sum_range_groupVars_eq_toFinset hnodup]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj'), List.getElem_map,
      List.getD_eq_getElem _ _ hj']
  have hle : (∑ v ∈ groupVars.toFinset, |row.getD v 0|) ≤
      ∑ v ∈ Finset.range row.length, |row.getD v 0| := by
    rw [← Finset.sum_subset (Finset.filter_subset (· < row.length) groupVars.toFinset)
      fun v hv hnot => by
        simp only [Finset.mem_filter, hv, true_and, not_lt] at hnot
        rw [List.getD_eq_default _ _ hnot]; simp]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun v hv => Finset.mem_range.mpr (Finset.mem_filter.mp hv).2) fun _ _ _ => abs_nonneg _
  rw [← hlhs, ← sum_map_natAbs_eq_sum_abs row] at hle; exact_mod_cast hle

/-- **Total polynomial `ℓ₁` preservation for `pullbackReplacementRow` (Lemma 4.6 of
[OpenAI2026ETH]).** When `placements.Nodup` and `∀ p ∈ placements, p.2 < D`, the sum across all
variables `v < n` and degrees `k < R` of `|Cslib.rowEntry (pullbackReplacementRow ...) v k|` is at
most the corresponding sum across `y < D` of row `u_e` in `blockRepl`. -/
theorem sum_abs_pullbackReplacementRow_le {n R D : ℕ} {placements : List (ℕ × ℕ)}
    {incVars : List ℕ} {e : ℕ} {blockRepl : List (List (List ℤ))}
    (hnodup : placements.Nodup) (hD : ∀ p ∈ placements, p.2 < D) :
    (∑ v ∈ Finset.range n, ∑ k ∈ Finset.range R,
      |Cslib.rowEntry (pullbackReplacementRow n R placements incVars e blockRepl) v k|) ≤
      ∑ y ∈ Finset.range D, ∑ k ∈ Finset.range R,
        |Cslib.rowEntry (blockRepl.getD (placements.getD e (0, 0)).2 []) y k| := by
  set row := pullbackReplacementRow n R placements incVars e blockRepl
  set pe := placements.getD e (0, 0); set uRow := blockRepl.getD pe.2 []
  have hslice (l : List (List ℤ)) (i k : ℕ) :
      (l.map fun poly => poly.getD k 0).getD i 0 = Cslib.rowEntry l i k :=
    List.getD_map l ([] : List ℤ) (fun poly : List ℤ => poly.getD k 0)
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range D)]
  refine Finset.sum_le_sum fun k hk => ?_
  have hlhs_eq : (∑ v ∈ Finset.range n, |Cslib.rowEntry row v k|) =
      ∑ v ∈ Finset.range n, |(pullbackMeasurementRow n placements incVars pe.1
        (uRow.map fun poly => poly.getD k 0)).getD v 0| := by
    dsimp only [row]
    rw [← map_coeff_pullbackReplacementRow n R placements incVars e blockRepl
      (Finset.mem_range.mp hk)]
    exact Finset.sum_congr rfl fun v _ => by rw [hslice]
  rw [hlhs_eq]
  exact (sum_abs_pullbackMeasurementRow_le (incVars := incVars) hnodup hD pe.1 _).trans
    (le_of_eq (Finset.sum_congr rfl fun y _ => by rw [hslice]))

/-- **`Cslib.jetL1Norm` preservation for `pullbackReplacementRow`.** When `placements.Nodup`, the
executable `ℓ₁` table norm `Cslib.jetL1Norm` of `pullbackReplacementRow` is at most that of row
`u_e` in `blockRepl`. -/
theorem jetL1Norm_pullbackReplacementRow_le {n R : ℕ} {placements : List (ℕ × ℕ)}
    {incVars : List ℕ} {e : ℕ} {blockRepl : List (List (List ℤ))} (hnodup : placements.Nodup) :
    Cslib.jetL1Norm (pullbackReplacementRow n R placements incVars e blockRepl) ≤
      Cslib.jetL1Norm (blockRepl.getD (placements.getD e (0, 0)).2 []) := by
  set row := pullbackReplacementRow n R placements incVars e blockRepl
  set uRow := blockRepl.getD (placements.getD e (0, 0)).2 []
  let D := (placements.map Prod.snd).sum + 1
  have hD : ∀ p ∈ placements, p.2 < D := fun p hp =>
    Nat.lt_succ_of_le (List.le_sum_of_mem (List.mem_map_of_mem hp))
  have hlhs : Cslib.jetL1Norm row =
      ∑ v ∈ Finset.range n, ∑ k ∈ Finset.range R, (Cslib.rowEntry row v k).natAbs := by
    dsimp only [row, pullbackReplacementRow]; rw [Cslib.jetL1Norm_tabulateTable]
    exact Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun k hk => by
      rw [Cslib.rowEntry_tabulateTable_of_lt _ (Finset.mem_range.mp hv) (Finset.mem_range.mp hk)]
  have hmid : (∑ v ∈ Finset.range n, ∑ k ∈ Finset.range R, (Cslib.rowEntry row v k).natAbs) ≤
      ∑ y ∈ Finset.range D, ∑ k ∈ Finset.range R, (Cslib.rowEntry uRow y k).natAbs := by
    have hz := sum_abs_pullbackReplacementRow_le (n := n) (R := R) (D := D) (incVars := incVars)
      (e := e) (blockRepl := blockRepl) hnodup hD
    simp only [← Int.natCast_natAbs] at hz; exact_mod_cast hz
  exact (le_of_eq hlhs).trans (hmid.trans (Cslib.sum_rowEntry_natAbs_le_jetL1Norm D R uRow))

/-! ### Group-separation kernel transfer -/

/-- When `groupVars.Nodup`, `∀ v ∈ groupVars, v < row.length`, and `x` vanishes below `row.length`
outside `groupVars`, evaluating the restricted row against `x` on `groupVars` agrees with
evaluating `row` against `x` on `0, …, row.length - 1`. -/
theorem sum_restrictGroupRow_mul {K : Type*} [CommRing K]
    {groupVars : List ℕ} {row : List ℤ} {x : ℕ → K}
    (hnodup : groupVars.Nodup) (hvars : ∀ v ∈ groupVars, v < row.length)
    (hsupp : ∀ v < row.length, v ∉ groupVars → x v = 0) :
    (∑ j ∈ Finset.range groupVars.length,
      ((groupVars.map fun v => row.getD v 0).getD j 0 : K) * x (groupVars.getD j 0)) =
      ∑ v ∈ Finset.range row.length, (row.getD v 0 : K) * x v := by
  have hcongr : (∑ j ∈ Finset.range groupVars.length,
        ((groupVars.map fun v => row.getD v 0).getD j 0 : K) * x (groupVars.getD j 0)) =
      ∑ j ∈ Finset.range groupVars.length,
        (row.getD (groupVars.getD j 0) 0 : K) * x (groupVars.getD j 0) :=
    Finset.sum_congr rfl fun j hj => by
      have hj' := Finset.mem_range.mp hj
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj'), List.getElem_map,
        List.getD_eq_getElem _ _ hj']
  rw [hcongr, sum_range_groupVars_eq_toFinset hnodup fun v => (row.getD v 0 : K) * x v]
  refine Finset.sum_subset (fun v hv => Finset.mem_range.mpr (hvars v (List.mem_toFinset.mp hv)))
    fun v hv hnot => ?_
  rw [hsupp v (Finset.mem_range.mp hv) (mt List.mem_toFinset.mpr hnot), mul_zero]

/-- **Kernel transfer from `restrictGroupColumns` to `blockMeas` (`C^B (π_c ι ξ̃) = 0`, p. 32 of
[OpenAI2026ETH]).** When `groupVars.Nodup`, `∀ v ∈ groupVars, v < n`, `∀ v ∈ incVars, v < n`,
`∀ p ∈ placements, p.2 < D`, `x` vanishes below `n` outside `groupVars`, and its restriction lies
in the kernel of `restrictGroupColumns groupVars (pullbackMeasurementMatrix ...)`, every
`copyIdx < h` and `auxRow ∈ blockMeas` annihilates `copyEmbedExec placements incVars x copyIdx`. -/
theorem sum_copyEmbedExec_eq_zero_of_restrict_kernel {K : Type*} [CommRing K]
    {n h D : ℕ} {groupVars : List ℕ} {placements : List (ℕ × ℕ)} {incVars : List ℕ}
    {blockMeas : List (List ℤ)} {x : ℕ → K}
    (hnodup : groupVars.Nodup) (hgroup : ∀ v ∈ groupVars, v < n)
    (hinc : ∀ v ∈ incVars, v < n) (hD : ∀ p ∈ placements, p.2 < D)
    (hsupp : ∀ v < n, v ∉ groupVars → x v = 0)
    (hker : ∀ r ∈ restrictGroupColumns groupVars
      (pullbackMeasurementMatrix n h placements incVars blockMeas),
      ∑ j ∈ Finset.range groupVars.length, (r.getD j 0 : K) * x (groupVars.getD j 0) = 0)
    {copyIdx : ℕ} (hcopy : copyIdx < h) {auxRow : List ℤ} (haux : auxRow ∈ blockMeas) :
    ∑ y ∈ Finset.range D,
      (auxRow.getD y 0 : K) * copyEmbedExec placements incVars x copyIdx y = 0 := by
  set pbRow := pullbackMeasurementRow n placements incVars copyIdx auxRow
  have hmem_rest : (groupVars.map fun v => pbRow.getD v 0) ∈
      restrictGroupColumns groupVars
        (pullbackMeasurementMatrix n h placements incVars blockMeas) := by
    simp only [restrictGroupColumns, pullbackMeasurementMatrix, List.mem_map, List.mem_flatMap,
      List.mem_range]
    exact ⟨pbRow, ⟨copyIdx, hcopy, auxRow, haux, rfl⟩, rfl⟩
  have hzero := hker _ hmem_rest
  rw [sum_restrictGroupRow_mul hnodup
    (by simpa only [pbRow, length_pullbackMeasurementRow] using hgroup)
    (by simpa only [pbRow, length_pullbackMeasurementRow] using hsupp)] at hzero
  simp only [pbRow, length_pullbackMeasurementRow] at hzero
  rwa [sum_pullbackMeasurementRow_mul hinc hD] at hzero

/-- **Support separation under copy embedding.** When `∀ v ∈ incVars, v < varSchedules.length`, `x`
vanishes below `varSchedules.length` outside `varGroupList varSchedules t g`, and every incidence
`e < min placements.length incVars.length` placed at `(copyIdx, y)` has step-`t` schedule value
`labelGroup ≠ g`, `copyEmbedExec placements incVars x copyIdx y = 0`. -/
theorem copyEmbedExec_eq_zero_of_ne_group {K : Type*} [AddCommMonoid K]
    {varSchedules : List (List ℕ)} {t g : ℕ} {placements : List (ℕ × ℕ)} {incVars : List ℕ}
    {x : ℕ → K} {copyIdx y labelGroup : ℕ}
    (hinc : ∀ v ∈ incVars, v < varSchedules.length)
    (hsupp : ∀ v < varSchedules.length, v ∉ varGroupList varSchedules t g → x v = 0)
    (hcompat : ∀ e < min placements.length incVars.length,
      placements.getD e (0, 0) = (copyIdx, y) →
        (varSchedules.getD (incVars.getD e 0) []).getD t 0 = labelGroup)
    (hne : labelGroup ≠ g) :
    copyEmbedExec placements incVars x copyIdx y = 0 := by
  rw [copyEmbedExec, sum_map_zip (0, 0) 0]
  refine Finset.sum_eq_zero fun e he => ?_
  have he' := Finset.mem_range.mp he
  dsimp only
  split_ifs with hmatch
  · exact hsupp _ (hinc _ (getD_mem_of_lt 0 (Nat.lt_min.mp he').2)) fun hmem =>
      hne ((hcompat e he' (Prod.ext hmatch.1 hmatch.2)).symm.trans (mem_varGroupList.mp hmem).2)
  · rfl

/-- **End-to-end replacement-row kernel-orthogonality transfer (Section 4.5, p. 32 and Lemma 4.7,
p. 34 of [OpenAI2026ETH]).** Under `groupVars.Nodup`, `∀ v ∈ groupVars, v < n`,
`∀ v ∈ incVars, v < n`, `∀ p ∈ placements, p.2 < D`, `(placements.getD e (0, 0)).1 < h`, and row
`u_e` polynomial lengths `≤ R`, if `x : ℕ → K` is supported on `groupVars`, lies in the restricted
kernel of `pullbackMeasurementMatrix`, has `copyEmbedExec ... c_e` vanishing on `badY` below `D`,
and row `u_e` annihilates at `t` every `blockMeas`-kernel vector avoiding `badY`, then evaluating
`pullbackReplacementRow` at `t` against `x` yields `0`. -/
theorem sum_evalCoeffList_pullbackReplacementRow_eq_zero_of_kernel {K : Type*} [CommRing K]
    {n h R D : ℕ} {groupVars : List ℕ} {placements : List (ℕ × ℕ)} {incVars : List ℕ}
    {blockMeas : List (List ℤ)} {blockRepl : List (List (List ℤ))} {e : ℕ} {t : K} {x : ℕ → K}
    {badY : ℕ → Prop}
    (hnodup : groupVars.Nodup) (hgroup : ∀ v ∈ groupVars, v < n)
    (hinc : ∀ v ∈ incVars, v < n) (hD : ∀ p ∈ placements, p.2 < D)
    (hcopy : (placements.getD e (0, 0)).1 < h)
    (hdeg : ∀ poly ∈ blockRepl.getD (placements.getD e (0, 0)).2 [], poly.length ≤ R)
    (hsupp : ∀ v < n, v ∉ groupVars → x v = 0)
    (hker : ∀ r ∈ restrictGroupColumns groupVars
      (pullbackMeasurementMatrix n h placements incVars blockMeas),
      ∑ j ∈ Finset.range groupVars.length, (r.getD j 0 : K) * x (groupVars.getD j 0) = 0)
    (havoid : ∀ y < D, badY y →
      copyEmbedExec placements incVars x (placements.getD e (0, 0)).1 y = 0)
    (hblockAnn : ∀ η : ℕ → K,
      (∀ auxRow ∈ blockMeas, ∑ y ∈ Finset.range D, (auxRow.getD y 0 : K) * η y = 0) →
      (∀ y < D, badY y → η y = 0) →
      ∑ y ∈ Finset.range D,
        Polynomial.evalCoeffList t
          (((blockRepl.getD (placements.getD e (0, 0)).2 []).getD y []).map Int.cast) * η y = 0) :
    (∑ v ∈ Finset.range n,
      Polynomial.evalCoeffList t
        (((pullbackReplacementRow n R placements incVars e blockRepl).getD v []).map Int.cast) *
        x v) = 0 := by
  rw [sum_evalCoeffList_pullbackReplacementRow hinc hD hdeg t x]
  exact hblockAnn _ (fun _ haux =>
    sum_copyEmbedExec_eq_zero_of_restrict_kernel hnodup hgroup hinc hD hsupp hker hcopy haux) havoid

/-! ### Specification bridges to `Foundations.LinearAlgebra.VariableCopyPlacement` -/

private theorem sum_map_zip_ofFn {M : ℕ} {K : Type*} [AddCommMonoid K] {α β : Type*}
    (da : α) (db : β) (fa : Fin M → α) (fb : Fin M → β) (f : α × β → K) :
    (((List.ofFn fa).zip (List.ofFn fb)).map f).sum = ∑ e : Fin M, f (fa e, fb e) := by
  have hmin : min (List.ofFn fa).length (List.ofFn fb).length = M := by simp
  rw [sum_map_zip da db, hmin, ← Fin.sum_univ_eq_sum_range (fun i =>
    f ((List.ofFn fa).getD i da, (List.ofFn fb).getD i db)) M]
  refine Finset.sum_congr rfl fun e _ => ?_
  have ha : e.1 < (List.ofFn fa).length := by simpa only [List.length_ofFn] using e.2
  have hb : e.1 < (List.ofFn fb).length := by simpa only [List.length_ofFn] using e.2
  simp only [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb, List.getElem_ofFn]

/-- `copyEmbedExec` agrees with `Cslib.LinearAlgebra.copyProj ∘ Cslib.LinearAlgebra.copyEmbed`
under any injective integer encoding `code` of `AuxLabel Q r`. -/
theorem copyEmbedExec_ofFn_eq_copyProj_copyEmbed {M n h Q r : ℕ} {K : Type*} [AddCommMonoid K]
    (place : Fin M → Fin h × Cslib.LinearAlgebra.AuxLabel Q r) (varOf : Fin M → Fin n)
    {code : Cslib.LinearAlgebra.AuxLabel Q r → ℕ} (hcode : Function.Injective code)
    (x : Fin n → K) (xExec : ℕ → K) (hx : ∀ v : Fin n, xExec v.1 = x v)
    (c : Fin h) (u : Cslib.LinearAlgebra.AuxLabel Q r) :
    copyEmbedExec (List.ofFn fun e => ((place e).1.val, code (place e).2))
        (List.ofFn fun e => (varOf e).1) xExec c.1 (code u) =
      Cslib.LinearAlgebra.copyProj c (Cslib.LinearAlgebra.copyEmbed place varOf x) u := by
  classical
  rw [copyEmbedExec, sum_map_zip_ofFn (0, 0) 0, Cslib.LinearAlgebra.copyProj,
    Cslib.LinearAlgebra.copyEmbed, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  dsimp only
  have hiff : ((place e).1.1 = c.1 ∧ code (place e).2 = code u) ↔ place e = (c, u) := by
    rw [Prod.ext_iff, Fin.ext_iff, hcode.eq_iff]
  by_cases hp : place e = (c, u)
  · rw [ite_eq_left (hiff.mpr hp), ite_eq_left hp, hx]
  · rw [ite_eq_right (mt hiff.mp hp), ite_eq_right hp]

/-- Entry `v` of `pullbackMeasurementRow` agrees with
`Cslib.LinearAlgebra.varMeasurementMatrix Q r A₀ R ℤ place varOf (c, β) v` whenever `auxRow`
encodes row `β` of `Cslib.LinearAlgebra.measurementMatrix` along `code`. -/
theorem getD_pullbackMeasurementRow_ofFn_eq_varMeasurementMatrix {M n h Q r A₀ R : ℕ}
    (place : Fin M → Fin h × Cslib.LinearAlgebra.AuxLabel Q r) (varOf : Fin M → Fin n)
    (code : Cslib.LinearAlgebra.AuxLabel Q r → ℕ) (auxRow : List ℤ)
    (c : Fin h) (β : Cslib.LinearAlgebra.measurementIndices Q r A₀ R)
    (hrow : ∀ u : Cslib.LinearAlgebra.AuxLabel Q r,
      auxRow.getD (code u) 0 = Cslib.LinearAlgebra.measurementMatrix Q r A₀ R ℤ β u)
    (v : Fin n) :
    (pullbackMeasurementRow n (List.ofFn fun e => ((place e).1.val, code (place e).2))
        (List.ofFn fun e => (varOf e).1) c.1 auxRow).getD v.1 0 =
      Cslib.LinearAlgebra.varMeasurementMatrix Q r A₀ R ℤ place varOf (c, β) v := by
  classical
  rw [pullbackMeasurementRow, List.getD_map_range _ 0 v.2, sum_map_zip_ofFn (0, 0) 0,
    Cslib.LinearAlgebra.varMeasurementMatrix, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  dsimp only
  have hiff : ((place e).1.1 = c.1 ∧ (varOf e).1 = v.1) ↔ ((place e).1 = c ∧ varOf e = v) := by
    simp only [Fin.ext_iff]
  by_cases hm : (place e).1 = c ∧ varOf e = v
  · rw [ite_eq_left (hiff.mpr hm), ite_eq_left hm, hrow]
  · rw [ite_eq_right (mt hiff.mp hm), ite_eq_right hm]

/-- When `Cslib.rowEntry (blockRepl.getD (code (place e).2) []) (code y) k` agrees with the
degree-`k` coefficient of `Cslib.LinearAlgebra.auxReplacementRowScaledInt` for all `y` and `k < R`,
entry `v` of `pullbackReplacementRow` equals `Polynomial.coeffsBelow _ R` of
`Cslib.LinearAlgebra.varReplacementRowScaledInt`. -/
theorem getD_pullbackReplacementRow_ofFn_eq_coeffsBelow_varReplacementRowScaledInt
    {M n h Q r A₀ R : ℕ}
    (place : Fin M → Fin h × Cslib.LinearAlgebra.AuxLabel Q r) (varOf : Fin M → Fin n)
    (code : Cslib.LinearAlgebra.AuxLabel Q r → ℕ) (blockRepl : List (List (List ℤ))) (e : Fin M)
    (hrepl : ∀ (y : Cslib.LinearAlgebra.AuxLabel Q r) {k : ℕ}, k < R →
      Cslib.rowEntry (blockRepl.getD (code (place e).2) []) (code y) k =
        (Cslib.LinearAlgebra.auxReplacementRowScaledInt Q r A₀ R (place e).2 y).coeff k)
    (v : Fin n) :
    (pullbackReplacementRow n R (List.ofFn fun i => ((place i).1.val, code (place i).2))
        (List.ofFn fun i => (varOf i).1) e.1 blockRepl).getD v.1 [] =
      (Cslib.LinearAlgebra.varReplacementRowScaledInt Q r A₀ R place varOf e v).coeffsBelow R := by
  classical
  have he_lt : e.1 < (List.ofFn fun i : Fin M => ((place i).1.1, code (place i).2)).length := by
    simpa only [List.length_ofFn] using e.2
  rw [pullbackReplacementRow, Cslib.tabulateTable, List.getD_eq_getElem _ _ he_lt,
    List.getElem_ofFn, List.getD_map_range _ [] v.2, Polynomial.coeffsBelow]
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < R := List.mem_range.mp hk
  rw [sum_map_zip_ofFn (0, 0) 0, Cslib.LinearAlgebra.varReplacementRowScaledInt,
    Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  have hiff : ((place i).1.1 = (place e).1.1 ∧ (varOf i).1 = v.1) ↔
      ((place i).1 = (place e).1 ∧ varOf i = v) := by simp only [Fin.ext_iff]
  by_cases hm : (place i).1 = (place e).1 ∧ varOf i = v
  · rw [ite_eq_left (hiff.mpr hm), ite_eq_left hm, hrepl _ hk']
  · rw [ite_eq_right (mt hiff.mp hm), ite_eq_right hm]

/-- When `0 < R` and `Cslib.rowEntry (blockRepl.getD (code (place e).2) []) (code y) k` agrees with
the degree-`k` coefficient of `Cslib.LinearAlgebra.auxReplacementRowScaledInt` for all `y` and
`k < R`, `Polynomial.ofCoeffList` of entry `v` of `pullbackReplacementRow` equals
`Cslib.LinearAlgebra.varReplacementRowScaledInt Q r A₀ R place varOf e v`. -/
theorem ofCoeffList_pullbackReplacementRow_ofFn_eq_varReplacementRowScaledInt
    {M n h Q r A₀ R : ℕ} (hR : 0 < R)
    (place : Fin M → Fin h × Cslib.LinearAlgebra.AuxLabel Q r) (varOf : Fin M → Fin n)
    (code : Cslib.LinearAlgebra.AuxLabel Q r → ℕ) (blockRepl : List (List (List ℤ))) (e : Fin M)
    (hrepl : ∀ (y : Cslib.LinearAlgebra.AuxLabel Q r) {k : ℕ}, k < R →
      Cslib.rowEntry (blockRepl.getD (code (place e).2) []) (code y) k =
        (Cslib.LinearAlgebra.auxReplacementRowScaledInt Q r A₀ R (place e).2 y).coeff k)
    (v : Fin n) :
    Polynomial.ofCoeffList
        ((pullbackReplacementRow n R (List.ofFn fun i => ((place i).1.val, code (place i).2))
          (List.ofFn fun i => (varOf i).1) e.1 blockRepl).getD v.1 []) =
      Cslib.LinearAlgebra.varReplacementRowScaledInt Q r A₀ R place varOf e v := by
  rw [getD_pullbackReplacementRow_ofFn_eq_coeffsBelow_varReplacementRowScaledInt place varOf code
    blockRepl e hrepl v]
  refine Polynomial.ofCoeffList_coeffsBelow
    (Nat.lt_of_le_of_lt (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_)
      (Nat.sub_lt hR Nat.one_pos))
  have hq := congrArg (fun p : Polynomial ℚ => p.coeff N)
    (Cslib.LinearAlgebra.map_varReplacementRowScaledInt Q r A₀ R place varOf e v)
  simp only [Polynomial.coeff_map, eq_intCast, Polynomial.coeff_smul, smul_eq_mul] at hq
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
    ((Cslib.LinearAlgebra.natDegree_varReplacementRow_le Q r A₀ R place varOf e v).trans_lt hN),
    mul_zero] at hq
  exact Int.cast_eq_zero.mp hq

/-! ### Plain polynomial-time certificates (`ComputableInPolyTime`) -/

section PolyTime

open ComputableInPolyTime

private theorem cp_take : ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.take p.2)
    (encPair (encList encNat) encUnary) (encList encNat) := by fun_prop

private theorem cp_count : ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.count p.2)
    (encPair (encList encNat) encNat) encUnary := by fun_prop

private theorem cp_intBin_sum : ComputableInPolyTime List.sum (encList encIntBin) encIntBin := by
  fun_prop

/-- Compositional plain polynomial-time certificate for `fiberRanks`. -/
@[fun_prop] theorem computableInPolyTime_fiberRanksWithInput {Input : Type}
    {encIn : Input ↪ List Bool} {labels : Input → List ℕ}
    (hlabels : ComputableInPolyTime labels encIn (encList encNat)) :
    ComputableInPolyTime (fun x => fiberRanks (labels x)) encIn (encList encNat) := by
  unfold fiberRanks
  apply mapWithInput (range.comp ((length_list encNat).comp hlabels))
  have htake := cp_take.comp ((hlabels.comp (fst encIn encUnary)).prod (snd encIn encUnary))
  have hval := listGetDWithInput (hlabels.comp (fst encIn encUnary)) (snd encIn encUnary) 0
  exact unary_to_binary.comp (cp_count.comp (htake.prod hval))

/-- `fiberRanks` is computable in polynomial time on framed lists of binary naturals. -/
@[fun_prop] theorem computableInPolyTime_fiberRanks :
    ComputableInPolyTime fiberRanks (encList encNat) (encList encNat) := by fun_prop

/-- Compositional plain polynomial-time certificate for `flatPlacement`. -/
@[fun_prop] theorem computableInPolyTime_flatPlacementWithInput {Input : Type}
    {encIn : Input ↪ List Bool} {D : Input → ℕ} {labels : Input → List ℕ}
    (hD : ComputableInPolyTime D encIn encNat)
    (hlabels : ComputableInPolyTime labels encIn (encList encNat)) :
    ComputableInPolyTime (fun x => flatPlacement (D x) (labels x)) encIn (encList encNat) := by
  have hfib := computableInPolyTime_fiberRanksWithInput hlabels
  unfold flatPlacement
  apply mapWithInput ((zip encNat encNat).comp (hfib.prod hlabels))
  have hp1 := fst encIn (encPair encNat encNat)
  have hp2 := snd encIn (encPair encNat encNat)
  exact binary_add.comp ((binary_mul' hp2.fst' (hD.comp hp1)).prod hp2.snd')

/-- `flatPlacement` is computable in polynomial time from `(D, labels)`. -/
@[fun_prop] theorem computableInPolyTime_flatPlacement :
    ComputableInPolyTime (fun p : ℕ × List ℕ => flatPlacement p.1 p.2)
      (encPair encNat (encList encNat)) (encList encNat) := by fun_prop

/-- Compositional plain polynomial-time certificate for `varGroupList`. -/
@[fun_prop] theorem computableInPolyTime_varGroupListWithInput {Input : Type}
    {encIn : Input ↪ List Bool} {varSchedules : Input → List (List ℕ)} {t g : Input → ℕ}
    (hsched : ComputableInPolyTime varSchedules encIn (encList (encList encNat)))
    (ht : ComputableInPolyTime t encIn encNat) (hg : ComputableInPolyTime g encIn encNat) :
    ComputableInPolyTime (fun x => varGroupList (varSchedules x) (t x) (g x))
      encIn (encList encNat) := by
  have hfilt : ComputableInPolyTime
      (fun x => varGroupList (varSchedules x) (t x) (g x)) encIn (encList encUnary) := by
    unfold varGroupList
    apply filterWithInput (range.comp ((length_list (encList encNat)).comp hsched))
    have hrow := listGetDWithInput (hsched.comp (fst encIn encUnary)) (snd encIn encUnary) []
    exact decide_eq'
      (listGetD_binary 0 hrow (ht.comp (fst encIn encUnary))) (hg.comp (fst encIn encUnary))
  have hmap : ComputableInPolyTime (List.map id) (encList encUnary) (encList encNat) :=
    mapWithInput id' (unary_to_binary.comp (snd (encList encUnary) encUnary))
  exact (hmap.comp hfilt).of_enc_eq fun _ => congrArg (encList encNat) (by simp)

/-- `varGroupList` is computable in polynomial time on `(varSchedules, (t, g))`. -/
@[fun_prop] theorem computableInPolyTime_varGroupList :
    ComputableInPolyTime
      (fun ((varSchedules, t, g) : List (List ℕ) × (ℕ × ℕ)) => varGroupList varSchedules t g)
      (encPair (encList (encList encNat)) (encPair encNat encNat)) (encList encNat) := by fun_prop

private theorem ite_eq_and_intBin {Q : Type} {encQ : Q ↪ List Bool} {a₁ a₂ b₁ b₂ : Q → ℕ}
    {val : Q → ℤ} (ha₁ : ComputableInPolyTime a₁ encQ encNat)
    (ha₂ : ComputableInPolyTime a₂ encQ encNat)
    (hb₁ : ComputableInPolyTime b₁ encQ encNat)
    (hb₂ : ComputableInPolyTime b₂ encQ encNat)
    (hval : ComputableInPolyTime val encQ encIntBin) :
    ComputableInPolyTime
      (fun q => if a₁ q = a₂ q ∧ b₁ q = b₂ q then val q else 0) encQ encIntBin := by
  have hcond := bool_and.comp ((decide_eq' ha₁ ha₂).prod (decide_eq' hb₁ hb₂))
  refine (hcond.ite' hval (const 0)).of_enc_eq fun q => congrArg encIntBin ?_
  dsimp only [Function.comp_def]
  by_cases h1 : a₁ q = a₂ q <;> [by_cases h2 : b₁ q = b₂ q <;> simp [h1, h2]; simp [h1]]

/-- Compositional plain polynomial-time certificate for `pullbackMeasurementRow` (`n` in unary). -/
@[fun_prop] theorem computableInPolyTime_pullbackMeasurementRowWithInput {Input : Type}
    {encIn : Input ↪ List Bool} {n : Input → ℕ} {placements : Input → List (ℕ × ℕ)}
    {incVars : Input → List ℕ} {copyIdx : Input → ℕ} {auxRow : Input → List ℤ}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hpl : ComputableInPolyTime placements encIn (encList (encPair encNat encNat)))
    (hinc : ComputableInPolyTime incVars encIn (encList encNat))
    (hcopy : ComputableInPolyTime copyIdx encIn encNat)
    (haux : ComputableInPolyTime auxRow encIn (encList encIntBin)) :
    ComputableInPolyTime
      (fun x => pullbackMeasurementRow (n x) (placements x) (incVars x) (copyIdx x) (auxRow x))
      encIn (encList encIntBin) := by
  unfold pullbackMeasurementRow; apply mapWithInput (range.comp hn); apply cp_intBin_sum.comp
  apply mapWithInput ((zip (encPair encNat encNat) encNat).comp
    ((hpl.comp (fst encIn encUnary)).prod (hinc.comp (fst encIn encUnary))))
  have hxin : ComputableInPolyTime (fun q : (Input × ℕ) × ((ℕ × ℕ) × ℕ) => q.1.1)
      (encPair (encPair encIn encUnary) (encPair (encPair encNat encNat) encNat)) encIn :=
    (fst encIn encUnary).comp (fst _ _)
  exact ite_eq_and_intBin
    ((fst encNat encNat).comp ((fst _ _).comp (snd _ _))) (hcopy.comp hxin)
    ((snd _ _).comp (snd _ _)) (unary_to_binary.comp ((snd encIn encUnary).comp (fst _ _)))
    (listGetD_binary 0 (haux.comp hxin) ((snd encNat encNat).comp ((fst _ _).comp (snd _ _))))

/-- `pullbackMeasurementRow` is computable in polynomial time with `n` in `encUnary`. -/
@[fun_prop] theorem computableInPolyTime_pullbackMeasurementRow :
    ComputableInPolyTime
      (fun ((n, placements, incVars, copyIdx, auxRow) :
          ℕ × (List (ℕ × ℕ) × (List ℕ × (ℕ × List ℤ)))) =>
        pullbackMeasurementRow n placements incVars copyIdx auxRow)
      (encPair encUnary (encPair (encList (encPair encNat encNat))
        (encPair (encList encNat) (encPair encNat (encList encIntBin)))))
      (encList encIntBin) := by fun_prop

/-- Compositional plain polynomial-time certificate for `pullbackMeasurementMatrix` (`(n, h)` in
unary). -/
@[fun_prop] theorem computableInPolyTime_pullbackMeasurementMatrixWithInput {Input : Type}
    {encIn : Input ↪ List Bool} {n h : Input → ℕ} {placements : Input → List (ℕ × ℕ)}
    {incVars : Input → List ℕ} {blockMeas : Input → List (List ℤ)}
    (hn : ComputableInPolyTime n encIn encUnary) (hh : ComputableInPolyTime h encIn encUnary)
    (hpl : ComputableInPolyTime placements encIn (encList (encPair encNat encNat)))
    (hinc : ComputableInPolyTime incVars encIn (encList encNat))
    (hmeas : ComputableInPolyTime blockMeas encIn (encList (encList encIntBin))) :
    ComputableInPolyTime
      (fun x => pullbackMeasurementMatrix (n x) (h x) (placements x) (incVars x) (blockMeas x))
      encIn (encList (encList encIntBin)) := by
  unfold pullbackMeasurementMatrix; apply flatMapWithInput (range.comp hh)
  apply mapWithInput (hmeas.comp (fst encIn encUnary))
  exact computableInPolyTime_pullbackMeasurementRowWithInput
    (hn.comp ((fst encIn encUnary).comp (fst _ _)))
    (hpl.comp ((fst encIn encUnary).comp (fst _ _)))
    (hinc.comp ((fst encIn encUnary).comp (fst _ _)))
    (unary_to_binary.comp ((snd encIn encUnary).comp (fst _ _)))
    (snd _ _)

/-- `pullbackMeasurementMatrix` is computable in polynomial time with `(n, h)` in `encUnary`. -/
@[fun_prop] theorem computableInPolyTime_pullbackMeasurementMatrix :
    ComputableInPolyTime
      (fun (((n, h), placements, incVars, blockMeas) :
          (ℕ × ℕ) × (List (ℕ × ℕ) × (List ℕ × List (List ℤ)))) =>
        pullbackMeasurementMatrix n h placements incVars blockMeas)
      (encPair (encPair encUnary encUnary) (encPair (encList (encPair encNat encNat))
        (encPair (encList encNat) (encList (encList encIntBin)))))
      (encList (encList encIntBin)) := by fun_prop

/-- Compositional plain polynomial-time certificate for `restrictGroupColumns`. -/
@[fun_prop] theorem computableInPolyTime_restrictGroupColumnsWithInput {Input : Type}
    {encIn : Input ↪ List Bool} {groupVars : Input → List ℕ} {mat : Input → List (List ℤ)}
    (hgroup : ComputableInPolyTime groupVars encIn (encList encNat))
    (hmat : ComputableInPolyTime mat encIn (encList (encList encIntBin))) :
    ComputableInPolyTime (fun x => restrictGroupColumns (groupVars x) (mat x))
      encIn (encList (encList encIntBin)) := by
  unfold restrictGroupColumns; apply mapWithInput hmat
  apply mapWithInput (hgroup.comp (fst encIn (encList encIntBin)))
  exact listGetD_binary 0 ((snd encIn (encList encIntBin)).comp (fst _ _)) (snd _ _)

/-- `restrictGroupColumns` is computable in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_restrictGroupColumns :
    ComputableInPolyTime (fun p : List ℕ × List (List ℤ) => restrictGroupColumns p.1 p.2)
      (encPair (encList encNat) (encList (encList encIntBin)))
      (encList (encList encIntBin)) := by fun_prop

/-- Compositional plain polynomial-time certificate for `pullbackReplacementRow` (`(n, R)` in
unary). -/
@[fun_prop] theorem computableInPolyTime_pullbackReplacementRowWithInput {Input : Type}
    {encIn : Input ↪ List Bool} {n R : Input → ℕ} {placements : Input → List (ℕ × ℕ)}
    {incVars : Input → List ℕ} {e : Input → ℕ} {blockRepl : Input → List (List (List ℤ))}
    (hn : ComputableInPolyTime n encIn encUnary) (hR : ComputableInPolyTime R encIn encUnary)
    (hpl : ComputableInPolyTime placements encIn (encList (encPair encNat encNat)))
    (hinc : ComputableInPolyTime incVars encIn (encList encNat))
    (he : ComputableInPolyTime e encIn encNat)
    (hrepl : ComputableInPolyTime blockRepl encIn (encList (encList (encList encIntBin)))) :
    ComputableInPolyTime
      (fun x => pullbackReplacementRow (n x) (R x) (placements x) (incVars x) (e x) (blockRepl x))
      encIn (encList (encList encIntBin)) := by
  unfold pullbackReplacementRow
  refine Cslib.computableInPolyTime_tabulateTable hn hR ?_
  dsimp only [Cslib.rowEntry]
  have hpe : ComputableInPolyTime _ encIn (encPair encNat encNat) :=
    listGetD_binary (0, 0) hpl he
  have hce := (fst encNat encNat).comp hpe
  have huRow : ComputableInPolyTime _ encIn (encList (encList encIntBin)) :=
    listGetD_binary [] hrepl ((snd encNat encNat).comp hpe)
  have hzip0 := (zip (encPair encNat encNat) encNat).comp (hpl.prod hinc)
  have hxin_vk : ComputableInPolyTime (fun vk : (Input × ℕ) × ℕ => vk.1.1)
      (encPair (encPair encIn encUnary) encUnary) encIn := (fst encIn encUnary).comp (fst _ _)
  apply cp_intBin_sum.comp; apply mapWithInput (hzip0.comp hxin_vk)
  have hxin := hxin_vk.comp (fst (encPair (encPair encIn encUnary) encUnary)
    (encPair (encPair encNat encNat) encNat))
  have hpoly : ComputableInPolyTime _ _ (encList encIntBin) :=
    listGetD_binary [] (huRow.comp hxin) ((snd encNat encNat).comp ((fst _ _).comp (snd _ _)))
  exact ite_eq_and_intBin
    ((fst encNat encNat).comp ((fst _ _).comp (snd _ _))) (hce.comp hxin)
    ((snd _ _).comp (snd _ _))
    (unary_to_binary.comp ((snd encIn encUnary).comp ((fst _ _).comp (fst _ _))))
    ((listGetD 0).comp (hpoly.prod ((snd _ _).comp (fst _ _))))

/-- `pullbackReplacementRow` is computable in polynomial time with `(n, R)` in `encUnary`. -/
@[fun_prop] theorem computableInPolyTime_pullbackReplacementRow :
    ComputableInPolyTime
      (fun (((n, R), placements, incVars, e, blockRepl) :
          (ℕ × ℕ) × (List (ℕ × ℕ) × (List ℕ × (ℕ × List (List (List ℤ)))))) =>
        pullbackReplacementRow n R placements incVars e blockRepl)
      (encPair (encPair encUnary encUnary) (encPair (encList (encPair encNat encNat))
        (encPair (encList encNat) (encPair encNat (encList (encList (encList encIntBin)))))))
      (encList (encList encIntBin)) := by fun_prop

end PolyTime

end Cslib.LinearAlgebra.CopyPlacement
