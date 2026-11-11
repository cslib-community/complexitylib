/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.TimeLayer.Fin

/-!
# Bounded-degree paired-port matrix representations

A `Matrix.PairedPorts M dOut dIn` structure equips a matrix `M : Matrix V V R` with explicit
outgoing ports `Fin dOut` at each row, incoming ports `Fin dIn` at each column, and outgoing port
weights such that:

* outgoing and incoming ports invert one another
  (`outPort u p = some (v, q) ↔ inPort v q = some (u, p)`),
* distinct outgoing ports from a source `u` target distinct vertices (`outPort_target_injective`),
* inactive ports carry weight `0` while active ports carry `M u v`, and
* every nonzero matrix entry `M u v ≠ 0` appears on an outgoing port.

Inactive or zero-weighted active ports are permitted so the representation works uniformly over
arbitrary rings without characteristic assumptions while still determining every matrix entry,
matrix-vector product, and transpose-matrix-vector product as a finite sum over local ports.

## Main definitions

* `Matrix.PairedPorts`: bounded-degree paired-port representation of a matrix.
* `Matrix.PairedPorts.inWeight`: incoming port weight induced by `inPort` and `outWeight`.
* `Matrix.PairedPorts.transpose`: dual paired-port structure on `Mᵀ`.
* `Matrix.PairedPorts.ofLists`: paired ports built from nodup outgoing and incoming lists.
* `Matrix.PairedPorts.finTimeLayer`: lifting paired ports from `P` to `Matrix.finTimeLayer T P`.

## Main results

* `Matrix.PairedPorts.inPort_source_injective`: distinct incoming ports at `v` have distinct
  sources.
* `Matrix.PairedPorts.entry_eq_sum_outPort`: each entry `M u v` is the sum over outgoing ports.
* `Matrix.PairedPorts.mulVec_apply_eq_sum_outPort`,
  `Matrix.PairedPorts.transpose_mulVec_apply_eq_sum_inPort`: local port formulas for `M *ᵥ x` and
  `Mᵀ *ᵥ x`.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 2, Lemma 2.1 (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Matrix

/-- Directed bounded-degree paired-port representation of `M : Matrix V V R`. -/
structure PairedPorts {V R : Type*} [Zero R] (M : Matrix V V R) (dOut dIn : ℕ) where
  /-- Outgoing port map sending `(u, p)` to `some (v, q)` or `none` when inactive. -/
  outPort : V → Fin dOut → Option (V × Fin dIn)
  /-- Incoming port map sending `(v, q)` to `some (u, p)` or `none` when inactive. -/
  inPort : V → Fin dIn → Option (V × Fin dOut)
  /-- Weight carried by outgoing port `(u, p)`. -/
  outWeight : V → Fin dOut → R
  /-- Outgoing and incoming ports are exact mutual inverses. -/
  outPort_eq_some_iff : ∀ u p v q, outPort u p = some (v, q) ↔ inPort v q = some (u, p)
  /-- Distinct outgoing ports from the same source target distinct vertices. -/
  outPort_target_injective :
    ∀ u {p₁ p₂ v q₁ q₂}, outPort u p₁ = some (v, q₁) → outPort u p₂ = some (v, q₂) → p₁ = p₂
  /-- Inactive outgoing ports carry zero weight. -/
  outWeight_eq_zero_of_none : ∀ u p, outPort u p = none → outWeight u p = 0
  /-- Every active outgoing port carries the matrix entry `M u v`. -/
  outWeight_eq_entry : ∀ {u p v q}, outPort u p = some (v, q) → outWeight u p = M u v
  /-- Every nonzero matrix entry is realized by an active outgoing port. -/
  exists_outPort_of_ne_zero : ∀ {u v}, M u v ≠ 0 → ∃ p q, outPort u p = some (v, q)

namespace PairedPorts

section Basic

variable {V R : Type*} [Zero R] {M : Matrix V V R} {dOut dIn : ℕ}

/-- Incoming-to-outgoing direction of mutual port inversion. -/
theorem inPort_eq_some_iff (hp : PairedPorts M dOut dIn) (v : V) (q : Fin dIn)
    (u : V) (p : Fin dOut) :
    hp.inPort v q = some (u, p) ↔ hp.outPort u p = some (v, q) :=
  (hp.outPort_eq_some_iff u p v q).symm

/-- Distinct incoming ports at the same target vertex originate from distinct source vertices. -/
theorem inPort_source_injective (hp : PairedPorts M dOut dIn) (v : V)
    {q₁ q₂ : Fin dIn} {u : V} {p₁ p₂ : Fin dOut}
    (h₁ : hp.inPort v q₁ = some (u, p₁)) (h₂ : hp.inPort v q₂ = some (u, p₂)) : q₁ = q₂ := by
  have h₁' := (hp.outPort_eq_some_iff u p₁ v q₁).mpr h₁
  have h₂' := (hp.outPort_eq_some_iff u p₂ v q₂).mpr h₂
  have hp_eq : p₁ = p₂ := hp.outPort_target_injective u h₁' h₂'
  subst hp_eq
  exact (Prod.mk.inj (Option.some.inj (h₁'.symm.trans h₂'))).2

/-- Every nonzero matrix entry is realized by an active incoming port. -/
theorem exists_inPort_of_ne_zero (hp : PairedPorts M dOut dIn) {u v : V} (h : M u v ≠ 0) :
    ∃ q p, hp.inPort v q = some (u, p) := by
  obtain ⟨p, q, hpq⟩ := hp.exists_outPort_of_ne_zero h
  exact ⟨q, p, (hp.outPort_eq_some_iff u p v q).mp hpq⟩

/-- Weight carried by incoming port `(v, q)`, defined via the paired outgoing port. -/
@[expose] def inWeight (hp : PairedPorts M dOut dIn) (v : V) (q : Fin dIn) : R :=
  match hp.inPort v q with
  | none => 0
  | some (u, p) => hp.outWeight u p

/-- Inactive incoming ports carry zero weight. -/
theorem inWeight_eq_zero_of_none (hp : PairedPorts M dOut dIn) (v : V) (q : Fin dIn)
    (h : hp.inPort v q = none) : hp.inWeight v q = 0 := by
  simp [inWeight, h]

/-- An active incoming port carries the same weight as its paired outgoing port. -/
theorem inWeight_eq_outWeight (hp : PairedPorts M dOut dIn) {v : V} {q : Fin dIn}
    {u : V} {p : Fin dOut} (h : hp.inPort v q = some (u, p)) :
    hp.inWeight v q = hp.outWeight u p := by
  simp [inWeight, h]

/-- Every active incoming port carries the matrix entry `M u v`. -/
theorem inWeight_eq_entry (hp : PairedPorts M dOut dIn) {v : V} {q : Fin dIn}
    {u : V} {p : Fin dOut} (h : hp.inPort v q = some (u, p)) :
    hp.inWeight v q = M u v := by
  rw [hp.inWeight_eq_outWeight h]
  exact hp.outWeight_eq_entry ((hp.outPort_eq_some_iff u p v q).mpr h)

/-- Dual paired-port representation of the transpose matrix `Mᵀ`, swapping outgoing and incoming
ports. -/
@[expose] def transpose (hp : PairedPorts M dOut dIn) : PairedPorts Mᵀ dIn dOut where
  outPort := hp.inPort
  inPort := hp.outPort
  outWeight := hp.inWeight
  outPort_eq_some_iff u q v p := (hp.outPort_eq_some_iff v p u q).symm
  outPort_target_injective := hp.inPort_source_injective
  outWeight_eq_zero_of_none := hp.inWeight_eq_zero_of_none
  outWeight_eq_entry h := hp.inWeight_eq_entry h
  exists_outPort_of_ne_zero h := hp.exists_inPort_of_ne_zero h

@[simp]
theorem transpose_outPort (hp : PairedPorts M dOut dIn) : hp.transpose.outPort = hp.inPort := rfl

@[simp]
theorem transpose_inPort (hp : PairedPorts M dOut dIn) : hp.transpose.inPort = hp.outPort := rfl

@[simp]
theorem transpose_outWeight (hp : PairedPorts M dOut dIn) :
    hp.transpose.outWeight = hp.inWeight := rfl

end Basic

section Algebra

/-- Every matrix entry `M u v` is the sum of `outWeight u p` over outgoing ports targeting `v`. -/
theorem entry_eq_sum_outPort {V R : Type*} [DecidableEq V] [AddCommMonoid R]
    {M : Matrix V V R} {dOut dIn : ℕ} (hp : PairedPorts M dOut dIn) (u v : V) :
    M u v = ∑ p : Fin dOut,
      match hp.outPort u p with
      | none => (0 : R)
      | some (w, _) => if w = v then hp.outWeight u p else 0 := by
  by_cases hex : ∃ p q, hp.outPort u p = some (v, q)
  · obtain ⟨p₀, q₀, hp₀⟩ := hex
    symm
    rw [Finset.sum_eq_single p₀]
    · simp [hp₀, hp.outWeight_eq_entry hp₀]
    · intro p _ hp_ne
      cases h : hp.outPort u p with
      | none => rfl
      | some wq =>
        obtain ⟨w, q⟩ := wq
        by_cases hw : w = v
        · subst hw
          exact absurd (hp.outPort_target_injective u h hp₀) hp_ne
        · simp [hw]
    · intro hmem
      exact absurd (Finset.mem_univ p₀) hmem
  · have hzero : M u v = 0 := by
      by_contra hne
      exact hex (hp.exists_outPort_of_ne_zero hne)
    rw [hzero]
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    cases h : hp.outPort u p with
    | none => rfl
    | some wq =>
      obtain ⟨w, q⟩ := wq
      have hw : w ≠ v := fun heq => hex ⟨p, q, heq ▸ h⟩
      simp [hw]

/-- Every matrix entry `M u v` is the sum of `inWeight v q` over incoming ports originating at
`u`. -/
theorem entry_eq_sum_inPort {V R : Type*} [DecidableEq V] [AddCommMonoid R]
    {M : Matrix V V R} {dOut dIn : ℕ} (hp : PairedPorts M dOut dIn) (u v : V) :
    M u v = ∑ q : Fin dIn,
      match hp.inPort v q with
      | none => (0 : R)
      | some (w, _) => if w = u then hp.inWeight v q else 0 :=
  hp.transpose.entry_eq_sum_outPort v u

/-- Local outgoing-port formula for `(M *ᵥ x) u`. -/
theorem mulVec_apply_eq_sum_outPort {V R : Type*} [Fintype V] [NonAssocSemiring R]
    {M : Matrix V V R} {dOut dIn : ℕ} (hp : PairedPorts M dOut dIn) (x : V → R) (u : V) :
    (M *ᵥ x) u = ∑ p : Fin dOut,
      match hp.outPort u p with
      | none => (0 : R)
      | some (v, _) => hp.outWeight u p * x v := by
  classical
  change (∑ v : V, M u v * x v) = _
  simp_rw [hp.entry_eq_sum_outPort u, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  cases h : hp.outPort u p with
  | none => simp
  | some vq =>
    obtain ⟨v, q⟩ := vq
    rw [Finset.sum_eq_single v]
    · simp
    · intro w _ hw
      simp [hw.symm]
    · intro hmem
      exact absurd (Finset.mem_univ v) hmem

/-- Local incoming-port formula for `(Mᵀ *ᵥ x) v` in terms of `inWeight`. -/
theorem transpose_mulVec_apply_eq_sum_inPort {V R : Type*} [Fintype V] [NonAssocSemiring R]
    {M : Matrix V V R} {dOut dIn : ℕ} (hp : PairedPorts M dOut dIn) (x : V → R) (v : V) :
    (Mᵀ *ᵥ x) v = ∑ q : Fin dIn,
      match hp.inPort v q with
      | none => (0 : R)
      | some (u, _) => hp.inWeight v q * x u :=
  hp.transpose.mulVec_apply_eq_sum_outPort x v

/-- Local incoming-port formula for `(Mᵀ *ᵥ x) v` in terms of `outWeight` at the paired source
port. -/
theorem transpose_mulVec_apply_eq_sum_inPort_outWeight {V R : Type*} [Fintype V]
    [NonAssocSemiring R] {M : Matrix V V R} {dOut dIn : ℕ} (hp : PairedPorts M dOut dIn)
    (x : V → R) (v : V) :
    (Mᵀ *ᵥ x) v = ∑ q : Fin dIn,
      match hp.inPort v q with
      | none => (0 : R)
      | some (u, p) => hp.outWeight u p * x u := by
  rw [hp.transpose_mulVec_apply_eq_sum_inPort]
  refine Finset.sum_congr rfl fun q _ => ?_
  cases h : hp.inPort v q with
  | none => rfl
  | some up =>
    obtain ⟨u, p⟩ := up
    rw [hp.inWeight_eq_outWeight h]

end Algebra

section OfLists

variable {V R : Type*} [DecidableEq V] [Zero R]

/-- Lookup helper pairing the `idx`-th element `v` of `targets u` with the index of `u` in
`other v`, returning `none` if out of bounds. -/
@[expose] def listPortLookup {dOther : ℕ} (targets : V → List V) (other : V → List V)
    (u : V) (idx : ℕ) : Option (V × Fin dOther) :=
  match (targets u)[idx]? with
  | none => none
  | some v =>
    if hq : (other v).idxOf u < dOther then
      some (v, ⟨(other v).idxOf u, hq⟩)
    else
      none

private theorem listPortLookup_eq_some_iff {dOther : ℕ}
    {targets other : V → List V}
    (hother_len : ∀ v, (other v).length ≤ dOther)
    (hmem : ∀ u v, v ∈ targets u → u ∈ other v)
    (u : V) (idx : ℕ) (v : V) (q : Fin dOther) :
    listPortLookup targets other u idx = some (v, q) ↔
      (targets u)[idx]? = some v ∧ q.val = (other v).idxOf u := by
  unfold listPortLookup
  cases hg : (targets u)[idx]? with
  | none => simp
  | some w =>
    have hw_mem : w ∈ targets u := List.mem_of_getElem? hg
    have hu_mem : u ∈ other w := hmem u w hw_mem
    have hq_lt : (other w).idxOf u < dOther :=
      (List.idxOf_lt_length_of_mem hu_mem).trans_le (hother_len w)
    dsimp only
    rw [dite_eq_left hq_lt]
    simp only [Option.some.injEq, Prod.mk.injEq, Fin.ext_iff]
    constructor
    · rintro ⟨rfl, hq_eq⟩
      exact ⟨rfl, hq_eq.symm⟩
    · rintro ⟨rfl, hq_eq⟩
      exact ⟨rfl, hq_eq.symm⟩

private theorem listPortLookup_eq_none_iff {dOther : ℕ}
    {targets other : V → List V}
    (hother_len : ∀ v, (other v).length ≤ dOther)
    (hmem : ∀ u v, v ∈ targets u → u ∈ other v)
    (u : V) (idx : ℕ) :
    listPortLookup (dOther := dOther) targets other u idx = none ↔ (targets u)[idx]? = none := by
  unfold listPortLookup
  cases hg : (targets u)[idx]? with
  | none => simp
  | some w =>
    have hq_lt : (other w).idxOf u < dOther :=
      (List.idxOf_lt_length_of_mem (hmem u w (List.mem_of_getElem? hg))).trans_le (hother_len w)
    dsimp only
    rw [dite_eq_left hq_lt]
    simp

/-- Construct a `PairedPorts` structure from duplicate-free bounded outgoing and incoming neighbor
lists satisfying `v ∈ outTargets u ↔ u ∈ inSources v` and covering all nonzero entries of `M`. -/
@[expose] def ofLists (M : Matrix V V R) (dOut dIn : ℕ)
    (outTargets : V → List V) (inSources : V → List V)
    (hout_nodup : ∀ u, (outTargets u).Nodup)
    (hin_nodup : ∀ v, (inSources v).Nodup)
    (hout_len : ∀ u, (outTargets u).length ≤ dOut)
    (hin_len : ∀ v, (inSources v).length ≤ dIn)
    (hmem_iff : ∀ u v, v ∈ outTargets u ↔ u ∈ inSources v)
    (hne_zero : ∀ {u v}, M u v ≠ 0 → v ∈ outTargets u) :
    PairedPorts M dOut dIn where
  outPort u p := listPortLookup outTargets inSources u p.val
  inPort v q := listPortLookup inSources outTargets v q.val
  outWeight u p :=
    match (outTargets u)[p.val]? with
    | none => 0
    | some v => M u v
  outPort_eq_some_iff u p v q := by
    rw [listPortLookup_eq_some_iff hin_len (fun a b h => (hmem_iff a b).mp h),
      listPortLookup_eq_some_iff hout_len (fun a b h => (hmem_iff b a).mpr h)]
    constructor
    · rintro ⟨hout, hq⟩
      have hv_mem : v ∈ outTargets u := List.mem_of_getElem? hout
      have hu_mem : u ∈ inSources v := (hmem_iff u v).mp hv_mem
      have hq_lt : (inSources v).idxOf u < (inSources v).length :=
        List.idxOf_lt_length_of_mem hu_mem
      obtain ⟨hp_lt, hp_eq⟩ := List.getElem?_eq_some_iff.mp hout
      refine ⟨?_, ?_⟩
      · rw [hq, List.getElem?_eq_getElem hq_lt, List.getElem_idxOf hq_lt]
      · rw [← hp_eq]
        exact ((hout_nodup u).idxOf_getElem p.val hp_lt).symm
    · rintro ⟨hin, hp⟩
      have hu_mem : u ∈ inSources v := List.mem_of_getElem? hin
      have hv_mem : v ∈ outTargets u := (hmem_iff u v).mpr hu_mem
      have hp_lt : (outTargets u).idxOf v < (outTargets u).length :=
        List.idxOf_lt_length_of_mem hv_mem
      obtain ⟨hq_lt, hq_eq⟩ := List.getElem?_eq_some_iff.mp hin
      refine ⟨?_, ?_⟩
      · rw [hp, List.getElem?_eq_getElem hp_lt, List.getElem_idxOf hp_lt]
      · rw [← hq_eq]
        exact ((hin_nodup v).idxOf_getElem q.val hq_lt).symm
  outPort_target_injective u {p₁ p₂ v q₁ q₂} h₁ h₂ := by
    obtain ⟨hg₁, -⟩ :=
      (listPortLookup_eq_some_iff hin_len (fun a b h => (hmem_iff a b).mp h) u p₁.val v q₁).mp h₁
    obtain ⟨hg₂, -⟩ :=
      (listPortLookup_eq_some_iff hin_len (fun a b h => (hmem_iff a b).mp h) u p₂.val v q₂).mp h₂
    obtain ⟨hp₁, he₁⟩ := List.getElem?_eq_some_iff.mp hg₁
    obtain ⟨hp₂, he₂⟩ := List.getElem?_eq_some_iff.mp hg₂
    apply Fin.ext
    exact (List.Nodup.getElem_inj_iff (hout_nodup u)).mp (he₁.trans he₂.symm)
  outWeight_eq_zero_of_none u p h := by
    have hg :=
      (listPortLookup_eq_none_iff hin_len (fun a b h => (hmem_iff a b).mp h) u p.val).mp h
    rw [hg]
  outWeight_eq_entry {u p v q} h := by
    obtain ⟨hg, -⟩ :=
      (listPortLookup_eq_some_iff hin_len (fun a b h => (hmem_iff a b).mp h) u p.val v q).mp h
    rw [hg]
  exists_outPort_of_ne_zero {u v} hne := by
    have hv : v ∈ outTargets u := hne_zero hne
    have hp_lt : (outTargets u).idxOf v < (outTargets u).length := List.idxOf_lt_length_of_mem hv
    let p : Fin dOut := ⟨(outTargets u).idxOf v, hp_lt.trans_le (hout_len u)⟩
    let q : Fin dIn := ⟨(inSources v).idxOf u,
      (List.idxOf_lt_length_of_mem ((hmem_iff u v).mp hv)).trans_le (hin_len v)⟩
    refine ⟨p, q,
      (listPortLookup_eq_some_iff hin_len (fun a b h => (hmem_iff a b).mp h) u p.val v q).mpr
        ⟨?_, rfl⟩⟩
    rw [List.getElem?_eq_getElem hp_lt, List.getElem_idxOf hp_lt]

/-- Characterization of `(ofLists ...).outPort u p = some (v, q)`. -/
theorem ofLists_outPort_eq_some_iff (M : Matrix V V R) (dOut dIn : ℕ)
    (outTargets : V → List V) (inSources : V → List V)
    (hout_nodup : ∀ u, (outTargets u).Nodup)
    (hin_nodup : ∀ v, (inSources v).Nodup)
    (hout_len : ∀ u, (outTargets u).length ≤ dOut)
    (hin_len : ∀ v, (inSources v).length ≤ dIn)
    (hmem_iff : ∀ u v, v ∈ outTargets u ↔ u ∈ inSources v)
    (hne_zero : ∀ {u v}, M u v ≠ 0 → v ∈ outTargets u)
    (u : V) (p : Fin dOut) (v : V) (q : Fin dIn) :
    (ofLists M dOut dIn outTargets inSources hout_nodup hin_nodup hout_len hin_len hmem_iff
      hne_zero).outPort u p = some (v, q) ↔
      (outTargets u)[p.val]? = some v ∧ q.val = (inSources v).idxOf u :=
  listPortLookup_eq_some_iff hin_len (fun a b h => (hmem_iff a b).mp h) u p.val v q

/-- Characterization of `(ofLists ...).outPort u p = none`. -/
theorem ofLists_outPort_eq_none_iff (M : Matrix V V R) (dOut dIn : ℕ)
    (outTargets : V → List V) (inSources : V → List V)
    (hout_nodup : ∀ u, (outTargets u).Nodup)
    (hin_nodup : ∀ v, (inSources v).Nodup)
    (hout_len : ∀ u, (outTargets u).length ≤ dOut)
    (hin_len : ∀ v, (inSources v).length ≤ dIn)
    (hmem_iff : ∀ u v, v ∈ outTargets u ↔ u ∈ inSources v)
    (hne_zero : ∀ {u v}, M u v ≠ 0 → v ∈ outTargets u)
    (u : V) (p : Fin dOut) :
    (ofLists M dOut dIn outTargets inSources hout_nodup hin_nodup hout_len hin_len hmem_iff
      hne_zero).outPort u p = none ↔ (outTargets u)[p.val]? = none :=
  listPortLookup_eq_none_iff hin_len (fun a b h => (hmem_iff a b).mp h) u p.val

/-- Characterization of `(ofLists ...).inPort v q = some (u, p)`. -/
theorem ofLists_inPort_eq_some_iff (M : Matrix V V R) (dOut dIn : ℕ)
    (outTargets : V → List V) (inSources : V → List V)
    (hout_nodup : ∀ u, (outTargets u).Nodup)
    (hin_nodup : ∀ v, (inSources v).Nodup)
    (hout_len : ∀ u, (outTargets u).length ≤ dOut)
    (hin_len : ∀ v, (inSources v).length ≤ dIn)
    (hmem_iff : ∀ u v, v ∈ outTargets u ↔ u ∈ inSources v)
    (hne_zero : ∀ {u v}, M u v ≠ 0 → v ∈ outTargets u)
    (v : V) (q : Fin dIn) (u : V) (p : Fin dOut) :
    (ofLists M dOut dIn outTargets inSources hout_nodup hin_nodup hout_len hin_len hmem_iff
      hne_zero).inPort v q = some (u, p) ↔
      (inSources v)[q.val]? = some u ∧ p.val = (outTargets u).idxOf v :=
  listPortLookup_eq_some_iff hout_len (fun a b h => (hmem_iff b a).mpr h) v q.val u p

/-- Characterization of `(ofLists ...).inPort v q = none`. -/
theorem ofLists_inPort_eq_none_iff (M : Matrix V V R) (dOut dIn : ℕ)
    (outTargets : V → List V) (inSources : V → List V)
    (hout_nodup : ∀ u, (outTargets u).Nodup)
    (hin_nodup : ∀ v, (inSources v).Nodup)
    (hout_len : ∀ u, (outTargets u).length ≤ dOut)
    (hin_len : ∀ v, (inSources v).length ≤ dIn)
    (hmem_iff : ∀ u v, v ∈ outTargets u ↔ u ∈ inSources v)
    (hne_zero : ∀ {u v}, M u v ≠ 0 → v ∈ outTargets u)
    (v : V) (q : Fin dIn) :
    (ofLists M dOut dIn outTargets inSources hout_nodup hin_nodup hout_len hin_len hmem_iff
      hne_zero).inPort v q = none ↔ (inSources v)[q.val]? = none :=
  listPortLookup_eq_none_iff hout_len (fun a b h => (hmem_iff b a).mpr h) v q.val

/-- Explicit value of `(ofLists ...).outWeight u p`. -/
theorem ofLists_outWeight_apply (M : Matrix V V R) (dOut dIn : ℕ)
    (outTargets : V → List V) (inSources : V → List V)
    (hout_nodup : ∀ u, (outTargets u).Nodup)
    (hin_nodup : ∀ v, (inSources v).Nodup)
    (hout_len : ∀ u, (outTargets u).length ≤ dOut)
    (hin_len : ∀ v, (inSources v).length ≤ dIn)
    (hmem_iff : ∀ u v, v ∈ outTargets u ↔ u ∈ inSources v)
    (hne_zero : ∀ {u v}, M u v ≠ 0 → v ∈ outTargets u)
    (u : V) (p : Fin dOut) :
    (ofLists M dOut dIn outTargets inSources hout_nodup hin_nodup hout_len hin_len hmem_iff
      hne_zero).outWeight u p =
      match (outTargets u)[p.val]? with
      | none => 0
      | some v => M u v := rfl

end OfLists

section FinTimeLayer

variable {n : ℕ} {R : Type*} [Zero R] {P : Matrix (Fin n) (Fin n) R} {dOut dIn : ℕ}

private theorem divNat_symm_toLex (T n : ℕ) (i : Fin (T + 1)) (v : Fin n) :
    (((timeLayerEquiv T n).symm (toLex (i, v))).divNat) = i := by
  have h := timeLayerEquiv_apply T n ((timeLayerEquiv T n).symm (toLex (i, v)))
  rw [Equiv.apply_symm_apply] at h
  exact (Prod.mk.inj (toLex.injective h)).1.symm

private theorem modNat_symm_toLex (T n : ℕ) (i : Fin (T + 1)) (v : Fin n) :
    (((timeLayerEquiv T n).symm (toLex (i, v))).modNat) = v := by
  have h := timeLayerEquiv_apply T n ((timeLayerEquiv T n).symm (toLex (i, v)))
  rw [Equiv.apply_symm_apply] at h
  exact (Prod.mk.inj (toLex.injective h)).2.symm

private theorem val_symm_toLex (T n : ℕ) (i : Fin (T + 1)) (v : Fin n) :
    ((timeLayerEquiv T n).symm (toLex (i, v))).val = i.val * n + v.val := by
  have h := timeLayerEquiv_val T n ((timeLayerEquiv T n).symm (toLex (i, v)))
  rw [Equiv.apply_symm_apply] at h
  dsimp only [ofLex_toLex] at h
  calc
    ((timeLayerEquiv T n).symm (toLex (i, v))).val = v.val + n * i.val := h
    _ = i.val * n + v.val := by ring

private theorem val_div_symm_toLex (T n : ℕ) (i : Fin (T + 1)) (v : Fin n) :
    ((timeLayerEquiv T n).symm (toLex (i, v))).val / n = i.val := by
  change (((timeLayerEquiv T n).symm (toLex (i, v))).divNat).val = i.val
  rw [divNat_symm_toLex]

/-- Lift a paired-port structure on `P : Matrix (Fin n) (Fin n) R` to the consecutive-index
time-layered matrix `Matrix.finTimeLayer T P` on `Fin ((T + 1) * n)`, preserving port degrees
`dOut` and `dIn`. -/
@[expose] def finTimeLayer (hp : PairedPorts P dOut dIn) (T : ℕ) :
    PairedPorts (Matrix.finTimeLayer T P) dOut dIn where
  outPort a p :=
    if h : a.val / n < T then
      match hp.outPort a.modNat p with
      | none => none
      | some (v, q) =>
        some ((timeLayerEquiv T n).symm (toLex (⟨a.val / n + 1, Nat.succ_lt_succ h⟩, v)), q)
    else none
  inPort b q :=
    if _ : 0 < b.val / n then
      match hp.inPort b.modNat q with
      | none => none
      | some (u, p) =>
        some ((timeLayerEquiv T n).symm
          (toLex (⟨b.val / n - 1, lt_of_le_of_lt (Nat.pred_le _) b.divNat.isLt⟩, u)), p)
    else none
  outWeight a p :=
    if a.val / n < T then hp.outWeight a.modNat p else 0
  outPort_eq_some_iff a p b q := by
    constructor
    · intro hout
      by_cases ha : a.val / n < T
      · rw [dite_eq_left ha] at hout
        cases hg : hp.outPort a.modNat p with
        | none =>
          rw [hg] at hout
          cases hout
        | some vq =>
          obtain ⟨v, q'⟩ := vq
          rw [hg] at hout
          obtain ⟨hb_eq, hq_eq⟩ := Prod.mk.inj (Option.some.inj hout)
          subst hb_eq
          subst q'
          let iNext : Fin (T + 1) := ⟨a.val / n + 1, Nat.succ_lt_succ ha⟩
          have hdiv_val : ((timeLayerEquiv T n).symm (toLex (iNext, v))).val / n =
              a.val / n + 1 := val_div_symm_toLex T n iNext v
          have hmod : ((timeLayerEquiv T n).symm (toLex (iNext, v))).modNat = v :=
            modNat_symm_toLex T n iNext v
          have hpos : 0 < ((timeLayerEquiv T n).symm (toLex (iNext, v))).val / n := by
            rw [hdiv_val]; exact Nat.succ_pos _
          have hin_base : hp.inPort v q = some (a.modNat, p) :=
            (hp.outPort_eq_some_iff a.modNat p v q).mp hg
          rw [dite_eq_left hpos, hmod, hin_base]
          simp only [Option.some.injEq, Prod.mk.injEq, and_true]
          have hidx : (⟨((timeLayerEquiv T n).symm (toLex (iNext, v))).val / n - 1,
              lt_of_le_of_lt (Nat.pred_le _)
                (((timeLayerEquiv T n).symm (toLex (iNext, v))).divNat).isLt⟩ : Fin (T + 1)) =
              a.divNat := by
            apply Fin.ext
            change ((timeLayerEquiv T n).symm (toLex (iNext, v))).val / n - 1 = a.val / n
            rw [hdiv_val]
            omega
          rw [hidx, ← timeLayerEquiv_apply T n a, Equiv.symm_apply_apply]
      · rw [dite_eq_right ha] at hout
        cases hout
    · intro hin
      by_cases hb : 0 < b.val / n
      · rw [dite_eq_left hb] at hin
        cases hg : hp.inPort b.modNat q with
        | none =>
          rw [hg] at hin
          cases hin
        | some up =>
          obtain ⟨u, p'⟩ := up
          rw [hg] at hin
          obtain ⟨ha_eq, hp_eq⟩ := Prod.mk.inj (Option.some.inj hin)
          subst ha_eq
          subst p'
          let iPred : Fin (T + 1) :=
            ⟨b.val / n - 1, lt_of_le_of_lt (Nat.pred_le _) b.divNat.isLt⟩
          have hdiv_val : ((timeLayerEquiv T n).symm (toLex (iPred, u))).val / n =
              b.val / n - 1 := val_div_symm_toLex T n iPred u
          have hmod : ((timeLayerEquiv T n).symm (toLex (iPred, u))).modNat = u :=
            modNat_symm_toLex T n iPred u
          have hb_lt : b.val / n < T + 1 := b.divNat.isLt
          have hlt : ((timeLayerEquiv T n).symm (toLex (iPred, u))).val / n < T := by
            rw [hdiv_val]; omega
          have hout_base : hp.outPort u p = some (b.modNat, q) :=
            (hp.outPort_eq_some_iff u p b.modNat q).mpr hg
          rw [dite_eq_left hlt, hmod, hout_base]
          simp only [Option.some.injEq, Prod.mk.injEq, and_true]
          have hidx : (⟨((timeLayerEquiv T n).symm (toLex (iPred, u))).val / n + 1,
              Nat.succ_lt_succ hlt⟩ : Fin (T + 1)) = b.divNat := by
            apply Fin.ext
            change ((timeLayerEquiv T n).symm (toLex (iPred, u))).val / n + 1 = b.val / n
            rw [hdiv_val]
            omega
          rw [hidx, ← timeLayerEquiv_apply T n b, Equiv.symm_apply_apply]
      · rw [dite_eq_right hb] at hin
        cases hin
  outPort_target_injective a {p₁ p₂ b q₁ q₂} h₁ h₂ := by
    by_cases ha : a.val / n < T
    · rw [dite_eq_left ha] at h₁ h₂
      cases hg₁ : hp.outPort a.modNat p₁ with
      | none => rw [hg₁] at h₁; cases h₁
      | some vq₁ =>
        cases hg₂ : hp.outPort a.modNat p₂ with
        | none => rw [hg₂] at h₂; cases h₂
        | some vq₂ =>
          obtain ⟨v₁, q₁'⟩ := vq₁
          obtain ⟨v₂, q₂'⟩ := vq₂
          rw [hg₁] at h₁
          rw [hg₂] at h₂
          have hsymm_eq :=
            (Prod.mk.inj (Option.some.inj h₁)).1.trans (Prod.mk.inj (Option.some.inj h₂)).1.symm
          have hv : v₁ = v₂ :=
            (Prod.mk.inj (toLex.injective ((timeLayerEquiv T n).symm.injective hsymm_eq))).2
          subst hv
          exact hp.outPort_target_injective a.modNat hg₁ hg₂
    · rw [dite_eq_right ha] at h₁
      cases h₁
  outWeight_eq_zero_of_none a p h := by
    by_cases ha : a.val / n < T
    · rw [dite_eq_left ha] at h
      rw [ite_eq_left ha]
      cases hg : hp.outPort a.modNat p with
      | none => exact hp.outWeight_eq_zero_of_none a.modNat p hg
      | some vq => rw [hg] at h; cases h
    · exact ite_eq_right ha
  outWeight_eq_entry {a p b q} h := by
    by_cases ha : a.val / n < T
    · rw [dite_eq_left ha] at h
      rw [ite_eq_left ha]
      cases hg : hp.outPort a.modNat p with
      | none => rw [hg] at h; cases h
      | some vq =>
        obtain ⟨v, q'⟩ := vq
        rw [hg] at h
        obtain ⟨hb_eq, -⟩ := Prod.mk.inj (Option.some.inj h)
        subst hb_eq
        let iNext : Fin (T + 1) := ⟨a.val / n + 1, Nat.succ_lt_succ ha⟩
        have hclock : a.val / n + 1 =
            ((timeLayerEquiv T n).symm (toLex (iNext, v))).val / n :=
          (val_div_symm_toLex T n iNext v).symm
        have hmod : ((timeLayerEquiv T n).symm (toLex (iNext, v))).modNat = v :=
          modNat_symm_toLex T n iNext v
        rw [Matrix.finTimeLayer_apply, ite_eq_left hclock, hmod]
        exact hp.outWeight_eq_entry hg
    · rw [dite_eq_right ha] at h
      cases h
  exists_outPort_of_ne_zero {a b} hne := by
    rw [Matrix.finTimeLayer_apply] at hne
    split_ifs at hne with hclock
    · have hb_lt : b.val / n < T + 1 := b.divNat.isLt
      have ha : a.val / n < T := by omega
      obtain ⟨p, q, hpq⟩ := hp.exists_outPort_of_ne_zero hne
      refine ⟨p, q, ?_⟩
      rw [dite_eq_left ha, hpq]
      simp only [Option.some.injEq, Prod.mk.injEq, and_true]
      have hdiv : (⟨a.val / n + 1, Nat.succ_lt_succ ha⟩ : Fin (T + 1)) = b.divNat := by
        apply Fin.ext
        exact hclock
      rw [hdiv, ← timeLayerEquiv_apply T n b, Equiv.symm_apply_apply]
    · exact absurd rfl hne

/-- Explicit arithmetic value of `(hp.finTimeLayer T).outPort a p` on natural-number components. -/
theorem finTimeLayer_outPort_val (hp : PairedPorts P dOut dIn) (T : ℕ)
    (a : Fin ((T + 1) * n)) (p : Fin dOut) :
    ((hp.finTimeLayer T).outPort a p).map (fun bq => (bq.1.val, bq.2)) =
      if a.val / n < T then
        match hp.outPort a.modNat p with
        | none => none
        | some (v, q) => some ((a.val / n + 1) * n + v.val, q)
      else none := by
  dsimp only [finTimeLayer]
  by_cases ha : a.val / n < T
  · rw [dite_eq_left ha, ite_eq_left ha]
    cases hp.outPort a.modNat p with
    | none => rfl
    | some vq =>
      obtain ⟨v, q⟩ := vq
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      exact val_symm_toLex T n ⟨a.val / n + 1, Nat.succ_lt_succ ha⟩ v
  · rw [dite_eq_right ha, ite_eq_right ha]
    rfl

/-- Explicit arithmetic value of `(hp.finTimeLayer T).inPort b q` on natural-number components. -/
theorem finTimeLayer_inPort_val (hp : PairedPorts P dOut dIn) (T : ℕ)
    (b : Fin ((T + 1) * n)) (q : Fin dIn) :
    ((hp.finTimeLayer T).inPort b q).map (fun up => (up.1.val, up.2)) =
      if 0 < b.val / n then
        match hp.inPort b.modNat q with
        | none => none
        | some (u, p) => some ((b.val / n - 1) * n + u.val, p)
      else none := by
  dsimp only [finTimeLayer]
  by_cases hb : 0 < b.val / n
  · rw [dite_eq_left hb, ite_eq_left hb]
    cases hp.inPort b.modNat q with
    | none => rfl
    | some up =>
      obtain ⟨u, p⟩ := up
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      exact val_symm_toLex T n
        ⟨b.val / n - 1, lt_of_le_of_lt (Nat.pred_le _) b.divNat.isLt⟩ u
  · rw [dite_eq_right hb, ite_eq_right hb]
    rfl

/-- Explicit value of `(hp.finTimeLayer T).outWeight a p`. -/
theorem finTimeLayer_outWeight_apply (hp : PairedPorts P dOut dIn) (T : ℕ)
    (a : Fin ((T + 1) * n)) (p : Fin dOut) :
    (hp.finTimeLayer T).outWeight a p =
      if a.val / n < T then hp.outWeight a.modNat p else 0 := rfl

end FinTimeLayer

end PairedPorts

end Matrix
