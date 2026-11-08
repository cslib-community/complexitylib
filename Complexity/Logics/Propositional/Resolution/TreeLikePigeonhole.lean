/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Pigeonhole
public import Complexity.Logics.Propositional.Resolution.ProverDelayer
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Tree-like resolution lower bound for the pigeonhole principle

Every tree-like resolution refutation of the weak pigeonhole formula `PHP^m_n`, `m > n`, has at
least `(n + 1 - h) ^ h` nodes for every `h`, a bound that is nontrivial for `h ≤ n`
(`Cslib.Logic.PL.CNF.Derivation.pow_le_size_pigeonhole`). At `h = n / 2` this is the
`(n / 2 + 1) ^ (n / 2) = 2 ^ Ω(n log n)` bound of Beyersdorff, Galesi and Lauria
[BeyersdorffGalesiLauria2010, Theorem 2]
(`Cslib.Logic.PL.CNF.Derivation.pow_half_le_size_pigeonhole`), which they obtain from an asymmetric
Prover–Delayer game; the bound `2 ^ Θ(n log n)` was first proved by Iwama and Miyazaki
[IwamaMiyazaki1999] and by Dantchev and Riis [DantchevRiis2001]. It improves on the bound
`2 ^ (n / 24)` that Haken's theorem gives for `m = n + 1`
(`Cslib.Logic.PL.CNF.Derivation.two_pow_le_size_pigeonhole`), and holds for every number of
pigeons. The same bound applies to DPLL search trees: a decision tree finding a falsified clause of
`PHP^m_n` has more than `(n + 1 - h) ^ h / 2` leaves
(`Cslib.Logic.PL.CNF.pow_lt_two_mul_leafCount_pigeonhole`).

**The potential.** Delayer keeps the positive literals of the partial assignment `ρ` a partial
matching of pigeons to holes. For an unmatched pigeon `i`, let `p_i` be the number of holes that
are unoccupied but excluded for `i` by `ρ`, and `d_i = n + 1 - h - p_i` (truncated at `0`). With
`k` matched pigeons, the potential of `ρ` is the least product `∏_{i ∈ U} d_i` over sets `U` of
`h - k` unmatched pigeons; it is `(n + 1 - h) ^ h` at the empty assignment. It splits at every
unset variable `(i, j)`
(`Cslib.Logic.PL.CNF.Derivation.potential_le_size`): if `i` is matched or `j` occupied, setting
`(i, j)` to `false` changes nothing; otherwise setting it to `false` lowers `d_i` by one and setting
it to `true` matches `i`, which removes the factor `d_i` and can only raise the other `d`'s. A
pigeon clause is falsified only when the pigeon is unmatched and every unoccupied hole is excluded
for it, so either `h` pigeons are matched (potential `1`) or `d_i = 0` (potential `0`); a hole
clause is never falsified by a matching. Their theorem uses `h = n / 2` and assigns a pigeon to a
hole once it has `n / 2` excluded holes; here pigeons with `d_i = 0` are left to the Prover, which
removes that rule. Informally, choosing `h ≈ n - n / ln n` gives `n ^ ((1 - o(1)) n)`, whose
logarithm has the same leading term `n log n` as the size `≈ n!` of the refutation that places the
pigeons one at a time; only the explicit bound for each `h` is formalized.

## Main results

* `Cslib.Logic.PL.CNF.Derivation.pow_le_size_pigeonhole`: `(n + 1 - h) ^ h` nodes for every `h`.
* `Cslib.Logic.PL.CNF.Derivation.pow_half_le_size_pigeonhole`: `(n / 2 + 1) ^ (n / 2)` nodes
  [BeyersdorffGalesiLauria2010, Theorem 2].
* `Cslib.Logic.PL.CNF.pow_lt_two_mul_leafCount_pigeonhole`: the same bound for DPLL search trees.

## References

* [O. Beyersdorff, N. Galesi, M. Lauria, *A lower bound for the pigeonhole principle in tree-like
  Resolution by asymmetric Prover–Delayer games*][BeyersdorffGalesiLauria2010]
* [S. Dantchev, S. Riis, *Tree resolution proofs of the weak pigeon-hole
  principle*][DantchevRiis2001]
* [K. Iwama, S. Miyazaki, *Tree-like resolution is superpolynomially slower than dag-like
  resolution for the pigeonhole principle*][IwamaMiyazaki1999]
-/

public section

namespace Cslib.Logic.PL

namespace CNF

open Finset

variable {m n : ℕ}

/-! ### Partial matchings and the potential -/

/-- The positive literals of `ρ` form a partial matching: no pigeon sits in two holes and no hole
holds two pigeons. -/
private def IsMatching (ρ : Fin m × Fin n → Option Bool) : Prop :=
  (∀ i j j', ρ (i, j) = some true → ρ (i, j') = some true → j = j') ∧
    ∀ i i' j, ρ (i, j) = some true → ρ (i', j) = some true → i = i'

/-- The pigeons that `ρ` puts in a hole. -/
private def matched (ρ : Fin m × Fin n → Option Bool) : Finset (Fin m) :=
  {i | ∃ j, ρ (i, j) = some true}

/-- The holes that `ρ` puts a pigeon in. -/
private def occupied (ρ : Fin m × Fin n → Option Bool) : Finset (Fin n) :=
  {j | ∃ i, ρ (i, j) = some true}

/-- The unoccupied holes that `ρ` excludes for pigeon `i`. -/
private def excluded (ρ : Fin m × Fin n → Option Bool) (i : Fin m) : Finset (Fin n) :=
  {j | ρ (i, j) = some false ∧ j ∉ occupied ρ}

/-- The weight `d_i = n + 1 - h - p_i` of pigeon `i`, truncated at `0`. -/
private def weight (h : ℕ) (ρ : Fin m × Fin n → Option Bool) (i : Fin m) : ℕ :=
  n + 1 - h - #(excluded ρ i)

/-- The products of weights over sets of `h - k` unmatched pigeons, `k` the number of matched
pigeons. -/
private def products (h : ℕ) (ρ : Fin m × Fin n → Option Bool) : Set ℕ :=
  {x | ∃ U ⊆ (matched ρ)ᶜ, #U = h - #(matched ρ) ∧ x = ∏ i ∈ U, weight h ρ i}

/-- The least product of weights over sets of `h - k` unmatched pigeons. -/
private noncomputable def potential (h : ℕ) (ρ : Fin m × Fin n → Option Bool) : ℕ :=
  sInf (products h ρ)

open Classical in
/-- The potential on partial matchings, and `0` elsewhere. -/
private noncomputable def μ (h : ℕ) (ρ : Fin m × Fin n → Option Bool) : ℕ :=
  if IsMatching ρ then potential h ρ else 0

private theorem mem_matched {ρ : Fin m × Fin n → Option Bool} {i : Fin m} :
    i ∈ matched ρ ↔ ∃ j, ρ (i, j) = some true := by
  simp [matched]

private theorem mem_occupied {ρ : Fin m × Fin n → Option Bool} {j : Fin n} :
    j ∈ occupied ρ ↔ ∃ i, ρ (i, j) = some true := by
  simp [occupied]

private theorem mem_excluded {ρ : Fin m × Fin n → Option Bool} {i : Fin m} {j : Fin n} :
    j ∈ excluded ρ i ↔ ρ (i, j) = some false ∧ j ∉ occupied ρ := by
  simp [excluded]

private theorem μ_of_isMatching {h : ℕ} {ρ : Fin m × Fin n → Option Bool} (hρ : IsMatching ρ) :
    μ h ρ = potential h ρ := by
  simp [μ, hρ]

private theorem μ_of_not_isMatching {h : ℕ} {ρ : Fin m × Fin n → Option Bool}
    (hρ : ¬ IsMatching ρ) : μ h ρ = 0 := by
  simp [μ, hρ]

private theorem potential_le {h : ℕ} {ρ : Fin m × Fin n → Option Bool} {U : Finset (Fin m)}
    (hU : U ⊆ (matched ρ)ᶜ) (hcard : #U = h - #(matched ρ)) :
    potential h ρ ≤ ∏ i ∈ U, weight h ρ i :=
  Nat.sInf_le ⟨U, hU, hcard, rfl⟩

/-- With `h ≤ m`, the potential is a product of weights over some set of `h - k` unmatched
pigeons. -/
private theorem exists_potential_eq {h : ℕ} (ρ : Fin m × Fin n → Option Bool) (hh : h ≤ m) :
    ∃ U ⊆ (matched ρ)ᶜ, #U = h - #(matched ρ) ∧ potential h ρ = ∏ i ∈ U, weight h ρ i := by
  have hne : (products h ρ).Nonempty := by
    obtain ⟨U, hU, hcard⟩ := exists_subset_card_eq (s := (matched ρ)ᶜ) (n := h - #(matched ρ))
      (by rw [card_compl, Fintype.card_fin]; omega)
    exact ⟨_, U, hU, hcard, rfl⟩
  exact Nat.sInf_mem hne

/-- Potentials agree when the matched pigeons agree and the weights of unmatched pigeons agree. -/
private theorem potential_congr {h : ℕ} {ρ ρ' : Fin m × Fin n → Option Bool}
    (hm : matched ρ' = matched ρ) (hw : ∀ i ∉ matched ρ, weight h ρ' i = weight h ρ i) :
    potential h ρ' = potential h ρ := by
  unfold potential products
  congr 1
  ext x
  rw [hm]
  refine exists_congr fun U => and_congr_right fun hU => and_congr_right fun _ => ?_
  rw [prod_congr rfl fun i hi => hw i (mem_compl.1 (hU hi))]

/-! ### The empty assignment -/

private theorem isMatching_none : IsMatching (fun _ : Fin m × Fin n => none) :=
  ⟨fun _ _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩

private theorem potential_none {h : ℕ} (hh : h ≤ m) :
    potential h (fun _ : Fin m × Fin n => none) = (n + 1 - h) ^ h := by
  have hm : matched (fun _ : Fin m × Fin n => none) = ∅ := by
    ext i
    simp [mem_matched]
  have hw : ∀ i, weight h (fun _ : Fin m × Fin n => none) i = n + 1 - h := fun i => by
    simp [weight, excluded]
  obtain ⟨U, -, hcard, heq⟩ := exists_potential_eq (n := n) (h := h) (fun _ => none) hh
  rw [heq, prod_congr rfl fun i _ => hw i, prod_const, hcard, hm, card_empty, Nat.sub_zero]

/-! ### Falsified clauses -/

/-- The occupied holes are at most the matched pigeons in a partial matching. -/
private theorem card_occupied_le {ρ : Fin m × Fin n → Option Bool} (hρ : IsMatching ρ) :
    #(occupied ρ) ≤ #(matched ρ) := by
  refine card_le_card_of_forall_subsingleton (r := fun j i => ρ (i, j) = some true) ?_ ?_
  · intro j hj
    obtain ⟨i, hi⟩ := mem_occupied.1 hj
    exact ⟨i, mem_matched.2 ⟨j, hi⟩, hi⟩
  · intro i _ j₁ hj₁ j₂ hj₂
    exact hρ.1 i j₁ j₂ hj₁.2 hj₂.2

/-- **A partial assignment falsifying a clause of `PHP^m_n` has potential at most `1`.** -/
private theorem μ_le_one {h : ℕ} (hhn : h ≤ n) (hnm : n < m) (ρ : Fin m × Fin n → Option Bool)
    (c : Clause (Fin m × Fin n)) (hc : c ∈ pigeonhole m n) (hρc : Clause.FalsifiedBy ρ c) :
    μ h ρ ≤ 1 := by
  by_cases hρ : IsMatching ρ
  swap
  · rw [μ_of_not_isMatching hρ]
    exact Nat.zero_le _
  rw [μ_of_isMatching hρ]
  rcases mem_pigeonhole.1 hc with ⟨i, rfl⟩ | ⟨i, i', j, hii', rfl⟩
  · -- every hole is excluded for pigeon `i` or occupied
    have hfalse : ∀ j, ρ (i, j) = some false := fun j =>
      hρc ((i, j), true) (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩)
    have hi : i ∉ matched ρ := by
      simp [mem_matched, hfalse]
    have hex : excluded ρ i = (occupied ρ)ᶜ := by
      ext j
      simp [mem_excluded, hfalse]
    have hocc := card_occupied_le hρ
    by_cases hk : h ≤ #(matched ρ)
    · refine (potential_le (U := ∅) (empty_subset _) ?_).trans_eq prod_empty
      rw [card_empty]
      omega
    · obtain ⟨U, hiU, hU, hcard⟩ := exists_subsuperset_card_eq
        (s := {i}) (t := (matched ρ)ᶜ) (n := h - #(matched ρ))
        (singleton_subset_iff.2 (mem_compl.2 hi)) (by rw [card_singleton]; omega)
        (by rw [card_compl, Fintype.card_fin]; omega)
      have hzero : weight h ρ i = 0 := by
        rw [weight, hex, card_compl, Fintype.card_fin]
        omega
      have := potential_le hU hcard
      rw [prod_eq_zero (singleton_subset_iff.1 hiU) hzero] at this
      omega
  · -- a matching falsifies no hole clause
    have h₁ : ρ (i, j) = some true := hρc ((i, j), false) (by simp [holeClause])
    have h₂ : ρ (i', j) = some true := hρc ((i', j), false) (by simp [holeClause])
    exact absurd (hρ.2 i i' j h₁ h₂) (ne_of_lt hii')

/-! ### Setting one variable -/

open Function

section Update

variable {ρ : Fin m × Fin n → Option Bool} {i : Fin m} {j : Fin n}

private theorem update_eq_some_true_iff (hv : ρ (i, j) = none) (b : Bool) (a : Fin m)
    (c : Fin n) :
    update ρ (i, j) (some b) (a, c) = some true ↔
      ((a, c) = (i, j) ∧ b = true) ∨ ρ (a, c) = some true := by
  by_cases he : (a, c) = (i, j)
  · rw [he, update_self, hv]
    simp
  · rw [update_of_ne he]
    simp [he]

private theorem isMatching_update_false (hρ : IsMatching ρ) (hv : ρ (i, j) = none) :
    IsMatching (update ρ (i, j) (some false)) := by
  constructor
  · intro a c c' h₁ h₂
    simp only [update_eq_some_true_iff hv, Bool.false_eq_true, and_false, false_or] at h₁ h₂
    exact hρ.1 a c c' h₁ h₂
  · intro a a' c h₁ h₂
    simp only [update_eq_some_true_iff hv, Bool.false_eq_true, and_false, false_or] at h₁ h₂
    exact hρ.2 a a' c h₁ h₂

private theorem matched_update_false (hv : ρ (i, j) = none) :
    matched (update ρ (i, j) (some false)) = matched ρ := by
  ext a
  simp only [mem_matched, update_eq_some_true_iff hv, Bool.false_eq_true, and_false, false_or]

private theorem occupied_update_false (hv : ρ (i, j) = none) :
    occupied (update ρ (i, j) (some false)) = occupied ρ := by
  ext c
  simp only [mem_occupied, update_eq_some_true_iff hv, Bool.false_eq_true, and_false, false_or]

private theorem excluded_update_false_of_ne (hv : ρ (i, j) = none) {a : Fin m} (ha : a ≠ i) :
    excluded (update ρ (i, j) (some false)) a = excluded ρ a := by
  ext c
  have hne : (a, c) ≠ (i, j) := fun he => ha (Prod.ext_iff.1 he).1
  rw [mem_excluded, mem_excluded, occupied_update_false hv, update_of_ne hne]

private theorem excluded_update_false_self (hv : ρ (i, j) = none) :
    excluded (update ρ (i, j) (some false)) i =
      if j ∈ occupied ρ then excluded ρ i else insert j (excluded ρ i) := by
  ext c
  rw [mem_excluded, occupied_update_false hv]
  by_cases hc : c = j
  · subst hc
    split_ifs with hj <;> simp [mem_excluded, hv, hj]
  · have hne : (i, c) ≠ (i, j) := fun he => hc (Prod.ext_iff.1 he).2
    rw [update_of_ne hne]
    split_ifs <;> simp [mem_excluded, hc]

private theorem isMatching_update_true (hρ : IsMatching ρ) (hv : ρ (i, j) = none)
    (hi : i ∉ matched ρ) (hj : j ∉ occupied ρ) : IsMatching (update ρ (i, j) (some true)) := by
  constructor
  · intro a c c' h₁ h₂
    simp only [update_eq_some_true_iff hv, and_true] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact (Prod.ext_iff.1 h₁).2.trans (Prod.ext_iff.1 h₂).2.symm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₁
      exact absurd (mem_matched.2 ⟨c', h₂⟩) hi
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂
      exact absurd (mem_matched.2 ⟨c, h₁⟩) hi
    · exact hρ.1 a c c' h₁ h₂
  · intro a a' c h₁ h₂
    simp only [update_eq_some_true_iff hv, and_true] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact (Prod.ext_iff.1 h₁).1.trans (Prod.ext_iff.1 h₂).1.symm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₁
      exact absurd (mem_occupied.2 ⟨a', h₂⟩) hj
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂
      exact absurd (mem_occupied.2 ⟨a, h₁⟩) hj
    · exact hρ.2 a a' c h₁ h₂

private theorem matched_update_true (hv : ρ (i, j) = none) :
    matched (update ρ (i, j) (some true)) = insert i (matched ρ) := by
  ext a
  simp only [mem_matched, update_eq_some_true_iff hv, and_true, mem_insert, Prod.ext_iff]
  constructor
  · rintro ⟨c, ⟨rfl, -⟩ | hc⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨c, hc⟩
  · rintro (rfl | ⟨c, hc⟩)
    · exact ⟨j, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨c, Or.inr hc⟩

private theorem occupied_subset_update_true (hv : ρ (i, j) = none) :
    occupied ρ ⊆ occupied (update ρ (i, j) (some true)) := fun c hc => by
  obtain ⟨a, ha⟩ := mem_occupied.1 hc
  exact mem_occupied.2 ⟨a, (update_eq_some_true_iff hv true a c).2 (Or.inr ha)⟩

private theorem weight_le_update_true {h : ℕ} (hv : ρ (i, j) = none) {a : Fin m} (ha : a ≠ i) :
    weight h ρ a ≤ weight h (update ρ (i, j) (some true)) a := by
  have hsub : excluded (update ρ (i, j) (some true)) a ⊆ excluded ρ a := fun c hc => by
    have hne : (a, c) ≠ (i, j) := fun he => ha (Prod.ext_iff.1 he).1
    rw [mem_excluded, update_of_ne hne] at hc
    exact mem_excluded.2 ⟨hc.1, fun hco => hc.2 (occupied_subset_update_true hv hco)⟩
  have := card_le_card hsub
  unfold weight
  omega

end Update

/-! ### Splitting -/

/-- Splitting at a variable `(i, j)` with `i` unmatched and `j` unoccupied: setting it to `false`
lowers the weight of `i` by one, and setting it to `true` matches `i`. -/
private theorem potential_split {h : ℕ} (hhm : h ≤ m) {ρ : Fin m × Fin n → Option Bool}
    {i : Fin m} {j : Fin n} (hv : ρ (i, j) = none) (hi : i ∉ matched ρ) (hj : j ∉ occupied ρ) :
    potential h ρ ≤ potential h (update ρ (i, j) (some false)) +
      potential h (update ρ (i, j) (some true)) := by
  have hw₀i : weight h (update ρ (i, j) (some false)) i = weight h ρ i - 1 := by
    have hjex : j ∉ excluded ρ i := by
      simp [mem_excluded, hv]
    rw [weight, weight, excluded_update_false_self hv, ite_eq_right hj, card_insert_of_notMem hjex]
    omega
  have hw₀ : ∀ a, a ≠ i → weight h (update ρ (i, j) (some false)) a = weight h ρ a :=
    fun a ha => by rw [weight, weight, excluded_update_false_of_ne hv ha]
  obtain ⟨U₀, hU₀, hcard₀, heq₀⟩ := exists_potential_eq (update ρ (i, j) (some false)) hhm
  rw [matched_update_false hv] at hU₀ hcard₀
  by_cases hiU : i ∈ U₀
  swap
  · -- the weights on `U₀` are those of `ρ`
    refine le_add_right ((potential_le hU₀ hcard₀).trans_eq ?_)
    rw [heq₀]
    exact prod_congr rfl fun a ha => (hw₀ a fun he => hiU (he ▸ ha)).symm
  have hk : 1 ≤ h - #(matched ρ) := by
    have := card_pos.2 ⟨i, hiU⟩
    omega
  set P := ∏ a ∈ U₀.erase i, weight h ρ a with hP
  set D := weight h ρ i with hD
  -- `potential ρ ≤ D * P`
  have hle₁ : potential h ρ ≤ D * P := by
    refine (potential_le hU₀ hcard₀).trans_eq ?_
    rw [← mul_prod_erase U₀ _ hiU]
  -- `potential ρ₀ = (D - 1) * P`
  have heq₀' : potential h (update ρ (i, j) (some false)) = (D - 1) * P := by
    rw [heq₀, ← mul_prod_erase U₀ _ hiU, hw₀i]
    congr 1
    exact prod_congr rfl fun a ha => hw₀ a (ne_of_mem_erase ha)
  -- `potential ρ ≤ D * potential ρ₁`
  have hle₂ : potential h ρ ≤ D * potential h (update ρ (i, j) (some true)) := by
    obtain ⟨W, hW, hcardW, heqW⟩ := exists_potential_eq (update ρ (i, j) (some true)) hhm
    rw [matched_update_true hv] at hW hcardW
    have hiW : i ∉ W := fun hiW => mem_compl.1 (hW hiW) (mem_insert_self i _)
    have hW' : insert i W ⊆ (matched ρ)ᶜ := by
      intro a ha
      rcases mem_insert.1 ha with rfl | ha
      · exact mem_compl.2 hi
      · exact mem_compl.2 fun hm => mem_compl.1 (hW ha) (mem_insert_of_mem hm)
    have hcardW' : #(insert i W) = h - #(matched ρ) := by
      rw [card_insert_of_notMem hiW, hcardW, card_insert_of_notMem hi]
      omega
    refine (potential_le hW' hcardW').trans ?_
    rw [prod_insert hiW, heqW]
    exact Nat.mul_le_mul_left _ (prod_le_prod fun a ha =>
      weight_le_update_true hv fun he => hiW (he ▸ ha))
  rw [heq₀']
  rcases Nat.eq_zero_or_pos D with hD0 | hD0
  · rw [hD0, zero_mul] at hle₁
    omega
  obtain ⟨D', hD'⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  rw [hD', Nat.add_sub_cancel]
  rw [hD'] at hle₁ hle₂
  rcases le_total (potential h (update ρ (i, j) (some true))) P with hR | hR
  · calc potential h ρ ≤ (D' + 1) * potential h (update ρ (i, j) (some true)) := hle₂
      _ = D' * potential h (update ρ (i, j) (some true)) +
          potential h (update ρ (i, j) (some true)) := by ring
      _ ≤ D' * P + potential h (update ρ (i, j) (some true)) := by gcongr
  · calc potential h ρ ≤ (D' + 1) * P := hle₁
      _ = D' * P + P := by ring
      _ ≤ D' * P + potential h (update ρ (i, j) (some true)) := by gcongr

/-- **The potential splits at every unset variable.** -/
private theorem μ_split {h : ℕ} (hhm : h ≤ m) (ρ : Fin m × Fin n → Option Bool)
    (v : Fin m × Fin n) (hv : ρ v = none) :
    μ h ρ ≤ μ h (update ρ v (some false)) + μ h (update ρ v (some true)) := by
  by_cases hρ : IsMatching ρ
  swap
  · rw [μ_of_not_isMatching hρ]
    exact Nat.zero_le _
  obtain ⟨i, j⟩ := v
  rw [μ_of_isMatching hρ, μ_of_isMatching (isMatching_update_false hρ hv)]
  by_cases hfree : i ∈ matched ρ ∨ j ∈ occupied ρ
  · -- nothing changes
    refine le_add_right (le_of_eq (potential_congr (matched_update_false hv) fun a ha => ?_).symm)
    by_cases hai : a = i
    · subst hai
      rw [weight, weight, excluded_update_false_self hv, ite_eq_left (hfree.resolve_left ha)]
    · rw [weight, weight, excluded_update_false_of_ne hv hai]
  · simp only [not_or] at hfree
    rw [μ_of_isMatching (isMatching_update_true hρ hv hfree.1 hfree.2)]
    exact potential_split hhm hv hfree.1 hfree.2

/-! ### The lower bound -/

namespace Derivation

/-- **Tree-like resolution lower bound for the pigeonhole principle.** For `m > n` and every `h`,
every tree-like resolution refutation of `PHP^m_n` has at least `(n + 1 - h) ^ h` nodes (the bound
is `0` for `h > n`). This is the asymmetric Prover–Delayer argument of
[BeyersdorffGalesiLauria2010, Theorem 2] with the threshold `n / 2` replaced by `h`. -/
theorem pow_le_size_pigeonhole (h : ℕ) (hnm : n < m) (d : (pigeonhole m n).Derivation []) :
    (n + 1 - h) ^ h ≤ d.size := by
  by_cases hhn : h ≤ n
  swap
  · rw [Nat.sub_eq_zero_of_le (by omega), zero_pow (by omega)]
    exact Nat.zero_le _
  have hroot : μ h (fun _ : Fin m × Fin n => none) = (n + 1 - h) ^ h := by
    rw [μ_of_isMatching isMatching_none, potential_none (by omega)]
  rw [← hroot]
  exact potential_none_le_size (μ h) (μ_split (by omega)) (μ_le_one hhn hnm) d

/-- **Tree-like resolution needs `2 ^ Ω(n log n)` nodes for the pigeonhole principle**
[BeyersdorffGalesiLauria2010, Theorem 2]: for `m > n`, every tree-like resolution refutation of
`PHP^m_n` has at least `(n / 2 + 1) ^ (n / 2)` nodes. -/
theorem pow_half_le_size_pigeonhole (hnm : n < m) (d : (pigeonhole m n).Derivation []) :
    (n / 2 + 1) ^ (n / 2) ≤ d.size :=
  (Nat.pow_le_pow_left (by omega) _).trans (pow_le_size_pigeonhole (n / 2) hnm d)

end Derivation

/-- **DPLL search trees for the pigeonhole principle**: for `m > n` and every `h`, a decision tree
finding a falsified clause of `PHP^m_n` has more than `(n + 1 - h) ^ h / 2` leaves. -/
theorem pow_lt_two_mul_leafCount_pigeonhole (h : ℕ) (hnm : n < m)
    {t : DecisionTree (Fin m × Fin n) (Clause (Fin m × Fin n))}
    (ht : t.FindsFalsifiedClause (pigeonhole m n)) : (n + 1 - h) ^ h < 2 * t.leafCount := by
  obtain ⟨d, hd⟩ := ht.exists_derivation
  have := d.pow_le_size_pigeonhole h hnm
  omega

end CNF

end Cslib.Logic.PL
