/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Pigeonhole
public import Complexity.Logics.Propositional.Resolution.TreeLike
import Complexity.Foundations.Data.List.Counting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith

/-!
# Haken's resolution lower bound for the pigeonhole principle

[Haken][Haken1985] proved that resolution refutations of the pigeonhole formula `PHP^{n+1}_n`
(`Cslib.Logic.PL.CNF.pigeonhole (n + 1) n`) have exponential size. This file follows the
simplified proof of [Beame and Pitassi][BeamePitassi1996] (see also [Jukna, Section 18.6]
[Jukna2012]), replacing random restrictions by a greedy choice of one pigeon–hole pair at a time.

Let `P ⊆ Fin m` and `H ⊆ Fin n` be sets of remaining pigeons and holes with `#P = #H + 1`, and let
`pigeonholeOn P H` be the pigeonhole formula restricted to `P` and `H`.

1. **Critical assignments and the width of the monotone translation.** A *critical assignment*
   (`Cslib.Logic.PL.Pigeonhole.IsCrit`) is an injection `g : H → P`; its truth assignment
   (`Cslib.Logic.PL.Pigeonhole.critAssign`) places `g j` in hole `j` for each `j ∈ H` and leaves a
   single pigeon `i₀ ∈ P \ H.image g` outside all holes. Let `falsifiedPigeons P H c` be the set of
   pigeons `i₀ ∈ P` that are left out by some critical assignment falsifying `c`. Each clause of
   `pigeonholeOn P H` has `#(falsifiedPigeons P H c) ≤ 1`, resolution steps are subadditive, and the
   empty clause has `falsifiedPigeons P H [] = P`, so every refutation contains a line `c` with
   `#P ≤ 3 #(falsifiedPigeons P H c) ≤ 2 #P` (for `#H ≥ 1`), giving
   `2 (#H)² ≤ 9 #(falsifiedPigeons P H c) (#P - #(falsifiedPigeons P H c))`.

   For `i₀ ∈ falsifiedPigeons P H c` (witnessed by `g`) and `j ∈ H` with
   `g j ∈ P \ falsifiedPigeons P H c`, updating `g` at `j` to `i₀` gives a critical assignment with
   missing pigeon `g j`, which must satisfy `c`. Any literal of `c` that flips from `false` to
   `true` under this swap lies in column `j` and is satisfied by the partial assignment
   `matchPair i₀ j` that matches `i₀` to `j`. Thus `(i₀, j)` belongs to `satPairs P H c`, the set
   of pairs in `P ×ˢ H` whose matching assignment satisfies `c`, so
   `#(falsifiedPigeons P H c) (#P - #(falsifiedPigeons P H c)) ≤ #(satPairs P H c)` and every
   refutation of `pigeonholeOn P H` contains a line with `2 (#H)² ≤ 9 #(satPairs P H c)`
   (`Cslib.Logic.PL.Pigeonhole.exists_le_card_satPairs`).

2. **Eliminating wide lines by matching one pair at a time.** Restricting a proof from
   `pigeonholeOn P H` by `matchPair i₀ j₀` (`Cslib.Logic.PL.CNF.IsProof.restrictBy`) yields a proof
   from `pigeonholeOn (P.erase i₀) (H.erase j₀)` whose lines are subclauses of a sublist of the
   lines not satisfied by `matchPair i₀ j₀`. Since `satPairs` is monotone in `P`, `H`, and the
   clause, choosing `(i₀, j₀) ∈ P ×ˢ H` by averaging reduces the number `f` of lines with
   `d ≤ #(satPairs P H c)` to `f'` with `C f' ≤ (C - 1) f` whenever `#P · #H ≤ C d`. After
   `t = n / 3` steps from `PHP^{n+1}_n` with `d = 2 (n - n / 3)² / 9` and `C = 12` (for `n ≥ 8`),
   a line with `d ≤ #(satPairs P_t H_t c)` still remains, so `12 ^ (n / 3) ≤ 11 ^ (n / 3) · s`
   (`Cslib.Logic.PL.CNF.pow_le_mul_of_refutableInSize_pigeonhole`) and `2 ^ (n / 24) ≤ s` for all
   `n` (`Cslib.Logic.PL.CNF.two_pow_le_of_refutableInSize_pigeonhole`).

## Main definitions

* `Cslib.Logic.PL.Pigeonhole.pigeonClauseOn`, `Cslib.Logic.PL.Pigeonhole.pigeonholeOn`: the pigeon
  clauses and pigeonhole formula on subsets `P` and `H`.
* `Cslib.Logic.PL.Pigeonhole.matchPair`: the partial assignment matching a pigeon to a hole.
* `Cslib.Logic.PL.Pigeonhole.satPairs`: the pairs in `P ×ˢ H` whose matching assignment satisfies a
  clause (its monotone translation).
* `Cslib.Logic.PL.Pigeonhole.IsCrit`, `Cslib.Logic.PL.Pigeonhole.critAssign`,
  `Cslib.Logic.PL.Pigeonhole.falsifiedPigeons`: critical assignments and the missing pigeons of
  critical assignments falsifying a clause.

## Main results

* `Cslib.Logic.PL.Pigeonhole.exists_le_card_satPairs`: every refutation of `pigeonholeOn P H`
  (with `#P = #H + 1`) has a line `c` with `2 (#H)² ≤ 9 #(satPairs P H c)`.
* `Cslib.Logic.PL.CNF.pow_le_mul_of_refutableInSize_pigeonhole`: for `n ≥ 8`, every resolution
  refutation of `PHP^{n+1}_n` of `s` lines satisfies `12 ^ (n / 3) ≤ 11 ^ (n / 3) · s`.
* `Cslib.Logic.PL.CNF.two_pow_le_of_refutableInSize_pigeonhole`,
  `Cslib.Logic.PL.CNF.not_refutableInSize_pigeonhole`: **Haken's theorem**: every resolution
  refutation of `PHP^{n+1}_n` has at least `2 ^ (n / 24)` lines.
* `Cslib.Logic.PL.CNF.Derivation.two_pow_le_size_pigeonhole`: the same lower bound for tree-like
  resolution refutations.

## References

* [A. Haken, *The intractability of resolution*][Haken1985]
* [P. Beame, T. Pitassi, *Simplified and improved resolution lower bounds*][BeamePitassi1996]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Section 18.6][Jukna2012]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset

namespace Pigeonhole

variable {m n : ℕ}

/-! ### Pigeonhole formulas on subsets of pigeons and holes -/

/-- The pigeon clause of pigeon `i` restricted to the holes `H`. -/
def pigeonClauseOn (H : Finset (Fin n)) (i : Fin m) : Clause (Fin m × Fin n) :=
  ((List.finRange n).filter (· ∈ H)).map fun j => ((i, j), true)

/-- The pigeonhole formula restricted to the pigeons `P` and holes `H`. -/
def pigeonholeOn (P : Finset (Fin m)) (H : Finset (Fin n)) : CNF (Fin m × Fin n) :=
  ((List.finRange m).filter (· ∈ P)).map (pigeonClauseOn H) ++
    ((List.finRange n).filter (· ∈ H)).flatMap fun j =>
      ((List.finRange m).filter (· ∈ P)).flatMap fun i =>
        ((List.finRange m).filter (fun i' => i' ∈ P ∧ i < i')).map fun i' => CNF.holeClause i i' j

/-- Restricting the pigeon clause of `i` to all holes gives `CNF.pigeonClause n i`. -/
@[simp] theorem pigeonClauseOn_univ (i : Fin m) :
    pigeonClauseOn (univ : Finset (Fin n)) i = CNF.pigeonClause n i := by
  simp [pigeonClauseOn, CNF.pigeonClause]

/-- Restricting the pigeonhole formula to all pigeons and holes gives `CNF.pigeonhole m n`. -/
@[simp] theorem pigeonholeOn_univ :
    pigeonholeOn (univ : Finset (Fin m)) (univ : Finset (Fin n)) = CNF.pigeonhole m n := by
  simp [pigeonholeOn, CNF.pigeonhole]

/-- The clauses of `pigeonholeOn P H` are its pigeon clauses and its hole clauses on `P` and `H`. -/
theorem mem_pigeonholeOn {P : Finset (Fin m)} {H : Finset (Fin n)} {c : Clause (Fin m × Fin n)} :
    c ∈ pigeonholeOn P H ↔
      (∃ i ∈ P, c = pigeonClauseOn H i) ∨
        ∃ i ∈ P, ∃ i' ∈ P, ∃ j ∈ H, i < i' ∧ c = CNF.holeClause i i' j := by
  simp only [pigeonholeOn, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq, List.mem_flatMap]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨j, hj, i, hi, i', ⟨hi', hii'⟩, rfl⟩)
    exacts [Or.inl ⟨i, hi, rfl⟩, Or.inr ⟨i, hi, i', hi', j, hj, hii', rfl⟩]
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, i', hi', j, hj, hii', rfl⟩)
    exacts [Or.inl ⟨i, hi, rfl⟩, Or.inr ⟨j, hj, i, hi, i', ⟨hi', hii'⟩, rfl⟩]

/-- `pigeonClauseOn H i` evaluates to `true` under `σ` iff `σ (i, j) = true` for some `j ∈ H`. -/
@[simp] theorem eval_pigeonClauseOn (σ : Fin m × Fin n → Bool) (H : Finset (Fin n)) (i : Fin m) :
    (pigeonClauseOn H i).eval σ = true ↔ ∃ j ∈ H, σ (i, j) = true := by
  simp [pigeonClauseOn, Clause.eval_eq_true_iff]

/-! ### Matching a pigeon to a hole -/

/-- The partial assignment matching pigeon `i` to hole `j`: `(i, j)` is set to `true`, and all
other variables in row `i` or column `j` are set to `false`. -/
def matchPair (i : Fin m) (j : Fin n) (v : Fin m × Fin n) : Option Bool :=
  if v.1 = i ∧ v.2 = j then some true
  else if v.1 = i ∨ v.2 = j then some false
  else none

/-- `matchPair i j` assigns `some true` to `(i, j)`. -/
@[simp] theorem matchPair_self (i : Fin m) (j : Fin n) : matchPair i j (i, j) = some true := by
  simp [matchPair]

/-- `matchPair i j` leaves `v` unassigned iff `v.1 ≠ i` and `v.2 ≠ j`. -/
theorem matchPair_eq_none {i : Fin m} {j : Fin n} {v : Fin m × Fin n} :
    matchPair i j v = none ↔ v.1 ≠ i ∧ v.2 ≠ j := by
  simp only [matchPair]
  split_ifs with h₁ h₂
  · simp [h₁.1]
  · simp only [false_iff, not_and_or, not_ne_iff]
    exact h₂
  · push Not at h₂
    simp [h₂]

private theorem matchPair_of_fst_eq_of_snd_ne {i : Fin m} {j j' : Fin n} (hj : j' ≠ j) :
    matchPair i j (i, j') = some false := by
  simp [matchPair, hj]

private theorem matchPair_of_fst_ne_of_snd_eq {i i' : Fin m} {j : Fin n} (hi : i' ≠ i) :
    matchPair i j (i', j) = some false := by
  simp [matchPair, hi]

/-- Restricting `pigeonholeOn P H` by matching `i₀` to `j₀ ∈ H` leaves clauses of
`pigeonholeOn (P.erase i₀) (H.erase j₀)`. -/
private theorem restrictBy_pigeonholeOn_subset {P : Finset (Fin m)} {H : Finset (Fin n)}
    {i₀ : Fin m} {j₀ : Fin n} (hj₀ : j₀ ∈ H) :
    (pigeonholeOn P H).restrictBy (matchPair i₀ j₀) ⊆ pigeonholeOn (P.erase i₀) (H.erase j₀) := by
  intro c hc
  obtain ⟨d, hd, hsat, rfl⟩ := CNF.mem_restrictBy.1 hc
  rcases mem_pigeonholeOn.1 hd with ⟨i, hi, rfl⟩ | ⟨i, hi, i', hi', j, hj, hii', rfl⟩
  · have hii₀ : i ≠ i₀ := by
      rintro rfl
      refine hsat ((i, j₀), true) ?_ (matchPair_self i j₀)
      simp [pigeonClauseOn, hj₀]
    refine mem_pigeonholeOn.2 (Or.inl ⟨i, mem_erase.2 ⟨hii₀, hi⟩, ?_⟩)
    simp only [pigeonClauseOn, List.filter_map, List.filter_filter]
    congr 1
    refine List.filter_congr fun j _ => ?_
    simp [matchPair_eq_none, hii₀, mem_erase]
  · have hne : i ≠ i' := hii'.ne
    have hii₀ : i ≠ i₀ := by
      rintro rfl
      by_cases hjj₀ : j = j₀
      · subst hjj₀
        exact hsat ((i', j), false) (by simp [CNF.holeClause])
          (matchPair_of_fst_ne_of_snd_eq hne.symm)
      · exact hsat ((i, j), false) (by simp [CNF.holeClause]) (matchPair_of_fst_eq_of_snd_ne hjj₀)
    have hjj₀ : j ≠ j₀ := by
      rintro rfl
      exact hsat ((i, j), false) (by simp [CNF.holeClause]) (matchPair_of_fst_ne_of_snd_eq hii₀)
    have hi'i₀ : i' ≠ i₀ := by
      rintro rfl
      exact hsat ((i', j), false) (by simp [CNF.holeClause]) (matchPair_of_fst_eq_of_snd_ne hjj₀)
    refine mem_pigeonholeOn.2 (Or.inr ⟨i, mem_erase.2 ⟨hii₀, hi⟩, i', mem_erase.2 ⟨hi'i₀, hi'⟩,
      j, mem_erase.2 ⟨hjj₀, hj⟩, hii', ?_⟩)
    simp [CNF.holeClause, matchPair_eq_none, hii₀, hi'i₀, hjj₀]

/-! ### Critical assignments and the monotone width bound -/

/-- `g` is a **critical assignment** of the holes `H` into the pigeons `P`: it maps `H` injectively
into `P`. When `#P = #H + 1`, this leaves out a single pigeon of `P`. -/
def IsCrit (P : Finset (Fin m)) (H : Finset (Fin n)) (g : Fin n → Fin m) : Prop :=
  (∀ j ∈ H, g j ∈ P) ∧ Set.InjOn g H

/-- The truth assignment of a hole-to-pigeon map `g` on the holes `H`: `(i, j)` is `true` when
`j ∈ H` and `g j = i`. -/
def critAssign (H : Finset (Fin n)) (g : Fin n → Fin m) (v : Fin m × Fin n) : Bool :=
  decide (v.2 ∈ H ∧ g v.2 = v.1)

/-- Every hole clause on distinct pigeons is satisfied by `critAssign H g`. -/
private theorem eval_holeClause_critAssign (H : Finset (Fin n)) (g : Fin n → Fin m) {i i' : Fin m}
    (hne : i ≠ i') (j : Fin n) :
    (CNF.holeClause i i' j).eval (critAssign H g) = true := by
  rw [CNF.eval_holeClause]
  by_contra! h
  simp only [critAssign, Bool.not_eq_false, decide_eq_true_eq] at h
  exact hne (h.1.2.symm.trans h.2.2)

/-- The pigeon clause of `i` on `H` is satisfied by `critAssign H g` iff `i ∈ H.image g`. -/
private theorem eval_pigeonClauseOn_critAssign (H : Finset (Fin n)) (g : Fin n → Fin m)
    (i : Fin m) : (pigeonClauseOn H i).eval (critAssign H g) = true ↔ i ∈ H.image g := by
  simp [eval_pigeonClauseOn, critAssign, mem_image]

/-- When `#P = #H + 1`, a critical assignment leaves out at most one pigeon of `P`. -/
private theorem eq_of_not_mem_image_of_isCrit {P : Finset (Fin m)} {H : Finset (Fin n)}
    {g : Fin n → Fin m} (hP : #P = #H + 1) (hg : IsCrit P H g) {i₁ i₂ : Fin m} (hi₁ : i₁ ∈ P)
    (hi₂ : i₂ ∈ P) (h₁ : i₁ ∉ H.image g) (h₂ : i₂ ∉ H.image g) : i₁ = i₂ := by
  by_contra hne
  have hsub : H.image g ⊆ P := image_subset_iff.2 hg.1
  have hcard : #(H.image g) = #H := card_image_of_injOn hg.2
  have hpair : ({i₁, i₂} : Finset (Fin m)) ⊆ P \ H.image g := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact mem_sdiff.2 ⟨hi₁, h₁⟩
    · rw [mem_singleton.1 hx]
      exact mem_sdiff.2 ⟨hi₂, h₂⟩
  have hle := (card_le_card hpair).trans_eq (card_sdiff_of_subset hsub)
  rw [card_pair hne, hcard, hP] at hle
  omega

private theorem mem_image_of_ne_of_isCrit {P : Finset (Fin m)} {H : Finset (Fin n)}
    {g : Fin n → Fin m} (hP : #P = #H + 1) (hg : IsCrit P H g) {i₀ i : Fin m} (hi₀ : i₀ ∈ P)
    (h₀ : i₀ ∉ H.image g) (hi : i ∈ P) (hne : i ≠ i₀) : i ∈ H.image g := by
  by_contra h
  exact hne (eq_of_not_mem_image_of_isCrit hP hg hi hi₀ h h₀)

/-- Swapping the missing pigeon `i₀` into hole `j ∈ H` gives a critical assignment whose missing
pigeon is `g j`. -/
private theorem isCrit_update {P : Finset (Fin m)} {H : Finset (Fin n)} {g : Fin n → Fin m}
    (hg : IsCrit P H g) {i₀ : Fin m} (hi₀ : i₀ ∈ P) (h₀ : i₀ ∉ H.image g) {j : Fin n} :
    IsCrit P H (Function.update g j i₀) := by
  refine ⟨fun y hy => ?_, fun y₁ hy₁ y₂ hy₂ heq => ?_⟩
  · by_cases hyj : y = j
    · subst hyj
      simpa using hi₀
    · simpa [hyj] using hg.1 y hy
  · by_cases h₁ : y₁ = j <;> by_cases h₂ : y₂ = j
    · exact h₁.trans h₂.symm
    · subst h₁
      simp only [Function.update_self, Function.update_of_ne h₂] at heq
      exact absurd (heq ▸ mem_image_of_mem g hy₂) h₀
    · subst h₂
      simp only [Function.update_self, Function.update_of_ne h₁] at heq
      exact absurd (heq.symm ▸ mem_image_of_mem g hy₁) h₀
    · simp only [Function.update_of_ne h₁, Function.update_of_ne h₂] at heq
      exact hg.2 hy₁ hy₂ heq

private theorem not_mem_image_update {P : Finset (Fin m)} {H : Finset (Fin n)} {g : Fin n → Fin m}
    (hg : IsCrit P H g) {i₀ : Fin m} (h₀ : i₀ ∉ H.image g) {j : Fin n} (hj : j ∈ H) :
    g j ∉ H.image (Function.update g j i₀) := by
  intro h
  obtain ⟨y, hy, heq⟩ := mem_image.1 h
  by_cases hyj : y = j
  · subst hyj
    simp only [Function.update_self] at heq
    exact h₀ (heq ▸ mem_image_of_mem g hj)
  · simp only [Function.update_of_ne hyj] at heq
    exact hyj (hg.2 hy hj heq)

/-- When `#P = #H + 1`, every pigeon `i₀ ∈ P` is the missing pigeon of some critical assignment. -/
private theorem exists_isCrit_not_mem_image {P : Finset (Fin m)} {H : Finset (Fin n)}
    (hP : #P = #H + 1) {i₀ : Fin m} (hi₀ : i₀ ∈ P) :
    ∃ g, IsCrit P H g ∧ i₀ ∉ H.image g := by
  have hcard : Fintype.card H = Fintype.card (P.erase i₀) := by
    rw [Fintype.card_coe, Fintype.card_coe, card_erase_of_mem hi₀, hP]
    omega
  let e : H ≃ P.erase i₀ := Fintype.equivOfCardEq hcard
  let g : Fin n → Fin m := fun j => if hj : j ∈ H then (e ⟨j, hj⟩).1 else i₀
  refine ⟨g, ⟨fun j hj => ?_, fun j₁ hj₁ j₂ hj₂ heq => ?_⟩, ?_⟩
  · simp only [g, hj, ↓reduceDIte]
    exact erase_subset i₀ P (e ⟨j, hj⟩).2
  · rw [mem_coe] at hj₁ hj₂
    simp only [g, hj₁, hj₂, ↓reduceDIte] at heq
    have := e.injective (Subtype.ext heq)
    simpa using this
  · intro h
    obtain ⟨j, hj, heq⟩ := mem_image.1 h
    simp only [g, hj, ↓reduceDIte] at heq
    exact (mem_erase.1 (e ⟨j, hj⟩).2).1 heq

/-- If a variable `v` changes truth value when hole `j ∈ H` is updated to `i₀`, then `v` lies in
column `j` and `matchPair i₀ j` assigns `v` its new truth value. -/
private theorem matchPair_eq_some_of_critAssign_ne {H : Finset (Fin n)} {g : Fin n → Fin m}
    {i₀ : Fin m} {j : Fin n} (hj : j ∈ H) {v : Fin m × Fin n}
    (hne : critAssign H g v ≠ critAssign H (Function.update g j i₀) v) :
    matchPair i₀ j v = some (critAssign H (Function.update g j i₀) v) := by
  obtain ⟨x, y⟩ := v
  have hyj : y = j := by
    by_contra hyj
    exact hne (by simp [critAssign, hyj])
  subst hyj
  by_cases hxi₀ : x = i₀
  · subst hxi₀
    simp [matchPair, critAssign, hj]
  · simp [matchPair, critAssign, hj, hxi₀, Ne.symm hxi₀]

/-- The pairs `(i, j) ∈ P ×ˢ H` whose matching assignment `matchPair i j` satisfies a literal of
`c`. This is the monotone translation of `c` (together with row-negation pairs). -/
def satPairs (P : Finset (Fin m)) (H : Finset (Fin n)) (c : Clause (Fin m × Fin n)) :
    Finset (Fin m × Fin n) :=
  (P ×ˢ H).filter fun p => ∃ l ∈ c, matchPair p.1 p.2 l.1 = some l.2

private theorem satPairs_subset {P' P : Finset (Fin m)} {H' H : Finset (Fin n)}
    {c' c : Clause (Fin m × Fin n)} (hP : P' ⊆ P) (hH : H' ⊆ H) (hc : ∀ l ∈ c', l ∈ c) :
    satPairs P' H' c' ⊆ satPairs P H c := by
  intro p hp
  obtain ⟨hpPH, l, hl, hmatch⟩ := mem_filter.1 hp
  exact mem_filter.2 ⟨ product_subset_product hP hH hpPH, l, hc l hl, hmatch⟩

/-- The pigeons of `P` that can be the missing pigeon of a critical assignment falsifying `c`. -/
noncomputable def falsifiedPigeons (P : Finset (Fin m)) (H : Finset (Fin n))
    (c : Clause (Fin m × Fin n)) : Finset (Fin m) :=
  open Classical in
  P.filter fun i => ∃ g, IsCrit P H g ∧ i ∉ H.image g ∧ c.eval (critAssign H g) = false

/-- A pigeon `i` belongs to `falsifiedPigeons P H c` iff `i ∈ P` and `i` is the missing pigeon of
some critical assignment falsifying `c`. -/
theorem mem_falsifiedPigeons {P : Finset (Fin m)} {H : Finset (Fin n)}
    {c : Clause (Fin m × Fin n)} {i : Fin m} :
    i ∈ falsifiedPigeons P H c ↔
      i ∈ P ∧ ∃ g, IsCrit P H g ∧ i ∉ H.image g ∧ c.eval (critAssign H g) = false := by
  classical
  simp [falsifiedPigeons]

/-- `falsifiedPigeons P H c` is a subset of `P`. -/
theorem falsifiedPigeons_subset (P : Finset (Fin m)) (H : Finset (Fin n))
    (c : Clause (Fin m × Fin n)) : falsifiedPigeons P H c ⊆ P := by
  intro i hi
  exact (mem_falsifiedPigeons.1 hi).1

/-- A clause of `pigeonholeOn P H` has at most one falsified pigeon when `#P = #H + 1`. -/
private theorem card_falsifiedPigeons_le_one_of_mem_pigeonholeOn {P : Finset (Fin m)}
    {H : Finset (Fin n)} (hP : #P = #H + 1) {c : Clause (Fin m × Fin n)}
    (hc : c ∈ pigeonholeOn P H) : #(falsifiedPigeons P H c) ≤ 1 := by
  rcases mem_pigeonholeOn.1 hc with ⟨i₀, hi₀, rfl⟩ | ⟨i, _, i', _, j, _, hii', rfl⟩
  · refine card_le_one.2 fun i₁ hi₁ i₂ hi₂ => ?_
    obtain ⟨hi₁P, g₁, hg₁, h₁, hc₁⟩ := mem_falsifiedPigeons.1 hi₁
    obtain ⟨hi₂P, g₂, hg₂, h₂, hc₂⟩ := mem_falsifiedPigeons.1 hi₂
    rw [Bool.eq_false_iff, ne_eq, eval_pigeonClauseOn_critAssign] at hc₁ hc₂
    exact (eq_of_not_mem_image_of_isCrit hP hg₁ hi₁P hi₀ h₁ hc₁).trans
      (eq_of_not_mem_image_of_isCrit hP hg₂ hi₀ hi₂P hc₂ h₂)
  · refine card_le_one.2 fun i₁ hi₁ => ?_
    obtain ⟨-, g, -, -, hc₁⟩ := mem_falsifiedPigeons.1 hi₁
    rw [eval_holeClause_critAssign H g hii'.ne j] at hc₁
    cases hc₁

/-- `falsifiedPigeons` is subadditive across resolution steps. -/
private theorem card_falsifiedPigeons_resolvent_le (P : Finset (Fin m)) (H : Finset (Fin n))
    (c₁ c₂ : Clause (Fin m × Fin n)) (v : Fin m × Fin n) :
    #(falsifiedPigeons P H (c₁.resolvent c₂ v)) ≤
      #(falsifiedPigeons P H c₁) + #(falsifiedPigeons P H c₂) := by
  classical
  refine (card_le_card fun i hi => ?_).trans (card_union_le _ _)
  obtain ⟨hiP, g, hg, h₀, hc⟩ := mem_falsifiedPigeons.1 hi
  by_cases hc₁ : c₁.eval (critAssign H g) = false
  · exact mem_union_left _ (mem_falsifiedPigeons.2 ⟨hiP, g, hg, h₀, hc₁⟩)
  · have hc₂ : c₂.eval (critAssign H g) = false := by
      by_contra hc₂
      exact Bool.false_ne_true (hc.symm.trans (Clause.eval_resolvent v
        (Bool.not_eq_false _ ▸ hc₁) (Bool.not_eq_false _ ▸ hc₂)))
    exact mem_union_right _ (mem_falsifiedPigeons.2 ⟨hiP, g, hg, h₀, hc₂⟩)

/-- Every pigeon of `P` is a falsified pigeon of the empty clause when `#P = #H + 1`. -/
private theorem falsifiedPigeons_nil {P : Finset (Fin m)} {H : Finset (Fin n)} (hP : #P = #H + 1) :
    falsifiedPigeons P H [] = P := by
  ext i
  rw [mem_falsifiedPigeons]
  refine ⟨fun h => h.1, fun hi => ⟨hi, ?_⟩⟩
  obtain ⟨g, hg, h₀⟩ := exists_isCrit_not_mem_image hP hi
  exact ⟨g, hg, h₀, rfl⟩

/-- Along a proof from `pigeonholeOn P H` with `#P = #H + 1` and `#H ≥ 1`, either every line has
`3 #(falsifiedPigeons P H c) < #P`, or some line has `#P ≤ 3 #(falsifiedPigeons P H c) ≤ 2 #P`. -/
private theorem forall_or_exists_card_falsifiedPigeons {P : Finset (Fin m)} {H : Finset (Fin n)}
    (hP : #P = #H + 1) (hH : 1 ≤ #H) {ls : List (Clause (Fin m × Fin n))}
    (h : (pigeonholeOn P H).IsProof ls) :
    (∀ c ∈ ls, 3 * #(falsifiedPigeons P H c) < #P) ∨
      ∃ c ∈ ls, #P ≤ 3 * #(falsifiedPigeons P H c) ∧ 3 * #(falsifiedPigeons P H c) ≤ 2 * #P := by
  induction h with
  | nil => exact Or.inl (by simp)
  | @mem ls c _ hc ih =>
    rcases ih with ih | ⟨d, hd, hd'⟩
    · have h1 := card_falsifiedPigeons_le_one_of_mem_pigeonholeOn hP hc
      by_cases h3 : 3 * #(falsifiedPigeons P H c) < #P
      · exact Or.inl fun d hd => (List.mem_cons.1 hd).elim (fun h => h ▸ h3) (ih d)
      · exact Or.inr ⟨c, List.mem_cons_self, by omega, by omega⟩
    · exact Or.inr ⟨d, List.mem_cons_of_mem _ hd, hd'⟩
  | @resolvent ls c₁ c₂ v _ h₁ h₂ _ _ ih =>
    rcases ih with ih | ⟨d, hd, hd'⟩
    · have hle := card_falsifiedPigeons_resolvent_le P H c₁ c₂ v
      have hc₁ := ih c₁ h₁
      have hc₂ := ih c₂ h₂
      by_cases h3 : 3 * #(falsifiedPigeons P H (c₁.resolvent c₂ v)) < #P
      · exact Or.inl fun d hd => (List.mem_cons.1 hd).elim (fun h => h ▸ h3) (ih d)
      · exact Or.inr ⟨_, List.mem_cons_self, by omega, by omega⟩
    · exact Or.inr ⟨d, List.mem_cons_of_mem _ hd, hd'⟩

/-- Every refutation of `pigeonholeOn P H` (with `#P = #H + 1`) contains a line `c` with
`2 (#H)² ≤ 9 #(falsifiedPigeons P H c) (#P - #(falsifiedPigeons P H c))`. -/
private theorem exists_le_card_falsifiedPigeons_mul {P : Finset (Fin m)} {H : Finset (Fin n)}
    (hP : #P = #H + 1) {ls : List (Clause (Fin m × Fin n))} (h : (pigeonholeOn P H).IsProof ls)
    (hnil : [] ∈ ls) :
    ∃ c ∈ ls, 2 * (#H) ^ 2 ≤
      9 * #(falsifiedPigeons P H c) * (#P - #(falsifiedPigeons P H c)) := by
  rcases Nat.eq_zero_or_pos #H with hH0 | hH
  · exact ⟨[], hnil, by simp [hH0]⟩
  rcases forall_or_exists_card_falsifiedPigeons hP hH h with hall | ⟨c, hc, h₁, h₂⟩
  · have h' := hall [] hnil
    rw [falsifiedPigeons_nil hP] at h'
    omega
  · refine ⟨c, hc, ?_⟩
    set s := #(falsifiedPigeons P H c)
    have hsP : s ≤ #P := card_le_card (falsifiedPigeons_subset P H c)
    have hprod : 0 ≤ (3 * s - #P) * (2 * #P - 3 * s) := Nat.zero_le _
    zify [hsP, h₁, h₂] at hprod ⊢
    nlinarith

/-- For each `i₀ ∈ falsifiedPigeons P H c`, at least `#P - #(falsifiedPigeons P H c)` holes `j ∈ H`
have `(i₀, j) ∈ satPairs P H c`. -/
private theorem sub_le_card_filter_satPairs {P : Finset (Fin m)} {H : Finset (Fin n)}
    (hP : #P = #H + 1) {c : Clause (Fin m × Fin n)} {i₀ : Fin m}
    (hi₀ : i₀ ∈ falsifiedPigeons P H c) :
    #P - #(falsifiedPigeons P H c) ≤ #((satPairs P H c).filter fun p => p.1 = i₀) := by
  set S := falsifiedPigeons P H c
  obtain ⟨hi₀P, g, hg, h₀, hc₀⟩ := mem_falsifiedPigeons.1 hi₀
  -- every `i₁ ∈ P \ S` is `g j` for a hole `j ∈ H` with `(i₀, j) ∈ satPairs P H c`
  have hsub : P \ S ⊆ (H.filter fun j => (i₀, j) ∈ satPairs P H c).image g := by
    intro i₁ hi₁
    obtain ⟨hi₁P, hi₁S⟩ := mem_sdiff.1 hi₁
    have hne : i₁ ≠ i₀ := fun h => hi₁S (h ▸ hi₀)
    obtain ⟨j, hj, rfl⟩ := mem_image.1 (mem_image_of_ne_of_isCrit hP hg hi₀P h₀ hi₁P hne)
    refine mem_image_of_mem g (mem_filter.2 ⟨hj, ?_⟩)
    -- swapping `i₀` into hole `j` gives a critical assignment with missing pigeon `g j ∉ S`
    have hc₁ : c.eval (critAssign H (Function.update g j i₀)) = true := by
      by_contra hc₁
      exact hi₁S (mem_falsifiedPigeons.2 ⟨hg.1 j hj, _, isCrit_update hg hi₀P h₀,
        not_mem_image_update hg h₀ hj, Bool.eq_false_iff.2 hc₁⟩)
    obtain ⟨l, hl, hl₁⟩ := (Clause.eval_eq_true_iff _ _).1 hc₁
    have hne' : critAssign H g l.1 ≠ critAssign H (Function.update g j i₀) l.1 := fun h =>
      Bool.false_ne_true (hc₀.symm.trans ((Clause.eval_eq_true_iff _ _).2 ⟨l, hl, h.trans hl₁⟩))
    exact mem_filter.2 ⟨mem_product.2 ⟨hi₀P, hj⟩, l, hl,
      hl₁ ▸ matchPair_eq_some_of_critAssign_ne hj hne'⟩
  have hSP : S ⊆ P := falsifiedPigeons_subset P H c
  calc #P - #S = #(P \ S) := (card_sdiff_of_subset hSP).symm
    _ ≤ #((H.filter fun j => (i₀, j) ∈ satPairs P H c).image g) := card_le_card hsub
    _ ≤ #(H.filter fun j => (i₀, j) ∈ satPairs P H c) := card_image_le
    _ ≤ #((satPairs P H c).filter fun p => p.1 = i₀) := by
      refine card_le_card_of_injOn (fun j => (i₀, j)) (fun j hj => ?_)
        fun _ _ _ _ heq => (Prod.mk.inj heq).2
      exact mem_filter.2 ⟨(mem_filter.1 hj).2, rfl⟩

/-- **Relating falsified pigeons and monotone pairs** [Beame and Pitassi][BeamePitassi1996]:
`#(falsifiedPigeons P H c) (#P - #(falsifiedPigeons P H c)) ≤ #(satPairs P H c)`. -/
private theorem card_falsifiedPigeons_mul_le_card_satPairs {P : Finset (Fin m)} {H : Finset (Fin n)}
    (hP : #P = #H + 1) (c : Clause (Fin m × Fin n)) :
    #(falsifiedPigeons P H c) * (#P - #(falsifiedPigeons P H c)) ≤ #(satPairs P H c) := by
  set S := falsifiedPigeons P H c
  calc #S * (#P - #S) = ∑ _i₀ ∈ S, (#P - #S) := by simp
    _ ≤ ∑ i₀ ∈ S, #((satPairs P H c).filter fun p => p.1 = i₀) :=
      sum_le_sum fun i₀ hi₀ => sub_le_card_filter_satPairs hP hi₀
    _ = #(S.biUnion fun i₀ => (satPairs P H c).filter fun p => p.1 = i₀) := by
      refine (card_biUnion fun i₁ _ i₂ _ hne => disjoint_left.2 fun p hp₁ hp₂ => ?_).symm
      exact hne ((mem_filter.1 hp₁).2.symm.trans (mem_filter.1 hp₂).2)
    _ ≤ #(satPairs P H c) := card_le_card fun p hp => by
      obtain ⟨_, -, hp⟩ := mem_biUnion.1 hp
      exact (mem_filter.1 hp).1

/-- **Every refutation of `pigeonholeOn P H` has a wide monotone line**
[Beame and Pitassi, Lemma 4][BeamePitassi1996] [Jukna, Lemma 18.17][Jukna2012]. When
`#P = #H + 1`, every resolution refutation of `pigeonholeOn P H` contains a line `c` with
`2 (#H)² ≤ 9 #(satPairs P H c)`. -/
theorem exists_le_card_satPairs {P : Finset (Fin m)} {H : Finset (Fin n)} (hP : #P = #H + 1)
    {ls : List (Clause (Fin m × Fin n))} (h : (pigeonholeOn P H).IsProof ls) (hnil : [] ∈ ls) :
    ∃ c ∈ ls, 2 * (#H) ^ 2 ≤ 9 * #(satPairs P H c) := by
  obtain ⟨c, hc, hle⟩ := exists_le_card_falsifiedPigeons_mul hP h hnil
  have hmul := card_falsifiedPigeons_mul_le_card_satPairs hP c
  exact ⟨c, hc, hle.trans (by rw [mul_assoc]; exact Nat.mul_le_mul_left 9 hmul)⟩

/-! ### Eliminating wide lines by greedy matching restrictions -/

private theorem sum_countP_mem_eq_sum_card {α β : Type*} [DecidableEq α] (U : Finset α)
    (S : β → Finset α) :
    ∀ F : List β, (∀ c ∈ F, S c ⊆ U) →
      ∑ x ∈ U, F.countP (fun c => x ∈ S c) = (F.map fun c => #(S c)).sum
  | [], _ => by simp
  | c :: F, hF => by
    simp only [List.countP_cons, sum_add_distrib, List.map_cons, List.sum_cons]
    rw [sum_countP_mem_eq_sum_card U S F fun e he => hF e (List.mem_cons_of_mem _ he), add_comm]
    congr 1
    rw [sum_boole, Nat.cast_id]
    congr 1
    ext x
    simp only [decide_eq_true_eq, mem_filter, and_iff_right_iff_imp]
    exact fun hx => hF c List.mem_cons_self hx

private theorem exists_le_countP_mem {α β : Type*} [DecidableEq α] (U : Finset α) (S : β → Finset α)
    (d : ℕ) (F : List β) (hU : U.Nonempty) (hF : ∀ c ∈ F, S c ⊆ U) (hwide : ∀ c ∈ F, d ≤ #(S c)) :
    ∃ x ∈ U, d * F.length ≤ F.countP (fun c => x ∈ S c) * #U := by
  refine exists_le_of_sum_le hU ?_
  rw [sum_const, nsmul_eq_mul, ← sum_mul, sum_countP_mem_eq_sum_card U S F hF]
  have hge : F.length * d ≤ (F.map fun c => #(S c)).sum := by
    simpa using List.sum_le_sum (l := F) (f := fun _ => d) (g := fun c => #(S c)) hwide
  nlinarith

private theorem countP_le_of_forall₂ {α β : Type*} {R : α → β → Prop} {p : α → Bool}
    {q : β → Bool} {as : List α} {bs : List β} (h : List.Forall₂ R as bs)
    (hpq : ∀ a b, R a b → p a = true → q b = true) :
    as.countP p ≤ bs.countP q := by
  induction h with
  | nil => rfl
  | @cons a b as bs hab _ ih =>
    rw [List.countP_cons, List.countP_cons]
    by_cases ha : p a = true
    · simp only [ha, hpq a b hab ha, ↓reduceIte]
      omega
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      split <;> omega

/-- **One step of greedy matching restriction.** If `#P · #H ≤ C d` and `0 < d`, some pair
`(i₀, j₀) ∈ P ×ˢ H` restricts a refutation of `pigeonholeOn P H` to a refutation of
`pigeonholeOn (P.erase i₀) (H.erase j₀)` whose number `f'` of lines with
`d ≤ #(satPairs (P.erase i₀) (H.erase j₀) c)` satisfies `C f' ≤ (C - 1) f`. -/
private theorem exists_restrict_countP_satPairs {P : Finset (Fin m)} {H : Finset (Fin n)} {C d : ℕ}
    (hP : P.Nonempty) (hH : H.Nonempty) (hd : 0 < d) (hC : #P * #H ≤ C * d)
    {ls : List (Clause (Fin m × Fin n))} (h : (pigeonholeOn P H).IsProof ls) (hnil : [] ∈ ls) :
    ∃ i₀ ∈ P, ∃ j₀ ∈ H, ∃ ls',
      (pigeonholeOn (P.erase i₀) (H.erase j₀)).IsProof ls' ∧ [] ∈ ls' ∧
        C * ls'.countP (fun c => d ≤ #(satPairs (P.erase i₀) (H.erase j₀) c)) ≤
          (C - 1) * ls.countP (fun c => d ≤ #(satPairs P H c)) := by
  set F := ls.filter (fun c => d ≤ #(satPairs P H c))
  have hFlen : F.length = ls.countP (fun c => d ≤ #(satPairs P H c)) := by
    rw [List.countP_eq_length_filter]
  obtain ⟨⟨i₀, j₀⟩, hpU, hmany⟩ := exists_le_countP_mem (P ×ˢ H) (satPairs P H) d F
    (hP.product hH) (fun c _ => filter_subset _ _)
    (fun c hc => by simpa using (List.mem_filter.1 hc).2)
  obtain ⟨hi₀, hj₀⟩ := mem_product.1 hpU
  rw [card_product, hFlen] at hmany
  obtain ⟨ls', h', hsub, ks, hks, hfree, hF⟩ := h.restrictBy (matchPair i₀ j₀)
  obtain ⟨c₀, hc₀, hsub₀⟩ := hsub [] hnil (by simp)
  have hc₀' : c₀ = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl => List.not_mem_nil (hsub₀ l hl)
  refine ⟨i₀, hi₀, j₀, hj₀, ls', h'.mono (restrictBy_pigeonholeOn_subset hj₀), hc₀' ▸ hc₀, ?_⟩
  -- lines of `ls'` are subclauses of lines of `ks`, which are not satisfied by `matchPair i₀ j₀`
  have hle₁ : ls'.countP (fun c => d ≤ #(satPairs (P.erase i₀) (H.erase j₀) c)) ≤
      ks.countP (fun c => (i₀, j₀) ∉ satPairs P H c ∧ d ≤ #(satPairs P H c)) := by
    refine (countP_le_of_forall₂ (q := fun c => decide (d ≤ #(satPairs P H c))) hF
      fun c' c hcc' hw => ?_).trans ?_
    · simp only [decide_eq_true_eq] at hw ⊢
      exact hw.trans (card_le_card (satPairs_subset (erase_subset _ _) (erase_subset _ _) hcc'))
    · refine le_of_eq (List.countP_congr fun c hc => ?_)
      simp only [decide_eq_true_eq, iff_and_self]
      intro _ hmem
      obtain ⟨_, l, hl, hmatch⟩ := mem_filter.1 hmem
      exact hfree c hc l hl hmatch
  have hle₂ := hle₁.trans hks.countP_le
  have hsplit := List.countP_and_not_add_countP_and (fun c => d ≤ #(satPairs P H c))
    (fun c => (i₀, j₀) ∈ satPairs P H c) ls
  have hcnt : F.countP (fun c => (i₀, j₀) ∈ satPairs P H c) =
      ls.countP (fun c => d ≤ #(satPairs P H c) ∧ (i₀, j₀) ∈ satPairs P H c) := by
    rw [List.countP_filter]
    congr 1
    funext c
    simp [Bool.and_comm]
  rw [hcnt] at hmany
  set f := ls.countP (fun c => d ≤ #(satPairs P H c))
  set f' := ls'.countP (fun c => d ≤ #(satPairs (P.erase i₀) (H.erase j₀) c))
  set g := ls.countP (fun c => d ≤ #(satPairs P H c) ∧ (i₀, j₀) ∈ satPairs P H c)
  have hfg : f' + g ≤ f := by omega
  have hdg : d * f ≤ d * (C * g) := by
    calc d * f ≤ g * (C * d) := hmany.trans (Nat.mul_le_mul_left g hC)
      _ = d * (C * g) := by ring
  have hfg' : f ≤ C * g := Nat.le_of_mul_le_mul_left hdg hd
  have hC1 : 1 ≤ C := by
    rcases C with _ | C
    · have := Nat.mul_pos (card_pos.2 hP) (card_pos.2 hH)
      omega
    · omega
  zify [hC1] at hfg hfg' ⊢
  nlinarith

/-- **Iterated greedy matching restriction.** If `#P = #H + 1`, `t ≤ #H`, `#P · #H ≤ C d`,
`0 < d`, and `9 d ≤ 2 (#H - t)²`, then every refutation `ls` of `pigeonholeOn P H` satisfies
`C ^ t ≤ (C - 1) ^ t · ls.countP (fun c => d ≤ #(satPairs P H c))`. -/
private theorem pow_le_mul_countP_satPairs {C d : ℕ} (hd : 0 < d) :
    ∀ (t : ℕ) {P : Finset (Fin m)} {H : Finset (Fin n)} {ls : List (Clause (Fin m × Fin n))},
      #P = #H + 1 → t ≤ #H → #P * #H ≤ C * d → 9 * d ≤ 2 * (#H - t) ^ 2 →
      (pigeonholeOn P H).IsProof ls → [] ∈ ls →
      C ^ t ≤ (C - 1) ^ t * ls.countP (fun c => d ≤ #(satPairs P H c))
  | 0, P, H, ls, hP, _, _, hdH, h, hnil => by
    obtain ⟨c, hc, hwide⟩ := exists_le_card_satPairs hP h hnil
    rw [Nat.sub_zero] at hdH
    have hdc : d ≤ #(satPairs P H c) := by omega
    have hpos : 0 < ls.countP (fun c => d ≤ #(satPairs P H c)) :=
      List.countP_pos_iff.2 ⟨c, hc, by simpa using hdc⟩
    simpa using hpos
  | t + 1, P, H, ls, hP, htH, hC, hdH, h, hnil => by
    have hHpos : 0 < #H := by omega
    have hPpos : 0 < #P := by omega
    obtain ⟨i₀, hi₀, j₀, hj₀, ls', h', hnil', hstep⟩ :=
      exists_restrict_countP_satPairs (card_pos.1 hPpos) (card_pos.1 hHpos) hd hC h hnil
    have hP' : #(P.erase i₀) = #(H.erase j₀) + 1 := by
      rw [card_erase_of_mem hi₀, card_erase_of_mem hj₀]
      omega
    have htH' : t ≤ #(H.erase j₀) := by
      rw [card_erase_of_mem hj₀]
      omega
    have hC' : #(P.erase i₀) * #(H.erase j₀) ≤ C * d :=
      (Nat.mul_le_mul (card_erase_le) (card_erase_le)).trans hC
    have hdH' : 9 * d ≤ 2 * (#(H.erase j₀) - t) ^ 2 := by
      rw [card_erase_of_mem hj₀, Nat.sub_sub, add_comm]
      exact hdH
    have ih := pow_le_mul_countP_satPairs hd t hP' htH' hC' hdH' h' hnil'
    calc C ^ (t + 1) = C ^ t * C := pow_succ C t
      _ ≤ (C - 1) ^ t * ls'.countP (fun c => d ≤ #(satPairs (P.erase i₀) (H.erase j₀) c)) * C :=
        Nat.mul_le_mul_right C ih
      _ = (C - 1) ^ t *
          (C * ls'.countP (fun c => d ≤ #(satPairs (P.erase i₀) (H.erase j₀) c))) := by
        ring
      _ ≤ (C - 1) ^ t * ((C - 1) * ls.countP (fun c => d ≤ #(satPairs P H c))) :=
        Nat.mul_le_mul_left _ hstep
      _ = (C - 1) ^ (t + 1) * ls.countP (fun c => d ≤ #(satPairs P H c)) := by ring

end Pigeonhole

/-! ### Haken's lower bound for `PHP^{n+1}_n` -/

namespace CNF

variable {n : ℕ}

/-- Every resolution refutation of `PHP^{n+1}_n` contains a line whose monotone translation has at
least `2 n² / 9` variable pairs [Beame and Pitassi, Lemma 4][BeamePitassi1996]. -/
theorem exists_le_card_satPairs_pigeonhole {ls : List (Clause (Fin (n + 1) × Fin n))}
    (h : (pigeonhole (n + 1) n).IsProof ls) (hnil : [] ∈ ls) :
    ∃ c ∈ ls, 2 * n ^ 2 ≤ 9 * #(Pigeonhole.satPairs univ univ c) := by
  rw [← Pigeonhole.pigeonholeOn_univ] at h
  simpa using Pigeonhole.exists_le_card_satPairs (by simp) h hnil

private theorem mul_le_twelve_mul_div (hn : 8 ≤ n) :
    (n + 1) * n ≤ 12 * (2 * (n - n / 3) ^ 2 / 9) := by
  rcases lt_or_ge n 12 with hn12 | hn12
  · rcases (by omega : n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11) with rfl | rfl | rfl | rfl <;> decide
  · set m := n - n / 3
    have hm : 2 * n ≤ 3 * m := by omega
    have hsq : 4 * n ^ 2 ≤ 9 * m ^ 2 := by nlinarith
    set d := 2 * m ^ 2 / 9
    have hd : 2 * m ^ 2 ≤ 9 * d + 8 := by omega
    nlinarith

/-- **Haken's theorem (recurrence form)** [Haken][Haken1985]
[Beame and Pitassi, Theorem 2][BeamePitassi1996] [Jukna, Theorem 18.15][Jukna2012]. For `n ≥ 8`,
every resolution refutation of `PHP^{n+1}_n` of `s` lines satisfies
`12 ^ (n / 3) ≤ 11 ^ (n / 3) · s`. -/
theorem pow_le_mul_of_refutableInSize_pigeonhole (hn : 8 ≤ n) {s : ℕ}
    (hs : (pigeonhole (n + 1) n).RefutableInSize s) :
    12 ^ (n / 3) ≤ 11 ^ (n / 3) * s := by
  obtain ⟨ls, h, hnil, hlen⟩ := hs
  rw [← Pigeonhole.pigeonholeOn_univ] at h
  set d := 2 * (n - n / 3) ^ 2 / 9
  have hd : 0 < d := by
    have : 6 ≤ n - n / 3 := by omega
    have : 72 ≤ 2 * (n - n / 3) ^ 2 := by nlinarith
    omega
  have hpow := Pigeonhole.pow_le_mul_countP_satPairs (C := 12) hd (n / 3) (by simp)
    (by simp [Nat.div_le_self]) (by simpa using mul_le_twelve_mul_div hn)
    (by simpa using Nat.mul_div_le (2 * (n - n / 3) ^ 2) 9) h hnil
  exact hpow.trans (Nat.mul_le_mul_left _ (List.countP_le_length.trans hlen))

/-- **Haken's theorem**: every resolution refutation of `PHP^{n+1}_n` has at least `2 ^ (n / 24)`
lines [Haken][Haken1985] [Beame and Pitassi][BeamePitassi1996] [Jukna, Theorem 18.15][Jukna2012]. -/
theorem two_pow_le_of_refutableInSize_pigeonhole {s : ℕ}
    (hs : (pigeonhole (n + 1) n).RefutableInSize s) :
    2 ^ (n / 24) ≤ s := by
  rcases lt_or_ge n 24 with hn | hn
  · have hdiv : n / 24 = 0 := Nat.div_eq_of_lt hn
    obtain ⟨ls, -, hnil, hlen⟩ := hs
    rw [hdiv, pow_zero]
    exact (List.length_pos_of_mem hnil).trans_le hlen
  · set k := n / 24
    have h8k : 8 * k ≤ n / 3 := by omega
    obtain ⟨r, hr⟩ : ∃ r, n / 3 = 8 * k + r := ⟨n / 3 - 8 * k, by omega⟩
    have hpow := pow_le_mul_of_refutableInSize_pigeonhole (by omega) hs
    have h2 : 2 * 11 ^ 8 ≤ 12 ^ 8 := by decide
    have h2k : 2 ^ k * (11 ^ 8) ^ k ≤ (12 ^ 8) ^ k := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left h2 k
    have h11 : (11 ^ 8) ^ k * 11 ^ r = 11 ^ (n / 3) := by
      rw [hr, pow_add, pow_mul]
    have h12 : (12 ^ 8) ^ k * 12 ^ r = 12 ^ (n / 3) := by
      rw [hr, pow_add, pow_mul]
    have hle : 2 ^ k * 11 ^ (n / 3) ≤ 12 ^ (n / 3) := by
      calc 2 ^ k * 11 ^ (n / 3) = 2 ^ k * (11 ^ 8) ^ k * 11 ^ r := by rw [← h11, mul_assoc]
        _ ≤ (12 ^ 8) ^ k * 12 ^ r :=
          Nat.mul_le_mul h2k (Nat.pow_le_pow_left (by decide) r)
        _ = 12 ^ (n / 3) := h12
    have hpos : 0 < 11 ^ (n / 3) := Nat.pow_pos (by decide)
    exact Nat.le_of_mul_le_mul_right (hle.trans (hpow.trans_eq (mul_comm _ _))) hpos

/-- **Haken's theorem**: `PHP^{n+1}_n` has no resolution refutation with fewer than `2 ^ (n / 24)`
lines [Haken][Haken1985] [Beame and Pitassi][BeamePitassi1996]. -/
theorem not_refutableInSize_pigeonhole {s : ℕ} (hs : s < 2 ^ (n / 24)) :
    ¬ (pigeonhole (n + 1) n).RefutableInSize s :=
  fun h => hs.not_ge (two_pow_le_of_refutableInSize_pigeonhole h)

/-- **Tree-like resolution lower bound for `PHP^{n+1}_n`**: every tree-like resolution refutation
of `PHP^{n+1}_n` has at least `2 ^ (n / 24)` nodes. -/
theorem Derivation.two_pow_le_size_pigeonhole (d : (pigeonhole (n + 1) n).Derivation []) :
    2 ^ (n / 24) ≤ d.size :=
  two_pow_le_of_refutableInSize_pigeonhole d.refutableInSize

end CNF

end Cslib.Logic.PL
