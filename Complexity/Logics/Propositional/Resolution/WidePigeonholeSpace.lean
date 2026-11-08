/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Pigeonhole
public import Complexity.Logics.Propositional.Resolution.Space
import Complexity.Logics.Propositional.Resolution.TreeLikeSpace

/-!
# Clause space of the pigeonhole formula

**Torán's pigeonhole space bound**: the wide pigeonhole formula `PHP^m_n`
(`Cslib.Logic.PL.CNF.pigeonhole`) with `n ≥ 1` holes needs clause space `n + 2`, and it is
refutable in this space when `m > n`, whatever the number `m` of pigeons:

* `Cslib.Logic.PL.CNF.add_two_le_of_refutableInSpace_pigeonhole`: for `1 ≤ n`, a refutation in
  clause space `s` has `n + 2 ≤ s`;
* `Cslib.Logic.PL.CNF.refutableInSpace_pigeonhole`: for `n < m`, `PHP^m_n` is refutable in clause
  space `n + 2`;
* `Cslib.Logic.PL.CNF.refutableInSpace_pigeonhole_iff`: for `0 < n < m`, `PHP^m_n` is refutable
  in clause space `s` exactly when `n + 2 ≤ s`.

The clauses of `PHP^m_n` have width `n`, so the Atserias–Dalmau inequality
(`Cslib.Logic.PL.CNF.RefutableInSpace.add_four_le`) gives nothing here. It gives the bound for the
`3`-CNF encoding instead (`Cslib.Logic.PL.CNF.le_of_refutableInSpace_pigeonholeExt`). With no
holes, `PHP^m_0` contains the empty clause for `m ≥ 1` and is refutable in clause space `1`.

**Source and convention.** Torán's survey [Torán, Section 4][Toran2004] states that the
pigeonhole formulas with `m > n` have resolution space exactly `n + 1`, independently of the number
of pigeons. It credits this to Torán's paper *Lower bounds for the space used in resolution* (CSL
1999), which was not inspected for this formalization; the proofs below are a reconstruction and
are not claimed to follow it. The space of the survey is that of a pebble game that may shift a
pebble from a premise to the resolvent [Torán, Definition 7 and Lemma 8][Toran2004], while
configurations here (`Cslib.Logic.PL.CNF.configLTS`) keep both premises while they add the
resolvent. As explained in `Complexity.Logics.Propositional.Resolution.TreeLikeSpace`, this makes
every bound one larger, and Torán's `n + 1` becomes `n + 2`.

**Lower bound.** A partial matching of pigeons to holes *implies* a clause if every matching
containing it satisfies the clause, reading a matching as the assignment that is `true` exactly
on its pairs. Every matching implies the hole clauses; a matching containing a pair of pigeon `i`
implies the pigeon clause of `i`; implication is closed under resolution; and no matching implies
the empty clause. A clause implied by a matching is implied by at most one of its pairs, so the
clauses of a configuration of `k` clauses implied by a matching are implied by at most `k` of its
pairs. In a refutation in clause space at most `n + 1`, every configuration is implied by a
matching except perhaps for one pigeon clause. When a configuration of at most `n` clauses grows,
the exceptional pigeon clause is first sent to a hole left free by the at most `n - 1` pairs
implying the rest; a configuration of `n + 1` clauses can only shrink. So the empty clause never
appears.

**Upper bound.** A DPLL tree queries pigeon `i` in each free hole `h` in turn. If `i` is in no
free hole, the pigeon clause of `i` is falsified. If `i` is in `h`, it queries the later pigeons in
`h`, reaching a falsified hole clause if one of them is there, and otherwise continues with the
next pigeon and the free holes other than `h`. By induction on the number of free holes, the tree
has Ehrenfeucht–Haussler rank at most `n`, so it gives clause space `n + 2`
(`Cslib.DecisionTree.FindsFalsifiedClause.refutableInSpace`).

## Main results

* `Cslib.Logic.PL.CNF.add_two_le_of_refutableInSpace_pigeonhole`: the lower bound `n + 2`.
* `Cslib.Logic.PL.CNF.refutableInSpace_pigeonhole`: the upper bound `n + 2`.
* `Cslib.Logic.PL.CNF.refutableInSpace_pigeonhole_iff`: the exact clause space.

## References

* [J. Torán, *Space and width in propositional resolution*][Toran2004]
-/

public section

namespace Cslib.Logic.PL

open Finset

namespace WidePigeonhole

variable {m n : ℕ}

/-! ### Implication by partial matchings -/

/-- A set of pigeon–hole pairs is a partial matching: no two pairs share a pigeon or a hole. -/
private def IsMatching (α : Finset (Fin m × Fin n)) : Prop :=
  ∀ x ∈ α, ∀ y ∈ α, (x.1 = y.1 ∨ x.2 = y.2) → x = y

/-- `α` implies `c` if every matching containing `α`, read as an assignment, satisfies `c`. -/
private def MatchImplies (α : Finset (Fin m × Fin n)) (c : Clause (Fin m × Fin n)) : Prop :=
  ∀ β : Finset (Fin m × Fin n), IsMatching β → α ⊆ β → c.eval (fun x => decide (x ∈ β)) = true

private theorem IsMatching.mono {α β : Finset (Fin m × Fin n)} (h : IsMatching β)
    (hαβ : α ⊆ β) : IsMatching α :=
  fun x hx y hy => h x (hαβ hx) y (hαβ hy)

private theorem MatchImplies.mono {α β : Finset (Fin m × Fin n)} {c : Clause (Fin m × Fin n)}
    (h : MatchImplies α c) (hαβ : α ⊆ β) : MatchImplies β c :=
  fun γ hγ hβγ => h γ hγ (hαβ.trans hβγ)

/-- **Locality**: a clause implied by a matching is implied by at most one of its pairs. Otherwise
the empty set and each pair have a matching extension falsifying the clause; then the matching
together with the variables of the negative literals is a matching extension falsifying it. -/
private theorem MatchImplies.exists_card_le_one {α : Finset (Fin m × Fin n)}
    {c : Clause (Fin m × Fin n)} (hα : IsMatching α) (h : MatchImplies α c) :
    ∃ e ⊆ α, #e ≤ 1 ∧ MatchImplies e c := by
  by_contra! hne
  have h₀ : ¬ MatchImplies (∅ : Finset (Fin m × Fin n)) c :=
    hne ∅ (empty_subset _) (by simp)
  have h₁ : ∀ x ∈ α, ¬ MatchImplies {x} c := fun x hx =>
    hne {x} (singleton_subset_iff.2 hx) (by simp)
  simp only [MatchImplies, not_forall, Bool.not_eq_true, exists_prop] at h₀ h₁
  obtain ⟨β₀, hβ₀, -, hc₀⟩ := h₀
  choose! β hβ hxβ hcβ using h₁
  replace hxβ : ∀ x ∈ α, x ∈ β x := fun x hx => singleton_subset_iff.1 (hxβ x hx)
  -- `N`: the variables of the negative literals of `c`
  let N : Finset (Fin m × Fin n) := ((c.filter fun l => l.2 = false).map Prod.fst).toFinset
  have hfalse : ∀ {γ : Finset (Fin m × Fin n)}, c.eval (fun x => decide (x ∈ γ)) = false →
      ∀ l ∈ c, decide (l.1 ∈ γ) ≠ l.2 := fun {γ} hγ l hl hl' => by
    have := (Clause.eval_eq_true_iff (fun x => decide (x ∈ γ)) c).2 ⟨l, hl, hl'⟩
    rw [hγ] at this
    exact Bool.false_ne_true this
  have hN : ∀ y ∈ N, (y, false) ∈ c := by
    intro y hy
    simp only [N, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at hy
    obtain ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩ := hy
    simp only at hb
    exact hb ▸ hz
  have hNβ : ∀ {γ : Finset (Fin m × Fin n)}, c.eval (fun x => decide (x ∈ γ)) = false →
      N ⊆ γ := fun {γ} hγ y hy => by
    simpa using hfalse hγ _ (hN y hy)
  have hPβ : ∀ {γ : Finset (Fin m × Fin n)}, c.eval (fun x => decide (x ∈ γ)) = false →
      ∀ z, (z, true) ∈ c → z ∉ γ := fun {γ} hγ z hz hzγ => by
    simpa [hzγ] using hfalse hγ _ hz
  -- `α ∪ N` is a matching containing `α` that falsifies `c`
  have hmatch : IsMatching (α ∪ N) := by
    intro x hx y hy hxy
    rcases mem_union.1 hx with hx | hx <;> rcases mem_union.1 hy with hy | hy
    · exact hα x hx y hy hxy
    · exact hβ x hx x (hxβ x hx) y (hNβ (hcβ x hx) hy) hxy
    · exact (hβ y hy y (hxβ y hy) x (hNβ (hcβ y hy) hx) (hxy.imp Eq.symm Eq.symm)).symm
    · exact hβ₀ x (hNβ hc₀ hx) y (hNβ hc₀ hy) hxy
  obtain ⟨⟨z, b⟩, hz, hzb⟩ := (Clause.eval_eq_true_iff _ c).1 (h _ hmatch subset_union_left)
  cases b with
  | true =>
    simp only [decide_eq_true_eq, mem_union] at hzb
    rcases hzb with hzα | hzN
    · exact hPβ (hcβ _ hzα) z hz (hxβ _ hzα)
    · exact hPβ hc₀ z hz (hNβ hc₀ hzN)
  | false =>
    simp only [decide_eq_false_iff_not, mem_union, not_or] at hzb
    exact hzb.2 (List.mem_toFinset.2 (List.mem_map.2
      ⟨(z, false), List.mem_filter.2 ⟨hz, by simp⟩, rfl⟩))

/-- **Shrinking**: the clauses of `M` implied by a matching are implied by at most `#M` of its
pairs. -/
private theorem exists_subset_card_le {α : Finset (Fin m × Fin n)} (hα : IsMatching α)
    (M : Finset (Clause (Fin m × Fin n))) (hM : ∀ c ∈ M, MatchImplies α c) :
    ∃ α' ⊆ α, #α' ≤ #M ∧ ∀ c ∈ M, MatchImplies α' c := by
  induction M using Finset.induction_on with
  | empty => exact ⟨∅, empty_subset _, by simp, by simp⟩
  | @insert c M hcM ih =>
    obtain ⟨α', hα'α, hα'M, hα'⟩ := ih fun d hd => hM d (mem_insert_of_mem hd)
    obtain ⟨e, heα, he, hec⟩ := (hM c (mem_insert_self _ _)).exists_card_le_one hα
    refine ⟨α' ∪ e, union_subset hα'α heα, ?_, ?_⟩
    · rw [card_insert_of_notMem hcM]
      exact (card_union_le _ _).trans (by omega)
    · intro d hd
      rcases mem_insert.1 hd with rfl | hd
      exacts [hec.mono subset_union_right, (hα' d hd).mono subset_union_left]

/-- Fewer than `n` pairs leave a hole free. -/
private theorem exists_hole_free {α : Finset (Fin m × Fin n)} (h : #α < n) :
    ∃ j, ∀ x ∈ α, x.2 ≠ j := by
  obtain ⟨j, -, hj⟩ := exists_mem_notMem_of_card_lt_card (s := α.image Prod.snd)
    (t := univ) (card_image_le.trans_lt (by rwa [card_univ, Fintype.card_fin]))
  exact ⟨j, fun x hx hxj => hj (hxj ▸ mem_image_of_mem _ hx)⟩

/-- A matching containing a pair of pigeon `i` implies the pigeon clause of `i`. -/
private theorem matchImplies_pigeonClause {α : Finset (Fin m × Fin n)} {x : Fin m × Fin n}
    (hx : x ∈ α) : MatchImplies α (CNF.pigeonClause n x.1) := fun β _ hαβ => by
  rw [CNF.eval_pigeonClause]
  exact ⟨x.2, by simpa using hαβ hx⟩

/-- Every matching implies the hole clauses of two different pigeons. -/
private theorem matchImplies_holeClause (α : Finset (Fin m × Fin n)) {i i' : Fin m}
    (hii' : i ≠ i') (j : Fin n) : MatchImplies α (CNF.holeClause i i' j) := fun β hβ _ => by
  rw [CNF.eval_holeClause]
  by_contra! h
  simp only [ne_eq, decide_eq_false_iff_not, not_not] at h
  exact hii' (congrArg Prod.fst (hβ _ h.1 _ h.2 (Or.inr rfl)))

/-- Implication by a matching is closed under resolution. -/
private theorem MatchImplies.resolvent {α : Finset (Fin m × Fin n)}
    {c₁ c₂ : Clause (Fin m × Fin n)} (v : Fin m × Fin n) (h₁ : MatchImplies α c₁)
    (h₂ : MatchImplies α c₂) : MatchImplies α (c₁.resolvent c₂ v) := fun β hβ hαβ =>
  Clause.eval_resolvent v (h₁ β hβ hαβ) (h₂ β hβ hαβ)

/-- No matching implies the empty clause. -/
private theorem not_matchImplies_nil {α : Finset (Fin m × Fin n)} (hα : IsMatching α) :
    ¬ MatchImplies α [] := fun h => by
  simpa using h α hα subset_rfl

/-- Adding a pair with a new pigeon and a free hole to a matching gives a matching. -/
private theorem IsMatching.insert {α : Finset (Fin m × Fin n)} (hα : IsMatching α)
    {x : Fin m × Fin n} (h₁ : ∀ y ∈ α, y.1 ≠ x.1) (h₂ : ∀ y ∈ α, y.2 ≠ x.2) :
    IsMatching (insert x α) := by
  intro y hy z hz hyz
  rcases mem_insert.1 hy with hyx | hyα <;> rcases mem_insert.1 hz with hzx | hzα
  · rw [hyx, hzx]
  · subst hyx
    exact absurd (hyz.imp Eq.symm Eq.symm) (by simpa using ⟨h₁ z hzα, h₂ z hzα⟩)
  · subst hzx
    exact absurd hyz (by simpa using ⟨h₁ y hyα, h₂ y hyα⟩)
  · exact hα y hyα z hzα hyz

/-! ### The invariant of refutations in clause space `n + 1` -/

/-- A matching implying every clause of `M`. -/
private def Good (α : Finset (Fin m × Fin n)) (M : Finset (Clause (Fin m × Fin n))) : Prop :=
  IsMatching α ∧ ∀ c ∈ M, MatchImplies α c

/-- The invariant: a configuration is implied by a matching, except perhaps for one pigeon
clause. -/
private def Inv (M : Finset (Clause (Fin m × Fin n))) : Prop :=
  (∃ α, Good α M) ∨ ∃ i : Fin m, ∃ α, Good α (M.erase (CNF.pigeonClause n i))

private theorem Good.mono {α : Finset (Fin m × Fin n)} {M N : Finset (Clause (Fin m × Fin n))}
    (h : Good α M) (hNM : N ⊆ M) : Good α N :=
  ⟨h.1, fun c hc => h.2 c (hNM hc)⟩

/-- A configuration of at most `n` clauses satisfying the invariant is implied by a matching: the
pairs implying the other clauses leave a hole free for the exceptional pigeon clause. -/
private theorem Inv.exists_good {M : Finset (Clause (Fin m × Fin n))} (h : Inv M)
    (hM : #M ≤ n) : ∃ α, Good α M := by
  rcases h with h | ⟨i, α, hα, hαM⟩
  · exact h
  by_cases hiM : CNF.pigeonClause n i ∈ M
  swap
  · exact ⟨α, hα, by rwa [erase_eq_of_notMem hiM] at hαM⟩
  obtain ⟨α', hα'α, hα'card, hα'⟩ := exists_subset_card_le hα _ hαM
  rw [card_erase_of_mem hiM] at hα'card
  have hMpos := card_pos.2 ⟨_, hiM⟩
  have hα'm := hα.mono hα'α
  by_cases hi : ∃ x ∈ α', x.1 = i
  · obtain ⟨x, hx, rfl⟩ := hi
    refine ⟨α', hα'm, fun c hc => ?_⟩
    by_cases hcx : c = CNF.pigeonClause n x.1
    · exact hcx ▸ matchImplies_pigeonClause hx
    · exact hα' c (mem_erase.2 ⟨hcx, hc⟩)
  · push Not at hi
    obtain ⟨j, hj⟩ := exists_hole_free (α := α') (by omega)
    refine ⟨insert (i, j) α', hα'm.insert hi hj, fun c hc => ?_⟩
    by_cases hci : c = CNF.pigeonClause n i
    · exact hci ▸ matchImplies_pigeonClause (x := (i, j)) (mem_insert_self _ _)
    · exact (hα' c (mem_erase.2 ⟨hci, hc⟩)).mono (subset_insert _ _)

/-- A step of a refutation in clause space at most `n + 1` preserves the invariant. A step that
adds a new clause starts from at most `n` clauses, which are implied by a matching; a new pigeon
clause becomes the exceptional clause. -/
private theorem Inv.step {s : ℕ} (hs : s ≤ n + 1) {M M' : Finset (Clause (Fin m × Fin n))}
    {mv : ConfigMove (Fin m × Fin n)} (h : ((CNF.pigeonhole m n).configLTS s).Tr M mv M')
    (hM : Inv M) : Inv M' := by
  obtain ⟨hstep, hcard⟩ := h
  have hins : ∀ {x}, M' = insert x M → x ∉ M → ∃ α, Good α M := fun {x} hM' hx => by
    refine hM.exists_good ?_
    rw [hM', card_insert_of_notMem hx] at hcard
    omega
  cases hstep with
  | erase c =>
    rcases hM with ⟨α, hα⟩ | ⟨i, α, hα⟩
    · exact .inl ⟨α, hα.mono (erase_subset _ _)⟩
    · refine .inr ⟨i, α, hα.mono ?_⟩
      rw [erase_right_comm]
      exact erase_subset _ _
  | @download c hc =>
    by_cases hcM : c ∈ M
    · rwa [insert_eq_of_mem hcM]
    obtain ⟨α, hα⟩ := hins rfl hcM
    rcases CNF.mem_pigeonhole.1 hc with ⟨i, rfl⟩ | ⟨i, i', j, hii', rfl⟩
    · exact .inr ⟨i, α, hα.mono (erase_insert_subset _ _)⟩
    · refine .inl ⟨α, hα.1, fun d hd => ?_⟩
      rcases mem_insert.1 hd with rfl | hd
      exacts [matchImplies_holeClause α hii'.ne j, hα.2 d hd]
  | @infer c₁ c₂ v h₁ h₂ hv₁ hv₂ =>
    by_cases hcM : c₁.resolvent c₂ v ∈ M
    · rwa [insert_eq_of_mem hcM]
    obtain ⟨α, hα⟩ := hins rfl hcM
    refine .inl ⟨α, hα.1, fun d hd => ?_⟩
    rcases mem_insert.1 hd with rfl | hd
    exacts [(hα.2 _ h₁).resolvent v (hα.2 _ h₂), hα.2 d hd]

private theorem Inv.mTr {s : ℕ} (hs : s ≤ n + 1) {M M' : Finset (Clause (Fin m × Fin n))}
    {ms : List (ConfigMove (Fin m × Fin n))}
    (h : ((CNF.pigeonhole m n).configLTS s).MTr M ms M') (hM : Inv M) : Inv M' := by
  induction h with
  | refl => exact hM
  | stepL hstep _ ih => exact ih (hM.step hs hstep)

/-- With at least one hole, a configuration satisfying the invariant does not contain the empty
clause. -/
private theorem Inv.nil_notMem (hn : 1 ≤ n) {M : Finset (Clause (Fin m × Fin n))} (h : Inv M) :
    [] ∉ M := by
  intro hnil
  rcases h with ⟨α, hα⟩ | ⟨i, α, hα⟩
  · exact not_matchImplies_nil hα.1 (hα.2 _ hnil)
  · have hne : ([] : Clause (Fin m × Fin n)) ≠ CNF.pigeonClause n i := fun h => by
      have := congrArg List.length h
      rw [List.length_nil, CNF.length_pigeonClause] at this
      omega
    exact not_matchImplies_nil hα.1 (hα.2 _ (mem_erase.2 ⟨hne, hnil⟩))

/-! ### A DPLL tree of rank `n` -/

/-- Having found pigeon `i` in hole `h`, query the pigeons `R` in hole `h`, and continue with `t`
if none of them is there. -/
private def holeChain (i : Fin m) (h : Fin n)
    (t : DecisionTree (Fin m × Fin n) (Clause (Fin m × Fin n))) :
    List (Fin m) → DecisionTree (Fin m × Fin n) (Clause (Fin m × Fin n))
  | [] => t
  | i' :: R => .node (i', h) (holeChain i h t R) (.leaf (CNF.holeClause i i' h))

mutual

/-- The DPLL tree for the pigeons `P` and the free holes `H`. -/
private def phpTree :
    List (Fin m) → List (Fin n) → DecisionTree (Fin m × Fin n) (Clause (Fin m × Fin n))
  | [], _ => .leaf []
  | i :: rest, H => spine i rest H H

/-- Query pigeon `i` in the holes `L`, among the free holes `H`. -/
private def spine (i : Fin m) (rest : List (Fin m)) (H : List (Fin n)) :
    List (Fin n) → DecisionTree (Fin m × Fin n) (Clause (Fin m × Fin n))
  | [] => .leaf (CNF.pigeonClause n i)
  | h :: L => .node (i, h) (spine i rest H L) (holeChain i h (phpTree rest (H.erase h)) rest)

end

/-- `t` reaches a clause of `PHP^m_n` falsified by `σ`. -/
private def Finds (σ : Fin m × Fin n → Bool)
    (t : DecisionTree (Fin m × Fin n) (Clause (Fin m × Fin n))) : Prop :=
  t.eval σ ∈ CNF.pigeonhole m n ∧ (t.eval σ).eval σ = false

private theorem Finds.node_of_true {σ : Fin m × Fin n → Bool} {v : Fin m × Fin n}
    {t₀ t₁ : DecisionTree (Fin m × Fin n) (Clause (Fin m × Fin n))} (hv : σ v = true)
    (h : Finds σ t₁) : Finds σ (.node v t₀ t₁) := by
  simpa only [Finds, DecisionTree.eval, hv, Bool.cond_true] using h

private theorem Finds.node_of_false {σ : Fin m × Fin n → Bool} {v : Fin m × Fin n}
    {t₀ t₁ : DecisionTree (Fin m × Fin n) (Clause (Fin m × Fin n))} (hv : σ v = false)
    (h : Finds σ t₀) : Finds σ (.node v t₀ t₁) := by
  simpa only [Finds, DecisionTree.eval, hv, Bool.cond_false] using h

private theorem finds_holeChain {σ : Fin m × Fin n → Bool} {i : Fin m} {h : Fin n}
    {t : DecisionTree (Fin m × Fin n) (Clause (Fin m × Fin n))} (hi : σ (i, h) = true) :
    ∀ {R : List (Fin m)}, (∀ i' ∈ R, i < i') → ((∀ i' ∈ R, σ (i', h) = false) → Finds σ t) →
      Finds σ (holeChain i h t R)
  | [], _, ht => ht (by simp)
  | i' :: R, hR, ht => by
    rw [holeChain]
    by_cases hσ : σ (i', h) = true
    · refine Finds.node_of_true hσ
        ⟨CNF.mem_pigeonhole.2 (.inr ⟨i, i', h, hR i' (by simp), rfl⟩), ?_⟩
      simp [DecisionTree.eval, CNF.holeClause, hi, hσ]
    · rw [Bool.not_eq_true] at hσ
      refine Finds.node_of_false hσ
        (finds_holeChain hi (fun i'' h'' => hR i'' (by simp [h''])) fun h' => ?_)
      refine ht fun i'' h'' => ?_
      rcases List.mem_cons.1 h'' with rfl | h''
      exacts [hσ, h' i'' h'']

/-- The DPLL tree finds a falsified clause on every assignment that puts the pigeons `P`, in
increasing order and more numerous than the free holes `H`, in no other hole. -/
private theorem finds_phpTree {σ : Fin m × Fin n → Bool} :
    ∀ {P : List (Fin m)} {H : List (Fin n)}, P.Pairwise (· < ·) → H.length < P.length →
      (∀ i ∈ P, ∀ j ∉ H, σ (i, j) = false) → Finds σ (phpTree P H)
  | [], _, _, hlen, _ => absurd hlen (Nat.not_lt_zero _)
  | i :: rest, H, hP, hlen, hσ => by
    rw [List.pairwise_cons] at hP
    rw [phpTree]
    -- induction over the holes `L` still to be queried for pigeon `i`
    suffices ∀ L : List (Fin n), (∀ h ∈ L, h ∈ H) → (∀ j ∈ H, j ∉ L → σ (i, j) = false) →
        Finds σ (spine i rest H L) from this H (fun _ => id) (fun _ _ hjH => absurd ‹_› hjH)
    intro L
    induction L with
    | nil =>
      intro _ hL
      rw [spine]
      refine ⟨CNF.mem_pigeonhole.2 (.inl ⟨i, rfl⟩), ?_⟩
      simp only [DecisionTree.eval]
      rw [Bool.eq_false_iff, ne_eq, CNF.eval_pigeonClause, not_exists]
      intro j hj
      by_cases hjH : j ∈ H
      · rw [hL j hjH List.not_mem_nil] at hj
        exact Bool.false_ne_true hj
      · rw [hσ i List.mem_cons_self j hjH] at hj
        exact Bool.false_ne_true hj
    | cons h L ih =>
      intro hLH hL
      rw [spine]
      by_cases hih : σ (i, h) = true
      · have hhH := hLH h List.mem_cons_self
        refine Finds.node_of_true hih
          (finds_holeChain hih hP.1 fun hR => finds_phpTree hP.2 ?_ ?_)
        · rw [List.length_erase_of_mem hhH]
          have := List.length_pos_of_mem hhH
          simp only [List.length_cons] at hlen
          omega
        · intro i' hi' j hj
          by_cases hjh : j = h
          · exact hjh ▸ hR i' hi'
          · exact hσ i' (List.mem_cons_of_mem _ hi') j fun hjH =>
              hj ((List.mem_erase_of_ne hjh).2 hjH)
      · rw [Bool.not_eq_true] at hih
        refine Finds.node_of_false hih
          (ih (fun h' h'' => hLH h' (List.mem_cons_of_mem _ h'')) fun j hj hjL => ?_)
        by_cases hjh : j = h
        · exact hjh ▸ hih
        · exact hL j hj (by simp [hjh, hjL])

private theorem rank_holeChain_le (i : Fin m) (h : Fin n)
    (t : DecisionTree (Fin m × Fin n) (Clause (Fin m × Fin n))) :
    ∀ R : List (Fin m), (holeChain i h t R).rank ≤ max 1 t.rank
  | [] => le_max_right _ _
  | i' :: R => by
    have := rank_holeChain_le i h t R
    rw [holeChain, DecisionTree.rank_node, DecisionTree.rank_leaf]
    split_ifs <;> omega

private theorem rank_spine_le (i : Fin m) (rest : List (Fin m)) (H : List (Fin n)) {c : ℕ}
    (hc : ∀ h ∈ H, (holeChain i h (phpTree rest (H.erase h)) rest).rank ≤ c) :
    ∀ L : List (Fin n), (∀ h ∈ L, h ∈ H) → (spine i rest H L).rank ≤ c + 1
  | [], _ => by rw [spine, DecisionTree.rank_leaf]; omega
  | h :: L, hL => by
    have ih := rank_spine_le i rest H hc L fun h' h'' => hL h' (List.mem_cons_of_mem _ h'')
    have := hc h (hL h List.mem_cons_self)
    rw [spine, DecisionTree.rank_node]
    split_ifs <;> omega

/-- The DPLL tree has rank at most the number of free holes. -/
private theorem rank_phpTree_le :
    ∀ (P : List (Fin m)) (H : List (Fin n)), (phpTree P H).rank ≤ H.length
  | [], _ => by rw [phpTree, DecisionTree.rank_leaf]; omega
  | i :: rest, [] => by rw [phpTree, spine, DecisionTree.rank_leaf]; omega
  | i :: rest, [h] => by
    have h1 := rank_holeChain_le i h (phpTree rest []) rest
    have h2 := rank_phpTree_le rest []
    rw [List.length_nil, Nat.le_zero] at h2
    rw [h2] at h1
    rw [phpTree, spine, spine, List.erase_cons_head, DecisionTree.rank_node,
      DecisionTree.rank_leaf, List.length_singleton]
    split_ifs <;> omega
  | i :: rest, h₁ :: h₂ :: H => by
    rw [phpTree]
    refine (rank_spine_le i rest _ (c := H.length + 1) (fun h hh => ?_) _ fun _ => id).trans
      (by simp)
    refine (rank_holeChain_le _ _ _ _).trans (max_le (by omega) ?_)
    refine (rank_phpTree_le rest _).trans ?_
    rw [List.length_erase_of_mem hh]
    simp

private theorem findsFalsifiedClause_phpTree (h : n < m) :
    (phpTree (List.finRange m) (List.finRange n)).FindsFalsifiedClause (CNF.pigeonhole m n) :=
  fun _ => finds_phpTree (List.pairwise_lt_finRange m) (by simpa using h)
    fun _ _ j hj => absurd (List.mem_finRange j) hj

end WidePigeonhole

namespace CNF

/-- **Torán's lower bound** [Torán, Section 4][Toran2004]: with at least one hole, every resolution
refutation of the pigeonhole formula `PHP^m_n` in clause space `s` has `n + 2 ≤ s`, whatever the
number `m` of pigeons. The survey states space `n + 1` for a pebble game that shifts a pebble from
a premise to the resolvent, credited to Torán's CSL 1999 paper, which was not inspected; clause
space here is one larger, and the proof is a reconstruction. -/
theorem add_two_le_of_refutableInSpace_pigeonhole {m n s : ℕ} (hn : 1 ≤ n)
    (h : (pigeonhole m n).RefutableInSpace s) : n + 2 ≤ s := by
  by_contra! hs
  obtain ⟨ms, M, hM, hnil⟩ := h
  exact (WidePigeonhole.Inv.mTr (by omega) hM
    (.inl ⟨∅, fun x hx => by simp at hx, by simp⟩)).nil_notMem hn hnil

/-- **Torán's upper bound** [Torán, Section 4][Toran2004]: with more pigeons than holes, the
pigeonhole formula `PHP^m_n` is refutable in clause space `n + 2`, whatever the number `m` of
pigeons. This is the survey's space `n + 1`, for a pebble game that shifts a pebble from a premise
to the resolvent, in the convention of `Cslib.Logic.PL.CNF.configLTS`; the proof, by a DPLL tree
of rank at most `n`, is a reconstruction. -/
theorem refutableInSpace_pigeonhole {m n : ℕ} (h : n < m) :
    (pigeonhole m n).RefutableInSpace (n + 2) :=
  (WidePigeonhole.findsFalsifiedClause_phpTree h).refutableInSpace.mono <| by
    have := WidePigeonhole.rank_phpTree_le (List.finRange m) (List.finRange n)
    rw [List.length_finRange] at this
    omega

/-- **The clause space of the pigeonhole formula is `n + 2`** [Torán, Section 4][Toran2004]: for
`0 < n < m`, `PHP^m_n` is refutable in clause space `s` exactly when `n + 2 ≤ s`. -/
theorem refutableInSpace_pigeonhole_iff {m n s : ℕ} (hn : 0 < n) (h : n < m) :
    (pigeonhole m n).RefutableInSpace s ↔ n + 2 ≤ s :=
  ⟨add_two_le_of_refutableInSpace_pigeonhole hn, (refutableInSpace_pigeonhole h).mono⟩

end CNF

end Cslib.Logic.PL
