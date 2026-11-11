/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Resolution.ExistentialPebble
public import CslibFrontier.Logics.Propositional.Resolution.Space

/-!
# Clause space bounds width

**Atserias and Dalmau's inequality** [Atserias and Dalmau, Theorem 3][AtseriasDalmau2008]: a
formula of clauses of width at most `k` that is refutable in clause space `s` is refutable in width
`s + k - 3` (`Cslib.Logic.PL.CNF.RefutableInSpace.refutableInWidth`). The exact constant
`s + k - 3` is that of [Filmus, Lauria, Mikša, Nordström and Vinyals,
Theorem 1][FilmusLauriaMiksaNordstromVinyals2014], whose statement we follow. They state it as a
result of Atserias and Dalmau, labelling it "Theorem 1 ([2])" with [2] the journal version of
Atserias and Dalmau's paper:

> Let F be a k-CNF formula and let π : F ⊢ ⊥ be a resolution refutation in space Sp(π) = s. Then
> there is a resolution refutation π′ of F in width W(π′) ≤ s + k − 3.

That paper assumes that `F` does not contain the empty clause; we do not, since a formula containing
it is refutable in width `0`. Clauses there are sets, and weakening is optional; here they are lists
(`Cslib.Logic.PL.Clause.width` counts distinct literals), and neither the space refutation nor the
width refutation uses weakening. Lower bounds on width thus give lower bounds on clause space
(`Cslib.Logic.PL.CNF.RefutableInSpace.add_four_le`).

The proof follows Atserias and Dalmau, and works for any winning strategy `S` for Duplicator in
the existential `p`-pebble game (`Cslib.Logic.PL.CNF.DuplicatorStrategy`): if `φ` has clauses of
width at most `k` and is refutable in space `s`, then `p + 3 ≤ s + k`
(`Cslib.Logic.PL.CNF.DuplicatorStrategy.add_three_le`). A position of `S` on at most `p - k`
variables extends to a position satisfying any given clause of `φ`, which it cannot falsify. Then,
along a refutation in space `s`, every set `N` of fewer than `s` clauses of the current
configuration is satisfied by a position of `S` on at most `|N|` variables: after a download of
`A ∈ N`, satisfy the other clauses of `N` and extend to satisfy `A`; after an inference of `R ∈ N`,
satisfy the parents of `R` instead, which together satisfy `R`; and keep only one satisfying
variable per clause (the Locality Lemma, [Atserias and Dalmau, Lemma 4][AtseriasDalmau2008]).
Applied to the set of the empty clause, this is a contradiction. Atserias and Dalmau (Lemma 5)
keep one assignment satisfying the whole configuration; asking only for sets of fewer than `s`
clauses saves one in the width bound and gives the constant of Filmus et al. The constant stated in
Atserias and Dalmau's Theorem 3 may be weaker and is not quoted or claimed here.

If `φ` has no refutation of width `w` and no clause of width `w + 1`, Duplicator wins with `w + 1`
pebbles [Atserias and Dalmau, Lemma 2][AtseriasDalmau2008]
(`Cslib.Logic.PL.CNF.DuplicatorStrategy.ofNotRefutableInWidth`), which gives `add_four_le`; if some
clause has width `w + 1`, then `w < k` and the bound `3 ≤ s` suffices.

## Main results

* `Cslib.Logic.PL.CNF.DuplicatorStrategy.add_three_le`: a clause-space lower bound from a
  Duplicator strategy.
* `Cslib.Logic.PL.CNF.RefutableInSpace.refutableInWidth`: **the Atserias–Dalmau inequality**.
* `Cslib.Logic.PL.CNF.RefutableInSpace.add_four_le`: its contrapositive, a clause-space lower bound
  from a width lower bound.

## References

* [A. Atserias, V. Dalmau, *A combinatorial characterization of resolution
  width*][AtseriasDalmau2008]
* [Y. Filmus, M. Lauria, M. Mikša, J. Nordström, M. Vinyals, *From small space to small width in
  resolution*][FilmusLauriaMiksaNordstromVinyals2014]
-/

public section

namespace Cslib.Logic.PL

namespace CNF

variable {V : Type*} [DecidableEq V] {φ : CNF V} {w : ℕ}

/-! ### Satisfying partial assignments

A partial assignment is a total assignment `σ` read only on a finite set `d` of variables;
`Cslib.Logic.PL.CNF.Falsifies σ d c` says that it falsifies `c`. -/

/-- The assignment `σ`, read on `d`, satisfies `c`: some literal of `c` is on a variable of `d`
and true under `σ`. -/
private def Satisfies (σ : V → Bool) (d : Finset V) (c : Clause V) : Prop :=
  ∃ l ∈ c, l.1 ∈ d ∧ σ l.1 = l.2

/-- **Satisfying a clause of the formula**: a position of a `p`-pebble strategy on `d` extends to
a position satisfying a clause `A ∈ φ` and agreeing with it on `d`, provided
`|d| + width A ≤ p`. -/
private theorem DuplicatorStrategy.exists_satisfies {p : ℕ} (S : DuplicatorStrategy φ p)
    {σ : V → Bool} {d : Finset V} (hσ : S.Mem σ d) {A : Clause V} (hA : A ∈ φ)
    (hdA : d.card + A.width ≤ p) :
    ∃ σ' d', S.Mem σ' d' ∧ d ⊆ d' ∧ (∀ x ∈ d, σ' x = σ x) ∧ Satisfies σ' d' A := by
  obtain ⟨σ', hσ', hag⟩ := S.exists_extend_union hσ (A.toFinset.image Prod.fst)
    ((Nat.add_le_add_left Finset.card_image_le _).trans hdA)
  refine ⟨σ', _, hσ', Finset.subset_union_left, hag, ?_⟩
  by_contra hns
  refine S.not_falsifies hσ' A hA fun l hl => ?_
  refine ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hl)), ?_⟩
  exact fun he => hns ⟨l, hl, Finset.mem_union_right _
    (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hl)), he⟩

omit [DecidableEq V] in
/-- Satisfaction survives enlarging the domain, keeping the assignment on it. -/
private theorem Satisfies.mono {σ σ' : V → Bool} {d d' : Finset V} {c : Clause V}
    (h : Satisfies σ d c) (hd : d ⊆ d') (hσ : ∀ x ∈ d, σ' x = σ x) : Satisfies σ' d' c :=
  let ⟨l, hl, hd', he⟩ := h
  ⟨l, hl, hd hd', (hσ _ hd').trans he⟩

/-- An assignment satisfying both parents satisfies the resolvent. -/
private theorem Satisfies.resolvent {σ : V → Bool} {d : Finset V} {c₁ c₂ : Clause V} (v : V)
    (h₁ : Satisfies σ d c₁) (h₂ : Satisfies σ d c₂) : Satisfies σ d (c₁.resolvent c₂ v) := by
  obtain ⟨l₁, hl₁, hd₁, he₁⟩ := h₁
  obtain ⟨l₂, hl₂, hd₂, he₂⟩ := h₂
  by_cases hv₁ : l₁ = (v, true)
  · subst hv₁
    refine ⟨l₂, Clause.mem_resolvent.2 (Or.inr ⟨hl₂, ?_⟩), hd₂, he₂⟩
    rintro rfl
    exact Bool.noConfusion (he₁.symm.trans he₂ : true = false)
  · exact ⟨l₁, Clause.mem_resolvent.2 (Or.inl ⟨hl₁, hv₁⟩), hd₁, he₁⟩

omit [DecidableEq V] in
/-- **Locality** [Atserias and Dalmau, Lemma 4][AtseriasDalmau2008]: an assignment satisfying a set
`N` of clauses on `d` satisfies them on a subset of `d` of at most `|N|` variables. -/
private theorem exists_subset_satisfies {σ : V → Bool} {d : Finset V} (N : Finset (Clause V))
    (h : ∀ c ∈ N, Satisfies σ d c) :
    ∃ d' ⊆ d, d'.card ≤ N.card ∧ ∀ c ∈ N, Satisfies σ d' c := by
  classical
  induction N using Finset.induction_on with
  | empty => exact ⟨∅, Finset.empty_subset _, le_rfl, by simp⟩
  | @insert c N hcN ih =>
    obtain ⟨d', hd', hcard, hsat⟩ := ih fun c' hc' => h c' (Finset.mem_insert_of_mem hc')
    obtain ⟨l, hl, hld, he⟩ := h c (Finset.mem_insert_self _ _)
    refine ⟨insert l.1 d', Finset.insert_subset hld hd', ?_, fun c' hc' => ?_⟩
    · rw [Finset.card_insert_of_notMem hcN]
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hcard)
    · rcases Finset.mem_insert.1 hc' with rfl | hc'
      · exact ⟨l, hl, Finset.mem_insert_self _ _, he⟩
      · exact (hsat c' hc').mono (Finset.subset_insert _ _) fun _ _ => rfl

/-! ### The invariant -/

/-- The invariant along a refutation in space `s`, for a Duplicator strategy `S`: every set `N` of
fewer than `s` clauses of the configuration `M` is satisfied by a position of `S` on at most `|N|`
variables. -/
private def Inv {p : ℕ} (S : DuplicatorStrategy φ p) (s : ℕ) (M : Finset (Clause V)) : Prop :=
  ∀ N ⊆ M, N.card + 1 ≤ s →
    ∃ σ d, S.Mem σ d ∧ d.card ≤ N.card ∧ ∀ c ∈ N, Satisfies σ d c

/-- The invariant holds for the empty configuration. -/
private theorem inv_empty {p : ℕ} (S : DuplicatorStrategy φ p) (s : ℕ) : Inv S s ∅ := by
  intro N hN _
  rw [Finset.subset_empty.1 hN]
  obtain ⟨σ, d, hσ⟩ := S.nonempty
  exact ⟨σ, ∅, S.restrict hσ (Finset.empty_subset _), by simp, by simp⟩

/-- The invariant survives one step of a refutation in space `s`, for a `p`-pebble strategy with
`s + k ≤ p + 2`. -/
private theorem Inv.step {k p s : ℕ} {S : DuplicatorStrategy φ p} (hk : ∀ c ∈ φ, c.width ≤ k)
    (hp : s + k ≤ p + 2) {M M' : Finset (Clause V)} {m : ConfigMove V} (h : Inv S s M)
    (hstep : (φ.configLTS s).Tr M m M') : Inv S s M' := by
  obtain ⟨hstep, hcard⟩ := hstep
  intro N hN hNs
  cases hstep with
  | @download A hA =>
    by_cases hAN : A ∈ N
    · -- satisfy the other clauses of `N`, then extend to satisfy `A`
      have hN₀ : N.erase A ⊆ M := fun c hc => by
        rcases Finset.mem_insert.1 (hN (Finset.mem_of_mem_erase hc)) with rfl | hc'
        exacts [absurd rfl (Finset.ne_of_mem_erase hc), hc']
      have hcard₀ := Finset.card_erase_add_one hAN
      obtain ⟨σ, d, hσ, hd, hsat⟩ := h _ hN₀ (by omega)
      have hAk := hk A hA
      obtain ⟨σ', d', hσ', hdd', hag, hA'⟩ := S.exists_satisfies hσ hA (by omega)
      have hsat' : ∀ c ∈ N, Satisfies σ' d' c := fun c hc => by
        by_cases hcA : c = A
        · exact hcA ▸ hA'
        · exact (hsat c (Finset.mem_erase.2 ⟨hcA, hc⟩)).mono hdd' hag
      obtain ⟨d'', hd'', hcard'', hsat''⟩ := exists_subset_satisfies N hsat'
      exact ⟨σ', d'', S.restrict hσ' hd'', hcard'', hsat''⟩
    · refine h N (fun c hc => ?_) hNs
      rcases Finset.mem_insert.1 (hN hc) with rfl | hc'
      exacts [absurd hc hAN, hc']
  | @infer c₁ c₂ v h₁ h₂ _ _ =>
    by_cases hR : c₁.resolvent c₂ v ∈ N ∧ c₁.resolvent c₂ v ∉ M
    · -- satisfy the parents of the resolvent and the other clauses of `N`
      obtain ⟨hRN, hRM⟩ := hR
      have hMs : M.card + 1 ≤ s := by
        rw [Finset.card_insert_of_notMem hRM] at hcard
        exact hcard
      set N' := insert c₁ (insert c₂ (N.erase (c₁.resolvent c₂ v)))
      have hN' : N' ⊆ M := by
        refine Finset.insert_subset h₁ (Finset.insert_subset h₂ fun c hc => ?_)
        rcases Finset.mem_insert.1 (hN (Finset.mem_of_mem_erase hc)) with rfl | hc'
        exacts [absurd rfl (Finset.ne_of_mem_erase hc), hc']
      obtain ⟨σ, d, hσ, -, hsat⟩ := h N' hN' (by
        have := Finset.card_le_card hN'
        omega)
      have hsat' : ∀ c ∈ N, Satisfies σ d c := fun c hc => by
        by_cases hcR : c = c₁.resolvent c₂ v
        · rw [hcR]
          exact (hsat c₁ (Finset.mem_insert_self _ _)).resolvent v
            (hsat c₂ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        · exact hsat c (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.2 ⟨hcR, hc⟩)))
      obtain ⟨d', hd', hcard', hsat''⟩ := exists_subset_satisfies N hsat'
      exact ⟨σ, d', S.restrict hσ hd', hcard', hsat''⟩
    · refine h N (fun c hc => ?_) hNs
      rcases Finset.mem_insert.1 (hN hc) with rfl | hc'
      · by_contra hcM
        exact hR ⟨hc, hcM⟩
      · exact hc'
  | erase c => exact h N (hN.trans (Finset.erase_subset _ _)) hNs

/-- The invariant survives a run of a refutation in space `s`, for a `p`-pebble strategy with
`s + k ≤ p + 2`. -/
private theorem Inv.mTr {k p s : ℕ} {S : DuplicatorStrategy φ p} (hk : ∀ c ∈ φ, c.width ≤ k)
    (hp : s + k ≤ p + 2) {M M' : Finset (Clause V)} {ms : List (ConfigMove V)} (h : Inv S s M)
    (hM : (φ.configLTS s).MTr M ms M') : Inv S s M' := by
  induction hM with
  | refl => exact h
  | stepL hstep _ ih => exact ih (h.step hk hp hstep)

/-! ### The inequality -/

/-- **Duplicator strategies give clause-space lower bounds** [Atserias and Dalmau,
Lemma 5][AtseriasDalmau2008]: if Duplicator wins the existential `p`-pebble game on a formula of
clauses of width at most `k`, its refutations need clause space at least `p + 3 - k`. The constant
is the one that gives that of [Filmus, Lauria, Mikša, Nordström and Vinyals,
Theorem 1][FilmusLauriaMiksaNordstromVinyals2014] with `p = w + 1`; the constant of Atserias and
Dalmau's Lemma 5 is not quoted. -/
theorem DuplicatorStrategy.add_three_le {k p s : ℕ} (S : DuplicatorStrategy φ p)
    (hk : ∀ c ∈ φ, c.width ≤ k) (h : φ.RefutableInSpace s) : p + 3 ≤ s + k := by
  have hφ : [] ∉ φ := fun hφ => by
    obtain ⟨σ, d, hσ⟩ := S.nonempty
    exact S.not_falsifies hσ [] hφ (falsifies_nil σ d)
  have hs := h.three_le hφ
  by_contra hlt
  obtain ⟨ms, M, hM, hnil⟩ := h
  obtain ⟨σ, d, -, -, hsat⟩ := (inv_empty S s).mTr hk (by omega) hM {[]}
    (Finset.singleton_subset_iff.2 hnil) (by rw [Finset.card_singleton]; omega)
  obtain ⟨l, hl, -⟩ := hsat [] (Finset.mem_singleton_self _)
  simp at hl

/-- A formula containing the empty clause is refutable in width `0`. -/
private theorem refutableInWidth_zero_of_nil_mem (hφ : [] ∈ φ) : φ.RefutableInWidth 0 :=
  ⟨[[]], IsProof.nil.mem hφ, List.mem_singleton_self _, by simp⟩

namespace RefutableInSpace

/-- **Width lower bounds give clause-space lower bounds**: if a formula of clauses of width at most
`k` has no refutation of width `w`, its refutations need clause space at least `w + 4 - k`. -/
theorem add_four_le {k s : ℕ} (hk : ∀ c ∈ φ, c.width ≤ k) (hw : ¬ φ.RefutableInWidth w)
    (h : φ.RefutableInSpace s) : w + 4 ≤ s + k := by
  by_cases hkw : ∀ c ∈ φ, c.width ≠ w + 1
  · exact (DuplicatorStrategy.ofNotRefutableInWidth hkw hw).add_three_le hk h
  -- otherwise some clause has width `w + 1`, so `w < k`
  push Not at hkw
  obtain ⟨c, hc, hcw⟩ := hkw
  have hφ : [] ∉ φ := fun hφ => hw ((refutableInWidth_zero_of_nil_mem hφ).mono (Nat.zero_le _))
  have := h.three_le hφ
  have := hk c hc
  omega

/-- **Clause space bounds width** [Atserias and Dalmau, Theorem 3][AtseriasDalmau2008]
[Filmus, Lauria, Mikša, Nordström and Vinyals, Theorem 1][FilmusLauriaMiksaNordstromVinyals2014]: a
formula of clauses of width at most `k` that is refutable in clause space `s` is refutable in width
`s + k - 3`. The exact constant `s + k - 3` is that of Filmus et al., Theorem 1. -/
theorem refutableInWidth {k s : ℕ} (hk : ∀ c ∈ φ, c.width ≤ k) (h : φ.RefutableInSpace s) :
    φ.RefutableInWidth (s + k - 3) := by
  by_contra hw
  have := h.add_four_le hk hw
  omega

end RefutableInSpace

end CNF

end Cslib.Logic.PL
