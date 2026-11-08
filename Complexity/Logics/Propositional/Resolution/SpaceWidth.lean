/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Resolution.Space

/-!
# Clause space bounds width

**Atserias and Dalmau's inequality** [Atserias and Dalmau, Section 4][AtseriasDalmau2008]: a
formula of clauses of width at most `k` that is refutable in clause space `s` is refutable in width
`s + k - 3` (`Cslib.Logic.PL.CNF.RefutableInSpace.refutableInWidth`). We follow the statement of
[Filmus, Lauria, Mikša, Nordström and Vinyals, Theorem 1][FilmusLauriaMiksaNordstromVinyals2014]:

> Let F be a k-CNF formula and let π : F ⊢ ⊥ be a resolution refutation in space Sp(π) = s. Then
> there is a resolution refutation π′ of F in width W(π′) ≤ s + k − 3.

That paper assumes that `F` does not contain the empty clause; we do not, since a formula containing
it is refutable in width `0`. Clauses there are sets, and weakening is optional; here they are lists
(`Cslib.Logic.PL.Clause.width` counts distinct literals), and neither the space refutation nor the
width refutation uses weakening. Lower bounds on width thus give lower bounds on clause space
(`Cslib.Logic.PL.CNF.RefutableInSpace.add_four_le`).

The proof follows Atserias and Dalmau, with their Duplicator strategy for the existential pebble
game written out as a set of partial assignments. Fix `w = s + k - 3` and suppose `φ` has no
refutation of width `w`. Call a partial assignment *good* if it falsifies no clause derivable within
width `w`. The empty assignment is good, and a good assignment on at most `w` variables extends to
any further variable: if both extensions falsified derivable clauses, their resolvent would be a
derivable clause falsified by the original assignment, of width at most `w` [Atserias and Dalmau,
Lemma 2][AtseriasDalmau2008]. Repeating this, a good assignment on at most `w + 1 - k` variables
extends to a good assignment satisfying any given clause of `φ`, which it cannot falsify. Then,
along a refutation in space `s`, every set `N` of fewer than `s` clauses of the current
configuration is satisfied by some good assignment on at most `|N|` variables: after a download of
`A ∈ N`, satisfy the other clauses of `N` and extend to satisfy `A`; after an inference of `R ∈ N`,
satisfy the parents of `R` instead, which together satisfy `R`; and keep only one satisfying
variable per clause (the Locality Lemma, [Atserias and Dalmau, Lemma 4][AtseriasDalmau2008]).
Applied to the set of the empty clause, this is a contradiction. Atserias and Dalmau (Lemma 5)
keep one assignment satisfying the whole configuration; asking only for sets of fewer than `s`
clauses saves one in the width bound and gives the constant of Filmus et al. The exact constant
stated by Atserias and Dalmau is not quoted here.

## Main results

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

/-! ### Good partial assignments

A partial assignment is a total assignment `σ` read only on a finite set `d` of variables. -/

/-- `c` is a line of some proof from `φ` whose lines have width at most `w`. -/
private def WDerives (φ : CNF V) (w : ℕ) (c : Clause V) : Prop :=
  ∃ ls, φ.IsProof ls ∧ c ∈ ls ∧ ∀ c' ∈ ls, c'.width ≤ w

/-- The assignment `σ`, read on `d`, falsifies `c`: every literal of `c` is on a variable of `d`
and false under `σ`. -/
private def Falsifies (σ : V → Bool) (d : Finset V) (c : Clause V) : Prop :=
  ∀ l ∈ c, l.1 ∈ d ∧ σ l.1 ≠ l.2

/-- The assignment `σ`, read on `d`, satisfies `c`: some literal of `c` is on a variable of `d`
and true under `σ`. -/
private def Satisfies (σ : V → Bool) (d : Finset V) (c : Clause V) : Prop :=
  ∃ l ∈ c, l.1 ∈ d ∧ σ l.1 = l.2

/-- The assignment `σ`, read on `d`, is **good**: it falsifies no clause derivable within width
`w`. -/
private def Good (φ : CNF V) (w : ℕ) (σ : V → Bool) (d : Finset V) : Prop :=
  ∀ c, WDerives φ w c → ¬ Falsifies σ d c

/-- A clause falsified on `d` has width at most `|d|`. -/
private theorem width_le_of_falsifies {σ : V → Bool} {d : Finset V} {c : Clause V}
    (h : Falsifies σ d c) : c.width ≤ d.card := by
  refine Finset.card_le_card_of_injOn Prod.fst (fun l hl => (h l (List.mem_toFinset.1 hl)).1) ?_
  intro l₁ hl₁ l₂ hl₂ he
  have h₁ := (h l₁ (List.mem_toFinset.1 hl₁)).2
  have h₂ := (h l₂ (List.mem_toFinset.1 hl₂)).2
  rcases l₁ with ⟨v₁, b₁⟩
  rcases l₂ with ⟨v₂, b₂⟩
  simp only at he h₁ h₂
  subst he
  cases hσ : σ v₁ <;> cases b₁ <;> cases b₂ <;> simp_all

/-- If `φ` has no refutation of width `w`, the empty assignment is good. -/
private theorem good_empty (h : ¬ φ.RefutableInWidth w) (σ : V → Bool) : Good φ w σ ∅ := by
  rintro c ⟨ls, hp, hc, hw⟩ hf
  have : c = [] := List.eq_nil_iff_forall_not_mem.2 fun l hl => by simpa using (hf l hl).1
  exact h ⟨ls, hp, this ▸ hc, hw⟩

/-- Goodness passes to a smaller domain, and to an assignment agreeing on it. -/
private theorem Good.mono {σ σ' : V → Bool} {d d' : Finset V} (h : Good φ w σ d) (hd : d' ⊆ d)
    (hσ : ∀ x ∈ d', σ' x = σ x) : Good φ w σ' d' :=
  fun c hc hf => h c hc fun l hl => ⟨hd (hf l hl).1, hσ _ (hf l hl).1 ▸ (hf l hl).2⟩

/-- A literal, other than `(x, !b)`, of a clause falsified by `σ` updated at `x` to `b` and read on
`insert x d`, is falsified by `σ` read on `d`. -/
private theorem falsifies_update {σ : V → Bool} {d : Finset V} {x : V} {b : Bool} {c : Clause V}
    (h : Falsifies (Function.update σ x b) (insert x d) c) {l : Literal V} (hl : l ∈ c)
    (hlx : l ≠ (x, !b)) : l.1 ∈ d ∧ σ l.1 ≠ l.2 := by
  obtain ⟨h₁, h₂⟩ := h l hl
  rcases l with ⟨v, b'⟩
  by_cases hv : v = x
  · subst hv
    simp only [Function.update_self] at h₂
    cases b <;> cases b' <;> simp_all
  · rw [Function.update_of_ne hv] at h₂
    exact ⟨(Finset.mem_insert.1 h₁).resolve_left hv, h₂⟩

/-- **One-variable extension**: a good assignment on at most `w` variables extends to a good
assignment on one more variable [Atserias and Dalmau, Lemma 2][AtseriasDalmau2008]. -/
private theorem Good.extend {σ : V → Bool} {d : Finset V} (h : Good φ w σ d) (hd : d.card ≤ w)
    (x : V) : ∃ b, Good φ w (Function.update σ x b) (insert x d) := by
  by_contra hne
  have hb (b : Bool) : ∃ c, WDerives φ w c ∧ Falsifies (Function.update σ x b) (insert x d) c := by
    by_contra hc
    exact hne ⟨b, fun c hw hf => hc ⟨c, hw, hf⟩⟩
  obtain ⟨c₀, ⟨ls₀, hp₀, hc₀, hw₀⟩, hf₀⟩ := hb false
  obtain ⟨c₁, ⟨ls₁, hp₁, hc₁, hw₁⟩, hf₁⟩ := hb true
  -- each clause contains the literal of `x` that its extension falsifies
  have hx₀ : (x, true) ∈ c₀ := by
    by_contra hx₀
    exact h c₀ ⟨ls₀, hp₀, hc₀, hw₀⟩ fun l hl =>
      falsifies_update hf₀ hl fun he => hx₀ (he ▸ hl)
  have hx₁ : (x, false) ∈ c₁ := by
    by_contra hx₁
    exact h c₁ ⟨ls₁, hp₁, hc₁, hw₁⟩ fun l hl =>
      falsifies_update hf₁ hl fun he => hx₁ (he ▸ hl)
  -- so their resolvent is a derivable clause falsified by `σ` on `d`
  have hf : Falsifies σ d (c₀.resolvent c₁ x) := by
    intro l hl
    rcases Clause.mem_resolvent.1 hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
    exacts [falsifies_update hf₀ hl hne, falsifies_update hf₁ hl hne]
  refine h _ ⟨_, (hp₀.append hp₁).resolvent x (List.mem_append_left _ hc₀)
    (List.mem_append_right _ hc₁) hx₀ hx₁, List.mem_cons_self, fun c hc => ?_⟩ hf
  rcases List.mem_cons.1 hc with rfl | hc
  · exact (width_le_of_falsifies hf).trans hd
  · rcases List.mem_append.1 hc with hc | hc
    exacts [hw₀ c hc, hw₁ c hc]

/-- **Extension to a set of variables**: a good assignment on `d` extends to a good assignment on
`d ∪ e` agreeing with it on `d`, provided `|d| + |e| ≤ w + 1`. -/
private theorem Good.extendSet {σ : V → Bool} {d : Finset V} (h : Good φ w σ d) (e : Finset V)
    (hde : d.card + e.card ≤ w + 1) :
    ∃ σ', Good φ w σ' (d ∪ e) ∧ ∀ x ∈ d, σ' x = σ x := by
  induction e using Finset.induction_on with
  | empty => exact ⟨σ, by simpa using h, fun _ _ => rfl⟩
  | @insert x e hxe ih =>
    rw [Finset.card_insert_of_notMem hxe] at hde
    obtain ⟨σ', hσ', hag⟩ := ih (by omega)
    by_cases hx : x ∈ d ∪ e
    · refine ⟨σ', ?_, hag⟩
      rwa [Finset.union_insert, Finset.insert_eq_of_mem hx]
    · have hcard : (d ∪ e).card ≤ w :=
        (Finset.card_union_le _ _).trans (by omega)
      obtain ⟨b, hb⟩ := hσ'.extend hcard x
      refine ⟨_, by rwa [Finset.union_insert], fun y hy => ?_⟩
      have hyx : y ≠ x := by
        rintro rfl
        exact hx (Finset.mem_union_left _ hy)
      rw [Function.update_of_ne hyx]
      exact hag y hy

/-- **Satisfying a clause of the formula**: a good assignment on `d` extends to a good assignment
satisfying a clause `A ∈ φ` and agreeing with it on `d`, provided `|d| + width A ≤ w + 1`. -/
private theorem Good.exists_satisfies {σ : V → Bool} {d : Finset V} (h : Good φ w σ d)
    {A : Clause V} (hA : A ∈ φ) (hAw : A.width ≤ w) (hdA : d.card + A.width ≤ w + 1) :
    ∃ σ' d', Good φ w σ' d' ∧ d ⊆ d' ∧ (∀ x ∈ d, σ' x = σ x) ∧ Satisfies σ' d' A := by
  obtain ⟨σ', hσ', hag⟩ := h.extendSet (A.toFinset.image Prod.fst)
    ((Nat.add_le_add_left Finset.card_image_le _).trans hdA)
  refine ⟨σ', _, hσ', Finset.subset_union_left, hag, ?_⟩
  by_contra hns
  refine hσ' A ⟨[A], IsProof.nil.mem hA, List.mem_singleton_self _, fun c hc => ?_⟩ fun l hl => ?_
  · rw [List.mem_singleton.1 hc]
    exact hAw
  · refine ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hl)), ?_⟩
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

/-- The invariant along a refutation in space `s`: every set `N` of fewer than `s` clauses of the
configuration `M` is satisfied by a good assignment on at most `|N|` variables. -/
private def Inv (φ : CNF V) (w s : ℕ) (M : Finset (Clause V)) : Prop :=
  ∀ N ⊆ M, N.card + 1 ≤ s →
    ∃ σ d, Good φ w σ d ∧ d.card ≤ N.card ∧ ∀ c ∈ N, Satisfies σ d c

/-- If `φ` has no refutation of width `w`, the invariant holds for the empty configuration. -/
private theorem inv_empty (h : ¬ φ.RefutableInWidth w) (s : ℕ) : Inv φ w s ∅ := by
  intro N hN _
  rw [Finset.subset_empty.1 hN]
  exact ⟨fun _ => false, ∅, good_empty h _, by simp, by simp⟩

/-- The invariant survives one step of a refutation in space `s`, with `w = s + k - 3`. -/
private theorem Inv.step {k s : ℕ} (hk : ∀ c ∈ φ, c.width ≤ k) (hs : 3 ≤ s)
    {M M' : Finset (Clause V)} {m : ConfigMove V} (h : Inv φ (s + k - 3) s M)
    (hstep : (φ.configLTS s).Tr M m M') : Inv φ (s + k - 3) s M' := by
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
      obtain ⟨σ', d', hσ', hdd', hag, hA'⟩ := hσ.exists_satisfies hA (by omega) (by omega)
      have hsat' : ∀ c ∈ N, Satisfies σ' d' c := fun c hc => by
        by_cases hcA : c = A
        · exact hcA ▸ hA'
        · exact (hsat c (Finset.mem_erase.2 ⟨hcA, hc⟩)).mono hdd' hag
      obtain ⟨d'', hd'', hcard'', hsat''⟩ := exists_subset_satisfies N hsat'
      exact ⟨σ', d'', hσ'.mono hd'' fun _ _ => rfl, hcard'', hsat''⟩
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
      exact ⟨σ, d', hσ.mono hd' fun _ _ => rfl, hcard', hsat''⟩
    · refine h N (fun c hc => ?_) hNs
      rcases Finset.mem_insert.1 (hN hc) with rfl | hc'
      · by_contra hcM
        exact hR ⟨hc, hcM⟩
      · exact hc'
  | erase c => exact h N (hN.trans (Finset.erase_subset _ _)) hNs

/-- The invariant survives a run of a refutation in space `s`, with `w = s + k - 3`. -/
private theorem Inv.mTr {k s : ℕ} (hk : ∀ c ∈ φ, c.width ≤ k) (hs : 3 ≤ s)
    {M M' : Finset (Clause V)} {ms : List (ConfigMove V)} (h : Inv φ (s + k - 3) s M)
    (hM : (φ.configLTS s).MTr M ms M') : Inv φ (s + k - 3) s M' := by
  induction hM with
  | refl => exact h
  | stepL hstep _ ih => exact ih (h.step hk hs hstep)

/-! ### The inequality -/

/-- A formula containing the empty clause is refutable in width `0`. -/
private theorem refutableInWidth_zero_of_nil_mem (hφ : [] ∈ φ) : φ.RefutableInWidth 0 :=
  ⟨[[]], IsProof.nil.mem hφ, List.mem_singleton_self _, by simp⟩

namespace RefutableInSpace

/-- **Clause space bounds width** [Atserias and Dalmau, Section 4][AtseriasDalmau2008]
[Filmus, Lauria, Mikša, Nordström and Vinyals, Theorem 1][FilmusLauriaMiksaNordstromVinyals2014]: a
formula of clauses of width at most `k` that is refutable in clause space `s` is refutable in width
`s + k - 3`. -/
theorem refutableInWidth {k s : ℕ} (hk : ∀ c ∈ φ, c.width ≤ k) (h : φ.RefutableInSpace s) :
    φ.RefutableInWidth (s + k - 3) := by
  by_cases hφ : [] ∈ φ
  · exact (refutableInWidth_zero_of_nil_mem hφ).mono (Nat.zero_le _)
  have hs := h.three_le hφ
  by_contra hw
  obtain ⟨ms, M, hM, hnil⟩ := h
  obtain ⟨σ, d, -, -, hsat⟩ := (inv_empty hw s).mTr hk hs hM {[]}
    (Finset.singleton_subset_iff.2 hnil) (by rw [Finset.card_singleton]; omega)
  obtain ⟨l, hl, -⟩ := hsat [] (Finset.mem_singleton_self _)
  simp at hl

/-- **Width lower bounds give clause-space lower bounds**: if a formula of clauses of width at most
`k` has no refutation of width `w`, its refutations need clause space at least `w + 4 - k`. -/
theorem add_four_le {k s : ℕ} (hk : ∀ c ∈ φ, c.width ≤ k) (hw : ¬ φ.RefutableInWidth w)
    (h : φ.RefutableInSpace s) : w + 4 ≤ s + k := by
  by_cases hφ : [] ∈ φ
  · exact absurd ((refutableInWidth_zero_of_nil_mem hφ).mono (Nat.zero_le _)) hw
  have hs := h.three_le hφ
  by_contra hlt
  exact hw ((h.refutableInWidth hk).mono (by omega))

end RefutableInSpace

end CNF

end Cslib.Logic.PL
