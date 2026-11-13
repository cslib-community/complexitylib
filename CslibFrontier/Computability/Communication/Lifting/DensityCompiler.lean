/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.SimulationTrace
public import CslibFrontier.Computability.Communication.Lifting.DensityOracle
public import CslibFrontier.Computability.Communication.Protocol.Alternating
public import CslibFrontier.Computability.DecisionTree.Basic
public import Mathlib.Data.Finset.Piecewise

/-!
# Recursive simulation of alternating protocols

The simulator queries exactly the coordinates restored by each density step. Its interface asks
only for local density steps and terminal full range, rather than an assumed decision-tree
simulation. These local hypotheses can be proved from single-block discrepancy. Alternating
ownership ensures that the next speaker has density `σ` and the next listener has density `τ`.
-/

@[expose] public section

namespace Cslib.Communication.Lifting

open Finset

variable {n m : ℕ}

/-- Densities indexed by the next speaker: `true` means Alice. -/
def TurnDense (τ σ : ℝ) (turn : Bool) (F : Finset (Fin n))
    (X Y : Finset (Fin n → Fin m)) : Prop :=
  if turn then IsDense σ F X ∧ IsDense τ F Y else IsDense τ F X ∧ IsDense σ F Y

/-- Outside the free coordinates the rectangle realizes the already queried assignment. -/
def OutputFixed (g : Fin m → Fin m → Bool) (F : Finset (Fin n))
    (X Y : Finset (Fin n → Fin m)) (ρ : Fin n → Bool) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ i ∉ F, g (x i) (y i) = ρ i

/-- The rectangle after an Alice step realizes the extended partial assignment. -/
theorem DensityStep.Valid.outputFixed {g : Fin m → Fin m → Bool} {τ σ : ℝ}
    {F : Finset (Fin n)} {X Y : Finset (Fin n → Fin m)} {send} {st : DensityStep n m}
    (h : st.Valid g τ σ F X Y send) {ρ : Fin n → Bool} (hf : OutputFixed g F X Y ρ)
    (a : Fin n → Bool) :
    OutputFixed g (F \ st.queried) st.speaker (st.listener a)
      (st.queried.piecewise a ρ) := by
  intro x hx y hy i hi
  by_cases hI : i ∈ st.queried
  · simpa [hI] using h.output_eq a x hx y hy i hI
  · have hF : i ∉ F := fun hF => hi (mem_sdiff.mpr ⟨hF, hI⟩)
    simpa [hI] using hf x (h.speaker_subset hx) y (h.listener_subset a hy) i hF

/-- Assemble continuations by querying the freshly restored coordinates. -/
private theorem exists_graft_density {O : Type*} (R : (Fin n → Bool) → O → Prop)
    (F I : Finset (Fin n)) (ρ : Fin n → Bool) (q Q : ℕ)
    (hc : ∀ a : Fin n → Bool, ∃ t : DecisionTree (Fin n) O,
      t.depth + (q + #I) ≤ Q ∧
      ∀ z, (∀ i ∉ F \ I, z i = I.piecewise a ρ i) → R z (t.eval z)) :
    ∃ t : DecisionTree (Fin n) O, t.depth + q ≤ Q ∧
      ∀ z, (∀ i ∉ F, z i = ρ i) → R z (t.eval z) := by
  classical
  choose trees htrees using hc
  refine ⟨DecisionTree.graft I.toList trees ρ, ?_, ?_⟩
  · have hdepth := DecisionTree.depth_graft_le I.toList trees ρ
      (d := Q - (q + #I)) (fun a => by have := (htrees a).1; omega)
    have := (htrees ρ).1
    simp only [length_toList] at hdepth
    omega
  · intro z hz
    rw [DecisionTree.eval_graft]
    apply (htrees (fun i => if i ∈ I.toList then z i else ρ i)).2
    intro i hi
    by_cases hI : i ∈ I
    · simp [hI]
    · have hF : i ∉ F := fun hF => hi (mem_sdiff.mpr ⟨hF, hI⟩)
      simpa [hI] using hz i hF

/-- Recursive compilation from local density guarantees. Every input extending the current
partial assignment obtains an output satisfying the outer relation. -/
theorem exists_density_decisionTree {O : Type*} (g : Fin m → Fin m → Bool) (τ σ : ℝ)
    (oa : DensityOracle (n := n) g τ σ)
    (ob : DensityOracle (n := n) (fun y x => g x y) τ σ)
    (R : (Fin n → Bool) → O → Prop)
    (C Q : ℕ) (hm : 0 < m) (hτ : 0 < τ)
    (hbound : ∀ q : ℕ, q ≤ n → ((m : ℝ) / (2 * τ)) ^ q ≤ 8 ^ C → q ≤ Q)
    (p : Protocol (Fin n → Fin m) (Fin n → Fin m) O)
    (turn : Bool) (halt : Protocol.Alternates turn p)
    (F : Finset (Fin n)) (X Y : Finset (Fin n → Fin m)) (ρ : Fin n → Bool)
    (c q : ℕ)
    (trace : DensityTrace g τ σ univ univ univ F X Y c q)
    (hbudget : c + p.depth ≤ C)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hd : TurnDense τ σ turn F X Y)
    (hf : OutputFixed g F X Y ρ)
    (hp : ∀ x ∈ X, ∀ y ∈ Y, R (fun i => g (x i) (y i)) (p.run x y)) :
    ∃ t : DecisionTree (Fin n) O, t.depth + q ≤ Q ∧
      ∀ z, (∀ i ∉ F, z i = ρ i) → R z (t.eval z) := by
  classical
  induction p generalizing turn F X Y ρ c q with
  | output o =>
    have hqn : q ≤ n := by
      have hc := trace.card_free
      simp only [card_univ, Fintype.card_fin] at hc
      omega
    have hq := hbound q hqn ((trace.query_bound hm hτ).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) (by simpa using hbudget)))
    refine ⟨.leaf o, by simpa using hq, ?_⟩
    intro z hz
    have hr : ∃ x ∈ X, ∃ y ∈ Y, ∀ i ∈ F, g (x i) (y i) = z i := by
      cases turn
      · obtain ⟨x, hx, y, hy, he⟩ := ob.full F Y X hY hX hd.2 hd.1 z
        exact ⟨y, hy, x, hx, he⟩
      · exact oa.full F X Y hX hY hd.1 hd.2 z
    obtain ⟨x, hx, y, hy, he⟩ := hr
    have heq : (fun i => g (x i) (y i)) = z := by
      funext i
      by_cases hi : i ∈ F
      · exact he i hi
      · exact (hf x hx y hy i hi).trans (hz i hi).symm
    simpa [heq] using hp x hx y hy
  | alice send p₀ p₁ ih₀ ih₁ =>
    obtain ⟨hturn, halt₀, halt₁⟩ := halt
    subst turn
    obtain ⟨st, hv⟩ := oa.step F X Y hX hY hd.1 hd.2 send
    have hc (a : Fin n → Bool) : ∃ t : DecisionTree (Fin n) O,
        t.depth + (q + #st.queried) ≤ Q ∧
        ∀ z, (∀ i ∉ F \ st.queried, z i = st.queried.piecewise a ρ i) →
          R z (t.eval z) := by
      have trace' := trace.append (DensityTrace.alice st send a hv
        (DensityTrace.stop (F \ st.queried) st.speaker (st.listener a)))
      have hf' := hv.outputFixed hf a
      have hd' : TurnDense τ σ false (F \ st.queried) st.speaker (st.listener a) :=
        ⟨hv.speaker_dense, hv.listener_dense a⟩
      have hp' : ∀ x ∈ st.speaker, ∀ y ∈ st.listener a,
          R (fun i => g (x i) (y i)) ((cond st.message p₁ p₀).run x y) := by
        intro x hx y hy
        have hh := hp x (hv.speaker_subset hx) y (hv.listener_subset a hy)
        simp only [Protocol.run_alice, hv.message_eq x hx] at hh
        cases hm : st.message <;> simpa [hm] using hh
      cases hm : st.message
      · simp only [hm, Bool.cond_false] at hp'
        exact ih₀ false halt₀ (F \ st.queried) st.speaker (st.listener a)
          (st.queried.piecewise a ρ) (c + 1) (q + #st.queried)
          (by simpa using trace') (by simp only [Protocol.depth] at hbudget; omega)
          hv.speaker_nonempty (hv.listener_nonempty a) hd' hf' hp'
      · simp only [hm, Bool.cond_true] at hp'
        exact ih₁ false halt₁ (F \ st.queried) st.speaker (st.listener a)
          (st.queried.piecewise a ρ) (c + 1) (q + #st.queried)
          (by simpa using trace') (by simp only [Protocol.depth] at hbudget; omega)
          hv.speaker_nonempty (hv.listener_nonempty a) hd' hf' hp'
    exact exists_graft_density R F st.queried ρ q Q hc
  | bob send p₀ p₁ ih₀ ih₁ =>
    obtain ⟨hturn, halt₀, halt₁⟩ := halt
    subst turn
    obtain ⟨st, hv⟩ := ob.step F Y X hY hX hd.2 hd.1 send
    have hc (a : Fin n → Bool) : ∃ t : DecisionTree (Fin n) O,
        t.depth + (q + #st.queried) ≤ Q ∧
        ∀ z, (∀ i ∉ F \ st.queried, z i = st.queried.piecewise a ρ i) →
          R z (t.eval z) := by
      have trace' := trace.append (DensityTrace.bob st send a hv
        (DensityTrace.stop (F \ st.queried) (st.listener a) st.speaker))
      have hfSwap : OutputFixed (fun y x => g x y) F Y X ρ :=
        fun y hy x hx i hi => hf x hx y hy i hi
      have hf' : OutputFixed g (F \ st.queried) (st.listener a) st.speaker
          (st.queried.piecewise a ρ) := by
        intro x hx y hy i hi
        exact hv.outputFixed hfSwap a y hy x hx i hi
      have hd' : TurnDense τ σ true (F \ st.queried) (st.listener a) st.speaker :=
        ⟨hv.listener_dense a, hv.speaker_dense⟩
      have hp' : ∀ x ∈ st.listener a, ∀ y ∈ st.speaker,
          R (fun i => g (x i) (y i)) ((cond st.message p₁ p₀).run x y) := by
        intro x hx y hy
        have hh := hp x (hv.listener_subset a hx) y (hv.speaker_subset hy)
        simp only [Protocol.run_bob, hv.message_eq y hy] at hh
        cases hm : st.message <;> simpa [hm] using hh
      cases hm : st.message
      · simp only [hm, Bool.cond_false] at hp'
        exact ih₀ true halt₀ (F \ st.queried) (st.listener a) st.speaker
          (st.queried.piecewise a ρ) (c + 1) (q + #st.queried)
          (by simpa using trace') (by simp only [Protocol.depth] at hbudget; omega)
          (hv.listener_nonempty a) hv.speaker_nonempty hd' hf' hp'
      · simp only [hm, Bool.cond_true] at hp'
        exact ih₁ true halt₁ (F \ st.queried) (st.listener a) st.speaker
          (st.queried.piecewise a ρ) (c + 1) (q + #st.queried)
          (by simpa using trace') (by simp only [Protocol.depth] at hbudget; omega)
          (hv.listener_nonempty a) hv.speaker_nonempty hd' hf' hp'
    exact exists_graft_density R F st.queried ρ q Q hc

/-- Every protocol admits a correct decision-tree simulation whose query cost satisfies the
volume bound. The protocol is first made alternating, accounting for the factor two in its
communication depth. The local density guarantees are the only gadget-specific hypotheses. -/
theorem exists_simulating_decisionTree {O : Type*} (g : Fin m → Fin m → Bool) (τ σ : ℝ)
    (oa : DensityOracle (n := n) g τ σ)
    (ob : DensityOracle (n := n) (fun y x => g x y) τ σ)
    (hm : 0 < m) (hτ : 0 < τ) (hσ : 0 ≤ σ)
    (hτm : τ ≤ m) (hσm : σ ≤ m) (hbase : 1 ≤ (m : ℝ) / (2 * τ))
    (R : (Fin n → Bool) → O → Prop)
    (p : Protocol (Fin n → Fin m) (Fin n → Fin m) O)
    (hp : ∀ x y, R (fun i => g (x i) (y i)) (p.run x y)) :
    ∃ t : DecisionTree (Fin n) O, (∀ z, R z (t.eval z)) ∧
      ((m : ℝ) / (2 * τ)) ^ t.depth ≤ 8 ^ (2 * p.depth) := by
  classical
  let S := (range (n + 1)).filter fun q => ((m : ℝ) / (2 * τ)) ^ q ≤ 8 ^ (2 * p.depth)
  have hS : S.Nonempty := ⟨0, by simp [S, one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 8)]⟩
  let Q := S.max' hS
  have hQ : Q ∈ S := max'_mem S hS
  have hbound (q : ℕ) (hqn : q ≤ n)
      (hq : ((m : ℝ) / (2 * τ)) ^ q ≤ 8 ^ (2 * p.depth)) : q ≤ Q :=
    le_max' S q (mem_filter.mpr ⟨mem_range.mpr (by omega), hq⟩)
  let : NeZero m := ⟨by omega⟩
  have hne : (univ : Finset (Fin n → Fin m)).Nonempty := univ_nonempty
  obtain ⟨t, ht, hsem⟩ := exists_density_decisionTree g τ σ oa ob R (2 * p.depth) Q
    hm hτ hbound (p.alternate true) true (p.alternates_alternate true)
    univ univ univ (fun _ => false) 0 0 (DensityTrace.stop _ _ _)
    (by simpa using p.depth_alternate_le true) hne hne
    ⟨isDense_univ hσ hσm _, isDense_univ hτ.le hτm _⟩
    (by intro x hx y hy i hi; exact (hi (mem_univ i)).elim)
    (by intro x hx y hy; simpa using hp x y)
  refine ⟨t, fun z => hsem z (by simp), ?_⟩
  exact (pow_le_pow_right₀ hbase (by simpa using ht)).trans (mem_filter.mp hQ).2

end Cslib.Communication.Lifting
