/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Tally
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.Set.Finite.List

/-!
# Hausdorff decompositions of bounded truth-table reductions

A bounded truth-table reduction of `L` to `B` writes `L` as a Boolean combination of conjunctive
conditions on `B`, and Hausdorff's theorem writes such a combination as a union of differences
`C (2 d) \ C (2 d + 1)` of a decreasing chain of sets [Arvind, Köbler and Mundhenk, Theorem 3.1]
[ArvindKoblerMundhenk1992]. Here the chain is built directly from the truth table. Let the
reduction ask `r a ≤ k` queries of `a`, with answers `b`, and accept when the truth table
`f = d (a, ·)` takes the value `true` at `b`. The set `C j`
(`Cslib.Complexity.BTT.Hausdorff f b j`) holds when there are answer vectors
`h > v₁ > ⋯ > v_j`, strictly decreasing componentwise with `h ≤ b`, on which `f` alternates and
ends with `true` (`Cslib.Complexity.BTT.StepBelow`). Then:

* the sets decrease (`Cslib.Complexity.BTT.Hausdorff.of_succ`): drop `h`;
* `f b = true` exactly when `b` lies in `C (2 d) \ C (2 d + 1)` for some `d`
  (`Cslib.Complexity.BTT.eq_true_iff_exists_hausdorff`): a longest chain below `b` has the value
  `f b` at its top, since otherwise `b` would extend it, so `f b` is `true` exactly when it has
  odd length. The number of `true` answers strictly decreases along a chain, so a chain has at most
  `r a + 1` vectors, and `d ≤ k / 2`.

Each `C j` is a union, over the finitely many candidate chains of vectors of length at most `k`, of
a polynomial-time condition (the chain is valid for `f` and `r a`) and the conjunctive condition
that the queries answered `true` at `h` lie in `B`. If `B` reduces conjunctively to a tally
problem, so does each `C j` (`Cslib.Complexity.BTT.exists_polyTimeCTTReducible_hausdorff`), by the
closure of these reductions under intersection and finite unions
[Arvind, Köbler and Mundhenk, Lemma 3.2][ArvindKoblerMundhenk1992].

The source obtains the decomposition from Hausdorff's theorem for the Boolean closure of the set
ring `R_ctt(SPARSE)`, together with the fact that bounded truth-table reductions to a class with
suitable closure properties give its Boolean closure [Arvind, Köbler and Mundhenk, Fact 3.3]
[ArvindKoblerMundhenk1992]; the chains of answer vectors above are this library's direct
construction for a single reduction.

## Main definitions

* `Cslib.Complexity.BTT.StepBelow`: one step of an alternating chain of answer vectors.
* `Cslib.Complexity.BTT.Hausdorff`: the Hausdorff sets of a truth table at given answers.

## Main results

* `Cslib.Complexity.BTT.Hausdorff.of_succ`, `Cslib.Complexity.BTT.Hausdorff.mono`: the sets
  decrease.
* `Cslib.Complexity.BTT.le_length_of_hausdorff`: the `j`-th set is empty unless `j` is at most the
  number of answers.
* `Cslib.Complexity.BTT.eq_true_iff_exists_hausdorff`: the Hausdorff decomposition of the truth
  table.
* `Cslib.Complexity.BTT.forall₂_le_truthTableAnswers_iff`: lying below the answers of a
  truth-table reduction is a conjunctive condition.
* `Cslib.Complexity.BTT.exists_polyTimeCTTReducible_hausdorff`: the Hausdorff sets of a bounded
  truth-table reduction to a problem with a conjunctive reduction to a tally problem reduce
  conjunctively to tally problems.

## References

* [V. Arvind, J. Köbler, M. Mundhenk, *On Bounded Truth-Table, Conjunctive, and Randomized
  Reductions to Sparse Sets*][ArvindKoblerMundhenk1992]
-/

@[expose] public section

namespace Cslib.Complexity.BTT

/-! ### Alternating chains of answer vectors -/

section Chain

/-- One step of an alternating chain for the truth table `f`: the answer vector `v` lies strictly
below `w` componentwise, and `f` takes different values at them. -/
def StepBelow (f : List Bool → Bool) (w v : List Bool) : Prop :=
  List.Forall₂ (· ≤ ·) v w ∧ v ≠ w ∧ f v ≠ f w

/-- **The `j`-th Hausdorff set** of the truth table `f` at the answers `b`: there are answer
vectors `h, v₁, …, v_j`, each strictly below the previous one with the opposite value of `f`, such
that `h ≤ b` componentwise and `f` is `true` at `v_j`; that is, `f h` is `true` exactly when `j` is
even. -/
def Hausdorff (f : List Bool → Bool) (b : List Bool) (j : ℕ) : Prop :=
  ∃ (h : List Bool) (t : List (List Bool)), (∀ p ∈ (h :: t).zip t, StepBelow f p.1 p.2) ∧
    t.length = j ∧ f h = decide (Even j) ∧ List.Forall₂ (· ≤ ·) h b

variable {f : List Bool → Bool} {b : List Bool}

private theorem forall₂_le_trans {u v w : List Bool} (h₁ : List.Forall₂ (· ≤ ·) u v)
    (h₂ : List.Forall₂ (· ≤ ·) v w) : List.Forall₂ (· ≤ ·) u w := by
  induction h₁ generalizing w with
  | nil => cases h₂; exact .nil
  | cons hab _ ih =>
    cases h₂ with
    | cons hbc h₂ => exact .cons (le_trans hab hbc) (ih h₂)

private theorem count_le_of_forall₂ {v w : List Bool} (h : List.Forall₂ (· ≤ ·) v w) :
    v.count true ≤ w.count true := by
  induction h with
  | nil => exact le_rfl
  | @cons a b _ _ hab _ ih =>
    rw [List.count_cons, List.count_cons]
    cases a <;> cases b
    · simpa using ih
    · change List.count true _ + 0 ≤ List.count true _ + 1
      omega
    · exact absurd hab (by decide)
    · simpa using ih

private theorem count_lt_of_forall₂ {v w : List Bool} (h : List.Forall₂ (· ≤ ·) v w)
    (hne : v ≠ w) : v.count true < w.count true := by
  induction h with
  | nil => exact absurd rfl hne
  | @cons a b l₁ l₂ hab hrest ih =>
    rw [List.count_cons, List.count_cons]
    have hle := count_le_of_forall₂ hrest
    cases a <;> cases b
    · have : l₁ ≠ l₂ := fun h => hne (h ▸ rfl)
      simpa using ih this
    · change List.count true l₁ + 0 < List.count true l₂ + 1
      omega
    · exact absurd hab (by decide)
    · have : l₁ ≠ l₂ := fun h => hne (h ▸ rfl)
      simpa using ih this

/-- The steps of a chain from `h` through `t`. -/
private theorem zip_cons_cons (h v : List Bool) (t : List (List Bool)) :
    (h :: v :: t).zip (v :: t) = (h, v) :: (v :: t).zip t := rfl

/-- A chain from `h` has at most as many further vectors as `h` has `true` answers. -/
private theorem length_le_count {h : List Bool} {t : List (List Bool)}
    (hc : ∀ p ∈ (h :: t).zip t, StepBelow f p.1 p.2) : t.length ≤ h.count true := by
  induction t generalizing h with
  | nil => exact Nat.zero_le _
  | cons v t ih =>
    rw [zip_cons_cons] at hc
    have hstep : StepBelow f h v := hc (h, v) List.mem_cons_self
    have := ih fun p hp => hc p (List.mem_cons_of_mem _ hp)
    have := count_lt_of_forall₂ hstep.1 hstep.2.1
    rw [List.length_cons]
    omega

/-- The vectors of a chain have the length of its top. -/
private theorem length_eq_of_mem {h : List Bool} {t : List (List Bool)}
    (hc : ∀ p ∈ (h :: t).zip t, StepBelow f p.1 p.2) : ∀ v ∈ t, v.length = h.length := by
  induction t generalizing h with
  | nil => simp
  | cons v t ih =>
    rw [zip_cons_cons] at hc
    have hv := (hc (h, v) List.mem_cons_self).1.length_eq
    have := ih fun p hp => hc p (List.mem_cons_of_mem _ hp)
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hv
    · exact (this w hw).trans hv

private theorem decide_even_succ (j : ℕ) : decide (Even (j + 1)) = !decide (Even j) := by
  by_cases h : Even j <;> simp [h, Nat.even_add_one]

/-- **The Hausdorff sets decrease**: dropping the top of a chain. -/
theorem Hausdorff.of_succ {j : ℕ} (hH : Hausdorff f b (j + 1)) : Hausdorff f b j := by
  obtain ⟨h, t, hc, ht, hf, hb⟩ := hH
  obtain ⟨v, t, rfl⟩ : ∃ v t', t = v :: t' := List.exists_cons_of_length_eq_add_one ht
  rw [zip_cons_cons] at hc
  have hstep := hc (h, v) List.mem_cons_self
  refine ⟨v, t, fun p hp => hc p (List.mem_cons_of_mem _ hp), by simpa using ht, ?_,
    forall₂_le_trans hstep.1 hb⟩
  have hne := hstep.2.2
  rw [hf, decide_even_succ] at hne
  revert hne
  cases f v <;> cases decide (Even j) <;> simp

theorem Hausdorff.mono {i j : ℕ} (hij : i ≤ j) (hH : Hausdorff f b j) : Hausdorff f b i := by
  induction j, hij using Nat.le_induction with
  | base => exact hH
  | succ j _ ih => exact ih hH.of_succ

/-- The `j`-th Hausdorff set is empty unless `j` is at most the number of answers: the vectors of
a chain have strictly decreasing numbers of `true` answers. -/
theorem le_length_of_hausdorff {j : ℕ} (hH : Hausdorff f b j) : j ≤ b.length := by
  obtain ⟨h, t, hc, rfl, -, hb⟩ := hH
  exact (length_le_count hc).trans ((count_le_of_forall₂ hb).trans (List.count_le_length ..))

/-- At the last Hausdorff set containing the answers `b`, the value of `f` at `b` is the parity of
its index: the top of a longest chain has the value `f b`, since otherwise `b` would extend the
chain. -/
theorem eq_decide_even_of_hausdorff {j : ℕ} (hj : Hausdorff f b j)
    (hj' : ¬Hausdorff f b (j + 1)) : f b = decide (Even j) := by
  obtain ⟨h, t, hc, ht, hf, hb⟩ := hj
  by_cases heq : h = b
  · exact heq ▸ hf
  by_contra hne
  refine hj' ⟨b, h :: t, fun p hp => ?_, by simp [ht], ?_, List.forall₂_refl b⟩
  · rw [zip_cons_cons] at hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨hb, heq, hf ▸ Ne.symm hne⟩
    · exact hc p hp
  · rw [decide_even_succ]
    revert hne
    cases f b <;> cases decide (Even j) <;> simp

/-- **The Hausdorff decomposition of a truth table**: `f b = true` exactly when `b` lies in the
`2 d`-th Hausdorff set but not in the next one, for some `d < D`, provided `b` has fewer than
`2 D` answers. -/
theorem eq_true_iff_exists_hausdorff {D : ℕ} (hb : b.length < 2 * D) :
    f b = true ↔ ∃ d < D, Hausdorff f b (2 * d) ∧ ¬Hausdorff f b (2 * d + 1) := by
  constructor
  · intro hf
    have h0 : Hausdorff f b 0 := ⟨b, [], by simp, rfl, by simpa using hf, List.forall₂_refl b⟩
    obtain ⟨j, hj, hj'⟩ : ∃ j, Hausdorff f b j ∧ ¬Hausdorff f b (j + 1) := by
      by_contra hall
      push Not at hall
      have hall' : ∀ j, Hausdorff f b j := fun j => by
        induction j with
        | zero => exact h0
        | succ j ih => exact hall j ih
      exact absurd (le_length_of_hausdorff (hall' (b.length + 1))) (by omega)
    have heven : Even j := by simpa [hf] using (eq_decide_even_of_hausdorff hj hj').symm
    obtain ⟨d, rfl⟩ := heven
    refine ⟨d, ?_, by rwa [two_mul], by rwa [two_mul]⟩
    have := le_length_of_hausdorff hj
    omega
  · rintro ⟨d, -, hd, hd'⟩
    simpa using eq_decide_even_of_hausdorff hd hd'

end Chain

/-! ### Answers of truth-table reductions -/

/-- **Lying below the answers of a truth-table reduction is a conjunctive condition**: a vector
lies below the answers componentwise exactly when it has one entry per query and every query at
which it is `true` is in the target. -/
theorem forall₂_le_truthTableAnswers_iff {α : Type} {A : Set (α × ℕ)} {r : α → ℕ} {a : α}
    {v : List Bool} : List.Forall₂ (· ≤ ·) v (truthTableAnswers A r a) ↔
      v.length = r a ∧ ∀ i, v[i]? = some true → (a, i) ∈ A := by
  classical
  rw [List.forall₂_iff_get]
  constructor
  · rintro ⟨hlen, h⟩
    refine ⟨by simpa using hlen, fun i hi => ?_⟩
    obtain ⟨hi', hvi⟩ := List.getElem?_eq_some_iff.1 hi
    have := h i hi' (hlen ▸ hi')
    simp only [List.get_eq_getElem, hvi, truthTableAnswers, List.getElem_ofFn] at this
    simpa [Bool.le_iff_imp] using this
  · rintro ⟨hlen, h⟩
    refine ⟨by simpa using hlen, fun i h₁ h₂ => ?_⟩
    simp only [List.get_eq_getElem, truthTableAnswers, List.getElem_ofFn, Bool.le_iff_imp,
      decide_eq_true_eq]
    exact fun hv => h i (List.getElem?_eq_some_iff.2 ⟨h₁, hv⟩)

/-! ### Conjunctive reductions of the Hausdorff sets -/

open Turing.MultiTapeTM ComputableInPolyTime

/-- The lists of length `j` with entries in a finite set form a finite set. -/
private theorem finite_lists {δ : Type*} {V : Set δ} (hV : V.Finite) (j : ℕ) :
    {t : List δ | t.length = j ∧ ∀ v ∈ t, v ∈ V}.Finite := by
  induction j with
  | zero => exact (Set.finite_singleton []).subset fun t ht => by simpa using ht.1
  | succ j ih =>
    refine (hV.image2 (· :: ·) ih).subset ?_
    rintro (_ | ⟨v, t⟩) ⟨hlen, hmem⟩
    · simp at hlen
    · exact ⟨v, hmem v List.mem_cons_self, t,
        ⟨by simpa using hlen, fun w hw => hmem w (List.mem_cons_of_mem _ hw)⟩, rfl⟩

/-- The candidate chains for the `j`-th Hausdorff set of a reduction making at most `k` queries:
a top and `j` further vectors, all of length at most `k`. -/
private theorem finite_candidates (k j : ℕ) :
    ({v : List Bool | v.length ≤ k} ×ˢ
      {t : List (List Bool) | t.length = j ∧ ∀ v ∈ t, v ∈ {v : List Bool | v.length ≤ k}}).Finite :=
  (List.finite_length_le Bool k).prod (finite_lists (List.finite_length_le Bool k) j)

/-- The positions at which a vector is `true`. -/
private def ones (v : List Bool) : List ℕ := (v.zipIdx.filter (·.1)).map Prod.snd

private theorem mem_ones {v : List Bool} {i : ℕ} : i ∈ ones v ↔ v[i]? = some true := by
  simp only [ones, List.mem_map, List.mem_filter, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨x, i⟩, ⟨hx, hx1⟩, rfl⟩
    simp only at hx1
    simpa [hx1] using hx
  · intro h
    exact ⟨(true, i), ⟨h, rfl⟩, rfl⟩

/-- Testing every element of a fixed list is polynomial-time when each test is. -/
private theorem computableInPolyTime_all_const {γ ι : Type} {encIn : γ ↪ List Bool} (l : List ι)
    {test : γ → ι → Bool} (h : ∀ i ∈ l, ComputableInPolyTime (fun x => test x i) encIn encBool) :
    ComputableInPolyTime (fun x => l.all (test x)) encIn encBool :=
  .of_tidy (ComputableTidilyInPolyTime.allConst l fun i hi => (h i hi).tidy)

/-- **The Hausdorff sets of a bounded truth-table reduction reduce conjunctively to tally
problems**, when the target of the reduction does. Here `r`, `q` and `d` are the query count, the
queries and the truth table of a reduction making at most `k` queries, and the target `B` has a
conjunctive reduction to a set of natural numbers written in unary
[Arvind, Köbler and Mundhenk, Lemma 3.2][ArvindKoblerMundhenk1992]. -/
theorem exists_polyTimeCTTReducible_hausdorff {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {B : Set β} {k : ℕ} {r : α → ℕ} {q : α × ℕ → β}
    {d : α × List Bool → Bool} (hB : ∃ A : Set ℕ, PolyTimeCTTReducible encB encUnary B A)
    (hr : ComputableInPolyTime r encA encUnary)
    (hq : ComputableInPolyTime q (encPair encA encUnary) encB)
    (hd : ComputableInPolyTime d (encPair encA encBits) encBool) (hk : ∀ a, r a ≤ k) (j : ℕ) :
    ∃ A : Set ℕ, PolyTimeCTTReducible encA encUnary
      {a | Hausdorff (fun v => d (a, v)) (truthTableAnswers (q ⁻¹' B) r a) j} A := by
  classical
  obtain ⟨AB, hAB⟩ := hB
  /- The candidate `(h, t)` is valid at `a` when it is a chain for `d (a, ·)` with the right parity
  and `h` has one entry per query. -/
  let valid (p : List Bool × List (List Bool)) (a : α) : Bool :=
    (((p.1 :: p.2).zip p.2).all fun e =>
      decide (List.Forall₂ (· ≤ ·) e.2 e.1 ∧ e.2 ≠ e.1) && (d (a, e.2) != d (a, e.1))) &&
    (d (a, p.1) == decide (Even p.2.length)) && (p.1.length == r a)
  have hvalid (p : List Bool × List (List Bool)) (a : α) : valid p a = true ↔
      (∀ e ∈ (p.1 :: p.2).zip p.2, StepBelow (fun v => d (a, v)) e.1 e.2) ∧
        d (a, p.1) = decide (Even p.2.length) ∧ p.1.length = r a := by
    simp only [valid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      beq_iff_eq, StepBelow, and_assoc]
  /- The queries answered `true` at the top `v`. -/
  let qs (v : List Bool) (a : α) : List β := (ones v).map fun i => q (a, i)
  set cands := (finite_candidates k j).toFinset.toList
  have hset : {a | Hausdorff (fun v => d (a, v)) (truthTableAnswers (q ⁻¹' B) r a) j} =
      ⋃ p ∈ cands, ({a | valid p a = true} ∩ {a | ∀ y ∈ qs p.1 a, y ∈ B}) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop, cands,
      Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_prod, hvalid, qs, List.mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ones]
    constructor
    · rintro ⟨h, t, hc, ht, hf, hb⟩
      obtain ⟨hlen, hbelow⟩ := forall₂_le_truthTableAnswers_iff.1 hb
      have hhk : h.length ≤ k := hlen ▸ hk a
      refine ⟨(h, t), ⟨hhk, ht, fun v hv => (length_eq_of_mem hc v hv).trans_le hhk⟩,
        ⟨hc, ht ▸ hf, hlen⟩, fun i hi => hbelow i hi⟩
    · rintro ⟨⟨h, t⟩, ⟨-, ht, -⟩, ⟨hc, hf, hlen⟩, hbelow⟩
      exact ⟨h, t, hc, ht, ht ▸ hf, forall₂_le_truthTableAnswers_iff.2 ⟨hlen, hbelow⟩⟩
  rw [hset]
  refine PolyTimeCTTReducible.exists_encUnary_biUnion cands fun p _ => ?_
  have hpoly : ComputableInPolyTime (valid p) encA encBool := by
    have hall : ComputableInPolyTime (fun a => ((p.1 :: p.2).zip p.2).all fun e =>
        decide (List.Forall₂ (· ≤ ·) e.2 e.1 ∧ e.2 ≠ e.1) && (d (a, e.2) != d (a, e.1)))
        encA encBool :=
      computableInPolyTime_all_const _ fun e _ => by fun_prop
    fun_prop
  obtain ⟨A₁, h₁⟩ := exists_polyTimeCTTReducible_encUnary_of_mem_P
    (L := {a | valid p a = true}) (mem_P.2 ⟨valid p, hpoly, fun _ => Iff.rfl⟩)
  exact h₁.exists_encUnary_inter (hAB.forall_mem (Qs := qs p.1) (by fun_prop))

end Cslib.Complexity.BTT
