/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MoserTardos.Symmetric
import CslibFrontier.Foundations.Probability.InfinitePi

/-!
# Lopsided Moser–Tardos algorithmic local lemma

This module proves **Section 6** of [MoserTardos2010] (Theorem 6.1 and Lemma 6.2), replacing the
variable-sharing dependency graph `Adj vbl` with the *lopsidependency* graph `Lopsidependent`:
two events `A i` and `A j` are lopsidependent if there exist assignments `f` and `g` agreeing
outside `vbl i ∩ vbl j` such that `f ∈ A i`, `g ∈ A j`, and either `f ∉ A j` or `g ∉ A i`.
Disjoint variable sets are never lopsidependent (`not_lopsidependent_of_disjoint`), so the
lopsided local lemma weakens the hypothesis and strictly generalizes Theorem 1.2.

## Main definitions

* `Cslib.Probability.MoserTardos.Lopsidependent`: lopsidependence of two events depending on
  `vbl i` and `vbl j`.
* `Cslib.Probability.MoserTardos.lopsidedAdj`: reflexive closure `i = j ∨ Lopsidependent vbl A i j`.

## Main results

* `Cslib.Probability.MoserTardos.Lopsided.table_witness_le`: **Lemma 6.2** of [MoserTardos2010],
  bounding the probability that a fixed structure occurs as a lopsided witness structure by
  `∏ p ∈ S, Pr[A p.1]`, proved by normalizing the log into a canonical depth-ordered log using the
  commutation of non-lopsidependent consecutive resamplings.
* `Cslib.Probability.MoserTardos.Lopsided.lintegral_resamplings_le`,
  `Cslib.Probability.MoserTardos.Lopsided.lintegral_sum_resamplings_le`,
  `Cslib.Probability.MoserTardos.Lopsided.ae_exists_forall_notMem_run`,
  `Cslib.Probability.MoserTardos.Lopsided.exists_forall_notMem`: **Theorem 6.1** of
  [MoserTardos2010] (asymmetric form) and its symmetric specialization (`*_symmetric`).

## References

* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010, Section 6]
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Cslib.Probability.MoserTardos

section Lopsidependent

variable {V ι : Type*} {α : V → Type*}

/-- Events `A i` and `A j` are *lopsidependent* [MoserTardos2010, Section 6] when there exist
assignments `f` and `g` differing only on `vbl i ∩ vbl j` such that `f ∈ A i`, `g ∈ A j`, and
either `f ∉ A j` or `g ∉ A i`. -/
def Lopsidependent [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (i j : ι) : Prop :=
  ∃ f g : ∀ v, α v, (∀ v, v ∉ vbl i ∩ vbl j → f v = g v) ∧
    f ∈ A i ∧ g ∈ A j ∧ (f ∉ A j ∨ g ∉ A i)

theorem lopsidependent_iff [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    {i j : ι} : Lopsidependent vbl A i j ↔
      ∃ f g : ∀ v, α v, (∀ v, v ∉ vbl i ∩ vbl j → f v = g v) ∧
        f ∈ A i ∧ g ∈ A j ∧ (f ∉ A j ∨ g ∉ A i) := by
  rw [Lopsidependent]

theorem lopsidependent_comm [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    {i j : ι} : Lopsidependent vbl A i j ↔ Lopsidependent vbl A j i := by
  constructor <;>
  · rintro ⟨f, g, hfg, hfi, hgj, hne⟩
    refine ⟨g, f, fun v hv => (hfg v ?_).symm, hgj, hfi, hne.symm⟩
    rwa [inter_comm]

theorem not_lopsidependent_of_disjoint [DecidableEq V] (vbl : ι → Finset V)
    (A : ι → Set (∀ v, α v)) {i j : ι} (hd : Disjoint (vbl i) (vbl j)) :
    ¬Lopsidependent vbl A i j := by
  rintro ⟨f, g, hfg, hfi, hgj, hne⟩
  have heq : f = g := funext fun v => hfg v (by simp [disjoint_iff_inter_eq_empty.1 hd])
  subst heq
  rcases hne with h | h <;> exact h (by assumption)

/-- Reflexive lopsidependency relation `i = j ∨ Lopsidependent vbl A i j`. -/
def lopsidedAdj [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (i j : ι) : Prop :=
  i = j ∨ Lopsidependent vbl A i j

theorem lopsidedAdj_iff [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    {i j : ι} : lopsidedAdj vbl A i j ↔ i = j ∨ Lopsidependent vbl A i j := by
  rw [lopsidedAdj]

theorem lopsidedAdj_refl [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (i : ι) : lopsidedAdj vbl A i i :=
  Or.inl rfl

theorem lopsidedAdj_comm [DecidableEq V] (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    {i j : ι} : lopsidedAdj vbl A i j ↔ lopsidedAdj vbl A j i := by
  unfold lopsidedAdj
  rw [eq_comm, lopsidependent_comm]

end Lopsidependent

section CanonicalLog

variable {V ι : Type*} [DecidableEq V] {α : V → Type*} (vbl : ι → Finset V)

private theorem uses_cons_swap (u v : List ι) (a b : ι) (x : V) :
    uses vbl (u ++ a :: b :: v) x = uses vbl (u ++ b :: a :: v) x := by
  induction u with
  | nil =>
    rw [List.nil_append, List.nil_append, uses_cons, uses_cons, uses_cons, uses_cons]
    omega
  | cons c u ih =>
    rw [List.cons_append, List.cons_append, uses_cons, uses_cons, ih]

private theorem current_append_swap (T : ∀ p : V × ℕ, α p.1) (u v : List ι) (a b : ι) :
    current vbl T (u ++ a :: b :: v) = current vbl T (u ++ b :: a :: v) := by
  funext x
  rw [current_apply, current_apply, uses_cons_swap]

private theorem isLog_swap_cons {A : ι → Set (∀ v, α v)}
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1}
    {a b : ι} (hab : ¬Lopsidependent vbl A a b) {v : List ι}
    (h : IsLog vbl A T (a :: b :: v)) : IsLog vbl A T (b :: a :: v) := by
  rw [isLog_cons, isLog_cons] at h ⊢
  rcases h with ⟨hg, hf, hv⟩
  let f := current vbl T v
  let g := current vbl T (b :: v)
  let φ := current vbl T (a :: v)
  let hfn : ∀ x, α x := fun x => if x ∈ vbl a ∩ vbl b then g x else f x
  have h_eq_f : ∀ x, x ∉ vbl a ∩ vbl b → hfn x = f x := fun x hx => ite_eq_right hx
  have h_eq_g : ∀ x ∈ (vbl a : Set V), hfn x = g x := by
    intro x hx
    have hxa : x ∈ vbl a := Finset.mem_coe.1 hx
    by_cases hxb : x ∈ vbl b
    · exact ite_eq_left (mem_inter.2 ⟨hxa, hxb⟩)
    · dsimp [hfn]
      rw [ite_eq_right (fun hm => hxb (mem_inter.1 hm).2)]
      dsimp [f, g]
      rw [current_apply, current_apply, uses_cons, ite_eq_right hxb, add_zero]
  have ha_hfn : hfn ∈ A a := (hA a h_eq_g).mpr hg
  have hnot : ¬(hfn ∉ A b ∨ f ∉ A a) := fun hbad => hab ⟨hfn, f, h_eq_f, ha_hfn, hf, hbad⟩
  rw [not_or, not_not, not_not] at hnot
  have h_eq_φ : ∀ x ∈ (vbl b : Set V), hfn x = φ x := by
    intro x hx
    have hxb : x ∈ vbl b := Finset.mem_coe.1 hx
    by_cases hxa : x ∈ vbl a
    · dsimp [hfn]
      rw [ite_eq_left (mem_inter.2 ⟨hxa, hxb⟩)]
      dsimp [g, φ]
      rw [current_apply, current_apply, uses_cons, uses_cons, ite_eq_left hxb, ite_eq_left hxa]
    · dsimp [hfn]
      rw [ite_eq_right (fun hm => hxa (mem_inter.1 hm).1)]
      dsimp [f, φ]
      rw [current_apply, current_apply, uses_cons, ite_eq_right hxa, add_zero]
  exact ⟨(hA b h_eq_φ).mp hnot.1, hnot.2, hv⟩

private theorem isLog_swap {A : ι → Set (∀ v, α v)}
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1}
    {a b : ι} (hab : ¬Lopsidependent vbl A a b) :
    ∀ u v : List ι, IsLog vbl A T (u ++ a :: b :: v) → IsLog vbl A T (u ++ b :: a :: v)
  | [], v, h => isLog_swap_cons vbl hA hab h
  | c :: u, v, h => by
    rw [List.cons_append, isLog_cons] at h ⊢
    rw [← current_append_swap vbl T u v a b]
    exact ⟨h.1, isLog_swap hA hab u v h.2⟩

private noncomputable def canonList (S : Finset (ι × ℕ)) : List ι :=
  (S.toList.mergeSort (fun a b => decide (a.2 ≤ b.2))).map Prod.fst

section Trace

variable (R : ι → ι → Prop) [DecidableRel R] [DecidableEq ι]

private def foldPush (S₀ : Finset (ι × ℕ)) (w : List ι) : Finset (ι × ℕ) :=
  w.foldl (fun S j => pushRel R j S) S₀

private theorem foldPush_append (S₀ : Finset (ι × ℕ)) (u v : List ι) :
    foldPush R S₀ (u ++ v) = foldPush R (foldPush R S₀ u) v := by
  simp [foldPush, List.foldl_append]

private theorem witnessRel_eq_foldPush (i : ι) (w : List ι) :
    witnessRel R i w = foldPush R {(i, 0)} w := by
  induction w using List.reverseRecOn with
  | nil => rw [witnessRel_nil, foldPush, List.foldl_nil]
  | append_singleton w j ih =>
    rw [witnessRel_append_singleton, ih, foldPush, foldPush, List.foldl_append, List.foldl_cons,
      List.foldl_nil]

private def traceSteps (S₀ : Finset (ι × ℕ)) : List ι → List (Option (ι × ℕ))
  | [] => []
  | j :: w =>
    let l := levelRel R j S₀
    if l = 0 then none :: traceSteps S₀ w
    else some (j, l) :: traceSteps (insert (j, l) S₀) w

private theorem traceSteps_length (S₀ : Finset (ι × ℕ)) (w : List ι) :
    (traceSteps R S₀ w).length = w.length := by
  induction w generalizing S₀ with
  | nil => simp [traceSteps]
  | cons j w ih =>
    simp only [traceSteps]
    split_ifs <;> simp [ih]

private theorem traceSteps_append (S₀ : Finset (ι × ℕ)) (u v : List ι) :
    traceSteps R S₀ (u ++ v) = traceSteps R S₀ u ++ traceSteps R (foldPush R S₀ u) v := by
  induction u generalizing S₀ with
  | nil => simp [traceSteps, foldPush]
  | cons j u ih =>
    simp only [List.cons_append, traceSteps, foldPush, List.foldl_cons]
    by_cases h0 : levelRel R j S₀ = 0
    · simp only [h0, ↓reduceIte, List.cons_append, pushRel_of_eq_zero h0]
      exact congrArg (none :: ·) (ih S₀)
    · simp only [h0, ↓reduceIte, List.cons_append, pushRel_of_ne_zero h0]
      exact congrArg (some (j, levelRel R j S₀) :: ·) (ih (insert (j, levelRel R j S₀) S₀))

private theorem traceSteps_swap (hRs : ∀ {i j}, R i j → R j i) (S₀ : Finset (ι × ℕ))
    {a b : ι} {la : ℕ} {o : Option (ι × ℕ)}
    (hst : traceSteps R S₀ [a, b] = [some (a, la), o])
    (ho : o = none ∨ ∃ lb : ℕ, o = some (b, lb) ∧ lb ≤ la) :
    ¬R a b ∧ traceSteps R S₀ [b, a] = [o, some (a, la)] ∧
      foldPush R S₀ [b, a] = foldPush R S₀ [a, b] := by
  by_cases ha0 : levelRel R a S₀ = 0
  · simp [traceSteps, ha0] at hst
  · have hst' : (if levelRel R b (insert (a, levelRel R a S₀) S₀) = 0 then [none]
        else [some (b, levelRel R b (insert (a, levelRel R a S₀) S₀))]) = [o] ∧
        levelRel R a S₀ = la := by
      simp only [traceSteps, ha0, ↓reduceIte, List.cons.injEq, Option.some.injEq,
        Prod.mk.injEq, true_and] at hst
      exact ⟨hst.2, hst.1⟩
    rcases hst' with ⟨hsb, hla⟩
    subst hla
    set la' := levelRel R a S₀
    set S₁ := insert (a, la') S₀
    rcases ho with rfl | ⟨lb, rfl, hle⟩
    · have hb0 : levelRel R b S₁ = 0 := by
        by_cases h : levelRel R b S₁ = 0
        · exact h
        · simp [h] at hsb
      have hnab : ¬R a b := levelRel_eq_zero hb0 (mem_insert_self _ _)
      have hnba : ¬R b a := fun h => hnab (hRs h)
      have hb0' : levelRel R b S₀ = 0 := by
        rwa [← levelRel_insert_of_not_rel hnab la' S₀]
      refine ⟨hnab, ?_, ?_⟩
      · have ha0' : levelRel R a S₀ ≠ 0 := ha0
        simp only [traceSteps, hb0', ha0', ↓reduceIte]
        rfl
      · simp only [foldPush, List.foldl_cons, List.foldl_nil]
        exact (pushRel_comm_of_not_rel hnba hnab S₀).symm
    · have hb_ne : levelRel R b S₁ ≠ 0 := by
        intro h
        simp [h] at hsb
      have hlb : levelRel R b S₁ = lb := by
        simp only [hb_ne, ↓reduceIte, List.cons.injEq, Option.some.injEq, Prod.mk.injEq,
          and_true] at hsb
        exact hsb.2
      have hnab : ¬R a b := fun hab => by
        have hlt := lt_levelRel (mem_insert_self (a, la') S₀) hab
        dsimp [S₁] at hlb
        rw [hlb] at hlt
        dsimp [la'] at hlt
        omega
      have hnba : ¬R b a := fun h => hnab (hRs h)
      have hlb0 : levelRel R b S₀ = lb := by
        rw [← hlb, ← levelRel_insert_of_not_rel hnab la' S₀]
      have hlb_pos : lb ≠ 0 := hlb ▸ hb_ne
      have hla1 : levelRel R a (insert (b, lb) S₀) = la' :=
        levelRel_insert_of_not_rel hnba lb S₀
      refine ⟨hnab, ?_, ?_⟩
      · simp [traceSteps, hlb0, hlb_pos, hla1, ha0]
      · simp only [foldPush, List.foldl_cons, List.foldl_nil]
        exact (pushRel_comm_of_not_rel hnba hnab S₀).symm

private theorem traceSteps_map_some_eq (hRr : ∀ i, R i i) :
    ∀ (S₀ : Finset (ι × ℕ)) (w : List ι) (L : List (ι × ℕ)),
      traceSteps R S₀ w = L.map some →
      w = L.map Prod.fst ∧ L.Nodup ∧ (∀ p ∈ L, p ∉ S₀) ∧
        foldPush R S₀ w = S₀ ∪ L.toFinset
  | S₀, [], [], _ => by simp [foldPush]
  | S₀, [], p :: L, h => by simp [traceSteps] at h
  | S₀, j :: w, [], h => by
    simp only [traceSteps] at h
    split_ifs at h <;> simp at h
  | S₀, j :: w, p :: L, h => by
    simp only [traceSteps] at h
    split_ifs at h with h0
    · simp at h
    · rcases List.cons.inj h with ⟨hp, hw⟩
      obtain rfl := Option.some.inj hp
      obtain ⟨hwm, hnodup, hnot, hfold⟩ :=
        traceSteps_map_some_eq hRr (insert (j, levelRel R j S₀) S₀) w L hw
      have hnot0 : (j, levelRel R j S₀) ∉ S₀ := levelRel_notMem hRr j S₀
      refine ⟨by simp [hwm], List.nodup_cons.2 ⟨fun hm => hnot _ hm (mem_insert_self _ _), hnodup⟩,
        fun q hq => ?_, ?_⟩
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact hnot0
        · exact fun hm => hnot q hq (mem_insert_of_mem hm)
      · rw [foldPush, List.foldl_cons, pushRel_of_ne_zero h0, ← foldPush, hfold,
          List.toFinset_cons]
        ext q
        simp [or_left_comm]

private theorem traceSteps_split_none :
    ∀ (S₀ : Finset (ι × ℕ)) (w : List ι),
      none ∈ traceSteps R S₀ w →
      ∃ k < w.length, (traceSteps R S₀ w)[k]? = some none ∧
        ∀ m < k, ∃ p, (traceSteps R S₀ w)[m]? = some (some p)
  | S₀, [], h => by simp [traceSteps] at h
  | S₀, j :: w, h => by
    simp only [traceSteps] at h ⊢
    split_ifs at h with h0
    · exact ⟨0, by simp, by simp [h0], fun m hm => by omega⟩
    · simp only [List.mem_cons, reduceCtorEq, false_or] at h
      obtain ⟨k, hk, heq, hpre⟩ := traceSteps_split_none (insert (j, levelRel R j S₀) S₀) w h
      refine ⟨k + 1, Nat.succ_lt_succ hk, ?_, fun m hm => ?_⟩
      · simpa [h0] using heq
      · cases m with
        | zero => exact ⟨(j, levelRel R j S₀), by simp [h0]⟩
        | succ m => simpa [h0] using hpre m (Nat.lt_of_succ_lt_succ hm)

private theorem traceSteps_split_at (S₀ : Finset (ι × ℕ)) (w : List ι) (k : ℕ)
    (hk : k + 1 < w.length) :
    let u := w.take k
    let a := w[k]
    let b := w[k + 1]
    let v := w.drop (k + 2)
    w = u ++ a :: b :: v ∧
      traceSteps R S₀ w = traceSteps R S₀ u ++ traceSteps R (foldPush R S₀ u) [a, b] ++
        traceSteps R (foldPush R (foldPush R S₀ u) [a, b]) v := by
  intro u a b v
  have hw : w = u ++ a :: b :: v := by
    have h1 := List.take_append_drop k w
    have hdrop : w.drop k = a :: b :: v := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
    rw [hdrop] at h1
    exact h1.symm
  refine ⟨hw, ?_⟩
  conv_lhs => rw [hw]
  rw [traceSteps_append, show (a :: b :: v) = [a, b] ++ v from rfl, traceSteps_append,
    List.append_assoc]

private theorem traceSteps_two_eq_iff (S₀ : Finset (ι × ℕ)) (a b : ι)
    (o₁ o₂ : Option (ι × ℕ)) :
    (traceSteps R S₀ [a, b])[0]? = some o₁ ∧ (traceSteps R S₀ [a, b])[1]? = some o₂ →
      traceSteps R S₀ [a, b] = [o₁, o₂] := by
  intro ⟨h0, h1⟩
  have hlen : (traceSteps R S₀ [a, b]).length = 2 := traceSteps_length R S₀ [a, b]
  match h : traceSteps R S₀ [a, b], hlen with
  | [x, y], _ =>
    rw [h] at h0 h1
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h1
    rw [h0, h1]

end Trace

private theorem phase1_elim_none {A : ι → Set (∀ v, α v)}
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1}
    [DecidableEq ι] [DecidableRel (lopsidedAdj vbl A)] (i : ι) :
    ∀ (n : ℕ) (w : List ι), w.length = n → IsLog vbl A T (i :: w) →
      ∃ w' : List ι, IsLog vbl A T (i :: w') ∧
        witnessRel (lopsidedAdj vbl A) i w' = witnessRel (lopsidedAdj vbl A) i w ∧
        ∃ L : List (ι × ℕ),
          traceSteps (lopsidedAdj vbl A) {(i, 0)} w' = L.map some := by
  let R := lopsidedAdj vbl A
  have hRs : ∀ {a b}, R a b → R b a := fun h => (lopsidedAdj_comm vbl A).1 h
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ihn =>
    intro w hlen hlog
    by_cases hnone : none ∈ traceSteps R {(i, 0)} w
    · obtain ⟨k, hk, hkq, hpre⟩ := traceSteps_split_none R {(i, 0)} w hnone
      induction k generalizing w with
      | zero =>
        cases w with
        | nil => simp at hk
        | cons j w' =>
          have hj0 : levelRel R j {(i, 0)} = 0 := by
            by_cases h0 : levelRel R j {(i, 0)} = 0
            · exact h0
            · simp [traceSteps, h0] at hkq
          have hnij : ¬R i j := levelRel_eq_zero hj0 (mem_singleton_self _)
          have hnlop : ¬Lopsidependent vbl A i j := fun h => hnij (Or.inr h)
          have hlog' : IsLog vbl A T (i :: w') :=
            ((isLog_cons vbl).1 (isLog_swap vbl hA hnlop [] w' hlog)).2
          have hw' : witnessRel R i (j :: w') = witnessRel R i w' :=
            witnessRel_cons_of_not_rel R hnij w'
          obtain ⟨w'', hl'', hw'', L, hL⟩ :=
            ihn w'.length (by simp only [List.length_cons] at hlen; omega) w' rfl hlog'
          exact ⟨w'', hl'', hw''.trans hw'.symm, L, hL⟩
      | succ k ihk =>
        set u := w.take k
        set a := w[k]
        set b := w[k + 1]
        set v := w.drop (k + 2)
        obtain ⟨hw_eq, happ⟩ := traceSteps_split_at R {(i, 0)} w k hk
        have hulen : u.length = k := List.length_take_of_le (by omega)
        obtain ⟨pa, hpa⟩ := hpre k (Nat.lt_succ_self k)
        have hstep_ab :
            traceSteps R (foldPush R {(i, 0)} u) [a, b] = [some pa, none] := by
          refine traceSteps_two_eq_iff R (foldPush R {(i, 0)} u) a b (some pa) none ⟨?_, ?_⟩
          · rw [happ, List.append_assoc,
              List.getElem?_append_right (by rw [traceSteps_length, hulen]),
              traceSteps_length, hulen, Nat.sub_self,
              List.getElem?_append_left (by rw [traceSteps_length]; exact Nat.zero_lt_two)] at hpa
            exact hpa
          · rw [happ, List.append_assoc,
              List.getElem?_append_right (by rw [traceSteps_length, hulen]; omega),
              traceSteps_length, hulen, Nat.add_sub_cancel_left,
              List.getElem?_append_left (by rw [traceSteps_length]; exact Nat.one_lt_two)] at hkq
            exact hkq
        have ha_eq' : pa = (a, levelRel R a (foldPush R {(i, 0)} u)) := by
          by_cases ha0 : levelRel R a (foldPush R {(i, 0)} u) = 0
          · simp [traceSteps, ha0] at hstep_ab
          · simp only [traceSteps, ha0, ↓reduceIte, List.cons.injEq, Option.some.injEq] at hstep_ab
            exact hstep_ab.1.symm
        have hstep_ab' : traceSteps R (foldPush R {(i, 0)} u) [a, b] =
            [some (a, pa.2), none] := by
          rw [hstep_ab, ha_eq']
        obtain ⟨hnab, hswap_tr, hswap_fold⟩ :=
          traceSteps_swap R hRs (foldPush R {(i, 0)} u) hstep_ab' (Or.inl rfl)
        have hnlop : ¬Lopsidependent vbl A a b := fun h => hnab (Or.inr h)
        set w' := u ++ b :: a :: v
        have hw'len : w'.length = n := by
          have h1 := congrArg List.length hw_eq
          dsimp [w', u, v] at h1 ⊢
          simp only [List.length_append, List.length_cons] at h1 ⊢
          omega
        have hlog' : IsLog vbl A T (i :: w') := by
          have h0 : IsLog vbl A T ((i :: u) ++ a :: b :: v) := by
            rw [List.cons_append, ← hw_eq]
            exact hlog
          have h1 := isLog_swap vbl hA hnlop (i :: u) v h0
          rw [List.cons_append] at h1
          exact h1
        have hw'eq : witnessRel R i w' = witnessRel R i w := by
          have hbav : w' = u ++ [b, a] ++ v := by simp [w']
          have habv : w = u ++ [a, b] ++ v := by
            have hw_eq' : w = u ++ a :: b :: v := hw_eq
            conv_lhs => rw [hw_eq']
            simp
          rw [witnessRel_eq_foldPush, witnessRel_eq_foldPush, hbav, habv,
            foldPush_append, foldPush_append, foldPush_append, foldPush_append, hswap_fold]
        have htr_w' : traceSteps R {(i, 0)} w' = traceSteps R {(i, 0)} u ++
            [none, some (a, pa.2)] ++
            traceSteps R (foldPush R (foldPush R {(i, 0)} u) [a, b]) v := by
          have hbav : w' = u ++ [b, a] ++ v := by simp [w']
          rw [hbav, traceSteps_append, traceSteps_append, foldPush_append, hswap_tr, hswap_fold]
        have hkq' : (traceSteps R {(i, 0)} w')[k]? = some none := by
          rw [htr_w', List.append_assoc,
            List.getElem?_append_right (by rw [traceSteps_length, hulen]),
            traceSteps_length, hulen, Nat.sub_self]
          rfl
        have hpre' : ∀ m < k, ∃ p, (traceSteps R {(i, 0)} w')[m]? = some (some p) := by
          intro m hm
          rw [htr_w', List.append_assoc,
            List.getElem?_append_left (by rw [traceSteps_length, hulen]; exact hm)]
          have hpm := hpre m (Nat.lt_succ_of_lt hm)
          rw [happ, List.append_assoc,
            List.getElem?_append_left (by
              rw [traceSteps_length, List.length_take_of_le (by omega)]
              exact hm)] at hpm
          exact hpm
        obtain ⟨w'', hl'', hw'', L, hL⟩ :=
          ihk w' hw'len hlog' (List.mem_of_getElem? hkq') (by omega) hkq' hpre'
        exact ⟨w'', hl'', hw''.trans hw'eq, L, hL⟩
    · suffices hmap : ∀ l : List (Option (ι × ℕ)), none ∉ l →
          ∃ L : List (ι × ℕ), l = L.map some from
        ⟨w, hlog, rfl, hmap _ hnone⟩
      intro l hl
      induction l with
      | nil => exact ⟨[], rfl⟩
      | cons o os ih =>
        cases o with
        | none => exact absurd List.mem_cons_self hl
        | some p =>
          obtain ⟨L, hL⟩ := ih fun hm => hl (List.mem_cons_of_mem _ hm)
          exact ⟨p :: L, by simp [hL]⟩

private theorem phase2_sort_perm {A : ι → Set (∀ v, α v)}
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1}
    [DecidableEq ι] [DecidableRel (lopsidedAdj vbl A)] :
    ∀ (c : List (ι × ℕ)) (pref : List (ι × ℕ)) (S₀' : Finset (ι × ℕ))
      (w : List ι) (L : List (ι × ℕ)),
      IsLog vbl A T ((pref.map Prod.fst) ++ w) →
      traceSteps (lopsidedAdj vbl A) S₀' w = L.map some →
      L.Perm c → c.Pairwise (fun a b => a.2 ≤ b.2) → c.Nodup →
      IsLog vbl A T ((pref.map Prod.fst) ++ c.map Prod.fst)
  | [], _, S₀', w, L, hlog, htr, hperm, _, _ => by
    obtain rfl := hperm.eq_nil
    cases w with
    | nil => exact hlog
    | cons j w =>
      simp only [traceSteps, List.map_nil] at htr
      split_ifs at htr
  | p :: c', pref, S₀', w, L, hlog, htr, hperm, hpair, hnod => by
    let R := lopsidedAdj vbl A
    have hRs : ∀ {a b}, R a b → R b a := fun h => (lopsidedAdj_comm vbl A).1 h
    have hpL : p ∈ L := hperm.symm.subset List.mem_cons_self
    obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hpL
    have hsub : ∀ k (w : List ι) (L₁ L₂ : List (ι × ℕ)),
        L₁.length = k →
        IsLog vbl A T ((pref.map Prod.fst) ++ w) →
        traceSteps R S₀' w = (L₁ ++ p :: L₂).map some →
        (L₁ ++ p :: L₂).Perm (p :: c') →
        IsLog vbl A T ((pref.map Prod.fst) ++ (p :: c').map Prod.fst) := by
      intro k
      induction k with
      | zero =>
        intro w' L₁' L₂' hk0 hlog' htr' hperm'
        obtain rfl := List.length_eq_zero_iff.1 hk0
        rw [List.nil_append] at htr' hperm'
        cases w' with
        | nil => simp [traceSteps] at htr'
        | cons j w'' =>
          simp only [traceSteps, List.map_cons] at htr'
          split_ifs at htr' with hj0
          · simp at htr'
          · rcases List.cons.inj htr' with ⟨hjp, htr''⟩
            have hjp' := (Option.some.inj hjp).symm
            have hj_fst : j = p.1 := congrArg Prod.fst hjp'.symm
            have hperm'' : L₂'.Perm c' := hperm'.cons_inv
            have hpair' := (List.pairwise_cons.1 hpair).2
            have hnod' := (List.nodup_cons.1 hnod).2
            have hlog_sub : IsLog vbl A T (((pref ++ [p]).map Prod.fst) ++ w'') := by
              simpa [List.append_assoc, hj_fst] using hlog'
            have htr_sub : traceSteps R (insert p S₀') w'' = L₂'.map some := by
              simpa [hjp'] using htr''
            have ih := phase2_sort_perm hA c' (pref ++ [p]) (insert p S₀') w'' L₂'
              hlog_sub htr_sub hperm'' hpair' hnod'
            simpa [List.append_assoc] using ih
      | succ k ihk =>
        intro w' L₁' L₂' hlen1 hlog' htr' hperm'
        rcases List.eq_nil_or_concat L₁' with rfl | ⟨L₀, q, hL₁⟩
        · simp at hlen1
        rw [hL₁, List.concat_eq_append] at hlen1 htr' hperm'
        have hlen0 : L₀.length = k := by simpa using hlen1
        have hnodL : (L₀ ++ [q] ++ p :: L₂').Nodup := hperm'.nodup_iff.2 hnod
        have hqp : q ≠ p := by
          intro h
          subst h
          simp only [List.nodup_append] at hnodL
          exact hnodL.2.2 q (by simp) q List.mem_cons_self rfl
        have hqc' : q ∈ c' := by
          have hmem : q ∈ p :: c' := hperm'.subset (by simp)
          exact (List.mem_cons.1 hmem).resolve_left hqp
        have hle : p.2 ≤ q.2 := (List.pairwise_cons.1 hpair).1 q hqc'
        have hwk : k + 1 < w'.length := by
          have := congrArg List.length htr'
          rw [traceSteps_length] at this
          simp only [List.length_map, List.length_append, List.length_cons] at this
          omega
        set u := w'.take k
        set a := w'[k]
        set b := w'[k + 1]
        set v := w'.drop (k + 2)
        obtain ⟨hw_eq, happ⟩ := traceSteps_split_at R S₀' w' k hwk
        have hulen : u.length = k := List.length_take_of_le (by omega)
        have happ' : traceSteps R S₀' u ++ traceSteps R (foldPush R S₀' u) [a, b] ++
            traceSteps R (foldPush R (foldPush R S₀' u) [a, b]) v =
            L₀.map some ++ [some q, some p] ++ L₂'.map some := by
          rw [← happ, htr']
          simp [List.map_append]
        have hlen_u : (traceSteps R S₀' u).length = (L₀.map some).length := by
          rw [traceSteps_length, hulen, List.length_map, hlen0]
        rw [List.append_assoc, List.append_assoc] at happ'
        obtain ⟨hpre_u, hsuf_u⟩ := List.append_inj happ' hlen_u
        obtain ⟨hst_ab, htail⟩ := List.append_inj hsuf_u (by rw [traceSteps_length]; rfl)
        have haq_val : q = (a, levelRel R a (foldPush R S₀' u)) := by
          by_cases ha0 : levelRel R a (foldPush R S₀' u) = 0
          · simp [traceSteps, ha0] at hst_ab
          · simp only [traceSteps, ha0, ↓reduceIte, List.cons.injEq, Option.some.injEq] at hst_ab
            exact hst_ab.1.symm
        have haq : q = (a, q.2) := by
          rw [haq_val]
        have hbp_val : p = (b, levelRel R b (insert (a, levelRel R a (foldPush R S₀' u))
            (foldPush R S₀' u))) := by
          by_cases ha0 : levelRel R a (foldPush R S₀' u) = 0
          · simp [traceSteps, ha0] at hst_ab
          · simp only [traceSteps, ha0, ↓reduceIte, List.cons.injEq] at hst_ab
            by_cases hb0 : levelRel R b (insert (a, levelRel R a (foldPush R S₀' u))
                (foldPush R S₀' u)) = 0
            · simp [hb0] at hst_ab
            · simp only [hb0, ↓reduceIte, List.cons.injEq, Option.some.injEq, and_true] at hst_ab
              exact hst_ab.2.symm
        have hbp : p = (b, p.2) := by
          rw [hbp_val]
        have hst_ab' : traceSteps R (foldPush R S₀' u) [a, b] = [some (a, q.2), some (b, p.2)] := by
          rw [hst_ab, ← haq, ← hbp]
        obtain ⟨hnab, hswap_tr, hswap_fold⟩ :=
          traceSteps_swap R hRs (foldPush R S₀' u) hst_ab' (Or.inr ⟨p.2, rfl, hle⟩)
        have hnlop : ¬Lopsidependent vbl A a b := fun h => hnab (Or.inr h)
        set w'' := u ++ b :: a :: v
        have hlog'' : IsLog vbl A T ((pref.map Prod.fst) ++ w'') := by
          have h0 : IsLog vbl A T ((pref.map Prod.fst ++ u) ++ a :: b :: v) := by
            rw [List.append_assoc, ← hw_eq]
            exact hlog'
          have h1 := isLog_swap vbl hA hnlop (pref.map Prod.fst ++ u) v h0
          exact (List.append_assoc (pref.map Prod.fst) u (b :: a :: v)).symm ▸ h1
        have htr'' : traceSteps R S₀' w'' = (L₀ ++ p :: (q :: L₂')).map some := by
          have hbav : w'' = u ++ [b, a] ++ v := by simp [w'']
          rw [hbav, traceSteps_append, traceSteps_append, foldPush_append, hpre_u, hswap_tr,
            hswap_fold, htail]
          simp [haq.symm, hbp.symm, List.map_append]
        have hperm'' : (L₀ ++ p :: q :: L₂').Perm (L₀ ++ [q] ++ p :: L₂') := by
          rw [List.append_assoc, List.singleton_append]
          exact List.Perm.append_left L₀ (List.Perm.swap q p L₂')
        exact ihk w'' L₀ (q :: L₂') hlen0 hlog'' htr'' (hperm''.trans hperm')
    exact hsub L₁.length w L₁ L₂ rfl hlog htr hperm

/-- Any valid log `i :: w` whose lopsided witness structure is `S` implies that the canonical
depth-ordered log `canonList S` is also valid on `T` [MoserTardos2010, Lemma 6.2]. -/
private theorem isLog_canonList {A : ι → Set (∀ v, α v)}
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {T : ∀ p : V × ℕ, α p.1}
    [DecidableEq ι] [DecidableRel (lopsidedAdj vbl A)]
    {i : ι} {w : List ι} {S : Finset (ι × ℕ)} (hlog : IsLog vbl A T (i :: w))
    (hS : witnessRel (lopsidedAdj vbl A) i w = S) :
    IsLog vbl A T (canonList S) := by
  let R := lopsidedAdj vbl A
  have hRr : ∀ a, R a a := lopsidedAdj_refl vbl A
  obtain ⟨w₁, hlog₁, hw₁, L, htr⟩ := phase1_elim_none vbl hA i w.length w rfl hlog
  have hS₁ : witnessRel R i w₁ = S := hw₁.trans hS
  obtain ⟨rfl, hnodL, hnotL, hfold⟩ := traceSteps_map_some_eq R hRr {(i, 0)} w₁ L htr
  rw [← witnessRel_eq_foldPush, hS₁] at hfold
  have hnot_root : (i, 0) ∉ L := fun hm => hnotL _ hm (mem_singleton_self _)
  set sorted := S.toList.mergeSort (fun a b => decide (a.2 ≤ b.2))
  have hpermS : sorted.Perm S.toList := List.mergeSort_perm S.toList _
  have hpairS : sorted.Pairwise (fun a b => a.2 ≤ b.2) := by
    refine (List.pairwise_mergeSort (le := fun (a b : ι × ℕ) => decide (a.2 ≤ b.2))
      (fun a b c h1 h2 => decide_eq_true (Nat.le_trans (of_decide_eq_true h1)
        (of_decide_eq_true h2)))
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega)
      S.toList).imp fun {a b} hab => of_decide_eq_true hab
  have hroot : RootedRel R i S := hS₁ ▸ rooted_witnessRel R i (L.map Prod.fst)
  have hne : sorted ≠ [] := by
    intro h
    have : (i, 0) ∈ sorted := hpermS.symm.subset (mem_toList.2 hroot.root)
    rw [h] at this
    simp at this
  obtain ⟨p₀, t, hsorted⟩ := List.exists_cons_of_ne_nil hne
  have hp₀ : p₀ = (i, 0) := by
    have hp₀S : p₀ ∈ S := mem_toList.1 (hpermS.subset (by simp [hsorted]))
    have hi0 : (i, 0) ∈ t ∨ p₀ = (i, 0) := by
      have hmem : (i, 0) ∈ p₀ :: t := hsorted ▸ hpermS.symm.subset (mem_toList.2 hroot.root)
      rcases List.mem_cons.1 hmem with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    rcases hi0 with hit | rfl
    · have hle := (List.pairwise_cons.1 (hsorted ▸ hpairS)).1 (i, 0) hit
      exact hroot.zero p₀ hp₀S (Nat.eq_zero_of_le_zero hle)
    · rfl
  subst hp₀
  have hnod_sorted : ((i, 0) :: t).Nodup := hsorted ▸ hpermS.nodup_iff.2 S.nodup_toList
  have hpair_t : t.Pairwise (fun a b => a.2 ≤ b.2) := (List.pairwise_cons.1 (hsorted ▸ hpairS)).2
  have hnod_t : t.Nodup := (List.nodup_cons.1 hnod_sorted).2
  have hperm_ins : ((i, 0) :: L).Perm S.toList := by
    rw [List.perm_iff_count]
    intro q
    have hnod1 : ((i, 0) :: L).Nodup := List.nodup_cons.2 ⟨hnot_root, hnodL⟩
    have hnod2 : S.toList.Nodup := S.nodup_toList
    by_cases hq : q ∈ (i, 0) :: L
    · have hq2 : q ∈ S.toList := by
        rw [mem_toList, hfold, mem_union, mem_singleton]
        simpa [List.mem_cons, List.mem_toFinset] using hq
      rw [List.count_eq_one_of_mem hnod1 hq, List.count_eq_one_of_mem hnod2 hq2]
    · have hq2 : q ∉ S.toList := by
        rw [mem_toList, hfold, mem_union, mem_singleton]
        simpa [List.mem_cons, List.mem_toFinset] using hq
      rw [List.count_eq_zero.2 hq, List.count_eq_zero.2 hq2]
  have hperm_t : L.Perm t :=
    (hperm_ins.trans (hsorted ▸ hpermS.symm)).cons_inv
  have hres := phase2_sort_perm vbl hA t [(i, 0)] {(i, 0)} (L.map Prod.fst) L
    hlog₁ htr hperm_t hpair_t hnod_t
  change IsLog vbl A T (sorted.map Prod.fst)
  rw [hsorted, List.map_cons]
  exact hres

end CanonicalLog

namespace Lopsided

section Measure

variable {V ι : Type*} [Fintype V] [DecidableEq V] {α : V → Type*}
  [∀ v, MeasurableSpace (α v)] (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
  (vbl : ι → Finset V)

private def stepCoords (vbl : ι → Finset V) : List ι → Finset (V × ℕ)
  | [] => ∅
  | j :: w => ((vbl j).image fun v => (v, uses vbl w v)) ∪ stepCoords vbl w

omit [Fintype V] [∀ v, MeasurableSpace (α v)] [∀ v, IsProbabilityMeasure (μ v)] in
private theorem lt_uses_of_mem_stepCoords :
    ∀ {w : List ι} {p : V × ℕ}, p ∈ stepCoords vbl w → p.2 < uses vbl w p.1
  | [], _, hp => by simp [stepCoords] at hp
  | j :: w, ⟨v, k⟩, hp => by
    simp only [stepCoords, mem_union, mem_image] at hp
    rw [uses_cons]
    rcases hp with ⟨v', hv', he⟩ | hp
    · rcases Prod.mk.inj he with ⟨rfl, rfl⟩
      simp [hv']
    · exact Nat.lt_of_lt_of_le (lt_uses_of_mem_stepCoords hp) (Nat.le_add_right _ _)

omit [Fintype V] [∀ v, MeasurableSpace (α v)] [∀ v, IsProbabilityMeasure (μ v)] in
private theorem disjoint_stepCoords (j : ι) (w : List ι) :
    Disjoint ((vbl j).image fun v => (v, uses vbl w v)) (stepCoords vbl w) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨v, -, rfl⟩ := mem_image.1 hp
  exact lt_irrefl _ (lt_uses_of_mem_stepCoords vbl hq)

omit [Fintype V] [∀ v, MeasurableSpace (α v)] [∀ v, IsProbabilityMeasure (μ v)] in
private theorem isLog_dependsOn (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) :
    ∀ w : List ι, DependsOn (fun T => IsLog vbl A T w) (stepCoords vbl w : Set (V × ℕ))
  | [], T, T', _ => by simp [isLog_nil]
  | j :: w, T, T', h => by
    have hcur : (fun v => T (v, uses vbl w v)) ∈ A j ↔
        (fun v => T' (v, uses vbl w v)) ∈ A j := by
      refine (hA j fun v hv => h (v, uses vbl w v) ?_).to_iff
      exact Finset.mem_coe.2 (mem_union_left _ (mem_image_of_mem _ (Finset.mem_coe.1 hv)))
    have htail : IsLog vbl A T w = IsLog vbl A T' w :=
      isLog_dependsOn A hA w fun c hc =>
        h c (Finset.mem_coe.2 (mem_union_right _ (Finset.mem_coe.1 hc)))
    have hfun : ∀ T₀ : ∀ p : V × ℕ, α p.1,
        current vbl T₀ w = fun v => T₀ (v, uses vbl w v) :=
      fun T₀ => funext fun v => current_apply vbl T₀ w v
    change IsLog vbl A T (j :: w) = IsLog vbl A T' (j :: w)
    rw [isLog_cons, isLog_cons, hfun T, hfun T']
    exact propext (and_congr hcur (iff_of_eq htail))

/-- For any fixed list `w`, the event `IsLog vbl A T w` reads pairwise disjoint table entries,
so its probability is `∏ j ∈ w, Pr[A j]`. -/
theorem table_isLog_eq_prod (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) :
    ∀ w : List ι, table μ {T | IsLog vbl A T w} = (w.map fun i => Measure.pi μ (A i)).prod
  | [] => by simp [isLog_nil]
  | j :: w => by
    have heq : {T : ∀ p : V × ℕ, α p.1 | IsLog vbl A T (j :: w)} =
        (fun T v => T (v, uses vbl w v)) ⁻¹' A j ∩ {T | IsLog vbl A T w} := by
      ext T
      rw [Set.mem_ofPred_eq, isLog_cons]
      have hcur : current vbl T w = fun v => T (v, uses vbl w v) :=
        funext fun v => current_apply vbl T w v
      rw [hcur]
      rfl
    have hm1 : MeasurableSet ((fun (T : ∀ p : V × ℕ, α p.1) v => T (v, uses vbl w v)) ⁻¹' A j) :=
      measurable_read (fun v => uses vbl w v) (hAm j)
    have hm2 : MeasurableSet {T : ∀ p : V × ℕ, α p.1 | IsLog vbl A T w} :=
      measurableSet_isLog vbl A hAm w
    have hd1 : DependsOn
        (· ∈ (fun (T : ∀ p : V × ℕ, α p.1) v => T (v, uses vbl w v)) ⁻¹' A j)
        (((vbl j).image fun v => (v, uses vbl w v)) : Set (V × ℕ)) := fun T T' h =>
      hA j fun v hv => h (v, uses vbl w v)
        (Finset.mem_coe.2 (mem_image_of_mem _ (Finset.mem_coe.1 hv)))
    have hind := indepSet_infinitePi_of_dependsOn (P := fun p : V × ℕ => μ p.1)
      (S := (vbl j).image fun v => (v, uses vbl w v)) (T := stepCoords vbl w)
      hm1 hm2 hd1 (isLog_dependsOn vbl A hA w) (disjoint_stepCoords vbl j w)
    rw [heq, table_def, hind.measure_inter_eq_mul, ← table_def, List.map_cons, List.prod_cons,
      table_isLog_eq_prod A hAm hA w]
    congr 1
    rw [← Measure.map_apply (measurable_read _) (hAm j), table_map_read]

private theorem table_canonList_eq_prod (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (S : Finset (ι × ℕ)) :
    table μ {T | IsLog vbl A T (canonList S)} = ∏ p ∈ S, Measure.pi μ (A p.1) := by
  rw [table_isLog_eq_prod μ vbl A hAm hA (canonList S)]
  have hperm : ((canonList S).map fun j => Measure.pi μ (A j)).Perm
      (S.toList.map fun p => Measure.pi μ (A p.1)) := by
    rw [canonList, List.map_map]
    exact (List.mergeSort_perm S.toList _).map _
  rw [hperm.prod_eq, Finset.prod_map_toList]

open scoped Classical in
/-- **Lemma 6.2** of [MoserTardos2010]: the probability that a fixed structure `S` occurs as the
lopsided witness structure of a step of some valid log on the table is at most
`∏ p ∈ S, Pr[A p.1]`. -/
theorem table_witness_le [DecidableEq ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (S : Finset (ι × ℕ)) :
    table μ {T | ∃ i w, IsLog vbl A T (i :: w) ∧
        witnessRel (lopsidedAdj vbl A) i w = S} ≤
      ∏ p ∈ S, Measure.pi μ (A p.1) := by
  have hsub : {T : ∀ p : V × ℕ, α p.1 | ∃ i w, IsLog vbl A T (i :: w) ∧
      witnessRel (lopsidedAdj vbl A) i w = S} ⊆ {T | IsLog vbl A T (canonList S)} := by
    intro T ⟨i, w, hlog, hS⟩
    exact isLog_canonList vbl hA hlog hS
  exact (measure_mono hsub).trans (table_canonList_eq_prod μ vbl A hAm hA S).le

end Measure

section Theorem

variable {V ι : Type*} [Fintype V] [DecidableEq V] {α : V → Type*}
  [∀ v, MeasurableSpace (α v)] (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
  (vbl : ι → Finset V)

/-- **Lopsided Moser–Tardos, for all valid logs at once** [MoserTardos2010, Theorem 6.1]. Under
the lopsided local-lemma hypothesis, where `Γ i` contains every other event lopsidependent on
`A i`, the expected supremum over all valid logs of `w.count i` is at most `x i / (1 - x i)`. -/
theorem lintegral_iSup_count_le [DecidableEq ι] [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) (i : ι) :
    ∫⁻ T, ⨆ (w : List ι) (_ : IsLog vbl A T w), (w.count i : ℝ≥0∞) ∂table μ ≤
      ENNReal.ofReal (x i / (1 - x i)) := by
  have := Fintype.ofFinite ι
  let _ : DecidableRel (lopsidedAdj vbl A) := Classical.decRel _
  refine lintegral_iSup_count_le_of_pass μ vbl (lopsidedAdj vbl A) (lopsidedAdj_refl vbl A) A
    (fun S T => IsLog vbl A T (canonList S))
    (fun S => measurableSet_isLog vbl A hAm (canonList S))
    (fun S => (table_canonList_eq_prod μ vbl A hAm hA S).le)
    (fun T j H w hw hl => ?_) Γ
    (fun a b hne hadj => hΓ a b hne (hadj.resolve_left hne.symm)) hx hP i
  obtain ⟨W, hcard, hW⟩ := exists_witnessesRel (lopsidedAdj vbl A) (lopsidedAdj_refl vbl A)
    (fun h => (lopsidedAdj_comm vbl A).1 h) j H w hl (IsLog vbl A T)
    (fun a u h => ((isLog_cons vbl).1 h).2) hw
  refine ⟨W, hcard, fun S hS => ?_⟩
  obtain ⟨hsh, -, u, hu, hiu⟩ := hW S hS
  exact ⟨hsh, isLog_canonList vbl hA hiu hu.symm⟩

/-- **Lopsided Moser–Tardos theorem** [MoserTardos2010, Theorem 6.1]. Let `x i ∈ [0, 1)` with
`Pr[A i] ≤ x i ∏ j ∈ Γ i, (1 - x j)`, where `Γ i` contains every other event lopsidependent on
`A i`. Then every valid selection rule resamples `A i` at most `x i / (1 - x i)` times in
expectation. -/
theorem lintegral_resamplings_le [DecidableEq ι] [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) (i : ι) :
    ∫⁻ T, resamplings sel i T ∂table μ ≤ ENNReal.ofReal (x i / (1 - x i)) :=
  lintegral_resamplings_le_of_bound μ vbl A (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i)
    hsel

/-- **Theorem 6.1 for the outer expectation** [MoserTardos2010]: one measurable function with
expectation at most `x i / (1 - x i)` bounds the resampling count under every valid rule. -/
theorem exists_measurable_ge_resamplings [DecidableEq ι] [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) (i : ι) :
    ∃ g : (∀ p : V × ℕ, α p.1) → ℝ≥0∞, Measurable g ∧
      ∫⁻ T, g T ∂table μ ≤ ENNReal.ofReal (x i / (1 - x i)) ∧
      ∀ sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι,
        (∀ T w j, sel T w = some j → current vbl T w ∈ A j) →
          ∀ T, resamplings sel i T ≤ g T :=
  exists_measurable_ge_resamplings_of_bound μ vbl A hAm
    (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i)

/-- **Expected total resamplings under lopsidependence** [MoserTardos2010, Theorem 6.1]: at most
`∑ i, x i / (1 - x i)` for every valid selection rule. -/
theorem lintegral_sum_resamplings_le [DecidableEq ι] [Fintype ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) :
    ∫⁻ T, ∑ i, resamplings sel i T ∂table μ ≤ ∑ i, ENNReal.ofReal (x i / (1 - x i)) :=
  lintegral_sum_resamplings_le_of_bound μ vbl A hAm
    (fun i => lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i) hsel

/-- **Termination under lopsidependence** [MoserTardos2010, Theorem 6.1]: almost surely every
valid rule stops in finitely many steps. -/
theorem ae_exists_run_eq_none [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) :
    ∀ᵐ T ∂table μ, ∃ n, sel T (run sel T n) = none :=
  ae_exists_run_eq_none_of_bound μ vbl A hAm
    (fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i))
    hsel

/-- **Algorithmic lopsided local lemma** [MoserTardos2010, Theorem 6.1]: almost surely any valid
rule that stops only when no event occurs reaches an avoiding assignment. -/
theorem ae_exists_forall_notMem_run [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i)
    (hstop : ∀ T w, sel T w = none → ∀ i, current vbl T w ∉ A i) :
    ∀ᵐ T ∂table μ, ∃ n, ∀ i, current vbl T (run sel T n) ∉ A i :=
  ae_exists_forall_notMem_run_of_bound μ vbl A hAm
    (fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i))
    hsel hstop

/-- **Greedy lopsided Moser–Tardos** [MoserTardos2010, Theorem 6.1]: almost surely the greedy run
reaches an assignment avoiding every event. -/
theorem ae_exists_forall_notMem_run_greedy [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∀ᵐ T ∂table μ, ∃ n, ∀ i, current vbl T (run (greedy vbl A) T n) ∉ A i :=
  ae_exists_forall_notMem_run_greedy_of_bound μ vbl A hAm
    (fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i))

/-- **Constructive lopsided local lemma** [MoserTardos2010, Theorem 6.1]. -/
theorem exists_forall_notMem [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi μ).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∃ σ : ∀ v, α v, ∀ i, σ ∉ A i := by
  classical
  exact exists_forall_notMem_of_bound μ vbl A hAm
    (fun i => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_iSup_count_le μ vbl A hAm hA Γ hΓ hx hP i))

section Symmetric

/-- **Symmetric lopsided Moser–Tardos** (`1 ≤ d`): expected resamplings at most `1 / d` when each
`A i` has probability at most `q`, lopsidependency degree at most `d`, and `e * q * (d + 1) ≤ 1`. -/
theorem lintegral_resamplings_le_symmetric [DecidableEq ι] [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {d : ℕ} (hdpos : 1 ≤ d) (hd : ∀ i, #(Γ i) ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) (i : ι) :
    ∫⁻ T, resamplings sel i T ∂table μ ≤ ENNReal.ofReal (1 / (d : ℝ)) := by
  obtain ⟨x, hx, hP, hx1, -⟩ :=
    exists_weights_of_symmetric Γ hd (fun _ => measureReal_nonneg) hq hlll
  exact (lintegral_resamplings_le μ vbl A hAm hA Γ hΓ hx hP hsel i).trans
    (le_of_eq (congrArg ENNReal.ofReal (hx1 hdpos i)))

/-- Expected total resamplings under symmetric lopsided Moser–Tardos (`1 ≤ d`). -/
theorem lintegral_sum_resamplings_le_symmetric [DecidableEq ι] [Fintype ι]
    (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {d : ℕ} (hdpos : 1 ≤ d) (hd : ∀ i, #(Γ i) ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) :
    ∫⁻ T, ∑ i, resamplings sel i T ∂table μ ≤ Fintype.card ι * ENNReal.ofReal (1 / (d : ℝ)) := by
  obtain ⟨x, hx, hP, hx1, -⟩ :=
    exists_weights_of_symmetric Γ hd (fun _ => measureReal_nonneg) hq hlll
  have h := lintegral_sum_resamplings_le μ vbl A hAm hA Γ hΓ hx hP hsel
  simpa only [hx1 hdpos, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

/-- Almost sure success under symmetric lopsided Moser–Tardos (`e * q * (d + 1) ≤ 1`) for every
`d : ℕ`. -/
theorem ae_exists_forall_notMem_run_symmetric [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {d : ℕ} (hd : ∀ i, #(Γ i) ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i)
    (hstop : ∀ T w, sel T w = none → ∀ i, current vbl T w ∉ A i) :
    ∀ᵐ T ∂table μ, ∃ n, ∀ i, current vbl T (run sel T n) ∉ A i := by
  obtain ⟨x, hx, hP, -, -⟩ :=
    exists_weights_of_symmetric Γ hd (fun _ => measureReal_nonneg) hq hlll
  exact ae_exists_forall_notMem_run μ vbl A hAm hA Γ hΓ hx hP hsel hstop

/-- **Symmetric constructive lopsided local lemma** (`e * q * (d + 1) ≤ 1`). -/
theorem exists_forall_notMem_symmetric [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → Lopsidependent vbl A i j → j ∈ Γ i)
    {d : ℕ} (hd : ∀ i, #(Γ i) ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1) :
    ∃ σ : ∀ v, α v, ∀ i, σ ∉ A i := by
  classical
  obtain ⟨x, hx, hP, -, -⟩ :=
    exists_weights_of_symmetric Γ hd (fun _ => measureReal_nonneg) hq hlll
  exact exists_forall_notMem μ vbl A hAm hA Γ hΓ hx hP

end Symmetric

end Theorem

end Lopsided

end Cslib.Probability.MoserTardos
