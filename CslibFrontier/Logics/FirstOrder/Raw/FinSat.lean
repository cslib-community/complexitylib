/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Raw.Primrec
public import Mathlib.Computability.RE
import CslibFrontier.Foundations.Computability.ComputablePred
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Finite satisfiability is r.e.

A raw formula `φ` is finitely satisfiable iff it is satisfied on some `Fin (n + 1)`, under an
interpretation given by a finite list of true atoms and an assignment given by a list of values
for the variables below `φ.varBound`. Satisfaction of such a finite witness is primitive
recursive: the satisfying assignments are computed by structural recursion on `φ`, quantifiers
ranging over `Fin (n + 1)`. Searching all witnesses shows that finite satisfiability is
recursively enumerable (the easy half of Trakhtenbrot's theorem, [Libkin2004], Chapter 9).

## Main results

* `Cslib.Logic.FO.RawFormula.rePred_finSat`: `FinSat` is r.e.
* `Cslib.Logic.FO.RawFormula.rePred_not_finValid`: finite non-validity is r.e.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

namespace Cslib.Logic.FO

namespace RawFormula

/-! ### Evaluation on `Fin (n + 1)` -/

/-- All length-`k` lists of numbers below `n`. -/
private def tuples (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (tuples n k).flatMap fun t => (List.range n).map fun i => i :: t

private theorem mem_tuples {n : ℕ} :
    ∀ {k : ℕ} {t : List ℕ}, t ∈ tuples n k ↔ t.length = k ∧ ∀ i ∈ t, i < n
  | 0, t => by cases t <;> simp [tuples]
  | k + 1, [] => by simp [tuples]
  | k + 1, a :: t => by
    simp only [tuples, List.mem_flatMap, List.mem_map, List.mem_range, List.cons.injEq,
      List.length_cons, List.mem_cons, forall_eq_or_imp, Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨s, hs, i, hi, rfl, rfl⟩
      exact ⟨(mem_tuples.1 hs).1, hi, (mem_tuples.1 hs).2⟩
    · rintro ⟨hl, ha, ht⟩
      exact ⟨t, mem_tuples.2 ⟨hl, ht⟩, a, ha, rfl, rfl⟩

/-- Satisfying assignments among length-`V` tuples, on universe `range (n + 1)`, with relations
given by the list `T` of true atoms. -/
private def satList (n : ℕ) (T : List (ℕ × List ℕ)) (V : ℕ) : RawFormula → List (List ℕ)
  | falsum => []
  | equal x y => (tuples (n + 1) V).filter fun a => a.getD x 0 = a.getD y 0
  | rel r args => (tuples (n + 1) V).filter fun a => (r, args.map (a.getD · 0)) ∈ T
  | imp φ ψ => (tuples (n + 1) V).filter fun a =>
      a ∈ satList n T V φ → a ∈ satList n T V ψ
  | all x φ => (tuples (n + 1) V).filter fun a =>
      ∀ i < n + 1, a.set x i ∈ satList n T V φ

/-- The interpretation on `Fin (n + 1)` given by a list of true atoms. -/
private def interp (n : ℕ) (T : List (ℕ × List ℕ)) : ℕ → List (Fin (n + 1)) → Prop :=
  fun r as => (r, as.map Fin.val) ∈ T

/-- The assignment on `Fin (n + 1)` given by a tuple. -/
private def assign (n : ℕ) (a : List ℕ) : ℕ → Fin (n + 1) :=
  fun x => Fin.ofNat (n + 1) (a.getD x 0)

private theorem val_assign {n : ℕ} {a : List ℕ} (ha : ∀ i ∈ a, i < n + 1) (x : ℕ) :
    (assign n a x : ℕ) = a.getD x 0 := by
  simp only [assign, Fin.val_ofNat]
  apply Nat.mod_eq_of_lt
  rw [List.getD_eq_getElem?_getD]
  cases h : a[x]? with
  | none => simp
  | some i => exact ha i (List.mem_of_getElem? h)

private theorem mem_satList {n : ℕ} {T : List (ℕ × List ℕ)} {V : ℕ} :
    ∀ (φ : RawFormula), φ.varBound ≤ V → ∀ {a : List ℕ}, a.length = V → (∀ i ∈ a, i < n + 1) →
      (a ∈ satList n T V φ ↔ φ.Realize (interp n T) (assign n a))
  | falsum, _, a, _, _ => by simp [satList, Realize]
  | equal x y, _, a, hl, ha => by
    have hmem : a ∈ tuples (n + 1) V := mem_tuples.2 ⟨hl, ha⟩
    simp only [satList, List.mem_filter, hmem, true_and, decide_eq_true_eq, Realize]
    rw [← val_assign ha x, ← val_assign ha y, Fin.val_inj]
  | rel r args, _, a, hl, ha => by
    have hmem : a ∈ tuples (n + 1) V := mem_tuples.2 ⟨hl, ha⟩
    simp only [satList, List.mem_filter, hmem, true_and, decide_eq_true_eq, Realize, interp,
      List.map_map]
    rw [List.map_congr_left fun x _ => (val_assign ha x).symm]
    rfl
  | imp φ ψ, hV, a, hl, ha => by
    have hmem : a ∈ tuples (n + 1) V := mem_tuples.2 ⟨hl, ha⟩
    simp only [varBound, max_le_iff] at hV
    simp only [satList, List.mem_filter, hmem, true_and, decide_eq_true_eq, Realize]
    rw [mem_satList φ hV.1 hl ha, mem_satList ψ hV.2 hl ha]
  | all x φ, hV, a, hl, ha => by
    have hmem : a ∈ tuples (n + 1) V := mem_tuples.2 ⟨hl, ha⟩
    simp only [varBound, max_le_iff] at hV
    simp only [satList, List.mem_filter, hmem, true_and, decide_eq_true_eq, Realize]
    have hx : x < a.length := by omega
    have hset : ∀ i < n + 1, ∀ j ∈ a.set x i, j < n + 1 := by
      intro i hi j hj
      rcases List.mem_or_eq_of_mem_set hj with hj | rfl
      · exact ha j hj
      · exact hi
    have hupd : ∀ i (hi : i < n + 1),
        assign n (a.set x i) = Function.update (assign n a) x ⟨i, hi⟩ := by
      intro i hi
      funext y
      apply Fin.ext
      rw [val_assign (hset i hi)]
      by_cases hyx : y = x
      · subst hyx; simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hx]
      · rw [Function.update_of_ne hyx, val_assign ha, List.getD_eq_getElem?_getD,
          List.getElem?_set_ne (Ne.symm hyx), ← List.getD_eq_getElem?_getD]
    constructor
    · intro h m
      have hm := (mem_satList φ hV.2 (by simp [hl]) (hset m m.2)).1 (h m m.2)
      rwa [hupd m m.2] at hm
    · intro h i hi
      rw [mem_satList φ hV.2 (by simp [hl]) (hset i hi), hupd i hi]
      exact h ⟨i, hi⟩

private theorem satList_sub_tuples {n : ℕ} {T : List (ℕ × List ℕ)} {V : ℕ} {a : List ℕ} :
    ∀ {φ : RawFormula}, a ∈ satList n T V φ → a ∈ tuples (n + 1) V
  | falsum, h => by simp [satList] at h
  | equal _ _, h => (List.mem_filter.1 h).1
  | rel _ _, h => (List.mem_filter.1 h).1
  | imp _ _, h => (List.mem_filter.1 h).1
  | all _ _, h => (List.mem_filter.1 h).1

/-! ### Primitive recursiveness -/

section Primrec

open Primrec

private theorem primrec_tuples : Primrec₂ tuples := by
  have h := nat_rec (α := ℕ) (β := List (List ℕ)) (const [[]])
    (g := fun n p => p.2.flatMap fun t => (List.range n).map fun i => i :: t)
    (list_flatMap (snd.comp snd)
      (list_map (list_range.comp (fst.comp fst)) (list_cons.comp snd (snd.comp fst)).to₂).to₂).to₂
  refine h.of_eq fun n k => ?_
  induction k with
  | zero => rfl
  | succ k ih => simp only [tuples, ← ih]

private theorem primrec_mem_list {β : Type*} [Primcodable β] :
    PrimrecRel fun (b : β) (l : List β) => b ∈ l := by
  classical
  exact ((PrimrecRel.exists_mem_list (Primrec.eq (α := β))).swap).of_eq fun b l => by simp

private theorem primrec_satList :
    Primrec₂ fun (c : ℕ × List (ℕ × List ℕ) × ℕ) φ => satList c.1 c.2.1 c.2.2 φ := by
  have htup : Primrec fun c : ℕ × List (ℕ × List ℕ) × ℕ => tuples (c.1 + 1) c.2.2 :=
    primrec_tuples.comp (succ.comp fst) (snd.comp snd)
  have hT : Primrec fun c : ℕ × List (ℕ × List ℕ) × ℕ => c.2.1 := fst.comp snd
  refine primrec₂_of_rec _ (const [])
    (e := fun c p => (tuples (c.1 + 1) c.2.2).filter fun a => a.getD p.1 0 = a.getD p.2 0)
    ?_
    (r := fun c p => (tuples (c.1 + 1) c.2.2).filter fun a =>
      (p.1, p.2.map (a.getD · 0)) ∈ c.2.1) ?_
    (i := fun c p => (tuples (c.1 + 1) c.2.2).filter fun a => a ∈ p.2.1 → a ∈ p.2.2) ?_
    (l := fun c p => (tuples (c.1 + 1) c.2.2).filter fun a =>
      ∀ i < c.1 + 1, a.set p.1.1 i ∈ p.2) ?_
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  · have hR : PrimrecRel fun (a : List ℕ) (q : (ℕ × List (ℕ × List ℕ) × ℕ) × ℕ × ℕ) =>
        a.getD q.2.1 0 = a.getD q.2.2 0 :=
      Primrec.eq.comp ((list_getD 0).comp fst (fst.comp (snd.comp snd)))
        ((list_getD 0).comp fst (snd.comp (snd.comp snd)))
    exact (PrimrecRel.listFilter hR).comp (htup.comp fst) Primrec.id |>.to₂
  · have hR : PrimrecRel fun (a : List ℕ) (q : (ℕ × List (ℕ × List ℕ) × ℕ) × ℕ × List ℕ) =>
        (q.2.1, q.2.2.map (a.getD · 0)) ∈ q.1.2.1 :=
      primrec_mem_list.comp (Primrec.pair (fst.comp (snd.comp snd))
        (list_map (snd.comp (snd.comp snd)) ((list_getD 0).comp (fst.comp fst) snd).to₂))
        (hT.comp (fst.comp snd))
    exact (PrimrecRel.listFilter hR).comp (htup.comp fst) Primrec.id |>.to₂
  · have hR : PrimrecRel fun (a : List ℕ)
        (q : (ℕ × List (ℕ × List ℕ) × ℕ) × (RawFormula × RawFormula) × List (List ℕ) ×
          List (List ℕ)) => a ∈ q.2.2.1 → a ∈ q.2.2.2 :=
      (PrimrecPred.or (primrec_mem_list.comp fst (fst.comp (snd.comp (snd.comp snd)))).not
        (primrec_mem_list.comp fst (snd.comp (snd.comp (snd.comp snd))))).of_eq
        fun _ => by tauto
    exact (PrimrecRel.listFilter hR).comp (htup.comp fst) Primrec.id |>.to₂
  · have hR : PrimrecRel fun (a : List ℕ)
        (q : (ℕ × List (ℕ × List ℕ) × ℕ) × (ℕ × RawFormula) × List (List ℕ)) =>
          ∀ i < q.1.1 + 1, a.set q.2.1.1 i ∈ q.2.2 := by
      have h1 : PrimrecRel fun (i : ℕ)
          (p : List ℕ × (ℕ × List (ℕ × List ℕ) × ℕ) × (ℕ × RawFormula) × List (List ℕ)) =>
            p.1.set p.2.2.1.1 i ∈ p.2.2.2 :=
        primrec_mem_list.comp (list_set.comp (fst.comp snd)
          (Primrec.pair (fst.comp (fst.comp (snd.comp (snd.comp snd)))) fst))
          (snd.comp (snd.comp (snd.comp snd)))
      exact (PrimrecRel.comp (PrimrecRel.forall_mem_list h1)
        (list_range.comp (succ.comp (fst.comp (fst.comp snd)))) Primrec.id).of_eq
        fun _ => by simp only [List.mem_range, id, Nat.succ_eq_add_one]
    exact (PrimrecRel.listFilter hR).comp (htup.comp fst) Primrec.id |>.to₂

end Primrec

/-- A finite-model witness for `φ`: a universe size `n + 1`, a list `T` of true atoms and a
satisfying tuple of values for the variables. -/
private def IsWitness (φ : RawFormula) (w : ℕ × List (ℕ × List ℕ) × List ℕ) : Prop :=
  w.2.2 ∈ satList w.1 w.2.1 φ.varBound φ

open Primrec in
private theorem primrecRel_isWitness : PrimrecRel IsWitness :=
  primrec_mem_list.comp (snd.comp (snd.comp snd))
    (primrec_satList.comp (Primrec.pair (fst.comp snd)
      (Primrec.pair (fst.comp (snd.comp snd)) (primrec_varBound.comp fst))) fst)

private theorem finSat_iff_exists_isWitness (φ : RawFormula) :
    φ.FinSat ↔ ∃ w, IsWitness φ w := by
  constructor
  · rintro ⟨M, _, _, I, v, h⟩
    have hpos : 0 < Nat.card M := Nat.card_pos
    obtain ⟨n, hn⟩ : ∃ n, Nat.card M = n + 1 := ⟨Nat.card M - 1, by omega⟩
    let e : M ≃ Fin (n + 1) := (Finite.equivFin M).trans (finCongr hn)
    let I' : ℕ → List (Fin (n + 1)) → Prop := fun r as => I r (as.map e.symm)
    let v' : ℕ → Fin (n + 1) := e ∘ v
    have h' : φ.Realize I' v' := (realize_equiv e I φ v).2 h
    classical
    let T : List (ℕ × List ℕ) := φ.atoms.flatMap fun rk =>
      ((tuples (n + 1) rk.2).filter fun t => I' rk.1 (t.map (Fin.ofNat (n + 1)))).map
        fun t => (rk.1, t)
    let a : List ℕ := (List.range φ.varBound).map fun x => (v' x : ℕ)
    have ha : ∀ i ∈ a, i < n + 1 := by
      intro i hi
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hi
      exact (v' x).2
    refine ⟨(n, T, a), (mem_satList φ le_rfl (by simp [a]) ha).2 ?_⟩
    have hv : ∀ x < φ.varBound, assign n a x = v' x := by
      intro x hx
      apply Fin.ext
      rw [val_assign ha]
      simp [a, List.getD_eq_getElem?_getD, hx]
    rw [realize_congr_var φ hv]
    refine (realize_congr_rel φ v' fun r as hr => ?_).2 h'
    have hofNat : (as.map Fin.val).map (Fin.ofNat (n + 1)) = as := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id as]
      refine List.map_congr_left fun i _ => ?_
      apply Fin.ext
      simp
    change (r, as.map Fin.val) ∈ T ↔ I' r as
    simp only [T, List.mem_flatMap, List.mem_map, List.mem_filter, mem_tuples, Prod.mk.injEq]
    constructor
    · rintro ⟨rk, hrk, t, ⟨⟨htl, htb⟩, hI⟩, h1, h2⟩
      subst h1 h2
      simpa [hofNat] using hI
    · intro hI
      refine ⟨(r, as.length), hr, as.map Fin.val,
        ⟨⟨by simp, fun i hi => ?_⟩, ?_⟩, rfl, rfl⟩
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
        exact j.2
      simpa [hofNat] using hI
  · rintro ⟨⟨n, T, a⟩, h⟩
    have ht := mem_tuples.1 (satList_sub_tuples h)
    exact ⟨Fin (n + 1), inferInstance, inferInstance, interp n T, assign n a,
      (mem_satList φ le_rfl ht.1 ht.2).1 h⟩

/-- **Finite satisfiability is r.e.** ([Libkin2004], Chapter 9): search for a finite witness. -/
theorem rePred_finSat : REPred FinSat :=
  (ComputablePred.rePred_exists (p := IsWitness) primrecRel_isWitness.computablePred).of_eq
    fun φ => (finSat_iff_exists_isWitness φ).symm

/-- Finite non-validity is r.e.: `φ` is not finitely valid iff `¬φ` is finitely satisfiable. -/
theorem rePred_not_finValid : REPred fun φ => ¬FinValid φ :=
  (rePred_finSat.comp (primrec_neg Primrec.id).to_comp).of_eq fun φ => by
    change FinSat (neg φ) ↔ _
    rw [finValid_iff_not_finSat_neg, not_not]

end RawFormula

end Cslib.Logic.FO
