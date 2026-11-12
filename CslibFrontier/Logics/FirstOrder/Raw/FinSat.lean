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
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.Sublists
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Fixed-size evaluation and r.e. finite satisfiability

`Cslib.Logic.FO.RawFormula.SatOnFin n φ` states that a raw formula `φ` holds on `Fin (n + 1)` under
some relation interpretation and variable assignment. Because satisfaction depends only on the
ground atoms over `φ.atoms` and on the variables below `φ.varBound`, `SatOnFin` is decidable and
primitive recursive (`Cslib.Logic.FO.RawFormula.primrecRel_satOnFin`), computed by enumerating the
sublists of those ground atoms and evaluating `φ` by structural recursion over `Fin (n + 1)`.

A raw formula is finitely satisfiable iff `SatOnFin n φ` holds for some `n`
(`Cslib.Logic.FO.RawFormula.finSat_iff_exists_satOnFin`). Unbounded search over `n` therefore shows
that finite satisfiability is recursively enumerable (`Cslib.Logic.FO.RawFormula.rePred_finSat`,
the easy half of Trakhtenbrot's theorem, [Libkin2004], Chapter 9), while bounded search backs the
decision procedure for monadic languages.

## Main definitions

* `Cslib.Logic.FO.RawFormula.SatOnFin`: satisfiability on `Fin (n + 1)`.
* `Cslib.Logic.FO.RawFormula.checkSatOnFin`: Boolean decision procedure for `SatOnFin`.

## Main results

* `Cslib.Logic.FO.RawFormula.checkSatOnFin_eq_true_iff`: correctness of `checkSatOnFin`.
* `Cslib.Logic.FO.RawFormula.primrec₂_checkSatOnFin`,
  `Cslib.Logic.FO.RawFormula.primrecRel_satOnFin`: `checkSatOnFin` and `SatOnFin` are primitive
  recursive.
* `Cslib.Logic.FO.RawFormula.finSat_iff_exists_satOnFin`: `FinSat φ ↔ ∃ n, SatOnFin n φ`.
* `Cslib.Logic.FO.RawFormula.rePred_finSat`: `FinSat` is r.e.
* `Cslib.Logic.FO.RawFormula.rePred_not_finValid`: finite non-validity is r.e.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

namespace Cslib.Logic.FO

namespace RawFormula

/-- `φ` is **satisfiable on `Fin (n + 1)`**: it holds on `Fin (n + 1)` under some relation
interpretation and variable assignment. -/
@[expose]
def SatOnFin (n : ℕ) (φ : RawFormula) : Prop :=
  ∃ (I : ℕ → List (Fin (n + 1)) → Prop) (v : ℕ → Fin (n + 1)), φ.Realize I v

theorem satOnFin_iff {n : ℕ} {φ : RawFormula} :
    SatOnFin n φ ↔ ∃ (I : ℕ → List (Fin (n + 1)) → Prop) (v : ℕ → Fin (n + 1)), φ.Realize I v :=
  by rfl

/-- A raw formula is finitely satisfiable iff it is satisfiable on `Fin (n + 1)` for some `n`. -/
theorem finSat_iff_exists_satOnFin (φ : RawFormula) :
    φ.FinSat ↔ ∃ n, SatOnFin n φ := by
  constructor
  · rintro ⟨M, _, _, I, v, h⟩
    have hpos : 0 < Nat.card M := Nat.card_pos
    obtain ⟨n, hn⟩ : ∃ n, Nat.card M = n + 1 := ⟨Nat.card M - 1, by omega⟩
    let e : M ≃ Fin (n + 1) := (Finite.equivFin M).trans (finCongr hn)
    exact ⟨n, fun r as => I r (as.map e.symm), e ∘ v, (realize_equiv e I φ v).2 h⟩
  · rintro ⟨n, I, v, h⟩
    exact ⟨Fin (n + 1), inferInstance, inferInstance, I, v, h⟩

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
  rcases List.getD_mem_or a x 0 with h | h
  · exact ha _ h
  · omega

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
    have hset : ∀ i < n + 1, ∀ j ∈ a.set x i, j < n + 1 :=
      fun _ hi => List.forall_mem_set_of_forall_mem ha hi
    have hupd : ∀ i (hi : i < n + 1),
        assign n (a.set x i) = Function.update (assign n a) x ⟨i, hi⟩ := by
      intro i hi
      funext y
      apply Fin.ext
      rw [val_assign (hset i hi)]
      by_cases hyx : y = x
      · subst hyx; rw [Function.update_self, List.getD_set_self hx]
      · rw [Function.update_of_ne hyx, val_assign ha, List.getD_set_ne (Ne.symm hyx)]
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

/-- All ground atoms `(r, t)` on `range (n + 1)` whose `(r, |t|)` occurs in `φ.atoms`. -/
private def groundAtoms (n : ℕ) (φ : RawFormula) : List (ℕ × List ℕ) :=
  φ.atoms.flatMap fun rk => (tuples (n + 1) rk.2).map fun t => (rk.1, t)

private theorem mem_groundAtoms {n : ℕ} {φ : RawFormula} {r : ℕ} {t : List ℕ} :
    (r, t) ∈ groundAtoms n φ ↔ (r, t.length) ∈ φ.atoms ∧ ∀ i ∈ t, i < n + 1 := by
  simp only [groundAtoms, List.mem_flatMap, List.mem_map, mem_tuples, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨_, k⟩, hrk, s, ⟨hsl, hsb⟩, rfl, rfl⟩
    exact ⟨hsl ▸ hrk, hsb⟩
  · rintro ⟨hr, ht⟩
    exact ⟨(r, t.length), hr, t, ⟨rfl, ht⟩, rfl, rfl⟩

/-- Satisfying variable tuples of `φ` on `range (n + 1)`, collected over all sublists of
`groundAtoms n φ`. -/
private def satOnFinWitnesses (n : ℕ) (φ : RawFormula) : List (List ℕ) :=
  (groundAtoms n φ).sublists.flatMap fun T => satList n T φ.varBound φ

private theorem satOnFin_iff_ne_nil {n : ℕ} {φ : RawFormula} :
    SatOnFin n φ ↔ satOnFinWitnesses n φ ≠ [] := by
  rw [satOnFin_iff]
  constructor
  · rintro ⟨I, v, h⟩
    classical
    let T : List (ℕ × List ℕ) :=
      (groundAtoms n φ).filter fun rt => I rt.1 (rt.2.map (Fin.ofNat (n + 1)))
    let a : List ℕ := (List.range φ.varBound).map fun x => (v x : ℕ)
    have ha : ∀ i ∈ a, i < n + 1 := by
      intro i hi
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hi
      exact (v x).2
    have hsat : a ∈ satList n T φ.varBound φ := by
      refine (mem_satList φ le_rfl (by simp [a]) ha).2 ?_
      have hv : ∀ x < φ.varBound, assign n a x = v x := by
        intro x hx
        apply Fin.ext
        rw [val_assign ha, List.getD_map_range _ 0 hx]
      rw [realize_congr_var φ hv]
      refine (realize_congr_rel φ v fun r as hr => ?_).2 h
      have hofNat : (as.map Fin.val).map (Fin.ofNat (n + 1)) = as := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id as]
        refine List.map_congr_left fun i _ => ?_
        apply Fin.ext
        simp
      have hg : (r, as.map Fin.val) ∈ groundAtoms n φ := by
        refine mem_groundAtoms.2 ⟨by simpa using hr, fun i hi => ?_⟩
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
        exact j.2
      change (r, as.map Fin.val) ∈ T ↔ I r as
      simp [T, hg, hofNat]
    have hmem : a ∈ satOnFinWitnesses n φ :=
      List.mem_flatMap.2 ⟨T, List.mem_sublists.2 List.filter_sublist, hsat⟩
    rintro hnil
    rw [hnil] at hmem
    simp at hmem
  · intro hne
    obtain ⟨T, -, ha⟩ := List.mem_flatMap.1 (List.head_mem hne)
    have ht := mem_tuples.1 (satList_sub_tuples ha)
    exact ⟨interp n T, assign n ((satOnFinWitnesses n φ).head hne),
      (mem_satList φ le_rfl ht.1 ht.2).1 ha⟩

/-- Boolean decision procedure for `SatOnFin n φ`, enumerating interpretations over the ground
atoms of `φ` on `Fin (n + 1)`. -/
def checkSatOnFin (n : ℕ) (φ : RawFormula) : Bool :=
  !(satOnFinWitnesses n φ).isEmpty

theorem checkSatOnFin_eq_true_iff {n : ℕ} {φ : RawFormula} :
    checkSatOnFin n φ = true ↔ SatOnFin n φ := by
  rw [checkSatOnFin, Bool.not_eq_true', List.isEmpty_eq_false_iff, satOnFin_iff_ne_nil]

instance : DecidableRel SatOnFin :=
  fun n φ => decidable_of_iff (checkSatOnFin n φ = true) checkSatOnFin_eq_true_iff

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

private theorem primrec_groundAtoms : Primrec₂ groundAtoms :=
  list_flatMap (primrec_atoms.comp snd)
    (list_map (primrec_tuples.comp (succ.comp (fst.comp fst)) (snd.comp snd))
      (Primrec.pair (fst.comp (snd.comp fst)) snd).to₂).to₂

private theorem primrec_sublists {β : Type*} [Primcodable β] :
    Primrec (List.sublists : List β → List (List β)) :=
  (list_foldr Primrec.id (const [[]])
    (list_flatMap (snd.comp snd)
      (list_cons.comp snd (list_cons.comp (list_cons.comp (fst.comp (snd.comp fst)) snd)
        (const []))).to₂).to₂).of_eq fun l => by
    dsimp only [id]
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.sublists_cons, List.bind_eq_flatMap, List.foldr_cons, ih]

private theorem primrec_satOnFinWitnesses : Primrec₂ satOnFinWitnesses :=
  list_flatMap (primrec_sublists.comp primrec_groundAtoms)
    (primrec_satList.comp
      (Primrec.pair (fst.comp fst) (Primrec.pair snd (primrec_varBound.comp (snd.comp fst))))
      (snd.comp fst)).to₂

/-- `checkSatOnFin` is primitive recursive. -/
theorem primrec₂_checkSatOnFin : Primrec₂ checkSatOnFin :=
  (Primrec.not.comp (Primrec.eq.decide.comp primrec_satOnFinWitnesses (const []))).of_eq
    fun (n, φ) => by dsimp only [checkSatOnFin]; cases satOnFinWitnesses n φ <;> rfl

/-- **Fixed-size satisfiability on `Fin (n + 1)` is primitive recursive**: enumerate the sublists
of ground atoms occurring in `φ` and evaluate `φ` on all variable tuples below `varBound φ`. -/
theorem primrecRel_satOnFin : PrimrecRel SatOnFin :=
  (Primrec.eq.comp primrec₂_checkSatOnFin (const true)).of_eq fun _ => checkSatOnFin_eq_true_iff

end Primrec

/-- **Finite satisfiability is r.e.** ([Libkin2004], Chapter 9): search for a universe size `n + 1`
satisfying `SatOnFin n φ`. -/
theorem rePred_finSat : REPred FinSat :=
  (ComputablePred.rePred_exists (p := fun φ n => SatOnFin n φ)
    primrecRel_satOnFin.swap.computablePred).of_eq fun φ =>
    (finSat_iff_exists_satOnFin φ).symm

/-- Finite non-validity is r.e.: `φ` is not finitely valid iff `¬φ` is finitely satisfiable. -/
theorem rePred_not_finValid : REPred fun φ => ¬FinValid φ :=
  (rePred_finSat.comp (primrec_neg Primrec.id).to_comp).of_eq fun φ => by
    change FinSat (neg φ) ↔ _
    rw [finValid_iff_not_finSat_neg, not_not]

end RawFormula

end Cslib.Logic.FO
