/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Foundations.Order.BooleanSubalgebra
import Complexity.Computability.Complexity.Reduction.ManyOne
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Union and intersection closure at each level of the polynomial hierarchy

Pair the two certificates at each quantifier block and split them before running the two
verifiers. This preserves the number and polarity of the quantifiers, including at level zero.
The construction uses exact certificate lengths and polynomial-time bit-string slicing.

## Main definitions

* `splitAlternatingBlocks`: split each paired block into its left and right certificates.

## Main results

* `alternation_splitAlternatingBlocks`: alternating-quantifier equivalence for paired blocks.
* `computableInPolyTime_splitAlternatingBlocks`: plain polynomial-time certificate for splitting
  paired blocks whose lengths are polynomials of a computed unary size.
* `inter_mem_SigmaP`, `union_mem_SigmaP`: closure of each existential level.
* `inter_mem_PiP`, `union_mem_PiP`: closure of each universal level.
* `compl_mem_PH`, `inter_mem_PH`, `union_mem_PH`, `diff_mem_PH`: Boolean closure of the hierarchy.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [L. Stockmeyer, *The polynomial-time hierarchy*][Stockmeyer1976]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Split consecutive blocks of lengths `n + m` into two words, concatenating their first `n`
and last `m` bits respectively. Bits beyond the specified blocks are ignored. -/
def splitAlternatingBlocks : List (ℕ × ℕ) → List Bool → List Bool × List Bool
  | [], _ => ([], [])
  | (n, m) :: ns, w =>
    let tail := splitAlternatingBlocks ns (w.drop (n + m))
    (w.take n ++ tail.1, (w.drop n).take m ++ tail.2)

private theorem splitAlternatingBlocks_append {n m : ℕ} (ns : List (ℕ × ℕ))
    {u v : List Bool} (hu : u.length = n) (hv : v.length = m) (w : List Bool) :
    splitAlternatingBlocks ((n, m) :: ns) (u ++ v ++ w) =
      (u ++ (splitAlternatingBlocks ns w).1, v ++ (splitAlternatingBlocks ns w).2) := by
  simp [splitAlternatingBlocks, ← hu, ← hv, List.append_assoc]

/-- Independent alternating predicates can be conjoined by pairing their certificate blocks.
Each quantified domain is nonempty, including blocks of length zero. -/
theorem alternation_splitAlternatingBlocks (ns : List (ℕ × ℕ)) (q : Bool)
    (P Q : List Bool → Prop) :
    Alternation q (ns.map fun nm => nm.1 + nm.2)
      (fun w => P (splitAlternatingBlocks ns w).1 ∧ Q (splitAlternatingBlocks ns w).2) ↔
      Alternation q (ns.map Prod.fst) P ∧ Alternation q (ns.map Prod.snd) Q := by
  induction ns generalizing q P Q with
  | nil => simp [splitAlternatingBlocks]
  | cons nm ns ih =>
    rcases nm with ⟨n, m⟩
    have key (u v : List Bool) (hu : u.length = n) (hv : v.length = m) (r : Bool) :
        Alternation r (ns.map fun nm => nm.1 + nm.2)
          (fun w => P (splitAlternatingBlocks ((n, m) :: ns) ((u ++ v) ++ w)).1 ∧
            Q (splitAlternatingBlocks ((n, m) :: ns) ((u ++ v) ++ w)).2) ↔
          Alternation r (ns.map Prod.fst) (fun w => P (u ++ w)) ∧
          Alternation r (ns.map Prod.snd) (fun w => Q (v ++ w)) := by
      simp only [splitAlternatingBlocks_append ns hu hv]
      exact ih r (fun w => P (u ++ w)) (fun w => Q (v ++ w))
    simp only [List.map_cons]
    cases q
    · simp only [alternation_false_cons]
      constructor
      · intro h
        constructor
        · intro u hu
          exact ((key u (List.replicate m false) hu (by simp) true).1
            (h (u ++ List.replicate m false) (by simp [hu]))).1
        · intro v hv
          exact ((key (List.replicate n false) v (by simp) hv true).1
            (h (List.replicate n false ++ v) (by simp [hv]))).2
      · rintro ⟨hP, hQ⟩ w hw
        have hu : (w.take n).length = n := by simp [hw]
        have hv : (w.drop n).length = m := by simp [hw]
        simpa only [List.take_append_drop] using
          (key (w.take n) (w.drop n) hu hv true).2 ⟨hP _ hu, hQ _ hv⟩
    · simp only [alternation_true_cons]
      constructor
      · rintro ⟨w, hw, h⟩
        have hu : (w.take n).length = n := by simp [hw]
        have hv : (w.drop n).length = m := by simp [hw]
        have hh := (key (w.take n) (w.drop n) hu hv false).1
          (by simpa only [List.take_append_drop] using h)
        exact ⟨⟨_, hu, hh.1⟩, ⟨_, hv, hh.2⟩⟩
      · rintro ⟨⟨u, hu, hP⟩, ⟨v, hv, hQ⟩⟩
        exact ⟨u ++ v, by simp [hu, hv], (key u v hu hv false).2 ⟨hP, hQ⟩⟩

/-- Splitting paired blocks is polynomial-time when their lengths are fixed polynomials of a
computed unary size. -/
theorem computableInPolyTime_splitAlternatingBlocks {γ : Type}
    {encIn : γ ↪ List Bool} (ps : List (Polynomial ℕ × Polynomial ℕ)) {N : γ → ℕ}
    (hN : ComputableInPolyTime N encIn encUnary) {W : γ → List Bool}
    (hW : ComputableInPolyTime W encIn encBits) :
    ComputableInPolyTime
      (fun x => splitAlternatingBlocks (ps.map fun pq => (pq.1.eval (N x), pq.2.eval (N x)))
        (W x)) encIn (encPair encBits encBits) := by
  induction ps generalizing W with
  | nil => exact .const ([], [])
  | cons pq ps ih =>
    have hp := (ComputableInPolyTime.unary_eval pq.1).comp hN
    have hq := (ComputableInPolyTime.unary_eval pq.2).comp hN
    have ht := ih (hW.bitsDropWithInput (ComputableInPolyTime.unary_add.comp
      (hp.prod hq)))
    exact ((hW.bitsTakeWithInput hp).bitsAppend ht.fst').prod
      (((hW.bitsDropWithInput hp).bitsTakeWithInput hq).bitsAppend ht.snd')

variable {α : Type} {enc : α ↪ List Bool}

/-- Conjoin two alternating verifiers by pairing equally positioned certificate blocks. -/
theorem IsAlternatingVerifier.inter {q : Bool}
    {ps : List (Polynomial ℕ × Polynomial ℕ)} {V W : α × List Bool → Bool} {A B : Set α}
    (hA : IsAlternatingVerifier enc q (ps.map Prod.fst) V A)
    (hB : IsAlternatingVerifier enc q (ps.map Prod.snd) W B) :
    IsAlternatingVerifier enc q (ps.map fun pq => pq.1 + pq.2)
      (fun x =>
        let w := splitAlternatingBlocks
          (ps.map fun pq => (pq.1.eval (enc x.1).length, pq.2.eval (enc x.1).length)) x.2
        V (x.1, w.1) && W (x.1, w.2)) (A ∩ B) := by
  intro a
  rw [Set.mem_inter_iff, hA a, hB a]
  simp only [List.map_map, Function.comp_def, Polynomial.eval_add, Bool.and_eq_true]
  simpa only [List.map_map, Function.comp_def] using (alternation_splitAlternatingBlocks
    (ps.map fun pq => (pq.1.eval (enc a).length, pq.2.eval (enc a).length)) q
    (fun w => V (a, w) = true) (fun w => W (a, w) = true)).symm

private theorem exists_inter_verifier {q : Bool} {k : ℕ} {A B : Set α}
    (hA : ∃ ps V, ps.length = k ∧
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      IsAlternatingVerifier enc q ps V A)
    (hB : ∃ ps V, ps.length = k ∧
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      IsAlternatingVerifier enc q ps V B) :
    ∃ ps V, ps.length = k ∧
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      IsAlternatingVerifier enc q ps V (A ∩ B) := by
  obtain ⟨ps, V, hp, hV, hA⟩ := hA
  obtain ⟨qs, W, hq, hW, hB⟩ := hB
  have hlen : ps.length = qs.length := hp.trans hq.symm
  have hA' : IsAlternatingVerifier enc q ((ps.zip qs).map Prod.fst) V A := by
    simpa only [List.map_fst_zip hlen.le] using hA
  have hB' : IsAlternatingVerifier enc q ((ps.zip qs).map Prod.snd) W B := by
    simpa only [List.map_snd_zip hlen.ge] using hB
  refine ⟨_, _, ?_, ?_, hA'.inter hB'⟩
  · simp [hp, hq]
  · have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
        (encPair enc encBits) encUnary := by fun_prop
    have hs := computableInPolyTime_splitAlternatingBlocks (ps.zip qs) hn (.snd enc encBits)
    exact ComputableInPolyTime.bool_and.comp
      ((hV.comp ((ComputableInPolyTime.fst enc encBits).prod hs.fst')).prod
        (hW.comp ((ComputableInPolyTime.fst enc encBits).prod hs.snd')))

variable {k : ℕ} {A B : Set α}

/-- Each existential level is closed under intersection, without adding a quantifier block. -/
theorem inter_mem_SigmaP (hA : A ∈ SigmaP k enc) (hB : B ∈ SigmaP k enc) :
    A ∩ B ∈ SigmaP k enc := exists_inter_verifier hA hB

/-- Each universal level is closed under intersection, without adding a quantifier block. -/
theorem inter_mem_PiP (hA : A ∈ PiP k enc) (hB : B ∈ PiP k enc) :
    A ∩ B ∈ PiP k enc := exists_inter_verifier hA hB

/-- Each existential level is closed under union, by intersection and quantifier duality. -/
theorem union_mem_SigmaP (hA : A ∈ SigmaP k enc) (hB : B ∈ SigmaP k enc) :
    A ∪ B ∈ SigmaP k enc :=
  SigmaP_eq_preimage_compl_PiP ▸ compl_union_mem inter_mem_PiP
    (compl_mem_PiP_of_mem_SigmaP hA) (compl_mem_PiP_of_mem_SigmaP hB)

/-- Each universal level is closed under union, by intersection and quantifier duality. -/
theorem union_mem_PiP (hA : A ∈ PiP k enc) (hB : B ∈ PiP k enc) :
    A ∪ B ∈ PiP k enc :=
  PiP_eq_preimage_compl_SigmaP ▸ compl_union_mem inter_mem_SigmaP
    (compl_mem_SigmaP_of_mem_PiP hA) (compl_mem_SigmaP_of_mem_PiP hB)

/-- Complementation swaps quantifier polarities, remaining within the polynomial hierarchy. -/
theorem compl_mem_PH (hA : A ∈ PH enc) : Aᶜ ∈ PH enc := by
  obtain ⟨k, hk⟩ := mem_PH.mp hA
  exact PiP_subset_PH k (compl_mem_PiP_of_mem_SigmaP hk)

/-- Two PH languages can be intersected at the larger of their two existential levels. -/
theorem inter_mem_PH (hA : A ∈ PH enc) (hB : B ∈ PH enc) : A ∩ B ∈ PH enc := by
  obtain ⟨k, hk⟩ := mem_PH.mp hA
  obtain ⟨l, hl⟩ := mem_PH.mp hB
  exact SigmaP_subset_PH (max k l)
    (inter_mem_SigmaP (SigmaP_mono (le_max_left k l) hk) (SigmaP_mono (le_max_right k l) hl))

open scoped symmDiff

/-- `PH` as a Boolean subalgebra of `Set α`. -/
def PH.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (PH enc) (P_subset_PH empty_mem_P) (fun _ => compl_mem_PH)
    (fun _ _ => inter_mem_PH)

@[simp]
theorem PH.coe_booleanSubalgebra : (PH.booleanSubalgebra enc : Set (Set α)) = PH enc := rfl

@[simp]
theorem PH.mem_booleanSubalgebra : A ∈ PH.booleanSubalgebra enc ↔ A ∈ PH enc := Iff.rfl

/-- Two PH languages can be united at the larger of their two existential levels. -/
theorem union_mem_PH (hA : A ∈ PH enc) (hB : B ∈ PH enc) : A ∪ B ∈ PH enc :=
  (PH.booleanSubalgebra enc).sup_mem hA hB

/-- The polynomial hierarchy is closed under set difference. -/
theorem diff_mem_PH (hA : A ∈ PH enc) (hB : B ∈ PH enc) : A \ B ∈ PH enc :=
  (PH.booleanSubalgebra enc).sdiff_mem hA hB

/-- The polynomial hierarchy is closed under symmetric difference. -/
theorem symmDiff_mem_PH (hA : A ∈ PH enc) (hB : B ∈ PH enc) : A ∆ B ∈ PH enc :=
  (PH.booleanSubalgebra enc).symmDiff_mem hA hB

end Cslib.Complexity
