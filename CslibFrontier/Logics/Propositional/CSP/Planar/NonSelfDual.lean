/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.RelationMinor
import CslibFrontier.Logics.Propositional.CSP.Affine
import CslibFrontier.Foundations.Data.BitString.Hamming
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ordered minors for nonselfdual Boolean languages

The arbitrary-arity parity and majority minor arguments are an original reconstruction of the
expressibility argument omitted after Lemma 4 of
[DvorakKupec2015], printed pp. 438–439. They are not attributed to a printed proof of that lemma.
All relations use the existing `CSP.booleanRelation`/`IsPolymorphism` interface. Traces preserve
survivor order. These are finite semantic constructions; geometric realization, native reduction,
runtime and planar hardness are separate obligations.

## Main results

* `Cslib.Logic.PL.CSP.RelationMinor.exists_majority_minor`: a normalized ternary majority failure.
* `Cslib.Logic.PL.CSP.RelationMinor.exists_binary_parity_minor`: a binary parity failure.
* `Cslib.Logic.PL.CSP.RelationMinor.exists_nand_trace`: an actual ordered trace to NAND.
-/

public section

namespace Cslib.Logic.PL.CSP.RelationMinor

open Cslib.BitString

variable {m n : ℕ}

/-- Choose an arity-minimal failing relation among actual finite traces. No bound on the
starting arity or truth-table enumeration is used. -/
private theorem exists_minimal_failure {R : Set (Fin m → Bool)} {k : ℕ}
    {f : (Fin k → Bool) → Bool} (h : ¬IsPolymorphism f R) :
    ∃ (n : ℕ) (S : Set (Fin n → Bool)), Nonempty (Trace R S) ∧ ¬IsPolymorphism f S ∧
      ∀ (l : ℕ) (T : Set (Fin l → Bool)), Nonempty (Trace S T) → l < n → IsPolymorphism f T := by
  classical
  let P (n : ℕ) := ∃ S : Set (Fin n → Bool), Nonempty (Trace R S) ∧ ¬IsPolymorphism f S
  have hex : ∃ n, P n := ⟨m, R, ⟨.refl⟩, h⟩
  obtain ⟨S, ⟨trace⟩, hS⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, S, ⟨trace⟩, hS, ?_⟩
  intro l T ⟨tail⟩ hlt
  by_contra hT
  exact (Nat.find_min hex hlt) ⟨T, ⟨trace.trans tail⟩, hT⟩

/-- Translation commutation lets a minimum failure be normalized to a missing zero tuple.
Every smaller minor, including every projection and cofactor, preserves the operation. -/
private theorem exists_normalized_minimal_failure {R : Set (Fin m → Bool)} {k : ℕ}
    {f : (Fin k → Bool) → Bool}
    (htranslate : ∀ (a : Fin k → Bool) b,
      f (fun j => a j + b) = f a + b)
    (h : ¬IsPolymorphism f R) :
    ∃ (n : ℕ) (S : Set (Fin n → Bool)), Nonempty (Trace R S) ∧
      (0 : Fin n → Bool) ∉ S ∧ ¬IsPolymorphism f S ∧
      (∃ a : Fin k → Fin n → Bool, (∀ j, a j ∈ S) ∧
        (fun i => f (fun j => a j i)) = 0) ∧
      ∀ (l : ℕ) (T : Set (Fin l → Bool)), Nonempty (Trace S T) → l < n → IsPolymorphism f T := by
  classical
  obtain ⟨n, S, ⟨trace⟩, hS, hmin⟩ := exists_minimal_failure h
  simp only [IsPolymorphism, not_forall] at hS
  obtain ⟨a, ha, hout⟩ := hS
  let t : Fin n → Bool := fun i => f (fun j => a j i)
  let T := twist S t
  have hin (j : Fin k) : a j + t ∈ T := by
    change (a j + t) + t ∈ S
    have ht : t + t = 0 := by ext i; exact BooleanRing.add_self _
    simpa only [add_assoc, ht, add_zero] using ha j
  have hz : (0 : Fin n → Bool) ∉ T := by
    simpa [T, twist, t] using hout
  have ho : (fun i => f (fun j => (a j + t) i)) = (0 : Fin n → Bool) := by
    ext i
    change f (fun j => a j i + t i) = (0 : Bool)
    rw [htranslate]
    exact BooleanRing.add_self _
  have hb : ¬IsPolymorphism f T := fun hT => hz (ho ▸ hT (fun j => a j + t) hin)
  refine ⟨n, T, ⟨trace.translate t⟩, hz, hb, ⟨_, hin, ho⟩, ?_⟩
  intro l U ⟨tail⟩ hl
  exact hmin l U ⟨(Trace.refl.translate t).trans tail⟩ hl

private theorem parity_translate (a : Fin 3 → Bool) (b : Bool) :
    Cslib.parity 3 (fun j => a j + b) = Cslib.parity 3 a + b := by
  have heq : a = ![a 0, a 1, a 2] := by ext j; fin_cases j <;> rfl
  rw [heq]
  generalize a 0 = x, a 1 = y, a 2 = z
  cases x <;> cases y <;> cases z <;> cases b <;> decide

private theorem majority_translate (a : Fin 3 → Bool) (b : Bool) :
    Cslib.majority 3 (fun j => a j + b) = Cslib.majority 3 a + b := by
  have heq : a = ![a 0, a 1, a 2] := by ext j; fin_cases j <;> rfl
  rw [heq]
  generalize a 0 = x, a 1 = y, a 2 = z
  cases x <;> cases y <;> cases z <;> cases b <;> decide

/-- Every relation of arity at most one is preserved by ternary parity, including empty
and nullary relations. -/
theorem parity_preserves_of_arity_le_one {R : Set (Fin n → Bool)} (hn : n ≤ 1) :
    IsPolymorphism (Cslib.parity 3) R := by
  have choose (a : Fin 3 → Fin n → Bool) :
      ∃ j, (fun i => Cslib.parity 3 (fun k => a k i)) = a j := by
    interval_cases n
    · exact ⟨0, Subsingleton.elim _ _⟩
    · revert a
      decide
  intro a ha
  obtain ⟨j, hj⟩ := choose a
  rw [hj]
  exact ha j

/-- Every relation of arity at most two is majority-preserved, including empty and nullary
relations. The finite check concerns the operation's two-coordinate selector law only. -/
theorem majority_preserves_of_arity_le_two {R : Set (Fin n → Bool)} (hn : n ≤ 2) :
    IsPolymorphism (Cslib.majority 3) R := by
  have choose (a : Fin 3 → Fin n → Bool) :
      ∃ j, (fun i => Cslib.majority 3 (fun k => a k i)) = a j := by
    interval_cases n
    · exact ⟨0, Subsingleton.elim _ _⟩
    · revert a
      decide
    · revert a
      decide
  intro a ha
  obtain ⟨j, hj⟩ := choose a
  rw [hj]
  exact ha j

/-- If a projected zero output is forced by closure, its unique feasible lift is the unit
at the deleted port. This works for any operation fixing the constant zero input. -/
theorem units_of_projection_closure {R : Set (Fin (n + 1) → Bool)} {k : ℕ}
    {f : (Fin k → Bool) → Bool} (hz : (0 : Fin (n + 1) → Bool) ∉ R)
    (a : Fin k → Fin (n + 1) → Bool) (ha : ∀ j, a j ∈ R)
    (hout : (fun i => f (fun j => a j i)) = 0)
    (hp : ∀ j, IsPolymorphism f (project R j)) :
    ∀ j, Pi.single j true ∈ R := by
  intro j
  apply single_mem_of_zero_mem_project hz j
  have h := hp j (fun k => j.removeNth (a k)) (fun k => remove_mem_project (ha k) j)
  have he : (fun i => f (fun k => j.removeNth (a k) i)) = (0 : Fin n → Bool) :=
    congrArg j.removeNth hout
  exact he ▸ h

/-- Cofactor closure applied to tuples sharing the pinned bit, lifted back to the original
relation. The operation must fix that constant bit. -/
theorem mem_of_cofactor_closure {R : Set (Fin (n + 1) → Bool)} {k : ℕ}
    {f : (Fin k → Bool) → Bool} {j : Fin (n + 1)} {b : Bool}
    (hf : f (fun _ => b) = b) (h : IsPolymorphism f (cofactor R j b))
    (a : Fin k → Fin (n + 1) → Bool) (ha : ∀ i, a i ∈ R)
    (hb : ∀ i, a i j = b) : (fun i => f (fun k => a k i)) ∈ R := by
  have hm (i : Fin k) : j.removeNth (a i) ∈ cofactor R j b := by
    rw [← hb i]
    exact remove_mem_cofactor (ha i) j
  have hout := h (fun i => j.removeNth (a i)) hm
  change j.insertNth b _ ∈ R at hout
  convert hout using 1
  apply (Fin.eq_insertNth_iff).mpr
  constructor
  · simpa only [hb] using hf
  · rfl

private theorem majority_const (b : Bool) : Cslib.majority 3 (fun _ => b) = b := by
  cases b <;> decide

private theorem parity_const (b : Bool) : Cslib.parity 3 (fun _ => b) = b := by
  cases b <;> decide

private theorem median_units {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    median (Pi.single i true) (Pi.single j true) (Pi.single k true) = 0 := by
  ext l
  by_cases hi : l = i
  · subst l
    simp [median, hij, hik]
  · by_cases hj : l = j
    · subst l
      simp [median, hi, hjk]
    · simp [median, hi, hj, Bool.zero_eq_false]

/-- A majority failure has an actual ordered ternary minor containing the three units and
missing zero. This original reconstruction works at every starting arity; it assumes neither
pins as language symbols nor a minor oracle. Interpreting cofactors as gadgets still needs pins. -/
theorem exists_majority_minor {R : Set (Fin m → Bool)}
    (h : ¬IsPolymorphism (Cslib.majority 3) R) :
    ∃ S : Set (Fin 3 → Bool), Nonempty (Trace R S) ∧
      (0 : Fin 3 → Bool) ∉ S ∧ (∀ i, Pi.single i true ∈ S) := by
  obtain ⟨n, S, trace, hz, hb, ⟨a, ha, hout⟩, hmin⟩ :=
    exists_normalized_minimal_failure majority_translate h
  have hn : 3 ≤ n := by
    by_contra hh
    exact hb (majority_preserves_of_arity_le_two (by omega))
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hp (j : Fin (n + 1)) : IsPolymorphism (Cslib.majority 3) (project S j) :=
    hmin n _ ⟨.project .refl j⟩ (by omega)
  have hu := units_of_projection_closure hz a ha hout hp
  have hn3 : n + 1 = 3 := by
    by_contra hh
    have hn4 : 4 ≤ n + 1 := by omega
    let i : Fin (n + 1) := ⟨0, by omega⟩
    let j : Fin (n + 1) := ⟨1, by omega⟩
    let k : Fin (n + 1) := ⟨2, by omega⟩
    let l : Fin (n + 1) := ⟨3, by omega⟩
    have hc := hmin n (cofactor S l false) ⟨.cofactor .refl l false⟩ (by omega)
    have hm := mem_of_cofactor_closure (majority_const false) hc
      ![Pi.single i true, Pi.single j true, Pi.single k true]
      (by intro q; fin_cases q <;> exact hu _)
      (by intro q; fin_cases q <;> simp [i, j, k, l, Bool.zero_eq_false])
    have he := median_units (n := n + 1) (i := i) (j := j) (k := k)
      (by simp [i, j]) (by simp [i, k]) (by simp [j, k])
    have he' : (fun p => Cslib.majority 3
        (fun q => (![Pi.single i true, Pi.single j true, Pi.single k true] :
          Fin 3 → Fin (n + 1) → Bool) q p)) = 0 := by
      rw [← he]
      ext p
      exact (median_apply_eq_majority _ _ _ _).symm
    exact hz (he' ▸ hm)
  have hn2 : n = 2 := by omega
  subst n
  exact ⟨S, trace, hz, hu⟩

private theorem parity_eq_true_of_units {R : Set (Fin n → Bool)}
    (hp : IsPolymorphism (Cslib.parity 3) R) (hz : (0 : Fin n → Bool) ∉ R)
    (hu : ∀ i, Pi.single i true ∈ R) {x : Fin n → Bool} (hx : x ∈ R) :
    Cslib.parityOn Finset.univ x = true := by
  classical
  obtain ⟨⟨vs, b⟩, he, he0⟩ := exists_separating_affineEquation hp hz
  have hb : b = true := by
    cases b
    · apply False.elim
      apply he0
      change (vs.map (fun _ => (0 : Bool))).sum = 0
      simp
    · rfl
  let f : (Fin n → Bool) → Bool := fun a => (vs.map a).sum
  have hadd (a b : Fin n → Bool) : f (a + b) = (f a ^^ f b) := by
    change (vs.map (fun i => a i + b i)).sum = _
    rw [List.sum_map_add, Bool.add_eq_xor]
  obtain ⟨s, hs⟩ := BitString.exists_eq_parityOn_iff.mpr hadd
  have hsall : s = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    have hi := he _ (hu i)
    change f (Pi.single i true) = b at hi
    rw [hs, hb, Cslib.parityOn_eq_sum] at hi
    by_contra hnot
    have hzsum : (∑ j ∈ s, (Pi.single i true : Fin n → Bool) j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j ≠ i := by intro heq; exact hnot (heq ▸ hj)
      exact Pi.single_eq_of_ne (M := fun _ : Fin n => Bool) hji true
    rw [hzsum] at hi
    exact Bool.false_ne_true hi
  have h := he x hx
  change f x = b at h
  rwa [hs, hsall, hb] at h

private theorem insert_false_single (j : Fin (n + 1)) (i : Fin n) :
    j.insertNth false (Pi.single i true) =
      (Pi.single (j.succAbove i) true : Fin (n + 1) → Bool) := by
  apply (Fin.insertNth_eq_iff).mpr
  constructor
  · simp [Ne.symm (Fin.succAbove_ne j i), Bool.zero_eq_false]
  · ext k
    simp [Fin.removeNth, Pi.single_apply, Fin.succAbove_inj]

private theorem proper_even_impossible {R : Set (Fin (n + 1) → Bool)}
    (hz : (0 : Fin (n + 1) → Bool) ∉ R) (hu : ∀ i, Pi.single i true ∈ R)
    (hc : ∀ j, IsPolymorphism (Cslib.parity 3) (cofactor R j false))
    {v : Fin (n + 1) → Bool} (hv : v ∈ R)
    (heven : Cslib.parityOn Finset.univ v = false) (j : Fin (n + 1)) : v j = true := by
  by_contra hh
  have hj : v j = false := by cases h : v j <;> simp_all
  have hz' : (0 : Fin n → Bool) ∉ cofactor R j false := by
    intro h
    apply hz
    change j.insertNth false (0 : Fin n → Bool) ∈ R at h
    have heq : (j.insertNth false (0 : Fin n → Bool) : Fin (n + 1) → Bool) = 0 := by
      ext i
      rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩ <;>
        simp [Bool.zero_eq_false]
    exact heq ▸ h
  have hu' (i : Fin n) : Pi.single i true ∈ cofactor R j false := by
    change j.insertNth false _ ∈ R
    rw [insert_false_single]
    exact hu _
  have hv' : j.removeNth v ∈ cofactor R j false := by
    rw [← hj]
    exact remove_mem_cofactor hv j
  have hodd := parity_eq_true_of_units (hc j) hz' hu' hv'
  have hsum : Cslib.parityOn Finset.univ v =
      Cslib.parityOn Finset.univ (j.removeNth v) := by
    simp only [Cslib.parityOn_eq_sum]
    rw [Fin.sum_univ_succAbove _ j, hj]
    simp only [← Bool.zero_eq_false, zero_add]
    rfl
  rw [hsum, hodd] at heven
  contradiction

/-- Every parity-failing Boolean relation has a binary parity-failing ordered minor. This
arbitrary-arity reconstruction uses actual projection/cofactor/twist traces. Affine separation
is used only to prove the even-tuple cancellation step, not as a gadget or minor oracle. -/
theorem exists_binary_parity_minor {R : Set (Fin m → Bool)}
    (h : ¬IsPolymorphism (Cslib.parity 3) R) :
    ∃ S : Set (Fin 2 → Bool), Nonempty (Trace R S) ∧ ¬IsPolymorphism (Cslib.parity 3) S ∧
      (0 : Fin 2 → Bool) ∉ S ∧ (∀ i, Pi.single i true ∈ S) := by
  obtain ⟨n, S, trace, hz, hb, ⟨a, ha, hout⟩, hmin⟩ :=
    exists_normalized_minimal_failure parity_translate h
  have hn : 2 ≤ n := by
    by_contra hh
    exact hb (parity_preserves_of_arity_le_one (by omega))
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hp (j : Fin (n + 1)) : IsPolymorphism (Cslib.parity 3) (project S j) :=
    hmin n _ ⟨.project .refl j⟩ (by omega)
  have hc (j : Fin (n + 1)) (b : Bool) :
      IsPolymorphism (Cslib.parity 3) (cofactor S j b) :=
    hmin n _ ⟨.cofactor .refl j b⟩ (by omega)
  have hu := units_of_projection_closure hz a ha hout hp
  have heven_full {v : Fin (n + 1) → Bool} (hv : v ∈ S)
      (he : Cslib.parityOn Finset.univ v = false) : v = fun _ => true := by
    ext j
    exact proper_even_impossible hz hu (fun j => hc j false) hv he j
  have hex : ∃ k : Fin 3, Cslib.parityOn Finset.univ (a k) = false := by
    by_contra hh
    have hall (k : Fin 3) : Cslib.parityOn Finset.univ (a k) = true := by
      have : Cslib.parityOn Finset.univ (a k) ≠ false := fun h => hh ⟨k, h⟩
      cases h : Cslib.parityOn Finset.univ (a k) <;> simp_all
    have heq : a 0 + a 1 + a 2 = (0 : Fin (n + 1) → Bool) := by
      convert hout using 1
      ext i
      simp [Cslib.parity, Cslib.parityOn_eq_sum, Fin.sum_univ_succ, add_assoc]
    have he := congrArg (Cslib.parityOn Finset.univ) heq
    rw [Cslib.parityOn_add, Cslib.parityOn_add, hall, hall, hall] at he
    have hzpar : Cslib.parityOn Finset.univ (0 : Fin (n + 1) → Bool) = false := by
      rw [Cslib.parityOn_eq_sum]
      change (∑ _ : Fin (n + 1), (0 : Bool)) = 0
      simp
    rw [hzpar] at he
    exact (by decide : (true : Bool) ≠ false) he
  obtain ⟨q, hq⟩ := hex
  have hfull : (fun _ : Fin (n + 1) => true) ∈ S := heven_full (ha q) hq ▸ ha q
  have hefull : Cslib.parityOn Finset.univ (fun _ : Fin (n + 1) => true) = false := by
    rwa [heven_full (ha q) hq] at hq
  have hn2 : n + 1 = 2 := by
    by_contra hh
    have hn3 : 3 ≤ n + 1 := by omega
    have hne3 : n + 1 ≠ 3 := by
      intro hn3
      have hn' : n = 2 := by omega
      subst n
      revert hefull
      decide
    have hn4 : 4 ≤ n + 1 := by omega
    let i : Fin (n + 1) := ⟨0, by omega⟩
    let j : Fin (n + 1) := ⟨1, by omega⟩
    let k : Fin (n + 1) := ⟨2, by omega⟩
    let l : Fin (n + 1) := ⟨3, by omega⟩
    let w : Fin (n + 1) → Bool := Pi.single i true + Pi.single j true + Pi.single k true
    have hw : w ∈ S := by
      have hm := mem_of_cofactor_closure (parity_const false) (hc l false)
        ![Pi.single i true, Pi.single j true, Pi.single k true]
        (by intro q; fin_cases q <;> exact hu _)
        (by intro q; fin_cases q <;> simp [i, j, k, l, Bool.zero_eq_false])
      convert hm using 1
      ext p
      simp [w, Cslib.parity, Cslib.parityOn_eq_sum, Fin.sum_univ_succ, add_assoc]
    have hv : (fun _ : Fin (n + 1) => true) + Pi.single i true + w ∈ S := by
      have hm := mem_of_cofactor_closure (parity_const true) (hc i true)
        ![fun _ => true, Pi.single i true, w]
        (by
          intro q
          fin_cases q
          · exact hfull
          · exact hu i
          · exact hw)
        (by intro q; fin_cases q <;> simp [w, i, j, k])
      convert hm using 1
      ext p
      simp [Cslib.parity, Cslib.parityOn_eq_sum, Fin.sum_univ_succ, add_assoc]
    have he : Cslib.parityOn Finset.univ
        ((fun _ : Fin (n + 1) => true) + Pi.single i true + w) = false := by
      have hunit (p : Fin (n + 1)) : Cslib.parityOn Finset.univ (Pi.single p true) = true := by
        simp only [Cslib.parityOn_eq_sum, Pi.single_apply, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
      change Cslib.parityOn Finset.univ
        ((fun _ : Fin (n + 1) => true) + Pi.single i true +
          (Pi.single i true + Pi.single j true + Pi.single k true)) = false
      rw [Cslib.parityOn_add, Cslib.parityOn_add, Cslib.parityOn_add,
        Cslib.parityOn_add, hefull, hunit i, hunit j, hunit k]
      rfl
    have hj := congrFun (heven_full hv he) j
    simp [w, i, j, k] at hj
  have hn1 : n = 1 := by omega
  subst n
  exact ⟨S, trace, hb, hz, hu⟩

/-- A normalized binary parity failure has exactly the three nonzero tuples. In particular
the minimum-failure argument has not produced an empty or two-tuple relation. -/
theorem binary_parity_failure_eq {S : Set (Fin 2 → Bool)}
    (h : ¬IsPolymorphism (Cslib.parity 3) S) (hz : (0 : Fin 2 → Bool) ∉ S)
    (hu : ∀ i, Pi.single i true ∈ S) : S = {x | x ≠ 0} := by
  have rows (x : Fin 2 → Bool) : x = 0 ∨ x = Pi.single 0 true ∨
      x = Pi.single 1 true ∨ x = fun _ => true := by revert x; decide
  have hfull : (fun _ : Fin 2 => true) ∈ S := by
    by_contra hh
    have he : S = disequality := by
      ext x
      rcases rows x with rfl | rfl | rfl | rfl <;>
        simp [disequality, hz, hu, hh]
    rw [he] at h
    exact h (by unfold IsPolymorphism disequality; decide)
  ext x
  rcases rows x with rfl | rfl | rfl | rfl <;>
    simp [hz, hu, hfull, show (fun _ : Fin 2 => true) ≠ 0 by decide]

/-- Every relation failing ternary parity has an actual finite ordered trace to NAND.
Only projections, cofactors and single-port twists occur in the returned trace. -/
theorem exists_nand_trace {R : Set (Fin m → Bool)}
    (h : ¬IsPolymorphism (Cslib.parity 3) R) : Nonempty (Trace R nand) := by
  obtain ⟨S, ⟨trace⟩, hb, hz, hu⟩ := exists_binary_parity_minor h
  have he := binary_parity_failure_eq hb hz hu
  have ht : twist S (fun _ => true) = nand := by
    rw [he]
    ext x
    change (x + (fun _ => true) ≠ 0) ↔ ¬(x 0 = true ∧ x 1 = true)
    revert x
    decide
  exact ⟨ht ▸ trace.translate (fun _ => true)⟩

end Cslib.Logic.PL.CSP.RelationMinor
