/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Complexity.Problems.Permanent.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Complexity.Classes.SharpP.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.Matrix.Permanent.ZeroOne
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The 0/1 permanent is in #P

A certificate for a Boolean table `A` with `n` rows is an `n × n` Boolean matrix, written row by
row in `n * n` bits: bit `j + n * i` is entry `(i, j)`. The verifier
`Cslib.Complexity.ZeroOnePermanent.verifier` accepts it when it is the matrix of a permutation
`σ` (every row has a `true` entry, and no row or column has two) whose entries all lie on `true`
entries of `A`. Such certificates correspond exactly to the permutations counted by
`zeroOnePermanent_eq_card`, so the accepting count at length `n * n` is the 0/1 permanent
(`ZeroOnePermanent.acceptCount_verifier`). The verifier is polynomial-time on
`encPair encBoolTable encBits`, and padding to a polynomial length in the encoded table
(`mem_SharpP_of_polyTime_length`) puts `ZeroOnePermanent` in #P, the membership half of Valiant's
theorem [Valiant][Valiant1979], [Arora and Barak, Section 9.2][AroraBarak07],
[Goldreich, Section 6.2.1][Goldreich2007Draft].

## Main definitions

* `Cslib.Complexity.ZeroOnePermanent.verifier`: the permutation-matrix verifier.

## Main results

* `Cslib.Complexity.ZeroOnePermanent.acceptCount_verifier`: the verifier counts the permanent.
* `Cslib.Complexity.ZeroOnePermanent.mem_SharpP`: `ZeroOnePermanent ∈ SharpP encBoolTable`.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

namespace ZeroOnePermanent

/-- Entry `(i, j)` of an `n × n` Boolean matrix written row by row in the bit string `w`. -/
@[expose]
def bit (w : List Bool) (n i j : ℕ) : Bool := w.getD (j + n * i) false

/-- Reading an entry of a computed certificate at computed unary coordinates is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_bit {γ : Type} {input : γ ↪ List Bool} {w : γ → List Bool}
    {n i j : γ → ℕ} (hw : ComputableInPolyTime w input encBits)
    (hn : ComputableInPolyTime n input encUnary) (hi : ComputableInPolyTime i input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun x => bit (w x) (n x) (i x) (j x)) input encBool :=
  bitsGetDWithInput hw (unary_add' hj (unary_mul' hn hi)) false

/-- Accept a certificate `w` for the table `A` with `n` rows when, read as an `n × n` matrix by
`bit`, every row has a `true` entry, no row or column has two, and every `true` entry is a `true`
entry of `A`. -/
@[expose]
def verifier (x : List (List Bool) × List Bool) : Bool :=
  (List.range x.1.length).all fun i =>
    ((List.range x.1.length).any fun j => bit x.2 x.1.length i j) &&
      (List.range x.1.length).all fun j =>
        (!bit x.2 x.1.length i j || (x.1.getD i []).getD j false) &&
          (List.range x.1.length).all fun k =>
            (!(bit x.2 x.1.length i j && bit x.2 x.1.length i k) || j == k) &&
              (!(bit x.2 x.1.length i j && bit x.2 x.1.length k j) || i == k)

section PolyTime

variable {γ : Type} {input : γ ↪ List Bool} {L : γ → List (List Bool)} {w : γ → List Bool}
  {i j : γ → ℕ}

private theorem polyTime_colCheck (hL : ComputableInPolyTime L input encBoolTable)
    (hw : ComputableInPolyTime w input encBits) (hi : ComputableInPolyTime i input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun x => (List.range (L x).length).all fun k =>
      (!(bit (w x) (L x).length (i x) (j x) && bit (w x) (L x).length (i x) k) || j x == k) &&
        (!(bit (w x) (L x).length (i x) (j x) && bit (w x) (L x).length k (j x)) || i x == k))
      input encBool := by
  have hn : ComputableInPolyTime (fun x => (L x).length) input encUnary :=
    (length_list (encList encBool)).comp hL
  exact allWithInput (range.comp hn) (by fun_prop)

private theorem polyTime_entryCheck (hL : ComputableInPolyTime L input encBoolTable)
    (hw : ComputableInPolyTime w input encBits) (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun x => (List.range (L x).length).all fun j =>
      (!bit (w x) (L x).length (i x) j || ((L x).getD (i x) []).getD j false) &&
        (List.range (L x).length).all fun k =>
          (!(bit (w x) (L x).length (i x) j && bit (w x) (L x).length (i x) k) || j == k) &&
            (!(bit (w x) (L x).length (i x) j && bit (w x) (L x).length k j) || i x == k))
      input encBool := by
  have hn : ComputableInPolyTime (fun x => (L x).length) input encUnary :=
    (length_list (encList encBool)).comp hL
  refine allWithInput (range.comp hn) (bool_and' ?_ ?_)
  · have hrow : ComputableInPolyTime (fun p : γ × ℕ => (L p.1).getD (i p.1) [])
        (encPair input encUnary) (encList encBool) :=
      listGetDWithInput (hL.comp (fst _ _)) (hi.comp (fst _ _)) []
    exact bool_or' (bool_not.comp (computableInPolyTime_bit (hw.comp (fst _ _))
      (hn.comp (fst _ _)) (hi.comp (fst _ _)) (snd _ _)))
      (listGetDWithInput hrow (snd _ _) false)
  · exact polyTime_colCheck (hL.comp (fst _ _)) (hw.comp (fst _ _)) (hi.comp (fst _ _))
      (snd _ _)

end PolyTime

/-- The verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encBoolTable encBits) encBool := by
  have hL : ComputableInPolyTime (fun x : List (List Bool) × List Bool => x.1)
      (encPair encBoolTable encBits) encBoolTable := fst _ _
  have hw : ComputableInPolyTime (fun x : List (List Bool) × List Bool => x.2)
      (encPair encBoolTable encBits) encBits := snd _ _
  have hn := (length_list (encList encBool)).comp hL
  refine allWithInput (range.comp hn) (bool_and' ?_ ?_)
  · exact anyWithInput (range.comp (hn.comp (fst _ _))) (computableInPolyTime_bit
      (hw.comp ((fst _ _).comp (fst _ _))) (hn.comp ((fst _ _).comp (fst _ _)))
      ((snd _ _).comp (fst _ _)) (snd _ _))
  · exact polyTime_entryCheck (hL.comp (fst _ _)) (hw.comp (fst _ _)) (snd _ _)

/-- The verifier's condition, on a certificate of length `n * n`, read as a Boolean matrix. -/
theorem verifier_ofFn (A : List (List Bool)) (w : Fin (A.length * A.length) → Bool) :
    verifier (A, List.ofFn w) = true ↔
      (∀ i, ∃ j, w (finProdFinEquiv (i, j)) = true) ∧
        (∀ i j k, w (finProdFinEquiv (i, j)) = true → w (finProdFinEquiv (i, k)) = true →
          j = k) ∧
        (∀ i k j, w (finProdFinEquiv (i, j)) = true → w (finProdFinEquiv (k, j)) = true →
          i = k) ∧
        ∀ i j : Fin A.length, w (finProdFinEquiv (i, j)) = true → A[i].getD j false = true := by
  have hbit : ∀ i j : Fin A.length,
      bit (List.ofFn w) A.length i j = w (finProdFinEquiv (i, j)) := fun i j =>
    List.getD_ofFn_of_lt w (finProdFinEquiv (i, j)).isLt false
  simp only [verifier, List.all_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_iff_eq]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i j k hj hk => ?_, fun i k j hi hk => ?_, fun i j hij => ?_⟩
    · obtain ⟨j, hj, hb⟩ := (h i i.isLt).1
      exact ⟨⟨j, hj⟩, by rw [← hbit]; exact hb⟩
    · rcases ((h i i.isLt).2 j j.isLt).2 k k.isLt |>.1 with (h' | h') | h'
      · rw [hbit] at h'; simp [hj] at h'
      · rw [hbit] at h'; simp [hk] at h'
      · exact Fin.ext h'
    · rcases ((h i i.isLt).2 j j.isLt).2 k k.isLt |>.2 with (h' | h') | h'
      · rw [hbit] at h'; simp [hi] at h'
      · rw [hbit] at h'; simp [hk] at h'
      · exact Fin.ext h'
    · rcases ((h i i.isLt).2 j j.isLt).1 with h' | h'
      · rw [hbit] at h'; simp [hij] at h'
      · rwa [List.getD_eq_getElem _ _ i.isLt] at h'
  · rintro ⟨hrow, huniq, hcol, hsupp⟩ i hi
    refine ⟨?_, fun j hj => ⟨?_, fun k hk => ⟨?_, ?_⟩⟩⟩
    · obtain ⟨j, hj⟩ := hrow ⟨i, hi⟩
      exact ⟨j, j.isLt, by rw [hbit ⟨i, hi⟩ j]; exact hj⟩
    · by_cases hb : w (finProdFinEquiv (⟨i, hi⟩, ⟨j, hj⟩)) = true
      · right
        rw [List.getD_eq_getElem _ _ hi]
        exact hsupp ⟨i, hi⟩ ⟨j, hj⟩ hb
      · left
        rw [hbit ⟨i, hi⟩ ⟨j, hj⟩]
        simpa using hb
    · by_cases hb : w (finProdFinEquiv (⟨i, hi⟩, ⟨j, hj⟩)) = true
      · by_cases hb' : w (finProdFinEquiv (⟨i, hi⟩, ⟨k, hk⟩)) = true
        · exact Or.inr (congrArg Fin.val (huniq _ _ _ hb hb'))
        · left; right; rw [hbit ⟨i, hi⟩ ⟨k, hk⟩]; simpa using hb'
      · left; left; rw [hbit ⟨i, hi⟩ ⟨j, hj⟩]; simpa using hb
    · by_cases hb : w (finProdFinEquiv (⟨i, hi⟩, ⟨j, hj⟩)) = true
      · by_cases hb' : w (finProdFinEquiv (⟨k, hk⟩, ⟨j, hj⟩)) = true
        · exact Or.inr (congrArg Fin.val (hcol _ _ _ hb hb'))
        · left; right; rw [hbit ⟨k, hk⟩ ⟨j, hj⟩]; simpa using hb'
      · left; left; rw [hbit ⟨i, hi⟩ ⟨j, hj⟩]; simpa using hb

/-- **The verifier counts the 0/1 permanent**: at certificate length `n * n` it accepts exactly
the row-by-row permutation matrices supported on `true` entries. -/
theorem acceptCount_verifier (A : List (List Bool)) :
    acceptCount verifier A (A.length * A.length) = ZeroOnePermanent A := by
  classical
  rw [zeroOnePermanent_eq_card,
    ← Matrix.card_filter_isPermMatrix fun i j : Fin A.length => A[i].getD j false = true,
    acceptCount]
  let e : (Fin (A.length * A.length) → Bool) ≃ (Fin A.length → Fin A.length → Bool) :=
    (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)
  refine Finset.card_equiv e fun w => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, verifier_ofFn]
  have he : ∀ i j, e w i j = w (finProdFinEquiv (i, j)) := fun i j => by
    simp [e, Equiv.arrowCongr_apply]
  simp only [he]

/-- **The 0/1 permanent is in #P** [Valiant][Valiant1979]. -/
theorem mem_SharpP : ZeroOnePermanent ∈ SharpP encBoolTable := by
  have h := mem_SharpP_of_polyTime_length (enc := encBoolTable) computableInPolyTime_verifier
    (r := fun A => A.length * A.length) (by fun_prop)
  simpa only [acceptCount_verifier] using h

end ZeroOnePermanent

end Cslib.Complexity
