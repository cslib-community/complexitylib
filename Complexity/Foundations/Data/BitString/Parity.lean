/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.Const
public import Mathlib.Logic.Function.DependsOn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Index

/-!
# The parity function

`parityOn s x` says whether an odd number of the bits of `x : ι → Bool` in `s` are true, and
`parity n` is the parity of all `n` bits. These are the parity functions `χ_S` of
[O'Donnell, Chapter 1][ODonnell2014], with values in `Bool` rather than `±1`.

In the Boolean ring `Bool`, where `a + b = (a ^^ b)`, the parity on `s` is the sum of the bits in
`s` (`parityOn_eq_sum`), so it splits over disjoint unions (`parityOn_union`), the parity on a
symmetric difference is the exclusive or of the parities (`parityOn_symmDiff`), and it is additive
for the coordinatewise sum of bit strings (`parityOn_add`, bundled as `parityOnAddMonoidHom`). Bit
strings are added with `+`, under which each is its own negative (`BooleanRing.add_self`), and
single bits with `^^`. Flipping one of the bits negates the parity (`parityOn_update_not`), so
the parity of a nonempty set of bits is not constant and depends on each of them; being additive,
it then takes each value on exactly half of the inputs (`card_filter_parityOn_eq`).

## Main definitions

* `Cslib.parityOn`: the parity of the bits in a set, and `Cslib.parityOnAddMonoidHom` the same as
  an additive map.
* `Cslib.parity`: the parity of all bits.

## Main results

* `Cslib.parityOn_eq_sum`: the parity is the sum of the bits in the Boolean ring.
* `Cslib.parityOn_singleton`: the parity on a singleton `{i}` is `x i`.
* `Cslib.parityOn_union`, `Cslib.parityOn_sdiff`, `Cslib.parityOn_biUnion`: the parity of a
  disjoint union, set difference, and disjoint indexed union.
* `Cslib.parityOn_symmDiff`: the parity of a symmetric difference.
* `Cslib.parityOn_add`, `Cslib.BitString.exists_eq_parityOn_iff`: the parities are the linear
  Boolean functions.
* `Cslib.parity_update_not`: flipping any bit flips the parity.
* `Cslib.card_filter_parityOn_eq`, `Cslib.dens_filter_parityOn_eq`: the parity on a nonempty set
  takes each value on half of the inputs.
* `Cslib.card_filter_parity_eq_true`: parity of `n ≥ 1` bits is true on `2 ^ (n - 1)` inputs.
* `Cslib.foldl_bne_eq_parity`: folding `xor` (`bne`) over a list of bits computes `parity`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib

open Finset Function

variable {ι : Type*}

/-- The parity of the bits of `x` in `s`: whether an odd number of them are true. -/
def parityOn (s : Finset ι) (x : ι → Bool) : Bool :=
  decide (#{i ∈ s | x i = true} % 2 = 1)

/-- The parity function on `n` bits. -/
def parity (n : ℕ) : BooleanFunction n :=
  parityOn univ

/-- A natural number, read in the Boolean ring, is its parity. -/
private theorem natCast_bool (k : ℕ) : (k : Bool) = decide (k % 2 = 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.cast_succ, ih, Bool.add_eq_xor]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;>
      simp [h, Nat.succ_mod_two_eq_one_iff, Bool.one_eq_true]

/-- **The parity is the sum of the bits** in the Boolean ring `Bool`. -/
theorem parityOn_eq_sum (s : Finset ι) (x : ι → Bool) : parityOn s x = ∑ i ∈ s, x i := by
  have h (b : Bool) : b = if b = true then 1 else 0 := by cases b <;> rfl
  rw [sum_congr rfl fun i _ => h (x i), sum_boole, natCast_bool]
  rfl

/-- The parity on the empty set is `false`. -/
@[simp] theorem parityOn_empty (x : ι → Bool) : parityOn ∅ x = false := by
  rw [parityOn_eq_sum, sum_empty]
  rfl

/-- The parity on a singleton `{i}` is the bit `x i`. -/
@[simp] theorem parityOn_singleton (i : ι) (x : ι → Bool) : parityOn {i} x = x i := by
  rw [parityOn_eq_sum, sum_singleton]

/-- The parity on `s` only reads the bits in `s`. -/
theorem parityOn_congr {s : Finset ι} {x y : ι → Bool} (h : ∀ j ∈ s, x j = y j) :
    parityOn s x = parityOn s y := by
  simp only [parityOn_eq_sum]
  exact sum_congr rfl h

/-- **Parities are linear**: the parity of a sum of bit strings is the exclusive or of the
parities. -/
theorem parityOn_add (S : Finset ι) (x y : ι → Bool) :
    parityOn S (x + y) = (parityOn S x ^^ parityOn S y) := by
  simp only [parityOn_eq_sum]
  exact sum_add_distrib

/-- The parity on `s`, as an additive map from bit strings to bits. -/
def parityOnAddMonoidHom (s : Finset ι) : (ι → Bool) →+ Bool where
  toFun := parityOn s
  map_zero' := by
    rw [parityOn_eq_sum]
    exact sum_const_zero
  map_add' := parityOn_add s

/-- `parityOnAddMonoidHom s` evaluates to `parityOn s`. -/
@[simp] theorem parityOnAddMonoidHom_apply (s : Finset ι) (x : ι → Bool) :
    parityOnAddMonoidHom s x = parityOn s x :=
  rfl

section DecidableEq

variable [DecidableEq ι] {s t : Finset ι} {i : ι}

/-- Adding a new position `i ∉ s` to the set exclusive-ors the bit `x i` into the parity. -/
theorem parityOn_insert (hi : i ∉ s) (x : ι → Bool) :
    parityOn (insert i s) x = (x i ^^ parityOn s x) := by
  simp only [parityOn_eq_sum]
  exact sum_insert hi

/-- For `i ∈ s`, the parity on `s` is `x i` exclusive-or the parity on `s.erase i`. -/
theorem parityOn_eq_xor_erase (hi : i ∈ s) (x : ι → Bool) :
    parityOn s x = (x i ^^ parityOn (s.erase i) x) := by
  simp only [parityOn_eq_sum]
  exact (add_sum_erase s x hi).symm

/-- Changing a bit outside `s` does not change the parity on `s`. -/
theorem parityOn_update_of_notMem (hi : i ∉ s) (x : ι → Bool) (b : Bool) :
    parityOn s (update x i b) = parityOn s x :=
  parityOn_congr fun _ hj => update_of_ne (ne_of_mem_of_not_mem hj hi) _ _

/-- The parity of a disjoint union is the exclusive or of the parities. -/
theorem parityOn_union (h : Disjoint s t) (x : ι → Bool) :
    parityOn (s ∪ t) x = (parityOn s x ^^ parityOn t x) := by
  simp only [parityOn_eq_sum]
  exact sum_union h

/-- The parity on a set difference `t \ s` for `s ⊆ t` is the exclusive or of the parities. -/
theorem parityOn_sdiff (h : s ⊆ t) (x : ι → Bool) :
    parityOn (t \ s) x = (parityOn t x ^^ parityOn s x) := by
  have hpar : parityOn t x = (parityOn (t \ s) x ^^ parityOn s x) := by
    rw [← parityOn_union disjoint_sdiff_self_left x, sdiff_union_of_subset h]
  rw [hpar, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The parity on a symmetric difference is the exclusive or of the parities: the bits in both
sets are counted twice. -/
theorem parityOn_symmDiff (s t : Finset ι) (x : ι → Bool) :
    parityOn (symmDiff s t) x = (parityOn s x ^^ parityOn t x) := by
  have hsdiff := sum_sdiff (f := x) (inter_subset_union : s ∩ t ⊆ s ∪ t)
  have hunion := sum_union_inter (s₁ := s) (s₂ := t) (f := x)
  rw [symmDiff_eq_sup_sdiff_inf, parityOn_eq_sum, parityOn_eq_sum, parityOn_eq_sum,
    ← Bool.add_eq_xor, ← hunion, ← hsdiff, add_assoc, BooleanRing.add_self, add_zero]

/-- The parity of a union of pairwise disjoint blocks is the parity of the parities of the
blocks. -/
theorem parityOn_biUnion {κ : Type*} {S : Finset κ} {B : κ → Finset ι}
    (hB : (S : Set κ).PairwiseDisjoint B) (x : ι → Bool) :
    parityOn (S.biUnion B) x = parityOn S fun j => parityOn (B j) x := by
  simp only [parityOn_eq_sum]
  exact sum_biUnion hB

/-- Flipping one of the bits negates the parity. -/
theorem parityOn_update_not (hi : i ∈ s) (x : ι → Bool) :
    parityOn s (update x i !x i) = !parityOn s x := by
  rw [parityOn_eq_xor_erase hi, parityOn_eq_xor_erase hi, update_self,
    parityOn_update_of_notMem (notMem_erase i s)]
  cases x i <;> simp

/-- Flipping any bit flips the parity. -/
theorem parity_update_not {n : ℕ} (x : BitString n) (i : Fin n) :
    parity n (update x i !x i) = !parity n x :=
  parityOn_update_not (mem_univ i) x

section Fintype

variable [Fintype ι]

/-- **Parities of nonempty sets are balanced**: the parity on a nonempty set of bits takes each
value on half of the inputs. Being additive, it has fibers of equal size. -/
theorem card_filter_parityOn_eq (hs : s.Nonempty) (b : Bool) :
    #{x : ι → Bool | parityOn s x = b} = 2 ^ (Fintype.card ι - 1) := by
  obtain ⟨i, hi⟩ := hs
  have hrange (c : Bool) : c ∈ Set.range (parityOnAddMonoidHom s) := by
    cases c
    · exact ⟨0, map_zero _⟩
    · have h0 : parityOn s 0 = false := map_zero (parityOnAddMonoidHom s)
      have h := parityOn_update_not hi 0
      rw [h0] at h
      exact ⟨_, h⟩
  have hfib (c : Bool) : #{x : ι → Bool | parityOn s x = c} =
      #{x : ι → Bool | parityOn s x = b} :=
    AddMonoidHom.card_fiber_eq_of_mem_range _ (hrange c) (hrange b)
  have htotal := card_filter_add_card_filter_not (s := (univ : Finset (ι → Bool)))
    fun x => parityOn s x = true
  simp only [Bool.not_eq_true, card_univ, Fintype.card_fun, Fintype.card_bool, hfib] at htotal
  have := Nat.two_pow_pred_mul_two (Fintype.card_pos_iff.2 ⟨i⟩)
  omega

/-- **Parities of nonempty sets are balanced**: the parity on a nonempty set of bits takes each
value with probability one half at a uniformly random input. -/
theorem dens_filter_parityOn_eq (hs : s.Nonempty) (b : Bool) :
    dens {x : ι → Bool | parityOn s x = b} = 2⁻¹ := by
  obtain ⟨i, hi⟩ := hs
  rw [dens_eq_card_div_card, card_filter_parityOn_eq ⟨i, hi⟩ b, Fintype.card_fun,
    Fintype.card_bool, ← Nat.two_pow_pred_mul_two (Fintype.card_pos_iff.2 ⟨i⟩), Nat.cast_mul,
    Nat.cast_ofNat, div_mul_cancel_left₀ (by positivity)]

end Fintype

end DecidableEq

/-- Parity of `n ≥ 1` bits is true on half of the inputs. -/
theorem card_filter_parity_eq_true {n : ℕ} (hn : 1 ≤ n) :
    #{x : BitString n | parity n x = true} = 2 ^ (n - 1) := by
  rw [parity, card_filter_parityOn_eq ⟨⟨0, hn⟩, mem_univ _⟩ true, Fintype.card_fin]

/-- Parity of `n ≥ 1` bits is false on half of the inputs. -/
theorem card_filter_parity_eq_false {n : ℕ} (hn : 1 ≤ n) :
    #{x : BitString n | parity n x = false} = 2 ^ (n - 1) := by
  rw [parity, card_filter_parityOn_eq ⟨⟨0, hn⟩, mem_univ _⟩ false, Fintype.card_fin]

variable {s : Finset ι} {i : ι}

/-- The parity, possibly negated, depends on each of its bits. -/
theorem not_dependsOn_parityOn (hi : i ∈ s) (c : Bool) :
    ¬DependsOn (fun x => c ^^ parityOn s x) {i}ᶜ := fun h => by
  classical
  have h' := h (x := update (fun _ => false) i true) (y := fun _ => false) fun j hj =>
    update_of_ne (by simpa using hj) _ _
  have := parityOn_update_not hi (fun _ => false)
  simp only [Bool.not_false] at this
  simp only [this] at h'
  cases parityOn s fun _ => false <;> cases c <;> simp at h'

/-- The parity of a nonempty set of bits, possibly negated, is not constant. -/
theorem not_isConst_parityOn (hs : s.Nonempty) (c : Bool) :
    ¬IsConst fun x => c ^^ parityOn s x := fun h => by
  obtain ⟨i, hi⟩ := hs
  exact not_dependsOn_parityOn hi c fun x y _ => h x y

/-- **The linear Boolean functions are the parities**: a Boolean function turns sums of bit
strings into the exclusive or of its values exactly when it is the parity of some set of
coordinates [O'Donnell, Definition 1.28][ODonnell2014]. -/
theorem BitString.exists_eq_parityOn_iff [Finite ι] {f : (ι → Bool) → Bool} :
    (∃ S, f = parityOn S) ↔ ∀ x y, f (x + y) = (f x ^^ f y) := by
  classical
  have := Fintype.ofFinite ι
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨S, rfl⟩
    exact parityOn_add S
  -- `a i` is the value of `f` at the unit vector of `i`.
  set a : ι → Bool := fun i => f (Pi.single i true)
  have hT (T : Finset ι) : f (fun j => decide (j ∈ T)) = parityOn T a := by
    induction T using Finset.induction_on with
    | empty =>
      have h0 := hf 0 0
      rw [add_zero, Bool.xor_self] at h0
      simp only [notMem_empty, decide_false, parityOn_empty]
      exact h0
    | insert i T hi ih =>
      have h : (fun j => decide (j ∈ insert i T)) =
          Pi.single i true + fun j => decide (j ∈ T) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [hi, Bool.add_eq_xor]
        · simp [hj, Bool.add_eq_xor, Bool.zero_eq_false]
      rw [h, hf, ih, parityOn_insert hi]
  refine ⟨({i | a i = true} : Finset ι), funext fun x => ?_⟩
  calc f x = f fun j => decide (j ∈ ({j | x j = true} : Finset ι)) := by simp
    _ = parityOn {j | x j = true} a := hT _
    _ = parityOn {i | a i = true} x := by simp only [parityOn, filter_filter, and_comm]

/-- Folding `xor` over a Boolean word computes `parity` of its slice. -/
theorem foldl_bne_eq_parity (w : List Bool) :
    w.foldl bne false = parity w.length (fun i => w[i]) := by
  have hcount : w.foldl bne false = decide (w.count true % 2 = 1) := by
    have hgen (b : Bool) (l : List Bool) :
        l.foldl bne b = (b != decide (l.count true % 2 = 1)) := by
      induction l generalizing b with
      | nil => cases b <;> simp
      | cons a l ih =>
        rw [List.foldl_cons, ih, List.count_cons]
        cases a <;> cases b <;>
        · by_cases h : l.count true % 2 = 1
          · have h0 : (l.count true + 1) % 2 = 0 := by omega
            simp [h, h0]
          · have h1 : (l.count true + 1) % 2 = 1 := by omega
            simp [h, h1]
    simpa using hgen false w
  rw [hcount, parity, parityOn, Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq,
    Finset.card_filter]
  have hcard (l : List Bool) :
      (∑ i : Fin l.length, if l[i] = true then 1 else 0) = l.count true := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.count_cons, ← ih]
      refine (Fin.sum_univ_succ fun i : Fin (l.length + 1) =>
        if (a :: l)[i] = true then (1 : ℕ) else 0).trans ?_
      cases a <;> simp [Nat.add_comm]
  rw [hcard w]

end Cslib
