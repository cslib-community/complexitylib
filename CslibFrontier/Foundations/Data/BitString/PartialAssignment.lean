/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Part
public import Mathlib.Logic.Function.DependsOn

/-!
# Partial assignments

A *partial assignment* of the coordinates `ι` fixes some of them and leaves the others free: a map
`ρ : ι → Option Bool` with `ρ i = some b` when coordinate `i` is fixed to `b`. In circuit complexity
it is called a *restriction*, Jukna's `ρ : ι → {0, 1, *}` [Jukna, Section 1.6][Jukna2012],
[Hastad1986]. Restricting a function `f` on `ι → Bool` by `ρ` gives `f ∘ ρ.fill`, Jukna's `f↾ρ`,
where `ρ.fill x` takes the fixed coordinates from `ρ` and the free ones from `x`.

The *subfunctions* of `f` on a set `Y` of coordinates are its restrictions by the partial
assignments that fix exactly the coordinates outside `Y` (`subfunctions`, `mem_subfunctions_iff`);
counting them is the method of Nechiporuk.

## Main definitions

* `Cslib.BitString.PartialAssignment`: partial assignments of the coordinates `ι`, and
  `Cslib.BitString.PartialAssignment.empty` the one fixing nothing.
* `Cslib.BitString.PartialAssignment.fill`: complete an input by the fixed coordinates.
* `Cslib.BitString.PartialAssignment.Agrees`: an input agrees with a partial assignment.
* `Cslib.BitString.PartialAssignment.free`, `Cslib.BitString.PartialAssignment.support`: the free
  and the fixed coordinates.
* `Cslib.BitString.PartialAssignment.assign`, `Cslib.BitString.PartialAssignment.unassign`: fix the
  coordinates of a set to the values of a word, and free the coordinates of a set.
* `Cslib.BitString.PartialAssignment.outside`: the partial assignment fixing the coordinates
  outside a set to the values of a word.
* `Cslib.BitString.PartialAssignment.Extends`: the information order on partial assignments.
* `Cslib.BitString.subfunctions`: the subfunctions of a function on a set of coordinates.

## Main results

* `Cslib.BitString.PartialAssignment.agrees_iff_fill_eq`: an input agrees with a partial
  assignment when filling it changes nothing.
* `Cslib.BitString.PartialAssignment.extends_iff_ofOption_le`: extension is the pointwise order of
  `Part Bool`.
* `Cslib.BitString.PartialAssignment.Extends.update_some`,
  `Cslib.BitString.PartialAssignment.Extends.update_none`: updating a free coordinate of `ρ₀`
  preserves extending `ρ₀`.
* `Cslib.BitString.mem_subfunctions_iff`: subfunctions are restrictions.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [J. Håstad, *Almost optimal lower bounds for small depth circuits*][Hastad1986]
-/

@[expose] public section

namespace Cslib.BitString

open Function Finset

/-- A partial assignment (a restriction, in circuit complexity) of the coordinates `ι`: `some b`
fixes a coordinate to `b`, and `none` leaves it free.

Being an abbreviation of `ι → Option Bool`, a partial assignment inherits the pointwise order of
the order of core on `Option Bool`, in which `none < some false < some true`. That order is not the
information order: `ρ ≤ ρ'` does not say that `ρ'` extends `ρ`. The information order is
`PartialAssignment.Extends`, the pointwise order on `Part Bool`
(`PartialAssignment.extends_iff_ofOption_le`). -/
abbrev PartialAssignment (ι : Type*) : Type _ :=
  ι → Option Bool

namespace PartialAssignment

variable {ι : Type*} {ρ : PartialAssignment ι} {i j : ι} {b : Bool}

/-- The partial assignment fixing nothing. -/
def empty : PartialAssignment ι :=
  fun _ => none

/-- The partial assignment fixing nothing leaves every coordinate free. -/
@[simp] theorem empty_apply (i : ι) : (empty : PartialAssignment ι) i = none :=
  rfl

/-- Complete `x` by the coordinates fixed by `ρ`. -/
def fill (ρ : PartialAssignment ι) (x : ι → Bool) : ι → Bool :=
  fun i => (ρ i).getD (x i)

/-- At a coordinate left free by `ρ`, `ρ.fill x` takes the bit of `x`. -/
@[simp] theorem fill_of_eq_none (hi : ρ i = none) (x : ι → Bool) : ρ.fill x i = x i := by
  simp [fill, hi]

/-- At a coordinate that `ρ` fixes to `b`, `ρ.fill x` is `b`. -/
@[simp] theorem fill_of_eq_some (hi : ρ i = some b) (x : ι → Bool) : ρ.fill x i = b := by
  simp [fill, hi]

/-- Fixing nothing changes nothing. -/
@[simp] theorem fill_empty (x : ι → Bool) : (empty : PartialAssignment ι).fill x = x :=
  rfl

/-- `fill_empty`, for the partial assignment fixing nothing written as a function. -/
@[simp] theorem fill_none (x : ι → Bool) : fill (fun _ => none) x = x :=
  fill_empty x

/-! ### Agreement -/

/-- The input `x` *agrees* with `ρ`: it takes the value fixed by `ρ` at every fixed coordinate. -/
def Agrees (ρ : PartialAssignment ι) (x : ι → Bool) : Prop :=
  ∀ i b, ρ i = some b → x i = b

/-- Agreement with a partial assignment of finitely many coordinates is decidable. -/
instance [Fintype ι] (ρ : PartialAssignment ι) (x : ι → Bool) : Decidable (ρ.Agrees x) :=
  inferInstanceAs (Decidable (∀ i b, ρ i = some b → x i = b))

/-- An input agrees with `ρ` exactly when filling it from `ρ` does not change it. -/
theorem agrees_iff_fill_eq {x : ι → Bool} : ρ.Agrees x ↔ ρ.fill x = x := by
  refine ⟨fun h => funext fun i => ?_, fun h i b hi => by rw [← h, fill_of_eq_some hi]⟩
  cases hρ : ρ i with
  | none => exact fill_of_eq_none hρ x
  | some c => rw [fill_of_eq_some hρ, h i c hρ]

/-- A filled input agrees with the partial assignment it was filled from. -/
theorem agrees_fill (ρ : PartialAssignment ι) (x : ι → Bool) : ρ.Agrees (ρ.fill x) :=
  fun _ _ hi => fill_of_eq_some hi x

/-- Every input agrees with the partial assignment fixing nothing. -/
@[simp] theorem agrees_empty (x : ι → Bool) : (empty : PartialAssignment ι).Agrees x :=
  fun _ _ h => by simp at h

/-- Filling preserves agreement away from coordinate `i`. -/
theorem fill_eq_fill_of_forall_ne {x y : ι → Bool} (h : ∀ j, j ≠ i → x j = y j) (j : ι)
    (hj : j ≠ i) : ρ.fill x j = ρ.fill y j := by
  simp [fill, h j hj]

/-- A function that ignores coordinate `i` still ignores it once coordinates are hardwired. -/
theorem dependsOn_comp_fill {β : Type*} {f : (ι → Bool) → β} (hf : DependsOn f {i}ᶜ)
    (ρ : PartialAssignment ι) : DependsOn (f ∘ ρ.fill) {i}ᶜ :=
  fun _ _ h => hf fun j hj => fill_eq_fill_of_forall_ne (fun k hk => h k hk) j hj

/-! ### Fixing and freeing coordinates -/

section DecidableEq

variable [DecidableEq ι]

/-- Filling after fixing coordinate `i` to `b` updates the filled input at `i`. -/
@[simp] theorem fill_update (ρ : PartialAssignment ι) (i : ι) (b : Bool) (x : ι → Bool) :
    fill (update ρ i (some b)) x = update (ρ.fill x) i b := by
  funext j
  by_cases hj : j = i <;> simp [fill, hj]

/-- Fixing a single coordinate `i` to `b` in the empty partial assignment updates the input at
`i`. -/
theorem fill_update_empty (i : ι) (b : Bool) (x : ι → Bool) :
    fill (update empty i (some b)) x = update x i b := by
  simp

/-- Filling after fixing one more free coordinate is filling twice. -/
theorem fill_fill_update (hi : ρ i = none) (b : Bool) (x : ι → Bool) :
    ρ.fill (fill (update ρ i (some b)) x) = fill (update ρ i (some b)) x := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [fill, hi]
  · simp only [fill, update_of_ne hj]
    cases ρ j <;> rfl

/-- Changing a fixed coordinate does not change the filled input. -/
theorem fill_update_of_ne_none (hi : ρ i ≠ none) (x : ι → Bool) (c : Bool) :
    ρ.fill (update x i c) = ρ.fill x := by
  funext j
  by_cases hj : j = i
  · subst hj
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hi
    simp [fill, hb]
  · simp [fill, update_of_ne hj]

/-- Changing a free coordinate changes the filled input there. -/
theorem fill_update_of_eq_none (hi : ρ i = none) (x : ι → Bool) (c : Bool) :
    ρ.fill (update x i c) = update (ρ.fill x) i c := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [fill, hi]
  · simp [fill, update_of_ne hj]

/-- Fix the coordinates of `S` to their values in `a`. -/
def assign (ρ : PartialAssignment ι) (S : Finset ι) (a : ι → Bool) : PartialAssignment ι :=
  S.piecewise (fun i => some (a i)) ρ

/-- `ρ.assign S a` fixes each coordinate of `S` to its value in `a`. -/
@[simp] theorem assign_of_mem {S : Finset ι} (hi : i ∈ S) (a : ι → Bool) :
    ρ.assign S a i = some (a i) :=
  piecewise_eq_of_mem _ _ _ hi

/-- `ρ.assign S a` agrees with `ρ` outside `S`. -/
@[simp] theorem assign_of_notMem {S : Finset ι} (hi : i ∉ S) (a : ι → Bool) :
    ρ.assign S a i = ρ i :=
  piecewise_eq_of_notMem _ _ _ hi

/-- Fixing the coordinates of `S` twice keeps the values of the second assignment. -/
@[simp] theorem assign_assign (ρ : PartialAssignment ι) (S : Finset ι) (a b : ι → Bool) :
    (ρ.assign S a).assign S b = ρ.assign S b :=
  piecewise_idem_right _ _ _ _

/-- Fixing coordinates to the values they already have changes nothing. -/
theorem assign_eq_self {S : Finset ι} {a : ι → Bool} (h : ∀ i ∈ S, ρ i = some (a i)) :
    ρ.assign S a = ρ := by
  funext i
  by_cases hi : i ∈ S
  · simp [hi, h i hi]
  · simp [hi]

/-- Free the coordinates of `S`. -/
def unassign (ρ : PartialAssignment ι) (S : Finset ι) : PartialAssignment ι :=
  S.piecewise empty ρ

/-- `ρ.unassign S` leaves the coordinates of `S` free. -/
@[simp] theorem unassign_of_mem {S : Finset ι} (hi : i ∈ S) : ρ.unassign S i = none :=
  piecewise_eq_of_mem _ _ _ hi

/-- `ρ.unassign S` agrees with `ρ` outside `S`. -/
@[simp] theorem unassign_of_notMem {S : Finset ι} (hi : i ∉ S) : ρ.unassign S i = ρ i :=
  piecewise_eq_of_notMem _ _ _ hi

/-- Freeing no coordinates changes nothing. -/
@[simp] theorem unassign_empty (ρ : PartialAssignment ι) : ρ.unassign ∅ = ρ :=
  piecewise_empty _ _

/-- The partial assignment fixing the coordinates outside `Y` to their values in `z`. -/
def outside (Y : Finset ι) (z : ι → Bool) : PartialAssignment ι :=
  fun j => if j ∈ Y then none else some (z j)

/-- Filling `x` from `outside Y z` takes the coordinates in `Y` from `x` and the others from
`z`. -/
@[simp] theorem fill_outside (Y : Finset ι) (z x : ι → Bool) :
    (outside Y z).fill x = Y.piecewise x z := by
  funext j
  by_cases hj : j ∈ Y <;> simp [outside, fill, hj]

end DecidableEq

/-! ### Free coordinates -/

section Fintype

variable [Fintype ι]

/-- The coordinates left free by `ρ`. -/
def free (ρ : PartialAssignment ι) : Finset ι :=
  {i | ρ i = none}

/-- A coordinate is free in `ρ` exactly when `ρ` maps it to `none`. -/
@[simp] theorem mem_free : i ∈ ρ.free ↔ ρ i = none := by
  simp [free]

/-- The partial assignment fixing nothing leaves every coordinate free. -/
@[simp] theorem free_empty : (empty : PartialAssignment ι).free = univ := by
  ext
  simp

/-- `free_empty`, for the partial assignment fixing nothing written as a function. -/
@[simp] theorem free_none : free (fun _ : ι => none) = univ :=
  free_empty

/-- The coordinates fixed by `ρ`, the complement of its free coordinates (`compl_free`). -/
def support (ρ : PartialAssignment ι) : Finset ι :=
  {i | (ρ i).isSome}

/-- A coordinate is in the support of `ρ` exactly when `ρ` fixes it. -/
@[simp] theorem mem_support : i ∈ ρ.support ↔ (ρ i).isSome := by
  simp [support]

/-- The partial assignment fixing nothing has empty support. -/
@[simp] theorem support_empty : (empty : PartialAssignment ι).support = ∅ := by
  ext
  simp

/-- A restricted function `f ∘ ρ.fill` depends only on the free coordinates of `ρ`. -/
theorem dependsOn_comp_fill_free {β : Type*} (f : (ι → Bool) → β) (ρ : PartialAssignment ι) :
    DependsOn (f ∘ ρ.fill) ρ.free := by
  intro x y h
  simp only [comp_apply]
  congr 1
  funext i
  by_cases hi : i ∈ ρ.free
  · rw [fill_of_eq_none (mem_free.1 hi), fill_of_eq_none (mem_free.1 hi), h i hi]
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 fun h' => hi (mem_free.2 h')
    rw [fill_of_eq_some hb, fill_of_eq_some hb]

variable [DecidableEq ι]

/-- The free coordinates are those outside the support. -/
theorem compl_free (ρ : PartialAssignment ι) : ρ.freeᶜ = ρ.support := by
  ext i
  simp [Option.isSome_iff_ne_none]

/-- The coordinates outside the support are the free coordinates. -/
theorem compl_support (ρ : PartialAssignment ι) : ρ.supportᶜ = ρ.free := by
  rw [← compl_free, compl_compl]

/-- Fixing coordinate `i` removes it from the free coordinates. -/
@[simp] theorem free_update (ρ : PartialAssignment ι) (i : ι) (b : Bool) :
    free (update ρ i (some b)) = ρ.free.erase i := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

/-- Freeing coordinate `i` adds it to the free coordinates. -/
@[simp] theorem free_update_none (ρ : PartialAssignment ι) (i : ι) :
    free (update ρ i none) = insert i ρ.free := by
  ext j
  by_cases hj : j = i <;> simp [hj]

/-- Fixing the coordinates of `S` removes them from the free coordinates. -/
@[simp] theorem free_assign (ρ : PartialAssignment ι) (S : Finset ι) (a : ι → Bool) :
    (ρ.assign S a).free = ρ.free \ S := by
  ext i
  by_cases hi : i ∈ S <;> simp [hi]

/-- Fixing free coordinates to the values of `x` does not change the input filled from `x`. -/
theorem fill_assign {S : Finset ι} (hS : S ⊆ ρ.free) {a x : ι → Bool}
    (h : ∀ i ∈ S, a i = x i) : (ρ.assign S a).fill x = ρ.fill x := by
  funext i
  by_cases hi : i ∈ S
  · simp [fill, hi, h i hi, mem_free.1 (hS hi)]
  · simp [fill, hi]

/-- Fixing free coordinates and freeing them again gives back the partial assignment. -/
theorem unassign_union_assign {S Q : Finset ι} (hS : S ⊆ ρ.free) (a : ι → Bool) :
    (ρ.assign S a).unassign (Q ∪ S) = ρ.unassign Q := by
  funext i
  by_cases hiS : i ∈ S
  · by_cases hiQ : i ∈ Q <;> simp [hiS, hiQ, mem_free.1 (hS hiS)]
  · by_cases hiQ : i ∈ Q <;> simp [hiS, hiQ]

/-- The free coordinates of `outside Y z` are exactly those of `Y`. -/
@[simp] theorem free_outside (Y : Finset ι) (z : ι → Bool) : (outside Y z).free = Y := by
  ext j
  by_cases hj : j ∈ Y <;> simp [outside, hj]

/-- Restricting `f ∘ ρ.fill` by fixing a free coordinate `i` of `ρ` to `b` is restricting `f` by
`update ρ i (some b)`. -/
theorem comp_fill_update_empty_of_mem_free {β : Type*} {ρ : PartialAssignment ι} {i : ι}
    (hi : i ∈ ρ.free) (b : Bool) (f : (ι → Bool) → β) :
    (f ∘ ρ.fill) ∘ fill (update empty i (some b)) = f ∘ fill (update ρ i (some b)) := by
  funext x
  simp [fill_update_of_eq_none (mem_free.1 hi)]

end Fintype

/-! ### Extensions -/

/-- `ρ'` extends `ρ`: it fixes every coordinate that `ρ` fixes, to the same value. This is the
information order on partial assignments; the order on `Option` in core is a different one. -/
def Extends (ρ' ρ : PartialAssignment ι) : Prop :=
  ∀ i b, ρ i = some b → ρ' i = some b

/-- Extension of partial assignments of finitely many coordinates is decidable. -/
instance [Fintype ι] (ρ' ρ : PartialAssignment ι) : Decidable (ρ'.Extends ρ) :=
  inferInstanceAs (Decidable (∀ i b, ρ i = some b → ρ' i = some b))

/-- Every partial assignment extends itself. -/
@[refl] theorem Extends.refl (ρ : PartialAssignment ι) : ρ.Extends ρ := fun _ _ h => h

/-- Extension is transitive: an extension of an extension of `ρ` extends `ρ`. -/
theorem Extends.trans {ρ ρ' ρ'' : PartialAssignment ι} (h₁ : ρ''.Extends ρ') (h₂ : ρ'.Extends ρ) :
    ρ''.Extends ρ :=
  fun i b h => h₁ i b (h₂ i b h)

/-- **The information order**: `ρ'` extends `ρ` exactly when it is above `ρ` pointwise in the
order of `Part Bool`, where an undefined value is below every value and distinct values are
incomparable. -/
theorem extends_iff_ofOption_le {ρ ρ' : PartialAssignment ι} :
    ρ'.Extends ρ ↔ (fun i => Part.ofOption (ρ i)) ≤ fun i => Part.ofOption (ρ' i) := by
  simp only [Pi.le_def]
  exact forall_congr' fun i => forall_congr' fun b => by
    simp only [Part.mem_ofOption, Option.mem_def]

/-- Every partial assignment extends the one fixing nothing. -/
@[simp] theorem extends_empty (ρ : PartialAssignment ι) : ρ.Extends empty :=
  fun _ _ h => by simp at h

/-- An input agreeing with `ρ'` agrees with every partial assignment that `ρ'` extends. -/
theorem Extends.agrees {ρ ρ' : PartialAssignment ι} (h : ρ'.Extends ρ) {x : ι → Bool}
    (hx : ρ'.Agrees x) : ρ.Agrees x :=
  fun i b hi => hx i b (h i b hi)

/-- Filling from an extension of `ρ` is not changed by filling from `ρ`. -/
theorem fill_fill_of_extends {ρ ρ' : PartialAssignment ι} (h : ρ'.Extends ρ) (x : ι → Bool) :
    ρ.fill (ρ'.fill x) = ρ'.fill x := by
  funext i
  cases hρ : ρ i with
  | none => simp [fill, hρ]
  | some b => simp [fill, hρ, h i b hρ]

section Fintype

variable [Fintype ι]

/-- A free coordinate of an extension is free in the partial assignment it extends. -/
theorem Extends.free_subset {ρ ρ' : PartialAssignment ι} (h : ρ'.Extends ρ) : ρ'.free ⊆ ρ.free :=
  fun i hi => mem_free.2 <| by
    cases hρ : ρ i with
    | none => rfl
    | some b => exact absurd (h i b hρ) (by rw [mem_free.1 hi]; simp)

variable [DecidableEq ι]

/-- Fixing free coordinates extends a partial assignment. -/
theorem extends_assign {S : Finset ι} (hS : S ⊆ ρ.free) (a : ι → Bool) :
    (ρ.assign S a).Extends ρ := fun i b hi => by
  have : i ∉ S := fun h => by simp [mem_free.1 (hS h)] at hi
  simpa [this] using hi

/-- Fixing a coordinate of `ρ` that is free in `ρ₀` preserves extending `ρ₀`. -/
theorem Extends.update_some {ρ₀ ρ : PartialAssignment ι} (h : ρ.Extends ρ₀) {i : ι}
    (hi : i ∈ ρ₀.free) (b : Bool) : Extends (update ρ i (some b)) ρ₀ :=
  fun j c hj => by
    rw [update_of_ne (by rintro rfl; simp [mem_free.1 hi] at hj)]
    exact h j c hj

/-- Freeing a coordinate of `ρ` that is free in `ρ₀` preserves extending `ρ₀`. -/
theorem Extends.update_none {ρ₀ ρ : PartialAssignment ι} (h : ρ.Extends ρ₀) {i : ι}
    (hi : i ∈ ρ₀.free) : Extends (update ρ i none) ρ₀ :=
  fun j c hj => by
    rw [update_of_ne (by rintro rfl; simp [mem_free.1 hi] at hj)]
    exact h j c hj

end Fintype

end PartialAssignment

/-! ### Subfunctions -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The subfunctions of `f` on the coordinates `Y`: for each assignment `z` of the other
coordinates, the function that reads the coordinates in `Y` from its input and the others from
`z`. -/
def subfunctions (f : (ι → Bool) → Bool) (Y : Finset ι) : Finset ((ι → Bool) → Bool) :=
  univ.image fun z x => f (Y.piecewise x z)

/-- `g` is a subfunction of `f` on `Y` exactly when, for some assignment `z`, `g` reads the
coordinates in `Y` from its input and the others from `z` before applying `f`. -/
@[simp] theorem mem_subfunctions {f g : (ι → Bool) → Bool} {Y : Finset ι} :
    g ∈ subfunctions f Y ↔ ∃ z, (fun x => f (Y.piecewise x z)) = g := by
  simp [subfunctions]

/-- The subfunctions on `Y` are the restrictions by the partial assignments fixing exactly the
coordinates outside `Y`. -/
theorem mem_subfunctions_iff {f g : (ι → Bool) → Bool} {Y : Finset ι} :
    g ∈ subfunctions f Y ↔ ∃ z, f ∘ (PartialAssignment.outside Y z).fill = g := by
  simp only [mem_subfunctions]
  exact exists_congr fun z => by rw [show f ∘ (PartialAssignment.outside Y z).fill =
    fun x => f (Y.piecewise x z) from funext fun x => by simp]

end Cslib.BitString
