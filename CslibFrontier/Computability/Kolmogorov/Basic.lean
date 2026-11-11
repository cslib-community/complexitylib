/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Seq.Computation
public import Mathlib.Data.ENat.Lattice

/-!
# Kolmogorov complexity relative to a description method

A *description method* runs binary programs: `M.run p` is the computation of the program `p`, a
Mathlib `Computation`, which may or may not terminate with an object. The computation comes with a
clock: `(M.run p).runFor t` is the output of `p` after `t` steps, or `none` if `p` has not
halted by then. A computation has at most one result, so every program describes at most one
object. The *plain Kolmogorov complexity* `M.ecomplexity x` of an object `x` is the length of a
shortest program that eventually outputs `x`, and its *time-bounded Kolmogorov complexity*
`M.etimeBoundedComplexity t x` is the length of a shortest program that outputs `x` within `t` steps
[Li and Vitányi, Chapters 2 and 7][LiVitanyi2019]. Both take values in `ℕ∞`, and are `⊤` when no
program describes `x`; as for cslib's circuit complexity `Cslib.Circuits.ecomplexity`, the prefix
`e` stands for "extended".

Nothing here depends on a machine model. A multi-tape Turing machine gives a description method
(`Cslib.Kolmogorov.DescriptionMethod.ofMultiTapeTM`), and so does any other model with a clocked
semantics. The usual machine-independent complexity is the complexity of a method that simulates
every other one with constant program overhead (`Cslib.Kolmogorov.DescriptionMethod.Simulation`);
for the partial recursive description methods, `Cslib.Kolmogorov.DescriptionMethod.universal` is
such a method.

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod`: binary programs run as computations.
* `Cslib.Kolmogorov.DescriptionMethod.Produces`: a program eventually outputs an object.
* `Cslib.Kolmogorov.DescriptionMethod.ecomplexity`: the plain complexity `C_M(x)`.
* `Cslib.Kolmogorov.DescriptionMethod.etimeBoundedComplexity`: the time-bounded complexity
  `C_M^t(x)`.
* `Cslib.Kolmogorov.DescriptionMethod.complexity`: the plain complexity as a natural number, for
  objects with a description.
* `Cslib.Kolmogorov.DescriptionMethod.literal`: the method in which every program prints itself.
* `Cslib.Kolmogorov.DescriptionMethod.map`: pushforward of a description method along `f : α → β`.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.Produces.unique`: a program describes at most one object.
* `Cslib.Kolmogorov.DescriptionMethod.ecomplexity_le_natCast_iff`,
  `Cslib.Kolmogorov.DescriptionMethod.etimeBoundedComplexity_le_natCast_iff`: the complexity is at
  most `k` exactly when some program of length at most `k` describes the object (within the time
  bound); the strict versions are `ecomplexity_lt_natCast_iff` and
  `etimeBoundedComplexity_lt_natCast_iff`.
* `Cslib.Kolmogorov.DescriptionMethod.exists_length_eq_ecomplexity`: a finite complexity is the
  length of a describing program.
* `Cslib.Kolmogorov.DescriptionMethod.etimeBoundedComplexity_antitone`: more time cannot increase
  the time-bounded complexity.
* `Cslib.Kolmogorov.DescriptionMethod.iInf_etimeBoundedComplexity`,
  `Cslib.Kolmogorov.DescriptionMethod.exists_etimeBoundedComplexity_eq_ecomplexity`: the plain
  complexity is the time-bounded complexity for a large enough time bound.
* `Cslib.Kolmogorov.DescriptionMethod.ecomplexity_map_le`,
  `Cslib.Kolmogorov.DescriptionMethod.ecomplexity_map_eq_of_injective`: pushing forward a
  description method cannot increase complexity and preserves it under injective maps.

## References

* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Kolmogorov

/-- A *description method* for objects of type `α`: `run p` is the computation of the binary
program `p`, which may or may not terminate with an object. Its clock is that of the computation:
`(run p).runFor t` is the output of `p` after `t` steps, if `p` has halted by then. This is the
clocked analogue of a partial function from programs to objects
[Li and Vitányi, Chapter 2][LiVitanyi2019]. -/
structure DescriptionMethod (α : Type*) where
  /-- The computation of the program `p`. -/
  run : List Bool → Computation α

namespace DescriptionMethod

variable {α : Type*} (M : DescriptionMethod α)

/-- The program `p` eventually outputs `x`. -/
def Produces (p : List Bool) (x : α) : Prop :=
  x ∈ M.run p

/-- The *plain Kolmogorov complexity* `C_M(x)` of `x`: the length of a shortest program that
outputs `x`, or `⊤` if there is none [Sipser, Section 6.4][Sipser2013]. -/
noncomputable def ecomplexity (x : α) : ℕ∞ :=
  ⨅ (p : List Bool) (_ : M.Produces p x), (p.length : ℕ∞)

/-- The *time-bounded Kolmogorov complexity* `C_M^t(x)` of `x`: the length of a shortest program
that outputs `x` within `t` steps, or `⊤` if there is none
[Li and Vitányi, Chapter 7][LiVitanyi2019].
-/
noncomputable def etimeBoundedComplexity (t : ℕ) (x : α) : ℕ∞ :=
  ⨅ (p : List Bool) (_ : x ∈ (M.run p).runFor t), (p.length : ℕ∞)

/-- The plain complexity `C_M(x)` as a natural number. It is `0` for an object without a
description, so it is the plain complexity only when `M.ecomplexity x ≠ ⊤`
(`natCast_complexity`). -/
noncomputable def complexity (x : α) : ℕ :=
  (M.ecomplexity x).toNat

variable {M} {p : List Bool} {t : ℕ} {x y : α}

/-! ### Programs and their outputs -/

theorem produces_iff_exists_mem_runFor : M.Produces p x ↔ ∃ t, x ∈ (M.run p).runFor t :=
  Computation.mem_iff_exists_mem_runFor

theorem Produces.of_mem_runFor (h : x ∈ (M.run p).runFor t) : M.Produces p x :=
  Computation.mem_of_mem_runFor h

/-- Two outputs of the same program, at any two times, are equal. -/
theorem eq_of_mem_runFor {t₁ t₂ : ℕ} (hx : x ∈ (M.run p).runFor t₁)
    (hy : y ∈ (M.run p).runFor t₂) : x = y :=
  Computation.eq_of_mem_runFor hx hy

/-- A program describes at most one object. -/
theorem Produces.unique (hx : M.Produces p x) (hy : M.Produces p y) : x = y :=
  Computation.mem_unique hx hy

/-! ### Plain complexity -/

theorem ecomplexity_le_length (h : M.Produces p x) : M.ecomplexity x ≤ p.length :=
  iInf₂_le p h

/-- The complexity is below `r` exactly when a program shorter than `r` describes the object. -/
theorem ecomplexity_lt_iff {r : ℕ∞} :
    M.ecomplexity x < r ↔ ∃ p : List Bool, (p.length : ℕ∞) < r ∧ M.Produces p x := by
  simp only [ecomplexity, iInf_lt_iff, exists_prop]
  exact exists_congr fun _ => and_comm

/-- The complexity is below `k` exactly when a program of length below `k` describes the
object. -/
theorem ecomplexity_lt_natCast_iff {k : ℕ} :
    M.ecomplexity x < k ↔ ∃ p : List Bool, p.length < k ∧ M.Produces p x := by
  simp [ecomplexity_lt_iff, ENat.natCast_lt_natCast]

/-- **Threshold characterization.** The complexity is at most `k` exactly when a program of
length at most `k` describes the object. -/
theorem ecomplexity_le_natCast_iff {k : ℕ} :
    M.ecomplexity x ≤ k ↔ ∃ p : List Bool, p.length ≤ k ∧ M.Produces p x := by
  rw [← ENat.lt_add_one_iff (ENat.natCast_ne_top k), ← Nat.cast_succ,
    ecomplexity_lt_natCast_iff]
  simp

theorem ecomplexity_eq_top_iff : M.ecomplexity x = ⊤ ↔ ∀ p, ¬M.Produces p x := by
  simp [ecomplexity]

theorem ecomplexity_ne_top_iff : M.ecomplexity x ≠ ⊤ ↔ ∃ p, M.Produces p x := by
  simp [ecomplexity_eq_top_iff]

theorem natCast_complexity (h : M.ecomplexity x ≠ ⊤) : (M.complexity x : ℕ∞) = M.ecomplexity x :=
  ENat.natCast_toNat h

/-- A finite complexity is the length of a describing program. -/
theorem exists_length_eq_ecomplexity (h : M.ecomplexity x ≠ ⊤) :
    ∃ p, M.Produces p x ∧ (p.length : ℕ∞) = M.ecomplexity x := by
  obtain ⟨p, hp, hpx⟩ := ecomplexity_le_natCast_iff.mp (ENat.natCast_toNat h).ge
  refine ⟨p, hpx, le_antisymm ?_ (ecomplexity_le_length hpx)⟩
  exact (ENat.natCast_le_natCast.mpr hp).trans_eq (ENat.natCast_toNat h)

/-! ### Time-bounded complexity -/

theorem etimeBoundedComplexity_le_length (h : x ∈ (M.run p).runFor t) :
    M.etimeBoundedComplexity t x ≤ p.length :=
  iInf₂_le p h

theorem etimeBoundedComplexity_lt_iff {r : ℕ∞} :
    M.etimeBoundedComplexity t x < r ↔
      ∃ p : List Bool, (p.length : ℕ∞) < r ∧ x ∈ (M.run p).runFor t := by
  simp only [etimeBoundedComplexity, iInf_lt_iff, exists_prop]
  exact exists_congr fun _ => and_comm

theorem etimeBoundedComplexity_lt_natCast_iff {k : ℕ} :
    M.etimeBoundedComplexity t x < k ↔ ∃ p : List Bool, p.length < k ∧ x ∈ (M.run p).runFor t := by
  simp [etimeBoundedComplexity_lt_iff, ENat.natCast_lt_natCast]

/-- **Threshold characterization.** The time-bounded complexity `C_M^t(x)` is at most `k` exactly
when a program of length at most `k` outputs `x` within `t` steps. -/
theorem etimeBoundedComplexity_le_natCast_iff {k : ℕ} :
    M.etimeBoundedComplexity t x ≤ k ↔ ∃ p : List Bool, p.length ≤ k ∧ x ∈ (M.run p).runFor t := by
  rw [← ENat.lt_add_one_iff (ENat.natCast_ne_top k), ← Nat.cast_succ,
    etimeBoundedComplexity_lt_natCast_iff]
  simp

theorem etimeBoundedComplexity_eq_top_iff :
    M.etimeBoundedComplexity t x = ⊤ ↔ ∀ p, x ∉ (M.run p).runFor t := by
  simp [etimeBoundedComplexity]

/-- A finite time-bounded complexity is the length of a program outputting the object in time. -/
theorem exists_length_eq_etimeBoundedComplexity (h : M.etimeBoundedComplexity t x ≠ ⊤) :
    ∃ p, x ∈ (M.run p).runFor t ∧ (p.length : ℕ∞) = M.etimeBoundedComplexity t x := by
  obtain ⟨p, hp, hpx⟩ := etimeBoundedComplexity_le_natCast_iff.mp (ENat.natCast_toNat h).ge
  refine ⟨p, hpx, le_antisymm ?_ (etimeBoundedComplexity_le_length hpx)⟩
  exact (ENat.natCast_le_natCast.mpr hp).trans_eq (ENat.natCast_toNat h)

/-- **Monotonicity in the time bound.** More time cannot increase the time-bounded complexity. -/
theorem etimeBoundedComplexity_antitone (M : DescriptionMethod α) (x : α) :
    Antitone (M.etimeBoundedComplexity · x) := fun _ _ h =>
  le_iInf₂ fun _ hp => etimeBoundedComplexity_le_length (Computation.mem_runFor_of_le h hp)

theorem etimeBoundedComplexity_mono {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    M.etimeBoundedComplexity t₂ x ≤ M.etimeBoundedComplexity t₁ x :=
  M.etimeBoundedComplexity_antitone x h

/-- Dropping the time bound cannot increase the complexity. -/
theorem ecomplexity_le_etimeBoundedComplexity (M : DescriptionMethod α) (t : ℕ) (x : α) :
    M.ecomplexity x ≤ M.etimeBoundedComplexity t x :=
  le_iInf₂ fun _ hp => ecomplexity_le_length (.of_mem_runFor hp)

/-- A large enough time bound attains the plain complexity. -/
theorem exists_etimeBoundedComplexity_eq_ecomplexity (M : DescriptionMethod α) (x : α) :
    ∃ t, M.etimeBoundedComplexity t x = M.ecomplexity x := by
  by_cases h : M.ecomplexity x = ⊤
  · exact ⟨0, h ▸ top_le_iff.mp (h ▸ M.ecomplexity_le_etimeBoundedComplexity 0 x)⟩
  obtain ⟨p, hpx, hp⟩ := exists_length_eq_ecomplexity h
  obtain ⟨t, ht⟩ := produces_iff_exists_mem_runFor.mp hpx
  exact ⟨t, le_antisymm (hp ▸ etimeBoundedComplexity_le_length ht)
    (M.ecomplexity_le_etimeBoundedComplexity t x)⟩

/-- The plain complexity is the limit of the time-bounded complexities. -/
theorem iInf_etimeBoundedComplexity (M : DescriptionMethod α) (x : α) :
    ⨅ t, M.etimeBoundedComplexity t x = M.ecomplexity x := by
  obtain ⟨t, ht⟩ := M.exists_etimeBoundedComplexity_eq_ecomplexity x
  exact le_antisymm (ht ▸ iInf_le _ t) (le_iInf (M.ecomplexity_le_etimeBoundedComplexity · x))

/-! ### The literal description method -/

/-- The description method for binary strings in which every program prints itself, taking one
step per bit. -/
def literal : DescriptionMethod (List Bool) where
  run p := (Computation.pure p).thinkN p.length

/-- A literal program halts after exactly one step per bit. -/
theorem results_literal_run (p : List Bool) : (literal.run p).Results p p.length :=
  Computation.results_thinkN_pure p p.length

theorem mem_literal_runFor {p x : List Bool} :
    x ∈ (literal.run p).runFor t ↔ p.length ≤ t ∧ p = x := by
  rw [(results_literal_run p).mem_runFor_iff, and_comm, eq_comm]

theorem literal_produces {p x : List Bool} : literal.Produces p x ↔ p = x :=
  ⟨fun h => Computation.mem_unique (results_literal_run p).mem h,
    fun h => h ▸ (results_literal_run p).mem⟩

/-- Every string is its own shortest literal description. -/
@[simp]
theorem ecomplexity_literal (x : List Bool) : literal.ecomplexity x = x.length :=
  le_antisymm (ecomplexity_le_length (literal_produces.mpr rfl))
    (le_iInf₂ fun _ hp => (literal_produces.mp hp) ▸ le_rfl)

theorem etimeBoundedComplexity_literal {x : List Bool} (h : x.length ≤ t) :
    literal.etimeBoundedComplexity t x = x.length :=
  le_antisymm (etimeBoundedComplexity_le_length (mem_literal_runFor.mpr ⟨h, rfl⟩))
    ((ecomplexity_literal x).symm.trans_le (literal.ecomplexity_le_etimeBoundedComplexity t x))

theorem etimeBoundedComplexity_literal_eq_top {x : List Bool} (h : t < x.length) :
    literal.etimeBoundedComplexity t x = ⊤ :=
  etimeBoundedComplexity_eq_top_iff.mpr fun _ hp =>
    absurd ((mem_literal_runFor.mp hp).2 ▸ (mem_literal_runFor.mp hp).1) h.not_ge

/-! ### Mapping outputs -/

section Map

variable {β : Type*}

/-- Mapping a function over the outputs of a description method, taking no steps of its own. -/
def map (f : α → β) (M : DescriptionMethod α) : DescriptionMethod β where
  run p := (M.run p).map f

@[simp]
theorem runFor_map (f : α → β) (M : DescriptionMethod α) (p : List Bool) (t : ℕ) :
    ((M.map f).run p).runFor t = ((M.run p).runFor t).map f :=
  Computation.runFor_map f (M.run p) t

theorem mem_map_runFor_iff {f : α → β} {M : DescriptionMethod α} {p : List Bool} {t : ℕ} {y : β} :
    y ∈ ((M.map f).run p).runFor t ↔ ∃ x ∈ (M.run p).runFor t, f x = y := by
  rw [runFor_map, Option.mem_def, Option.map_eq_some_iff]
  rfl

@[simp]
theorem map_produces_iff {f : α → β} {M : DescriptionMethod α} {p : List Bool} {y : β} :
    (M.map f).Produces p y ↔ ∃ x, M.Produces p x ∧ f x = y := by
  simp only [produces_iff_exists_mem_runFor, mem_map_runFor_iff]
  exact ⟨fun ⟨t, x, hx, hy⟩ => ⟨x, ⟨t, hx⟩, hy⟩, fun ⟨x, ⟨t, hx⟩, hy⟩ => ⟨t, x, hx, hy⟩⟩

/-- Mapping `f` over the outputs does not increase complexity: `f x` has complexity under
`M.map f` at most that of `x` under `M`. -/
theorem ecomplexity_map_le (f : α → β) (M : DescriptionMethod α) (x : α) :
    (M.map f).ecomplexity (f x) ≤ M.ecomplexity x :=
  le_iInf₂ fun _ hp => ecomplexity_le_length (map_produces_iff.mpr ⟨x, hp, rfl⟩)

theorem etimeBoundedComplexity_map_le (f : α → β) (M : DescriptionMethod α) (t : ℕ) (x : α) :
    (M.map f).etimeBoundedComplexity t (f x) ≤ M.etimeBoundedComplexity t x :=
  le_iInf₂ fun _ hp => etimeBoundedComplexity_le_length (mem_map_runFor_iff.mpr ⟨x, hp, rfl⟩)

/-- Mapping an injective `f` over the outputs preserves complexity: `f x` has the same
complexity under `M.map f` as `x` under `M`. -/
theorem ecomplexity_map_eq_of_injective {f : α → β} (hf : Function.Injective f)
    (M : DescriptionMethod α) (x : α) :
    (M.map f).ecomplexity (f x) = M.ecomplexity x :=
  le_antisymm (M.ecomplexity_map_le f x) <| le_iInf₂ fun _ hp => by
    obtain ⟨x', hx', hfx⟩ := map_produces_iff.mp hp
    exact hf hfx ▸ ecomplexity_le_length hx'

theorem etimeBoundedComplexity_map_eq_of_injective {f : α → β} (hf : Function.Injective f)
    (M : DescriptionMethod α) (t : ℕ) (x : α) :
    (M.map f).etimeBoundedComplexity t (f x) = M.etimeBoundedComplexity t x :=
  le_antisymm (M.etimeBoundedComplexity_map_le f t x) <| le_iInf₂ fun _ hp => by
    obtain ⟨x', hx', hfx⟩ := mem_map_runFor_iff.mp hp
    exact hf hfx ▸ etimeBoundedComplexity_le_length hx'

end Map

end DescriptionMethod

end Cslib.Kolmogorov
