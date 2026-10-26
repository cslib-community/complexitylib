/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Fin
public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.OfFn

/-!
# Count-Min sketches for weighted insertion streams

An update `(x, c)` adds the natural-number weight `c` to one bucket in each hash row. The
counter table is a vector of vectors, so updates materialize a finite table instead of retaining
a chain of functional updates. A point query takes the minimum of the counters addressed by
the queried item. It never underestimates the true frequency.

The exact bucket invariant identifies this executable update-and-fold algorithm with sums of
stream weights. Tables built with the same hashes merge by entrywise addition. Every counter is
bounded by the total inserted weight. These are semantic and numerical guarantees; this module
does not assign machine running times to Lean operations or certify their heap consumption.

## Main definitions

* `Cslib.CountMin.frequency`, `Cslib.CountMin.mass`: weighted frequency and total stream mass.
* `Cslib.CountMin.bucket`, `Cslib.CountMin.noise`: exact bucket and collision sums.
* `Cslib.CountMin.Table`, `Cslib.CountMin.update`, `Cslib.CountMin.run`: stored counters and
  the executable streaming algorithm.
* `Cslib.CountMin.estimate`: the minimum of a nonempty collection of hash rows.
* `Cslib.CountMin.merge`: entrywise addition of tables using the same hashes.

## Main results

* `Cslib.CountMin.bucket_hash_eq_frequency_add_noise`: a queried counter is frequency plus noise.
* `Cslib.CountMin.run_get`: every stored counter equals its bucket sum.
* `Cslib.CountMin.frequency_le_estimate_run`: no underestimation.
* `Cslib.CountMin.run_get_le_mass`: each counter is at most the total stream weight.
* `Cslib.CountMin.run_append`: concatenation of streams agrees with merging their tables.

## References

* [G. Cormode, S. Muthukrishnan, *An Improved Data Stream Summary: The Count-Min Sketch and its
  Applications*, Sections 3 and 4.1][CormodeMuthukrishnan2005]
-/

@[expose] public section

namespace Cslib.CountMin

variable {X : Type*} {d w : ℕ}

/-- Total weight inserted by a stream. -/
def mass (s : List (X × ℕ)) : ℕ := (s.map Prod.snd).sum

/-- Total weight inserted at the queried item. -/
def frequency [DecidableEq X] (s : List (X × ℕ)) (x : X) : ℕ :=
  (s.map fun u => if u.1 = x then u.2 else 0).sum

/-- The weight in one bucket of a hash row. -/
def bucket (h : X → Fin w) (s : List (X × ℕ)) (b : Fin w) : ℕ :=
  (s.map fun u => if h u.1 = b then u.2 else 0).sum

/-- Weight contributed by other items colliding with the query in one hash row. -/
def noise [DecidableEq X] (h : X → Fin w) (s : List (X × ℕ)) (x : X) : ℕ :=
  (s.map fun u => if u.1 ≠ x ∧ h u.1 = h x then u.2 else 0).sum

@[simp] theorem mass_nil : mass ([] : List (X × ℕ)) = 0 := rfl

@[simp] theorem mass_cons (u : X × ℕ) (s : List (X × ℕ)) :
    mass (u :: s) = u.2 + mass s := by simp [mass]

@[simp] theorem frequency_nil [DecidableEq X] (x : X) : frequency [] x = 0 := rfl

@[simp] theorem frequency_cons [DecidableEq X] (u : X × ℕ) (s : List (X × ℕ)) (x : X) :
    frequency (u :: s) x = (if u.1 = x then u.2 else 0) + frequency s x := by
  simp [frequency]

@[simp] theorem bucket_nil (h : X → Fin w) (b : Fin w) : bucket h [] b = 0 := rfl

@[simp] theorem bucket_cons (h : X → Fin w) (u : X × ℕ) (s : List (X × ℕ)) (b : Fin w) :
    bucket h (u :: s) b = (if h u.1 = b then u.2 else 0) + bucket h s b := by
  simp [bucket]

@[simp] theorem noise_nil [DecidableEq X] (h : X → Fin w) (x : X) : noise h [] x = 0 := rfl

@[simp] theorem noise_cons [DecidableEq X] (h : X → Fin w) (u : X × ℕ)
    (s : List (X × ℕ)) (x : X) :
    noise h (u :: s) x = (if u.1 ≠ x ∧ h u.1 = h x then u.2 else 0) + noise h s x := by
  simp [noise]

@[simp] theorem mass_append (s t : List (X × ℕ)) : mass (s ++ t) = mass s + mass t := by
  simp [mass]

@[simp] theorem frequency_append [DecidableEq X] (s t : List (X × ℕ)) (x : X) :
    frequency (s ++ t) x = frequency s x + frequency t x := by
  simp [frequency]

@[simp] theorem bucket_append (h : X → Fin w) (s t : List (X × ℕ)) (b : Fin w) :
    bucket h (s ++ t) b = bucket h s b + bucket h t b := by
  simp [bucket]

@[simp] theorem noise_append [DecidableEq X] (h : X → Fin w) (s t : List (X × ℕ)) (x : X) :
    noise h (s ++ t) x = noise h s x + noise h t x := by
  simp [noise]

/-- A queried bucket consists of the query's frequency and nonnegative collision noise. -/
theorem bucket_hash_eq_frequency_add_noise [DecidableEq X] (h : X → Fin w)
    (s : List (X × ℕ)) (x : X) : bucket h s (h x) = frequency s x + noise h s x := by
  induction s with
  | nil => simp
  | cons u s ih =>
    by_cases hx : u.1 = x
    · simp [hx, ih, Nat.add_assoc]
    · by_cases hh : h u.1 = h x <;> simp [hx, hh, ih, Nat.add_left_comm]

/-- A frequency cannot exceed the total inserted weight. -/
theorem frequency_le_mass [DecidableEq X] (s : List (X × ℕ)) (x : X) :
    frequency s x ≤ mass s := by
  induction s with
  | nil => simp
  | cons u s ih =>
    simp only [frequency_cons, mass_cons]
    split_ifs <;> omega

/-- Every bucket is bounded by the total inserted weight. -/
theorem bucket_le_mass (h : X → Fin w) (s : List (X × ℕ)) (b : Fin w) :
    bucket h s b ≤ mass s := by
  induction s with
  | nil => simp
  | cons u s ih =>
    simp only [bucket_cons, mass_cons]
    split_ifs <;> omega

/-- Collision noise is bounded by the total inserted weight. -/
theorem noise_le_mass [DecidableEq X] (h : X → Fin w) (s : List (X × ℕ)) (x : X) :
    noise h s x ≤ mass s :=
  (Nat.le_add_left _ _).trans ((bucket_hash_eq_frequency_add_noise h s x) ▸
    bucket_le_mass h s (h x))

/-- A stored array of `d` rows of `w` natural-number counters. -/
abbrev Table (d w : ℕ) := Vector (Vector ℕ w) d

/-- The initial table has every counter zero. -/
def zero (d w : ℕ) : Table d w := Vector.replicate d (Vector.replicate w 0)

/-- Read one stored counter. -/
def get (t : Table d w) (r : Fin d) (b : Fin w) : ℕ := t[r.val][b.val]

/-- Add the update weight to the addressed counter in every row. -/
def update (h : Fin d → X → Fin w) (t : Table d w) (u : X × ℕ) : Table d w :=
  Vector.ofFn fun r => (t[r.val]).set (h r u.1).val (get t r (h r u.1) + u.2)

/-- Process the stream in order, keeping only the current counter table. -/
def run (h : Fin d → X → Fin w) (s : List (X × ℕ)) : Table d w :=
  s.foldl (update h) (zero d w)

/-- Merge tables formed with the same hash bank by adding corresponding counters. -/
def merge (a b : Table d w) : Table d w :=
  Vector.ofFn fun r => Vector.ofFn fun c => get a r c + get b r c

/-- Take the minimum of the counters addressed by a query, using at least one row. -/
def estimate [NeZero d] (h : Fin d → X → Fin w) (t : Table d w) (x : X) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty fun r => get t r (h r x)

@[simp] theorem get_zero (r : Fin d) (b : Fin w) : get (zero d w) r b = 0 := by
  simp [get, zero]

@[simp] theorem get_merge (a c : Table d w) (r : Fin d) (b : Fin w) :
    get (merge a c) r b = get a r b + get c r b := by
  simp [get, merge]

/-- An update changes just its addressed bucket in each row. -/
theorem get_update (h : Fin d → X → Fin w) (t : Table d w) (u : X × ℕ)
    (r : Fin d) (b : Fin w) :
    get (update h t u) r b = get t r b + if h r u.1 = b then u.2 else 0 := by
  simp only [get, update, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases hb : h r u.1 = b
  · simp [hb]
  · have hv : (h r u.1).val ≠ b.val := fun hval => hb (Fin.ext hval)
    simp [hb, hv]

/-- An arbitrary starting table gains exactly the stream's bucket weights. -/
theorem foldl_update_get (h : Fin d → X → Fin w) (s : List (X × ℕ))
    (t : Table d w) (r : Fin d) (b : Fin w) :
    get (s.foldl (update h) t) r b = get t r b + bucket (h r) s b := by
  induction s generalizing t with
  | nil => simp
  | cons u s ih =>
    rw [List.foldl_cons, ih, get_update, bucket_cons, Nat.add_assoc]

/-- Every stored counter equals its exact weighted bucket sum. -/
theorem run_get (h : Fin d → X → Fin w) (s : List (X × ℕ)) (r : Fin d) (b : Fin w) :
    get (run h s) r b = bucket (h r) s b := by
  rw [run, foldl_update_get, get_zero, Nat.zero_add]

/-- Stored counters never exceed the total stream weight. -/
theorem run_get_le_mass (h : Fin d → X → Fin w) (s : List (X × ℕ))
    (r : Fin d) (b : Fin w) : get (run h s) r b ≤ mass s := by
  rw [run_get]
  exact bucket_le_mass (h r) s b

/-- A query is no larger than any of its addressed row counters. -/
theorem estimate_le_get [NeZero d] (h : Fin d → X → Fin w) (t : Table d w)
    (x : X) (r : Fin d) : estimate h t x ≤ get t r (h r x) :=
  Finset.inf'_le _ (Finset.mem_univ r)

/-- A query on a processed stream is bounded by the exact bucket sum in every row. -/
theorem estimate_run_le_bucket [NeZero d] (h : Fin d → X → Fin w) (s : List (X × ℕ))
    (x : X) (r : Fin d) : estimate h (run h s) x ≤ bucket (h r) s (h r x) := by
  rw [← run_get h s r (h r x)]
  exact estimate_le_get h (run h s) x r

/-- A Count-Min point query never underestimates the inserted frequency. -/
theorem frequency_le_estimate_run [DecidableEq X] [NeZero d] (h : Fin d → X → Fin w)
    (s : List (X × ℕ)) (x : X) : frequency s x ≤ estimate h (run h s) x := by
  apply Finset.le_inf'
  intro r _
  rw [run_get, bucket_hash_eq_frequency_add_noise]
  exact Nat.le_add_right _ _

/-- Concatenating streams agrees exactly with merging tables using the same hash bank. -/
theorem run_append (h : Fin d → X → Fin w) (s t : List (X × ℕ)) :
    run h (s ++ t) = merge (run h s) (run h t) := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro b hb
  change get (run h (s ++ t)) ⟨r, hr⟩ ⟨b, hb⟩ =
    get (merge (run h s) (run h t)) ⟨r, hr⟩ ⟨b, hb⟩
  rw [get_merge, run_get, run_get, run_get, bucket_append]

/-- Appending one update performs one update on the current table. -/
theorem run_append_singleton (h : Fin d → X → Fin w) (s : List (X × ℕ)) (u : X × ℕ) :
    run h (s ++ [u]) = update h (run h s) u := by
  simp [run, List.foldl_append]

end Cslib.CountMin
