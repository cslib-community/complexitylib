/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.BoundedDegreePartition
import Mathlib.Data.List.Nodup

/-!
# Ordered complete class-size vectors

For fixed q, enumerate all (v+1)^q vectors in class-label order. The first coordinate is the
outer ascending loop, the last varies fastest. The original graph size varies; q is not an input.
This is the actual polynomial traversal of [ChenJiangZhu2027], Theorem 7.3 (PDF p.25).
## Main results

* `mem_vectors`, `nodup_vectors`, `length_vectors`: complete unique ordered vector coverage.
* `vectors_polytime`: actual fixed-q polynomial materialization with binary output.

-/

public section

namespace Cslib.Logic.PL.DegreePartition.SizeVectors

open Turing.MultiTapeTM

/-- Actual ordered product traversal, with no supplied vector list. -/
@[expose] def vectors : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | q + 1, n => (List.range (n + 1)).flatMap fun k => (vectors q n).map (k :: ·)

/-- The exact number of emitted vectors is polynomial in v for each fixed q. -/
theorem length_vectors (q n : ℕ) : (vectors q n).length = (n + 1) ^ q := by
  induction q with
  | zero => rfl
  | succ q ih => simp [vectors, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

/-- Every bounded original-label size vector occurs, including vectors with zero coordinates. -/
theorem mem_vectors (q n : ℕ) (v : List ℕ) :
    v ∈ vectors q n ↔ v.length = q ∧ ∀ k ∈ v, k ≤ n := by
  induction q generalizing v with
  | zero =>
    simp only [vectors, List.mem_singleton]
    constructor
    · intro h; subst v; simp
    · rintro ⟨h, _⟩; exact List.length_eq_zero_iff.mp h
  | succ q ih =>
    cases v with
    | nil => simp [vectors]
    | cons h t =>
      simp only [vectors, List.mem_flatMap, List.mem_range, List.mem_map, List.cons.injEq]
      constructor
      · rintro ⟨a, ha, tail, ht, rfl, rfl⟩
        obtain ⟨hlen, hall⟩ := (ih tail).mp ht
        refine ⟨by simp [hlen], ?_⟩
        intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · omega
        · exact hall k hk
      · rintro ⟨hlen, hall⟩
        refine ⟨h, by have := hall h (by simp); omega, t, ?_, rfl, rfl⟩
        exact (ih t).mpr ⟨by simpa using hlen, fun k hk => hall k (List.mem_cons_of_mem _ hk)⟩

/-- Label vectors occur exactly once; the traversal introduces no coefficient multiplicity. -/
theorem nodup_vectors (q n : ℕ) : (vectors q n).Nodup := by
  induction q with
  | zero => simp [vectors]
  | succ q ih =>
    rw [vectors, List.nodup_flatMap]
    constructor
    · intro k _
      exact ih.map (fun _ _ h => (List.cons.inj h).2)
    · have hPairs : (List.range (n + 1)).Pairwise (fun a b => a ≠ b) := List.nodup_range
      apply hPairs.imp
      intro a b hab
      apply List.disjoint_left.mpr
      intro v ha hb
      obtain ⟨ta, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨tb, _, he⟩ := List.mem_map.mp hb
      exact hab (List.cons.inj he).1.symm

/-- Actual vector materialization is binary polynomial time for fixed q. Its polynomial degree
may depend on q; no uniform polynomial claim for growing label count is made. -/
@[fun_prop] theorem vectors_polytime (q : ℕ) : ComputableInPolyTime (vectors q) encUnary
    (encList (encList encNat)) := by
  induction q with
  | zero => exact .const [[]]
  | succ q ih =>
    have hr : ComputableInPolyTime (fun n : ℕ => List.range (n + 1)) encUnary
        (encList encUnary) := by fun_prop
    change ComputableInPolyTime (fun n => (List.range (n + 1)).flatMap fun k =>
      (vectors q n).map (k :: ·)) _ _
    apply ComputableInPolyTime.flatMapWithInput hr
    have ht := ih.comp (ComputableInPolyTime.fst encUnary encUnary)
    apply ComputableInPolyTime.mapWithInput ht
    have hh := ComputableInPolyTime.unary_to_binary.comp
      ((ComputableInPolyTime.snd encUnary encUnary).comp
        (ComputableInPolyTime.fst (encPair encUnary encUnary) (encList encNat)))
    exact ComputableInPolyTime.cons' hh (ComputableInPolyTime.snd _ _)

end Cslib.Logic.PL.DegreePartition.SizeVectors
