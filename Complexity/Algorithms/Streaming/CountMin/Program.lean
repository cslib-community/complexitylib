/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Streaming.CountMin.Probability
public import Complexity.Languages.Probabilistic.Vector
import Complexity.Probability.PMF.Uniform

/-!
# Count-Min as a probabilistic program

`sampleSketch` independently repeats a caller-supplied seed sampler and processes a weighted
insertion stream with the resulting hash rows. Its output retains both the row seeds and the
materialized counter table, so later queries use the same hashes. `sampleQuery` constructs a
sketch and returns one point query. The hash family is supplied separately and must remain fixed
between construction and queries.

When one seed is exactly uniform, repeated calls give the uniform distribution on row-seed
tuples. This identifies the output law of the program with the deterministic construction
analyzed in `CountMin.Probability`, giving its fixed-query failure bound. The stream and query
are fixed before the seeds are sampled. No running-time or representation cost is asserted for
the supplied sampler, hash function, or program.

## Main definitions

* `Cslib.CountMin.Sketch`: row seeds together with the stored counter table.
* `Cslib.CountMin.buildSketch`, `Cslib.CountMin.Sketch.query`: deterministic construction and
  point queries retaining the construction's hashes.
* `Cslib.CountMin.sampleSketch`, `Cslib.CountMin.sampleQuery`: probabilistic construction and
  a fixed point query.

## Main results

* `Cslib.CountMin.eval_sampleSketch`, `Cslib.CountMin.eval_sampleQuery`: output laws under a
  uniform seed sampler.
* `Cslib.CountMin.frequency_le_of_mem_support_sampleQuery`: every possible query result avoids
  underestimation, without any uniformity assumption.
* `Cslib.CountMin.sampleQuery_error_le_inv_two_pow`: failure probability at most `2⁻ᵈ` when
  `2 ≤ w * ε`, for a two-universal hash family and a uniform seed sampler.

## References

* [G. Cormode, S. Muthukrishnan, *An Improved Data Stream Summary: The Count-Min Sketch
  and its Applications*][CormodeMuthukrishnan2005], Section 4.1, Theorem 1.
-/

@[expose] public section

namespace Cslib.CountMin

open Probability

variable {X : Type*} {Seed : Type} {d w : ℕ}

/-- A stored sketch retains its sampled row seeds and materialized counter table. -/
structure Sketch (Seed : Type) (d w : ℕ) where
  /-- One seed for each hash row. -/
  seeds : Fin d → Seed
  /-- The counters updated using these row seeds. -/
  table : Table d w

/-- Process a stream with a fixed row-seed tuple, retaining it for later queries. -/
def buildSketch (hash : Seed → X → Fin w) (s : List (X × ℕ))
    (seeds : Fin d → Seed) : Sketch Seed d w :=
  ⟨seeds, run (fun r => hash (seeds r)) s⟩

/-- Query the stored table using the same hash family as in its construction. -/
def Sketch.query [NeZero d] (sketch : Sketch Seed d w) (hash : Seed → X → Fin w)
    (x : X) : ℕ :=
  estimate (fun r => hash (sketch.seeds r)) sketch.table x

/-- Draw independent row seeds and build the stored sketch for the supplied stream. -/
def sampleSketch (sampleSeed : ProbComp Seed) (hash : Seed → X → Fin w)
    (s : List (X × ℕ)) : ProbComp (Sketch Seed d w) :=
  buildSketch hash s <$> OracleComp.replicateFin d sampleSeed

/-- Build a sketch and return its estimate for one fixed point query. -/
def sampleQuery [NeZero d] (sampleSeed : ProbComp Seed) (hash : Seed → X → Fin w)
    (s : List (X × ℕ)) (x : X) : ProbComp ℕ :=
  (fun sketch => sketch.query hash x) <$> sampleSketch (d := d) sampleSeed hash s

/-- A uniform seed sampler gives the deterministic construction a uniform row-seed tuple. -/
theorem eval_sampleSketch [Fintype Seed] [Nonempty Seed] (sampleSeed : ProbComp Seed)
    (hs : ProbComp.eval sampleSeed = PMF.uniformOfFintype Seed)
    (hash : Seed → X → Fin w) (s : List (X × ℕ)) :
    ProbComp.eval (sampleSketch (d := d) sampleSeed hash s) =
      (PMF.uniformOfFintype (Fin d → Seed)).map (buildSketch hash s) := by
  simp only [sampleSketch, ProbComp.eval_map, ProbComp.eval_replicateFin, hs,
    PMF.pi_uniformOfFintype]

/-- The point-query program has the law of querying a uniformly sampled hash bank. -/
theorem eval_sampleQuery [Fintype Seed] [Nonempty Seed] [NeZero d]
    (sampleSeed : ProbComp Seed) (hs : ProbComp.eval sampleSeed = PMF.uniformOfFintype Seed)
    (hash : Seed → X → Fin w) (s : List (X × ℕ)) (x : X) :
    ProbComp.eval (sampleQuery (d := d) sampleSeed hash s x) =
      (PMF.uniformOfFintype (Fin d → Seed)).map (fun seeds =>
        estimate (fun r => hash (seeds r)) (run (fun r => hash (seeds r)) s) x) := by
  rw [sampleQuery, ProbComp.eval_map, eval_sampleSketch sampleSeed hs, PMF.map_comp]
  rfl

/-- Every possible output of the point-query program is at least the true frequency. -/
theorem frequency_le_of_mem_support_sampleQuery [DecidableEq X] [NeZero d]
    (sampleSeed : ProbComp Seed) (hash : Seed → X → Fin w) (s : List (X × ℕ)) (x : X)
    {answer : ℕ} (ha : answer ∈ (ProbComp.eval
      (sampleQuery (d := d) sampleSeed hash s x)).support) : frequency s x ≤ answer := by
  rw [sampleQuery, ProbComp.eval_map, PMF.mem_support_map_iff] at ha
  rcases ha with ⟨sketch, hsketch, rfl⟩
  rw [sampleSketch, ProbComp.eval_map, PMF.mem_support_map_iff] at hsketch
  rcases hsketch with ⟨seeds, _, rfl⟩
  exact frequency_le_estimate_run (fun r => hash (seeds r)) s x

/-- The actual point-query program has failure probability at most `2⁻ᵈ` with at least
`2 / ε` buckets and independently uniform seeds for a two-universal hash family. -/
theorem sampleQuery_error_le_inv_two_pow [DecidableEq X] [Fintype Seed] [Nonempty Seed]
    [NeZero d] [NeZero w] (sampleSeed : ProbComp Seed)
    (hs : ProbComp.eval sampleSeed = PMF.uniformOfFintype Seed)
    (hash : Seed → X → Fin w) (hh : IsTwoUniversal (PMF.uniformOfFintype Seed) hash)
    (s : List (X × ℕ)) (x : X) {ε : ℝ} (hε : 0 < ε) (hw : 2 ≤ (w : ℝ) * ε) :
    ((ProbComp.eval (sampleQuery (d := d) sampleSeed hash s x)).toOuterMeasure
      {answer | (frequency s x : ℝ) + ε * mass s < (answer : ℝ)}).toReal ≤
        (2 ^ d : ℝ)⁻¹ := by
  classical
  rw [eval_sampleQuery sampleSeed hs, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFintype_toReal]
  simpa only [Finset.nnratCast_dens, Set.mem_preimage, Set.mem_ofPred_eq] using
    dens_estimate_error_le_inv_two_pow (d := d) hash hh s x hε hw

end Cslib.CountMin
