/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.CorrelatedSampling.Embeddability
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.StatisticalDistance

/-! # Local embeddings

Independent private samples embed exactly, and a common value known to both parties is embedded
by Lemma 5.2. A perfectly correlated pair embeds with error `0`, whereas a target requiring one
party to reproduce the other party's uniform input without communication is not locally embeddable
below error `1 / 2`.
-/

namespace ComplexityTests.Embeddability

open Cslib.Probability.CorrelatedSampling
open scoped Cslib.Probability.PMF

-- Lemma 5.4: independent private samples embed with error `0`.
example (P₀ : PMF (Bool × Bool)) (KS : Bool → PMF Bool) (KT : Bool → PMF Bool) :
    IsEmbeddable P₀
      (P₀.bind fun xy => (KS xy.1).bind fun s => (KT xy.2).map fun t => (xy, (s, t))) 0 :=
  isEmbeddable_bind_prod P₀ KS KT

/-- A perfectly correlated triple of bits `((b, b), b)`. -/
noncomputable def correlatedTriple : PMF ((Bool × Bool) × Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype Bool).map fun b => ((b, b), b)

-- Lemma 5.2 instantiated on `correlatedTriple`.
example :
    IsEmbeddable (correlatedTriple.map Prod.fst)
      (correlatedTriple.map fun z => (z.1, (z.2, z.2)))
      (2 * dist correlatedTriple
          (withKernel (correlatedTriple.map Prod.fst) fun xy => condX correlatedTriple xy.1) +
        2 * dist correlatedTriple
          (withKernel (correlatedTriple.map Prod.fst) fun xy => condY correlatedTriple xy.2)) :=
  isEmbeddable_diag correlatedTriple

-- A perfectly correlated pair embeds its marginal in `((b, b), (b, b))` with error `0`.
example :
    IsEmbeddable (correlatedTriple.map Prod.fst)
      ((correlatedTriple.map Prod.fst).bind fun xy =>
        ((PMF.pure xy.1).map fun s => (s, s)).map (xy, ·)) 0 := by
  have h := isEmbeddable_withKernel (correlatedTriple.map Prod.fst) PMF.pure PMF.pure
    (fun xy => PMF.pure xy.1)
  have hYX : withKernel (correlatedTriple.map Prod.fst) (fun xy => PMF.pure xy.2) =
      withKernel (correlatedTriple.map Prod.fst) (fun xy => PMF.pure xy.1) := by
    simp only [correlatedTriple, withKernel, PMF.map_comp, PMF.bind_map]
    rfl
  simpa [hYX] using h

/-- A uniform input bit for Alice and a trivial input for Bob. -/
noncomputable def aliceInput : PMF (Bool × Unit) :=
  Cslib.Probability.PMF.uniformOfFintype (Bool × Unit)

/-- Target law where Bob's output bit equals Alice's input bit. -/
noncomputable def bobGuessesAlice : PMF ((Bool × Unit) × (Unit × Bool)) :=
  aliceInput.bind fun xy => (PMF.pure ((), xy.1)).map (xy, ·)

-- Without communication, Bob cannot match a uniform bit held only by Alice below error `1 / 2`.
example {ε : ℝ} (hε : ε < 1 / 2) : ¬ IsEmbeddable aliceInput bobGuessesAlice ε := by
  rintro ⟨R, ρ, fA, fB, h⟩
  set q : PMF (Unit × Bool) := ρ.map fun r => ((), fB () r)
  have hmap : (aliceInput.bind fun xy => ρ.map fun r => (xy, (fA xy.1 r, fB xy.2 r))) =
      aliceInput.bind fun xy => q.map (xy, ·) := by
    congr 1
    funext xy
    exact (PMF.map_comp _ _ _).symm
  rw [hmap, bobGuessesAlice, Cslib.Probability.PMF.dist_bind_pair] at h
  have hsum : (∑ a : Bool × Unit, (aliceInput a).toReal * dist q (PMF.pure ((), a.1))) =
      2⁻¹ * (dist q (PMF.pure ((), true)) + dist q (PMF.pure ((), false))) := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp [aliceInput, Cslib.Probability.PMF.uniformOfFintype_apply]
    ring
  have htri : dist (PMF.pure ((), true)) (PMF.pure ((), false)) ≤
      dist q (PMF.pure ((), true)) + dist q (PMF.pure ((), false)) :=
    dist_triangle_left _ _ _
  have hpure : dist (PMF.pure ((), true)) (PMF.pure ((), false)) = 1 := by
    simp [Cslib.Probability.PMF.dist_eq, Fintype.sum_prod_type]
  linarith

end ComplexityTests.Embeddability
