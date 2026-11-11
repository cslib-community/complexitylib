/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.CIKK.Amplification

/-! Checks of the reconstruction for the amplification `Amp(f) = (f^k)^GL` of Carmosino,
Impagliazzo, Kabanets and Kolokolova (Theorem 4.3): the queries that compute `Amp(f)`, the query
count of the reconstruction, and its learning guarantee for a single amplified function. -/

namespace CslibFrontierTests.CIKKAmplification

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.MachineLearning
  Cslib.MachineLearning.UniformLearning

/-! ### Computing `Amp(f)` with queries -/

/-- With `f x = x 0`, blocks `1` and `0` and mask `11`, the two queries compute the parity
`1 ⊕ 0 = 1`. -/
example : (glAmpQuery (n := 1) 2 ![true, false, true, true]).eval (fun x => x 0) = true := by
  decide

/-- The same value, through `eval_glAmpQuery`. -/
example (y : BitString (2 * 1 + 2)) :
    (glAmpQuery (n := 1) 2 y).eval (fun x => x 0) = glAmp (fun x => x 0) 2 y :=
  eval_glAmpQuery _ y

/-- Three blocks take at most three queries. -/
example {n : ℕ} (y : BitString (3 * n + 3)) : (glAmpQuery (n := n) 3 y).depth ≤ 3 :=
  depth_glAmpQuery_le y

/-! ### The reconstruction -/

variable {n k : ℕ} {Ω : Type*}

/-- A learner for `Amp(f)` making `q` queries gives a learner for `f` making `q k` queries. -/
example {A : QueryLearner (Fin (k * n + k)) Ω} {q : ℕ} (hA : A.QueriesAtMost q) (s m K : ℕ) :
    (ampLearner A s m K).QueriesAtMost (q * k) :=
  queriesAtMost_ampLearner hA s m K

/-- Theorem 4.3 for a single function: a learner for `glAmp f k` with error `1/2 - γ` gives a
learner for `f` with error `ε`, under the four parameter conditions. -/
example {s m K : ℕ} [NeZero k] [Fact (s ≤ k)] {A : QueryLearner (Fin (k * n + k)) Ω}
    {μ : PMF Ω} {f : BooleanFunction n} {γ ε p : ℝ}
    (hA : A.Learns μ {glAmp f k} (1 / 2 - γ) (1 - p)) (hp : p ≤ 1) (hγ : 0 < γ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hK : 0 < K) (hsize : (k : ℝ) ≤ 2 * (γ / 2) ^ 2 * ((2 ^ K - 1 : ℕ) : ℝ))
    (hsk : 2 * s ≤ k) (hs : 64 / ε * Real.log (512 / (ε * (γ / 2 ^ (K + 3)) ^ 2)) ≤ s)
    (hm : 16 / (γ / 2 ^ (K + 3)) * Real.log (8 / ε) ≤ m) :
    (ampLearner A s m K).Learns (ampSeed μ k s m K) {f} ε
      (1 - p * ((γ / 2 ^ (K + 3)) ^ 2 / 8)) :=
  learns_ampLearner (by rwa [Set.image_singleton]) hp hγ hε hε1 hK hsize hsk hs hm

end CslibFrontierTests.CIKKAmplification
