/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.Module
import CslibFrontier.Probability.Uniform

/-!
# Module-LWE with a retained public seed

`ModuleLWE.seededSampleLaw` retains the seed used to expand the matrix, and draws the secret
and error independently from their supplied laws. Its ideal comparison is the existing product
of the seed law with a uniform target. A distinguisher, including the output law of a quantum
circuit, consumes either distribution by `PMF.bind`; there is no new game or hardness notion.

The seed may itself include public randomness. For example, a seed together with an independent
uniform row, expanded to that row followed by a square seeded matrix or its transpose, gives the
augmented Hashed Module-LWE distribution of [Almeida et al.][AlmeidaEtAl2024Kyber], §4.1,
Figure 2 (p. 9). The checked client uses the existing ML-KEM CBD samplers with separate secret
and error widths. The construction here does not implement SHAKE expansion,
certify sampling time, assert hardness, or prove a quantum security reduction.

## Main definitions

* `Cslib.Crypto.ModuleLWE.seededSampleLaw`: joint public seed and noisy target law.

## Main results

* `Cslib.Crypto.ModuleLWE.seededSampleLaw_map_fst`: the public seed has its original law.
* `Cslib.Crypto.ModuleLWE.seededSampleLaw_uniform_error`: uniform error gives the ideal product.
* `Cslib.Crypto.ModuleLWE.seededSampleLaw_bind_eq_realGame`: uniform matrices recover the existing
  real game, for arbitrary secret and error laws.

## References

* [J. B. Almeida et al., *Formally verifying Kyber, Episode V*][AlmeidaEtAl2024Kyber],
  §4.1, Figure 2 (pp. 8–9). The laws here are distributional infrastructure. That source's
  security proof is classical; no hardness assumption or security reduction is transferred here.
-/

public section

namespace Cslib.Crypto.ModuleLWE

open Probability

variable {Seed : Type} {m d n q : ℕ}

/-- Joint law of a public seed and `expand seed · s + e`, with independent secret and error.
The seed law and the two noise laws need not be uniform or efficiently sampleable. -/
@[expose] noncomputable def seededSampleLaw (seedLaw : PMF Seed)
    (expand : Seed → Matrix (Fin m) (Fin d) (Fin n → ZMod q))
    (secretLaw : PMF (Fin d → Fin n → ZMod q))
    (errorLaw : PMF (Fin m → Fin n → ZMod q)) : PMF (Seed × (Fin m → Fin n → ZMod q)) := do
  let seed ← seedLaw
  let secret ← secretLaw
  let error ← errorLaw
  return (seed, sample (expand seed) secret error)

/-- Sampling a target does not change the retained public seed's marginal. -/
@[simp] theorem seededSampleLaw_map_fst (seedLaw : PMF Seed)
    (expand : Seed → Matrix (Fin m) (Fin d) (Fin n → ZMod q))
    (secretLaw : PMF (Fin d → Fin n → ZMod q))
    (errorLaw : PMF (Fin m → Fin n → ZMod q)) :
    (seededSampleLaw seedLaw expand secretLaw errorLaw).map Prod.fst = seedLaw := by
  simp [seededSampleLaw, PMF.map_bind, PMF.pure_map, PMF.bind_const, PMF.bind_pure]

/-- Uniform error makes the target uniform and independent of the public seed, regardless of
the deterministic expander or the secret distribution. -/
theorem seededSampleLaw_uniform_error [NeZero q] (seedLaw : PMF Seed)
    (expand : Seed → Matrix (Fin m) (Fin d) (Fin n → ZMod q))
    (secretLaw : PMF (Fin d → Fin n → ZMod q)) :
    seededSampleLaw seedLaw expand secretLaw (PMF.uniformOfFintype _) =
      (do
        let seed ← seedLaw
        let target ← PMF.uniformOfFintype (Fin m → Fin n → ZMod q)
        return (seed, target)) := by
  simp only [seededSampleLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  congr 1 with seed
  have hmask (secret : Fin d → Fin n → ZMod q) :
      (PMF.uniformOfFintype (Fin m → Fin n → ZMod q)).bind
          (fun error => PMF.pure (seed, sample (expand seed) secret error)) =
        (PMF.uniformOfFintype (Fin m → Fin n → ZMod q)).bind
          (fun target => PMF.pure (seed, target)) := by
    simpa only [sample] using
      PMF.uniformOfFintype_bind_add_left (moduleSISMap (expand seed) secret)
        (fun target => PMF.pure (seed, target))
  simp only [hmask, PMF.bind_const]

/-- Identity expansion of a uniform matrix gives the existing typed real Module-LWE game.
The equality concerns distributions and asserts no efficiency of the distinguisher. -/
theorem seededSampleLaw_bind_eq_realGame [NeZero q]
    (secretLaw : PMF (Fin d → Fin n → ZMod q))
    (errorLaw : PMF (Fin m → Fin n → ZMod q))
    (D : Matrix (Fin m) (Fin d) (Fin n → ZMod q) →
      (Fin m → Fin n → ZMod q) → ProbComp Bool) :
    (seededSampleLaw (PMF.uniformOfFintype _) id secretLaw errorLaw).bind
        (fun (A, b) => ProbComp.eval (D A b)) = realGame secretLaw errorLaw D := by
  rw [realGame_eq_uniform_bind]
  simp [seededSampleLaw, PMF.bind_bind, PMF.pure_bind]

end Cslib.Crypto.ModuleLWE
