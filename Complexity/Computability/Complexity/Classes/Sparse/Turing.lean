/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Complexity.Classes.Oracle
public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Complexity.Classes.Sparse
public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Foundations.Data.BitString.ShortMembers
import Complexity.Computability.Circuit.Boolean.Advice
import Complexity.Computability.Circuit.Boolean.PolynomialTime
import Complexity.Computability.Complexity.Classes.Oracle.ListOracle
import Complexity.Computability.Complexity.Classes.PH.KarpLipton
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Sparse Turing-hard sets

Polynomial time relative to a sparse oracle language `S` is in `P/poly`
(`Cslib.Complexity.PWithOracle_subset_PPolyOn`): on inputs of length `n` the oracle is asked only
words of length at most `q n` for a polynomial `q`, and the list of the members of `S` of length
at most `q n` (`Cslib.BitString.shortMembers`) has polynomial length because `S` is sparse. That
list is the advice; a finite list replaces the oracle in polynomial time
(`Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_listOracle_bool`), and hardwiring the
advice (`Cslib.Circuits.Boolean.PPoly.of_advice`) gives circuits of polynomial size. This is one
half of `P/poly = P^SPARSE`, which [Hemaspaandra and Ogihara, p. 22][HemaspaandraOgihara2002] cite
as well known, and whose bibliographic notes (p. 27) attribute it, through Berman and Hartmanis,
to Meyer.

Consequently, if `SAT` is polynomial-time Turing reducible to a sparse set, then `SAT` has circuits
of polynomial size and the Karp–Lipton theorem collapses the polynomial hierarchy to `Σ₂`
(`Cslib.Complexity.PH_eq_SigmaP_two_of_SAT_mem_PWithOracle`): if `NP` has a sparse
polynomial-time Turing-hard set, then `PH = NP^NP`
[Hemaspaandra and Ogihara, Theorem 1.16][HemaspaandraOgihara2002] [Karp and Lipton][KarpLipton1980].
The sparse set need not lie in `NP`.

## Main results

* `Cslib.Complexity.exists_length_shortMembers_le`,
  `Cslib.Complexity.exists_length_encList_shortMembers_le`: for a sparse language, the list of short
  members and its encoding have polynomial length.
* `Cslib.Complexity.PWithOracle_subset_PPolyOn`: `P^S ⊆ P/poly` for sparse `S`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_SAT_mem_PWithOracle`: a sparse Turing-hard set for `NP`
  collapses `PH` to `Σ₂`.

## References

* [L. A. Hemaspaandra, M. Ogihara, *The Complexity Theory Companion*][HemaspaandraOgihara2002]
* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
-/

@[expose] public section

namespace Cslib.Complexity

open Circuits Circuits.Boolean Turing.MultiTapeTM Cslib.Logic.PL BitString

variable {α : Type} {S : Set (List Bool)}

/-- **The census of a sparse language is polynomially bounded**: it has at most `c (n + 1) ^ d`
members of length at most `n`. -/
theorem exists_length_shortMembers_le (hS : S ∈ SPARSE encBits) :
    ∃ c d : ℕ, ∀ n, (shortMembers S n).length ≤ c * (n + 1) ^ d := by
  classical
  obtain ⟨c, d, hcard⟩ := exists_card_le_of_mem_SPARSE hS
  refine ⟨c, d, fun n => ?_⟩
  rw [length_shortMembers]
  exact hcard n _ fun w hw => by simpa [and_comm] using hw

/-- **Short members of a sparse language have a short listing**: the encoded list of the members
of length at most `n` has length at most `c (n + 1) ^ d`. -/
theorem exists_length_encList_shortMembers_le (hS : S ∈ SPARSE encBits) :
    ∃ c d : ℕ, ∀ n, (encList encBits (shortMembers S n)).length ≤ c * (n + 1) ^ d := by
  obtain ⟨c, d, hcensus⟩ := exists_length_shortMembers_le hS
  refine ⟨2 * c, d + 1, fun n => ?_⟩
  have hlen := hcensus n
  have hsum : ((shortMembers S n).map fun w => 2 * (encBits w).length + 1).sum ≤
      (shortMembers S n).length * (2 * n + 1) := by
    have h := List.sum_le_length_nsmul ((shortMembers S n).map fun w => 2 * (encBits w).length + 1)
      (2 * n + 1) fun x hx => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
        have := (mem_shortMembers.mp hw).2
        simp only [encBits_apply]
        omega
    simpa only [List.length_map, smul_eq_mul] using h
  rw [length_encList]
  calc _ ≤ (shortMembers S n).length * (2 * n + 1) := hsum
    _ ≤ c * (n + 1) ^ d * (2 * (n + 1)) := Nat.mul_le_mul hlen (by omega)
    _ = 2 * c * (n + 1) ^ (d + 1) := by ring

/-- **Polynomial time relative to a sparse oracle is in `P/poly`.** The advice at length `n` lists
the members of `S` no longer than the oracle words the computation may ask. -/
theorem PWithOracle_subset_PPolyOn (hS : S ∈ SPARSE encBits) (enc : α ↪ List Bool) :
    PWithOracle S enc ⊆ PPolyOn enc := by
  rintro L ⟨f, hf, hL⟩
  obtain ⟨F, q, hF, hFS⟩ := hf.exists_listOracle_bool
  have hF' : ComputableInPolyTime (fun x : List (List Bool) × α => F (x.2, x.1))
      (encPair (encList encBits) enc) encBool :=
    hF.comp (g := fun x : List (List Bool) × α => (x.2, x.1))
      ((ComputableInPolyTime.snd _ _).prod (.fst _ _))
  obtain ⟨M, hM, hFM⟩ := PPoly.exists_of_polyTime hF'
  obtain ⟨c, d, hadv⟩ := exists_length_encList_shortMembers_le hS
  let adv : ℕ → List Bool := fun n => encList encBits (shortMembers S (q.eval n))
  have hadvPoly : PolynomiallyBounded fun n => (adv n).length := by
    refine PolynomiallyBounded.mono_of_le (g := fun n => c * (q.eval n + 1) ^ d) (by fun_prop)
      fun n => hadv _
  let L' : Language Bool := {x : List Bool | frame (adv x.length) ++ x ∈ M}
  refine ⟨L', PPoly.of_advice hM adv hadvPoly (fun _ => Iff.rfl), fun a => ?_⟩
  change a ∈ L ↔ frame (adv (enc a).length) ++ enc a ∈ M
  have hFM' := hFM (shortMembers S (q.eval (enc a).length), a)
  rw [encPair_apply] at hFM'
  rw [hL a, ← hFM', hFS a _ fun w hw => by simp only [mem_shortMembers, hw, and_true]]

/-- **A sparse Turing-hard set for `NP` collapses `PH` to `Σ₂`**: if `SAT` is decided in
polynomial time relative to a sparse oracle language, then `SAT` has circuits of polynomial size,
and the Karp–Lipton theorem applies [Hemaspaandra and Ogihara, Theorem 1.16]
[HemaspaandraOgihara2002]. -/
theorem PH_eq_SigmaP_two_of_SAT_mem_PWithOracle (hS : S ∈ SPARSE encBits)
    (hSAT : SAT ∈ PWithOracle S encCNF) (enc : α ↪ List Bool) : PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_SAT (PWithOracle_subset_PPolyOn hS encCNF hSAT)

end Cslib.Complexity
