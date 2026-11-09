/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.KWiseIndependent
public import CslibFrontier.Probability.KWiseIndependent.Trinomial
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# Polynomial-size `k`-wise independent sample spaces for MAX-E`k`-SAT

For each fixed `k`, evaluating a uniformly random polynomial of degree `< k` over the explicit
binary field `Cslib.TrinomialField t` at the positions of the variables, and keeping one bit of
each value, gives `k`-wise independent uniform bits
(`Cslib.Probability.isKWiseIndependentHash_trinomialPolyHash`). With the field of the smallest
admissible size for `n` variables there are at most `(2 n + 4) ^ (3 k)` seeds. So for every list
`vs` of `n` variables there is a list of at most `(2 n + 4) ^ (3 k)` assignments, depending only on
`vs`, one of which falsifies at most `2 ^ -k` of the clauses of every formula on these variables
with at least `k` distinct literals per clause
(`Cslib.Logic.PL.exists_assignments_two_pow_mul_countUnsat_le`)
[Alon and Spencer, Section 16.2][AlonSpencer2016]. For fixed `k` this is polynomially many
assignments; searching them deterministically matches the random-assignment bound for
MAX-E`k`-SAT. The polynomial-time certificate for the field arithmetic is not provided here; for
`k ≤ 3` the search over the smaller Boolean affine space is certified in
`CslibFrontier.Logics.Propositional.CNF.ParitySearch.PolyTime`.

## Main results

* `Cslib.Logic.PL.exists_assignments_two_pow_mul_countUnsat_le`: polynomially many assignments
  for each fixed `k` serve every formula on the given variables.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Section 16.2][AlonSpencer2016]
-/

public section

namespace Cslib.Logic.PL

open Cslib.Probability

variable {V : Type*} [DecidableEq V]

/-- **Polynomial-size `k`-wise independent sample spaces for MAX-E`k`-SAT**: for every list `vs` of
`n` variables and every `k` there are at most `(2 n + 4) ^ (3 k)` assignments such that for every
formula on these variables whose clauses have at least `k` distinct literals, one of the
assignments falsifies at most `2 ^ -k` of the clauses. -/
theorem exists_assignments_two_pow_mul_countUnsat_le (k : ℕ) (vs : List V) :
    ∃ S : List (V → Bool), S.length ≤ (2 * vs.length + 4) ^ (3 * k) ∧
      ∀ φ : CNF V, (∀ v ∈ φ.vars, v ∈ vs) → (∀ c ∈ φ, k ≤ c.toFinset.card) →
        ∃ σ ∈ S, 2 ^ k * φ.countUnsat σ ≤ φ.length := by
  classical
  set U := vs.length + 1
  set t := trinomialStep U 1
  have hU : U ≤ 2 ^ (2 * 3 ^ t) := le_two_pow_trinomialDeg U 1
  have hM : 1 ≤ 2 * 3 ^ t := le_trinomialDeg U 1
  have hh := isKWiseIndependentHash_trinomialPolyHash (k := k) hU hM
  -- one bit per variable: `Fin (2 ^ 1) ≃ Bool`
  let bit : Fin (2 ^ 1) ≃ Bool := (finCongr (by norm_num)).trans finTwoEquiv
  have hbit := hh.map_equiv bit
  let pos : V → Fin U := fun v => ⟨min (vs.idxOf v) vs.length, by omega⟩
  let σ : (Fin k → Fin (2 ^ (2 * 3 ^ t))) → V → Bool := fun c v =>
    bit (trinomialPolyHash t k U 1 c (pos v))
  refine ⟨(Finset.univ.image σ).toList, ?_, fun φ hvs hk => ?_⟩
  · rw [Finset.length_toList]
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      pow_mul (2 * vs.length + 4) 3 k]
    refine Nat.pow_le_pow_left ?_ k
    have hm : max U 2 ≤ vs.length + 2 := max_le (by omega) (by omega)
    have hpos : 1 ≤ Nat.clog 2 (max U 2) := Nat.clog_pos (by norm_num) (by omega)
    have hdeg : 2 * 3 ^ t ≤ 3 * Nat.clog 2 (max U 2) := by
      have := trinomialDeg_le_three_mul U 1
      rwa [max_self, max_eq_left hpos] at this
    have hpow := Nat.pow_clog_le_mul (b := 2) (n := max U 2) (by norm_num) (by omega)
    calc 2 ^ (2 * 3 ^ t) ≤ 2 ^ (3 * Nat.clog 2 (max U 2)) := by gcongr
      _ = (2 ^ Nat.clog 2 (max U 2)) ^ 3 := by rw [mul_comm, pow_mul]
      _ ≤ (2 * vs.length + 4) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  · obtain ⟨c, hc⟩ := exists_two_pow_mul_countUnsat_le hbit (e := pos)
      (fun v hv w hw hvw => by
        have hv' := List.idxOf_lt_length_of_mem (hvs v hv)
        have hw' := List.idxOf_lt_length_of_mem (hvs w hw)
        have := congrArg Fin.val hvw
        simp only [pos, min_eq_left hv'.le, min_eq_left hw'.le] at this
        exact (List.idxOf_inj (hvs v hv)).1 this) hk
    exact ⟨σ c, Finset.mem_toList.2 (Finset.mem_image_of_mem σ (Finset.mem_univ c)), hc⟩

end Cslib.Logic.PL
