/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.SymAnd
public import Complexity.Foundations.BooleanAnalysis.Mobius
import Mathlib.Algebra.BigOperators.ModEq

/-!
# The canonical `SYM ∘ AND` circuit of a low-degree function

Let `c` be an integer function of degree at most `D` on the cube `T → Bool`, for a finite set of
positions `T`. Its subset Möbius coefficients `μ S = ∑_{U ⊆ S} (-1) ^ (#S - #U) c 1_U`
(`Cslib.BitString.subsetMobius`) vanish on sets of more than `D` positions, and
`c = ∑_S μ S · x^S` (`Cslib.BitString.eq_sum_subsetMobius_smul_monomial`). Modulo `M > 0`, taking
every set `S` of at most `D` positions as an AND gate with multiplicity the least residue of `μ S`
modulo `M` (`Cslib.Circuits.Boolean.SymAnd.mobiusGates`) gives a multiset of AND gates whose
number of satisfied gates is congruent to `c` modulo `M` at every point. Applying a symmetric gate
to that number modulo `M` gives the canonical circuit `Cslib.Circuits.Boolean.SymAnd.ofLowDegree`:
it outputs `out (c x mod M)` (`SymAnd.eval_ofLowDegree`), with fan-in at most `D` and at most
`M (|T| + 1) ^ D` AND gates.

The circuit is determined by `D`, `M`, `out` and the values of `c` at the indicators of sets of at
most `D` positions, with no choice. Its gates give the existence form
`SymAnd.exists_countP_modEq_of_mem_lowDegree`, and it is the step from which the collapse of
modular towers (`Complexity.Computability.Circuit.Boolean.SymAnd.Collapse`) builds its circuits.

## Main definitions

* `Cslib.Circuits.Boolean.SymAnd.mobiusGates`: the AND gates with Möbius multiplicities modulo `M`.
* `Cslib.Circuits.Boolean.SymAnd.ofLowDegree`: the canonical `SYM ∘ AND` circuit of `c` modulo `M`.

## Main results

* `Cslib.Circuits.Boolean.SymAnd.natCast_count_ofLowDegree_modEq`: the number of satisfied gates
  is `c` modulo `M`.
* `Cslib.Circuits.Boolean.SymAnd.eval_ofLowDegree`: the circuit computes `out (c x mod M)`.
* `Cslib.Circuits.Boolean.SymAnd.fanIn_ofLowDegree_le`,
  `Cslib.Circuits.Boolean.SymAnd.size_ofLowDegree_le`: fan-in at most `D`, size at most
  `M (|T| + 1) ^ D`.
* `Cslib.Circuits.Boolean.SymAnd.exists_countP_modEq_of_mem_lowDegree`: low-degree integer
  functions are AND counts modulo `M`.

## References

* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
-/

public section

namespace Cslib.Circuits.Boolean

namespace SymAnd

open Finset BitString

section Canonical

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The AND gates of `c` modulo `M` up to degree `D`: every set `S` of at most `D` positions, with
multiplicity the least residue modulo `M` of the subset Möbius coefficient of `c` at `S`. -/
@[expose] def mobiusGates (D M : ℕ) (c : (T → Bool) → ℤ) : Multiset (Finset T) :=
  (univ.filter fun S : Finset T => #S ≤ D).val.bind fun S =>
    Multiset.replicate (subsetMobius (fun U => c fun i => decide (i ∈ U)) S % M).toNat S

/-- Every gate of `mobiusGates D M c` reads at most `D` positions. -/
theorem card_le_of_mem_mobiusGates {D M : ℕ} {c : (T → Bool) → ℤ} {S : Finset T}
    (hS : S ∈ mobiusGates D M c) : #S ≤ D := by
  obtain ⟨U, hU, hSU⟩ := Multiset.mem_bind.1 hS
  rw [Multiset.eq_of_mem_replicate hSU]
  exact (mem_filter.1 hU).2

/-- There are at most `M (|T| + 1) ^ D` gates: fewer than `M` copies of each set of at most `D`
positions. -/
theorem card_mobiusGates_le (D : ℕ) {M : ℕ} (hM : 0 < M) (c : (T → Bool) → ℤ) :
    Multiset.card (mobiusGates D M c) ≤ M * (Fintype.card T + 1) ^ D := by
  rw [mobiusGates, Multiset.card_bind]
  change ∑ S ∈ univ.filter (fun S : Finset T => #S ≤ D),
    Multiset.card (Multiset.replicate _ S) ≤ _
  simp only [Multiset.card_replicate]
  calc _ ≤ ∑ _S ∈ univ.filter (fun S : Finset T => #S ≤ D), M :=
        sum_le_sum fun S _ => by
          rw [Int.toNat_le]
          exact (Int.emod_lt_of_pos _ (by exact_mod_cast hM)).le
    _ = M * #(univ.filter fun S : Finset T => #S ≤ D) := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ M * (Fintype.card T + 1) ^ D := Nat.mul_le_mul_left M (card_filter_card_le_le_pow D)

/-- The canonical `SYM ∘ AND` circuit of `c` modulo `M` up to degree `D`: the gates
`mobiusGates D M c` below the symmetric gate `z ↦ out (z mod M)`. -/
@[expose] def ofLowDegree (D M : ℕ) (c : (T → Bool) → ℤ) (out : ℕ → Bool) : SymAnd T :=
  ⟨mobiusGates D M c, fun z => out (z % M)⟩

/-- **The canonical gates count `c` modulo `M`.** If `c` has degree at most `D` and `M > 0`, the
number of satisfied gates of `ofLowDegree D M c out` is congruent to `c` modulo `M`. -/
theorem natCast_count_ofLowDegree_modEq {D : ℕ} {c : (T → Bool) → ℤ}
    (hc : c ∈ lowDegree ℤ T D) {M : ℕ} (hM : 0 < M) (out : ℕ → Bool) (x : T → Bool) :
    ((ofLowDegree D M c out).count x : ℤ) ≡ c x [ZMOD M] := by
  have hc' := mem_lowDegree_iff_subsetMobius_eq_zero.1 hc
  rw [natCast_count_eq_sum, congrFun (eq_sum_subsetMobius_smul_monomial c) x]
  simp only [ofLowDegree, mobiusGates, Multiset.map_bind, Multiset.sum_bind,
    Multiset.map_replicate, Multiset.sum_replicate, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, nsmul_eq_mul]
  change ∑ S ∈ univ.filter (fun S : Finset T => #S ≤ D), _ ≡ _ [ZMOD M]
  conv_rhs => rw [← sum_filter_of_ne (p := fun S : Finset T => #S ≤ D) fun S _ hS => by
    by_contra h
    exact hS (by rw [hc' S (by omega), zero_mul])]
  refine Int.ModEq.sum fun S _ => Int.ModEq.mul_right _ ?_
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hM.ne'))]
  exact Int.mod_modEq _ _

/-- The number of satisfied gates modulo `M` is the least residue of `c` modulo `M`. -/
theorem count_ofLowDegree_mod {D : ℕ} {c : (T → Bool) → ℤ} (hc : c ∈ lowDegree ℤ T D) {M : ℕ}
    (hM : 0 < M) (out : ℕ → Bool) (x : T → Bool) :
    (ofLowDegree D M c out).count x % M = (c x % M).toNat := by
  have h : ((ofLowDegree D M c out).count x : ℤ) % M = c x % M :=
    natCast_count_ofLowDegree_modEq hc hM out x
  have h' : (((ofLowDegree D M c out).count x % M : ℕ) : ℤ) = c x % M := by grind
  rw [← h', Int.toNat_natCast]

/-- **What the canonical circuit computes**: `out` of the least residue of `c x` modulo `M`, for
`c` of degree at most `D` and `M > 0`. -/
theorem eval_ofLowDegree {D : ℕ} {c : (T → Bool) → ℤ} (hc : c ∈ lowDegree ℤ T D) {M : ℕ}
    (hM : 0 < M) (out : ℕ → Bool) (x : T → Bool) :
    (ofLowDegree D M c out).eval x = out (c x % M).toNat := by
  rw [← count_ofLowDegree_mod hc hM out x]
  rfl

/-- The canonical circuit has fan-in at most `D`. -/
theorem fanIn_ofLowDegree_le (D M : ℕ) (c : (T → Bool) → ℤ) (out : ℕ → Bool) :
    (ofLowDegree D M c out).fanIn ≤ D :=
  fanIn_le_iff.2 fun _ hS => card_le_of_mem_mobiusGates hS

/-- The canonical circuit has at most `M (|T| + 1) ^ D` AND gates. -/
theorem size_ofLowDegree_le (D : ℕ) {M : ℕ} (hM : 0 < M) (c : (T → Bool) → ℤ)
    (out : ℕ → Bool) : (ofLowDegree D M c out).size ≤ M * (Fintype.card T + 1) ^ D :=
  card_mobiusGates_le D hM c

end Canonical

variable {T : Type*} [Fintype T]

/-- **Low-degree integer functions are AND counts modulo `M`.** For `c` of degree at most `D` on
the cube and `M > 0`, some multiset of at most `M * (|T| + 1) ^ D` sets of at most `D` positions
has, at every point, a number of satisfied sets congruent to `c` modulo `M`; the gates of
`ofLowDegree` are one. -/
theorem exists_countP_modEq_of_mem_lowDegree {D : ℕ} {c : (T → Bool) → ℤ}
    (hc : c ∈ lowDegree ℤ T D) {M : ℕ} (hM : 0 < M) :
    ∃ G : Multiset (Finset T), (∀ S ∈ G, #S ≤ D) ∧
      Multiset.card G ≤ M * (Fintype.card T + 1) ^ D ∧
      ∀ x, ((G.countP fun S => ∀ i ∈ S, x i = true : ℕ) : ℤ) ≡ c x [ZMOD M] := by
  classical
  exact ⟨mobiusGates D M c, fun _ => card_le_of_mem_mobiusGates, card_mobiusGates_le D hM c,
    natCast_count_ofLowDegree_modEq hc hM fun _ => false⟩

end SymAnd

end Cslib.Circuits.Boolean
