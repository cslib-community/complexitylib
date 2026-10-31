/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.LocalDeformation
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TaperedRecovery
public import Complexity.Foundations.Data.Polynomial.RingLagrange
public import Complexity.Foundations.Combinatorics.PacketPacking
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ChildSize

/-!
# One active call of the contraction recursion

This file proves the correctness of one active call of the recursive contraction algorithm of
[OpenAI2026ETH] (§D.4.4–§D.4.7, pp. 61–64): the contraction modulo `2 ^ p` is recovered from the
contractions of the children modulo the higher precisions `2 ^ p_t`.

**Setting.** Let `K` be a `ℚ`-algebra and `B` a subring containing `ℤ_(2)` (in the manuscript,
`K = ℚ[U] / (f)` and `B = O`), and let `N` be a Boolean tensor network with entries in `B` whose
edges run from rows to columns. Pack its `M` edges into packets of `L = 2 ^ a` slots, and choose
`n > M (2 L - 1)` interpolation points `ζ k ∈ B` whose differences are units (in the manuscript,
binary-coordinate lifts of residue-field elements). For each nonzero grid point `t` of positive
multiplicity `q_t` and each point `ζ k`, a value `v t k ∈ B` is supplied.

**Recovery** (`recoverFromValues`). Interpolate the values `v t ·` at the points `ζ` over `B`
(`Lagrange.ringInterpolate`), and apply the tapered Hermite recovery (D.9) to the interpolants
(`Cslib.Circuits.Frontier.taperedRecovery`).

**Correctness.** If every `v t k` agrees with the local deformation `F(t + α ζ k)`
(`TensorNetwork.localDeformation`) modulo `2 ^ p_t`, `p_t = p + 8 h D_t + 8 M (a + 1)`, then the
interpolant agrees with `F(t + α z)` modulo `2 ^ p_t` (`Lagrange.exists_ringInterpolate_eq_add`),
and Lemma D.5 (`Cslib.Circuits.Frontier.exists_taperedRecovery_eq_add_of_params`) recovers
`F(0) = Z(N)` modulo `2 ^ p` (`TensorNetwork.exists_recoverFromValues_eq_add`). Modulo `2 ^ p_t`,
`F(t + α ζ)` is the deformed contraction of the reduced network along the Cauchy matrix at
`T = t + α ζ` (`TensorNetwork.mk_eval_localDeformation`), which the child identity (D.16),
`TensorNetwork.deformedContraction_cauchyValueMatrix_eq_sum`, writes as the sum over the mode tuples
of the products of the contractions of the children. So the values may be computed from the
children's contractions modulo `2 ^ p_t` (`TensorNetwork.exists_recoverFromValues_eq_add_of_mk`).

**The packing bridge.** The orientation that the child identity needs is property (2) of
Lemma D.3 for `Cslib.PacketPacking.Packing` (`packingGroup_src_tgt`), and the port
counts of Lemma D.3 (3) are the group sizes that bound the children
(`card_packingGroup_src`, `card_packingGroup_tgt`, with
`TensorNetwork.ModeSplitting.mul_card_edges_child_le`).

## Main definitions

* `Cslib.Circuits.Frontier.integerHom`: the inclusion of `ℤ_(2)` into `B`.
* `Cslib.Circuits.Frontier.recoverFromValues`: interpolation followed by tapered recovery.
* `Cslib.Circuits.Frontier.packingGroup`: the group of a vertex in coordinate `i` of a packing.

## Main results

* `Lagrange.exists_ringInterpolate_eq_add`: interpolating values that agree with a polynomial
  modulo `π` gives a polynomial that agrees with it modulo `π`.
* `Cslib.Circuits.Frontier.TensorNetwork.exists_recoverFromValues_eq_add`: recovery modulo
  `2 ^ p` from values modulo `2 ^ p_t`.
* `Cslib.Circuits.Frontier.TensorNetwork.mk_eval_localDeformation`: the values of the local
  deformation modulo `2 ^ p_t` are deformed contractions along `cauchyValueMatrix`.
* `Cslib.Circuits.Frontier.TensorNetwork.exists_recoverFromValues_eq_add_of_mk`: correctness of
  one active call.
* `Cslib.Circuits.Frontier.packingGroup_src_tgt`: the packing bridge, with
  `packing_slot_lt`, `packing_slot_injective`, `card_packingGroup_src` and
  `card_packingGroup_tgt`.
* `Cslib.Circuits.Frontier.two_pow_padicValInt_dvd_and_not_dvd`: a node of valuation `i` meets
  the divisibility hypotheses of the child identity.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma D.3 (p. 58),
  §D.4.4–§D.4.7, pp. 60–64.
-/

public section

open Polynomial Finset

/-! ### Interpolation of congruent values -/

namespace Lagrange

variable {R ι : Type*} [CommRing R] [DecidableEq ι] {s : Finset ι} {v : ι → R}

/-- **Interpolating congruent values.** At nodes with unit differences, if the values `r i` agree
with a polynomial `f` of degree below `#s` modulo `π`, then so does every coefficient of their
interpolant. -/
theorem exists_ringInterpolate_eq_add (hvs : (s : Set ι).Pairwise fun i j => IsUnit (v i - v j))
    {f : R[X]} (hf : f.degree < #s) {π : R} {r : ι → R}
    (hr : ∀ i ∈ s, ∃ c, r i = f.eval (v i) + π * c) :
    ∃ g : R[X], ringInterpolate s v r = f + C π * g := by
  choose! c hc using hr
  refine ⟨∑ i ∈ s, C (c i) * ringBasis s v i, ?_⟩
  rw [← sub_eq_iff_eq_add']
  calc ringInterpolate s v r - f
      = ringInterpolate s v r - ringInterpolate s v (fun i => f.eval (v i)) := by
        rw [sub_right_inj]; exact eq_ringInterpolate hvs hf
    _ = ringInterpolate s v (r - fun i => f.eval (v i)) := (map_sub _ _ _).symm
    _ = ∑ i ∈ s, C (π * c i) * ringBasis s v i := by
        rw [ringInterpolate_apply]
        refine sum_congr rfl fun i hi => ?_
        rw [Pi.sub_apply, hc i hi, add_sub_cancel_left]
    _ = C π * ∑ i ∈ s, C (c i) * ringBasis s v i := by
        rw [mul_sum]
        exact sum_congr rfl fun i _ => by rw [C_mul, mul_assoc]

end Lagrange

namespace Cslib.Circuits.Frontier

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- The inclusion of `ℤ_(2)` into a subring `B` of a `ℚ`-algebra containing it. -/
@[expose] noncomputable def integerHom (B : Subring K) (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) :
    ℤ₍₂₎ →+* B :=
  ((algebraMap ℚ K).comp (ℤ₍₂₎).subtype).codRestrict B fun c => hB c c.2

theorem subtype_comp_integerHom (B : Subring K) (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) :
    B.subtype.comp (integerHom B hB) = (algebraMap ℚ K).comp (ℤ₍₂₎).subtype :=
  rfl

/-- The value recovered at an active call from the values `v t k` at the interpolation points
`ζ k`: interpolate over `B` at each node `t`, and apply tapered Hermite recovery (D.9). -/
noncomputable def recoverFromValues (B : Subring K) (a u h : ℕ) {n : ℕ} (ζ : Fin n → B)
    (v : ℤ → Fin n → B) : K :=
  taperedRecovery a u h fun t => (Lagrange.ringInterpolate univ ζ (v t)).map B.subtype

/-- A nonzero integer `t` of valuation `i` is divisible by `2 ^ i` but not by `2 ^ (i + 1)`. -/
theorem two_pow_padicValInt_dvd_and_not_dvd {t : ℤ} (ht : t ≠ 0) :
    (2 : ℤ) ^ padicValInt 2 t ∣ t ∧ ¬ (2 : ℤ) ^ (padicValInt 2 t + 1) ∣ t := by
  refine ⟨by exact_mod_cast padicValInt_dvd (p := 2) t, fun h => ?_⟩
  have := (padicValInt_dvd_iff (p := 2) (padicValInt 2 t + 1) t).mp (by exact_mod_cast h)
  omega

namespace TensorNetwork

variable {V E P : Type*} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq P]

/-- **Correctness of recovery from values.** Let `N` have entries in `B`, edges from rows to
columns packed into packets of `2 ^ a` slots, and let `1 ≤ u ≤ M` and `3 M ≤ h u ≤ 3 M + u` for
`M` edges. Let the `n > M (2 L - 1)` points `ζ k` have unit differences. If at every node `t` of
positive multiplicity the values `v t k` agree with `F(t + α ζ k)` modulo `2 ^ p_t`,
`p_t = p + 8 h D_t + 8 M (a + 1)`, then the recovered value agrees with the contraction modulo
`2 ^ p`. -/
theorem exists_recoverFromValues_eq_add (B : Subring K)
    (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) (N : TensorNetwork B Bool V E) (side : V → Bool)
    {a : ℕ} {packet : E → P} {slot : E → ℕ} (hslot : ∀ e, slot e < 2 ^ a)
    (hinj : ∀ e e', packet e = packet e' → slot e = slot e' → e = e') {u h p : ℕ} (hu : 1 ≤ u)
    (huM : u ≤ Fintype.card E) (hh : 3 * Fintype.card E ≤ h * u)
    (hh' : h * u ≤ 3 * Fintype.card E + u) {n : ℕ} (ζ : Fin n → B)
    (hζ : Pairwise fun k l => IsUnit (ζ k - ζ l)) (hn : Fintype.card E * (2 * 2 ^ a - 1) < n)
    (v : ℤ → Fin n → B)
    (hv : ∀ t ∈ recoveryNodes a, 0 < taperMult u h t → ∀ k, ∃ c : B,
      v t k = (N.localDeformation side (integerHom B hB) a t packet slot).eval (ζ k) +
        2 ^ (p + 8 * h * 2 ^ (a - padicValInt 2 t) + 8 * Fintype.card E * (a + 1)) * c) :
    ∃ b ∈ B, recoverFromValues B a u h ζ v = (N.contraction : K) + 2 ^ p * b := by
  have hF0 : (((N.map B.subtype).map C).deformedContraction side
      ((cauchyMatrix (2 ^ a) packet slot).map (mapRingHom (algebraMap ℚ K)))).eval 0 =
        (N.contraction : K) := by
    rw [eval_zero_deformedContraction_cauchyMatrix _ side hslot hinj, contraction_map]
    rfl
  rw [← hF0]
  refine exists_taperedRecovery_eq_add_of_params B hB hu huM hh hh'
    (natDegree_deformedContraction_cauchyMatrix_le _ side hslot) _ fun t ht j hj => ?_
  have htS : t ∈ cauchyGrid (2 ^ a) := mem_of_mem_erase ht
  have hnat : (N.localDeformation side (integerHom B hB) a t packet slot).natDegree < n :=
    (natDegree_localDeformation_le N side (integerHom B hB) hslot htS).trans_lt hn
  have hdeg : (N.localDeformation side (integerHom B hB) a t packet slot).degree <
      ↑(#(univ : Finset (Fin n))) := by
    rw [card_univ, Fintype.card_fin]
    exact (degree_le_natDegree).trans_lt (Nat.cast_lt.mpr hnat)
  obtain ⟨g, hg⟩ := Lagrange.exists_ringInterpolate_eq_add (s := univ) (v := ζ)
    (fun k _ l _ hkl => hζ hkl) hdeg
    (π := 2 ^ (p + 8 * h * 2 ^ (a - padicValInt 2 t) + 8 * Fintype.card E * (a + 1)))
    (fun k _ => hv t ht (by omega) k)
  refine ⟨(g.coeff j : K), (g.coeff j).2, ?_⟩
  rw [← map_localDeformation N side (integerHom B hB) B.subtype (subtype_comp_integerHom B hB)
    hslot htS, coeff_map, coeff_map, hg, coeff_add, coeff_C_mul, map_add, map_mul, map_pow]
  rfl

end TensorNetwork

/-! ### The packing bridge -/

section PackingBridge

variable {V E : Type*} {src tgt : E → V} {a r : ℕ}

/-- The group of a vertex in coordinate `i` of a packing of the edges `src e → tgt e`: its row
label if it is a row and its column label if it is a column. -/
@[expose] def packingGroup (side : V → Bool) (Q : PacketPacking.Packing src tgt a r) (i : Fin a)
    (v : V) : Fin r :=
  if side v then Q.rowLabel v i else Q.colLabel v i

/-- **The packing bridge.** For a packing of edges that run from rows to columns (Lemma D.3 of
[OpenAI2026ETH]), the groups in coordinate `i` are oriented by digit `i` of the slots
(Lemma D.3 (2)): the hypothesis of `TensorNetwork.cauchyModeSplitting`. The edge ends `src` and
`tgt` are arbitrary functions, so the bridge applies to `N.src` and `N.tgt` of any network with
these ends, such as `N.map f`. -/
theorem packingGroup_src_tgt (side : V → Bool) (hsrc : ∀ e, side (src e) = true)
    (htgt : ∀ e, side (tgt e) = false) (Q : PacketPacking.Packing src tgt a r) (i : Fin a)
    (e : E) :
    (packingGroup side Q i (src e), packingGroup side Q i (tgt e)) =
      if (Q.slot e : ℕ).testBit i then (Q.symbols (Q.packet e) i).swap
      else Q.symbols (Q.packet e) i := by
  simp only [packingGroup, hsrc, htgt, ↓reduceIte, Bool.false_eq_true]
  exact Q.labels_eq e i

/-- The slots of a packing lie below `2 ^ a`. -/
theorem packing_slot_lt (Q : PacketPacking.Packing src tgt a r) (e : E) :
    (Q.slot e : ℕ) < 2 ^ a :=
  (Q.slot e).isLt

/-- No two edges share a slot of a packet. -/
theorem packing_slot_injective (Q : PacketPacking.Packing src tgt a r) (e e' : E)
    (hp : Q.packet e = Q.packet e') (hs : (Q.slot e : ℕ) = Q.slot e') : e = e' :=
  Q.injective (Prod.ext hp (Fin.ext hs))

variable [Fintype E]

/-- The rows of group `σ` in coordinate `i` of a packing are the rows with symbol `σ`. -/
theorem card_packingGroup_src (side : V → Bool) (hsrc : ∀ e, side (src e) = true)
    (Q : PacketPacking.Packing src tgt a r) (i : Fin a) (σ : Fin r) :
    #{e | packingGroup side Q i (src e) = σ} = #{e | Q.rowLabel (src e) i = σ} := by
  simp only [packingGroup, hsrc, ↓reduceIte]

/-- The columns of group `σ` in coordinate `i` of a packing are the columns with symbol `σ`. -/
theorem card_packingGroup_tgt (side : V → Bool) (htgt : ∀ e, side (tgt e) = false)
    (Q : PacketPacking.Packing src tgt a r) (i : Fin a) (σ : Fin r) :
    #{e | packingGroup side Q i (tgt e) = σ} = #{e | Q.colLabel (tgt e) i = σ} := by
  simp only [packingGroup, htgt, Bool.false_eq_true, ↓reduceIte]

end PackingBridge

namespace TensorNetwork

variable {V E P : Type*} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq P]

/-- **The values of the local deformation modulo `2 ^ p_t`** are deformed contractions of the
reduced network along the Cauchy matrix at `T = t + α ζ` (which the child identity (D.16),
`TensorNetwork.deformedContraction_cauchyValueMatrix_eq_sum`, expands). -/
theorem mk_eval_localDeformation {B : Type*} [CommRing B] (N : TensorNetwork B Bool V E)
    (side : V → Bool) (κ : ℤ₍₂₎ →+* B) (a : ℕ) (t : ℤ) (packet : E → P) (slot : E → ℕ)
    (I : Ideal B) (ζ : B) :
    Ideal.Quotient.mk I ((N.localDeformation side κ a t packet slot).eval ζ) =
      (N.map (Ideal.Quotient.mk I)).deformedContraction side
        (cauchyValueMatrix ((Ideal.Quotient.mk I).comp κ) (Ideal.Quotient.mk I ζ) a t packet
          slot) := by
  rw [← eval₂_hom, eval₂_localDeformation]

/-- **Correctness of one active call** ([OpenAI2026ETH], §D.4.4–§D.4.7). Under the hypotheses of
`exists_recoverFromValues_eq_add`, suppose that at every node `t` of positive multiplicity, each
value `v t k` reduces modulo `2 ^ p_t` to the deformed contraction of the reduced network along the
Cauchy matrix at `T = t + α ζ k`, `p_t = p + 8 h D_t + 8 M (a + 1)`: by the child identity (D.16),
the sum over the mode tuples of the products of the contractions of the children. Then the
recovered value agrees with the contraction modulo `2 ^ p`. -/
theorem exists_recoverFromValues_eq_add_of_mk (B : Subring K)
    (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) (N : TensorNetwork B Bool V E) (side : V → Bool)
    {a : ℕ} {packet : E → P} {slot : E → ℕ} (hslot : ∀ e, slot e < 2 ^ a)
    (hinj : ∀ e e', packet e = packet e' → slot e = slot e' → e = e') {u h p : ℕ} (hu : 1 ≤ u)
    (huM : u ≤ Fintype.card E) (hh : 3 * Fintype.card E ≤ h * u)
    (hh' : h * u ≤ 3 * Fintype.card E + u) {n : ℕ} (ζ : Fin n → B)
    (hζ : Pairwise fun k l => IsUnit (ζ k - ζ l)) (hn : Fintype.card E * (2 * 2 ^ a - 1) < n)
    (v : ℤ → Fin n → B)
    (hv : ∀ t ∈ recoveryNodes a, 0 < taperMult u h t → ∀ k,
      let I := Ideal.span {(2 : B) ^ (p + 8 * h * 2 ^ (a - padicValInt 2 t) +
        8 * Fintype.card E * (a + 1))}
      Ideal.Quotient.mk I (v t k) =
        (N.map (Ideal.Quotient.mk I)).deformedContraction side
          (cauchyValueMatrix ((Ideal.Quotient.mk I).comp (integerHom B hB))
            (Ideal.Quotient.mk I (ζ k)) a t packet slot)) :
    ∃ b ∈ B, recoverFromValues B a u h ζ v = (N.contraction : K) + 2 ^ p * b := by
  refine exists_recoverFromValues_eq_add B hB N side hslot hinj hu huM hh hh' ζ hζ hn v
    fun t ht hq k => ?_
  have h1 := hv t ht hq k
  simp only at h1
  rw [← mk_eval_localDeformation, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, by rw [mul_comm, hc, add_sub_cancel]⟩

end TensorNetwork

end Cslib.Circuits.Frontier
