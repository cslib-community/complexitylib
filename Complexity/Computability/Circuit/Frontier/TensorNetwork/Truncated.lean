/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContraction
public import Complexity.Computability.PolyTime.GaloisRingInterpolation
public import Mathlib.Algebra.Polynomial.CoeffList
import Complexity.Computability.Circuit.Frontier.TensorNetwork.DescribedLift
import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeRecovery
import Complexity.Computability.PolyTime.GaloisRingSeries
import Complexity.Foundations.Data.Polynomial.CoeffList
import Complexity.Foundations.Data.Polynomial.RingLagrange
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.List.GetD
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Contraction at truncation order `ℓ`, by evaluation and interpolation

Theorem D.1 of [OpenAI2026ETH] (p. 53) contracts Boolean tensor networks whose entries lie in
`B_{P,ℓ} = (ℤ / 2 ^ P)[V] / (V ^ ℓ)`. This file gives that contraction for described networks
(`DescribedNetwork T`) and reduces it to contractions over `A_P = (ℤ / 2 ^ P)[U] / (f)` of networks
with the same ports, by evaluating `V` at points of `A_P` and interpolating.

**Entries and the contraction.** An entry is a list of natural numbers, its coefficients of
`1, V, V ^ 2, …` (Mathlib's `Polynomial.ofCoeffList`). The contraction over `ℕ[V]` of the entries
(`DescribedNetwork.polyContraction`) has, below `V ^ ℓ` and modulo `2 ^ P`, the coefficients of
the contraction in `B_{P,ℓ}` (`DescribedNetwork.truncContraction`): they depend only on the images
of the entries in `B_{P,ℓ}`, their coefficients below `ℓ` modulo `2 ^ P`
(`DescribedNetwork.truncContraction_congr`). So `truncContraction` is the `B_{P,ℓ}` contraction of
the canonical lifts of the entries, as in §D.4.1 (p. 58).

**Evaluation.** Cutting the entries to `ℓ` coefficients (`cutCoeffs`,
`DescribedNetwork.truncContraction_cutCoeffs`)
bounds the degree of the contraction over `ℕ[V]` by `(ℓ - 1) k` for `k` vertices
(`DescribedNetwork.natDegree_polyContraction_le`). The network specialized at a point `ζ` of
`A_P` (`DescribedNetwork.specNet`) has the same ports, and its entry at a vertex is the value at
`ζ` of the first `ℓ` coefficients of the original entry, by Horner's rule (`specEntry`). Its
contraction in `A_P` is the contraction over `ℕ[V]` evaluated at `ζ`
(`DescribedNetwork.val_contraction_specNet`).

**Interpolation.** At `n` points of `A_P` with unit differences, the Lagrange interpolant of the
values (`GaloisRingArith.interp`) is a polynomial of degree below `n` agreeing with the contraction
at the points. When `(ℓ - 1) k < n` it is the contraction, so the constant coordinates of its first
`ℓ` coefficients, modulo `2 ^ P`, are the truncated contraction (`interpRecover`,
`DescribedNetwork.interpRecover_eq_truncContraction`). The binary digits of `0, …, n - 1` are such
points once `n ≤ 2 ^ deg f` and `f` is irreducible modulo `2` (`isUnit_val_sub_digits`).

**The reduction** (`DescribedNetwork.interpContract`). Given a contraction `core` over `A_P` of the
specialized networks, contract the network specialized at each of the `(ℓ - 1) k + 1` digit
points and interpolate. If `core` is correct at those inputs, this is the truncated contraction
(`DescribedNetwork.interpContract_eq`). This route is not the manuscript's, which embeds the
entries into `A = O[V] / (V ^ ℓ)` and computes there throughout the recursion (§D.4.1, p. 57, and
the proof of Theorem D.1, §D.4.7, p. 64); it reduces truncation order `ℓ` to `ℓ = 1` over `A_P`
and leaves the recursion unchanged.

This file proves correctness only. The native machine running the reduction, with the time and
space bounds of Theorem D.1, is not formalized here (#1538).

## Main definitions

* `Cslib.Circuits.Frontier.cutCoeffs`: the first `ℓ` coefficients.
* `Cslib.Circuits.Frontier.DescribedNetwork.polyContraction`: the contraction over `ℕ[V]`.
* `Cslib.Circuits.Frontier.DescribedNetwork.truncContraction`: the contraction in `B_{P,ℓ}`.
* `Cslib.Circuits.Frontier.specEntry`, `Cslib.Circuits.Frontier.DescribedNetwork.specNet`: the
  network specialized at a point.
* `Cslib.Circuits.Frontier.interpRecover`: reading the truncated contraction off an interpolant.
* `Cslib.Circuits.Frontier.DescribedNetwork.interpContract`: the reduction to `ℓ = 1` over `A_P`.

## Main results

* `Cslib.Circuits.Frontier.DescribedNetwork.truncContraction_congr`: the contraction depends only
  on the entries in `B_{P,ℓ}`.
* `Cslib.Circuits.Frontier.DescribedNetwork.natDegree_polyContraction_le`: the degree bound.
* `Cslib.Circuits.Frontier.DescribedNetwork.val_contraction_specNet`: specialization is
  evaluation.
* `Cslib.Circuits.Frontier.interpRecover_eq`: recovery from values at points with unit
  differences.
* `Cslib.Circuits.Frontier.DescribedNetwork.interpRecover_eq_truncContraction`: the truncated
  contraction from the specialized contractions.
* `Cslib.Circuits.Frontier.DescribedNetwork.interpContract_eq`: the reduction is correct.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53),
  §D.4.1 (pp. 57–58) and §D.4.7 (p. 64).
-/

public section

namespace Cslib.Circuits.Frontier

open Polynomial Finset GaloisRingArith

/-! ### Entries as polynomials in `V` -/

/-- The first `ℓ` coefficients of a list, padded with zeros to length `ℓ`. -/
@[expose] def cutCoeffs (ℓ : ℕ) (c : List ℕ) : List ℕ := (List.range ℓ).map fun i => c.getD i 0

@[simp] theorem length_cutCoeffs (ℓ : ℕ) (c : List ℕ) : (cutCoeffs ℓ c).length = ℓ := by
  simp [cutCoeffs]

/-- Below `ℓ`, the cut list has the coefficients of the list. -/
theorem getD_cutCoeffs (c : List ℕ) {ℓ i : ℕ} (hi : i < ℓ) :
    (cutCoeffs ℓ c).getD i 0 = c.getD i 0 := by
  rw [cutCoeffs, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range]

/-! ### The contraction in `B_{P,ℓ}` -/

/-- The map `ℕ[V] → (ℤ / 2 ^ P)[V] / (V ^ ℓ)` onto `B_{P,ℓ}`. -/
noncomputable def truncHom (P ℓ : ℕ) :
    ℕ[X] →+* (ZMod (2 ^ P))[X] ⧸ Ideal.span {(X ^ ℓ : (ZMod (2 ^ P))[X])} :=
  (Ideal.Quotient.mk _).comp (mapRingHom (Nat.castRingHom (ZMod (2 ^ P))))

/-- **Two polynomials have the same image in `B_{P,ℓ}`** exactly when their coefficients below
`ℓ` agree modulo `2 ^ P`. -/
theorem truncHom_eq_iff {P ℓ : ℕ} {p q : ℕ[X]} :
    truncHom P ℓ p = truncHom P ℓ q ↔ ∀ j < ℓ, p.coeff j % 2 ^ P = q.coeff j % 2 ^ P := by
  rw [truncHom, RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq,
    Ideal.mem_span_singleton, X_pow_dvd_iff]
  refine forall₂_congr fun j _ => ?_
  rw [coeff_sub, sub_eq_zero, coe_mapRingHom, coeff_map, coeff_map]
  exact ZMod.natCast_eq_natCast_iff' _ _ _

namespace DescribedNetwork

variable {T : Type*}

/-- **The contraction over `ℕ[V]`** of a network whose entries are lists of coefficients of
`1, V, V ^ 2, …`. -/
@[expose] noncomputable def polyContraction (entry : T → List Bool → List ℕ)
    (G : DescribedNetwork T) : ℕ[X] :=
  G.contraction fun t bs => ofCoeffList (entry t bs)

/-- **The contraction in `B_{P,ℓ} = (ℤ / 2 ^ P)[V] / (V ^ ℓ)`**, as its `ℓ` coefficients in
`[0, 2 ^ P)`: the coefficients below `ℓ` of the contraction over `ℕ[V]`, modulo `2 ^ P`. -/
@[expose] noncomputable def truncContraction (entry : T → List Bool → List ℕ) (P ℓ : ℕ)
    (G : DescribedNetwork T) : List ℕ :=
  (List.range ℓ).map fun j => (G.polyContraction entry).coeff j % 2 ^ P

/-- The image of the contraction over `ℕ[V]` in `B_{P,ℓ}` is the contraction of the images. -/
theorem truncHom_polyContraction (entry : T → List Bool → List ℕ) (P ℓ : ℕ)
    (G : DescribedNetwork T) :
    truncHom P ℓ (G.polyContraction entry) =
      G.contraction fun t bs => truncHom P ℓ (ofCoeffList (entry t bs)) :=
  map_contraction _ _ G

/-- **The contraction depends only on the entries in `B_{P,ℓ}`**: entries whose coefficients
below `ℓ` agree modulo `2 ^ P` have the same truncated contraction. -/
theorem truncContraction_congr {entry entry' : T → List Bool → List ℕ} {P ℓ : ℕ}
    (G : DescribedNetwork T)
    (h : ∀ t bs, ∀ i < ℓ, (entry t bs).getD i 0 % 2 ^ P = (entry' t bs).getD i 0 % 2 ^ P) :
    G.truncContraction entry P ℓ = G.truncContraction entry' P ℓ := by
  have hG : truncHom P ℓ (G.polyContraction entry) = truncHom P ℓ (G.polyContraction entry') := by
    rw [truncHom_polyContraction, truncHom_polyContraction]
    congr 1
    funext t bs
    exact truncHom_eq_iff.mpr fun j hj => by simpa only [coeff_ofCoeffList] using h t bs j hj
  refine List.map_congr_left fun j hj => truncHom_eq_iff.mp hG j (List.mem_range.mp hj)

/-- Cutting the entries to their first `ℓ` coefficients does not change the truncated
contraction. -/
theorem truncContraction_cutCoeffs (entry : T → List Bool → List ℕ) (P ℓ : ℕ)
    (G : DescribedNetwork T) :
    G.truncContraction (fun t bs => cutCoeffs ℓ (entry t bs)) P ℓ = G.truncContraction entry P ℓ :=
  truncContraction_congr G fun t bs i hi => by rw [getD_cutCoeffs _ hi]

/-- **The degree bound**: if every entry has at most `ℓ` coefficients, the contraction over
`ℕ[V]` has degree at most `(ℓ - 1) k` for `k` vertices. -/
theorem natDegree_polyContraction_le {entry : T → List Bool → List ℕ} {ℓ : ℕ}
    (G : DescribedNetwork T) (h : ∀ t bs, (entry t bs).length ≤ ℓ) :
    (G.polyContraction entry).natDegree ≤ (ℓ - 1) * G.vertices.length := by
  refine natDegree_sum_le_of_forall_le _ _ fun x _ => (natDegree_list_prod_le _).trans ?_
  rw [List.map_map]
  refine (List.sum_le_length_nsmul _ (ℓ - 1) fun d hd => ?_).trans (by simp [mul_comm])
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hd
  exact (natDegree_ofCoeffList_le _).trans (Nat.sub_le_sub_right (h _ _) 1)

end DescribedNetwork

/-! ### Specialization at a point of `A_P` -/

/-- The descriptor of a vertex of a network specialized at a point: the original descriptor with
the precision `P`, the truncation order `ℓ`, the coefficients `fl` of the modulus and the point
`ζ`, a coefficient list of `A_P = (ℤ / 2 ^ P)[U] / (f)`. -/
abbrev SpecDesc (T : Type*) : Type _ := T × ℕ × ℕ × List ℕ × List ℕ

/-- The first `ℓ` coefficients of a list, each as a constant coefficient list of `A_P`. -/
@[expose] def constCoeffs (ℓ : ℕ) (c : List ℕ) : List (List ℕ) :=
  (List.range ℓ).map fun i => [c.getD i 0]

variable {T : Type*}

/-- **The entry of a specialized descriptor** `(t, P, ℓ, fl, ζ)`: the value at `ζ` in `A_P`, by
Horner's rule, of the first `ℓ` coefficients of the entry of `t`. -/
@[expose] def specEntry (entry : T → List Bool → List ℕ) :
    SpecDesc T → List Bool → List ℕ
  | (t, P, ℓ, fl, ζ), bs => peval P fl (constCoeffs ℓ (entry t bs)) ζ

/-- Constant coefficient lists represent the polynomial of the coefficients in `A_p`. -/
theorem pval_constCoeffs (p ℓ : ℕ) (fl c : List ℕ) :
    pval p fl (constCoeffs ℓ c) =
      (ofCoeffList (cutCoeffs ℓ c)).map (Nat.castRingHom (Ring p fl)) := by
  ext j
  rw [NativeRecovery.coeff_pval, coeff_map, coeff_ofCoeffList]
  by_cases hj : j < ℓ
  · rw [constCoeffs, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      List.getElem_range, val_singleton, getD_cutCoeffs _ hj, eq_natCast]
  · rw [List.getD_eq_default _ _ (by simpa [constCoeffs] using hj),
      List.getD_eq_default _ _ (by simpa using hj), val_nil, map_zero]

/-- **A specialized entry is the evaluation at the point** of the polynomial of the first `ℓ`
coefficients. -/
theorem val_specEntry (entry : T → List Bool → List ℕ) (t : T) (P ℓ : ℕ) (fl ζ : List ℕ)
    (bs : List Bool) :
    val P fl (specEntry entry (t, P, ℓ, fl, ζ) bs) =
      ((ofCoeffList (cutCoeffs ℓ (entry t bs))).map (Nat.castRingHom (Ring P fl))).eval
        (val P fl ζ) := by
  rw [specEntry, peval_eq, pval_constCoeffs]

namespace DescribedNetwork

/-- **The network specialized at a point `ζ`**: the same ports, with each descriptor `t`
replaced by `(t, P, ℓ, fl, ζ)`. -/
@[expose] def specNet (P ℓ : ℕ) (fl ζ : List ℕ) (G : DescribedNetwork T) :
    DescribedNetwork (SpecDesc T) :=
  ⟨G.numEdges, G.vertices.map fun v => (v.1, (v.2, P, ℓ, fl, ζ))⟩

@[simp] theorem numEdges_specNet (P ℓ : ℕ) (fl ζ : List ℕ) (G : DescribedNetwork T) :
    (specNet P ℓ fl ζ G).numEdges = G.numEdges := rfl

@[simp] theorem vertices_specNet (P ℓ : ℕ) (fl ζ : List ℕ) (G : DescribedNetwork T) :
    (specNet P ℓ fl ζ G).vertices = G.vertices.map fun v => (v.1, (v.2, P, ℓ, fl, ζ)) := rfl

/-- The contraction of a specialized network, for any evaluator, is that of the original network
with the evaluator read at the specialized descriptors. -/
theorem contraction_specNet {R : Type*} [CommSemiring R] (eval : SpecDesc T → List Bool → R)
    (P ℓ : ℕ) (fl ζ : List ℕ) (G : DescribedNetwork T) :
    (specNet P ℓ fl ζ G).contraction eval = G.contraction fun t bs => eval (t, P, ℓ, fl, ζ) bs := by
  simp only [contraction, vertices_specNet, List.map_map, Function.comp_def]
  rfl

/-- **Specialization is evaluation**: the contraction in `A_P` of the network specialized at `ζ`
is the contraction over `ℕ[V]` of the entries cut to `ℓ` coefficients, evaluated at `ζ`. -/
theorem val_contraction_specNet (entry : T → List Bool → List ℕ) (P ℓ : ℕ) (fl ζ : List ℕ)
    (G : DescribedNetwork T) :
    (specNet P ℓ fl ζ G).contraction (fun d bs => val P fl (specEntry entry d bs)) =
      ((G.polyContraction fun t bs => cutCoeffs ℓ (entry t bs)).map
        (Nat.castRingHom (Ring P fl))).eval (val P fl ζ) := by
  rw [contraction_specNet]
  have h := map_contraction ((evalRingHom (val P fl ζ)).comp
    (mapRingHom (Nat.castRingHom (Ring P fl))))
    (fun t bs => ofCoeffList (cutCoeffs ℓ (entry t bs))) G
  simp only [RingHom.comp_apply, coe_evalRingHom, coe_mapRingHom] at h
  rw [polyContraction, h]
  simp only [val_specEntry]

end DescribedNetwork

/-! ### Recovery by interpolation -/

/-- **Reading the truncated contraction off an interpolant**: interpolate the values `ys` at the
points `pts` and take the constant coordinates, modulo `2 ^ P`, of the first `ℓ` coefficients. -/
@[expose] def interpRecover (P ℓ : ℕ) (fl : List ℕ) (pts ys : List (List ℕ)) : List ℕ :=
  (List.range ℓ).map fun j => ((interp P fl pts ys).getD j []).getD 0 0 % 2 ^ P

/-- An irreducible modulus has positive degree. -/
theorem length_pos_of_irreducible {fl : List ℕ}
    (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2)))) : 0 < fl.length := by
  refine Nat.pos_of_ne_zero fun h => hirr.not_isUnit ?_
  simp [monicOf, h]

/-- **Recovery from values at points with unit differences.** If `Z` over `ℕ` has degree below the
number of points, the points have unit differences in `A_P`, and `ys` are the values of `Z` at
them, then reading off the interpolant gives the coefficients of `Z` below `ℓ` modulo `2 ^ P`. -/
theorem interpRecover_eq {P ℓ : ℕ} {fl : List ℕ}
    (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2)))) {pts ys : List (List ℕ)}
    (hunit : Pairwise fun i j : Fin pts.length =>
      IsUnit (val P fl (pts.getD i []) - val P fl (pts.getD j [])))
    {Z : ℕ[X]} (hdeg : Z.natDegree < pts.length)
    (hys : ∀ i < pts.length, val P fl (ys.getD i []) =
      (Z.map (Nat.castRingHom (Ring P fl))).eval (val P fl (pts.getD i []))) :
    interpRecover P ℓ fl pts ys = (List.range ℓ).map fun j => Z.coeff j % 2 ^ P := by
  set Z' := Z.map (Nat.castRingHom (Ring P fl))
  set ζ : Fin pts.length → Ring P fl := fun i => val P fl (pts.getD i [])
  -- The native interpolant is the interpolant of the values, which is `Z'`.
  obtain ⟨g, hg⟩ := NativeRecovery.exists_pval_interp_eq_add hirr (RingHom.id _) ζ hunit pts rfl
    (fun _ => rfl) (fun i => val P fl (ys.getD i [])) ys P fun _ => ⟨0, by simp⟩
  have h2 : (2 : Ring P fl) ^ P = 0 := by exact_mod_cast natCast_two_pow (p := P) (fl := fl)
  rw [h2, C_0, zero_mul, add_zero, Polynomial.map_id] at hg
  have hdeg' : Z'.degree < #(univ : Finset (Fin pts.length)) := by
    rw [card_univ, Fintype.card_fin]
    exact (degree_map_le.trans degree_le_natDegree).trans_lt (by exact_mod_cast hdeg)
  have hZ : Z' = Lagrange.ringInterpolate univ ζ fun i => val P fl (ys.getD i []) := by
    conv_lhs => rw [Lagrange.eq_ringInterpolate (fun i _ j _ hij => hunit hij) hdeg']
    congr 1
    funext i
    exact (hys i i.2).symm
  have hpval : pval P fl (interp P fl pts ys) = Z' := hg.trans hZ.symm
  refine List.map_congr_left fun j _ => ?_
  have hval : val P fl ((interp P fl pts ys).getD j []) = val P fl [Z.coeff j] := by
    rw [← NativeRecovery.coeff_pval, hpval, val_singleton, coeff_map, eq_natCast]
  simpa using mod_eq_of_val_eq hval (length_pos_of_irreducible hirr)

/-- **The binary digits are interpolation points of `A_P`.** The binary digits below
`e = fl.length` of `0, …, n - 1`, for `n ≤ 2 ^ e` and `f` irreducible modulo `2`, have unit
differences in `A_P`. -/
theorem isUnit_val_sub_digits {P : ℕ} {fl : List ℕ}
    (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2)))) {n : ℕ}
    (hn : n ≤ 2 ^ fl.length) :
    Pairwise fun i j : Fin ((List.range n).map (FastContraction.digits fl.length)).length =>
      IsUnit (val P fl (((List.range n).map (FastContraction.digits fl.length)).getD i []) -
        val P fl (((List.range n).map (FastContraction.digits fl.length)).getD j [])) :=
  fun i j hij => by
    have h := (pairwise_isUnit_liftO_sub_digits hirr hn hij).map
      (AdjoinRoot.reduction (monic_monicOf fl) hirr P)
    rwa [map_sub, reduction_liftO, reduction_liftO] at h

namespace DescribedNetwork

/-- The number `(ℓ - 1) k + 1` of interpolation points for truncation order `ℓ` and `k`
vertices. -/
@[expose] def pointCount (ℓ : ℕ) (G : DescribedNetwork T) : ℕ := (ℓ - 1) * G.vertices.length + 1

/-- **The truncated contraction from the specialized contractions.** At points with unit
differences in `A_P`, more than `(ℓ - 1) k` of them, if `ys` are the contractions in `A_P` of the
network specialized at the points, reading off the interpolant gives the truncated contraction. -/
theorem interpRecover_eq_truncContraction {entry : T → List Bool → List ℕ} {P ℓ : ℕ}
    {fl : List ℕ} (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    (G : DescribedNetwork T) {pts ys : List (List ℕ)}
    (hunit : Pairwise fun i j : Fin pts.length =>
      IsUnit (val P fl (pts.getD i []) - val P fl (pts.getD j [])))
    (hlen : (ℓ - 1) * G.vertices.length < pts.length)
    (hys : ∀ i < pts.length, val P fl (ys.getD i []) =
      (specNet P ℓ fl (pts.getD i []) G).contraction fun d bs => val P fl (specEntry entry d bs)) :
    interpRecover P ℓ fl pts ys = G.truncContraction entry P ℓ := by
  rw [← truncContraction_cutCoeffs]
  exact interpRecover_eq hirr hunit
    ((natDegree_polyContraction_le G fun _ _ => (length_cutCoeffs _ _).le).trans_lt hlen)
    fun i hi => (hys i hi).trans (val_contraction_specNet entry P ℓ fl _ G)

/-- **The reduction to `ℓ = 1` over `A_P`**: contract, with `core`, the network specialized at
each of the `(ℓ - 1) k + 1` binary-digit points of `A_P` for the modulus `fl`, and read the
truncated contraction off the interpolant. The input of `core` is the precision, the modulus, the
number `r` of rows and the specialized network. -/
@[expose] def interpContract (core : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) → List ℕ)
    (fl : List ℕ) (P ℓ r : ℕ) (G : DescribedNetwork T) : List ℕ :=
  interpRecover P ℓ fl ((List.range (pointCount ℓ G)).map (FastContraction.digits fl.length))
    (((List.range (pointCount ℓ G)).map (FastContraction.digits fl.length)).map fun ζ =>
      core (P, fl, r, specNet P ℓ fl ζ G))

/-- **The reduction is correct.** If `f` is irreducible modulo `2`, `A_P` has at least
`(ℓ - 1) k + 1` residues, and `core` computes the contraction in `A_P` of the network specialized
at each digit point, then `interpContract` is the truncated contraction. -/
theorem interpContract_eq {entry : T → List Bool → List ℕ}
    {core : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) → List ℕ} {fl : List ℕ} {P ℓ r : ℕ}
    (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    (G : DescribedNetwork T) (hn : pointCount ℓ G ≤ 2 ^ fl.length)
    (hcore : ∀ k < pointCount ℓ G,
      val P fl (core (P, fl, r, specNet P ℓ fl (FastContraction.digits fl.length k) G)) =
        (specNet P ℓ fl (FastContraction.digits fl.length k) G).contraction
          fun d bs => val P fl (specEntry entry d bs)) :
    interpContract core fl P ℓ r G = G.truncContraction entry P ℓ := by
  refine interpRecover_eq_truncContraction hirr G (isUnit_val_sub_digits hirr hn)
    (by simp [pointCount]) fun i hi => ?_
  have hi' : i < pointCount ℓ G := by simpa using hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_map,
    List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  exact hcore i hi'

end DescribedNetwork

end Cslib.Circuits.Frontier
