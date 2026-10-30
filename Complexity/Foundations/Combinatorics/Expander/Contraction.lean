/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Lazy

/-!
# Contraction through bounded vertex fibers

Represent the vertices of a graph by occupied slots in `W × I`, with an executable partial
inverse. Contract each fiber to its vertex in `W`, moving the slot into the edge label. Empty
slots carry self-loops. The new degree is `|I|` times the original degree, and no enumeration or
choice is used by the rotation program.

When every fiber is inhabited, the contraction retains edge expansion. Applying the existing
lazy Cheeger bound gives a spectral gap depending only on `|I|` and the original gap. This is
the size-adjustment step needed when a constructive expander tower supplies only selected
vertex counts. Quotient/remainder indexing also contracts `Fin m` to `Fin n` whenever
`n ≤ m ≤ k*n`. Numbering the tower's vertices and certifying uniform efficiency remain separate.

## Main definitions

* `Cslib.RotationMap.contractDart`: move the slot of a represented vertex into its edge label.
* `Cslib.RotationMap.contractRot`: the functional rotation program.
* `Cslib.RotationMap.contract`: contraction with self-loops in unoccupied slots.
* `Cslib.RotationMap.finSlotEncode`, `Cslib.RotationMap.finSlotDecode`: executable indexing.
* `Cslib.RotationMap.contractFin`: contraction of an indexed graph using those maps.

## Main results

* `Cslib.RotationMap.card_interedges_le_contract`: original crossing darts survive contraction.
* `Cslib.RotationMap.le_card_interedges_compl_contract`: inhabited fibers retain edge expansion.
* `Cslib.RotationMap.spectralExpansion_contract_lazy_le`: laziness gives a spectral gap with
  loss depending only on the number of slots.
* `Cslib.RotationMap.spectralExpansion_contractFin_lazy_le`: the indexed specialization.

## References

The spectral consequence uses the lazy Cheeger inequality from
[S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
applications*][HooryLinialWigderson2006].
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset

variable {V W I D : Type*}

/-- Move the slot of a represented vertex into its edge label. -/
def contractDart (encode : V → W × I) (p : V × D) : W × (I × D) :=
  let target := encode p.1
  (target.1, (target.2, p.2))

/-- Decode an occupied slot, rotate there, and encode the result; unused slots are self-loops. -/
def contractRot (encode : V → W × I) (decode : W × I → Option V)
    (rotate : V × D → V × D) (p : W × (I × D)) : W × (I × D) :=
  (decode (p.1, p.2.1)).elim p fun v => contractDart encode (rotate (v, p.2.2))

variable (encode : V → W × I) (decode : W × I → Option V)
  (h : Function.IsPartialInv encode decode)

include h in
/-- An occupied dart executes the original rotation and retains both return labels. -/
theorem contractRot_contractDart (rotate : V × D → V × D) (p : V × D) :
    contractRot encode decode rotate (contractDart encode p) =
      contractDart encode (rotate p) := by
  simp [contractRot, contractDart, h.eq]

/-- Contract the occupied slots over each vertex, completing the degree with self-loops. -/
@[reducible]
def contract (G : RotationMap V D) : RotationMap W (I × D) where
  rot := contractRot encode decode G.rot
  rot_involutive := by
    rintro ⟨w, i, d⟩
    cases hd : decode (w, i) with
    | none => simp [contractRot, hd]
    | some v =>
      have he := (h v (w, i)).mp hd
      have hp : (w, (i, d)) = contractDart encode (v, d) := by
        simp [contractDart, he]
      rw [hp, contractRot_contractDart _ _ h, contractRot_contractDart _ _ h, G.rot_rot]

variable (G : RotationMap V D)

/-- The rotation map of `contract encode decode h G` decodes the slot, rotates in `G`, and
re-encodes the resulting vertex, leaving an unoccupied slot as a self-loop. -/
theorem rot_contract (p : W × (I × D)) :
    (contract encode decode h G).rot p =
      (decode (p.1, p.2.1)).elim p fun v => contractDart encode (G.rot (v, p.2.2)) :=
  rfl

include h in
/-- On an occupied slot `contractDart encode p`, the rotation map of `contract encode decode h G`
rotates `p` in `G` and re-encodes the resulting dart. -/
@[simp]
theorem rot_contract_contractDart (p : V × D) :
    (contract encode decode h G).rot (contractDart encode p) = contractDart encode (G.rot p) :=
  contractRot_contractDart encode decode h G.rot p

/-- The neighbor of an occupied slot is the image of its original neighbor. -/
theorem neighbor_contract (v : V) (d : D) :
    (contract encode decode h G).neighbor (encode v).1 ((encode v).2, d) =
      (encode (G.neighbor v d)).1 :=
  congrArg Prod.fst (rot_contract_contractDart encode decode h G (v, d))

include h in
/-- Distinct original darts remain distinct after moving the slot into the label. -/
private theorem contractDart_injective : Function.Injective (contractDart (D := D) encode) := by
  rintro ⟨v, d⟩ ⟨v', d'⟩ he
  apply Prod.ext
  · apply h.injective
    exact Prod.ext (congrArg (fun p : W × (I × D) => p.1) he)
      (congrArg (fun p : W × (I × D) => p.2.1) he)
  · exact congrArg (fun p => p.2.2) he

variable [Fintype V] [Fintype I] [Fintype D] [DecidableEq V] [DecidableEq W]

/-- Every original edge crossing between lifted sets gives a distinct edge of the contraction.
The inequality also permits loops arising from unused slots when the two sets overlap. -/
theorem card_interedges_le_contract (S T : Finset W) :
    #(G.interedges {v | (encode v).1 ∈ S} {v | (encode v).1 ∈ T}) ≤
      #((contract encode decode h G).interedges S T) := by
  apply card_le_card_of_injOn (contractDart encode)
  · intro p hp
    simp only [mem_coe, mem_interedges, mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, by simpa only [contractDart, neighbor_contract] using hp.2⟩
  · exact (contractDart_injective encode decode h).injOn

variable [Fintype W]

omit [DecidableEq V] in
/-- If each new vertex has an original representative, contraction retains the original
unnormalized edge-expansion lower bound. -/
theorem le_card_interedges_compl_contract
    (hcover : Function.Surjective (fun v => (encode v).1)) {S : Finset W}
    (hS : 2 * #S ≤ Fintype.card W) :
    (1 - G.spectralExpansion) * Fintype.card D * #S / 2 ≤
      #((contract encode decode h G).interedges S Sᶜ) := by
  classical
  have hcard (T : Finset W) : #T ≤ #{v | (encode v).1 ∈ T} := by
    apply card_le_card_of_surjOn (fun v => (encode v).1)
    intro w hw
    obtain ⟨v, hv⟩ := hcover w
    exact ⟨v, by simpa only [mem_coe, mem_filter, mem_univ, true_and, hv] using hw, hv⟩
  let A : Finset V := {v | (encode v).1 ∈ S}
  have hAc : Aᶜ = ({v | (encode v).1 ∈ Sᶜ} : Finset V) := by ext; simp [A]
  have hcross := card_interedges_le_contract encode decode h G S Sᶜ
  rw [← hAc] at hcross
  have hgap : 0 ≤ 1 - G.spectralExpansion := sub_nonneg.mpr G.spectralExpansion_le_one
  refine le_trans (b := (#(G.interedges A Aᶜ) : ℝ)) ?_ (Nat.cast_le.mpr hcross)
  by_cases hA : 2 * #A ≤ Fintype.card V
  · refine le_trans ?_ (G.le_card_interedges_compl_of_two_mul_card_le hA)
    gcongr
    exact_mod_cast hcard S
  · have hA' : 2 * #Aᶜ ≤ Fintype.card V := by
      have := card_add_card_compl A
      lia
    have hSS : #S ≤ #Sᶜ := by
      have := card_add_card_compl S
      lia
    have hc : #S ≤ #Aᶜ := by rw [hAc]; exact hSS.trans (hcard Sᶜ)
    rw [G.card_interedges_comm A Aᶜ]
    have hb := G.le_card_interedges_compl_of_two_mul_card_le hA'
    rw [compl_compl] at hb
    refine le_trans ?_ hb
    gcongr

omit [DecidableEq V] [DecidableEq W] in
/-- Contracting inhabited fibers with at most `|I|` slots and then making the walk lazy gives
spectral expansion at most `1 - (1 - λ(G))² / (16 |I|²)`. -/
theorem spectralExpansion_contract_lazy_le [Nontrivial W] [Nonempty I] [Nonempty D]
    (hcover : Function.Surjective (fun v => (encode v).1)) :
    (contract encode decode h G).lazy.spectralExpansion ≤
      1 - (1 - G.spectralExpansion) ^ 2 / (16 * Fintype.card I ^ 2) := by
  classical
  have hgap : 0 ≤ 1 - G.spectralExpansion := sub_nonneg.mpr G.spectralExpansion_le_one
  have hbound := spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl
      (contract encode decode h G)
      (c := (1 - G.spectralExpansion) * Fintype.card D / 2) (by positivity)
      (fun S hS => by
        simpa only [div_mul_eq_mul_div] using
          le_card_interedges_compl_contract encode decode h G hcover hS)
  refine hbound.trans_eq ?_
  rw [Fintype.card_prod, Nat.cast_mul]
  have hI : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := I)
  have hD : (Fintype.card D : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := D)
  field_simp
  ring

section FiniteIndices

variable {m n k : ℕ}

/-- Place consecutive indices in columns of height `n`, using at most `k` slots per vertex. -/
def finSlotEncode (hcap : m ≤ k * n) (v : Fin m) : Fin n × Fin k :=
  ((Fin.castLE hcap v).modNat, (Fin.castLE hcap v).divNat)

/-- Decode a column and slot, rejecting unused slots beyond the original vertex count. -/
def finSlotDecode (p : Fin n × Fin k) : Option (Fin m) :=
  if hp : (finProdFinEquiv (p.2, p.1)).val < m then
    some ⟨(finProdFinEquiv (p.2, p.1)).val, hp⟩
  else none

/-- Quotient/remainder indexing and a checked multiply/add are partial inverses. -/
theorem isPartialInv_finSlots (hcap : m ≤ k * n) :
    Function.IsPartialInv (finSlotEncode hcap) (finSlotDecode (m := m)) := by
  intro v p
  constructor
  · intro hdecode
    unfold finSlotDecode at hdecode
    split at hdecode
    · have hv := Option.some.inj hdecode
      have he : Fin.castLE hcap v = finProdFinEquiv (p.2, p.1) := by
        apply Fin.ext
        exact (congrArg Fin.val hv).symm
      change Prod.swap (finProdFinEquiv.symm (Fin.castLE hcap v)) = p
      rw [he, Equiv.symm_apply_apply]
      rfl
    · contradiction
  · intro hencode
    have he : Fin.castLE hcap v = finProdFinEquiv (p.2, p.1) := by
      apply finProdFinEquiv.symm.injective
      rw [Equiv.symm_apply_apply]
      change Prod.swap (finSlotEncode hcap v) = (p.2, p.1)
      rw [hencode]
      rfl
    have hp : (finProdFinEquiv (p.2, p.1)).val < m := by rw [← he]; exact v.isLt
    simp only [finSlotDecode, hp, dite_true]
    apply congrArg some
    exact Fin.ext (congrArg (fun j : Fin (k * n) => j.val) he.symm)

/-- If there are at least `n` original vertices, every new vertex has a representative. -/
private theorem finSlotEncode_fst_surjective (hcap : m ≤ k * n) (hsize : n ≤ m) :
    Function.Surjective (fun v => (finSlotEncode hcap v).1) := by
  intro w
  refine ⟨⟨w.val, w.isLt.trans_le hsize⟩, ?_⟩
  apply Fin.ext
  exact Nat.mod_eq_of_lt w.isLt

/-- Contract an indexed graph from `m` vertices to `n` vertices, using `k` slots per vertex. -/
def contractFin (G : RotationMap (Fin m) D) (hcap : m ≤ k * n) :
    RotationMap (Fin n) (Fin k × D) :=
  contract (finSlotEncode hcap) finSlotDecode (isPartialInv_finSlots hcap) G

/-- An indexed graph with `n ≤ m ≤ k*n` contracts to `n ≥ 2` vertices. After adding laziness,
the gap bound depends on `k`, not on `m` or `n`, and is positive when the original gap is. -/
theorem spectralExpansion_contractFin_lazy_le [Nonempty D] (G : RotationMap (Fin m) D)
    (hcap : m ≤ k * n) (hsize : n ≤ m) (hn : 2 ≤ n) :
    (G.contractFin hcap).lazy.spectralExpansion ≤
      1 - (1 - G.spectralExpansion) ^ 2 / (16 * k ^ 2) := by
  have hk : 0 < k := by
    by_contra h
    have hk := Nat.eq_zero_of_not_pos h
    subst k
    simp only [zero_mul] at hcap
    lia
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  simpa only [contractFin, Fintype.card_fin] using
    spectralExpansion_contract_lazy_le (finSlotEncode hcap) finSlotDecode
      (isPartialInv_finSlots hcap) G (finSlotEncode_fst_surjective hcap hsize)

end FiniteIndices

end Cslib.RotationMap
