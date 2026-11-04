/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.CauchyModes
import all Complexity.Computability.Circuit.Frontier.TensorNetwork.CauchyModes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Fin

/-!
# Entries of the child networks

The child networks of an active call of the contraction algorithm of [OpenAI2026ETH] are kept
implicit: a packet vertex has up to `2 L` ports, so its table would have `2 ^ (2 L)` entries. The
source evaluates an entry by expanding the product of the at most `L` affine row factors of the
packet, enumerating the choices of a local term or a mode in each factor, keeping those with the
required exponents, and multiplying by the powers of the substituted modes (§D.4.6, p. 63). This
file gives that evaluation as an explicit formula on the data of the packet and proves that it is
the entry of the child network of `TensorNetwork.cauchyModeSplitting`.

**Coefficient extraction along a list** (`TensorNetwork.listCoeff`). For a list of factors, each
a function `T : Option M → R` (the local term at `none` and the coefficient of the mode `Z` at
`some Z`), and exponents `γ` on the modes of a finite set `F`, the coefficient of `∏ Z ^ γ Z` in
`∏ (T none + ∑ Z ∈ F, T (some Z) Z)` is computed recursively: the first factor contributes its
local term, or one of the modes still needed. This is the coefficient of a block
(`TensorNetwork.ModeSplitting.blockCoeff_eq_listCoeff`) for any mode splitting, with the rows of
the block in any order.

**Packet entries** (`TensorNetwork.packetEntry`). For the Cauchy modes of an active node, the
entry of the packet vertex of the child of group `g` at the packet `q` depends only on:
* the parameters `κ`, `ζ`, `a`, `i` and `t` of the node;
* whether the two symbols `sym q` of the packet are `g` and whether they differ;
* the exponents of the modes `(q, y₀, b)` of the packet;
* the slots and bits of its row ports and of its column ports, as two lists.

The local form of a row is a sum of kernel values over the column ports set to one
(`TensorNetwork.packetLocalForm`), a mode coefficient is the geometric expansion term (D.12)
(`TensorNetwork.packetModeCoeff`), and a mode value is a sum of powers `j ^ b` over the column ports
of its tile set to one (`TensorNetwork.packetModeValue`). The main result
(`TensorNetwork.packetTensor_cauchyModeSplitting`, and for the child itself
`TensorNetwork.child_tensor_inr_cauchyModeSplitting`) is that this formula is the packet tensor.
A retained vertex keeps its tensor (`TensorNetwork.ModeSplitting.child_tensor_inl`).

The formula commutes with ring homomorphisms (`TensorNetwork.map_packetEntry`) when `2` is
nilpotent, so an evaluation in one coefficient ring, such as the coefficient lists of
`(ℤ / 2 ^ p)[U] / (f)`, gives the entry in every ring it maps to, such as the quotients of the
recursion.

This file also supplies the field lemmas of `TensorNetwork.cauchyModeSplitting` beyond its sides,
groups and packets (`TensorNetwork.cauchyModeSplitting_localPart`,
`TensorNetwork.cauchyModeSplitting_coeff`, `TensorNetwork.cauchyModeSplitting_form` and the mode
packets, sources and targets), through `import all`, since the definition is not exposed.

## Main definitions

* `Cslib.Circuits.Frontier.TensorNetwork.listCoeff`: coefficient extraction along a list.
* `Cslib.Circuits.Frontier.TensorNetwork.packetLocalForm`,
  `Cslib.Circuits.Frontier.TensorNetwork.packetModeCoeff`,
  `Cslib.Circuits.Frontier.TensorNetwork.packetModeValue`,
  `Cslib.Circuits.Frontier.TensorNetwork.packetRowTerm`: the terms of a packet entry.
* `Cslib.Circuits.Frontier.TensorNetwork.packetEntry`: the entry of a packet vertex.

## Main results

* `Cslib.Circuits.Frontier.TensorNetwork.sum_eq_listCoeff`: the recursion sums over all choices.
* `Cslib.Circuits.Frontier.TensorNetwork.ModeSplitting.blockCoeff_eq_listCoeff`: block
  coefficients by the recursion.
* `Cslib.Circuits.Frontier.TensorNetwork.packetTensor_cauchyModeSplitting`,
  `Cslib.Circuits.Frontier.TensorNetwork.child_tensor_inr_cauchyModeSplitting`: the packet entries
  of the children.
* `Cslib.Circuits.Frontier.TensorNetwork.map_packetEntry`: packet entries commute with ring
  homomorphisms.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.5–§D.4.6,
  (D.12)–(D.16), pp. 62–63.
-/

public section

namespace Cslib.Circuits.Frontier

open Finset

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

namespace TensorNetwork

/-! ### The remaining fields of the Cauchy mode splitting -/

section Fields

variable {R V E G P : Type*} [CommRing R] [DecidableEq G] [DecidableEq P]
  {N : TensorNetwork R Bool V E} {group : V → G} {packet : E → P} {slot : E → ℕ}
  {sym : P → G × G} {i : ℕ}
  (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true)
  (htgt : ∀ e, side (N.tgt e) = false)
  (horient : ∀ e, (group (N.src e), group (N.tgt e)) =
    if (slot e).testBit i then (sym (packet e)).swap else sym (packet e))
  {a : ℕ} (hslot : ∀ e, slot e < 2 ^ a) (hia : i < a) (κ : ℤ₍₂₎ →+* R) (ζ : R) {p : ℕ}
  (hp : (2 : R) ^ p = 0) {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) (hti : (2 : ℤ) ^ i ∣ t)
  (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t)

/-- The local part of the Cauchy mode splitting: the Cauchy matrix between ports of the same
group. -/
@[simp] theorem cauchyModeSplitting_localPart [Fintype P] :
    (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').localPart =
      fun e e' => if group (N.tgt e') = group (N.src e) then
        cauchyValueMatrix κ ζ a t packet slot e e' else 0 := by
  unfold cauchyModeSplitting; rfl

/-- The packet of the mode `(q, y₀, b)` is `q`. -/
@[simp] theorem cauchyModeSplitting_modePacket [Fintype P] :
    (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').modePacket =
      Prod.fst := by
  unfold cauchyModeSplitting; rfl

/-- The source group of the mode `(q, y₀, b)`: the group of the columns of its tile. -/
@[simp] theorem cauchyModeSplitting_source [Fintype P] :
    (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').source =
      fun Z => if (Z.2.1 : ℕ).testBit i then (sym Z.1).1 else (sym Z.1).2 := by
  unfold cauchyModeSplitting; rfl

/-- The target group of the mode `(q, y₀, b)`: the other group of its packet. -/
@[simp] theorem cauchyModeSplitting_target [Fintype P] :
    (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').target =
      fun Z => if (Z.2.1 : ℕ).testBit i then (sym Z.1).2 else (sym Z.1).1 := by
  unfold cauchyModeSplitting; rfl

/-- The mode coefficients are `cauchyModeCoeff`. -/
@[simp] theorem cauchyModeSplitting_coeff [Fintype P] :
    (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').coeff =
      cauchyModeCoeff κ ζ a i t packet slot sym := by
  unfold cauchyModeSplitting; rfl

/-- The mode forms are `cauchyModeForm`. -/
@[simp] theorem cauchyModeSplitting_form [Fintype P] :
    (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').form =
      cauchyModeForm R i packet slot sym := by
  unfold cauchyModeSplitting; rfl

end Fields

/-! ### Coefficient extraction along a list -/

section ListCoeff

variable {R M : Type*} [CommRing R] [DecidableEq M]

/-- **Coefficient extraction along a list of factors.** Each factor is a function
`T : Option M → R`, standing for `T none + ∑ Z ∈ F, T (some Z) Z`. The value at the exponents `γ`
is the coefficient of `∏ Z ∈ F, Z ^ γ Z` in the product of the factors: the first factor
contributes its local term `T none`, or the coefficient of a mode `Z` with `γ Z ≠ 0`, lowering
`γ Z` by one, and the empty product has the coefficient `1` at zero exponents. -/
@[expose] def listCoeff (F : Finset M) : List (Option M → R) → (M → ℕ) → R
  | [], γ => if ∀ Z ∈ F, γ Z = 0 then 1 else 0
  | T :: ts, γ => T none * listCoeff F ts γ +
      ∑ Z ∈ F, if γ Z = 0 then 0 else
        T (some Z) * listCoeff F ts (Function.update γ Z (γ Z - 1))

@[simp] theorem listCoeff_nil (F : Finset M) (γ : M → ℕ) :
    listCoeff (R := R) F [] γ = if ∀ Z ∈ F, γ Z = 0 then 1 else 0 :=
  rfl

theorem listCoeff_cons (F : Finset M) (T : Option M → R) (ts : List (Option M → R))
    (γ : M → ℕ) :
    listCoeff F (T :: ts) γ = T none * listCoeff F ts γ +
      ∑ Z ∈ F, if γ Z = 0 then 0 else
        T (some Z) * listCoeff F ts (Function.update γ Z (γ Z - 1)) :=
  rfl

/-- The count condition after choosing the mode `Z ∈ F` in the first factor. -/
private theorem count_cons_iff {F : Finset M} {Z : M} (hZ : Z ∈ F) (c γ : M → ℕ) :
    (∀ Z' ∈ F, (if Z = Z' then 1 else 0) + c Z' = γ Z') ↔
      γ Z ≠ 0 ∧ ∀ Z' ∈ F, c Z' = Function.update γ Z (γ Z - 1) Z' := by
  constructor
  · intro h
    have hz := h Z hZ
    simp only [↓reduceIte] at hz
    refine ⟨by omega, fun Z' hZ' => ?_⟩
    by_cases hZZ : Z' = Z
    · subst hZZ
      rw [Function.update_self]
      omega
    · have := h Z' hZ'
      simp only [Ne.symm hZZ, ↓reduceIte, zero_add] at this
      rw [Function.update_of_ne hZZ, this]
  · rintro ⟨h0, h⟩ Z' hZ'
    by_cases hZZ : Z' = Z
    · subst hZZ
      simp only [↓reduceIte, h Z' hZ', Function.update_self]
      omega
    · simp only [Ne.symm hZZ, ↓reduceIte, zero_add, h Z' hZ', Function.update_of_ne hZZ]

/-- Picks of `Fin.cons o φ`: those of `o`, and those of `φ`. -/
private theorem card_cons_eq {n : ℕ} (o : Option M) (φ : Fin n → Option M) (Z : M) :
    #{j | (Fin.cons o φ : Fin (n + 1) → Option M) j = some Z} =
      (if o = some Z then 1 else 0) + #{j | φ j = some Z} := by
  rw [Fin.card_filter_univ_succ']
  simp only [Fin.cons_zero, Fin.cons_succ]

omit [DecidableEq M] in
/-- A sum over the functions on `Fin (n + 1)` splits off the value at `0`. -/
private theorem sum_pi_fin_succ [Fintype M] {n : ℕ} (f : (Fin (n + 1) → Option M) → R) :
    ∑ φ, f φ = ∑ o : Option M, ∑ φ : Fin n → Option M, f (Fin.cons o φ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Option M) _ _ fun x => rfl).symm

/-- **The recursion sums over all choices.** For factors `T j` indexed by `Fin n`, the sum over
the ways `φ` to pick in each factor its local term or a mode of `F`, each mode `Z` picked `γ Z`
times, of the product of the picked terms is `listCoeff`. -/
theorem sum_eq_listCoeff [Fintype M] (F : Finset M) :
    ∀ (n : ℕ) (T : Fin n → Option M → R) (γ : M → ℕ),
      (∑ φ : Fin n → Option M,
        if (∀ j Z, φ j = some Z → Z ∈ F) ∧ ∀ Z ∈ F, #{j | φ j = some Z} = γ Z then
          ∏ j, T j (φ j) else 0) = listCoeff F (List.ofFn T) γ
  | 0, T, γ => by
    rw [Fintype.sum_unique, List.ofFn_zero, listCoeff_nil]
    simp only [IsEmpty.forall_iff, true_and, Finset.univ_eq_empty, filter_empty, card_empty,
      Finset.prod_empty]
    by_cases h : ∀ Z ∈ F, γ Z = 0
    · rw [ite_eq_left h, ite_eq_left fun Z hZ => (h Z hZ).symm]
    · rw [ite_eq_right h, ite_eq_right fun h' => h fun Z hZ => (h' Z hZ).symm]
  | n + 1, T, γ => by
    rw [sum_pi_fin_succ, Fintype.sum_option, List.ofFn_succ, listCoeff_cons]
    congr 1
    · -- The local term of the first factor.
      rw [← sum_eq_listCoeff F n (fun j => T j.succ) γ, mul_sum]
      refine sum_congr rfl fun φ _ => ?_
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.forall_fin_succ, card_cons_eq, reduceCtorEq, false_implies, implies_true, true_and,
        ↓reduceIte, zero_add, mul_ite, mul_zero]
    · -- A mode in the first factor.
      rw [← sum_subset (subset_univ F) fun Z _ hZ => ?_]
      · refine sum_congr rfl fun Z hZ => ?_
        rw [← sum_eq_listCoeff F n (fun j => T j.succ), mul_sum]
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
          Fin.forall_fin_succ, card_cons_eq, Option.some.injEq, forall_eq', hZ, true_and,
          count_cons_iff hZ]
        by_cases h0 : γ Z = 0
        · simp only [h0, ne_eq, not_true_eq_false, false_and, and_false, ↓reduceIte,
            sum_const_zero]
        · simp only [h0, ne_eq, not_false_eq_true, true_and, ↓reduceIte, mul_ite, mul_zero]
      · refine sum_eq_zero fun φ _ => ite_eq_right ?_
        simp only [Fin.forall_fin_succ, Fin.cons_zero, Option.some.injEq, forall_eq', not_and]
        exact fun h => absurd h.1 hZ

/-- `listCoeff` along the image of an injective map of modes. -/
theorem listCoeff_map {M' : Type*} [DecidableEq M'] (f : M' ↪ M) (F : Finset M') :
    ∀ (ts : List (Option M → R)) (γ : M → ℕ),
      listCoeff (F.map f) ts γ = listCoeff F (ts.map fun T => T ∘ Option.map f) (γ ∘ f)
  | [], γ => by simp
  | T :: ts, γ => by
    rw [List.map_cons, listCoeff_cons, listCoeff_cons, sum_map, listCoeff_map f F ts γ]
    refine congrArg _ (sum_congr rfl fun Z _ => ?_)
    rw [listCoeff_map f F ts, Function.update_comp_eq_of_injective _ f.injective]
    rfl

end ListCoeff

/-! ### Block coefficients by the recursion -/

namespace ModeSplitting

variable {R V E G P M : Type*} [CommRing R] [Fintype M] {N : TensorNetwork R Bool V E}
  {W : Matrix E E R} (S : ModeSplitting N W G P M) [Fintype E] [DecidableEq E] [DecidableEq P]
  [DecidableEq G] [DecidableEq M]

/-- **Block coefficients by the recursion.** For a list `l` of the row ports of the block `k`,
without repetition and in any order, the coefficient of a mode monomial in the product of the
affine factors of the block is `listCoeff` along the terms of the rows of `l`. -/
theorem blockCoeff_eq_listCoeff (k : P × G) (β : M → ℕ) (Y X : E → Bool) {l : List E}
    (hl : l.Nodup) (hmem : ∀ e, e ∈ l ↔ S.rowBlock e = k) :
    S.blockCoeff k β Y X =
      listCoeff {Z | S.targetBlock Z = k} (l.map fun e => S.choiceTerm Y X e) β := by
  let σ : Fin l.length ≃ {e // S.rowBlock e = k} :=
    Equiv.ofBijective (fun j => ⟨l.get j, (hmem _).1 (List.get_mem _ _)⟩)
      ⟨fun j j' h => (hl.get_inj_iff).1 (congrArg Subtype.val h), fun e => by
        obtain ⟨j, hj⟩ := List.mem_iff_get.1 ((hmem e.1).2 e.2)
        exact ⟨j, Subtype.ext hj⟩⟩
  have hl' : (l.map fun e => S.choiceTerm Y X e) =
      List.ofFn fun j => S.choiceTerm Y X (σ j).1 := by
    conv_lhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  have hcard (φ : {e // S.rowBlock e = k} → Option M) (Z : M) :
      #{j | φ (σ j) = some Z} = #{e | φ e = some Z} :=
    Finset.card_equiv σ fun j => by simp only [mem_filter, mem_univ, true_and]
  rw [hl', ← sum_eq_listCoeff]
  refine Fintype.sum_equiv (σ.arrowCongr (Equiv.refl _)).symm _ _ fun φ => ?_
  simp only [Equiv.arrowCongr_symm, Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl,
    Function.comp_apply, id_eq, Equiv.symm_symm, mem_filter, mem_univ, true_and]
  refine if_congr (and_congr ⟨fun h j Z => h (σ j) Z, fun h e Z => ?_⟩
    (forall_congr' fun Z => imp_congr_right fun _ => ?_)) ?_ rfl
  · simpa using h (σ.symm e) Z
  · rw [hcard]
  · exact (Fintype.prod_equiv σ _ _ fun j => rfl).symm

/-- A retained vertex of a child keeps its tensor, reading the row bits on its edges when it is a
row and the column bits when it is a column. -/
theorem child_tensor_inl [DecidableEq V] (β : M → ℕ) (g : G) (v : {v // S.group v = g})
    (y : {e // S.group (N.src e) = g} ⊕ {e // S.group (N.tgt e) = g} → Bool) :
    (S.child β g).tensor (.inl v) y =
      if S.side v.1 then
        N.tensor v.1 fun e => if h : N.src e = v.1 then y (.inl ⟨e, h ▸ v.2⟩) else false
      else
        N.tensor v.1 fun e => if h : N.tgt e = v.1 then y (.inr ⟨e, h ▸ v.2⟩) else false :=
  rfl

/-- A packet vertex of a child has the packet tensor at the bits of its ports. -/
theorem child_tensor_inr [DecidableEq V] (β : M → ℕ) (g : G) (q : P)
    (y : {e // S.group (N.src e) = g} ⊕ {e // S.group (N.tgt e) = g} → Bool) :
    (S.child β g).tensor (.inr q) y =
      S.packetTensor β q g
        (fun e => if h : S.group (N.src e) = g then y (.inl ⟨e, h⟩) else false)
        (fun e => if h : S.group (N.tgt e) = g then y (.inr ⟨e, h⟩) else false) :=
  rfl

end ModeSplitting

/-! ### Packet entries -/

section Packet

variable {R : Type*} [CommRing R]

/-- The local form of a row port in slot `x` of a packet: the sum of the kernel values
`W_{y - x}(T)` over its column ports `(y, X_y)` set to one. -/
@[expose] noncomputable def packetLocalForm (κ : ℤ₍₂₎ →+* R) (ζ : R) (a : ℕ) (t : ℤ)
    (cols : List (ℕ × Bool)) (x : ℕ) : R :=
  (cols.map fun c => if c.2 then kernelValue κ ζ a t ((c.1 : ℤ) - x) else 0).sum

/-- The coefficient of the mode `(y₀, b)` of a packet in the form of a row port in slot `x`: when
the two symbols of the packet differ and digit `i` of `x` is that of `y₀`, the term
`W_{y₀ - x}(T) ρ ^ b` of the geometric expansion (D.12); otherwise zero. -/
@[expose] noncomputable def packetModeCoeff (κ : ℤ₍₂₎ →+* R) (ζ : R) (a i : ℕ) (t : ℤ)
    (differ : Bool) {p : ℕ} (x : ℕ) (Z : Fin (2 ^ (i + 1)) × Fin p) : R :=
  if differ = true ∧ x.testBit i = (Z.1 : ℕ).testBit i then
    kernelValue κ ζ a t ((Z.1 : ℤ) - x) * crossRatio a i t ((Z.1 : ℤ) - x) ζ ^ (Z.2 : ℕ)
  else 0

variable (R) in
/-- The value `L_Z(X)` of the mode `Z = (y₀, b)` of a packet on its column ports: when the two
symbols of the packet differ, the sum of `j ^ b` over the column ports in slots
`y = y₀ + 2 ^ (i + 1) j` set to one. -/
@[expose] def packetModeValue (i : ℕ) (differ : Bool) {p : ℕ}
    (cols : List (ℕ × Bool)) (Z : Fin (2 ^ (i + 1)) × Fin p) : R :=
  (cols.map fun c => if c.2 = true ∧ differ = true ∧ c.1 % 2 ^ (i + 1) = (Z.1 : ℕ) then
    ((c.1 / 2 ^ (i + 1) : ℕ) : R) ^ (Z.2 : ℕ) else 0).sum

/-- The terms of the affine factor of a row port `(x, Y_x)` of a packet: its local term at `none`,
and the coefficient of the mode `Z` at `some Z`. -/
@[expose] noncomputable def packetRowTerm (κ : ℤ₍₂₎ →+* R) (ζ : R) (a i : ℕ) (t : ℤ)
    (differ : Bool) {p : ℕ} (cols : List (ℕ × Bool)) (r : ℕ × Bool) :
    Option (Fin (2 ^ (i + 1)) × Fin p) → R
  | none => affineFactor r.2 (packetLocalForm κ ζ a t cols r.1)
  | some Z => affineSign r.2 * packetModeCoeff κ ζ a i t differ r.1 Z

/-- Whether the modes of the tile `y₀` of a packet target the group `g`, given whether the two
symbols of the packet are `g`: the target is the second symbol when digit `i` of `y₀` is `1`. -/
@[expose] def modeTargets (i : ℕ) (e₁ e₂ : Bool) (y₀ : ℕ) : Bool :=
  if y₀.testBit i then e₂ else e₁

/-- Whether the modes of the tile `y₀` of a packet have the source `g`: the source is the first
symbol when digit `i` of `y₀` is `1`. -/
@[expose] def modeSources (i : ℕ) (e₁ e₂ : Bool) (y₀ : ℕ) : Bool :=
  if y₀.testBit i then e₁ else e₂

/-- **The entry of a packet vertex** of a child (§D.4.6, p. 63). The packet has row ports
`rows` and column ports `cols`, each a slot and a bit; `e₁` and `e₂` say whether the two symbols
of the packet are the group of the child, and `differ` whether they differ; `β` gives the exponents
of the modes `(y₀, b)` of the packet. The entry is the coefficient, at the exponents of the modes
targeting the group, of the product of the affine row factors, times the powers of the values of
the modes with the group as source. -/
@[expose] noncomputable def packetEntry (κ : ℤ₍₂₎ →+* R) (ζ : R) (a i : ℕ) (t : ℤ) {p : ℕ}
    (e₁ e₂ differ : Bool) (β : Fin (2 ^ (i + 1)) × Fin p → ℕ) (rows cols : List (ℕ × Bool)) : R :=
  listCoeff {Z | modeTargets i e₁ e₂ Z.1 = true}
      (rows.map (packetRowTerm κ ζ a i t differ cols)) β *
    ∏ Z with modeSources i e₁ e₂ Z.1 = true, packetModeValue R i differ cols Z ^ β Z

end Packet

/-! ### Packet entries under ring homomorphisms -/

section Map

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Kernel values commute with ring homomorphisms. -/
theorem map_kernelValue (ψ : R →+* S) (κ : ℤ₍₂₎ →+* R) (ζ : R) (a : ℕ) (t d : ℤ) :
    ψ (kernelValue κ ζ a t d) = kernelValue (ψ.comp κ) (ψ ζ) a t d :=
  Polynomial.hom_eval₂ _ _ _ _

/-- A ring homomorphism maps the inverse of a unit to the inverse of its image. -/
private theorem map_ringInverse (ψ : R →+* S) {u : R} (hu : IsUnit u) :
    ψ (Ring.inverse u) = Ring.inverse (ψ u) := by
  obtain ⟨w, rfl⟩ := hu
  have h : ψ (w : R) = ((Units.map (ψ : R →* S) w : Sˣ) : S) := rfl
  rw [Ring.inverse_unit, h, Ring.inverse_unit, Units.coe_map_inv]
  rfl

/-- **Cross ratios commute with ring homomorphisms** when `2` is nilpotent and
`2 ^ (i + 1) ∤ t - d₀` with `i ≤ a`, so that the inverted element is a unit. -/
theorem map_crossRatio (ψ : R →+* S) {n : ℕ} (hn : (2 : R) ^ n = 0) {a i : ℕ} (hia : i ≤ a)
    {t d₀ : ℤ} (hcross : ¬ (2 : ℤ) ^ (i + 1) ∣ t - d₀) (ζ : R) :
    ψ (crossRatio a i t d₀ ζ) = crossRatio a i t d₀ (ψ ζ) := by
  obtain ⟨hvi, ⟨c, hc⟩, -⟩ := two_adic_split hcross
  have hU : IsUnit ((((t - d₀) / 2 ^ padicValInt 2 (t - d₀) : ℤ) : R) +
      2 ^ (a + 1 - padicValInt 2 (t - d₀)) * ζ) := by
    rw [hc, show a + 1 - padicValInt 2 (t - d₀) = a - padicValInt 2 (t - d₀) + 1 by omega,
      pow_succ]
    convert isUnit_one_add_two_mul hn ((c : R) + 2 ^ (a - padicValInt 2 (t - d₀)) * ζ) using 1
    push_cast
    ring
  rw [crossRatio, crossRatio, map_mul, map_pow, map_ofNat, map_ringInverse ψ hU, map_add,
    map_mul, map_pow, map_ofNat, map_intCast]

/-- Mode coefficients commute with ring homomorphisms when `2` is nilpotent, at a grid point `t`
of valuation `i ≤ a`. -/
theorem map_packetModeCoeff (ψ : R →+* S) {n : ℕ} (hn : (2 : R) ^ n = 0) (κ : ℤ₍₂₎ →+* R)
    (ζ : R) {a i : ℕ} (hia : i ≤ a) {t : ℤ} (hti : (2 : ℤ) ^ i ∣ t)
    (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t) (differ : Bool) {p : ℕ} (x : ℕ)
    (Z : Fin (2 ^ (i + 1)) × Fin p) :
    ψ (packetModeCoeff κ ζ a i t differ x Z) =
      packetModeCoeff (ψ.comp κ) (ψ ζ) a i t differ x Z := by
  unfold packetModeCoeff
  split_ifs with h
  · rw [map_mul, map_pow, map_kernelValue,
      map_crossRatio ψ hn hia (not_dvd_sub_sub_of_testBit_eq hti hti' Z.1.isLt h.2)]
  · exact map_zero ψ

/-- Local forms commute with ring homomorphisms. -/
theorem map_packetLocalForm (ψ : R →+* S) (κ : ℤ₍₂₎ →+* R) (ζ : R) (a : ℕ) (t : ℤ)
    (cols : List (ℕ × Bool)) (x : ℕ) :
    ψ (packetLocalForm κ ζ a t cols x) = packetLocalForm (ψ.comp κ) (ψ ζ) a t cols x := by
  rw [packetLocalForm, packetLocalForm, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply, apply_ite ψ, map_zero, map_kernelValue]

/-- Mode values commute with ring homomorphisms. -/
theorem map_packetModeValue (ψ : R →+* S) (i : ℕ) (differ : Bool) {p : ℕ}
    (cols : List (ℕ × Bool)) (Z : Fin (2 ^ (i + 1)) × Fin p) :
    ψ (packetModeValue R i differ cols Z) = packetModeValue S i differ cols Z := by
  rw [packetModeValue, packetModeValue, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_apply, apply_ite ψ, map_zero, map_pow, map_natCast]

/-- `listCoeff` commutes with ring homomorphisms. -/
theorem map_listCoeff {M : Type*} [DecidableEq M] (ψ : R →+* S) (F : Finset M) :
    ∀ (ts : List (Option M → R)) (γ : M → ℕ),
      ψ (listCoeff F ts γ) = listCoeff F (ts.map fun T => ψ ∘ T) γ
  | [], γ => by simp only [listCoeff_nil, List.map_nil, apply_ite ψ, map_one, map_zero]
  | T :: ts, γ => by
    rw [List.map_cons, listCoeff_cons, listCoeff_cons, map_add, map_mul, map_listCoeff ψ F ts,
      map_sum]
    refine congrArg _ (sum_congr rfl fun Z _ => ?_)
    rw [apply_ite ψ, map_zero, map_mul, map_listCoeff ψ F ts]
    rfl

/-- **Packet entries commute with ring homomorphisms** when `2` is nilpotent, at a grid point `t`
of valuation `i ≤ a`. So a packet entry evaluated in one coefficient ring gives the entry in
every ring it maps to. -/
theorem map_packetEntry (ψ : R →+* S) {n : ℕ} (hn : (2 : R) ^ n = 0) (κ : ℤ₍₂₎ →+* R) (ζ : R)
    {a i : ℕ} (hia : i ≤ a) {t : ℤ} (hti : (2 : ℤ) ^ i ∣ t) (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t)
    {p : ℕ} (e₁ e₂ differ : Bool) (β : Fin (2 ^ (i + 1)) × Fin p → ℕ)
    (rows cols : List (ℕ × Bool)) :
    ψ (packetEntry κ ζ a i t e₁ e₂ differ β rows cols) =
      packetEntry (ψ.comp κ) (ψ ζ) a i t e₁ e₂ differ β rows cols := by
  rw [packetEntry, packetEntry, map_mul, map_listCoeff, map_prod, List.map_map]
  congr 1
  · congr 1
    refine List.map_congr_left fun r _ => funext fun o => ?_
    cases o with
    | none =>
      cases hr : r.2 <;>
        simp only [Function.comp_apply, packetRowTerm, affineFactor, hr, Bool.false_eq_true,
          ↓reduceIte, map_sub, map_one, map_packetLocalForm]
    | some Z =>
      cases hr : r.2 <;>
        simp only [Function.comp_apply, packetRowTerm, affineSign, hr, Bool.false_eq_true,
          ↓reduceIte, map_mul, map_neg, map_one, map_packetModeCoeff ψ hn κ ζ hia hti hti']
  · refine prod_congr rfl fun Z _ => ?_
    rw [map_pow, map_packetModeValue]

end Map

/-! ### The packet entries of the Cauchy children -/

section Cauchy

variable {R V E G P : Type*} [CommRing R] [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq G]
  [DecidableEq P] {N : TensorNetwork R Bool V E} {group : V → G} {packet : E → P} {slot : E → ℕ}
  {sym : P → G × G} {i : ℕ}
  (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true)
  (htgt : ∀ e, side (N.tgt e) = false)
  (horient : ∀ e, (group (N.src e), group (N.tgt e)) =
    if (slot e).testBit i then (sym (packet e)).swap else sym (packet e))
  {a : ℕ} (hslot : ∀ e, slot e < 2 ^ a) (hia : i < a) (κ : ℤ₍₂₎ →+* R) (ζ : R) {p : ℕ}
  (hp : (2 : R) ^ p = 0) {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) (hti : (2 : ℤ) ^ i ∣ t)
  (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t)

/-- The modes of the packet `q`, as modes of the splitting. -/
private def packetModes (q : P) : Fin (2 ^ (i + 1)) × Fin p ↪ P × Fin (2 ^ (i + 1)) × Fin p :=
  ⟨fun Z => (q, Z), fun _ _ h => (Prod.ext_iff.1 h).2⟩

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq G] [DecidableEq P] in
private theorem packetModes_apply (q : P) (Z : Fin (2 ^ (i + 1)) × Fin p) :
    packetModes q Z = (q, Z) :=
  rfl

omit [Fintype E] [DecidableEq E] in
/-- The modes targeting the block `(q, g)` are the modes of `q` whose tiles target `g`. -/
private theorem targetBlock_eq_iff (q q' : P) (g : G) (Z : Fin (2 ^ (i + 1)) × Fin p) :
    (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').targetBlock
        (q', Z) = (q, g) ↔
      q' = q ∧ modeTargets i (decide ((sym q).1 = g)) (decide ((sym q).2 = g)) Z.1 = true := by
  simp only [ModeSplitting.targetBlock, cauchyModeSplitting_modePacket,
    cauchyModeSplitting_target, Prod.mk.injEq, modeTargets]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by split_ifs at h ⊢ <;> simp_all⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by split_ifs at h ⊢ <;> simp_all⟩

omit [Fintype E] [DecidableEq E] in
/-- The modes with the source block `(q, g)` are the modes of `q` whose tiles have source `g`. -/
private theorem sourceBlock_eq_iff (q q' : P) (g : G) (Z : Fin (2 ^ (i + 1)) × Fin p) :
    (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').sourceBlock
        (q', Z) = (q, g) ↔
      q' = q ∧ modeSources i (decide ((sym q).1 = g)) (decide ((sym q).2 = g)) Z.1 = true := by
  simp only [ModeSplitting.sourceBlock, cauchyModeSplitting_modePacket,
    cauchyModeSplitting_source, Prod.mk.injEq, modeSources]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by split_ifs at h ⊢ <;> simp_all⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by split_ifs at h ⊢ <;> simp_all⟩

omit [DecidableEq E] in
/-- The local form of a row port of the block `(q, g)` is `packetLocalForm` on the column ports
of the packet `q` in the group `g`. -/
private theorem localForm_cauchyModeSplitting (q : P) (g : G) (X : E → Bool) {cols : List E}
    (hcols : cols.Nodup) (hcols' : ∀ e, e ∈ cols ↔ packet e = q ∧ group (N.tgt e) = g) {e : E}
    (he : packet e = q) (heg : group (N.src e) = g) :
    (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').localForm X e =
      packetLocalForm κ ζ a t (cols.map fun e => (slot e, X e)) (slot e) := by
  classical
  rw [ModeSplitting.localForm, packetLocalForm, List.map_map, ← List.sum_toFinset _ hcols,
    ← sum_subset (subset_univ _) fun e' _ he' => ?_]
  · refine sum_congr rfl fun e' he' => ?_
    obtain ⟨hq, hg⟩ := (hcols' e').1 (List.mem_toFinset.1 he')
    simp only [cauchyModeSplitting_localPart, cauchyValueMatrix, hg, heg, he, hq, ↓reduceIte,
      Function.comp_apply, mul_ite, mul_one, mul_zero]
  · have h' : ¬ (packet e' = q ∧ group (N.tgt e') = g) := fun h =>
      he' (List.mem_toFinset.2 ((hcols' e').2 h))
    simp only [cauchyModeSplitting_localPart, cauchyValueMatrix, heg, he]
    split_ifs with h₁ h₂ <;> first | simp only [zero_mul] | exact absurd ⟨h₂.symm, h₁⟩ h'

omit [DecidableEq E] in
/-- The value of a mode `(q, Z)` with source `g` is `packetModeValue` on the column ports of the
packet `q` in the group `g`. -/
private theorem modeValue_cauchyModeSplitting (q : P) (g : G) (X : E → Bool) {cols : List E}
    (hcols : cols.Nodup) (hcols' : ∀ e, e ∈ cols ↔ packet e = q ∧ group (N.tgt e) = g)
    (Z : Fin (2 ^ (i + 1)) × Fin p)
    (hZ : (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').source
      (q, Z) = g) :
    (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').modeValue X (q, Z) =
      packetModeValue R i (decide ((sym q).1 ≠ (sym q).2)) (cols.map fun e => (slot e, X e)) Z := by
  classical
  set S := cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti'
  rw [ModeSplitting.modeValue, packetModeValue, List.map_map, ← List.sum_toFinset _ hcols,
    ← sum_subset (subset_univ _) fun e' _ he' => ?_]
  · refine sum_congr rfl fun e' he' => ?_
    obtain ⟨hq, -⟩ := (hcols' e').1 (List.mem_toFinset.1 he')
    simp only [S, cauchyModeSplitting_form, cauchyModeForm, hq, true_and, Function.comp_apply,
      decide_eq_true_eq]
    by_cases hX : X e' <;> simp [hX]
  · -- A column port outside the block contributes nothing.
    have h' : ¬ (packet e' = q ∧ group (N.tgt e') = g) := fun h =>
      he' (List.mem_toFinset.2 ((hcols' e').2 h))
    by_cases h0 : S.form (q, Z) e' = 0
    · rw [h0, zero_mul]
    · obtain ⟨hq, hg⟩ := S.form_ne_zero (q, Z) e' h0
      exact absurd ⟨hq.symm, hg.symm.trans hZ⟩ h'

/-- **The packet tensors of the Cauchy children.** For lists `rows` and `cols` of the row and
column ports of the packet `q` in the group `g`, without repetition and in any order, the packet
tensor of `cauchyModeSplitting` is `packetEntry` at their slots and bits. -/
theorem packetTensor_cauchyModeSplitting (β : P × Fin (2 ^ (i + 1)) × Fin p → ℕ) (q : P) (g : G)
    (Y X : E → Bool) {rows cols : List E} (hrows : rows.Nodup)
    (hrows' : ∀ e, e ∈ rows ↔ packet e = q ∧ group (N.src e) = g) (hcols : cols.Nodup)
    (hcols' : ∀ e, e ∈ cols ↔ packet e = q ∧ group (N.tgt e) = g) :
    (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').packetTensor β q g
        Y X =
      packetEntry κ ζ a i t (decide ((sym q).1 = g)) (decide ((sym q).2 = g))
        (decide ((sym q).1 ≠ (sym q).2)) (fun Z => β (q, Z)) (rows.map fun e => (slot e, Y e))
        (cols.map fun e => (slot e, X e)) := by
  set S := cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti'
  have htarget : ({Z | S.targetBlock Z = (q, g)} : Finset (P × Fin (2 ^ (i + 1)) × Fin p)) =
      ({Z | modeTargets i (decide ((sym q).1 = g)) (decide ((sym q).2 = g)) Z.1 = true} :
        Finset (Fin (2 ^ (i + 1)) × Fin p)).map (packetModes q) := by
    ext ⟨q', Z⟩
    simp only [S, mem_filter, mem_univ, true_and, mem_map, targetBlock_eq_iff, packetModes_apply,
      Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨Z, h, rfl, rfl⟩
    · rintro ⟨Z', h, rfl, rfl⟩
      exact ⟨rfl, h⟩
  have hsource : ({Z | S.sourceBlock Z = (q, g)} : Finset (P × Fin (2 ^ (i + 1)) × Fin p)) =
      ({Z | modeSources i (decide ((sym q).1 = g)) (decide ((sym q).2 = g)) Z.1 = true} :
        Finset (Fin (2 ^ (i + 1)) × Fin p)).map (packetModes q) := by
    ext ⟨q', Z⟩
    simp only [S, mem_filter, mem_univ, true_and, mem_map, sourceBlock_eq_iff, packetModes_apply,
      Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨Z, h, rfl, rfl⟩
    · rintro ⟨Z', h, rfl, rfl⟩
      exact ⟨rfl, h⟩
  rw [ModeSplitting.packetTensor, packetEntry, S.blockCoeff_eq_listCoeff (q, g) β Y X hrows
    (fun e => (hrows' e).trans (by rw [ModeSplitting.rowBlock, Prod.mk.injEq]; exact Iff.rfl)),
    htarget, listCoeff_map, hsource, prod_map,
    List.map_map, List.map_map]
  congr 1
  · congr 1
    refine List.map_congr_left fun e he => funext fun o => ?_
    obtain ⟨hq, hg⟩ := (hrows' e).1 he
    cases o with
    | none =>
      simp only [Function.comp_apply, Option.map_none, ModeSplitting.choiceTerm, packetRowTerm]
      rw [localForm_cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti' q g X
        hcols hcols' hq hg]
    | some Z =>
      simp only [Function.comp_apply, Option.map_some, ModeSplitting.choiceTerm, packetRowTerm,
        S, cauchyModeSplitting_coeff, cauchyModeCoeff, packetModeCoeff, packetModes_apply, hq,
        true_and, decide_eq_true_eq]
  · refine prod_congr rfl fun Z hZ => ?_
    have hZ' : S.source (q, Z) = g := congrArg Prod.snd
      ((sourceBlock_eq_iff side hsrc htgt horient hslot hia κ ζ hp ht hti hti' q q g Z).2
        ⟨rfl, (mem_filter.1 hZ).2⟩)
    rw [packetModes_apply, modeValue_cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht
      hti hti' q g X hcols hcols' Z hZ']

/-- **The packet entries of the Cauchy children** (§D.4.6, p. 63): the entry of the packet vertex
`q` of the child of group `g` at the bits `y` on its ports is `packetEntry` at the slots and bits
of its row ports and column ports, listed without repetition and in any order. -/
theorem child_tensor_inr_cauchyModeSplitting [DecidableEq V]
    (β : P × Fin (2 ^ (i + 1)) × Fin p → ℕ) (g : G) (q : P)
    (y : {e // (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').group
        (N.src e) = g} ⊕
      {e // (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').group
        (N.tgt e) = g} → Bool)
    {rows cols : List E} (hrows : rows.Nodup)
    (hrows' : ∀ e, e ∈ rows ↔ packet e = q ∧ group (N.src e) = g)
    (hcols : cols.Nodup) (hcols' : ∀ e, e ∈ cols ↔ packet e = q ∧ group (N.tgt e) = g) :
    ((cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').child β g).tensor
        (.inr q) y =
      packetEntry κ ζ a i t (decide ((sym q).1 = g)) (decide ((sym q).2 = g))
        (decide ((sym q).1 ≠ (sym q).2)) (fun Z => β (q, Z))
        (rows.map fun e => (slot e, if h : _ = g then y (.inl ⟨e, h⟩) else false))
        (cols.map fun e => (slot e, if h : _ = g then y (.inr ⟨e, h⟩) else false)) :=
  packetTensor_cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti' β q g _ _
    hrows hrows' hcols hcols'

end Cauchy

end TensorNetwork

end Cslib.Circuits.Frontier
