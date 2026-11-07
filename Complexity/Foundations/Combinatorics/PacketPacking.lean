/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.GreedySchedules
public import Complexity.Foundations.Data.BitString.Basic
import Complexity.Foundations.Data.BitString.Binary
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Packing the edges of a bipartite multigraph into packets

Lemma D.3 of [OpenAI2026ETH] (§D.4.2, pp. 58–59) labels the vertices on each side of a bipartite
multigraph by words in `[r]^a` and places its `M` edges into *packets* of `L = 2 ^ a` *slots*.
Edge `e` joins the row vertex `rowOf e` to the column vertex `colOf e`. A `Packing` records

* the row and column labels;
* for each edge its packet and slot, with no two edges in the same slot of the same packet
  (`Packing.injective`), so an edge occupies the same slot at its row and column ends and an
  unused slot has no ports;
* for each packet and coordinate `i` a pair of symbols `(σ, τ)`: an edge whose slot has binary
  digit `i` equal to `0` has row symbol `σ` and column symbol `τ` in coordinate `i`, and one
  whose digit is `1` has them the other way round (`Packing.labels_eq`). So the unordered pair
  of symbols is fixed in each packet and coordinate, and when the two symbols differ, digit `i`
  of the slot gives their orientation.

These are the structural properties (1)–(2) of Lemma D.3. The construction `packing` meets the
quantitative ones under the size hypotheses (D.6), `2 Δ D² ≤ M` and `L D ≤ M` with `D = r ^ (2a)`
the number of pairs of labels and `Δ` the maximum degree:

* (1) there are at most `3M / L` packets (`numPackets_packing_mul_le`);
* (3) in every coordinate, the vertices with a given symbol have at most `2M / r` ports on each
  side (`row_ports_packing_le`, `col_ports_packing_le`), which is within the `3M / r` of the
  source.

**Labels.** `rowLabels` and `colLabels` fix one whole label at a time by the method of conditional
expectations, minimizing the closed-form average `partialIncidencePotential` of the potential
`Φ = ∑_γ (X_γ - M / D)²`, where `X_γ` counts the edges with the pair of labels `γ`
(`Cslib.BalancedSchedules.greedyLabelPassBy`). Ties go to the first candidate in radix order
(`labelCandidates`), the order in which a machine streams the candidates by counting. For
independent uniform labels, `𝔼 Φ ≤ 2 M Δ` (`Cslib.BalancedSchedules.expect_incidence_potential_le`),
so the chosen labels have `Φ ≤ 2 M Δ` (`potential_labels_le`), and with `2 Δ D² ≤ M` every class
has at most `2M / D` edges (`occupancy_labels_mul_le`).

**Packets.** `Packing.ofLabels` packs the edges for any labels. Number the edges with each pair
of labels `γ` from zero in the order of `E` (`classIndex`), and pad each class to `h L` slots,
the largest class size rounded up to a multiple of `L` (`numBlocks`). An edge with number
`k = b L + o` goes to block `b`. In a coordinate where its two symbols differ, its slot digit is
their orientation; where they agree, it is the corresponding digit of `o`. Its packet is
determined by the block, the unordered pairs of symbols, and the digits of `o` in the
coordinates where the symbols differ. So each packet holds `2 ^ (a - a')` slots of each of the
`2 ^ a'` orientations of its pairs, as in the source, and there are `h D` packets.

The source's padded size `H_pad` is our `h L`. All constructions are executable finite
computations with mathematical correctness proofs. A native polynomial-time computation of
`packing` is in `Complexity/Computability/PolyTime/PacketPacking.lean`.

## Main definitions

* `Cslib.PacketPacking.Packing`: labels and an injective placement of the edges into slots of
  packets with the orientation property.
* `Cslib.PacketPacking.pairLabel`, `Cslib.PacketPacking.classIndex`,
  `Cslib.PacketPacking.numBlocks`: the pair of labels of an edge, its number within its class,
  and the number of blocks.
* `Cslib.PacketPacking.Packing.ofLabels`: the packing for given labels.
* `Cslib.PacketPacking.labelCandidates`: the candidate labels, in radix order.
* `Cslib.PacketPacking.rowLabels`, `Cslib.PacketPacking.colLabels`: the labels chosen by
  conditional expectations.
* `Cslib.PacketPacking.packing`: the packing of Lemma D.3.

## Main results

* `Cslib.PacketPacking.classIndex_lt_occupancy`, `Cslib.PacketPacking.classIndex_injective`:
  edges in a class are numbered injectively below the class size.
* `Cslib.PacketPacking.Packing.numPackets_ofLabels_mul_le`,
  `Cslib.PacketPacking.Packing.row_ports_ofLabels_le`,
  `Cslib.PacketPacking.Packing.col_ports_ofLabels_le`: the packet and port bounds from a bound on
  the class sizes.
* `Cslib.PacketPacking.potential_labels_le`, `Cslib.PacketPacking.occupancy_labels_mul_le`: the
  collision potential and class sizes of the chosen labels.
* `Cslib.PacketPacking.numPackets_packing_mul_le`, `Cslib.PacketPacking.row_ports_packing_le`,
  `Cslib.PacketPacking.col_ports_packing_le`: Lemma D.3 (1) and (3).
* `Cslib.PacketPacking.exists_packing`: Lemma D.3 as an existence statement.

## References

* [OpenAI2026ETH], Appendix D.4.2, Lemma D.3 and its proof, pp. 58–59, under (D.6), p. 58.
-/

public section

namespace Cslib.PacketPacking

open Finset Cslib.BalancedSchedules

variable {E R C : Type*}

/-! ### Packings -/

/-- A *packing* of the edges of a bipartite multigraph into packets of `2 ^ a` slots, where edge
`e` joins the row vertex `rowOf e` to the column vertex `colOf e`. It labels the vertices on
each side by words in `[r]^a`, places each edge in a slot of a packet with no two edges in the
same place, and gives each packet a pair of symbols in each coordinate. An edge whose slot has
binary digit `i` equal to `0` has the packet's pair as its row and column symbols in coordinate
`i`; one whose digit `i` is `1` has the pair swapped. -/
structure Packing (rowOf : E → R) (colOf : E → C) (a r : ℕ) where
  /-- The label of a row vertex. -/
  rowLabel : R → Fin a → Fin r
  /-- The label of a column vertex. -/
  colLabel : C → Fin a → Fin r
  /-- The number of packets. -/
  numPackets : ℕ
  /-- The packet of an edge. -/
  packet : E → Fin numPackets
  /-- The slot of an edge in its packet. -/
  slot : E → Fin (2 ^ a)
  /-- The pair of symbols of a packet in each coordinate, oriented as at slot `0`. -/
  symbols : Fin numPackets → Fin a → Fin r × Fin r
  /-- No two edges occupy the same slot of the same packet. -/
  injective : Function.Injective fun e => (packet e, slot e)
  /-- Digit `i` of the slot orients the packet's pair of symbols in coordinate `i`. -/
  labels_eq : ∀ e i, (rowLabel (rowOf e) i, colLabel (colOf e) i) =
    if (slot e : ℕ).testBit i then (symbols (packet e) i).swap else symbols (packet e) i

/-- The pair of labels of the row and column ends of an edge. -/
@[expose] def pairLabel (rowOf : E → R) (colOf : E → C) {a r : ℕ} (ρ : R → Fin a → Fin r)
    (κ : C → Fin a → Fin r) (e : E) : (Fin a → Fin r) × (Fin a → Fin r) :=
  (ρ (rowOf e), κ (colOf e))

/-! ### Numbering the edges within their classes -/

section Classes

variable [Fintype E] [LinearOrder E] (rowOf : E → R) (colOf : E → C) {a r : ℕ}
  (ρ : R → Fin a → Fin r) (κ : C → Fin a → Fin r)

/-- The number of an edge within its class: how many earlier edges have the same pair of labels. -/
@[expose] def classIndex (e : E) : ℕ :=
  #{e' | e' < e ∧ pairLabel rowOf colOf ρ κ e' = pairLabel rowOf colOf ρ κ e}

/-- The largest class size: one more than the largest number of an edge in its class, or zero
without edges. -/
@[expose] def maxLoad : ℕ :=
  univ.sup fun e => classIndex rowOf colOf ρ κ e + 1

/-- The number of blocks of `2 ^ a` slots needed for the largest class:
`⌈maxLoad / 2 ^ a⌉`. -/
@[expose] def numBlocks : ℕ :=
  (maxLoad rowOf colOf ρ κ + (2 ^ a - 1)) / 2 ^ a

/-- An edge is numbered below the size of its class. -/
theorem classIndex_lt_occupancy (e : E) :
    classIndex rowOf colOf ρ κ e <
      occupancy (pairLabel rowOf colOf ρ κ) (pairLabel rowOf colOf ρ κ e) := by
  rw [occupancy, Fintype.card_subtype, classIndex]
  refine Finset.card_lt_card ⟨fun e' he' => ?_, fun h => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at he' ⊢
    exact he'.2
  · have he := h (by simp : e ∈ ({e' | pairLabel rowOf colOf ρ κ e' =
      pairLabel rowOf colOf ρ κ e} : Finset E))
    simp at he

/-- Distinct edges in the same class have distinct numbers. -/
theorem classIndex_injective {e e' : E}
    (hlabel : pairLabel rowOf colOf ρ κ e = pairLabel rowOf colOf ρ κ e')
    (hindex : classIndex rowOf colOf ρ κ e = classIndex rowOf colOf ρ κ e') : e = e' := by
  -- An earlier edge of the class has strictly fewer predecessors in it.
  have key : ∀ {x y : E}, pairLabel rowOf colOf ρ κ x = pairLabel rowOf colOf ρ κ y → x < y →
      classIndex rowOf colOf ρ κ x < classIndex rowOf colOf ρ κ y := by
    intro x y hxy hlt
    refine Finset.card_lt_card ⟨fun z hz => ?_, fun h => ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hz ⊢
      exact ⟨hz.1.trans hlt, hz.2.trans hxy⟩
    · have hx := h (by simpa using ⟨hlt, hxy⟩ : x ∈ ({z | z < y ∧
        pairLabel rowOf colOf ρ κ z = pairLabel rowOf colOf ρ κ y} : Finset E))
      simp at hx
  rcases lt_trichotomy e e' with hlt | heq | hgt
  · exact absurd hindex (key hlabel hlt).ne
  · exact heq
  · exact absurd hindex (key hlabel.symm hgt).ne'

/-- An edge is numbered below the largest class size. -/
theorem classIndex_lt_maxLoad (e : E) : classIndex rowOf colOf ρ κ e < maxLoad rowOf colOf ρ κ :=
  Nat.lt_of_succ_le (Finset.le_sup (f := fun e => classIndex rowOf colOf ρ κ e + 1) (mem_univ e))

/-- The blocks hold the largest class. -/
theorem maxLoad_le_numBlocks_mul : maxLoad rowOf colOf ρ κ ≤ numBlocks rowOf colOf ρ κ * 2 ^ a := by
  have hL : 0 < 2 ^ a := Nat.two_pow_pos a
  have h := Nat.lt_div_mul_add (a := maxLoad rowOf colOf ρ κ + (2 ^ a - 1)) hL
  rw [numBlocks]
  generalize 2 ^ a = L at hL h ⊢
  generalize (maxLoad rowOf colOf ρ κ + (L - 1)) / L * L = q at h ⊢
  omega

/-- Rounding up to whole blocks adds fewer than `2 ^ a` slots. -/
theorem numBlocks_mul_le : numBlocks rowOf colOf ρ κ * 2 ^ a ≤ maxLoad rowOf colOf ρ κ + 2 ^ a := by
  have h := Nat.div_mul_le_self (maxLoad rowOf colOf ρ κ + (2 ^ a - 1)) (2 ^ a)
  rw [numBlocks]
  generalize (maxLoad rowOf colOf ρ κ + (2 ^ a - 1)) / 2 ^ a * 2 ^ a = q at h ⊢
  generalize 2 ^ a = L at h ⊢
  omega

/-- A bound `B` on the class sizes, in the form `X_γ D ≤ B`, bounds the largest class. -/
theorem maxLoad_mul_le {B : ℕ}
    (hocc : ∀ γ, occupancy (pairLabel rowOf colOf ρ κ) γ * r ^ (2 * a) ≤ B) :
    maxLoad rowOf colOf ρ κ * r ^ (2 * a) ≤ B := by
  rcases Nat.eq_zero_or_pos (r ^ (2 * a)) with hD | hD
  · rw [hD, Nat.mul_zero]
    exact Nat.zero_le _
  have hle : maxLoad rowOf colOf ρ κ ≤ B / r ^ (2 * a) := by
    refine Finset.sup_le fun e _ => ?_
    rw [Nat.le_div_iff_mul_le hD]
    exact (Nat.mul_le_mul_right _ (classIndex_lt_occupancy rowOf colOf ρ κ e)).trans (hocc _)
  exact (Nat.mul_le_mul_right _ hle).trans (Nat.div_mul_le_self _ _)

end Classes

/-! ### The packing for given labels -/

section OfLabels

variable [Fintype E] [LinearOrder E] (rowOf : E → R) (colOf : E → C) {a r : ℕ}
  (ρ : R → Fin a → Fin r) (κ : C → Fin a → Fin r)

/-- The digits of the slot of an edge. Where its row and column symbols differ, digit `i` is `1`
when the row symbol is the larger; where they agree, it is digit `i` of the number of the edge in
its class. -/
@[expose] def slotBits (e : E) (i : Fin a) : Bool :=
  if ρ (rowOf e) i = κ (colOf e) i then (classIndex rowOf colOf ρ κ e).testBit i
  else decide (κ (colOf e) i < ρ (rowOf e) i)

/-- The packet data of an edge: its block, and in each coordinate its sorted pair of symbols,
swapped when digit `i` of its number in its class is `1`. This determines the unordered pairs of
symbols and, where they differ, digit `i` of the number. -/
@[expose] def packetData (e : E) : ℕ × (Fin a → Fin r × Fin r) :=
  (classIndex rowOf colOf ρ κ e / 2 ^ a, fun i =>
    let x := ρ (rowOf e) i
    let y := κ (colOf e) i
    if (classIndex rowOf colOf ρ κ e).testBit i then (max x y, min x y) else (min x y, max x y))

/-- The packets: blocks, together with words of pairs of symbols, numbered in `Fin`. -/
@[expose] def packetEquiv (h a r : ℕ) :
    Fin h × (Fin a → Fin r × Fin r) ≃ Fin (h * (r * r) ^ a) :=
  (Equiv.prodCongr (Equiv.refl _)
    ((Equiv.arrowCongr (Equiv.refl _) finProdFinEquiv).trans finFunctionFinEquiv)).trans
    finProdFinEquiv

/-- The block of an edge is below the number of blocks. -/
theorem packetData_fst_lt (e : E) :
    (packetData rowOf colOf ρ κ e).1 < numBlocks rowOf colOf ρ κ := by
  have h1 := classIndex_lt_maxLoad rowOf colOf ρ κ e
  have h2 := maxLoad_le_numBlocks_mul rowOf colOf ρ κ
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)

/-- Digit `i` of the number of a bit string is its bit `i`. -/
private theorem testBit_equivFin (bits : Fin a → Bool) (i : Fin a) :
    (BitString.equivFin a bits : ℕ).testBit i = bits i := by
  rw [← BitString.equivFin_symm_apply, Equiv.symm_apply_apply]

/-- The orientation digit orients the sorted pair of two symbols. -/
private theorem pair_eq_orient {α : Type*} [LinearOrder α] (x y : α) (b : Bool) :
    (x, y) = if (if x = y then b else decide (y < x)) then (min x y, max x y).swap
      else (min x y, max x y) := by
  rcases lt_trichotomy x y with h | rfl | h
  · simp [h.ne, not_lt.mpr h.le, min_eq_left h.le, max_eq_right h.le]
  · cases b <;> simp
  · simp [h.ne', h, min_eq_right h.le, max_eq_left h.le]

/-- The sorted pair, swapped by a digit, and the orientation digit determine two symbols and the
digit. -/
private theorem orient_injective {α : Type*} [LinearOrder α] {x y x' y' : α} {b b' : Bool}
    (hp : (if b then (max x y, min x y) else (min x y, max x y)) =
      if b' then (max x' y', min x' y') else (min x' y', max x' y'))
    (hs : (if x = y then b else decide (y < x)) = if x' = y' then b' else decide (y' < x')) :
    x = x' ∧ y = y' ∧ b = b' := by
  simp only [min_def, max_def] at hp
  rcases lt_trichotomy x y with h1 | h1 | h1 <;> rcases lt_trichotomy x' y' with h2 | h2 | h2 <;>
    cases b <;> cases b' <;> grind

/-- **The packing for given labels.** -/
@[expose] def Packing.ofLabels : Packing rowOf colOf a r where
  rowLabel := ρ
  colLabel := κ
  numPackets := numBlocks rowOf colOf ρ κ * (r * r) ^ a
  packet e := packetEquiv _ a r
    (⟨(packetData rowOf colOf ρ κ e).1, packetData_fst_lt rowOf colOf ρ κ e⟩,
      (packetData rowOf colOf ρ κ e).2)
  slot e := BitString.equivFin a (slotBits rowOf colOf ρ κ e)
  symbols p i :=
    let q := ((packetEquiv _ a r).symm p).2 i
    (min q.1 q.2, max q.1 q.2)
  injective := by
    intro e e' hee'
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq] at hee'
    obtain ⟨⟨hblock, hpairs⟩, hslot⟩ := hee'
    have hi (i : Fin a) := orient_injective (congrFun hpairs i) (congrFun hslot i)
    have hlabel : pairLabel rowOf colOf ρ κ e = pairLabel rowOf colOf ρ κ e' :=
      Prod.ext (funext fun i => (hi i).1) (funext fun i => (hi i).2.1)
    refine classIndex_injective rowOf colOf ρ κ hlabel ?_
    have hmod : classIndex rowOf colOf ρ κ e % 2 ^ a = classIndex rowOf colOf ρ κ e' % 2 ^ a := by
      refine Nat.eq_of_testBit_eq fun j => ?_
      simp only [Nat.testBit_mod_two_pow]
      by_cases hj : j < a
      · simp only [hj, decide_true, Bool.true_and]
        exact (hi ⟨j, hj⟩).2.2
      · simp only [hj, decide_false, Bool.false_and]
    rw [← Nat.div_add_mod (classIndex rowOf colOf ρ κ e) (2 ^ a),
      ← Nat.div_add_mod (classIndex rowOf colOf ρ κ e') (2 ^ a), hmod]
    exact congrArg (· + _) (congrArg (2 ^ a * ·) hblock)
  labels_eq := by
    intro e i
    simp only [Equiv.symm_apply_apply, testBit_equivFin]
    have hsort : ∀ b : Bool, (fun q : Fin r × Fin r => (min q.1 q.2, max q.1 q.2))
        (if b then (max (ρ (rowOf e) i) (κ (colOf e) i), min (ρ (rowOf e) i) (κ (colOf e) i))
          else (min (ρ (rowOf e) i) (κ (colOf e) i), max (ρ (rowOf e) i) (κ (colOf e) i))) =
        (min (ρ (rowOf e) i) (κ (colOf e) i), max (ρ (rowOf e) i) (κ (colOf e) i)) := by
      intro b
      cases b <;> simp
    exact (pair_eq_orient _ _ _).trans (by rw [← hsort]; rfl)

/-- The number of pairs of labels is `r ^ (2a)`. -/
private theorem card_pairs : (r * r) ^ a = r ^ (2 * a) := by
  rw [← sq, ← pow_mul]

/-- **Lemma D.3 (1) from class sizes.** If every class has at most `2M / D` edges and
`L D ≤ M`, then there are at most `3M / L` packets. -/
theorem Packing.numPackets_ofLabels_mul_le
    (hocc : ∀ γ, occupancy (pairLabel rowOf colOf ρ κ) γ * r ^ (2 * a) ≤ 2 * Fintype.card E)
    (hM : 2 ^ a * r ^ (2 * a) ≤ Fintype.card E) :
    (Packing.ofLabels rowOf colOf ρ κ).numPackets * 2 ^ a ≤ 3 * Fintype.card E := by
  have hload := maxLoad_mul_le rowOf colOf ρ κ hocc
  have hblocks := Nat.mul_le_mul_right (r ^ (2 * a)) (numBlocks_mul_le rowOf colOf ρ κ)
  change numBlocks rowOf colOf ρ κ * (r * r) ^ a * 2 ^ a ≤ _
  rw [card_pairs, Nat.mul_right_comm]
  rw [Nat.add_mul] at hblocks
  omega

omit [LinearOrder E] in
/-- Edges with a pair of labels in `S` number at most `|S|` times the class size bound. -/
private theorem card_filter_mem_mul_le {α : Type*} [DecidableEq α] (γ : E → α)
    (S : Finset α) {D B : ℕ} (hocc : ∀ u, occupancy γ u * D ≤ B) :
    #{e | γ e ∈ S} * D ≤ #S * B := by
  rw [Finset.card_eq_sum_card_fiberwise (f := γ) (s := ({e | γ e ∈ S} : Finset E)) (t := S)
    (fun e he => (mem_filter.mp he).2), Finset.sum_mul, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun u _ => ?_
  refine le_trans (Nat.mul_le_mul_right _ (le_of_eq ?_)) (hocc u)
  rw [occupancy, Fintype.card_subtype]
  congr 1
  ext e
  simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
  rintro rfl
  assumption

/-- The words in `[r]^a` with a given symbol in a given coordinate number `r ^ (a - 1)`. -/
private theorem card_filter_apply_eq (i : Fin a) (σ : Fin r) :
    #{f : Fin a → Fin r | f i = σ} * r = r ^ a := by
  have h := Fintype.card_filter_piFinset_const_eq_of_mem (univ : Finset (Fin r)) i (mem_univ σ)
  rw [Fintype.piFinset_univ] at h
  rw [h, card_univ, Fintype.card_fin, Fintype.card_fin, ← pow_succ]
  congr 1
  have := i.pos
  omega

/-- From a bound on the class sizes, each symbol in each coordinate labels the row ends of at most
`2M / r` edges. -/
theorem Packing.row_ports_ofLabels_le
    (hocc : ∀ γ, occupancy (pairLabel rowOf colOf ρ κ) γ * r ^ (2 * a) ≤ 2 * Fintype.card E)
    (i : Fin a) (σ : Fin r) :
    r * #{e | (Packing.ofLabels rowOf colOf ρ κ).rowLabel (rowOf e) i = σ} ≤
      2 * Fintype.card E := by
  have hD : 0 < r ^ (2 * a) := Nat.pow_pos (Fin.pos σ)
  have h := card_filter_mem_mul_le (pairLabel rowOf colOf ρ κ)
    ({u | u.1 i = σ} : Finset ((Fin a → Fin r) × (Fin a → Fin r))) hocc
  rw [← Finset.univ_product_univ, Finset.filter_product_left (fun f : Fin a → Fin r => f i = σ),
    Finset.card_product,
    card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  have hcard := card_filter_apply_eq i σ
  have hfilter : #{e | pairLabel rowOf colOf ρ κ e ∈
      ({f | f i = σ} : Finset (Fin a → Fin r)) ×ˢ (univ : Finset (Fin a → Fin r))} =
      #{e | (Packing.ofLabels rowOf colOf ρ κ).rowLabel (rowOf e) i = σ} := by
    refine congrArg Finset.card (Finset.filter_congr fun e _ => ?_)
    simp [pairLabel, Packing.ofLabels]
  rw [hfilter] at h
  refine Nat.le_of_mul_le_mul_right ?_ hD
  calc r * #{e | (Packing.ofLabels rowOf colOf ρ κ).rowLabel (rowOf e) i = σ} * r ^ (2 * a)
      ≤ r * (#{f : Fin a → Fin r | f i = σ} * r ^ a * (2 * Fintype.card E)) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left r h
    _ = 2 * Fintype.card E * r ^ (2 * a) := by
        rw [two_mul a, pow_add, ← hcard]; ring

/-- From a bound on the class sizes, each symbol in each coordinate labels the column ends of at
most `2M / r` edges. -/
theorem Packing.col_ports_ofLabels_le
    (hocc : ∀ γ, occupancy (pairLabel rowOf colOf ρ κ) γ * r ^ (2 * a) ≤ 2 * Fintype.card E)
    (i : Fin a) (σ : Fin r) :
    r * #{e | (Packing.ofLabels rowOf colOf ρ κ).colLabel (colOf e) i = σ} ≤
      2 * Fintype.card E := by
  have hD : 0 < r ^ (2 * a) := Nat.pow_pos (Fin.pos σ)
  have h := card_filter_mem_mul_le (pairLabel rowOf colOf ρ κ)
    ({u | u.2 i = σ} : Finset ((Fin a → Fin r) × (Fin a → Fin r))) hocc
  rw [← Finset.univ_product_univ, Finset.filter_product_right (fun f : Fin a → Fin r => f i = σ),
    Finset.card_product,
    card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  have hcard := card_filter_apply_eq i σ
  have hfilter : #{e | pairLabel rowOf colOf ρ κ e ∈
      (univ : Finset (Fin a → Fin r)) ×ˢ ({f | f i = σ} : Finset (Fin a → Fin r))} =
      #{e | (Packing.ofLabels rowOf colOf ρ κ).colLabel (colOf e) i = σ} := by
    refine congrArg Finset.card (Finset.filter_congr fun e _ => ?_)
    simp [pairLabel, Packing.ofLabels]
  rw [hfilter] at h
  refine Nat.le_of_mul_le_mul_right ?_ hD
  calc r * #{e | (Packing.ofLabels rowOf colOf ρ κ).colLabel (colOf e) i = σ} * r ^ (2 * a)
      ≤ r * (r ^ a * #{f : Fin a → Fin r | f i = σ} * (2 * Fintype.card E)) := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left r h
    _ = 2 * Fintype.card E * r ^ (2 * a) := by
        rw [two_mul a, pow_add, ← hcard]; ring

end OfLabels

/-! ### Labels by conditional expectations -/

section Labels

/-- The candidate labels in radix order: the word numbered `j < r ^ a` has as its digit `i` the
digit `i` of `j` in base `r`, least significant first (`finFunctionFinEquiv`). A machine streams
them by counting `j`. -/
@[expose] def labelCandidates (a r : ℕ) : List (Fin a → Fin r) :=
  (List.finRange (r ^ a)).map finFunctionFinEquiv.symm

/-- Every label is a candidate. -/
theorem mem_labelCandidates {a r : ℕ} (word : Fin a → Fin r) : word ∈ labelCandidates a r :=
  List.mem_map.mpr ⟨finFunctionFinEquiv word, List.mem_finRange _, Equiv.symm_apply_apply _ _⟩

variable [Fintype E] [DecidableEq R] [FinEnum R] [DecidableEq C] [FinEnum C]
  (rowOf : E → R) (colOf : E → C) (a r : ℕ) [NeZero r]

/-- The partial labels after the conditional-expectation pass: every row vertex, then every column
vertex, receives the first candidate label minimizing the conditional expectation of the collision
potential of the pairs of labels, `partialIncidencePotential`. (In the convention of
`Cslib.BalancedSchedules`, rows are the variables and columns the factors.) -/
@[expose] def partialLabels : (R → Option (Fin a → Fin r)) × (C → Option (Fin a → Fin r)) :=
  greedyLabelPassBy (partialIncidencePotential fun e => (colOf e, rowOf e))
    (labelCandidates a r)
    ((FinEnum.toList R).map Sum.inl ++ (FinEnum.toList C).map Sum.inr)
    (fun _ => none, fun _ => none)

/-- The row labels chosen by conditional expectations. -/
@[expose] def rowLabels : R → Fin a → Fin r :=
  completeLabels (partialLabels rowOf colOf a r).1 fun _ _ => 0

/-- The column labels chosen by conditional expectations. -/
@[expose] def colLabels : C → Fin a → Fin r :=
  completeLabels (partialLabels rowOf colOf a r).2 fun _ _ => 0

/-- **The collision potential of the chosen labels.** If every vertex has degree at most `Δ`, the
potential `Φ = ∑_γ (X_γ - M / D)²` of the pairs of labels is at most `2 M Δ`, its average for
independent uniform labels. -/
theorem potential_labels_le {Δ : ℕ} (hrow : ∀ v, #{e | rowOf e = v} ≤ Δ)
    (hcol : ∀ w, #{e | colOf e = w} ≤ Δ) :
    potential (pairLabel rowOf colOf (rowLabels rowOf colOf a r) (colLabels rowOf colOf a r)) ≤
      2 * Fintype.card E * Δ := by
  let edge : E → C × R := fun e => (colOf e, rowOf e)
  let slots : List (R ⊕ C) := (FinEnum.toList R).map Sum.inl ++ (FinEnum.toList C).map Sum.inr
  let assigned := partialLabels rowOf colOf a r
  obtain ⟨hscore, hfill, -⟩ := greedyLabelPassBy_spec (partialIncidencePotential edge)
    (fun a d v hv => (expect_partialIncidencePotential_update_variable edge a d v hv).le)
    (fun a d f hf => (expect_partialIncidencePotential_update_factor edge a d f hf).le)
    (labelCandidates a r) mem_labelCandidates slots
    (fun _ => none, fun _ => none)
  have hv (v : R) : ∃ word, assigned.1 v = some word := hfill (.inl v) (by simp [slots])
  have hf (w : C) : ∃ word, assigned.2 w = some word := hfill (.inr w) (by simp [slots])
  have hvar (x : R → Fin a → Fin r) :
      completeLabels assigned.1 x = completeLabels assigned.1 (fun _ _ => 0) := by
    funext v
    obtain ⟨word, hword⟩ := hv v
    simp only [completeLabels, hword, Option.getD_some]
  have hfac (y : C → Fin a → Fin r) :
      completeLabels assigned.2 y = completeLabels assigned.2 (fun _ _ => 0) := by
    funext w
    obtain ⟨word, hword⟩ := hf w
    simp only [completeLabels, hword, Option.getD_some]
  have hout := partialIncidencePotential_eq_expect edge assigned.1 assigned.2
  simp only [hvar, hfac, Fintype.expect_const] at hout
  have hin := partialIncidencePotential_eq_expect (L := Fin a → Fin r) edge
    (fun _ => none) (fun _ => none)
  simp only [completeLabels, Option.getD_none] at hin
  have hexp := expect_incidence_potential_le (L := Fin a → Fin r) rowOf colOf
    (fun e => hrow (rowOf e)) (fun e => hcol (colOf e))
  unfold incidenceLabel at hexp
  have hle := hscore
  change partialIncidencePotential edge assigned.1 assigned.2 ≤
    partialIncidencePotential edge (fun _ => none) (fun _ => none) at hle
  rw [hout, hin] at hle
  calc potential (pairLabel rowOf colOf (rowLabels rowOf colOf a r) (colLabels rowOf colOf a r))
      ≤ (Fintype.card E : ℚ) * (Δ + Δ) := hle.trans hexp
    _ = 2 * Fintype.card E * Δ := by ring

/-- **Class sizes of the chosen labels.** Under the size hypothesis `2 Δ D² ≤ M` of (D.6), where
`D = r ^ (2a)` is the number of pairs of labels, every class has at most `2M / D` edges. -/
theorem occupancy_labels_mul_le {Δ : ℕ} (hrow : ∀ v, #{e | rowOf e = v} ≤ Δ)
    (hcol : ∀ w, #{e | colOf e = w} ≤ Δ) (hM : 2 * Δ * (r ^ (2 * a)) ^ 2 ≤ Fintype.card E)
    (γ : (Fin a → Fin r) × (Fin a → Fin r)) :
    occupancy (pairLabel rowOf colOf (rowLabels rowOf colOf a r) (colLabels rowOf colOf a r)) γ *
      r ^ (2 * a) ≤ 2 * Fintype.card E := by
  have hcard : Fintype.card ((Fin a → Fin r) × (Fin a → Fin r)) = r ^ (2 * a) := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_add,
      two_mul]
  rw [← hcard]
  refine occupancy_mul_card_le_of_variance_bound _ Fintype.card_pos Δ ?_ (hcard ▸ hM) γ
  exact potential_labels_le rowOf colOf a r hrow hcol

end Labels

/-! ### Lemma D.3 -/

section Packing

variable [Fintype E] [LinearOrder E] [DecidableEq R] [FinEnum R] [DecidableEq C] [FinEnum C]
  (rowOf : E → R) (colOf : E → C) (a r : ℕ) [NeZero r]

/-- **The packing of Lemma D.3**: the packing for the labels chosen by conditional
expectations. -/
@[expose] def packing : Packing rowOf colOf a r :=
  Packing.ofLabels rowOf colOf (rowLabels rowOf colOf a r) (colLabels rowOf colOf a r)

variable {Δ : ℕ} (hrow : ∀ v, #{e | rowOf e = v} ≤ Δ) (hcol : ∀ w, #{e | colOf e = w} ≤ Δ)
  (hM : 2 * Δ * (r ^ (2 * a)) ^ 2 ≤ Fintype.card E)
include hrow hcol hM

/-- **Lemma D.3 (1).** Under (D.6), `2 Δ D² ≤ M` and `L D ≤ M`, there are at most `3M / L`
packets. -/
theorem numPackets_packing_mul_le (hL : 2 ^ a * r ^ (2 * a) ≤ Fintype.card E) :
    (packing rowOf colOf a r).numPackets * 2 ^ a ≤ 3 * Fintype.card E :=
  Packing.numPackets_ofLabels_mul_le rowOf colOf _ _
    (occupancy_labels_mul_le rowOf colOf a r hrow hcol hM) hL

/-- **Lemma D.3 (3), rows.** Under (D.6), in every coordinate the row vertices with a given symbol
have at most `2M / r` ports. -/
theorem row_ports_packing_le (i : Fin a) (σ : Fin r) :
    r * #{e | (packing rowOf colOf a r).rowLabel (rowOf e) i = σ} ≤ 2 * Fintype.card E :=
  Packing.row_ports_ofLabels_le rowOf colOf _ _
    (occupancy_labels_mul_le rowOf colOf a r hrow hcol hM) i σ

/-- **Lemma D.3 (3), columns.** Under (D.6), in every coordinate the column vertices with a given
symbol have at most `2M / r` ports. -/
theorem col_ports_packing_le (i : Fin a) (σ : Fin r) :
    r * #{e | (packing rowOf colOf a r).colLabel (colOf e) i = σ} ≤ 2 * Fintype.card E :=
  Packing.col_ports_ofLabels_le rowOf colOf _ _
    (occupancy_labels_mul_le rowOf colOf a r hrow hcol hM) i σ

end Packing

/-- **Lemma D.3 (packing into packets).** Let a bipartite multigraph have `M` edges, joining row
vertices to column vertices, and maximum degree at most `Δ`, and let `D = r ^ (2a)` and
`L = 2 ^ a` satisfy (D.6): `2 Δ D² ≤ M` and `L D ≤ M`. Then there is a packing of its edges into
at most `3M / L` packets of `L` slots, oriented as in `Packing`, such that in every coordinate the
vertices with a given symbol have at most `3M / r` ports on each side. `packing` constructs it. -/
theorem exists_packing [Fintype E] [DecidableEq R] [DecidableEq C] [Finite R] [Finite C]
    (rowOf : E → R) (colOf : E → C) (a r : ℕ) [NeZero r] {Δ : ℕ}
    (hrow : ∀ v, #{e | rowOf e = v} ≤ Δ) (hcol : ∀ w, #{e | colOf e = w} ≤ Δ)
    (hM : 2 * Δ * (r ^ (2 * a)) ^ 2 ≤ Fintype.card E) (hL : 2 ^ a * r ^ (2 * a) ≤ Fintype.card E) :
    ∃ P : Packing rowOf colOf a r, P.numPackets * 2 ^ a ≤ 3 * Fintype.card E ∧
      (∀ i σ, r * #{e | P.rowLabel (rowOf e) i = σ} ≤ 3 * Fintype.card E) ∧
      (∀ i σ, r * #{e | P.colLabel (colOf e) i = σ} ≤ 3 * Fintype.card E) := by
  let _ : LinearOrder E := LinearOrder.lift' (Fintype.equivFin E) (Fintype.equivFin E).injective
  let _ : FinEnum R := FinEnum.ofEquiv _ (@Fintype.equivFin R (Fintype.ofFinite R))
  let _ : FinEnum C := FinEnum.ofEquiv _ (@Fintype.equivFin C (Fintype.ofFinite C))
  refine ⟨packing rowOf colOf a r, numPackets_packing_mul_le rowOf colOf a r hrow hcol hM hL,
    fun i σ => ?_, fun i σ => ?_⟩
  · have := row_ports_packing_le rowOf colOf a r hrow hcol hM i σ
    omega
  · have := col_ports_packing_le rowOf colOf a r hrow hcol hM i σ
    omega

end Cslib.PacketPacking
