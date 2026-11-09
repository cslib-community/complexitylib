/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.PartialCover
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# The actual X3C residual-cover construction

[Wang2027], setup (1)--(3), PDF pp. 12--13, Theorem 6 and proof, p. 13.
An input is an arbitrary finite family of triples with a promised exact cover.
The chosen exact-cover witness is oracle data, not a supplied dual certificate or
optimum. Canonical finite labels represent arbitrary finite X3C universes.

## Main definitions

* `Block`: promised yes-instance of X3C, with a hidden witness.
* `coverInstance`: disjoint blocks, original triple candidates and whole-block fallback sets.
* `payload`: actual original-set indices returned by specialists and near covers.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.ResidualCover
open Finset PartialCover

/-- An arbitrary promised X3C yes-instance on a canonically labelled universe.
The exact-cover witness determines oracle answers; no derived certificate is an input. -/
structure Block where
  /-- One third of the universe size. -/
  r : ℕ
  /-- Blocks are nonempty. -/
  r_pos : 0 < r
  /-- Original triples, with arbitrary overlap outside the chosen exact cover. -/
  family : Finset (Finset (Fin (3 * r)))
  /-- Every original candidate has size three. -/
  triples : ∀ A ∈ family, A.card = 3
  /-- Chosen promised exact cover, hidden from the selection algorithm. -/
  witness : Finset (Finset (Fin (3 * r)))
  /-- The witness uses original triples only. -/
  witness_subset : witness ⊆ family
  /-- Witness triples are disjoint. -/
  witness_disjoint : (witness : Set (Finset (Fin (3 * r)))).Pairwise Disjoint
  /-- Witness triples cover the universe. -/
  witness_covers : witness.biUnion id = univ

/-- The witness has exactly r triples, derived from its exact-cover properties. -/
theorem Block.witness_card (T : Block) : T.witness.card = T.r := by
  classical
  have hc := card_biUnion T.witness_disjoint
  rw [show T.witness.biUnion (fun A => A) = univ from T.witness_covers] at hc
  have hs : ∑ A ∈ T.witness, A.card = T.witness.card * 3 := by
    simp only [sum_congr rfl (fun A hA => T.triples A (T.witness_subset hA)),
      sum_const_nat, mul_comm]
  simp only [card_univ, Fintype.card_fin] at hc
  omega

variable {z : ℕ} (T : Fin z → Block)

/-- The actual disjoint-union universe. -/
abbrev Point := (j : Fin z) × Fin (3 * (T j).r)

/-- Original candidates: triples from each input, plus one whole-block fallback. -/
abbrev Candidate := (j : Fin z) × Option {A // A ∈ (T j).family}

/-- The source universe size is three times the sum of the X3C block parameters. -/
theorem universe_card : Fintype.card (Point T) = 3 * ∑ j, (T j).r := by
  simp [Point, Fintype.card_sigma, Finset.mul_sum]

/-- Inject a block point into the disjoint universe. -/
@[expose] def embed (j : Fin z) : Fin (3 * (T j).r) ↪ Point T :=
  ⟨fun e => ⟨j, e⟩, by intro a b h; cases h; rfl⟩

/-- The whole subuniverse U_j, an actual subset of the constructed universe. -/
@[expose] def groundBlock (j : Fin z) : Finset (Point T) := univ.map (embed T j)

/-- Candidate incidence is computed from the original triple or fallback tag. -/
@[expose] def sets : Candidate T → Finset (Point T)
  | ⟨j, none⟩ => groundBlock T j
  | ⟨j, some A⟩ => A.val.map (embed T j)

/-- The source weights distinguish triples from the more expensive block fallback. -/
@[expose] def weight : Candidate T → ℝ
  | ⟨_, none⟩ => 2 / z
  | ⟨j, some _⟩ => 1 / ((z : ℝ) * (T j).r)

/-- The constructed feasible dual, constant within each original X3C block. -/
@[expose] def dual (e : Point T) : ℝ := 1 / (3 * (z : ℝ) * (T e.1).r)

private theorem sum_mapped_dual (j : Fin z) (A : Finset (Fin (3 * (T j).r))) :
    ∑ e ∈ A.map (embed T j), dual T e = (A.card : ℝ) / (3 * (z : ℝ) * (T j).r) := by
  classical
  simp [dual, embed, Finset.sum_map, div_eq_mul_inv]

/-- The actual WSC instance and dual feasibility, derived from the triple sizes. -/
@[expose] def coverInstance (hz : 0 < z) : Instance (Point T) (Candidate T) where
  ground := univ
  sets := sets T
  sets_subset := by intros; exact subset_univ _
  weight := weight T
  weight_nonneg := by
    rintro ⟨j, c⟩
    cases c <;> dsimp only [weight] <;> positivity
  dual := dual T
  dual_nonneg := by intro e; dsimp only [dual]; positivity
  dual_feasible := by
    rintro ⟨j, _ | A⟩
    · rw [sets, groundBlock, sum_mapped_dual]
      simp only [card_univ, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, weight]
      have hr : (0 : ℝ) < (T j).r := by exact_mod_cast (T j).r_pos
      have hzr : (0 : ℝ) < z := by exact_mod_cast hz
      field_simp
      nlinarith
    · rw [sets, sum_mapped_dual, (T j).triples A.val A.property]
      simp only [weight, Nat.cast_ofNat]
      have hr : (0 : ℝ) < (T j).r := by exact_mod_cast (T j).r_pos
      have hzr : (0 : ℝ) < z := by exact_mod_cast hz
      field_simp
      norm_num

/-- Derived dual objective one for the actual constructed instance. -/
theorem dual_objective (hz : 0 < z) :
    ∑ e ∈ (coverInstance T hz).ground, (coverInstance T hz).dual e = 1 := by
  classical
  change (∑ e : Point T, dual T e) = 1
  rw [Fintype.sum_sigma]
  have he (j : Fin z) : (∑ e : Fin (3 * (T j).r), dual T ⟨j, e⟩) = (1 : ℝ) / z := by
    simp only [dual, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_ofNat]
    have hr : (0 : ℝ) < (T j).r := by exact_mod_cast (T j).r_pos
    have hzr : (0 : ℝ) < z := by exact_mod_cast hz
    field_simp
  simp only [he, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_one_div_cancel (by exact_mod_cast (ne_of_gt hz))

/-- Inject a hidden exact-cover triple into the original candidate index space. -/
@[expose] def witnessEmbed (j : Fin z) : {A // A ∈ (T j).witness} ↪ Candidate T :=
  ⟨fun A => ⟨j, some ⟨A.val, (T j).witness_subset A.property⟩⟩, by
    intro A B h
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Option.some.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext h.2⟩

/-- Specialist answer P_j consists of actual original triple indices. -/
@[expose] def specialist (j : Fin z) : Finset (Candidate T) := univ.map (witnessEmbed T j)

/-- The response returned for a collection of covered blocks. -/
@[expose] def payload (S : Finset (Fin z)) : Finset (Candidate T) := S.biUnion (specialist T)

/-- Specialist answers from distinct blocks never share an original candidate. -/
theorem specialist_disjoint :
    Pairwise (fun j k : Fin z => Disjoint (specialist T j) (specialist T k)) := by
  classical
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro c hc hd
  obtain ⟨a, _, rfl⟩ := mem_map.mp hc
  obtain ⟨b, _, he⟩ := mem_map.mp hd
  apply hjk
  exact (congrArg Sigma.fst he).symm

/-- Each specialist's token-independent WSC weight is exactly 1/z. -/
theorem specialist_cost (hz : 0 < z) (j : Fin z) :
    (coverInstance T hz).cost (specialist T j) = (1 : ℝ) / z := by
  classical
  simp only [Instance.cost, specialist, sum_map, witnessEmbed, coverInstance, weight]
  change (∑ _x : {A // A ∈ (T j).witness}, 1 / ((z : ℝ) * (T j).r)) = 1 / z
  rw [sum_const]
  simp only [card_univ, Fintype.card_coe, (T j).witness_card, nsmul_eq_mul]
  have hr : (0 : ℝ) < (T j).r := by exact_mod_cast (T j).r_pos
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz
  field_simp

/-- Arbitrary returned block collections have their actual summed WSC weight. -/
theorem payload_cost (hz : 0 < z) (S : Finset (Fin z)) :
    (coverInstance T hz).cost (payload T S) = (S.card : ℝ) / z := by
  classical
  rw [Instance.cost, payload, sum_biUnion (fun i _ j _ hij => specialist_disjoint T hij)]
  change (∑ j ∈ S, (coverInstance T hz).cost (specialist T j)) = _
  simp [specialist_cost T hz, div_eq_mul_inv]

/-- A specialist really covers the full corresponding X3C subuniverse. -/
theorem specialist_covered (hz : 0 < z) (j : Fin z) :
    (coverInstance T hz).covered (specialist T j) = groundBlock T j := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨c, hc, he⟩ := mem_biUnion.mp he
    obtain ⟨A, _, rfl⟩ := mem_map.mp hc
    change e ∈ A.val.map (embed T j) at he
    obtain ⟨a, _, rfl⟩ := mem_map.mp he
    exact mem_map.mpr ⟨a, mem_univ _, rfl⟩
  · intro he
    obtain ⟨a, _, rfl⟩ := mem_map.mp he
    have ha : a ∈ (T j).witness.biUnion id := by
      rw [(T j).witness_covers]
      exact mem_univ _
    obtain ⟨A, hA, ha⟩ := mem_biUnion.mp ha
    apply mem_biUnion.mpr
    refine ⟨witnessEmbed T j ⟨A, hA⟩, mem_map.mpr ⟨⟨A, hA⟩, mem_univ _, rfl⟩, ?_⟩
    change embed T j a ∈ A.map (embed T j)
    exact mem_map.mpr ⟨a, ha, rfl⟩

/-- Coverage of actual payloads is exactly the union of their block labels. -/
theorem payload_covered (hz : 0 < z) (S : Finset (Fin z)) :
    (coverInstance T hz).covered (payload T S) = S.biUnion (groundBlock T) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨c, hc, he⟩ := mem_biUnion.mp he
    obtain ⟨j, hj, hc⟩ := mem_biUnion.mp hc
    apply mem_biUnion.mpr
    refine ⟨j, hj, ?_⟩
    rw [← specialist_covered T hz j]
    exact mem_biUnion.mpr ⟨c, hc, he⟩
  · intro he
    obtain ⟨j, hj, he⟩ := mem_biUnion.mp he
    rw [← specialist_covered T hz j] at he
    obtain ⟨c, hc, he⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨c, mem_biUnion.mpr ⟨j, hj, hc⟩, he⟩

/-- Distinct blocks are disjoint, with identity recoverable from every point. -/
theorem mem_groundBlock (j : Fin z) (e : Point T) : e ∈ groundBlock T j ↔ e.1 = j := by
  classical
  constructor
  · rintro he
    obtain ⟨a, _, ha⟩ := mem_map.mp he
    exact (congrArg Sigma.fst ha).symm
  · rcases e with ⟨k, e⟩
    intro hk
    change k = j at hk
    subst k
    exact mem_map.mpr ⟨e, mem_univ _, rfl⟩

/-- Candidate incidence never crosses the source disjoint subuniverses. -/
theorem mem_sets_block (c : Candidate T) (e : Point T) (he : e ∈ sets T c) : e.1 = c.1 := by
  rcases c with ⟨j, c⟩
  cases c with
  | none => exact (mem_groundBlock T j e).mp he
  | some A =>
    obtain ⟨a, _, ha⟩ := mem_map.mp he
    exact (congrArg Sigma.fst ha).symm

/-- The actual incidence data recovers exactly the block partition: two points
share a candidate precisely when they belong to the same block. Whole-block
fallbacks supply the reverse implication. Thus its transitive closure has no
additional components or connections, without exposing the hidden exact cover. -/
theorem same_block_iff_common_candidate (e f : Point T) :
    e.1 = f.1 ↔ ∃ c : Candidate T, e ∈ sets T c ∧ f ∈ sets T c := by
  constructor
  · intro h
    refine ⟨⟨e.1, none⟩, ?_, ?_⟩
    · exact (mem_groundBlock T e.1 e).mpr rfl
    · exact (mem_groundBlock T e.1 f).mpr h.symm
  · rintro ⟨c, he, hf⟩
    exact (mem_sets_block T c e he).trans (mem_sets_block T c f hf).symm

/-- Every promised X3C block is nonempty. -/
theorem groundBlock_nonempty (j : Fin z) : (groundBlock T j).Nonempty := by
  have hp := (T j).r_pos
  have hn : 0 < 3 * (T j).r := by omega
  exact ⟨embed T j ⟨0, hn⟩, mem_map.mpr ⟨⟨0, hn⟩, mem_univ _, rfl⟩⟩

/-- Payload coverage is exactly its block-label membership. -/
theorem mem_payload_covered (hz : 0 < z) (S : Finset (Fin z)) (e : Point T) :
    e ∈ (coverInstance T hz).covered (payload T S) ↔ e.1 ∈ S := by
  rw [payload_covered]
  simp only [mem_biUnion, mem_groundBlock]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact hj
  · intro he; exact ⟨e.1, he, rfl⟩

/-- Actual payloads cover the instance exactly when every block has been returned. -/
theorem payload_covers_iff (hz : 0 < z) (S : Finset (Fin z)) :
    (coverInstance T hz).covered (payload T S) = (coverInstance T hz).ground ↔ S = univ := by
  classical
  constructor
  · intro hc
    apply eq_univ_of_forall
    intro j
    obtain ⟨e, he⟩ := groundBlock_nonempty T j
    have hj := (mem_groundBlock T j e).mp he
    have hm : e ∈ (coverInstance T hz).covered (payload T S) := hc ▸ mem_univ e
    simpa only [hj] using (mem_payload_covered T hz S e).mp hm
  · intro hS
    ext e
    change e ∈ (coverInstance T hz).covered (payload T S) ↔ e ∈ (univ : Finset (Point T))
    simp only [mem_payload_covered, hS, mem_univ]

/-- The source's near-cover residual is the actual subinstance U_j, not an
assumed residual certificate or supplied identification. -/
theorem near_residual (hz : 0 < z) (j : Fin z) :
    (coverInstance T hz).ground \ (coverInstance T hz).covered (payload T (univ.erase j)) =
      groundBlock T j := by
  classical
  ext e
  simp only [mem_sdiff, coverInstance, mem_univ, true_and]
  change (e ∉ (coverInstance T hz).covered (payload T (univ.erase j))) ↔ _
  rw [mem_payload_covered, mem_groundBlock]
  simp only [mem_erase, mem_univ, and_true, not_ne_iff]

/-- Returned original indices commute with unions of block responses. -/
theorem payload_union (S R : Finset (Fin z)) :
    payload T (S ∪ R) = payload T S ∪ payload T R := by
  classical
  simp [payload, union_biUnion]

/-- Neither source response alone is a full cover, while their actual union is.
The near response has the claimed weight (z-1)/z. -/
theorem near_specialist_properties (hz : 3 ≤ z) (j : Fin z) :
    (coverInstance T (by omega)).cost (payload T (univ.erase j)) = ((z - 1 : ℕ) : ℝ) / z ∧
    (coverInstance T (by omega)).covered (payload T (univ.erase j)) ≠
      (coverInstance T (by omega)).ground ∧
    (coverInstance T (by omega)).covered (specialist T j) ≠
      (coverInstance T (by omega)).ground ∧
    (coverInstance T (by omega)).covered (payload T (univ.erase j) ∪ specialist T j) =
      (coverInstance T (by omega)).ground := by
  classical
  have hz0 : 0 < z := by omega
  have hsingle : payload T {j} = specialist T j := by simp [payload]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [payload_cost, card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
  · intro hc
    have he := (payload_covers_iff T hz0 _).mp hc
    have hm : j ∈ univ.erase j := by rw [he]; exact mem_univ j
    simp at hm
  · rw [← hsingle]
    intro hc
    have he := (payload_covers_iff T hz0 _).mp hc
    have hc := congrArg Finset.card he
    simp only [card_singleton, card_univ, Fintype.card_fin] at hc
    omega
  · have he : univ.erase j ∪ {j} = univ := by ext k; simp
    rw [← hsingle, ← payload_union, he]
    exact (payload_covers_iff T hz0 univ).mpr rfl

/-- A cover of weight one is constructed, and every integral cover costs at least
one by the independently derived feasible dual. -/
theorem primal_optimum (hz : 0 < z) :
    (coverInstance T hz).covered (payload T univ) = (coverInstance T hz).ground ∧
    (coverInstance T hz).cost (payload T univ) = 1 ∧
    ∀ C, (coverInstance T hz).covered C = (coverInstance T hz).ground →
      1 ≤ (coverInstance T hz).cost C := by
  refine ⟨(payload_covers_iff T hz univ).mpr rfl, ?_, ?_⟩
  · rw [payload_cost, card_univ, Fintype.card_fin]
    exact div_self (by exact_mod_cast (ne_of_gt hz))
  · intro C hC
    have hb := (coverInstance T hz).dual_le_cost C
    rw [hC, dual_objective T hz] at hb
    exact hb

/-- Distinct subuniverses have disjoint point sets. -/
theorem groundBlock_disjoint :
    Pairwise (fun j k : Fin z => Disjoint (groundBlock T j) (groundBlock T k)) := by
  classical
  intro j k hjk
  apply disjoint_left.mpr
  intro e he hf
  exact hjk (((mem_groundBlock T j e).mp he).symm.trans ((mem_groundBlock T k e).mp hf))

/-- Each full block has dual charge 1/z. -/
theorem block_dual (hz : 0 < z) (j : Fin z) :
    ∑ e ∈ groundBlock T j, (coverInstance T hz).dual e = (1 : ℝ) / z := by
  rw [groundBlock]
  change (∑ e ∈ univ.map (embed T j), dual T e) = _
  rw [sum_mapped_dual]
  simp only [card_univ, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  have hr : (0 : ℝ) < (T j).r := by exact_mod_cast (T j).r_pos
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz
  field_simp

/-- Every returned payload exactly saturates its own covered dual charge. -/
theorem payload_dual (hz : 0 < z) (S : Finset (Fin z)) :
    ∑ e ∈ (coverInstance T hz).covered (payload T S), (coverInstance T hz).dual e =
      (coverInstance T hz).cost (payload T S) := by
  rw [payload_covered, sum_biUnion (fun i _ j _ hij => groundBlock_disjoint T hij), payload_cost]
  simp [block_dual T hz, div_eq_mul_inv]

/-- Near-cover and specialist responses pass the actual local dual tests with rho=1. -/
theorem responses_certified (hz : 3 ≤ z) (j : Fin z) :
    (coverInstance T (by omega)).Certified 1 ∅ (payload T (univ.erase j)) ∧
    (coverInstance T (by omega)).Certified 1 (payload T (univ.erase j)) (specialist T j) := by
  classical
  have hz0 : 0 < z := by omega
  let I := coverInstance T hz0
  have hS : (univ.erase j : Finset (Fin z)).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin]
    omega
  have hnear : (I.covered (payload T (univ.erase j))).Nonempty := by
    obtain ⟨k, hk⟩ := hS
    obtain ⟨e, he⟩ := groundBlock_nonempty T k
    exact ⟨e, (mem_payload_covered T hz0 _ e).mpr (by
      rw [(mem_groundBlock T k e).mp he]; exact hk)⟩
  constructor
  · change (I.covered _ \ I.covered ∅).Nonempty ∧ _
    have he : I.covered ∅ = ∅ := by simp [Instance.covered]
    rw [he, sdiff_empty, one_mul]
    exact ⟨hnear, (payload_dual T hz0 _).ge⟩
  · have hf : I.covered (specialist T j) \
        I.covered (payload T (univ.erase j)) = groundBlock T j := by
      change (coverInstance T hz0).covered (specialist T j) \
        (coverInstance T hz0).covered (payload T (univ.erase j)) = groundBlock T j
      ext e
      simp only [mem_sdiff, specialist_covered T hz0, mem_groundBlock,
        mem_payload_covered T hz0, mem_erase, mem_univ, and_true]
      tauto
    change (I.covered _ \ I.covered _).Nonempty ∧ _
    rw [hf]
    refine ⟨groundBlock_nonempty T j, ?_⟩
    change (coverInstance T hz0).cost (specialist T j) ≤
      1 * ∑ e ∈ groundBlock T j, (coverInstance T hz0).dual e
    rw [one_mul, specialist_cost T hz0, block_dual T hz0]

/-- Decode a residual using only the actual uncovered points, with a default on
empty residuals. In the construction the residual is nonempty. -/
@[expose] def residualIndex (hz : 0 < z) (R : Finset (Point T)) : Fin z :=
  if h : (R.image Sigma.fst).Nonempty then (R.image Sigma.fst).min' h else ⟨0, hz⟩

/-- The actual residual, rather than a supplied response label, identifies the
specialist to query next. -/
theorem decode_near_residual (hz : 0 < z) (j : Fin z) :
    residualIndex T hz ((coverInstance T hz).ground \
        (coverInstance T hz).covered (payload T (univ.erase j))) = j := by
  classical
  rw [near_residual]
  have he : (groundBlock T j).image Sigma.fst = {j} := by
    ext k
    simp only [mem_image, mem_singleton]
    constructor
    · rintro ⟨e, he, rfl⟩; exact (mem_groundBlock T j e).mp he
    · intro hk
      subst k
      obtain ⟨e, he⟩ := groundBlock_nonempty T j
      exact ⟨e, he, (mem_groundBlock T j e).mp he⟩
  simp [residualIndex, he]

/-- No alternative feasible nonnegative dual can exceed the constructed objective
one, since the actual primal cover has weight one. Thus L=OPT=1 is derived. -/
theorem dual_optimum (hz : 0 < z) (d : Point T → ℝ) (hd : ∀ e, 0 ≤ d e)
    (hf : ∀ c, ∑ e ∈ (coverInstance T hz).sets c, d e ≤ (coverInstance T hz).weight c) :
    ∑ e ∈ (coverInstance T hz).ground, d e ≤ 1 := by
  let I : Instance (Point T) (Candidate T) :=
    { coverInstance T hz with dual := d, dual_nonneg := hd, dual_feasible := hf }
  have hb := I.dual_le_cost (payload T univ)
  change (∑ e ∈ (coverInstance T hz).covered (payload T univ), d e) ≤
    (coverInstance T hz).cost (payload T univ) at hb
  rw [(primal_optimum T hz).1, (primal_optimum T hz).2.1] at hb
  exact hb

end Cslib.Probability.StochasticOracle.ResidualCover
