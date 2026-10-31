/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Huffman.Basic
public import Mathlib.InformationTheory.Coding.Kraft
public import Mathlib.InformationTheory.Coding.KraftMcMillan

import Mathlib.Data.List.Sort
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Binary Kraft Converse, Prefix-Free Trie Compaction, and McMillan Reduction

Mathlib's `Mathlib.InformationTheory.Coding.Kraft` and `KraftMcMillan` prove the forward $D$-ary
Kraft and Kraft–McMillan inequalities `∑ w ∈ S, (1 / D) ^ w.length ≤ 1` for finite prefix-free and
uniquely decodable codes. This module supplies the finite binary ($D = 2$, alphabet `Bool`)
constructive converse and tree reductions needed for Huffman optimality ([Kraft1949];
[McMillan1956]; [CoverThomas2006], Theorems 5.2.1 and 5.5.1, specialized from $D$-ary to binary
codes and from real probability weights to arbitrary ordered additive commutative monoids `β`):

1. **Prefix-free codebook compaction (`treeOfCodebook`)**: any nonempty prefix-free binary codebook
   contracts (by eliminating unary internal nodes) to a full binary `CodeTree α` with the same leaf
   symbols and at most the same weighted external path length under nonnegative weights.
2. **Constructive binary Kraft converse (`kraftAssign`, `exists_isPrefixFree_iff_kraft_le_one`)**:
   sorting symbols in nondecreasing order of target length `ℓ` and assigning consecutive dyadic
   subintervals of `[0, 2 ^ L)` constructs an explicit injective prefix-free binary code achieving
   exact lengths `ℓ` whenever `∑ a ∈ s, (1 / 2 : ℝ) ^ ℓ a ≤ 1`, completing the if-and-only-if
   characterization.
3. **McMillan tree reduction (`exists_codeTree_of_isUniquelyDecodable`)**: combining Mathlib's
   `IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one` with the binary Kraft converse and
   `treeOfCodebook`, every finite injective uniquely decodable binary code admits a full binary
   `CodeTree α` whose weighted path length is at most that of the original code over any ordered
   additive commutative monoid `β`.

## Main definitions

* `Cslib.Algorithms.Lean.Huffman.bitsOfNat`, `natOfBits`: MSB-first fixed-width binary encoding and
  decoding on `ℕ`.
* `Cslib.Algorithms.Lean.Huffman.kraftAssign`: constructive sorted dyadic codeword assignment.
* `Cslib.Algorithms.Lean.Huffman.treeOfCodebook`: compaction of a binary codebook into a full binary
  `CodeTree α`.

## Main results

* `Cslib.Algorithms.Lean.Huffman.exists_isPrefixFree_of_kraft_nat`: integer-scaled constructive
  binary Kraft converse.
* `Cslib.Algorithms.Lean.Huffman.exists_isPrefixFree_iff_kraft_le_one`: **Binary Kraft Theorem**
  (`∃` injective prefix-free binary code of lengths `ℓ` `↔ ∑ a ∈ s, (1 / 2 : ℝ) ^ ℓ a ≤ 1`).
* `Cslib.Algorithms.Lean.Huffman.exists_codeTree_of_isPrefixFree`: every nonempty finite injective
  prefix-free binary code is dominated in weighted path length by a full `CodeTree α`.
* `Cslib.Algorithms.Lean.Huffman.exists_codeTree_of_isUniquelyDecodable`: every nonempty finite
  injective uniquely decodable binary code is dominated in weighted path length by a full
  `CodeTree α`.

## References

* [Kraft1949] Leon G. Kraft, *A Device for Quantizing, Grouping, and Coding Amplitude-Modulated
  Pulses*, M.S. thesis, MIT, 1949.
* [McMillan1956] Brockway McMillan, *Two Inequalities Implied by Unique Decipherability*, 1956.
* [CoverThomas2006] Thomas M. Cover and Joy A. Thomas, *Elements of Information Theory* (2nd ed.),
  Section 5.2 and Section 5.5, 2006.
-/

public section

namespace Cslib.Algorithms.Lean.Huffman

/-! ## Fixed-width binary representation and dyadic prefix intervals -/

/-- Most-significant-bit-first `k`-bit binary representation of `q % 2 ^ k`. -/
def bitsOfNat : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, q => bitsOfNat k (q / 2) ++ [decide (q % 2 = 1)]

/-- Natural number represented by a most-significant-bit-first list of bits. -/
def natOfBits (bs : List Bool) : ℕ :=
  bs.foldl (fun acc b => 2 * acc + cond b 1 0) 0

@[simp] theorem length_bitsOfNat (k q : ℕ) : (bitsOfNat k q).length = k := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih => simp [bitsOfNat, ih]

private theorem foldl_bitStep_eq (bs : List Bool) (acc : ℕ) :
    bs.foldl (fun a b => 2 * a + cond b 1 0) acc = acc * 2 ^ bs.length + natOfBits bs := by
  induction bs generalizing acc with
  | nil => simp [natOfBits]
  | cons b bs ih =>
    have h0 : natOfBits (b :: bs) = (cond b 1 0) * 2 ^ bs.length + natOfBits bs := by
      simpa [natOfBits] using ih (cond b 1 0)
    simp only [List.foldl_cons, List.length_cons, ih, h0, Nat.pow_succ]
    ring

theorem natOfBits_append (u v : List Bool) :
    natOfBits (u ++ v) = natOfBits u * 2 ^ v.length + natOfBits v := by
  unfold natOfBits
  rw [List.foldl_append]
  exact foldl_bitStep_eq v (natOfBits u)

theorem natOfBits_lt_two_pow (bs : List Bool) : natOfBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [natOfBits]
  | cons b bs ih =>
    have h0 : natOfBits (b :: bs) = (cond b 1 0) * 2 ^ bs.length + natOfBits bs := by
      simpa [natOfBits] using foldl_bitStep_eq bs (cond b 1 0)
    rw [h0, List.length_cons, Nat.pow_succ]
    cases b <;> simp only [cond] <;> omega

theorem natOfBits_bitsOfNat {k q : ℕ} (hq : q < 2 ^ k) :
    natOfBits (bitsOfNat k q) = q := by
  induction k generalizing q with
  | zero =>
    simp only [Nat.pow_zero] at hq
    have hq0 : q = 0 := by omega
    subst hq0
    rfl
  | succ k ih =>
    rw [Nat.pow_succ] at hq
    have hdiv : q / 2 < 2 ^ k := by omega
    rw [bitsOfNat, natOfBits_append, ih hdiv]
    have hbit : natOfBits [decide (q % 2 = 1)] = q % 2 := by
      by_cases h : q % 2 = 1
      · simp [natOfBits, h]
      · have h0 : q % 2 = 0 := by omega
        simp [natOfBits, h0]
    simp only [List.length_singleton, Nat.pow_one, hbit]
    omega

/-- Left endpoint of the dyadic subinterval of `[0, 2 ^ L)` associated with codeword `c`. -/
private def dyadicStart (L : ℕ) (c : List Bool) : ℕ :=
  natOfBits c * 2 ^ (L - c.length)

private theorem dyadicStart_bounds_of_prefix {L : ℕ} {c₁ c₂ : List Bool}
    (hpref : c₁ <+: c₂) (hc₂ : c₂.length ≤ L) :
    dyadicStart L c₁ ≤ dyadicStart L c₂ ∧
      dyadicStart L c₂ < dyadicStart L c₁ + 2 ^ (L - c₁.length) := by
  rcases hpref with ⟨t, rfl⟩
  simp only [List.length_append] at hc₂
  have hsub : L - c₁.length = t.length + (L - (c₁.length + t.length)) := by omega
  have hexp : dyadicStart L (c₁ ++ t) =
      dyadicStart L c₁ + natOfBits t * 2 ^ (L - (c₁.length + t.length)) := by
    unfold dyadicStart
    rw [natOfBits_append, List.length_append, hsub, Nat.pow_add]
    ring
  have ht_lt : natOfBits t + 1 ≤ 2 ^ t.length := natOfBits_lt_two_pow t
  have hmul : (natOfBits t + 1) * 2 ^ (L - (c₁.length + t.length)) ≤
      2 ^ (L - c₁.length) := by
    rw [hsub, Nat.pow_add]
    exact Nat.mul_le_mul_right _ ht_lt
  have hpos : 0 < 2 ^ (L - (c₁.length + t.length)) := Nat.two_pow_pos _
  constructor
  · omega
  · calc
      dyadicStart L (c₁ ++ t)
        < dyadicStart L c₁ + (natOfBits t + 1) * 2 ^ (L - (c₁.length + t.length)) := by
          rw [hexp, Nat.add_mul, Nat.one_mul]
          omega
      _ ≤ dyadicStart L c₁ + 2 ^ (L - c₁.length) := Nat.add_le_add_left hmul _

/-! ## Constructive binary Kraft converse -/

/-- Assign consecutive dyadic codewords of lengths `ℓ` inside `[0, 2 ^ L)` to a list of symbols
sorted in nondecreasing order of `ℓ`. -/
def kraftAssign {α : Type*} (L : ℕ) (ℓ : α → ℕ) :
    ℕ → List α → List (α × List Bool)
  | _, [] => []
  | offset, a :: xs =>
    let step := 2 ^ (L - ℓ a)
    (a, bitsOfNat (ℓ a) (offset / step)) :: kraftAssign L ℓ (offset + step) xs

@[simp] theorem map_fst_kraftAssign {α : Type*} (L : ℕ) (ℓ : α → ℕ) (offset : ℕ) (xs : List α) :
    (kraftAssign L ℓ offset xs).map Prod.fst = xs := by
  induction xs generalizing offset with
  | nil => rfl
  | cons a xs ih => simp [kraftAssign, ih]

theorem length_snd_of_mem_kraftAssign {α : Type*} {L : ℕ} {ℓ : α → ℕ} {offset : ℕ} {xs : List α}
    {p : α × List Bool} (hp : p ∈ kraftAssign L ℓ offset xs) :
    p.2.length = ℓ p.1 := by
  induction xs generalizing offset with
  | nil => cases hp
  | cons a xs ih =>
    rcases List.mem_cons.mp hp with rfl | htail
    · simp [length_bitsOfNat]
    · exact ih htail

private theorem kraftAssign_spec {α : Type*} {L : ℕ} {ℓ : α → ℕ} (xs : List α) (offset : ℕ)
    (hL : ∀ x ∈ xs, ℓ x ≤ L)
    (hpw : xs.Pairwise (fun x y => ℓ x ≤ ℓ y))
    (hdvd : ∀ x ∈ xs, 2 ^ (L - ℓ x) ∣ offset)
    (hsum : offset + (xs.map fun x => 2 ^ (L - ℓ x)).sum ≤ 2 ^ L) :
    (∀ p ∈ kraftAssign L ℓ offset xs,
      offset ≤ dyadicStart L p.2 ∧
        dyadicStart L p.2 + 2 ^ (L - ℓ p.1) ≤ offset + (xs.map fun x => 2 ^ (L - ℓ x)).sum) ∧
      ((kraftAssign L ℓ offset xs).map Prod.snd).Pairwise
        (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁) := by
  induction xs generalizing offset with
  | nil => simp [kraftAssign]
  | cons a xs ih =>
    simp only [List.pairwise_cons, List.map_cons, List.sum_cons] at hpw hsum
    have haL : ℓ a ≤ L := hL a List.mem_cons_self
    have ha_dvd : 2 ^ (L - ℓ a) ∣ offset := hdvd a List.mem_cons_self
    have hstep_pos : 0 < 2 ^ (L - ℓ a) := Nat.two_pow_pos _
    have hpow_split : 2 ^ L = 2 ^ ℓ a * 2 ^ (L - ℓ a) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' haL]
    have hdiv_mul : offset / 2 ^ (L - ℓ a) * 2 ^ (L - ℓ a) = offset :=
      Nat.div_mul_cancel ha_dvd
    have hq_lt : offset / 2 ^ (L - ℓ a) < 2 ^ ℓ a := by
      have hlt : offset / 2 ^ (L - ℓ a) * 2 ^ (L - ℓ a) < 2 ^ ℓ a * 2 ^ (L - ℓ a) := by omega
      exact (Nat.mul_lt_mul_right hstep_pos).mp hlt
    have hca_len : (bitsOfNat (ℓ a) (offset / 2 ^ (L - ℓ a))).length = ℓ a :=
      length_bitsOfNat _ _
    have hca_start : dyadicStart L (bitsOfNat (ℓ a) (offset / 2 ^ (L - ℓ a))) = offset := by
      unfold dyadicStart
      rw [hca_len, natOfBits_bitsOfNat hq_lt]
      exact hdiv_mul
    have hL' : ∀ x ∈ xs, ℓ x ≤ L := fun x hx => hL x (List.mem_cons_of_mem a hx)
    have hdvd' : ∀ x ∈ xs, 2 ^ (L - ℓ x) ∣ offset + 2 ^ (L - ℓ a) := by
      intro x hx
      have hle : L - ℓ x ≤ L - ℓ a := by
        have := hpw.1 x hx
        omega
      exact Nat.dvd_add (hdvd x (List.mem_cons_of_mem a hx)) (Nat.pow_dvd_pow 2 hle)
    have hsum' : (offset + 2 ^ (L - ℓ a)) + (xs.map fun x => 2 ^ (L - ℓ x)).sum ≤ 2 ^ L := by
      omega
    rcases ih (offset + 2 ^ (L - ℓ a)) hL' hpw.2 hdvd' hsum' with ⟨hbds, hpw_tail⟩
    constructor
    · intro p hp
      simp only [kraftAssign, List.mem_cons, List.map_cons, List.sum_cons] at hp ⊢
      rcases hp with rfl | htail
      · dsimp only
        rw [hca_start]
        exact ⟨le_rfl, by omega⟩
      · rcases hbds p htail with ⟨hlo, hhi⟩
        exact ⟨by omega, by omega⟩
    · simp only [kraftAssign, List.map_cons, List.pairwise_cons]
      refine ⟨?_, hpw_tail⟩
      intro c hc
      rcases List.mem_map.mp hc with ⟨p, hp, rfl⟩
      have hp_len : p.2.length = ℓ p.1 := length_snd_of_mem_kraftAssign hp
      have hp_L : p.2.length ≤ L := by
        rw [hp_len]
        exact hL' p.1 ((map_fst_kraftAssign L ℓ (offset + 2 ^ (L - ℓ a)) xs) ▸
          List.mem_map.mpr ⟨p, hp, rfl⟩)
      have hca_L : (bitsOfNat (ℓ a) (offset / 2 ^ (L - ℓ a))).length ≤ L := by omega
      rcases hbds p hp with ⟨hp_lo, _⟩
      constructor
      · intro hpref
        have := (dyadicStart_bounds_of_prefix hpref hp_L).2
        rw [hca_start, hca_len] at this
        omega
      · intro hpref
        have := (dyadicStart_bounds_of_prefix hpref hca_L).1
        rw [hca_start] at this
        omega

private theorem le_foldr_max_of_mem {xs : List ℕ} {k : ℕ} (hk : k ∈ xs) :
    k ≤ xs.foldr max 0 := by
  induction xs with
  | nil => cases hk
  | cons x xs ih =>
    rcases List.mem_cons.mp hk with rfl | htail
    · exact Nat.le_max_left k _
    · exact Nat.le_trans (ih htail) (Nat.le_max_right x _)

private theorem lookup_kraftAssign_exists {α : Type*} [DecidableEq α]
    {pairs : List (α × List Bool)} {a : α}
    (ha : a ∈ pairs.map Prod.fst) :
    ∃ c, (a, c) ∈ pairs ∧ (pairs.find? fun p => p.1 == a) = some (a, c) := by
  induction pairs with
  | nil => cases ha
  | cons p ps ih =>
    rcases p with ⟨x, cx⟩
    by_cases hxa : x = a
    · subst hxa
      exact ⟨cx, List.mem_cons_self, by simp⟩
    · simp only [List.map_cons, List.mem_cons] at ha
      rcases ha with hEq | hps
      · exact absurd hEq.symm hxa
      · rcases ih hps with ⟨c, hmem, hfind⟩
        have hbeq : (x == a) = false := beq_false_of_ne hxa
        exact ⟨c, List.mem_cons_of_mem _ hmem, by simp [List.find?, hbeq, hfind]⟩

/-- **Integer-Scaled Binary Kraft Converse**: if `s : Finset α` and `ℓ : α → ℕ` satisfy
`∀ a ∈ s, ℓ a ≤ L` and `∑ a ∈ s, 2 ^ (L - ℓ a) ≤ 2 ^ L`, then there exists an injective prefix-free
binary code on `s` whose codewords have exact lengths `ℓ`. -/
theorem exists_isPrefixFree_of_kraft_nat {α : Type*} (s : Finset α) (ℓ : α → ℕ) (L : ℕ)
    (hL : ∀ a ∈ s, ℓ a ≤ L)
    (hkraft : (∑ a ∈ s, 2 ^ (L - ℓ a)) ≤ 2 ^ L) :
    ∃ code : α → List Bool,
      Set.InjOn code (s : Set α) ∧
      InformationTheory.IsPrefixFree (code '' (s : Set α)) ∧
      ∀ a ∈ s, (code a).length = ℓ a := by
  classical
  let sorted := s.toList.mergeSort (fun a b => decide (ℓ a ≤ ℓ b))
  have hperm : sorted.Perm s.toList := List.mergeSort_perm s.toList _
  have hpw_sorted : sorted.Pairwise (fun a b => ℓ a ≤ ℓ b) := by
    have htot : ∀ a b, (decide (ℓ a ≤ ℓ b) || decide (ℓ b ≤ ℓ a)) = true := by
      intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total (ℓ a) (ℓ b)
    have htr : ∀ a b c, decide (ℓ a ≤ ℓ b) = true → decide (ℓ b ≤ ℓ c) = true →
        decide (ℓ a ≤ ℓ c) = true := by
      intro a b c hab hbc
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hab hbc
    simpa [decide_eq_true_eq] using List.pairwise_mergeSort htr htot s.toList
  have hL_sorted : ∀ a ∈ sorted, ℓ a ≤ L := fun a ha =>
    hL a (Finset.mem_toList.mp (hperm.subset ha))
  have hsum_sorted : 0 + (sorted.map fun x => 2 ^ (L - ℓ x)).sum ≤ 2 ^ L := by
    rw [Nat.zero_add, (hperm.map _).sum_eq]
    simpa using hkraft
  let pairs := kraftAssign L ℓ 0 sorted
  have hspec := (kraftAssign_spec sorted 0 hL_sorted hpw_sorted (fun _ _ => Nat.dvd_zero _)
    hsum_sorted).2
  have hfst : pairs.map Prod.fst = sorted := map_fst_kraftAssign L ℓ 0 sorted
  let code : α → List Bool := fun a =>
    match pairs.find? (fun p => p.1 == a) with
    | some p => p.2
    | none => []
  have hcode_mem : ∀ a ∈ s, (a, code a) ∈ pairs := by
    intro a ha
    have ha_fst : a ∈ pairs.map Prod.fst := by
      rw [hfst]
      exact hperm.symm.subset (Finset.mem_toList.mpr ha)
    rcases lookup_kraftAssign_exists ha_fst with ⟨c, hmem, hfind⟩
    dsimp only [code]
    rw [hfind]
    exact hmem
  have hinj_pairs : ∀ {a b : α}, a ∈ s → b ∈ s → code a = code b → a = b := by
    intro a b ha hb hEq
    exact Classical.byContradiction fun hne => by
      have hma := hcode_mem a ha
      have hmb := hcode_mem b hb
      have hnodup_snd : (pairs.map Prod.snd).Nodup :=
        List.Pairwise.imp (fun {c₁ c₂} h (hc : c₁ = c₂) => h.1 (hc ▸ List.prefix_refl c₁)) hspec
      rcases List.append_of_mem hma with ⟨u, v, huv⟩
      rw [huv] at hmb hnodup_snd
      simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnodup_snd
      rcases List.mem_append.mp hmb with hbu | hbv
      · exact hnodup_snd.2.2 (code a) (List.mem_map.mpr ⟨(b, code b), hbu, hEq.symm⟩)
          (code a) List.mem_cons_self rfl
      · rcases List.mem_cons.mp hbv with hpair | hbv'
        · exact hne (Prod.mk.inj hpair).1.symm
        · exact hnodup_snd.2.1.1 (List.mem_map.mpr ⟨(b, code b), hbv', hEq.symm⟩)
  refine ⟨code, ?_, ?_, ?_⟩
  · intro a ha b hb hEq
    exact hinj_pairs ha hb hEq
  · intro x hx y hy hpref
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    exact Classical.byContradiction fun hne => by
      have hma : code a ∈ pairs.map Prod.snd :=
        List.mem_map.mpr ⟨(a, code a), hcode_mem a ha, rfl⟩
      have hmb : code b ∈ pairs.map Prod.snd :=
        List.mem_map.mpr ⟨(b, code b), hcode_mem b hb, rfl⟩
      have hrel := CodeTree.pairwise_rel_of_ne (fun h => ⟨h.2, h.1⟩) hspec hma hmb hne
      exact hrel.1 hpref
  · intro a ha
    exact length_snd_of_mem_kraftAssign (hcode_mem a ha)

/-- **Binary Kraft Theorem** ([Kraft1949]; [CoverThomas2006], Theorem 5.2.1 specialized to binary
alphabet `Bool`, $D = 2$, on finite codebooks `s : Finset α`): a finite symbol set `s` admits an
injective prefix-free binary code with codeword lengths `ℓ` if and only if
`∑ a ∈ s, (1 / 2 : ℝ) ^ ℓ a ≤ 1`. -/
theorem exists_isPrefixFree_iff_kraft_le_one {α : Type*} (s : Finset α) (ℓ : α → ℕ) :
    (∃ code : α → List Bool,
      Set.InjOn code (s : Set α) ∧
      InformationTheory.IsPrefixFree (code '' (s : Set α)) ∧
      ∀ a ∈ s, (code a).length = ℓ a) ↔
      (∑ a ∈ s, (1 / 2 : ℝ) ^ ℓ a) ≤ 1 := by
  classical
  constructor
  · rintro ⟨code, hinj, hpf, hlen⟩
    let S : Finset (List Bool) := s.image code
    have hcoe : (S : Set (List Bool)) = code '' (s : Set α) := Finset.coe_image
    have hS : InformationTheory.IsPrefixFree (S : Set (List Bool)) := hcoe ▸ hpf
    have hkraft := hS.finsetSum_one_div_card_pow_length_le_one
    have hcard : (Fintype.card Bool : ℝ) = 2 := by
      have : Fintype.card Bool = 2 := Fintype.card_bool
      exact_mod_cast this
    rw [hcard] at hkraft
    have hsum_eq : (∑ w ∈ S, (1 / 2 : ℝ) ^ w.length) = ∑ a ∈ s, (1 / 2 : ℝ) ^ ℓ a := by
      rw [Finset.sum_image (fun a ha b hb hEq => hinj ha hb hEq)]
      exact Finset.sum_congr rfl fun a ha => by rw [hlen a ha]
    rwa [← hsum_eq]
  · intro hkraft
    let L : ℕ := (s.toList.map ℓ).foldr max 0
    have hL : ∀ a ∈ s, ℓ a ≤ L := fun a ha =>
      le_foldr_max_of_mem (List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha, rfl⟩)
    have hcast_sum : ∀ (t : Finset α) (g : α → ℕ),
        ((∑ a ∈ t, g a : ℕ) : ℝ) = ∑ a ∈ t, (g a : ℝ) := by
      intro t g
      induction t using Finset.induction_on with
      | empty => simp
      | insert x u hxu ih => simp [Finset.sum_insert hxu, ih]
    have hmul_sum : ∀ (c : ℝ) (t : Finset α) (g : α → ℝ),
        (∑ a ∈ t, c * g a) = c * ∑ a ∈ t, g a := by
      intro c t g
      induction t using Finset.induction_on with
      | empty => simp
      | insert x u hxu ih => simp [Finset.sum_insert hxu, mul_add, ih]
    have hnat : (∑ a ∈ s, 2 ^ (L - ℓ a)) ≤ 2 ^ L := by
      have hreal : ((∑ a ∈ s, 2 ^ (L - ℓ a) : ℕ) : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
        rw [hcast_sum]
        have hterm : ∀ a ∈ s,
            ((2 ^ (L - ℓ a) : ℕ) : ℝ) = (2 : ℝ) ^ L * (1 / 2 : ℝ) ^ ℓ a := by
          intro a ha
          rw [Nat.cast_pow, Nat.cast_ofNat]
          have haL := hL a ha
          have hpow : (2 : ℝ) ^ L = (2 : ℝ) ^ (L - ℓ a) * (2 : ℝ) ^ ℓ a := by
            rw [← pow_add, Nat.sub_add_cancel haL]
          have hcancel : (2 : ℝ) ^ ℓ a * (1 / 2 : ℝ) ^ ℓ a = 1 := by
            rw [← mul_pow]
            norm_num
          rw [hpow, mul_assoc, hcancel, mul_one]
        rw [Finset.sum_congr rfl hterm, hmul_sum, Nat.cast_pow, Nat.cast_ofNat]
        have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ L := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hkraft hpos]
      exact_mod_cast hreal
    exact exists_isPrefixFree_of_kraft_nat s ℓ L hL hnat

/-! ## Prefix-free codebook compaction to `CodeTree` and McMillan reduction -/

/-- Fallback right-associated tree over a nonempty symbol list (only reached on invalid non-prefix
codebooks). -/
private def foldLeaves {α : Type*} : List α → Option (CodeTree α)
  | [] => none
  | [a] => some (.leaf a)
  | a :: b :: rest => (foldLeaves (b :: rest)).map (.branch (.leaf a))

/-- Entries of `ps` whose codeword starts with `false`, with that leading bit stripped. -/
private def leftChildren {α : Type*} : List (α × List Bool) → List (α × List Bool)
  | [] => []
  | (_, []) :: ps => leftChildren ps
  | (a, false :: bs) :: ps => (a, bs) :: leftChildren ps
  | (_, true :: _) :: ps => leftChildren ps

/-- Entries of `ps` whose codeword starts with `true`, with that leading bit stripped. -/
private def rightChildren {α : Type*} : List (α × List Bool) → List (α × List Bool)
  | [] => []
  | (_, []) :: ps => rightChildren ps
  | (_, false :: _) :: ps => rightChildren ps
  | (a, true :: bs) :: ps => (a, bs) :: rightChildren ps

/-- Total codeword bit length of a codebook `ps`. -/
private def codebookBitLength {α : Type*} (ps : List (α × List Bool)) : ℕ :=
  (ps.map fun p => p.2.length).sum

private theorem codebookBitLength_leftChildren_add_le {α : Type*} (ps : List (α × List Bool)) :
    codebookBitLength (leftChildren ps) + (leftChildren ps).length ≤ codebookBitLength ps := by
  induction ps with
  | nil => simp [leftChildren, codebookBitLength]
  | cons p ps ih =>
    rcases p with ⟨a, _ | ⟨b, bs⟩⟩
    · simp only [leftChildren, codebookBitLength, List.map_cons, List.sum_cons, List.length_nil]
        at ih ⊢
      omega
    · cases b <;>
        simp only [leftChildren, codebookBitLength, List.map_cons, List.sum_cons,
          List.length_cons] at ih ⊢ <;>
        omega

private theorem codebookBitLength_rightChildren_add_le {α : Type*} (ps : List (α × List Bool)) :
    codebookBitLength (rightChildren ps) + (rightChildren ps).length ≤ codebookBitLength ps := by
  induction ps with
  | nil => simp [rightChildren, codebookBitLength]
  | cons p ps ih =>
    rcases p with ⟨a, _ | ⟨b, bs⟩⟩
    · simp only [rightChildren, codebookBitLength, List.map_cons, List.sum_cons, List.length_nil]
        at ih ⊢
      omega
    · cases b <;>
        simp only [rightChildren, codebookBitLength, List.map_cons, List.sum_cons,
          List.length_cons] at ih ⊢ <;>
        omega

/-- Compact a binary codebook `pairs : List (α × List Bool)` into a full binary `CodeTree α` by
recursively branching on first bits and contracting unary internal nodes. -/
def treeOfCodebook {α : Type*} : List (α × List Bool) → Option (CodeTree α)
  | [] => none
  | [(a, _)] => some (.leaf a)
  | p₁ :: p₂ :: rest =>
    match hL : leftChildren (p₁ :: p₂ :: rest), hR : rightChildren (p₁ :: p₂ :: rest) with
    | [], [] => foldLeaves ((p₁ :: p₂ :: rest).map Prod.fst)
    | l₁ :: ls, [] =>
      have : codebookBitLength (l₁ :: ls) < codebookBitLength (p₁ :: p₂ :: rest) := by
        have h := codebookBitLength_leftChildren_add_le (p₁ :: p₂ :: rest)
        rw [hL] at h
        simp only [List.length_cons] at h
        omega
      treeOfCodebook (l₁ :: ls)
    | [], r₁ :: rs =>
      have : codebookBitLength (r₁ :: rs) < codebookBitLength (p₁ :: p₂ :: rest) := by
        have h := codebookBitLength_rightChildren_add_le (p₁ :: p₂ :: rest)
        rw [hR] at h
        simp only [List.length_cons] at h
        omega
      treeOfCodebook (r₁ :: rs)
    | l₁ :: ls, r₁ :: rs => do
      have : codebookBitLength (l₁ :: ls) < codebookBitLength (p₁ :: p₂ :: rest) := by
        have h := codebookBitLength_leftChildren_add_le (p₁ :: p₂ :: rest)
        rw [hL] at h
        simp only [List.length_cons] at h
        omega
      have : codebookBitLength (r₁ :: rs) < codebookBitLength (p₁ :: p₂ :: rest) := by
        have h := codebookBitLength_rightChildren_add_le (p₁ :: p₂ :: rest)
        rw [hR] at h
        simp only [List.length_cons] at h
        omega
      let tl ← treeOfCodebook (l₁ :: ls)
      let tr ← treeOfCodebook (r₁ :: rs)
      pure (.branch tl tr)
termination_by pairs => codebookBitLength pairs

private theorem mem_leftChildren_imp {α : Type*} {ps : List (α × List Bool)} {q : α × List Bool}
    (hq : q ∈ leftChildren ps) : (q.1, false :: q.2) ∈ ps := by
  induction ps with
  | nil => cases hq
  | cons p ps ih =>
    rcases p with ⟨a, _ | ⟨b, bs⟩⟩
    · exact List.mem_cons_of_mem _ (ih hq)
    · cases b
      · rcases List.mem_cons.mp hq with rfl | htail
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih htail)
      · exact List.mem_cons_of_mem _ (ih hq)

private theorem mem_rightChildren_imp {α : Type*} {ps : List (α × List Bool)} {q : α × List Bool}
    (hq : q ∈ rightChildren ps) : (q.1, true :: q.2) ∈ ps := by
  induction ps with
  | nil => cases hq
  | cons p ps ih =>
    rcases p with ⟨a, _ | ⟨b, bs⟩⟩
    · exact List.mem_cons_of_mem _ (ih hq)
    · cases b
      · exact List.mem_cons_of_mem _ (ih hq)
      · rcases List.mem_cons.mp hq with rfl | htail
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih htail)

private theorem pairwise_leftChildren {α : Type*} {ps : List (α × List Bool)}
    (hinc : (ps.map Prod.snd).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁)) :
    ((leftChildren ps).map Prod.snd).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁) := by
  induction ps with
  | nil => simp [leftChildren]
  | cons p ps ih =>
    simp only [List.map_cons, List.pairwise_cons] at hinc
    rcases p with ⟨a, _ | ⟨b, bs⟩⟩
    · exact ih hinc.2
    · cases b
      · simp only [leftChildren, List.map_cons, List.pairwise_cons]
        refine ⟨?_, ih hinc.2⟩
        intro c hc
        rcases List.mem_map.mp hc with ⟨q, hq, rfl⟩
        have hmem : false :: q.2 ∈ ps.map Prod.snd :=
          List.mem_map.mpr ⟨(q.1, false :: q.2), mem_leftChildren_imp hq, rfl⟩
        have hrel := hinc.1 _ hmem
        exact ⟨fun hp => hrel.1 (List.cons_prefix_cons.mpr ⟨rfl, hp⟩),
          fun hp => hrel.2 (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)⟩
      · exact ih hinc.2

private theorem pairwise_rightChildren {α : Type*} {ps : List (α × List Bool)}
    (hinc : (ps.map Prod.snd).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁)) :
    ((rightChildren ps).map Prod.snd).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁) := by
  induction ps with
  | nil => simp [rightChildren]
  | cons p ps ih =>
    simp only [List.map_cons, List.pairwise_cons] at hinc
    rcases p with ⟨a, _ | ⟨b, bs⟩⟩
    · exact ih hinc.2
    · cases b
      · exact ih hinc.2
      · simp only [rightChildren, List.map_cons, List.pairwise_cons]
        refine ⟨?_, ih hinc.2⟩
        intro c hc
        rcases List.mem_map.mp hc with ⟨q, hq, rfl⟩
        have hmem : true :: q.2 ∈ ps.map Prod.snd :=
          List.mem_map.mpr ⟨(q.1, true :: q.2), mem_rightChildren_imp hq, rfl⟩
        have hrel := hinc.1 _ hmem
        exact ⟨fun hp => hrel.1 (List.cons_prefix_cons.mpr ⟨rfl, hp⟩),
          fun hp => hrel.2 (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)⟩

private theorem partition_children_of_ne_nil {α β : Type*} [AddCommMonoid β]
    (w : α → β) {ps : List (α × List Bool)} (hne : ∀ p ∈ ps, p.2 ≠ []) :
    ((leftChildren ps ++ rightChildren ps).map Prod.fst).Perm (ps.map Prod.fst) ∧
      (ps.map fun p => p.2.length • w p.1).sum =
        ((leftChildren ps).map fun p => p.2.length • w p.1).sum +
          ((rightChildren ps).map fun p => p.2.length • w p.1).sum +
          (ps.map fun p => w p.1).sum := by
  induction ps with
  | nil => simp [leftChildren, rightChildren]
  | cons p ps ih =>
    rcases p with ⟨a, _ | ⟨b, bs⟩⟩
    · exact absurd rfl (hne (a, []) List.mem_cons_self)
    · rcases ih (fun q hq => hne q (List.mem_cons_of_mem _ hq)) with ⟨hperm, hcost⟩
      cases b
      · simp only [leftChildren, rightChildren, List.cons_append, List.map_cons, List.sum_cons,
          List.length_cons, succ_nsmul, hcost]
        refine ⟨hperm.cons a, ?_⟩
        ac_rfl
      · simp only [leftChildren, rightChildren, List.map_append, List.map_cons, List.sum_cons,
          List.length_cons, succ_nsmul, hcost]
        rw [List.map_append] at hperm
        refine ⟨List.perm_middle.trans (hperm.cons a), ?_⟩
        ac_rfl

private theorem list_sum_nonneg {β : Type*} [AddCommMonoid β] [PartialOrder β]
    [IsOrderedAddMonoid β] {L : List β} (h : ∀ x ∈ L, 0 ≤ x) : 0 ≤ L.sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons]
    exact add_nonneg (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem x hy))

/-- On any nonempty prefix-incomparable codebook `pairs`, `treeOfCodebook pairs` succeeds and
produces a full binary `CodeTree α` with the same leaf multiset and at most the same weighted
path length under nonnegative weights. -/
theorem treeOfCodebook_spec {α β : Type*} [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    {pairs : List (α × List Bool)} (hne : pairs ≠ [])
    (hinc : (pairs.map Prod.snd).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁))
    {w : α → β} (hw : ∀ p ∈ pairs, 0 ≤ w p.1) :
    ∃ T, treeOfCodebook pairs = some T ∧
      T.leaves.Perm (pairs.map Prod.fst) ∧
      T.weightedPathLength w ≤ (pairs.map fun p => p.2.length • w p.1).sum := by
  suffices h : ∀ (n : ℕ) (ps : List (α × List Bool)),
      codebookBitLength ps ≤ n → ps ≠ [] →
      (ps.map Prod.snd).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁) →
      (∀ p ∈ ps, 0 ≤ w p.1) →
      ∃ T, treeOfCodebook ps = some T ∧
        T.leaves.Perm (ps.map Prod.fst) ∧
        T.weightedPathLength w ≤ (ps.map fun p => p.2.length • w p.1).sum by
    exact h _ pairs le_rfl hne hinc hw
  intro n
  induction n with
  | zero =>
    intro ps hsum hne hinc hw'
    match ps with
    | [] => exact absurd rfl hne
    | [(a, c)] =>
      refine ⟨.leaf a, by simp [treeOfCodebook], List.Perm.refl _, ?_⟩
      simp only [CodeTree.weightedPathLength_leaf, List.map_singleton, List.sum_singleton]
      exact nsmul_nonneg (hw' (a, c) List.mem_cons_self) c.length
    | p₁ :: p₂ :: rest =>
      simp only [codebookBitLength, List.map_cons, List.sum_cons] at hsum
      have hp₁ : p₁.2 = [] := List.length_eq_zero_iff.mp (by omega)
      simp only [List.map_cons, List.pairwise_cons] at hinc
      have hrel := hinc.1 p₂.2 List.mem_cons_self
      rw [hp₁] at hrel
      exact absurd List.nil_prefix hrel.1
  | succ n ih =>
    intro ps hsum hne hinc hw'
    match ps with
    | [] => exact absurd rfl hne
    | [(a, c)] =>
      refine ⟨.leaf a, by simp [treeOfCodebook], List.Perm.refl _, ?_⟩
      simp only [CodeTree.weightedPathLength_leaf, List.map_singleton, List.sum_singleton]
      exact nsmul_nonneg (hw' (a, c) List.mem_cons_self) c.length
    | p₁ :: p₂ :: rest =>
      have hno_nil : ∀ p ∈ (p₁ :: p₂ :: rest), p.2 ≠ [] := by
        intro p hp hnil
        simp only [List.map_cons, List.pairwise_cons] at hinc
        rcases List.mem_cons.mp hp with rfl | htail
        · exact (hinc.1 p₂.2 List.mem_cons_self).1 (hnil ▸ List.nil_prefix)
        · exact (hinc.1 p.2 (List.mem_map.mpr ⟨p, htail, rfl⟩)).2 (hnil ▸ List.nil_prefix)
      rcases partition_children_of_ne_nil w hno_nil with ⟨hperm_part, hcost_part⟩
      have hincL := pairwise_leftChildren hinc
      have hincR := pairwise_rightChildren hinc
      have hwL : ∀ p ∈ leftChildren (p₁ :: p₂ :: rest), 0 ≤ w p.1 := fun p hp =>
        hw' (p.1, false :: p.2) (mem_leftChildren_imp hp)
      have hwR : ∀ p ∈ rightChildren (p₁ :: p₂ :: rest), 0 ≤ w p.1 := fun p hp =>
        hw' (p.1, true :: p.2) (mem_rightChildren_imp hp)
      have hsum_nonneg : 0 ≤ ((p₁ :: p₂ :: rest).map fun p => w p.1).sum := by
        refine list_sum_nonneg ?_
        intro x hx
        rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
        exact hw' p hp
      rw [treeOfCodebook]
      split
      · next hL hR =>
        have hlen := hperm_part.length_eq
        rw [hL, hR] at hlen
        simp at hlen
      · next l₁ ls hL hR =>
        have hltL : codebookBitLength (l₁ :: ls) ≤ n := by
          have h := codebookBitLength_leftChildren_add_le (p₁ :: p₂ :: rest)
          rw [hL] at h
          simp only [List.length_cons] at h
          omega
        rw [hL] at hincL hwL
        rcases ih (l₁ :: ls) hltL (List.cons_ne_nil _ _) hincL hwL with
          ⟨tl, htl, hpermL, hwplL⟩
        rw [hL, hR, List.append_nil] at hperm_part
        rw [hL, hR] at hcost_part
        refine ⟨tl, htl, hpermL.trans hperm_part, ?_⟩
        rw [hcost_part]
        simp only [List.map_nil, List.sum_nil, add_zero]
        exact le_add_of_le_of_nonneg hwplL hsum_nonneg
      · next r₁ rs hL hR =>
        have hltR : codebookBitLength (r₁ :: rs) ≤ n := by
          have h := codebookBitLength_rightChildren_add_le (p₁ :: p₂ :: rest)
          rw [hR] at h
          simp only [List.length_cons] at h
          omega
        rw [hR] at hincR hwR
        rcases ih (r₁ :: rs) hltR (List.cons_ne_nil _ _) hincR hwR with
          ⟨tr, htr, hpermR, hwplR⟩
        rw [hL, hR, List.nil_append] at hperm_part
        rw [hL, hR] at hcost_part
        refine ⟨tr, htr, hpermR.trans hperm_part, ?_⟩
        rw [hcost_part]
        simp only [List.map_nil, List.sum_nil, zero_add]
        exact le_add_of_le_of_nonneg hwplR hsum_nonneg
      · next l₁ ls r₁ rs hL hR =>
        have hltL : codebookBitLength (l₁ :: ls) ≤ n := by
          have h := codebookBitLength_leftChildren_add_le (p₁ :: p₂ :: rest)
          rw [hL] at h
          simp only [List.length_cons] at h
          omega
        have hltR : codebookBitLength (r₁ :: rs) ≤ n := by
          have h := codebookBitLength_rightChildren_add_le (p₁ :: p₂ :: rest)
          rw [hR] at h
          simp only [List.length_cons] at h
          omega
        rw [hL] at hincL hwL
        rw [hR] at hincR hwR
        rcases ih (l₁ :: ls) hltL (List.cons_ne_nil _ _) hincL hwL with
          ⟨tl, htl, hpermL, hwplL⟩
        rcases ih (r₁ :: rs) hltR (List.cons_ne_nil _ _) hincR hwR with
          ⟨tr, htr, hpermR, hwplR⟩
        rw [hL, hR] at hperm_part hcost_part
        have hperm_br : (CodeTree.branch tl tr).leaves.Perm
            ((p₁ :: p₂ :: rest).map Prod.fst) := by
          rw [CodeTree.leaves_branch]
          have happ : (tl.leaves ++ tr.leaves).Perm
              (((l₁ :: ls) ++ (r₁ :: rs)).map Prod.fst) := by
            rw [List.map_append]
            exact hpermL.append hpermR
          exact happ.trans hperm_part
        have hwt_eq : tl.weight w + tr.weight w = ((p₁ :: p₂ :: rest).map fun p => w p.1).sum := by
          rw [← CodeTree.weight_branch, CodeTree.weight_eq_sum_leaves,
            (hperm_br.map w).sum_eq, List.map_map]
          rfl
        refine ⟨.branch tl tr, by simp [htl, htr], hperm_br, ?_⟩
        rw [CodeTree.weightedPathLength_branch, hwt_eq, hcost_part]
        exact add_le_add (add_le_add hwplL hwplR) le_rfl

/-- **Prefix-Free Code Tree Reduction**: every nonempty finite injective prefix-free binary code on
`syms` admits a full binary `CodeTree α` with the same leaf symbols and at most the same weighted
path length under nonnegative weights. -/
theorem exists_codeTree_of_isPrefixFree {α β : Type*}
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    {syms : List α} (hne : syms ≠ []) (hnodup : syms.Nodup)
    {code : α → List Bool}
    (hinj : Set.InjOn code {a | a ∈ syms})
    (hpf : InformationTheory.IsPrefixFree (code '' {a | a ∈ syms}))
    {w : α → β} (hw : ∀ a ∈ syms, 0 ≤ w a) :
    ∃ T : CodeTree α,
      T.leaves.Perm syms ∧
      T.weightedPathLength w ≤ (syms.map fun a => (code a).length • w a).sum := by
  let pairs := syms.map fun a => (a, code a)
  have hpairs_ne : pairs ≠ [] := by
    intro hnil
    exact hne (List.map_eq_nil_iff.mp hnil)
  have hsnd : pairs.map Prod.snd = syms.map code := by
    simp [pairs, List.map_map, Function.comp_def]
  have hinc : (pairs.map Prod.snd).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁) := by
    rw [hsnd, List.pairwise_map]
    have hsub : ∀ {L : List α}, L.Nodup → (∀ a ∈ L, a ∈ syms) →
        L.Pairwise (fun a b => ¬ code a <+: code b ∧ ¬ code b <+: code a) := by
      intro L hnd hmem
      induction L with
      | nil => exact List.Pairwise.nil
      | cons a as iha =>
        simp only [List.nodup_cons] at hnd
        refine List.Pairwise.cons ?_ (iha hnd.2 (fun x hx => hmem x (List.mem_cons_of_mem a hx)))
        intro b hb
        have hab : a ≠ b := fun hEq => hnd.1 (hEq ▸ hb)
        have hca : code a ∈ code '' {x | x ∈ syms} :=
          ⟨a, hmem a List.mem_cons_self, rfl⟩
        have hcb : code b ∈ code '' {x | x ∈ syms} :=
          ⟨b, hmem b (List.mem_cons_of_mem a hb), rfl⟩
        have hcne : code a ≠ code b := fun hEq =>
          hab (hinj (hmem a List.mem_cons_self) (hmem b (List.mem_cons_of_mem a hb)) hEq)
        exact ⟨fun hp => hcne (hpf _ hca _ hcb hp),
          fun hp => hcne.symm (hpf _ hcb _ hca hp)⟩
    exact hsub hnodup (fun a ha => ha)
  have hw_pairs : ∀ p ∈ pairs, 0 ≤ w p.1 := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨a, ha, rfl⟩
    exact hw a ha
  rcases treeOfCodebook_spec hpairs_ne hinc hw_pairs with ⟨T, _, hperm, hwpl⟩
  have hfst : pairs.map Prod.fst = syms := by
    simp [pairs, List.map_map, Function.comp_def]
  have hcost : (pairs.map fun p => p.2.length • w p.1) =
      syms.map fun a => (code a).length • w a := by
    simp [pairs, List.map_map, Function.comp_def]
  rw [hfst] at hperm
  rw [hcost] at hwpl
  exact ⟨T, hperm, hwpl⟩

/-- **McMillan Code Tree Reduction** (derived from McMillan's forward inequality [McMillan1956] /
[CoverThomas2006], Theorem 5.5.1 in Mathlib together with the finite binary Kraft converse of
Theorem 5.2.1 and `exists_codeTree_of_isPrefixFree`): every nonempty finite injective uniquely
decodable binary ($D = 2$) code on `syms` admits a full binary `CodeTree α` with the same leaf
symbols and at most the same weighted path length under nonnegative weights over any ordered
additive commutative monoid `β`. -/
theorem exists_codeTree_of_isUniquelyDecodable {α β : Type*}
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
    {syms : List α} (hne : syms ≠ []) (hnodup : syms.Nodup)
    {code : α → List Bool}
    (hinj : Set.InjOn code {a | a ∈ syms})
    (hud : InformationTheory.IsUniquelyDecodable (code '' {a | a ∈ syms}))
    {w : α → β} (hw : ∀ a ∈ syms, 0 ≤ w a) :
    ∃ T : CodeTree α,
      T.leaves.Perm syms ∧
      T.weightedPathLength w ≤ (syms.map fun a => (code a).length • w a).sum := by
  classical
  let s : Finset α := syms.toFinset
  have hs_coe : (s : Set α) = {a | a ∈ syms} := by
    ext x
    simp [s]
  let S : Finset (List Bool) := s.image code
  have hS_coe : (S : Set (List Bool)) = code '' {a | a ∈ syms} := by
    rw [Finset.coe_image, hs_coe]
  have hS_ud : InformationTheory.IsUniquelyDecodable (S : Set (List Bool)) := hS_coe ▸ hud
  have hmc := hS_ud.finsetSum_one_div_card_pow_length_le_one
  have hcard : (Fintype.card Bool : ℝ) = 2 := by
    have : Fintype.card Bool = 2 := Fintype.card_bool
    exact_mod_cast this
  rw [hcard] at hmc
  have hinj_s : Set.InjOn code (s : Set α) := hs_coe ▸ hinj
  have hsum_eq : (∑ c ∈ S, (1 / 2 : ℝ) ^ c.length) =
      ∑ a ∈ s, (1 / 2 : ℝ) ^ (code a).length :=
    Finset.sum_image fun a ha b hb hEq => hinj_s ha hb hEq
  rw [hsum_eq] at hmc
  rcases (exists_isPrefixFree_iff_kraft_le_one s (fun a => (code a).length)).mpr hmc with
    ⟨code', hinj', hpf', hlen'⟩
  rw [hs_coe] at hinj' hpf'
  rcases exists_codeTree_of_isPrefixFree hne hnodup hinj' hpf' hw with ⟨T, hperm, hwpl⟩
  have hcost_eq : (syms.map fun a => (code' a).length • w a) =
      syms.map fun a => (code a).length • w a :=
    List.map_congr_left fun a ha => by rw [hlen' a (List.mem_toFinset.mpr ha)]
  rw [hcost_eq] at hwpl
  exact ⟨T, hperm, hwpl⟩

end Cslib.Algorithms.Lean.Huffman
