/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Huffman.Basic
public import Mathlib.InformationTheory.Coding.Kraft
public import Mathlib.InformationTheory.Coding.KraftMcMillan

import Mathlib.Algebra.Order.BigOperators.Group.List
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
    simp only [Nat.pow_zero, Nat.lt_one_iff] at hq
    subst hq; rfl
  | succ k ih =>
    rw [Nat.pow_succ] at hq
    have hbit : natOfBits [decide (q % 2 = 1)] = q % 2 := by grind [natOfBits]
    rw [bitsOfNat, natOfBits_append, ih (by omega), List.length_singleton, Nat.pow_one, hbit]
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
  have hmul : (natOfBits t + 1) * 2 ^ (L - (c₁.length + t.length)) ≤ 2 ^ (L - c₁.length) := by
    rw [hsub, Nat.pow_add]
    exact Nat.mul_le_mul_right _ (natOfBits_lt_two_pow t)
  have hpos : 0 < 2 ^ (L - (c₁.length + t.length)) := Nat.two_pow_pos _
  rw [hexp]
  rw [Nat.add_mul, Nat.one_mul] at hmul
  exact ⟨Nat.le_add_right _ _, by omega⟩

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
    have hq_lt : offset / 2 ^ (L - ℓ a) < 2 ^ ℓ a := by
      refine Nat.div_lt_of_lt_mul ?_
      rw [← Nat.pow_add, Nat.sub_add_cancel haL]
      omega
    have hca_len : (bitsOfNat (ℓ a) (offset / 2 ^ (L - ℓ a))).length = ℓ a :=
      length_bitsOfNat _ _
    have hca_start : dyadicStart L (bitsOfNat (ℓ a) (offset / 2 ^ (L - ℓ a))) = offset := by
      unfold dyadicStart
      rw [hca_len, natOfBits_bitsOfNat hq_lt, Nat.div_mul_cancel ha_dvd]
    have hL' : ∀ x ∈ xs, ℓ x ≤ L := fun x hx => hL x (List.mem_cons_of_mem a hx)
    have hdvd' : ∀ x ∈ xs, 2 ^ (L - ℓ x) ∣ offset + 2 ^ (L - ℓ a) := fun x hx =>
      Nat.dvd_add (hdvd x (List.mem_cons_of_mem a hx)) (Nat.pow_dvd_pow 2 (by grind))
    rcases ih (offset + 2 ^ (L - ℓ a)) hL' hpw.2 hdvd' (by omega) with ⟨hbds, hpw_tail⟩
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [kraftAssign, List.mem_cons, List.map_cons, List.sum_cons] at hp ⊢
      rcases hp with rfl | htail
      · dsimp only; rw [hca_start]; exact ⟨le_rfl, by omega⟩
      · rcases hbds p htail with ⟨hlo, hhi⟩; exact ⟨by omega, by omega⟩
    · simp only [kraftAssign, List.map_cons, List.pairwise_cons]
      refine ⟨?_, hpw_tail⟩
      intro c hc
      rcases List.mem_map.mp hc with ⟨p, hp, rfl⟩
      have hp_L : p.2.length ≤ L := by
        rw [length_snd_of_mem_kraftAssign hp]
        exact hL' p.1 (map_fst_kraftAssign L ℓ (offset + 2 ^ (L - ℓ a)) xs ▸
          List.mem_map.mpr ⟨p, hp, rfl⟩)
      rcases hbds p hp with ⟨hp_lo, _⟩
      exact ⟨fun h => by
          have := (dyadicStart_bounds_of_prefix h hp_L).2
          rw [hca_start, hca_len] at this; omega,
        fun h => by
          have := (dyadicStart_bounds_of_prefix h (hca_len ▸ haL)).1
          rw [hca_start] at this; omega⟩

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
    have htot : ∀ a b, (decide (ℓ a ≤ ℓ b) || decide (ℓ b ≤ ℓ a)) = true := by grind
    have htr : ∀ a b c, decide (ℓ a ≤ ℓ b) = true → decide (ℓ b ≤ ℓ c) = true →
        decide (ℓ a ≤ ℓ c) = true := by grind
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
    have ha_fst : a ∈ pairs.map Prod.fst := hfst ▸ hperm.symm.subset (Finset.mem_toList.mpr ha)
    rcases List.mem_map.mp ha_fst with ⟨p, hp, rfl⟩
    cases hfind : pairs.find? (fun q => q.1 == p.1) with
    | none => exact absurd (List.find?_eq_none.mp hfind p hp) (by simp)
    | some q =>
      have hq1 : q.1 = p.1 := by simpa using List.find?_some hfind
      dsimp only [code]; rw [hfind, ← hq1]
      exact List.mem_of_find?_eq_some hfind
  have hinj_pairs : ∀ {a b : α}, a ∈ s → b ∈ s → code a = code b → a = b := by
    intro a b ha hb hEq
    by_contra hne
    have hrel := CodeTree.pairwise_rel_of_ne (fun h => ⟨h.2, h.1⟩) (List.pairwise_map.mp hspec)
      (hcode_mem a ha) (hcode_mem b hb) (fun h => hne (Prod.mk.inj h).1)
    exact hrel.1 (hEq ▸ List.prefix_refl _)
  refine ⟨code, fun a ha b hb hEq => hinj_pairs ha hb hEq, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hpref
    by_contra hne
    exact (CodeTree.pairwise_rel_of_ne (fun h => ⟨h.2, h.1⟩) hspec
      (List.mem_map.mpr ⟨_, hcode_mem a ha, rfl⟩)
      (List.mem_map.mpr ⟨_, hcode_mem b hb, rfl⟩) hne).1 hpref
  · exact fun a ha => length_snd_of_mem_kraftAssign (hcode_mem a ha)

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
    have hS : InformationTheory.IsPrefixFree
        ((s.image code : Finset (List Bool)) : Set (List Bool)) := by
      simpa [Finset.coe_image] using hpf
    have hkraft := hS.finsetSum_one_div_card_pow_length_le_one
    have hcard : (Fintype.card Bool : ℝ) = 2 := by simp
    rw [hcard, Finset.sum_image (fun a ha b hb hEq => hinj ha hb hEq)] at hkraft
    exact (Finset.sum_congr rfl fun a ha => by rw [hlen a ha]).symm.trans_le hkraft
  · intro hkraft
    let L : ℕ := s.sup ℓ
    have hL : ∀ a ∈ s, ℓ a ≤ L := fun _ ha => Finset.le_sup ha
    have hnat : (∑ a ∈ s, 2 ^ (L - ℓ a)) ≤ 2 ^ L := by
      have hcast_mul : ∀ t : Finset α, (∀ a ∈ t, ℓ a ≤ L) →
          ((∑ a ∈ t, 2 ^ (L - ℓ a) : ℕ) : ℝ) = (2 : ℝ) ^ L * ∑ a ∈ t, (1 / 2 : ℝ) ^ ℓ a := by
        intro t ht
        induction t using Finset.induction_on with
        | empty => simp
        | insert a t ha ih =>
          rw [Finset.sum_insert ha, Nat.cast_add, Finset.sum_insert ha,
            ih fun x hx => ht x (Finset.mem_insert_of_mem hx), mul_add]
          congr 1
          have hpow : (2 : ℝ) ^ L = (2 : ℝ) ^ (L - ℓ a) * (2 : ℝ) ^ ℓ a := by
            rw [← pow_add, Nat.sub_add_cancel (ht a (Finset.mem_insert_self a t))]
          push_cast
          rw [hpow, mul_assoc, ← mul_pow]
          norm_num
      have hreal : ((∑ a ∈ s, 2 ^ (L - ℓ a) : ℕ) : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
        rw [hcast_mul s hL]
        push_cast
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) L]
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

private theorem leftChildren_eq_filterMap {α : Type*} (ps : List (α × List Bool)) :
    leftChildren ps = ps.filterMap fun p =>
      p.2.casesOn none fun b bs => if b == false then some (p.1, bs) else none := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a, _ | ⟨false | true, bs⟩⟩ <;> simp [leftChildren, ih]

private theorem rightChildren_eq_filterMap {α : Type*} (ps : List (α × List Bool)) :
    rightChildren ps = ps.filterMap fun p =>
      p.2.casesOn none fun b bs => if b == true then some (p.1, bs) else none := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a, _ | ⟨false | true, bs⟩⟩ <;> simp [rightChildren, ih]

private theorem codebookBitLength_filterMap_add_le {α : Type*} (bit : Bool)
    (ps : List (α × List Bool)) :
    let ch := ps.filterMap fun p =>
      p.2.casesOn none fun b bs => if b == bit then some (p.1, bs) else none
    codebookBitLength ch + ch.length ≤ codebookBitLength ps := by
  induction ps with
  | nil => simp [codebookBitLength]
  | cons p ps ih =>
    rcases p with ⟨a, _ | ⟨b, bs⟩⟩
    · simp only [List.filterMap_cons, codebookBitLength, List.map_cons, List.sum_cons] at ih ⊢
      omega
    · by_cases hb : b = bit
      · simp only [List.filterMap_cons, hb, beq_self_eq_true, ↓reduceIte, codebookBitLength,
          List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
        omega
      · simp only [List.filterMap_cons, beq_false_of_ne hb, Bool.false_eq_true, ↓reduceIte,
          codebookBitLength, List.map_cons, List.sum_cons] at ih ⊢
        omega

private theorem codebookBitLength_leftChildren_add_le {α : Type*} (ps : List (α × List Bool)) :
    codebookBitLength (leftChildren ps) + (leftChildren ps).length ≤ codebookBitLength ps := by
  rw [leftChildren_eq_filterMap]
  exact codebookBitLength_filterMap_add_le false ps

private theorem codebookBitLength_rightChildren_add_le {α : Type*} (ps : List (α × List Bool)) :
    codebookBitLength (rightChildren ps) + (rightChildren ps).length ≤ codebookBitLength ps := by
  rw [rightChildren_eq_filterMap]
  exact codebookBitLength_filterMap_add_le true ps

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

private theorem mem_filterMap_children_imp {α : Type*} {bit : Bool} {ps : List (α × List Bool)}
    {q : α × List Bool}
    (hq : q ∈ ps.filterMap fun p =>
      p.2.casesOn none fun b bs => if b == bit then some (p.1, bs) else none) :
    (q.1, bit :: q.2) ∈ ps := by
  rcases List.mem_filterMap.mp hq with ⟨⟨a, _ | ⟨b, bs⟩⟩, hp, h⟩
  · simp at h
  · by_cases hb : b = bit
    · simp only [hb, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [hb] using hp
    · simp only [beq_false_of_ne hb, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

private theorem pairwise_filterMap_children {α : Type*} (bit : Bool) {ps : List (α × List Bool)}
    (hinc : (ps.map Prod.snd).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁)) :
    ((ps.filterMap fun p =>
      p.2.casesOn none fun b bs => if b == bit then some (p.1, bs) else none).map
      Prod.snd).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.pairwise_cons] at hinc
    rcases p with ⟨a, _ | ⟨b, bs⟩⟩
    · exact ih hinc.2
    · by_cases hb : b = bit
      · simp only [List.filterMap_cons, hb, beq_self_eq_true, ↓reduceIte, List.map_cons,
          List.pairwise_cons]
        refine ⟨?_, ih hinc.2⟩
        intro c hc
        rcases List.mem_map.mp hc with ⟨q, hq, rfl⟩
        have hrel := hinc.1 _ (List.mem_map.mpr ⟨_, mem_filterMap_children_imp hq, rfl⟩)
        exact ⟨fun hp => hrel.1 (List.cons_prefix_cons.mpr ⟨hb, hp⟩),
          fun hp => hrel.2 (List.cons_prefix_cons.mpr ⟨hb.symm, hp⟩)⟩
      · simp only [List.filterMap_cons, beq_false_of_ne hb, Bool.false_eq_true, ↓reduceIte]
        exact ih hinc.2

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
        exact ⟨hperm.cons a, by ac_rfl⟩
      · simp only [leftChildren, rightChildren, List.map_append, List.map_cons, List.sum_cons,
          List.length_cons, succ_nsmul, hcost]
        rw [List.map_append] at hperm
        exact ⟨List.perm_middle.trans (hperm.cons a), by ac_rfl⟩

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
      codebookBitLength ps = n → ps ≠ [] →
      (ps.map Prod.snd).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁) →
      (∀ p ∈ ps, 0 ≤ w p.1) →
      ∃ T, treeOfCodebook ps = some T ∧
        T.leaves.Perm (ps.map Prod.fst) ∧
        T.weightedPathLength w ≤ (ps.map fun p => p.2.length • w p.1).sum from
    h _ pairs rfl hne hinc hw
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
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
      have hincL := leftChildren_eq_filterMap (p₁ :: p₂ :: rest) ▸
        pairwise_filterMap_children false hinc
      have hincR := rightChildren_eq_filterMap (p₁ :: p₂ :: rest) ▸
        pairwise_filterMap_children true hinc
      have hwL : ∀ p ∈ leftChildren (p₁ :: p₂ :: rest), 0 ≤ w p.1 := fun p hp =>
        hw' (p.1, false :: p.2) (mem_filterMap_children_imp (leftChildren_eq_filterMap _ ▸ hp))
      have hwR : ∀ p ∈ rightChildren (p₁ :: p₂ :: rest), 0 ≤ w p.1 := fun p hp =>
        hw' (p.1, true :: p.2) (mem_filterMap_children_imp (rightChildren_eq_filterMap _ ▸ hp))
      have hsum_nonneg : 0 ≤ ((p₁ :: p₂ :: rest).map fun p => w p.1).sum :=
        List.sum_nonneg fun x hx => by rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩; exact hw' p hp
      rw [treeOfCodebook]
      split
      · next hL hR =>
        have hlen := hperm_part.length_eq
        rw [hL, hR] at hlen; simp at hlen
      · next l₁ ls hL hR =>
        have hltL : codebookBitLength (l₁ :: ls) < n := by
          have h := codebookBitLength_leftChildren_add_le (p₁ :: p₂ :: rest)
          rw [hL] at h; simp only [List.length_cons] at h; omega
        rw [hL] at hincL hwL
        rcases ih _ hltL (l₁ :: ls) rfl (List.cons_ne_nil _ _) hincL hwL with
          ⟨tl, htl, hpermL, hwplL⟩
        rw [hL, hR, List.append_nil] at hperm_part
        rw [hL, hR] at hcost_part
        refine ⟨tl, htl, hpermL.trans hperm_part, ?_⟩
        rw [hcost_part]
        simp only [List.map_nil, List.sum_nil, add_zero]
        exact le_add_of_le_of_nonneg hwplL hsum_nonneg
      · next r₁ rs hL hR =>
        have hltR : codebookBitLength (r₁ :: rs) < n := by
          have h := codebookBitLength_rightChildren_add_le (p₁ :: p₂ :: rest)
          rw [hR] at h; simp only [List.length_cons] at h; omega
        rw [hR] at hincR hwR
        rcases ih _ hltR (r₁ :: rs) rfl (List.cons_ne_nil _ _) hincR hwR with
          ⟨tr, htr, hpermR, hwplR⟩
        rw [hL, hR, List.nil_append] at hperm_part
        rw [hL, hR] at hcost_part
        refine ⟨tr, htr, hpermR.trans hperm_part, ?_⟩
        rw [hcost_part]
        simp only [List.map_nil, List.sum_nil, zero_add]
        exact le_add_of_le_of_nonneg hwplR hsum_nonneg
      · next l₁ ls r₁ rs hL hR =>
        have hltL : codebookBitLength (l₁ :: ls) < n := by
          have h := codebookBitLength_leftChildren_add_le (p₁ :: p₂ :: rest)
          rw [hL] at h; simp only [List.length_cons] at h; omega
        have hltR : codebookBitLength (r₁ :: rs) < n := by
          have h := codebookBitLength_rightChildren_add_le (p₁ :: p₂ :: rest)
          rw [hR] at h; simp only [List.length_cons] at h; omega
        rw [hL] at hincL hwL; rw [hR] at hincR hwR
        rcases ih _ hltL (l₁ :: ls) rfl (List.cons_ne_nil _ _) hincL hwL with
          ⟨tl, htl, hpermL, hwplL⟩
        rcases ih _ hltR (r₁ :: rs) rfl (List.cons_ne_nil _ _) hincR hwR with
          ⟨tr, htr, hpermR, hwplR⟩
        rw [hL, hR] at hperm_part hcost_part
        have hperm_br : (CodeTree.branch tl tr).leaves.Perm
            ((p₁ :: p₂ :: rest).map Prod.fst) :=
          ((List.map_append ▸ hpermL.append hpermR) : _).trans hperm_part
        have hwt_eq : tl.weight w + tr.weight w = ((p₁ :: p₂ :: rest).map fun p => w p.1).sum := by
          rw [← CodeTree.weight_branch, CodeTree.weight_eq_sum_leaves,
            (hperm_br.map w).sum_eq, List.map_map]; rfl
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
  have hpairs_ne : pairs ≠ [] := fun hnil => hne (List.map_eq_nil_iff.mp hnil)
  have hsnd : pairs.map Prod.snd = syms.map code := by
    simp [pairs, List.map_map, Function.comp_def]
  have hinc : (pairs.map Prod.snd).Pairwise (fun c₁ c₂ => ¬ c₁ <+: c₂ ∧ ¬ c₂ <+: c₁) := by
    rw [hsnd, List.pairwise_map]
    refine hnodup.imp_of_mem fun {a b} ha hb hab => ?_
    have hcne : code a ≠ code b := fun hEq => hab (hinj ha hb hEq)
    exact ⟨fun hp => hcne (hpf _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hp),
      fun hp => hcne.symm (hpf _ ⟨b, hb, rfl⟩ _ ⟨a, ha, rfl⟩ hp)⟩
  have hw_pairs : ∀ p ∈ pairs, 0 ≤ w p.1 := fun p hp => by
    rcases List.mem_map.mp hp with ⟨a, ha, rfl⟩; exact hw a ha
  rcases treeOfCodebook_spec hpairs_ne hinc hw_pairs with ⟨T, _, hperm, hwpl⟩
  have hfst : pairs.map Prod.fst = syms := by simp [pairs, List.map_map, Function.comp_def]
  have hcost : (pairs.map fun p => p.2.length • w p.1) =
      syms.map fun a => (code a).length • w a := by
    simp [pairs, List.map_map, Function.comp_def]
  exact ⟨T, hfst ▸ hperm, hcost ▸ hwpl⟩

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
  have hs_coe : (s : Set α) = {a | a ∈ syms} := by ext x; simp [s]
  have hS_ud : InformationTheory.IsUniquelyDecodable
      ((s.image code : Finset (List Bool)) : Set (List Bool)) := by
    simpa [Finset.coe_image, hs_coe] using hud
  have hmc := hS_ud.finsetSum_one_div_card_pow_length_le_one
  have hcard : (Fintype.card Bool : ℝ) = 2 := by simp
  rw [hcard, Finset.sum_image (fun a ha b hb hEq => hinj (hs_coe ▸ ha) (hs_coe ▸ hb) hEq)] at hmc
  rcases (exists_isPrefixFree_iff_kraft_le_one s (fun a => (code a).length)).mpr hmc with
    ⟨code', hinj', hpf', hlen'⟩
  rw [hs_coe] at hinj' hpf'
  rcases exists_codeTree_of_isPrefixFree hne hnodup hinj' hpf' hw with ⟨T, hperm, hwpl⟩
  have hcost_eq : (syms.map fun a => (code' a).length • w a) =
      syms.map fun a => (code a).length • w a :=
    List.map_congr_left fun a ha => by rw [hlen' a (List.mem_toFinset.mpr ha)]
  exact ⟨T, hperm, hcost_eq ▸ hwpl⟩

end Cslib.Algorithms.Lean.Huffman
