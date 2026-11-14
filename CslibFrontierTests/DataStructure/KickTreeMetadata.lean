/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.KickTree.Facility
public import CslibFrontier.DataStructure.Dictionary.KickTree.Metadata
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Tests for KickTree Pure Metadata and Multi-Tier Facility Layer

Unit and non-vacuity tests covering:
1. **Four-Russians Bit-Table Specifications**:
   - `popcount`, `rank1`, `rank0`, `select1`, `select0`, `firstZeroBit`, `firstSetBit`.
   - `popcountTable` lookup evaluation matching semantic specification.
   - Boundedness theorems `rank1_le`, `rank0_le`, and soundness `select1_sound`, `select0_sound`.
2. **Mini-Array**:
   - Sequential read and write operations.
   - Point update correctness (`read_write_same` and `read_write_of_ne`).
   - Packed bit-size calculation and delimiter bitmap structure.
   - `delimiters_length_eq_totalBits` and `delimiters_count_delimiters` validation.
3. **Local Query Router (Prefix Trie)**:
   - Unique prefix insertion and routing queries (`query_insert_prefix`, `query_insert_same`).
   - Querying deleted prefix returning none (`query_delete_same`).
   - Deletion contracting empty branches, allowing subsequent insertion of prefixes.
   - Colliding prefix routing with shared prefix: divergent keys both retrieved,
     non-keys return none.
   - Frame theorem `query_insert_of_diverge` and key preservation `query_insert_two_distinct`.
   - DFS $(E_1, E_2)$ tree-shape and leaf-value encoding and decoding roundtrip
     (`decode_encode`).
4. **Free-Slot Tree**:
   - Depth-0 free-slot allocation (`allocSlot`) and deallocation (`freeSlot`).
   - Multi-level height-1 tree with $B = 2$ and 4 total slots, allocating, querying, and freeing.
   - Soundness and completeness of `findFree?` (`findFree?_sound`, `findFree?_complete`).
   - Structural validity `Valid` preservation under `allocSlot` and `freeSlot`.
   - Frame preservation (`allocSlot_leaf_of_ne`, `freeSlot_leaf_of_ne`).
5. **Multi-Tier Facility Layer**:
   - Configuration with power-of-two tier capacities and target ratios.
   - Item count conservation under `insertIntoTail`, `promoteFullTail`, and `tailReplace`.
   - Tier merging capacity arithmetic `merge_tier_length`.
-/

public section

namespace CslibFrontierTests.DataStructure.KickTreeMetadata

open Cslib.DataStructure.Dictionary.KickTree
open Cslib.DataStructure.Dictionary.KickTree.FourRussians
open Cslib.DataStructure.Dictionary.KickTree.PrefixTrie
open Cslib.DataStructure.Dictionary.KickTree.FreeSlotTree
open Cslib.DataStructure.Dictionary.KickTree.Facility
open Cslib.BitString

/-! ## 1. Four-Russians Bit-Table Tests -/

-- Test word 0b1011 = 11 in width 4
def sampleWord4 : Fin 16 := ⟨11, by decide⟩

example : (Cslib.BitString.equivFin 4).symm sampleWord4 ⟨0, by decide⟩ = true := by decide
example : (Cslib.BitString.equivFin 4).symm sampleWord4 ⟨1, by decide⟩ = true := by decide
example : (Cslib.BitString.equivFin 4).symm sampleWord4 ⟨2, by decide⟩ = false := by decide
example : (Cslib.BitString.equivFin 4).symm sampleWord4 ⟨3, by decide⟩ = true := by decide

example : popcount 4 sampleWord4 = 3 := by decide

example : rank1 4 sampleWord4 ⟨3, by decide⟩ = 2 := by decide

example : rank0 4 sampleWord4 ⟨3, by decide⟩ = 1 := by decide

example : rank1 4 sampleWord4 ⟨3, by decide⟩ ≤ 3 :=
  rank1_le 4 sampleWord4 ⟨3, by decide⟩

example : rank0 4 sampleWord4 ⟨3, by decide⟩ ≤ 3 :=
  rank0_le 4 sampleWord4 ⟨3, by decide⟩

example : rank0 4 sampleWord4 ⟨4, by decide⟩ + rank1 4 sampleWord4 ⟨4, by decide⟩ = 4 :=
  rank0_add_rank1 4 sampleWord4 ⟨4, by decide⟩

example : select1 4 sampleWord4 0 = some ⟨0, by decide⟩ := by decide
example : select1 4 sampleWord4 1 = some ⟨1, by decide⟩ := by decide
example : select1 4 sampleWord4 2 = some ⟨3, by decide⟩ := by decide

example : select0 4 sampleWord4 0 = some ⟨2, by decide⟩ := by decide

example : firstZeroBit 4 sampleWord4 = some ⟨2, by decide⟩ := by decide
example : firstSetBit 4 sampleWord4 = some ⟨0, by decide⟩ := by decide

-- Soundness theorems for select1 and select0
example : sampleWord4.val.testBit 0 = true :=
  select1_sound 4 sampleWord4 0 ⟨0, by decide⟩ (by decide)

example : sampleWord4.val.testBit 2 = false :=
  select0_sound 4 sampleWord4 0 ⟨2, by decide⟩ (by decide)

-- Table evaluation
example : (popcountTable 4).lookup sampleWord4 = 3 := by
  dsimp [popcountTable, popcount, sampleWord4]
  rfl

example : (popcountTable 4).spec ((Cslib.BitString.equivFin 4).symm sampleWord4) = 3 := by decide


-- Inversion theorems between rank and select
example : rank1 4 sampleWord4 ⟨1, by decide⟩ = 1 :=
  rank1_select1 4 sampleWord4 1 ⟨1, by decide⟩ (by decide)

example : rank0 4 sampleWord4 ⟨2, by decide⟩ = 0 :=
  rank0_select0 4 sampleWord4 0 ⟨2, by decide⟩ (by decide)

-- Domain completeness for select1 and select0
example : (select1 4 sampleWord4 1).isSome = true := by
  rw [select1_isSome_iff]
  decide

example : (select0 4 sampleWord4 0).isSome = true := by
  rw [select0_isSome_iff]
  decide

-- Bridge between FourRussians popcount and Nat.bitIndices / sum_testBit
example : popcount 4 sampleWord4 = sampleWord4.val.bitIndices.length :=
  popcount_eq_length_bitIndices 4 sampleWord4

example : popcount 4 sampleWord4 = ∑ i ∈ Finset.range 4, (sampleWord4.val.testBit i).toNat :=
  popcount_eq_sum_testBit 4 sampleWord4

/-! ## 2. Mini-Array Tests -/

def sampleMiniArray4 : MiniArray ℕ 4 :=
  ⟨fun i => match i.val with
    | 0 => 10
    | 1 => 20
    | 2 => 30
    | _ => 40⟩

example : sampleMiniArray4.read ⟨1, by decide⟩ = 20 := by decide

def updatedMiniArray4 := sampleMiniArray4.write ⟨1, by decide⟩ 99

example : updatedMiniArray4.read ⟨1, by decide⟩ = 99 := by decide
example : updatedMiniArray4.read ⟨0, by decide⟩ = 10 := by decide
example : updatedMiniArray4.read ⟨2, by decide⟩ = 30 := by decide

def sampleItemSize (n : ℕ) : ℕ := n / 10

example : sampleMiniArray4.totalBits sampleItemSize = 4 + (1 + 2 + 3 + 4) := by decide

example : sampleMiniArray4.itemOffset sampleItemSize ⟨2, by decide⟩ = 3 := by decide

example : (sampleMiniArray4.delimiters sampleItemSize).length =
    sampleMiniArray4.totalBits sampleItemSize :=
  sampleMiniArray4.delimiters_length_eq_totalBits sampleItemSize

example : ((sampleMiniArray4.delimiters sampleItemSize).filter id).length = 4 :=
  sampleMiniArray4.delimiters_count_delimiters sampleItemSize

/-! ## 3. Local Query Router (Prefix Trie) Tests -/

-- Build a small prefix trie with 2 leaves: 0 -> 100, 1 -> 200
def sampleTrie2 : PrefixTrie ℕ :=
  .branch (.leaf 100) (.leaf 200)

example : sampleTrie2.query [false] = some 100 := by decide
example : sampleTrie2.query [true] = some 200 := by decide

example : sampleTrie2.encodeE1 = [true, false, true, false, true] := by decide
example : sampleTrie2.encodeE2 = [100, 200] := by decide

example : decode sampleTrie2.encodeE1 sampleTrie2.encodeE2 = some sampleTrie2 :=
  decode_encode sampleTrie2

-- Prefix trie with two divergent keys sharing prefix [false]:
-- [false, true] -> 100, [false, false] -> 200
def step1Trie : PrefixTrie ℕ :=
  (insert? 100 .empty [false, true]).get (by decide)

def collidingTrie : PrefixTrie ℕ :=
  (insert? 200 step1Trie [false, false]).get (by decide)

example : collidingTrie.query [false, true] = some 100 := by decide
example : collidingTrie.query [false, false] = some 200 := by decide
example : collidingTrie.query [true] = none := by decide
example : collidingTrie.query [false, true, true] = some 100 := by decide

-- Collision-preventing insert? and zero silent drops
example : insert? 100 (PrefixTrie.leaf (α := ℕ) 42) [false] = none := rfl
example : insert? 100 (PrefixTrie.leaf (α := ℕ) 42) [] = none := rfl
example : (insert? 100 (.empty : PrefixTrie ℕ) [false, true]).isSome = true := by decide

-- Deletion contracts empty branches, allowing subsequent insertion of prefixes:
def sampleInsertTrie : PrefixTrie ℕ :=
  (insert? 42 .empty [false, false]).get (by decide)

def delPrefixTrie : PrefixTrie ℕ :=
  delete sampleInsertTrie [false, false]

example : delPrefixTrie = .empty := rfl
example : (insert? 99 delPrefixTrie [false]).isSome = true := by decide
example : (insert? 99 delPrefixTrie [false]) = some (.branch (.leaf 99) .empty) := rfl

-- Querying exact inserted prefix via query_insert_same
example :
    let opt_t := insert? 99 delPrefixTrie [false]
    let t := opt_t.get (by decide)
    query t [false] = some 99 := by
  have hins : insert? 99 delPrefixTrie [false] = some (.branch (.leaf 99) .empty) := rfl
  exact query_insert_same 99 delPrefixTrie _ [false] hins

-- Routing extensions via query_insert_prefix
example :
    let opt_t := insert? 100 (.empty : PrefixTrie ℕ) [false, true]
    let t := opt_t.get (by decide)
    query t ([false, true] ++ [true, false]) = some 100 := by
  have hins : insert? 100 (.empty : PrefixTrie ℕ) [false, true] =
      some (.branch (.branch .empty (.leaf 100)) .empty) := rfl
  exact query_insert_prefix 100 .empty _ [false, true] [true, false] hins

-- Frame theorem query_insert_of_diverge on divergent keys
example :
    let opt_t := insert? 100 (.branch .empty (.leaf 42) : PrefixTrie ℕ) ([false] ++ [true])
    let t := opt_t.get (by decide)
    query t ([false] ++ [false]) =
      query (.branch .empty (.leaf 42) : PrefixTrie ℕ) ([false] ++ [false]) := by
  have hins : insert? 100 (.branch .empty (.leaf 42) : PrefixTrie ℕ) ([false] ++ [true]) =
      some (.branch (.branch .empty (.leaf 100)) (.leaf 42)) := rfl
  exact query_insert_of_diverge 100 [false] true false (by decide) [] [] _ _ hins

-- Key preservation query_insert_two_distinct
example :
    let opt_t1 := insert? 100 (.empty : PrefixTrie ℕ) ([false] ++ [true])
    let t1 := opt_t1.get (by decide)
    let opt_t2 := insert? 200 t1 ([false] ++ [false])
    let t2 := opt_t2.get (by decide)
    query t2 ([false] ++ [true]) = some 100 ∧ query t2 ([false] ++ [false]) = some 200 := by
  have h1 : insert? 100 (.empty : PrefixTrie ℕ) ([false] ++ [true]) =
      some (.branch (.branch .empty (.leaf 100)) .empty) := rfl
  have h2 : insert? 200 (.branch (.branch .empty (.leaf 100)) .empty) ([false] ++ [false]) =
      some (.branch (.branch (.leaf 200) (.leaf 100)) .empty) := rfl
  exact query_insert_two_distinct 100 200 [false] true false (by decide) [] [] _ _ h1 h2

-- Deletion test
example : (collidingTrie.delete [false, true]).query [false, true] = none :=
  query_delete_same [false, true] collidingTrie

example : (collidingTrie.delete [false, true]).query [false, false] = some 200 := by decide

/-! ## 4. Free-Slot Tree Tests -/

-- Leaf with 4 slots: slot 0 and 2 free (0b0101 = 5)
def sampleFreeBits4 : Fin 4 → Bool
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false
  | ⟨2, _⟩ => true
  | ⟨3, _⟩ => false

def sampleLeafTree4 : FreeSlotTree 4 0 := .leaf sampleFreeBits4

example : sampleLeafTree4.isFree 0 = true := by decide
example : sampleLeafTree4.isFree 1 = false := by decide
example : sampleLeafTree4.isFree 2 = true := by decide
example : sampleLeafTree4.findFree? = some 0 := by decide

example : sampleLeafTree4.isFree 0 = true :=
  findFree?_sound sampleLeafTree4 trivial (i := 0) (by decide)

-- Height 1 FreeSlotTree with B = 2 (depth 1, 2 children of size 2, total 4 slots)
def child0 : FreeSlotTree 2 0 := .leaf (fun i => match i.val with | 0 => true | _ => false)
def child1 : FreeSlotTree 2 0 := .leaf (fun i => match i.val with | 0 => false | _ => true)

def sampleTree2_1 : FreeSlotTree 2 1 :=
  .node 0 (fun i => match i.val with | 0 => true | _ => true)
    (fun i => match i.val with | 0 => child0 | _ => child1)

example : sampleTree2_1.isFree 0 = true := by decide
example : sampleTree2_1.isFree 1 = false := by decide
example : sampleTree2_1.isFree 2 = false := by decide
example : sampleTree2_1.isFree 3 = true := by decide
example : sampleTree2_1.findFree? = some 0 := by decide

example : sampleTree2_1.Valid := by
  dsimp [Valid, sampleTree2_1, child0, child1, hasFree]
  refine ⟨fun i => by fin_cases i <;> trivial, ?_⟩
  intro i
  fin_cases i <;> decide

-- Allocate slot 0 in height 1 tree
def allocatedTree2_1 := sampleTree2_1.allocSlot 0

example : (sampleLeafTree4.allocSlot 0).isFree 2 = sampleLeafTree4.isFree 2 :=
  allocSlot_leaf_of_ne sampleFreeBits4 (i := ⟨0, by decide⟩) (j := ⟨2, by decide⟩) (by decide)

example : (sampleLeafTree4.freeSlot 0).isFree 2 = sampleLeafTree4.isFree 2 :=
  freeSlot_leaf_of_ne sampleFreeBits4 (i := ⟨0, by decide⟩) (j := ⟨2, by decide⟩) (by decide)

example : allocatedTree2_1.isFree 0 = false := by decide
example : allocatedTree2_1.isFree 3 = true := by decide
example : allocatedTree2_1.findFree? = some 3 := by decide

example : allocatedTree2_1.Valid :=
  allocSlot_preserves_valid sampleTree2_1 0 (by
    dsimp [Valid, sampleTree2_1, child0, child1, hasFree]
    refine ⟨fun i => by fin_cases i <;> trivial, ?_⟩
    intro i
    fin_cases i <;> decide)


-- Full-height tree slot update and frame theorems
example : (sampleTree2_1.allocSlot 0).isFree 0 = false :=
  allocSlot_self sampleTree2_1 (by decide)

example : (sampleTree2_1.allocSlot 0).isFree 3 = sampleTree2_1.isFree 3 :=
  allocSlot_of_ne sampleTree2_1 (by decide)

example : (allocatedTree2_1.freeSlot 0).isFree 0 = true :=
  freeSlot_self allocatedTree2_1 (by decide)

example : (allocatedTree2_1.freeSlot 0).isFree 3 = allocatedTree2_1.isFree 3 :=
  freeSlot_of_ne allocatedTree2_1 (by decide)

-- Free slot 0 in height 1 tree
def freedTree2_1 := allocatedTree2_1.freeSlot 0

example : freedTree2_1.isFree 0 = true := by decide
example : freedTree2_1.findFree? = some 0 := by decide

example : freedTree2_1.Valid :=
  freeSlot_preserves_valid allocatedTree2_1 0 (by
    dsimp [Valid, allocatedTree2_1, sampleTree2_1, child0, child1, hasFree, allocSlot, setSlot]
    refine ⟨fun i => by fin_cases i <;> trivial, ?_⟩
    intro i
    fin_cases i <;> decide)

-- Soundness and completeness on height 1 tree
example : sampleTree2_1.isFree 0 = true :=
  findFree?_sound sampleTree2_1 (by
    dsimp [Valid, sampleTree2_1, child0, child1, hasFree]
    refine ⟨fun i => by fin_cases i <;> trivial, ?_⟩
    intro i
    fin_cases i <;> decide) (i := 0) (by decide)

example : ∃ i, sampleTree2_1.findFree? = some i :=
  findFree?_complete sampleTree2_1 (by
    dsimp [Valid, sampleTree2_1, child0, child1, hasFree]
    refine ⟨fun i => by fin_cases i <;> trivial, ?_⟩
    intro i
    fin_cases i <;> decide) (by decide)

/-! ## 5. Multi-Tier Facility Layer Tests -/

-- Sample configuration: kEff = 2
-- Tier 0 capacity = 8, Tier 1 capacity = 16, Tier 2 capacity = 32
def sampleFacilityConfig : FacilityConfig where
  kEff := 2
  kEff_pos := by decide
  r := fun j => match j.val with
    | 0 => 8
    | 1 => 16
    | _ => 32
  r_pos := fun j => by
    fin_cases j <;> decide
  t := fun ⟨j, _⟩ => match j with
    | 0 => 2
    | _ => 2
  t_mul_r := fun j => by
    fin_cases j <;> decide

example : sampleFacilityConfig.r1 = 8 := by decide

-- Sample facility with one 100% full cubby and one tail cubby
def sampleFullItems8 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8]
def sampleTailItems : List ℕ := [101, 102, 103]

def sampleFullCubby8 : FullCubby sampleFacilityConfig ℕ :=
  ⟨⟨0, by decide⟩, sampleFullItems8, by decide⟩

def sampleTailCubby8 : TailCubby sampleFacilityConfig ℕ :=
  ⟨sampleTailItems, by decide⟩

def sampleFacility : Facility sampleFacilityConfig ℕ where
  fullCubbies := [sampleFullCubby8]
  tail := sampleTailCubby8

example : sampleFacility.totalItems = 11 := by decide

-- Tail insertion test: item conservation
def insertedFacility := (sampleFacility.insertIntoTail 999).get (by decide)
example : insertedFacility.totalItems = 12 := by decide

example : ∀ F', sampleFacility.insertIntoTail 999 = some F' → F'.totalItems = 12 := by
  intro F' hF'
  have h := totalItems_insertIntoTail sampleFacility 999 F' hF'
  rw [h]
  decide

-- Full tail promotion test: item conservation
def fullTailFacility : Facility sampleFacilityConfig ℕ where
  fullCubbies := []
  tail := ⟨[1, 2, 3, 4, 5, 6, 7, 8], by decide⟩

example : fullTailFacility.totalItems = 8 := by decide
def promotedFacility := fullTailFacility.promoteFullTail.get (by decide)
example : promotedFacility.totalItems = 8 := by decide

example : ∀ F', fullTailFacility.promoteFullTail = some F' → F'.totalItems = 8 := by
  intro F' hF'
  have h := totalItems_promoteFullTail fullTailFacility F' hF'
  rw [h]
  decide

-- Tail replacement on deletion from slot 3 of full cubby using tail item at index 1:
def replacedFacility := (sampleFacility.tailReplace 0 3 1).get (by decide)
example : replacedFacility.totalItems = 10 := by decide
example : replacedFacility.tail.items = [101, 103] := by decide
example : (replacedFacility.fullCubbies[0]?).map (fun c => c.items) =
    some [1, 2, 3, 102, 5, 6, 7, 8] := by decide

example : ∀ F', sampleFacility.tailReplace 0 3 1 = some F' → F'.totalItems = 10 := by
  intro F' hF'
  have htot : sampleFacility.totalItems = 11 := by decide
  have h := totalItems_tailReplace sampleFacility 0 3 1 F' hF'
  omega

-- Tier merge theorem
example : ([sampleFullItems8, sampleFullItems8].flatten).length =
    sampleFacilityConfig.r ⟨1, by decide⟩ := by
  have hall : ∀ l ∈ [sampleFullItems8, sampleFullItems8],
      l.length = sampleFacilityConfig.r ⟨0, by decide⟩ := by
    intro l hl
    cases hl with
    | head => decide
    | tail _ h =>
      cases h with
      | head => decide
      | tail _ h' => contradiction
  exact merge_tier_length (cfg := sampleFacilityConfig) ⟨0, by decide⟩
    [sampleFullItems8, sampleFullItems8] (by decide) hall

end CslibFrontierTests.DataStructure.KickTreeMetadata
