/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
public import Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORProgramGeneration
import all Complexity.Cryptanalysis.AddXNORSortedRecords
import all Complexity.Cryptanalysis.AddXNORNativeBuckets
import all Complexity.Cryptanalysis.AddXNORBitInput
import all Complexity.Computability.GenericRAM.Native.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Original source input to an actually generated sorted projected quarter

The machine receives the original operand list, computes the source quarter cut,
first-operand seed and capped projection depth, projects the first quarter and
executes packed-index generation, chain evaluation and uniform radix sorting.
Preparation, materialization, bit arithmetic, sorting and every transient prefix
are charged. No materialized quarter, executable or simulation contract is input.

For `q = N - 1` and `k = q / 4` this is an actual deterministic multitape
`O*(2^k)` time/space component of [WangLvShenZhang2027], Lemma 8,
PDF pp. 21–22, with polynomial overhead in original bit length explicit below.
Class counts/matching, inverse quarters, smaller-side full-state retention,
release/reuse and global source witness/miss resources are not supplied by this
first-quarter route. The existing complete uniform dissection execution remains
available with its old compaction/interpreter costs; it is not changed here.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR.SourceQuarter
open Turing.MultiTapeTM Cslib.GenericRAM ProgramGeneration

/-- Compute the actual source cut/depth, then project original first-quarter operands and seed. -/
def prepare (input : Source.Input) : SortedQuarterMachine.Input :=
  let source := Source.prepare input
  let depth := source.1.1.2
  let seed := source.1.2.1
  let operands := source.2.1.1
  let modulus := 2 ^ depth
  ((depth, seed % modulus), operands.map (fun a => a % modulus))

/-- This path executes the sorter/generator directly, bypassing sparse RAM interpretation. -/
def run (input : Source.Input) : List (ℕ × ℕ) := SortedQuarterMachine.run (prepare input)

/-- Source preparation and all modular projections are real polynomial-time computations. -/
theorem prepare_polyTime : ComputableInPolyTime prepare Source.encoding
    SortedQuarterMachine.encoding := by
  have hdepth : ComputableInPolyTime (fun x : Source.Input => (Source.prepare x).1.1.2)
      Source.encoding encUnary := by
    have h : ComputableInPolyTime (fun x : ProgramGeneration.Source => x.1.1.2)
        sourceEncoding encUnary := by fun_prop
    exact h.comp Source.prepare_polyTime
  have hseed : ComputableInPolyTime (fun x : Source.Input => (Source.prepare x).1.2.1)
      Source.encoding encNat := by
    have h : ComputableInPolyTime (fun x : ProgramGeneration.Source => x.1.2.1)
        sourceEncoding encNat := by fun_prop
    exact h.comp Source.prepare_polyTime
  have hoperands : ComputableInPolyTime (fun x : Source.Input => (Source.prepare x).2.1.1)
      Source.encoding (encList encNat) := by
    have h : ComputableInPolyTime (fun x : ProgramGeneration.Source => x.2.1.1)
        sourceEncoding (encList encNat) := by fun_prop
    exact h.comp Source.prepare_polyTime
  have hmodulus := ComputableInPolyTime.binary_pow' (.const 2) hdepth
  have hs := ComputableInPolyTime.binary_mod.comp (hseed.prod hmodulus)
  have hm : ComputableTidilyInPolyTime
      (fun q : Source.Input × ℕ => q.2 % 2 ^ (Source.prepare q.1).1.1.2)
      (encPair Source.encoding encNat) encNat :=
    ComputableInPolyTime.tidy (ComputableInPolyTime.binary_mod.comp
      ((ComputableInPolyTime.snd Source.encoding encNat).prod
        (hmodulus.comp (ComputableInPolyTime.fst Source.encoding encNat))))
  have hmap := hoperands.tidy.mapWithInput (encB := encNat)
    (f := fun x a => a % 2 ^ (Source.prepare x).1.1.2) hm
  exact ((hdepth.prod hs).prod (ComputableInPolyTime.of_tidy hmap)).of_enc_eq
    (encD := SortedQuarterMachine.encoding) (fun _ => rfl)

/-- The actual prepared quarter has the source length, including empty/residual source inputs. -/
theorem prepare_length (input : Source.Input) :
    (prepare input).2.length = input.2.tail.length / 4 := by
  have h := (Source.quarters_lengths input.2.tail).1
  simpa only [prepare, Source.prepare, List.length_map] using h

/-- Preparation is exactly the binary encoding of the actual projected words and seed. -/
theorem prepare_words (input : Source.Input) :
    let source := Source.prepare input
    let p := source.1.1.2
    prepare input = ((p, (BitVec.ofNat p source.1.2.1).toNat),
      (source.2.1.1.map (BitVec.ofNat p)).map BitVec.toNat) := by
  simp only [prepare, List.map_map, Function.comp_def, BitVec.toNat_ofNat]

/-- Original-input completeness and sound quarter witnesses, with no supplied list semantics. -/
theorem correct (input : Source.Input) :
    let source := Source.prepare input
    let p := source.1.1.2
    let as := source.2.1.1.map (BitVec.ofNat p)
    let seed := BitVec.ofNat p source.1.2.1
    (run input).Perm (SortedRecords.projectedQuarter p as seed) ∧
      (run input).Pairwise (fun a b => a.1 ≤ b.1) ∧
      ∀ r, r ∈ run input ↔ r.2 < 2 ^ as.length ∧
        r.1 = (eval ((Native.Quarter.decode as.length r.2).zip as) seed).toNat := by
  rw [run, prepare_words]
  exact SortedQuarterMachine.correct _ _

/-- From one original source input, one uniform multitape machine computes the sorted first
projected quarter in a quarter enumeration times a fixed polynomial in the original bit length.
The resource certificate charges preparation and all intermediate tapes, not just retained rows. -/
theorem run_computable :
    ∃ Q : ℕ → ℕ, Cslib.PolynomiallyBounded Q ∧ Monotone Q ∧
      ComputableInO run Source.encoding (encList RadixPartition.recordEncoding)
        (fun input => (2 ^ (input.2.tail.length / 4) + 1) *
          Q ((Source.encoding input).length + 1))
        (fun input => (2 ^ (input.2.tail.length / 4) + 1) *
          Q ((Source.encoding input).length + 1)) := by
  obtain ⟨Q, hQ, hmQ, hrun⟩ := SortedQuarterMachine.run_computable
  let prep := NativeCertificate.ofPolyTime prepare_polyTime
  obtain ⟨R, hR, hmR, hr⟩ := exists_mono_poly_cert prepare_polyTime
  obtain ⟨L, hL, hmL, hl⟩ := exists_mono_poly prepare_polyTime.polyBounded_length
  let P : ℕ → ℕ := fun B => R B + Q (L B + 1) + 1
  have hP : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have hmP : Monotone P := fun a b hab => by
    have := hmR hab
    have := hmQ (Nat.add_le_add_right (hmL hab) 1)
    dsimp only [P]
    omega
  refine ⟨P, hP, hmP, (hrun.comp prep.computes).mono_le ?_ ?_⟩
  all_goals intro input
  all_goals
    have ht := (hr input).1.trans (hmR (Nat.le_succ (Source.encoding input).length))
    have hs := (hr input).2.trans (hmR (Nat.le_succ (Source.encoding input).length))
    have hlen := (hl input).trans (hmL (Nat.le_succ (Source.encoding input).length))
    have hbudget := hmQ (Nat.add_le_add_right hlen 1)
    change Q ((SortedQuarterMachine.encoding (prepare input)).length + 1) ≤
      Q (L ((Source.encoding input).length + 1) + 1) at hbudget
    have he : 1 ≤ (2 : ℕ) ^ (input.2.tail.length / 4) + 1 := Nat.succ_pos _
    have hmul := Nat.mul_le_mul_left (2 ^ (input.2.tail.length / 4) + 1) hbudget
    change prep.time input ≤ R ((Source.encoding input).length + 1) at ht
    change prep.space input ≤ R ((Source.encoding input).length + 1) at hs
    have hRmul := Nat.mul_le_mul_right (R ((Source.encoding input).length + 1)) he
    have charge (t : ℕ) (h : t ≤ R ((Source.encoding input).length + 1)) :
        t + (2 ^ (input.2.tail.length / 4) + 1) *
          Q ((SortedQuarterMachine.encoding (prepare input)).length + 1) ≤
        (2 ^ (input.2.tail.length / 4) + 1) * P ((Source.encoding input).length + 1) := by
      dsimp only [P]
      calc
        _ ≤ R ((Source.encoding input).length + 1) +
            (2 ^ (input.2.tail.length / 4) + 1) *
              Q (L ((Source.encoding input).length + 1) + 1) := Nat.add_le_add h hmul
        _ ≤ (2 ^ (input.2.tail.length / 4) + 1) * R ((Source.encoding input).length + 1) +
            (2 ^ (input.2.tail.length / 4) + 1) *
              Q (L ((Source.encoding input).length + 1) + 1) := by
          exact Nat.add_le_add_right (by simpa only [Nat.one_mul] using hRmul) _
        _ = (2 ^ (input.2.tail.length / 4) + 1) *
            (R ((Source.encoding input).length + 1) +
              Q (L ((Source.encoding input).length + 1) + 1)) :=
          by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ _)
  · change prep.time input + _ ≤ _
    rw [prepare_length]
    exact charge _ ht
  · change prep.space input + _ ≤ _
    rw [prepare_length]
    exact charge _ hs

private theorem projectedQuarter_project {m p : ℕ} (hp : p ≤ m)
    (as : List (BitVec m)) (s : BitVec m) :
    SortedRecords.projectedQuarter p (as.map (BitVec.setWidth p)) (s.setWidth p) =
      SortedRecords.projectedQuarter p as s := by
  simp only [SortedRecords.projectedQuarter, List.length_map]
  apply List.map_congr_left
  intro u _
  have hz : (Native.Quarter.decode as.length u).zip (as.map (BitVec.setWidth p)) =
      project p ((Native.Quarter.decode as.length u).zip as) := by
    rw [List.zip_map_right]
    rfl
  have he := eval_project hp ((Native.Quarter.decode as.length u).zip as) s
  simp only [Native.Quarter.indexedState, List.length_map, hz, ← he,
    BitVec.toNat_setWidth, Nat.mod_mod]

/-- The original single-list source input produces the sorted first quarter with its original
full-width packed-witness semantics projected to the admitted depth. -/
theorem original_correct {m p : ℕ} (hm : p ≤ m) (a : BitVec m)
    (tail : List (BitVec m)) (hk : p ≤ tail.length / 4) :
    let as := (Source.quarters tail).1.1
    let sorted := run (Source.ofWords p a tail)
    sorted.Perm (SortedRecords.projectedQuarter p as a) ∧
      sorted.Pairwise (fun r s => r.1 ≤ s.1) ∧
      ∀ r, r ∈ sorted ↔ r.2 < 2 ^ as.length ∧
        r.1 = (eval ((Native.Quarter.decode as.length r.2).zip as) a).toNat % 2 ^ p := by
  have hp : prepare (Source.ofWords p a tail) =
      ((p, (a.setWidth p).toNat),
        (((Source.quarters tail).1.1).map (BitVec.setWidth p)).map BitVec.toNat) := by
    simp only [prepare, Source.prepare_ofWords_admitted hm a tail hk,
      ProgramGeneration.originalSource, BitInput.words, List.map_map,
      Function.comp_def, BitVec.toNat_setWidth]
  have generated := SortedQuarterMachine.generated_records
    (((Source.quarters tail).1.1).map (BitVec.setWidth p)) (a.setWidth p)
  simp only [List.length_map] at generated
  have hr : run (Source.ofWords p a tail) =
      RadixSort.sort (p, SortedRecords.projectedQuarter p (Source.quarters tail).1.1 a) := by
    rw [run, hp]
    simp only [SortedQuarterMachine.run, List.length_map, generated,
      projectedQuarter_project hm]
  rw [hr]
  exact SortedRecords.projectedQuarter_correct p _ _

/-- On admitted source inputs, the original wire is polynomial in operand count and physical
word width. The projection parameter does not become an uncharged extra input length. -/
theorem original_input_length {m p : ℕ} (hp : p ≤ m) (a : BitVec m)
    (tail : List (BitVec m)) :
    (Source.encoding (Source.ofWords p a tail)).length ≤
      6 * m + 3 + (tail.length + 1) * (2 * m + 1) := by
  have hlist := length_encList_le encNat ((a :: tail).map BitVec.toNat) (b := m) (by
    intro u hu
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu
    simpa only [encNat_apply, ← Nat.size_eq_bits_len] using Nat.size_le.mpr v.isLt)
  simp only [List.length_map, List.length_cons] at hlist
  simp only [Source.encoding, Source.ofWords, length_encPair, encUnary_apply,
    List.length_replicate]
  omega

end Cslib.Cryptanalysis.AddXNOR.SourceQuarter
