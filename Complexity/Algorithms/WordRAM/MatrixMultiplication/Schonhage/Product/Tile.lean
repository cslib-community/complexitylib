/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Arguments
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Catalogue
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.SavedGroups
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Kernel
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Magnitude

/-!
# One actual tile call on produced arrays and computed routing words

## Main results

* `QueriedProduct.exec_tileStep`: load the actual span, construct the kernel ABI, execute the
  native pruned kernel and propagate its returned epoch while advancing the real tile index.

The proof decodes typed queries from actual saved words; they are not program input.
The finite request set, encoding arrays, frames, arithmetic
fits and call charge are obtained from the actual producer contracts.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- One charged native tile, with the actual query set and a reusable timestamp directory.
The final memory witness contains every reported pruned value and is the same state whose
epoch is passed to the next tile. Its answers are the original signed matrix product. -/
public theorem exec_tileStep {w L m N A t E : ℕ} (hw : 0 < w) (hm : m ≤ L)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (old : ℕ → ℕ) (x : Data 160)
    (hp : Parameters L m N qs.length x) (hx : x.regs index = t)
    (ht : t < numBands L m N ^ 2) (hE : x.regs epoch = E) (hEbound : E ≤ epochBound L m N)
    (hg : SavedGroups L m N qs.length old x.mem) (he : EncodedBands hm X Y x.mem)
    (hvalues : ∀ i : Fin qs.length,
      old (Wanted.codeAddress L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
        (PrunedQuery.queryIndex
          (outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2)).val)
    (hoffsets : ∀ t ≤ numBands L m N ^ 2,
      old (Wanted.offsetAddress L m N qs.length + t) =
        Nat.count (fun k => (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) k < t) qs.length)
    (hmarks : ∀ j < 10 ^ L, x.mem (stampBase L m N qs.length + j) ≤ E)
    (hX : ∀ i k, |X i k| ≤ (A : ℤ)) (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m N qs.length)) :
    let a := x.mem (offsetBase L m N qs.length + t)
    let b := x.mem (offsetBase L m N qs.length + t + 1)
    let β := t / numBands L m N
    let γ := t % numBands L m N
    ∃ y,
      ExecWithin (w + 2) tileStep x y
        (4 * L + 29 * (b - a) +
          PrunedQuery.traceWeight (wantedStrings (MaskTable.layout hm) qs.toFinset β γ) + 64) ∧
      Parameters L m N qs.length y ∧ y.regs index = t + 1 ∧
      E + 1 ≤ y.regs epoch ∧ y.regs epoch ≤ E + 1 + PrunedQuery.epochAllowance L ∧
      SavedGroups L m N qs.length old y.mem ∧ EncodedBands hm X Y y.mem ∧
      (∀ j < 10 ^ L, y.mem (stampBase L m N qs.length + j) ≤ y.regs epoch) ∧
      (∀ i : Fin qs.length,
        (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) i.val = t →
          y.mem (groupedBase L m N qs.length +
              CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
            Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ p, ¬(groupedBase L m N qs.length + a ≤ p ∧
          p < groupedBase L m N qs.length + b) →
        ¬(scratchBase L m N qs.length ≤ p ∧ p < memoryEnd L m N qs.length) →
          y.mem p = x.mem p) := by
  dsimp only
  let B := numBands L m N
  let a := x.mem (offsetBase L m N qs.length + t)
  let b := x.mem (offsetBase L m N qs.length + t + 1)
  let β := t / B
  let γ := t % B
  let pa := BandPreparation.catalogueBase L m N + β * 10 ^ L
  let pb := BandPreparation.catalogueBase L m N + (B + γ) * 10 ^ L
  have habQ : a ≤ b ∧ b ≤ qs.length :=
    hg.span_bounds (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) hoffsets ht
  have hB : 0 < B := by dsimp only [B] at *; nlinarith only [ht, Nat.zero_le t]
  have hβ : β < B := (Nat.div_lt_iff_lt_mul hB).mpr (by simpa [B, pow_two] using ht)
  have hγ : γ < B := Nat.mod_lt t hB
  have hT : (β, γ) ∈ Cslib.Algorithms.MatrixMultiplication.Schonhage.tiles L m N :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr hβ, Finset.mem_range.mpr hγ⟩
  have htnum : β * numBands L m N + γ = t := by
    simpa only [β, γ, B, Nat.mul_comm] using Nat.div_add_mod t B
  have hcode (j : ℕ) (hj : j < qs.length) :
      x.mem (codeBase L m N qs.length + j) < 10 ^ L := by
    rw [hg.codes j hj]
    exact router_code_lt hm qs old hvalues j hj
  let queries : Fin (b - a) → OutStr L := fun i => PrunedQuery.queryAt
    ⟨x.mem (codeBase L m N qs.length + (a + i.val)), hcode _ (by have hi := i.isLt; omega)⟩
  have hinput (i : Fin (b - a)) : x.mem (codeBase L m N qs.length + (a + i.val)) =
      (PrunedQuery.queryIndex (queries i)).val := by
    simp only [queries, PrunedQuery.queryIndex_queryAt]
  have hset : Finset.univ.image queries =
      wantedStrings (MaskTable.layout hm) qs.toFinset β γ :=
    hg.span_queries hm qs hvalues hoffsets (β, γ) hT a b
      (by rw [htnum])
      (by rw [htnum]; rfl) queries hinput
  obtain ⟨arg, har, arp, arm, ari, _, arL, arA, arB, arq, arQ, aro, arf, arE⟩ :=
    exec_tileArguments x hp hx ht (rfl : x.mem (offsetBase L m N qs.length + t) = a)
      (rfl : x.mem (offsetBase L m N qs.length + t + 1) = b) habQ.1 habQ.2 hfit
  change (arg.comap bank).regs PrunedQuery.arrayA = pa at arA
  change (arg.comap bank).regs PrunedQuery.arrayB = pb at arB
  change (arg.comap bank).regs PrunedQuery.queries = codeBase L m N qs.length + a at arq
  change (arg.comap bank).regs PrunedQuery.queryCount = b - a at arQ
  change (arg.comap bank).regs PrunedQuery.output = groupedBase L m N qs.length + a at aro
  have hpab : pa + 10 ^ L ≤ BandPreparation.memoryEnd L m N ∧
      pb + 10 ^ L ≤ BandPreparation.memoryEnd L m N := by
    have hl := BandPreparation.catalogue_block_le false hβ
    have hr := BandPreparation.catalogue_block_le true hγ
    simpa only [BandPreparation.catalogueAddress, Bool.false_eq_true, ↓reduceIte,
      Nat.zero_add, Nat.add_zero, pa, pb, B] using And.intro hl hr
  have hlow : BandPreparation.memoryEnd L m N ≤ snapshotBase L m N qs.length ∧
      snapshotBase L m N qs.length ≤ offsetBase L m N qs.length ∧
      offsetBase L m N qs.length ≤ groupedBase L m N qs.length := by
    refine ⟨(producers_le_snapshot L m N qs.length).1, ?_, ?_⟩
    · unfold offsetBase
      omega
    · unfold groupedBase originalBase codeBase
      omega
  have hout : groupedBase L m N qs.length + qs.length = outputBase L m N qs.length := rfl
  have hqueries : codeBase L m N qs.length + qs.length ≤ groupedBase L m N qs.length := by
    unfold groupedBase originalBase
    omega
  have hfree : outputBase L m N qs.length ≤ scratchBase L m N qs.length := by
    unfold scratchBase
    omega
  have hbefore : BandPreparation.memoryEnd L m N ≤ scratchBase L m N qs.length := by omega
  have hleft (τ : Leaf L) : arg.mem (pa + (Encoding.leafIndex τ).val) =
      Signed.encode (encodingL (bandArrayL (MaskTable.layout hm) X β) τ) := by
    rw [arm]
    simpa only [pa, BandPreparation.catalogueAddress, Bool.false_eq_true, ↓reduceIte,
      Nat.zero_add, Nat.add_assoc] using he.left β hβ τ
  have hright (τ : Leaf L) : arg.mem (pb + (Encoding.leafIndex τ).val) =
      Signed.encode (encodingR (bandArrayR (MaskTable.layout hm) Y γ) τ) := by
    rw [arm]
    simpa only [pb, B, BandPreparation.catalogueAddress, ↓reduceIte, Nat.add_assoc] using
      he.right γ hγ τ
  have habsL (τ : Leaf L) : |encodingL (bandArrayL (MaskTable.layout hm) X β) τ| ≤
      ((7 ^ L * A : ℕ) : ℤ) := by
    exact_mod_cast abs_encodingL_le
      (abs_bandArrayL_le (MaskTable.layout hm) (by positivity) hX β) τ
  have habsR (τ : Leaf L) : |encodingR (bandArrayR (MaskTable.layout hm) Y γ) τ| ≤
      ((7 ^ L * A : ℕ) : ℤ) := by
    exact_mod_cast abs_encodingR_le
      (abs_bandArrayR_le (MaskTable.layout hm) (by positivity) hY γ) τ
  have hpa := (Nat.le_add_right pa (10 ^ L)).trans hpab.1
  have hpb := (Nat.le_add_right pb (10 ^ L)).trans hpab.2
  have hkernel := kernel_fits hfit hpa hpb
    (show codeBase L m N qs.length + a ≤ codeBase L m N qs.length + qs.length by omega)
    (show groupedBase L m N qs.length + a ≤ outputBase L m N qs.length by omega)
    (show b - a ≤ qs.length by omega) hEbound
  obtain ⟨k, hk, kv, kf, _, kel, keu, km⟩ := PrunedQuery.exec_kernel
    (L := L) (f := scratchBase L m N qs.length) (a0 := pa) (b0 := pb)
    (q0 := codeBase L m N qs.length + a) (o0 := groupedBase L m N qs.length + a)
    (Q := b - a) (E := E)
    (encodingL (bandArrayL (MaskTable.layout hm) X β))
    (encodingR (bandArrayR (MaskTable.layout hm) Y γ)) queries (arg.comap bank)
    arL arA arB arQ arq aro arf (arE.trans hE)
    (by intro i; simpa only [Data.comap_mem, arm, Nat.add_assoc] using hinput i)
    hleft hright (by omega) (by omega) (by omega) (by omega)
    (by simpa only [Data.comap_mem, arm, stampBase] using hmarks)
    habsL habsR hw (magnitude_admissions hw hmag).2.1 hkernel
  rw [hset] at hk kv
  let u := k.extend bank arg
  have hhigh (i : Fin 160) (hi : 96 ≤ i.val) : u.regs i = arg.regs i := by
    have hnot : ¬∃ j, bank j = i := by
      rintro ⟨j, hj⟩
      have hv := congrArg (fun r : Fin 160 => r.val) hj
      change j.val = i.val at hv
      omega
    exact Function.extend_apply' _ _ _ hnot
  have up : Parameters L m N qs.length u := arp.reframe hhigh
  have ui : u.regs index = t := (hhigh _ (by decide)).trans ari
  have ue : u.regs (bank PrunedQuery.epoch) = k.regs PrunedQuery.epoch :=
    bank_injective.extend_apply _ _ _
  have hnext : Fits (w + 2) (t + 1) := allocated_fits hfit (by
    unfold memoryEnd stampBase scratchBase outputBase groupedBase originalBase codeBase offsetBase
    have h10 := Nat.zero_le (10 ^ L)
    omega)
  let y := (u.set epoch (k.regs PrunedQuery.epoch)).set index (t + 1)
  have hpost : ExecWithin (B := .standard) (w + 2)
      (.seq (.op (.copy epoch (bank PrunedQuery.epoch))) (ram[index ← index + one])) u y 2 := by
    ram_eval [y, ue, ui, up.one, hnext, epoch, index, one]
  have yp : Parameters L m N qs.length y :=
    (up.set_work epoch (by decide) _).set_work index (by decide) _
  have yepoch : y.regs epoch = k.regs PrunedQuery.epoch := by simp [y, epoch, index]
  have yframe (p : ℕ)
      (ho : ¬(groupedBase L m N qs.length + a ≤ p ∧
        p < groupedBase L m N qs.length + b))
      (hf : ¬(scratchBase L m N qs.length ≤ p ∧ p < memoryEnd L m N qs.length)) :
      y.mem p = x.mem p := by
    change k.mem p = x.mem p
    rw [kf p (by omega) (by simpa only [memoryEnd, stampBase] using hf),
      Data.comap_mem, arm]
  refine ⟨y, ?_, yp, by simp [y], by simpa only [yepoch] using kel,
    by simpa only [yepoch] using keu, ?_, ?_, ?_, ?_, yframe⟩
  · apply (har.seq ((hk.rename bank_injective).seq hpost)).mono
    dsimp only [β, γ, B, a, b]
    omega
  · exact hg.reframe (fun p hp hbefore => yframe p (by omega) (by omega))
  · exact he.reframe (fun p hp => yframe p (by omega) (by omega))
  · intro j hj
    change k.mem (stampBase L m N qs.length + j) ≤ y.regs epoch
    simpa only [stampBase, yepoch] using km j hj
  · intro i hkey
    let p := CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i
    have hp : p < qs.length := CountingSort.position_lt _ i.isLt
    have hspan : a ≤ p ∧ p < b := by
      have hs := (CountingSort.position_mem_iff
        (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) i.isLt t).mpr hkey
      have ha := (hg.offsets t ht.le).trans (hoffsets t ht.le)
      have hb := (hg.offsets (t + 1) (by omega)).trans (hoffsets (t + 1) (by omega))
      change a = _ at ha
      change b = _ at hb
      simpa only [← ha, ← hb] using hs
    let j : Fin (b - a) := ⟨p - a, by omega⟩
    have hap : a + j.val = p := by dsimp only [j]; omega
    have hquery : queries j = outStrOfPos (MaskTable.layout hm) (qs.get i).1 (qs.get i).2 := by
      have hr := hinput j
      rw [hap, hg.codes p hp, hvalues i] at hr
      simpa only [PrunedQuery.queryAt_queryIndex] using
        congrArg PrunedQuery.queryAt (Fin.ext hr.symm)
    have htile : Wanted.tileKey L m N ((qs.get i).1.val, (qs.get i).2.val) =
        β * numBands L m N + γ := by
      simpa only [Function.comp_apply, Wanted.inputPairs_get, htnum] using hkey
    have hbands := (Wanted.tileKey_eq_iff hm (qs.get i).1 (qs.get i).2 (β, γ) hT).mp htile
    change bandOf L m (qs.get i).1.val = β ∧ bandOf L m (qs.get i).2.val = γ at hbands
    have hr := kv j
    rw [Nat.add_assoc, hap, hquery, ← hbands.1, ← hbands.2,
      thin_product_spec (MaskTable.layout hm) X Y qs.toFinset (qs.get i).1 (qs.get i).2
        (List.mem_toFinset.mpr (List.get_mem _ _))] at hr
    exact hr

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
