/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Bounds

/-!
# Exact native frontend from initialized signed input

The header is the unsigned length; payload cell one starts the canonical signed encoding.
The parameter program computes the magnitude and explicit radix bit count. The radix program
preserves full multiplicities; the complete descriptor program enumerates the existing inputs.

## Main results

* `exec_input`: complete initialized-input execution, exact descriptors and full multiplicities.
* `construct_preserves_parameters`: computed parameters remain available to the traversal caller.

Execution uses a positive logarithmic physical width and fixed code per exponent.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend

open Cslib.WordRAM

theorem parameterRegisters_injective : Function.Injective parameterRegisters := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp only [parameterRegisters] at this
  omega

theorem radixRegisters_injective : Function.Injective radixRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin 128 => z.val) h)

theorem arrayRegisters_injective : Function.Injective arrayRegisters := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp only [arrayRegisters] at this
  omega

/-- Parameter outputs remain available to the parent traversal without recomputation. -/
theorem construct_preserves_parameters (i : Fin 24) :
    construct.Preserves (parameterRegisters i) := by
  fin_cases i <;> decide

private theorem cost_sum_bound (p r A n k : ℕ) (hk : k ≤ n) :
    p + (4 + (r + (9 + (A * (43 * k + 32) + 21 + 3)))) ≤
      p + r + A * (43 * n + 32) + 38 - 1 := by
  have := Nat.mul_le_mul_left A (show 43 * k + 32 ≤ 43 * n + 32 by omega)
  omega

/-- Complete initialized-input native construction, with no supplied algorithm or fit advice. -/
theorem exec_input {κ w : ℕ} (input : List ℤ) (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    ∃ (y : Data 128) (rs : List (ℕ × ℕ)),
      ExecWithin w (program κ) (Data.init (input.map Signed.encode)) y (cost κ input.length - 1) ∧
      Output (layout κ input.length) ((input.length + 2) ^ κ) rs y.mem ∧
      y.regs descriptorBase = (layout κ input.length).descriptors ∧
      y.regs descriptorCount = (layout κ input.length).count ∧
      y.regs heapEnd = (layout κ input.length).endpoint ∧
      (rs.map Prod.fst).Nodup ∧ (rs.map Prod.fst).Pairwise (· < ·) ∧
      (∀ k, k ∈ rs.map Prod.fst ↔ k ∈ input.map Signed.encode) ∧
      (∀ p ∈ rs, 0 < p.2 ∧ (input.map Signed.encode).count p.1 = p.2) ∧
      Block.HoldsList (1 + 2 * input.length) (rs.map Prod.fst) y.mem ∧
      Block.HoldsList (1 + 3 * input.length) (rs.map Prod.snd) y.mem ∧
      ChanHe.Parameters.Output input.length ((input.length + 2) ^ κ)
        (y.comap parameterRegisters) ∧
      Modifies (Block.mk 1 ((layout κ input.length).endpoint - 1)).footprint
        (Data.init (input.map Signed.encode) : Data 128).mem y.mem := by
  let n := input.length
  let U := (n + 2) ^ κ
  let l := layout κ n
  let x : Data 128 := Data.init (input.map Signed.encode)
  have hparam : ChanHe.Parameters.width κ n ≤ w := by
    change ChanHe.Parameters.width κ input.length ≤ w
    dsimp only [width] at hw
    omega
  have hp := ChanHe.Parameters.budget_fits hparam
  have hfront := array_budget_fits hw
  have hN : Fits w (1 + 4 * n) := hp.of_le (by
    dsimp only [ChanHe.Parameters.Math.budget]; omega)
  have h1 : Fits w 1 := hN.of_le (by omega)
  have h2 : Fits w 2 := hp.of_le (by dsimp only [ChanHe.Parameters.Math.budget]; omega)
  have hB : Fits w l.digits := hp.of_le (by
    have hl := Nat.log_le_self 2 (4 * U)
    change Cslib.Algorithms.ThreeSum.labelBits (2 * U) ≤ ChanHe.Parameters.Math.budget n U
    dsimp only [Cslib.Algorithms.ThreeSum.labelBits, ChanHe.Parameters.Math.budget]
    rw [show 2 * (2 * U) = 4 * U by omega]
    omega)
  have hU : 1 ≤ U := Nat.one_le_pow _ _ (by omega)
  obtain ⟨p, hep, hop, hmp⟩ := ChanHe.Parameters.exec κ (x.comap parameterRegisters)
    (by simpa only [Data.comap_mem, x, Data.init_mem_zero, List.length_map] using hp)
  simp only [Data.comap_mem, x, Data.init_mem_zero, List.length_map] at hep hop
  let a := p.extend parameterRegisters x
  have ha := hep.rename parameterRegisters_injective
  have hpr (i : Fin 24) : a.regs (parameterRegisters i) = p.regs i := by
    exact congrArg (fun z : Data 24 => z.regs i)
      (Data.comap_extend parameterRegisters_injective p x)
  have han : a.regs (parameterRegisters ChanHe.Parameters.len) = n :=
    (hpr _).trans hop.len
  have haU : a.regs (parameterRegisters ChanHe.Parameters.magnitude) = U :=
    (hpr _).trans hop.magnitude
  have haB : a.regs (parameterRegisters ChanHe.Parameters.digits) = l.digits :=
    (hpr _).trans hop.digits
  have ham : a.mem = x.mem := hmp
  let b := (((a.set (radixRegisters RadixSort.len) n).set (radixRegisters RadixSort.src) 1).set
    (radixRegisters RadixSort.dst) (n + 1)).set (radixRegisters RadixSort.bits) l.digits
  have hb : ExecWithin w radixSetup a b 4 := by
    have hn1 := hN.of_le (show n + 1 ≤ 1 + 4 * n by omega)
    ram_eval [radixSetup, b, han, haB, h1, hB, hn1]
  have hmem : Block.HoldsList 1 (input.map Signed.encode) (b.comap radixRegisters).mem := by
    intro i
    change a.mem (1 + i.val) = (input.map Signed.encode)[i.val]
    rw [ham]
    dsimp only [x]
    rw [Nat.add_comm, Data.init_mem_succ]
    simp only [List.getD, List.getElem?_eq_getElem i.isLt, Option.getD_some]
  obtain ⟨q, rs, heq, hqout, hqkeys, hqcounts, hnodup, horder, hset, hcounts, hframe⟩ :=
    RadixSort.deduplicate_exec (input.map Signed.encode) (b.comap radixRegisters)
      (by simp +decide [b, Data.comap_regs, radixRegisters, n])
      (by simp +decide [b, Data.comap_regs, radixRegisters])
      (by simp +decide [b, Data.comap_regs, radixRegisters, n]; omega)
      (by simp +decide [b, Data.comap_regs, radixRegisters]) hmem
      (by
        intro u hu
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
        exact key_lt_two_pow hU (hvalues z hz))
      (input_fits input hw hvalues).2 (by simpa only [List.length_map] using hN) hB h2
  have hrlen : rs.length ≤ n := by
    have ht := hnodup.length_le_of_subset (fun k hk => (hset k).mp hk)
    simpa only [List.length_map] using ht
  let c := q.extend radixRegisters b
  have hradix := heq.rename radixRegisters_injective
  have hcout : c.regs (radixRegisters Deduplicate.out) = rs.length := by
    have he := congrArg (fun z : Data 16 => z.regs Deduplicate.out)
      (Data.comap_extend radixRegisters_injective q b)
    exact he.trans hqout
  have hhigh (i : Fin 24) : c.regs (parameterRegisters i) = a.regs (parameterRegisters i) := by
    have hnot : ¬∃ j, radixRegisters j = parameterRegisters i := by
      rintro ⟨j, he⟩
      have := congrArg Fin.val he
      dsimp only [radixRegisters, parameterRegisters] at this
      omega
    simp only [c, Data.extend, Function.extend_apply' _ _ _ hnot]
    have hne (j : Fin 16) : parameterRegisters i ≠ radixRegisters j := by
      intro he; exact hnot ⟨j, he.symm⟩
    simp only [b, Data.set_regs, Function.update_of_ne (hne _)]
  have hcn := (hhigh _).trans han
  have hcU := (hhigh _).trans haU
  have hcB := (hhigh _).trans haB
  let d := ((((((((c.set (arrayRegisters Scan.len) rs.length).set
    (arrayRegisters Select.magnitude) U).set (arrayRegisters Arrays.inputLen) n).set
    (arrayRegisters Arrays.digits) l.digits).set (arrayRegisters Select.one) 1).set
    (arrayRegisters Scan.keys) (n + n)).set (arrayRegisters Scan.keys) (n + n + 1)).set
    (arrayRegisters Scan.counts) (n + n + 1 + n)).set
    (arrayRegisters Arrays.descriptors) (n + n + 1 + n + n)
  have hd : ExecWithin w arraySetup c d 9 := by
    have f0 := hN.of_le (show n + n ≤ 1 + 4 * n by omega)
    have f1 := hN.of_le (show n + n + 1 ≤ 1 + 4 * n by omega)
    have f2 := hN.of_le (show n + n + 1 + n ≤ 1 + 4 * n by omega)
    have f3 := hN.of_le (show n + n + 1 + n + n ≤ 1 + 4 * n by omega)
    ram_eval [arraySetup, d, hcn, hcU, hcB, hcout, h1, f0, f1, f2, f3]
  have hrawkeys : ∀ v ∈ rs, v.1 ≤ 2 * U + 1 ∧ v.1 / 2 ≤ U := by
    intro v hv
    obtain ⟨z, hz, he⟩ := List.mem_map.mp ((hset v.1).mp (List.mem_map.mpr ⟨v, hv, rfl⟩))
    rw [← he]
    exact ⟨(Math.key_bounds (hvalues z hz)).1,
      by
        have hz' := hvalues z hz
        rw [Signed.encode_div_two]
        exact_mod_cast (show (z.natAbs : ℤ) ≤ (U : ℤ) by
          simpa only [Int.natCast_natAbs] using hz')⟩
  obtain ⟨r, her, hor, hregs, hrheap, hrkeys, hrcounts, hrframe⟩ := Arrays.exec l rs
    (d.comap arrayRegisters)
    (by simp +decide [d, Data.comap_regs, arrayRegisters])
    (by simp +decide [d, Data.comap_regs, arrayRegisters, l, layout])
    (by simp +decide [d, Data.comap_regs, arrayRegisters])
    (by simp +decide [d, Data.comap_regs, arrayRegisters, l, layout]; omega)
    (by simp +decide [d, Data.comap_regs, arrayRegisters, l, layout]; omega)
    (by simp +decide [d, Data.comap_regs, arrayRegisters])
    (by simp +decide [d, Data.comap_regs, arrayRegisters, Layout.descriptors, l, layout]; omega)
    hrlen (by simpa only [Data.comap_mem, d, c, Data.set_mem, Data.extend, List.length_map, l,
      layout] using hqkeys)
    (by simpa only [Data.comap_mem, d, c, Data.set_mem, Data.extend, List.length_map, l,
      layout] using hqcounts) hrawkeys hfront
  let e := r.extend arrayRegisters d
  have harray := her.rename arrayRegisters_injective
  have herg (i : Fin 48) : e.regs (arrayRegisters i) = r.regs i :=
    congrArg (fun z : Data 48 => z.regs i) (Data.comap_extend arrayRegisters_injective r d)
  let y := ((e.set descriptorBase l.descriptors).set descriptorCount l.count).set heapEnd l.endpoint
  have hy : ExecWithin w finish e y 3 := by
    ram_eval [finish, y, herg Arrays.descriptors, herg Arrays.triples, herg Arrays.heapEnd,
      hregs.descriptors, hregs.triples, hregs.heapEnd]
  have hall := ha.seq (hb.seq (hradix.seq (hd.seq (harray.seq hy))))
  refine ⟨y, rs, ?_, hor, ?_, ?_, ?_, hnodup, horder, hset, hcounts, hrkeys, hrcounts, ?_, ?_⟩
  · apply hall.mono
    simpa only [cost, List.length_map, n, U, l, layout] using cost_sum_bound
      (ChanHe.Parameters.time κ n U) (RadixSort.deduplicateTime n l.digits)
      l.arrays n rs.length hrlen
  · rfl
  · rfl
  · rfl
  · have hconstruct := hb.seq (hradix.seq (hd.seq (harray.seq hy)))
    have hprf (i : Fin 24) : y.regs (parameterRegisters i) = p.regs i :=
      (hconstruct.regs_eq (construct_preserves_parameters i)).trans (hpr i)
    -- Only register equalities are needed: the parameter output does not constrain memory.
    exact ⟨(hprf _).trans hop.len, (hprf _).trans hop.magnitude,
      (hprf _).trans hop.digits, (hprf _).trans hop.height, (hprf _).trans hop.fuel,
      (hprf _).trans hop.want, (hprf _).trans hop.primeBound,
      (hprf _).trans hop.packedLen, (hprf _).trans hop.padding⟩
  · intro baddr hbaddr
    have hbfront : baddr ∉ (Block.mk l.descriptors (l.endpoint - l.descriptors)).footprint := by
      intro hba
      apply hbaddr
      change baddr ∈ (Block.mk 1 (l.endpoint - 1)).footprint
      rw [Block.mem_footprint] at hba ⊢
      dsimp only [Block.Owns] at hba ⊢
      have hdesc : 1 ≤ l.descriptors := by dsimp [Layout.descriptors]; omega
      omega
    have hbradix : baddr ∉ (Block.mk 1 (4 * n)).footprint := by
      intro hba
      apply hbaddr
      change baddr ∈ (Block.mk 1 (l.endpoint - 1)).footprint
      rw [Block.mem_footprint] at hba ⊢
      dsimp only [Block.Owns] at hba ⊢
      have hbe : 1 + 4 * n ≤ l.endpoint := by
        dsimp only [Layout.endpoint, Layout.pointer, Layout.payloads, Layout.descriptors, l, layout]
        omega
      omega
    exact (hrframe baddr hbfront).trans ((hframe baddr
      (by simpa only [List.length_map, n] using hbradix)).trans (congrFun ham baddr))

end Cslib.Algorithms.WordRAM.ThreeSum.Frontend
