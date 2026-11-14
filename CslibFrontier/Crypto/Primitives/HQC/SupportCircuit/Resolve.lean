/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Scan
public import CslibFrontier.Crypto.Primitives.HQC.SupportSampling
public import CslibFrontier.Computability.Circuit.Parallel
import CslibFrontier.Foundations.Data.BitString.Block.Cons
import CslibFrontier.Foundations.Data.BitString.Binary

/-!
# Descending support correction circuit

The tail is corrected first and retained while the current candidate scans it. This follows
`scanSupport` exactly, including the order of the nested loops and reuse of corrected entries.

## Main definitions

* `Cslib.Crypto.HQC.supportScanCircuit`: the complete descending collision pass.

## Main results

* `Cslib.Crypto.HQC.val_eval_supportScanCircuit`: agreement with the existing array semantics.
* `Cslib.Crypto.HQC.size_supportScanCircuit`: exact cost for all pairs of positions.

## References

[HQC version 5.1][HQC2026], `SampleSupport2`, p. 19, lines 7–13. Circuit construction and resource
accounting are original bridges to the existing Boolean compiler.
-/

public section

namespace Cslib.Crypto.HQC

open Circuits Circuits.Boolean BitString

/-- Correct the tail before comparing the head against its corrected entries. Dimension casts
are ordinary wiring and carry no Boolean gates. -/
@[expose] def supportScanCircuit (bits : ℕ) : (offset count : ℕ) →
    Circuit signature (count * bits) (count * bits)
  | _, 0 => Circuit.id signature _
  | offset, count + 1 =>
    (Circuit.wiring signature (Fin.cast (by rw [Nat.succ_mul, Nat.add_comm] :
      (count + 1) * bits = bits + count * bits))).comp
      ((collisionScanCircuit bits offset count (List.finRange count)).comp
        (((Circuit.id signature bits).parallel (supportScanCircuit bits (offset + 1) count)).comp
          (Circuit.wiring signature (Fin.cast (by rw [Nat.succ_mul, Nat.add_comm] :
            bits + count * bits = (count + 1) * bits)))))

private theorem val_foldl_collision {bits offset count : ℕ} (hoff : offset < 2 ^ bits)
    (js : List (Fin count)) (a : BitString bits) (later : Fin count → BitString bits) :
    (equivFin bits (js.foldl (fun current j =>
      if current = later j then (fun i => offset.testBit i.val) else current) a) : ℕ) =
      js.foldl (fun current j =>
        if current = (equivFin bits (later j) : ℕ) then offset else current)
        (equivFin bits a : ℕ) := by
  have hc : (equivFin bits (fun i : Fin bits => offset.testBit i.val) : ℕ) = offset := by
    rw [show (fun i : Fin bits => offset.testBit i.val) =
      (equivFin bits).symm ⟨offset, hoff⟩ from
        funext fun i => (equivFin_symm_apply ⟨offset, hoff⟩ i).symm,
      Equiv.apply_symm_apply]
  have hinj : Function.Injective (fun x : BitString bits => (equivFin bits x : ℕ)) :=
    Fin.val_injective.comp (equivFin bits).injective
  symm
  apply List.foldl_hom (fun x : BitString bits => (equivFin bits x : ℕ))
  intro current j
  by_cases hcurrent : current = later j <;> simp [hinj.eq_iff, hcurrent, hc]

/-- Every corrected output word has exactly the value of the source array pass. Only the
replacement offsets must fit; the input words can be arbitrary. -/
theorem val_eval_supportScanCircuit {bits offset count : ℕ}
    (h : offset + count ≤ 2 ^ bits) (words : Fin count → BitString bits) :
    (fun j => (equivFin bits (block
      ((supportScanCircuit bits offset count).eval interpretation (blocksEquiv.symm words)) j) :
        ℕ)) = scanSupport offset (fun j => (equivFin bits (words j) : ℕ)) := by
  induction count generalizing offset with
  | zero => funext j; exact j.elim0
  | succ count ih =>
    let later := block ((supportScanCircuit bits (offset + 1) count).eval interpretation
      (blocksEquiv.symm (Fin.tail words)))
    have hi := ih (offset := offset + 1) (by omega) (Fin.tail words)
    have hp : blocksEquiv.symm words ∘
        Fin.cast (by rw [Nat.succ_mul, Nat.add_comm] :
          bits + count * bits = (count + 1) * bits) =
        Fin.append (words 0) (blocksEquiv.symm (Fin.tail words)) := by
      simpa only [Fin.cons_self_tail] using blocksEquiv_symm_cons (words 0) (Fin.tail words)
    have he : (supportScanCircuit bits offset (count + 1)).eval interpretation
        (blocksEquiv.symm words) = blocksEquiv.symm
          (Fin.cons ((List.finRange count).foldl (fun current j =>
            if current = later j then (fun i => offset.testBit i.val) else current) (words 0))
            later) := by
      simp only [supportScanCircuit, Circuit.eval_comp, Circuit.eval_wiring, hp,
        Circuit.eval_parallel, Fin.append_comp_castAdd, Fin.append_comp_natAdd,
        Circuit.id, Function.comp_id]
      rw [← blocksEquiv_symm_block
        ((supportScanCircuit bits (offset + 1) count).eval interpretation
          (blocksEquiv.symm (Fin.tail words)))]
      rw [eval_collisionScanCircuit]
      rw [← blocksEquiv_symm_cons]
      funext i
      simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
      rfl
    rw [he, block_blocksEquiv_symm]
    funext j
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero, scanSupport]
      rw [val_foldl_collision (by omega)]
      rw [← List.foldl_map (f := fun j => (equivFin bits (later j) : ℕ))
        (g := fun current x => if current = x then offset else current)]
      have hl : (List.finRange count).map (fun j => (equivFin bits (later j) : ℕ)) =
          List.ofFn (scanSupport (offset + 1)
            (Fin.tail (fun j => (equivFin bits (words j) : ℕ)))) := by
        rw [List.finRange, List.map_ofFn]
        change List.ofFn (fun j => (equivFin bits (later j) : ℕ)) = _
        exact congrArg List.ofFn hi
      rw [hl]
    | succ j =>
      simp only [Fin.cons_succ, scanSupport]
      exact congrFun hi j

/-- There is one comparison for each pair of positions, with no omitted correction gates. -/
theorem size_supportScanCircuit (bits offset count : ℕ) :
    (supportScanCircuit bits offset count).size = count.choose 2 * (13 * bits + 6) := by
  induction count generalizing offset with
  | zero => simp [supportScanCircuit, Circuit.id]
  | succ count ih =>
    simp only [supportScanCircuit, Circuit.size_comp, Circuit.size_wiring,
      Circuit.size_parallel, Circuit.id, size_collisionScanCircuit, List.length_finRange,
      Nat.zero_add, Nat.add_zero, ih, Nat.choose_succ_succ, Nat.choose_one_right]
    ring

end Cslib.Crypto.HQC
