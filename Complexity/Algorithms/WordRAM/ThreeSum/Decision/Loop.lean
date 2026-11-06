/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Body

/-!
# Complete native catalogue traversal

The invariant records exactly the processed entries of the existing emitted-node list. Every
pointer and signed cell is read from its actual represented block; all future entries survive
because the matrix/callee workspace starts at the independently supplied live allocation frontier.
The word envelope is used only to bound values and physical width.

## Main results

* `exec_calls`: complete charged loop, exact disjunction of all emitted Convolution instances,
  and preservation of the entire preprocessing prefix.

These native catalogue composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum (Convolution)
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- Execute all actual pointers, retaining every packed input and catalogue cell. -/
theorem exec_calls {r κ n w tab U G H : ℕ} (c : Host.Callee r)
    (out : List (ℕ × Node)) (x : Data (registerCount r))
    (hw : width κ c.widthCoefficient n ≤ w)
    (hN : 4 * G < (n + 2) ^ envelopeExponent κ)
    (hH : H ≤ (n + 2) ^ envelopeExponent κ)
    (hwords : ∀ p, x.mem p < (n + 2) ^ envelopeExponent κ)
    (hstored : ChanHe.Traversal.StoredNodes U G tab out x.mem)
    (hlayout : ChanHe.Traversal.OutputLayout G tab H out)
    (hc : Controls tab out.length (4 * G) ((n + 2) ^ envelopeExponent κ) H x)
    (hk : x.regs (controllerRegisters r current) = 0)
    (hb : x.regs (controllerRegisters r answer) = 0) :
    ∃ y, ExecWithin w (calls c.code) x y
        (out.length * (Host.callerTime (4 * G)
          (c.time (Host.sideLength (4 * G)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 12) + 2) ∧
      y.regs (controllerRegisters r answer) ≤ 1 ∧
      (y.regs (controllerRegisters r answer) = 1 ↔
        ∃ i : Fin out.length, Convolution (4 * G) (out[i.val].2.oneArray U)) ∧
      ∀ p < H, y.mem p = x.mem p := by
  let V := (n + 2) ^ envelopeExponent κ
  let I (z : Data (registerCount r)) : Prop :=
    z.regs (controllerRegisters r current) ≤ out.length ∧
    Controls tab out.length (4 * G) V H z ∧ z.regs (controllerRegisters r answer) ≤ 1 ∧
    (z.regs (controllerRegisters r answer) = 1 ↔ ∃ i : Fin out.length,
      i.val < z.regs (controllerRegisters r current) ∧
        Convolution (4 * G) (out[i.val].2.oneArray U)) ∧
    ∀ p < H, z.mem p = x.mem p
  have hval (i : Fin out.length) (u : ℕ) (hu : u < 4 * G) :
      |out[i.val].2.oneArray U u| ≤ (V : ℤ) := by
    have hm := hstored.cells i ⟨u, hu⟩
    change x.mem (out[i.val].1 + u) = Signed.encode (out[i.val].2.oneArray U u) at hm
    have hv := hwords (out[i.val].1 + u)
    rw [hm] at hv
    rw [← Int.natCast_natAbs]
    have hmag : (out[i.val].2.oneArray U u).natAbs ≤ V := by
      dsimp only [Signed.encode] at hv
      omega
    exact_mod_cast hmag
  have hbody (z : Data (registerCount r)) (hz : I z)
      (hlt : (Cond.lt (controllerRegisters r current) (controllerRegisters r count)).Holds z) :
      ∃ y, ExecWithin w (body c.code) z y
          (Host.callerTime (4 * G)
            (c.time (Host.sideLength (4 * G)) (2 * V + 1)) + 10) ∧
        I y ∧ out.length - y.regs (controllerRegisters r current) <
          out.length - z.regs (controllerRegisters r current) := by
    obtain ⟨hzk, hzc, hzb, hza, hzm⟩ := hz
    have hzklt : z.regs (controllerRegisters r current) < out.length := by
      simpa only [Cond.holds_lt, hzc.count] using hlt
    let i : Fin out.length := ⟨z.regs (controllerRegisters r current), hzklt⟩
    have hzstored := hstored.frame hlayout hzm
    have hp : z.mem (tab + i.val) = out[i.val].1 := by
      simpa using hzstored.pointers.get i.val (by simpa only [List.length_map] using i.isLt)
    have hpend := hlayout.payload_end i
    have hmem (u : ℕ) (hu : u < 4 * G) :
        z.mem (z.mem (tab + i.val) + u) = Signed.encode (out[i.val].2.oneArray U u) := by
      rw [hp]
      exact hzstored.cells i ⟨u, hu⟩
    obtain ⟨y, he, hyc, hyk, hyb, hya, hym⟩ := exec_body c z (out[i.val].2.oneArray U)
      hw hN hH hlayout.table_end hzklt hzc rfl rfl hzb
      (by rw [hp]; exact hpend) (hval i) hmem
    change y.regs (controllerRegisters r current) = z.regs (controllerRegisters r current) + 1
      at hyk
    refine ⟨y, he, ⟨by omega, hyc, hyb, ?_, ?_⟩, ?_⟩
    · rw [hya]
      constructor
      · rintro (h | h)
        · obtain ⟨j, hj, hs⟩ := hza.mp h
          exact ⟨j, by omega, hs⟩
        · exact ⟨i, by change z.regs (controllerRegisters r current) < _; omega, h⟩
      · rintro ⟨j, hj, hs⟩
        by_cases hjk : j.val < z.regs (controllerRegisters r current)
        · exact Or.inl (hza.mpr ⟨j, hjk, hs⟩)
        · have hji : j = i := Fin.ext (by
            change j.val = z.regs (controllerRegisters r current)
            omega)
          subst j
          exact Or.inr hs
    · intro p hp
      exact (hym p hp).trans (hzm p hp)
    · omega
  have hx : I x := by
    refine ⟨by omega, hc, by omega, ?_, fun _ _ => rfl⟩
    rw [hb, hk]
    simp only [Nat.not_lt_zero, false_and, exists_false, reduceCtorEq]
  obtain ⟨y, he, hy, hstop⟩ := ExecWithin.loop_invariant I
    (fun z => out.length - z.regs (controllerRegisters r current)) hbody hx
  obtain ⟨hyk, hyc, hyb, hya, hym⟩ := hy
  have hlast : y.regs (controllerRegisters r current) = out.length := by
    change ¬y.regs (controllerRegisters r current) < y.regs (controllerRegisters r count) at hstop
    rw [hyc.count] at hstop
    omega
  refine ⟨y, ?_, hyb, ?_, hym⟩
  · simpa only [calls, hk, Nat.sub_zero, Nat.add_assoc, Nat.reduceAdd] using he
  · rw [hya, hlast]
    constructor
    · rintro ⟨i, _, hs⟩
      exact ⟨i, hs⟩
    · rintro ⟨i, hs⟩
      exact ⟨i, i.isLt, hs⟩

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
