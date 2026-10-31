/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Program
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Exec

/-!
# Actual low-bank CountPrime multiplication call

The counter copies six real arguments and invokes the complete native 64-register Strassen
program in its low bank. Its 64-and-above metadata survives the existing native register
renaming semantics. Monomial inputs have coefficient magnitude at most one; all recursive
signed fits therefore follow from the explicit original cyclic-length/depth envelope.

This is an internal stage contract. The complete counter derives its monomial readback and
pointer separation from preceding native setup and matrix construction, rather than taking
a layout or multiplication certificate as an algorithm input.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Invoke the actual complete native Strassen program, charging argument copies, all
coefficient arithmetic/recursion and loop exit. No multiplication/run/time contract is assumed. -/
theorem exec_product {w p k : ℕ} (x : Data 128) (u v : ℕ → ℤ)
    (hp : 0 < p) (hpr : x.regs Reg.modulus = p) (hkr : x.regs Reg.depth = k)
    (hPQ : x.regs Reg.matrixP + 4 ^ k * p ≤ x.regs Reg.matrixQ)
    (hQR : x.regs Reg.matrixQ + 4 ^ k * p ≤ x.regs Reg.matrixR)
    (hRS : x.regs Reg.matrixR + 4 ^ k * p ≤ x.regs Reg.productScratch)
    (hu : ∀ i < 4 ^ k * p, (u i).natAbs ≤ 1)
    (hv : ∀ i < 4 ^ k * p, (v i).natAbs ≤ 1)
    (hleft : ∀ i < 4 ^ k * p, x.mem (x.regs Reg.matrixP + i) = encode (u i))
    (hright : ∀ i < 4 ^ k * p, x.mem (x.regs Reg.matrixQ + i) = encode (v i))
    (hmag : GenericRAM.Signed.Fits w ((2 * (p + 4) * 16 ^ k : ℕ) : ℤ))
    (haddr : Fits (w + 2) (Strassen.addressBound (x.regs Reg.productScratch + 4 ^ k * p)
      (x.regs Reg.productScratch + 4 ^ k * p) k)) :
    ∃ y, ExecWithin (w + 2) product x y (Strassen.traceBudget p k + 4 * k + 38) ∧
      (∀ i < 4 ^ k * p, y.mem (x.regs Reg.matrixR + i) = encode
        (Cslib.Algorithms.MatrixMultiplication.Strassen.multiply p k u v i)) ∧
      (∀ d, ¬Strassen.NodeWrites p k (x.regs Reg.matrixR) (x.regs Reg.productScratch)
        (x.regs Reg.productScratch + 4 ^ k * p) (x.regs Reg.productScratch + 4 ^ k * p) d →
        y.mem d = x.mem d) ∧
      ∀ i, 64 ≤ i.val → y.regs i = x.regs i := by
  let z := (((((x.set Reg.low32 (x.regs Reg.matrixP)).set Reg.low33 (x.regs Reg.matrixQ)).set
    Reg.low34 (x.regs Reg.matrixR)).set Reg.low35 (x.regs Reg.productScratch)).set
    Reg.low36 k).set Reg.low46 p
  have hargs : ExecWithin (B := .standard) (w + 2)
      (ram[ Reg.low32 ← Reg.matrixP; Reg.low33 ← Reg.matrixQ; Reg.low34 ← Reg.matrixR;
        Reg.low35 ← Reg.productScratch; Reg.low36 ← Reg.depth;
        Reg.low46 ← Reg.modulus ]) x z 6 := by
    ram_eval [z, hpr, hkr, Reg.low32, Reg.low33, Reg.low34, Reg.low35, Reg.low36, Reg.low46,
      Reg.matrixP, Reg.matrixQ, Reg.matrixR, Reg.productScratch, Reg.depth, Reg.modulus]
  let f : Fin 64 → Fin 128 := Fin.castLE (by decide)
  have ha : (z.comap f).regs Strassen.Reg.inputA = x.regs Reg.matrixP := by
    simp +decide [z, f, Data.comap, Strassen.Reg.inputA, Reg.low32, Reg.low33,
      Reg.low34, Reg.low35, Reg.low36, Reg.low46]
  have hb : (z.comap f).regs Strassen.Reg.inputB = x.regs Reg.matrixQ := by
    simp +decide [z, f, Data.comap, Strassen.Reg.inputB, Reg.low33,
      Reg.low34, Reg.low35, Reg.low36, Reg.low46]
  have ho : (z.comap f).regs Strassen.Reg.output = x.regs Reg.matrixR := by
    simp +decide [z, f, Data.comap, Strassen.Reg.output,
      Reg.low34, Reg.low35, Reg.low36, Reg.low46]
  have hs : (z.comap f).regs Strassen.Reg.scratch = x.regs Reg.productScratch := by
    simp +decide [z, f, Data.comap, Strassen.Reg.scratch, Reg.low35, Reg.low36, Reg.low46]
  have hk : (z.comap f).regs Strassen.Reg.depth = k := by
    simp +decide [z, f, Data.comap, Strassen.Reg.depth, Reg.low36, Reg.low46]
  have hpp : (z.comap f).regs Strassen.Reg.modulus = p := by
    simp [z, f, Data.comap, Strassen.Reg.modulus, Reg.low46]
  have hmag' : GenericRAM.Signed.Fits w (Strassen.magnitudeBound p 1 1 k : ℤ) := by
    convert hmag using 1
    simp [Strassen.magnitudeBound,
      CyclicConvolution.magnitudeBound, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  obtain ⟨s, he, result⟩ := Strassen.exec (z.comap f) u v hp hpp hk ha hb ho hs
    (by omega) (by omega) hRS (Or.inl (by omega)) (Or.inl hQR)
    hu hv hleft hright hmag' haddr
  let y := s.extend f z
  have hcall : ExecWithin (w + 2) (Strassen.program.rename f) z y
      (Strassen.traceBudget p k + 4 * k + 32) := he.rename (Fin.castLE_injective _)
  have hproduct : ExecWithin (w + 2) product x y
      (Strassen.traceBudget p k + 4 * k + 38) := by
    obtain ⟨n, hn, argsRun⟩ := hargs
    obtain ⟨m, hm, callRun⟩ := hcall
    cases argsRun with
    | seq h₁ rest₁ => cases rest₁ with
      | seq h₂ rest₂ => cases rest₂ with
        | seq h₃ rest₃ => cases rest₃ with
          | seq h₄ rest₄ => cases rest₄ with
            | seq h₅ h₆ =>
              exact ⟨_, by omega, .seq h₁ (.seq h₂ (.seq h₃ (.seq h₄ (.seq h₅ (.seq h₆ callRun)))))⟩
  refine ⟨y, hproduct, ?_, ?_, ?_⟩
  · exact result.values
  · exact result.outside
  · intro i hi
    have hn : ¬∃ j, f j = i := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      change j.val = i.val at hv
      omega
    have hyi : y.regs i = z.regs i := Function.extend_apply' _ _ _ hn
    apply hyi.trans
    simp only [z, Data.set,
      Function.update_of_ne (show i ≠ Reg.low32 by intro he; subst i; contradiction),
      Function.update_of_ne (show i ≠ Reg.low33 by intro he; subst i; contradiction),
      Function.update_of_ne (show i ≠ Reg.low34 by intro he; subst i; contradiction),
      Function.update_of_ne (show i ≠ Reg.low35 by intro he; subst i; contradiction),
      Function.update_of_ne (show i ≠ Reg.low36 by intro he; subst i; contradiction),
      Function.update_of_ne (show i ≠ Reg.low46 by intro he; subst i; contradiction)]

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
