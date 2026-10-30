/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationSpec
public import Complexity.Algorithms.ExactTriangle.PieceBounds

/-!
# Adjacency in prepared native ExactTriangle matrices

These consumer lemmas connect actual prepared memory to the existing finite lopsided graph.
The source prime window supplies the padding bound, and piece membership supplies each local
coordinate. Neither is an additional layout certificate for the program.

## Main results

* `PreparationSpec.instance_adjacency`: actual stored cells give the finite adjacency relations
  and zero padding, with piece coordinates and middle-width admissibility derived.

## References

The adjacency relations are those of the pinned
[Theorem 17 matrix construction](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/WriteMatrices.lean).
The composition with native memory readback is original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PreparationSpec

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix

/-- The actual prepared matrix cells express the existing finite graph's adjacency, and the
unused middle positions are zero. The prime-window and piece hypotheses discharge every
padding and local-coordinate premise of the matrix-entry API. -/
theorem instance_adjacency {n D g p : ℕ} (values : ℕ → ℤ)
    (wAB wBC wAC : Fin n → Fin n → ℤ)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow D)
    (hAB : ∀ a b, values (pairIndex (a, b)) = wAB a b)
    (hBC : ∀ b c, values (n * n + pairIndex (b, c)) = wBC b c)
    (hAC : ∀ a c, values (2 * (n * n) + pairIndex (a, c)) = wAC a c)
    {initial y : Data 64} (h : Instances.Output n D g p values initial y)
    (idx : InstanceIndex p) (hidx : idx ∈ instanceIndices wAB D g p) :
    let N := n * n
    let C := fun rho => Nat.count (fun q => (values q % (p : ℤ)).toNat = rho) N
    let H := numPieces n D g
    let B := pieceSize D g
    let ord := ChunkCatalogue.before C (queryCap n D) idx.1.val + idx.2.1
    let base := y.regs Instances.output +
      (ord * H + idx.2.2) * (6 + 2 * (n * D))
    let G := lopInstance wAB wBC wAC D g p idx
    (∀ (a b c : Fin n) (hc : c ∈ piece n D g idx.2.2) (label : Fin p),
      let middle := c.val % B * p + label.val
      (y.mem (base + 6 + (a.val * D + middle)) = 1 ↔
        G.adjA a (⟨c, hc⟩, label)) ∧
      (y.mem (base + 6 + n * D + (middle * n + b.val)) = 1 ↔
        G.adjB (⟨c, hc⟩, label) b)) ∧
    (∀ (a b : Fin n) (middle : Fin D),
      min B (n - idx.2.2 * B) ≤ middle.val / p →
        y.mem (base + 6 + (a.val * D + middle.val)) = 0 ∧
        y.mem (base + 6 + n * D + (middle.val * n + b.val)) = 0) := by
  let N := n * n
  let R := fun q => (values q % (p : ℤ)).toNat
  let C := fun rho => Nat.count (fun q => R q = rho) N
  let H := numPieces n D g
  let B := pieceSize D g
  let K := ChunkCatalogue.before C (queryCap n D) p
  let ord := ChunkCatalogue.before C (queryCap n D) idx.1.val + idx.2.1
  let base := 5 + 6 * N + p + 2 * N * p + 3 * K +
    (ord * H + idx.2.2) * (6 + 2 * (n * D))
  let A : WriteMatrices.Args :=
    ⟨5 + 5 * N, base + 6, n, D, p, idx.2.2 * B, min B (n - idx.2.2 * B), idx.1.val⟩
  let A' := { A with src := 5 + 4 * N, dst := base + 6 + n * D }
  have hp0 : p ≠ 0 := (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).1.ne_zero
  obtain ⟨-, hL, hR⟩ := instance_readback values wAB hp0 hAB hD hDn hg h idx hidx
  change (Block.mk A.dst (n * D)).Realizes y.mem
    (fun j => WriteMatrices.entry false A (fun q => R (2 * N + q)) j) at hL
  change (Block.mk A'.dst (n * D)).Realizes y.mem
    (fun j => WriteMatrices.entry true A' (fun q => R (N + q)) j) at hR
  have hpad : A.length * A.p ≤ A.D := pieceLength_mul_le_of_mem_sqrtPrimeWindow hg hp
  change min B (n - idx.2.2 * B) * p ≤ D at hpad
  have hloadL (a c : Fin n) :
      R (2 * N + (a.val * n + c.val)) = (wAC a c).natMod p := by
    change (values (2 * (n * n) + pairIndex (a, c)) % (p : ℤ)).toNat = _
    rw [hAC]
    rfl
  have hloadR (b c : Fin n) :
      R (N + (b.val * n + c.val)) = (wBC b c).natMod p := by
    change (values (n * n + pairIndex (b, c)) % (p : ℤ)).toNat = _
    rw [hBC]
    rfl
  have hout : y.regs Instances.output = 5 + 6 * N + p + 2 * N * p + 3 * K := h.2.2.2.1
  dsimp only
  rw [hout]
  constructor
  · intro a b c hc label
    obtain ⟨hvertex, hv⟩ := piece_coordinate hD hg c hc
    let v : Fin A.length := ⟨c.val % B, hv⟩
    have hm : v.val * p + label.val < D := by
      have hstep := Nat.mul_le_mul_right p v.isLt
      have hl := label.isLt
      change (v.val + 1) * p ≤ min B (n - idx.2.2 * B) * p at hstep
      rw [Nat.add_mul, Nat.one_mul] at hstep
      omega
    have hli : a.val * D + (v.val * p + label.val) < n * D := by
      have hi := Nat.mul_le_mul_right D a.isLt
      rw [Nat.succ_mul] at hi
      omega
    have hri : (v.val * p + label.val) * n + b.val < n * D := by
      have hi := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hm)
      rw [Nat.succ_mul] at hi
      have hb := b.isLt
      rw [Nat.mul_comm n D]
      omega
    have hleft := hL ⟨a.val * D + (v.val * p + label.val), hli⟩
    have hright := hR ⟨(v.val * p + label.val) * n + b.val, hri⟩
    change y.mem (A.dst + (a.val * D + (v.val * p + label.val))) = _ at hleft
    change y.mem (A'.dst + ((v.val * p + label.val) * n + b.val)) = _ at hright
    constructor
    · rw [hleft]
      exact MatrixSpec.left_lopInstance A (fun q => R (2 * N + q)) wAB wBC wAC
        g idx.2.1 idx.2.2 idx.1 rfl a c v label hc hvertex hpad hloadL
    · rw [hright]
      exact MatrixSpec.right_lopInstance A' (fun q => R (N + q)) wAB wBC wAC
        g idx.2.1 idx.2.2 idx.1 b c v label hc hvertex hloadR
  · intro a b middle hmiddle
    have hli : a.val * D + middle.val < n * D := by
      have hi := Nat.mul_le_mul_right D a.isLt
      rw [Nat.succ_mul] at hi
      have hm := middle.isLt
      omega
    have hri : middle.val * n + b.val < n * D := by
      have hi := Nat.mul_le_mul_right n (Nat.succ_le_of_lt middle.isLt)
      rw [Nat.succ_mul] at hi
      have hb := b.isLt
      rw [Nat.mul_comm n D]
      omega
    have hleft := hL ⟨a.val * D + middle.val, hli⟩
    have hright := hR ⟨middle.val * n + b.val, hri⟩
    change y.mem (A.dst + (a.val * D + middle.val)) = _ at hleft
    change y.mem (A'.dst + (middle.val * n + b.val)) = _ at hright
    constructor
    · rw [hleft]
      exact MatrixSpec.left_padding A (fun q => R (2 * N + q)) a middle hmiddle
    · rw [hright]
      exact MatrixSpec.right_padding A' (fun q => R (N + q)) b middle hmiddle

end Cslib.Algorithms.WordRAM.ExactTriangle.PreparationSpec
