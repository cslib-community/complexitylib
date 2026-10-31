/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.GenericRAM.Native.StackRecursion
import Complexity.Computability.Circuit.Frontier.TensorNetwork.DirectContraction
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-! # A stack recursion whose leaves are direct contractions

A toy instance of `Cslib.GenericRAM.StackRecursion` with the direct-summation contraction of an
explicit network as its leaf step: a node `(k, (P, r, d))` is a chain of `k` calls, each with one
child `(k - 1, (P, r, d))` and the identity as combination, ending in a leaf that contracts `d`
modulo `2 ^ P` by `directContractionCertificate`. One fixed native machine computes
`d.contraction % 2 ^ P` on every input, with linear fuel. -/

namespace ComplexityTests.StackRecursionDirect

open Cslib.GenericRAM Cslib.GenericRAM.StackRecursion Cslib.Circuits.Frontier
  Cslib.Circuits.Frontier.ExplicitTensorNetwork Turing.MultiTapeTM

/-- The input of a node: the chain length and a contraction input `(P, r, d)`. -/
abbrev Node := ℕ × (ℕ × ℕ × ExplicitTensorNetwork ℕ)

/-- The chain scheme: the accumulator stores the value of the only child. -/
def chain : Scheme Node (Option ℕ) ℕ where
  isLeaf q := q.1 == 0
  leaf q := directContraction q.2
  start _ := none
  next q a := a.elim (some (q.1 - 1, q.2)) fun _ => none
  absorb _ _ y := some y
  finish _ a := a.getD 0

/-- No invariant. -/
def trivialInvariant : Invariant Node (Option ℕ) ℕ :=
  ⟨fun _ => True, fun _ _ => True, fun _ => True⟩

/-- **Every chain has a derivation**, with `k + 1` nodes and `k` open calls, and the value of
its leaf. -/
theorem eval_chain (k : ℕ) (x : ℕ × ℕ × ExplicitTensorNetwork ℕ) :
    chain.Eval trivialInvariant (k, x) (directContraction x) (k + 1) k := by
  induction k with
  | zero => exact Scheme.Eval.leaf (R := chain) trivial rfl trivial
  | succ k ih =>
    have hloop : chain.Loop trivialInvariant (k + 1, x) (chain.start (k + 1, x))
        (some (directContraction x)) (k + 1 + 0) (max k 0) :=
      Scheme.Loop.child trivial rfl ih (Scheme.Loop.done rfl)
    have h := Scheme.Eval.call (R := chain) (I := trivialInvariant) trivial rfl hloop trivial
    simp only [Nat.add_zero, Nat.max_zero] at h
    exact h

/-- With fuel `2 k + 1`, the machine returns the contraction modulo `2 ^ P`. -/
theorem run_chain (k P r : ℕ) (d : ExplicitTensorNetwork ℕ) :
    chain.run (fun q => 2 * q.1 + 1) id (k, (P, r, d)) = some (d.contraction % 2 ^ P) := by
  rw [Scheme.run_eq_some (fuel := fun q : Node => 2 * q.1 + 1) (root := id)
    (a := (k, (P, r, d))) (eval_chain k (P, r, d)) (by simp; omega), directContraction_eq]

/-- The encoding of a node: the chain length in unary and the contraction input. -/
abbrev encNode : Node ↪ List Bool := encPair encUnary encContractionInput

/-- **The polynomial-time components** of the chain. -/
theorem chain_polyTime : chain.PolyTime encNode (encOption encNat) encNat where
  isLeaf := ComputableInPolyTime.beq (ComputableInPolyTime.fst _ _)
    (ComputableInPolyTime.const 0)
  start := ComputableInPolyTime.const none
  next := by
    have hq := ComputableInPolyTime.fst encNode (encOption encNat)
    have hchild : ComputableInPolyTime (fun p : Node × Option ℕ => (p.1.1 - 1, p.1.2))
        (encPair encNode (encOption encNat)) encNode :=
      (ComputableInPolyTime.unary_sub' ((ComputableInPolyTime.fst _ _).comp hq)
        (ComputableInPolyTime.const 1)).prod ((ComputableInPolyTime.snd _ _).comp hq)
    exact ComputableInPolyTime.optionElimWithInput (value := fun p : Node × Option ℕ => p.2)
      (fallback := fun p => some (p.1.1 - 1, p.1.2)) (body := fun _ _ => none)
      (ComputableInPolyTime.snd _ _) ((ComputableInPolyTime.optionSome encNode).comp hchild)
      (ComputableInPolyTime.const none)
  absorb := (ComputableInPolyTime.optionSome encNat).comp (ComputableInPolyTime.snd _ _)
  finish := ComputableInPolyTime.optionGetDWithInput (ComputableInPolyTime.snd _ _)
    (ComputableInPolyTime.const 0)

/-- The leaf step: direct summation on the contraction input. -/
noncomputable def leafCertificate : NativeCertificate chain.leaf encNode encNat :=
  directContractionCertificate.comp (NativeCertificate.payload encUnary encContractionInput)

/-- The fuel `2 k + 1`, in binary. -/
noncomputable def fuelCertificate :
    NativeCertificate (fun q : Node => 2 * q.1 + 1) encNode encNat :=
  NativeCertificate.ofPolyTime (ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul'
      (ComputableInPolyTime.const 2) (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.const 1)))

/-- The root is the input. -/
noncomputable def rootCertificate : NativeCertificate (id : Node → Node) encNode encNode :=
  NativeCertificate.ofPolyTime ComputableInPolyTime.id'

/-- **One fixed machine computes the contraction modulo `2 ^ P`** through the chain, with the
direct-summation certificate at the leaf. -/
noncomputable def chainCertificate :
    NativeCertificate (chain.run (fun q => 2 * q.1 + 1) id) encNode (encOption encNat) :=
  Scheme.certificate chain_polyTime leafCertificate fuelCertificate rootCertificate

-- It computes `some (d.contraction % 2 ^ P)` on every input.
example (k P r : ℕ) (d : ExplicitTensorNetwork ℕ) :
    chain.run (fun q => 2 * q.1 + 1) id (k, (P, r, d)) = some (d.contraction % 2 ^ P) :=
  run_chain k P r d

/-! ### Resources: a non-polynomial leaf -/

/-- The invariant below the root `(k₀, x)`: nodes and frames keep `x` and a shorter chain, frames
have not yet absorbed their child, and values are residues modulo `2 ^ P`. -/
def bounded (k₀ : ℕ) (x : ℕ × ℕ × ExplicitTensorNetwork ℕ) : Invariant Node (Option ℕ) ℕ :=
  ⟨fun q => q.1 ≤ k₀ ∧ q.2 = x, fun q a => q.1 ≤ k₀ ∧ q.2 = x ∧ a = none,
    fun y => y < 2 ^ x.1⟩

theorem eval_chain_bounded {k₀ k : ℕ} (hk : k ≤ k₀) (x : ℕ × ℕ × ExplicitTensorNetwork ℕ) :
    chain.Eval (bounded k₀ x) (k, x) (directContraction x) (k + 1) k := by
  have hv : directContraction x < 2 ^ x.1 := by
    obtain ⟨P, r, d⟩ := x
    rw [directContraction_eq]
    exact Nat.mod_lt _ (Nat.two_pow_pos P)
  induction k with
  | zero => exact Scheme.Eval.leaf (R := chain) ⟨hk, rfl⟩ rfl hv
  | succ k ih =>
    have hloop : chain.Loop (bounded k₀ x) (k + 1, x) (chain.start (k + 1, x))
        (some (directContraction x)) (k + 1 + 0) (max k 0) :=
      Scheme.Loop.child ⟨hk, rfl, rfl⟩ rfl (ih (by omega)) (Scheme.Loop.done rfl)
    have h := Scheme.Eval.call (R := chain) (I := bounded k₀ x) ⟨hk, rfl⟩ rfl hloop hv
    simp only [Nat.add_zero, Nat.max_zero] at h
    exact h

/-- **The resources of the chain**: `2 k + 2` rounds, each a polynomial in
`(k + 1) (F + 1)` plus the leaf's `K (n + 1) ^ K 2 ^ m`, and polynomial workspace, for `F` three
times the input length and `m` the number of edges. Only the leaf is exponential. -/
theorem chainCertificate_le : ∃ K L : ℕ, ∀ (k P r : ℕ) (d : ExplicitTensorNetwork ℕ),
    let n := (encNode (k, (P, r, d))).length
    chainCertificate.time (k, (P, r, d)) ≤ fuelCertificate.time (k, (P, r, d)) +
        rootCertificate.time (k, (P, r, d)) + 2 * n +
        (2 * k + 1 + 1) * (K * ((k + 1) * (3 * n + 1 + 1)) ^ K +
          (n + L * (n + 1) ^ L * 2 ^ d.numEdges) + ((encNat (2 * k + 1)).length + 1) ^ 2) ∧
      chainCertificate.space (k, (P, r, d)) ≤ fuelCertificate.space (k, (P, r, d)) +
        rootCertificate.space (k, (P, r, d)) + 2 * n +
        K * ((k + 1) * (3 * n + 1 + 1)) ^ K + (n + L * (n + 1) ^ L) +
          (encNat (2 * k + 1)).length := by
  obtain ⟨K, hK⟩ := Scheme.certificate_le chain_polyTime leafCertificate
  obtain ⟨L, hL⟩ := exists_directContractionCertificate_le
  refine ⟨K, L, fun k P r d => ?_⟩
  set x := (P, r, d)
  set n := (encNode (k, x)).length
  have hP : P ≤ n := by simp [n, x, encContractionInput, length_encPair]; omega
  have hm : (encContractionInput x).length ≤ n := by
    simp only [n, length_encPair]; omega
  have hnode (q : Node) (hq : (bounded k x).node q) : (encNode q).length ≤ n := by
    obtain ⟨hq, hx⟩ := hq
    obtain ⟨k', y⟩ := q
    simp only at hq hx
    subst hx
    simp [n, encNode, length_encPair]
    omega
  refine hK fuelCertificate rootCertificate (bounded k x)
    (3 * n + 1) (n + L * (n + 1) ^ L * 2 ^ d.numEdges) (n + L * (n + 1) ^ L)
    (fun q hq => ⟨by have := hnode q hq; omega, fun _ => ?_⟩) (fun q a ha => ?_)
    (fun y hy => ?_) (k, x) _ _ _ (eval_chain_bounded le_rfl x)
  · obtain ⟨hq1, hx⟩ := hq
    have hq' := hnode q ⟨hq1, hx⟩
    have hl : directContractionCertificate.time x ≤
          L * ((encContractionInput x).length + 1) ^ L * 2 ^ d.numEdges ∧
        directContractionCertificate.space x ≤ L * ((encContractionInput x).length + 1) ^ L :=
      hL x
    have hpow : ((encContractionInput x).length + 1) ^ L ≤ (n + 1) ^ L :=
      Nat.pow_le_pow_left (by omega) L
    refine ⟨?_, ?_⟩
    · change (encNode q).length + directContractionCertificate.time q.2 ≤ _
      rw [hx]
      have := Nat.mul_le_mul_right (2 ^ d.numEdges) (Nat.mul_le_mul_left L hpow)
      omega
    · change (encNode q).length + directContractionCertificate.space q.2 ≤ _
      rw [hx]
      have := Nat.mul_le_mul_left L hpow
      omega
  · obtain ⟨hq, hx, rfl⟩ := ha
    have h1 := hnode q ⟨hq, hx⟩
    have h2 := length_encPair (enc₁ := encNode) (enc₂ := encOption encNat) (q, none)
    simp only [encOption_none, List.length_nil] at h2
    omega
  · have : (encNat y).length ≤ P := by
      have h := Nat.size_le.mpr hy
      rw [← Nat.size_eq_bits_len] at h
      exact h
    omega

end ComplexityTests.StackRecursionDirect
