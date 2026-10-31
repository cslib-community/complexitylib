/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.GenericRAM.Native.StackRecursion
import Complexity.Foundations.Data.Nat.RecursionTree
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.SqrtLog
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-! # Depth-first stack recursion on a toy scheme

The halving recursion: a node `x ≥ 2` has two children `x / 2`, a leaf has value `1`, and a call
adds its children's values. The value of `x` is its number of leaves. The tests run the stack
machine, derive `Eval` for every node, instantiate the polynomial-time components (so the
`PolyTime` hypotheses of the native certificate are satisfiable) and check the node-count
arithmetic. -/

namespace ComplexityTests.StackRecursion

open Cslib.GenericRAM Cslib.GenericRAM.StackRecursion Turing.MultiTapeTM

/-- The halving scheme. The accumulator counts the children done and sums their values. -/
def halving : Scheme ℕ (ℕ × ℕ) ℕ where
  isLeaf x := decide (x < 2)
  leaf _ := 1
  start _ := (0, 0)
  next x a := if a.1 < 2 then some (x / 2) else none
  absorb _ a y := (a.1 + 1, a.2 + y)
  finish _ a := a.2

/-- The number of leaves below `x`. -/
def leaves (x : ℕ) : ℕ := if x < 2 then 1 else 2 * leaves (x / 2)
decreasing_by omega

/-- The number of nodes below `x`. -/
def nodes (x : ℕ) : ℕ := if x < 2 then 1 else 2 * nodes (x / 2) + 1
decreasing_by omega

/-- The number of open calls while evaluating `x`. -/
def height (x : ℕ) : ℕ := if x < 2 then 0 else height (x / 2) + 1
decreasing_by omega

/-- No invariant. -/
def none : Invariant ℕ (ℕ × ℕ) ℕ := ⟨fun _ => True, fun _ _ => True, fun _ => True⟩

-- The machine on `8`: four levels, eight leaves, fifteen nodes, so `2 * 15 - 1 = 29` steps.
example : halving.run (fun _ : Unit => 29) (fun _ => 8) () = some 8 := by decide

-- One step fewer, the value `4` of the second child is still waiting to be absorbed by the root.
example : halving.run (fun _ : Unit => 28) (fun _ => 8) () = some 4 := by decide

-- Extra fuel changes nothing: the final state is fixed.
example : halving.run (fun _ : Unit => 100) (fun _ => 8) () = some 8 := by decide

/-- **Every node has a derivation**, with its leaves as value. -/
theorem eval_halving (x : ℕ) : halving.Eval none x (leaves x) (nodes x) (height x) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : x < 2
    · have hl : leaves x = 1 := by rw [leaves]; simp [hx]
      have hn : nodes x = 1 := by rw [nodes]; simp [hx]
      have hh : height x = 0 := by rw [height]; simp [hx]
      rw [hl, hn, hh]
      exact Scheme.Eval.leaf (R := halving) trivial (decide_eq_true hx) trivial
    · have hl : leaves x = leaves (x / 2) + leaves (x / 2) := by rw [leaves]; simp [hx]; ring
      have hn : nodes x = (nodes (x / 2) + (nodes (x / 2) + 0)) + 1 := by
        rw [nodes]; simp [hx]; ring
      have hh : height x = max (height (x / 2)) (max (height (x / 2)) 0) + 1 := by
        rw [height]; simp [hx]
      have hc := ih (x / 2) (by omega)
      have hloop : halving.Loop none x (halving.start x)
          (2, 0 + leaves (x / 2) + leaves (x / 2)) (nodes (x / 2) + (nodes (x / 2) + 0))
          (max (height (x / 2)) (max (height (x / 2)) 0)) :=
        Scheme.Loop.child trivial (by simp [halving]) hc
          (Scheme.Loop.child trivial (by simp [halving]) hc (Scheme.Loop.done (by simp [halving])))
      have := Scheme.Eval.call (R := halving) (I := none) trivial (decide_eq_false hx) hloop
        trivial
      rw [hl, hn, hh]
      simpa [halving] using this

/-- `nodes x + 1 ≤ 2 max x 1`. -/
theorem nodes_add_one_le (x : ℕ) : nodes x + 1 ≤ 2 * max x 1 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : x < 2
    · rw [nodes]; simp only [hx, ite_true]; omega
    · have := ih (x / 2) (by omega)
      rw [nodes]; simp only [hx, ite_false]
      omega

/-- `2 * nodes x - 1 ≤ 4 * x + 1`: linear fuel suffices. -/
theorem two_mul_nodes_le (x : ℕ) : 2 * nodes x - 1 ≤ 4 * x + 1 := by
  have := nodes_add_one_le x
  omega

/-- With fuel `4 x + 1`, the machine returns the number of leaves, on every input. -/
theorem run_halving (x : ℕ) :
    halving.run (fun x => 4 * x + 1) id x = some (leaves x) :=
  Scheme.run_eq_some (eval_halving x) (two_mul_nodes_le x)

/-- **The polynomial-time components** of the halving scheme, in binary. -/
theorem halving_polyTime : halving.PolyTime encNat (encPair encNat encNat) encNat where
  isLeaf := ComputableInPolyTime.binary_lt' ComputableInPolyTime.id'
    (ComputableInPolyTime.const 2)
  start := ComputableInPolyTime.const (0, 0)
  next := by
    have hk : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => p.2.1)
        (encPair encNat (encPair encNat encNat)) encNat :=
      (ComputableInPolyTime.fst encNat encNat).comp (ComputableInPolyTime.snd _ _)
    have hhalf : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => p.1 / 2)
        (encPair encNat (encPair encNat encNat)) encNat :=
      (ComputableInPolyTime.binary_shiftRight' (ComputableInPolyTime.fst _ _)
        (ComputableInPolyTime.const 1)).of_enc_eq fun p => by
          rw [Nat.shiftRight_eq_div_pow, pow_one]
    refine (ComputableInPolyTime.ite (ComputableInPolyTime.binary_lt' hk
      (ComputableInPolyTime.const 2)) ((ComputableInPolyTime.optionSome encNat).comp hhalf)
      (ComputableInPolyTime.const Option.none)).of_enc_eq fun p => ?_
    by_cases h : p.2.1 < 2
    · have h' : p.2.1 ≤ 1 := by omega
      simp [halving, h, h']
    · have h' : ¬p.2.1 ≤ 1 := by omega
      simp [halving, h, h']
  absorb := by
    have hk : ComputableInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × ℕ => p.1.2.1)
        (encPair (encPair encNat (encPair encNat encNat)) encNat) encNat :=
      (ComputableInPolyTime.fst encNat encNat).comp
        ((ComputableInPolyTime.snd encNat _).comp (ComputableInPolyTime.fst _ _))
    have hs : ComputableInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × ℕ => p.1.2.2)
        (encPair (encPair encNat (encPair encNat encNat)) encNat) encNat :=
      (ComputableInPolyTime.snd encNat encNat).comp
        ((ComputableInPolyTime.snd encNat _).comp (ComputableInPolyTime.fst _ _))
    exact (ComputableInPolyTime.binary_add.comp (hk.prod (ComputableInPolyTime.const 1))).prod
      (ComputableInPolyTime.binary_add.comp (hs.prod (ComputableInPolyTime.snd _ _)))
  finish := (ComputableInPolyTime.snd encNat encNat).comp (ComputableInPolyTime.snd _ _)

/-- The fuel `4 x + 1`, in binary. -/
noncomputable def fuelCertificate : NativeCertificate (fun x : ℕ => 4 * x + 1) encNat encNat :=
  NativeCertificate.ofPolyTime (ComputableInPolyTime.binary_add.comp
    ((ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 4)
      ComputableInPolyTime.id').prod (ComputableInPolyTime.const 1)))

/-- The root is the input. -/
noncomputable def rootCertificate : NativeCertificate (id : ℕ → ℕ) encNat encNat :=
  NativeCertificate.ofPolyTime ComputableInPolyTime.id'

/-- The leaf step: the constant `1`. -/
def leafCertificate : NativeCertificate halving.leaf encNat encNat := NativeCertificate.const 1

/-- **One fixed machine computes the number of leaves** of every input. -/
noncomputable def halvingCertificate :
    NativeCertificate (halving.run (fun x => 4 * x + 1) id) encNat (encOption encNat) :=
  Scheme.certificate halving_polyTime leafCertificate fuelCertificate rootCertificate

/-- The size invariant below a root `x₀`: nodes are at most `x₀`, frames have counted at most two
children and summed at most `x₀ + 1`, and values are at most `x₀ + 1`. -/
def bounded (x₀ : ℕ) : Invariant ℕ (ℕ × ℕ) ℕ :=
  ⟨fun y => y ≤ x₀, fun y a => y ≤ x₀ ∧ a.1 ≤ 2 ∧ a.2 ≤ x₀ + 1, fun v => v ≤ x₀ + 1⟩

theorem leaves_le_max (x : ℕ) : leaves x ≤ max x 1 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    by_cases hx : x < 2
    · rw [leaves]; simp only [hx, ite_true]; omega
    · have := ih (x / 2) (by omega)
      rw [leaves]; simp only [hx, ite_false]
      omega

theorem leaves_le (x : ℕ) : leaves x ≤ x + 1 := by
  have := leaves_le_max x
  omega

/-- **Every node below `x₀` has a derivation keeping the size invariant.** -/
theorem eval_halving_bounded {x₀ x : ℕ} (hx₀ : x ≤ x₀) :
    halving.Eval (bounded x₀) x (leaves x) (nodes x) (height x) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    have hlx := leaves_le x
    by_cases hx : x < 2
    · have hl : leaves x = 1 := by rw [leaves]; simp [hx]
      have hn : nodes x = 1 := by rw [nodes]; simp [hx]
      have hh : height x = 0 := by rw [height]; simp [hx]
      rw [hl, hn, hh]
      exact Scheme.Eval.leaf (R := halving) hx₀ (decide_eq_true hx)
        (show 1 ≤ x₀ + 1 by omega)
    · have hl : leaves x = leaves (x / 2) + leaves (x / 2) := by rw [leaves]; simp [hx]; ring
      have hn : nodes x = (nodes (x / 2) + (nodes (x / 2) + 0)) + 1 := by
        rw [nodes]; simp [hx]; ring
      have hh : height x = max (height (x / 2)) (max (height (x / 2)) 0) + 1 := by
        rw [height]; simp [hx]
      have hc := ih (x / 2) (by omega) (by omega)
      have hhalf := leaves_le (x / 2)
      have hloop : halving.Loop (bounded x₀) x (halving.start x)
          (2, 0 + leaves (x / 2) + leaves (x / 2)) (nodes (x / 2) + (nodes (x / 2) + 0))
          (max (height (x / 2)) (max (height (x / 2)) 0)) :=
        Scheme.Loop.child (show x ≤ x₀ ∧ 0 ≤ 2 ∧ 0 ≤ x₀ + 1 by omega) (by simp [halving]) hc
          (Scheme.Loop.child (show x ≤ x₀ ∧ 1 ≤ 2 ∧ 0 + leaves (x / 2) ≤ x₀ + 1 by omega)
            (by simp [halving]) hc (Scheme.Loop.done (by simp [halving])))
      have := Scheme.Eval.call (R := halving) (I := bounded x₀) hx₀ (decide_eq_false hx) hloop
        (show 0 + leaves (x / 2) + leaves (x / 2) ≤ x₀ + 1 by omega)
      rw [hl, hn, hh]
      simpa [halving] using this

private theorem length_encNat_mono {y z : ℕ} (h : y ≤ z) :
    (encNat y).length ≤ (encNat z).length := by
  simpa [Nat.size_eq_bits_len] using Nat.size_le_size h

/-- **The resource theorem applies**: with `ℓ` the length of `x + 1` in binary, nodes, frames and
values are at most `F = 3 ℓ + 6` long, and the leaf costs at most `F`, so the time is
`4 x + 2` times a polynomial in `(height x + 1) (F + 1)`, and the workspace is polynomial in it. -/
theorem halvingCertificate_le : ∃ K : ℕ, ∀ x : ℕ,
    halvingCertificate.time x ≤ fuelCertificate.time x + rootCertificate.time x +
        2 * (encNat x).length + (4 * x + 1 + 1) *
          (K * ((height x + 1) * (3 * (encNat (x + 1)).length + 6 + 1)) ^ K +
            (3 * (encNat (x + 1)).length + 6) + ((encNat (4 * x + 1)).length + 1) ^ 2) ∧
      halvingCertificate.space x ≤ fuelCertificate.space x + rootCertificate.space x +
        2 * (encNat x).length +
          K * ((height x + 1) * (3 * (encNat (x + 1)).length + 6 + 1)) ^ K +
            (3 * (encNat (x + 1)).length + 6) + (encNat (4 * x + 1)).length := by
  obtain ⟨K, hK⟩ := Scheme.certificate_le halving_polyTime leafCertificate
  refine ⟨K, fun x => ?_⟩
  have h2 : (encNat 2).length ≤ 2 := by decide
  refine hK fuelCertificate rootCertificate (bounded x) (3 * (encNat (x + 1)).length + 6) _ _
    (fun y hy => ⟨?_, fun _ => ⟨?_, ?_⟩⟩) (fun y a ha => ?_) (fun v hv => ?_) x (leaves x)
    (nodes x) (height x) (eval_halving_bounded le_rfl)
  · have := length_encNat_mono (show y ≤ x + 1 by simp only [bounded] at hy; omega)
    omega
  · have := length_encNat_mono (show y ≤ x + 1 by simp only [bounded] at hy; omega)
    simp only [leafCertificate, NativeCertificate.const_time]
    omega
  · have := length_encNat_mono (show y ≤ x + 1 by simp only [bounded] at hy; omega)
    simp only [leafCertificate, NativeCertificate.const_space]
    omega
  · obtain ⟨hy, hk, hs⟩ := ha
    have h1 := length_encNat_mono (show y ≤ x + 1 by omega)
    have h3 := length_encNat_mono (show a.2 ≤ x + 1 by omega)
    have h4 := (length_encNat_mono hk).trans h2
    simp only [length_encPair]
    omega
  · have := length_encNat_mono (show v ≤ x + 1 by simp only [bounded] at hv; omega)
    omega

/-! ### Node-count arithmetic -/

-- Binary branching for three levels: `1 + 2 (1 + 2 (1 + 2)) = 15` nodes.
example : Nat.recursionBound (fun _ => 2) 3 0 = 15 := rfl

-- The product bound: `15 ≤ 4 * 2 ^ 3`.
example : Nat.recursionBound (fun _ => 2) 3 0 ≤ (3 + 1) * ∏ _j ∈ Finset.range 3, max 1 2 :=
  Nat.recursionBound_le _ 3 0

-- Halving excess exponents: `100 + 50 + 25 + 12 + 6 = 193 ≤ 200`.
example : ∑ j ∈ Finset.range 5, 100 / 2 ^ j ≤ 2 * 100 := Nat.sum_div_two_pow_le 100 5

/-! ### The clock -/

-- The fuel `2 ^ (3 n / √⌊log₂ n⌋)` of a subexponential recursion, from `n` in unary.
example : ComputableInPolyTime (fun n : ℕ => 2 ^ (3 * n / Nat.sqrt (Nat.log 2 n))) encUnary
    encNat :=
  ComputableInPolyTime.unary_two_pow_div_sqrt_log_two 3

-- At `n = 16`: `⌊log₂ 16⌋ = 4`, `√4 = 2`, so the clock is `2 ^ 24`.
example : 2 ^ (3 * 16 / Nat.sqrt (Nat.log 2 16)) = 2 ^ 24 := by
  have h1 : Nat.log 2 16 = 4 := by rw [show (16 : ℕ) = 2 ^ 4 by rfl, Nat.log_pow one_lt_two]
  have h2 : Nat.sqrt 4 = 2 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  rw [h1, h2]

end ComplexityTests.StackRecursion
