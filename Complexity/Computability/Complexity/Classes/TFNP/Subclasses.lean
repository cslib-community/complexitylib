/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.EvaluationTime
public import Complexity.Computability.Complexity.Classes.TFNP.Subclasses.Principles
public import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.List.GetD

/-!
# Total search subclasses: `PLS`, `PPP`, `PPAD` and `PPA`

The subclasses `PLS` [Johnson, Papadimitriou and Yannakakis][JohnsonPapadimitriouYannakakis1988]
and `PPP`, `PPAD`, `PPA` [Papadimitriou][Papadimitriou1994PPAD], [Beame, Cook, Edmonds,
Impagliazzo and Pitassi][BeameEtAl1998] classify total `FNP` search problems by the finite
combinatorial principle that witnesses totality on the hypercube `{0, 1} ^ (n a)`:

* `Cslib.Complexity.PLS`: problems search-reducible to finding a local minimum of a polynomial-time
  cost function `C : α × List Bool → ℕ` with respect to a polynomial-time neighbor function
  `N : α × List Bool → List Bool` (`localOptRel`).
* `Cslib.Complexity.PPP`: problems search-reducible to finding a preimage of `0 ^ (n a)` or a
  collision of a polynomial-time map `F : α × List Bool → List Bool` (`pigeonRel`).
* `Cslib.Complexity.PPAD`: problems search-reducible to finding an unbalanced vertex other than
  the source `0 ^ (n a)` (or showing `0 ^ (n a)` itself lacks an active outgoing edge) in a
  directed graph of in-degree and out-degree at most `1` given by polynomial-time predecessor and
  successor maps `P, S : α × List Bool → List Bool` (`endOfLineRel`).
* `Cslib.Complexity.PPA`: problems search-reducible to finding an odd-degree vertex other than
  `0 ^ (n a)` (or showing `0 ^ (n a)` has even degree) in an undirected graph of maximum degree `2`
  given by two polynomial-time neighbor maps `N₁, N₂ : α × List Bool → List Bool` (`leafRel`).

## Uniform polynomial-time families and canonical circuit problems

Each class is defined via *uniform polynomial-time families* on the instance type `α`: the vertex
bit-length `n : α → ℕ` is computable in polynomial time in unary (`encUnary`), and the
neighbor, successor, predecessor or cost maps are computable in polynomial time on pairs
`encPair enc encBits` (with costs in binary `encNat`), in the sense of
`Turing.MultiTapeTM.ComputableInPolyTime`. By pulling a family back along the instance map of a
search reduction, each class is closed under `SearchReducible` across arbitrary encoded instance
  types
(`SearchReducible.mem_PLS`, `.mem_PPP`, `.mem_PPAD`, `.mem_PPA`).

The canonical circuit-presented problems `LocalOpt`, `Pigeon`, `EndOfLine` and `Leaf`, whose
instances supply `n` in unary together with raw De Morgan circuit codes
(`Cslib.Circuits.Boolean.encCode`) evaluated via `evalCode`
(`Complexity.Computability.Circuit.Boolean.EvaluationTime`), are instances of these uniform
families (`LocalOpt_mem_PLS`, `Pigeon_mem_PPP`, `EndOfLine_mem_PPAD`, `Leaf_mem_PPA`) and
therefore belong to `TFNP`. The companion module
`Complexity/Computability/Complexity/Classes/TFNP/Subclasses/Completeness.lean` compiles
uniform polynomial-time family evaluations into circuit codes, proving `SearchComplete` for
`LocalOpt`, `Pigeon`, `EndOfLine` and `Leaf`. These reductions preserve vertex witnesses and, for
local search, the numerical cost values through fixed-width binary words with leading zeros.

## Main definitions

* `Cslib.Complexity.PLS`, `Cslib.Complexity.PPP`, `Cslib.Complexity.PPAD`, `Cslib.Complexity.PPA`.
* `Cslib.Complexity.padBits`, `Cslib.Complexity.evalCircuitOutputs`,
  `Cslib.Complexity.evalCircuitCode`: circuit-code evaluation normalized to `n`-bit strings.
* `Cslib.Complexity.CircuitCode`, `Cslib.Complexity.encPigeon`, `Cslib.Complexity.encLocalOpt`,
  `Cslib.Complexity.encEndOfLine`, `Cslib.Complexity.encLeaf`.
* `Cslib.Complexity.LocalOpt`, `Cslib.Complexity.Pigeon`, `Cslib.Complexity.EndOfLine`,
  `Cslib.Complexity.Leaf`: the canonical circuit-presented total search problems.

## Main results

* `Cslib.Complexity.PLS_subset_TFNP`, `Cslib.Complexity.PPP_subset_TFNP`,
  `Cslib.Complexity.PPAD_subset_TFNP`, `Cslib.Complexity.PPA_subset_TFNP`.
* `Cslib.Complexity.PPAD_subset_PPP`, `Cslib.Complexity.PPAD_subset_PPA`: `PPAD` is contained in
  both `PPP` and `PPA` [Papadimitriou1994PPAD], [BeameEtAl1998].
* `Cslib.Complexity.LocalOpt_mem_PLS`, `Cslib.Complexity.Pigeon_mem_PPP`,
  `Cslib.Complexity.EndOfLine_mem_PPAD`, `Cslib.Complexity.Leaf_mem_PPA`.
* `Cslib.Complexity.LocalOpt_mem_TFNP`, `Cslib.Complexity.Pigeon_mem_TFNP`,
  `Cslib.Complexity.EndOfLine_mem_TFNP`, `Cslib.Complexity.Leaf_mem_TFNP`.

## References

* [D. S. Johnson, C. H. Papadimitriou, M. Yannakakis, *How easy is local
  search?*][JohnsonPapadimitriouYannakakis1988]
* [C. H. Papadimitriou, *On the complexity of the parity argument and other inefficient proofs of
  existence*][Papadimitriou1994PPAD]
* [P. Beame, S. Cook, J. Edmonds, R. Impagliazzo, T. Pitassi, *The relative complexity of NP
  search problems*][BeameEtAl1998]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {α β : Type}

/-! ### Polynomial-time bit-string and binary-number primitives -/

/-- `zeroVertex n = List.replicate n false` is computable in polynomial time from `n` in unary. -/
private theorem computableTidilyInPolyTime_zeroVertex :
    ComputableTidilyInPolyTime zeroVertex encUnary encBits := by
  have heq (n : ℕ) : (List.replicate n true).foldl (fun acc _ => false :: acc) [] =
      zeroVertex n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.replicate_succ', List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      rfl
  have h := foldl_of_bounded_growth (encA := encBool) (encL := encBits) (encB := encBits)
    (list := fun n => List.replicate n true) (init := fun _ => [])
    (step := fun acc _ => false :: acc)
    (of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl) (const [])
    (bitsCons (const false) (fst encBits encBool)) (growth := 1) (fun _ _ => by simp)
  simpa only [heq] using h

private theorem computableTidilyInPolyTime_zeroVertex_comp {encIn : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    ComputableTidilyInPolyTime (fun a => zeroVertex (n a)) encIn encBits :=
  computableTidilyInPolyTime_zeroVertex.comp hn

attribute [local fun_prop] computableTidilyInPolyTime_zeroVertex_comp

@[fun_prop]
theorem computableInPolyTime_zeroVertex_comp {encIn : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun a => zeroVertex (n a)) encIn encBits :=
  .of_tidy (computableTidilyInPolyTime_zeroVertex_comp hn.tidy)

/-- One step of converting a most-significant-first bit string to `Nat.bits` (`encNat`): strip
leading `false` bits and prepend significant bits. -/
private def binaryBitsStep (acc : List Bool) (bit : Bool) : List Bool :=
  if acc.isEmpty && !bit then [] else bit :: acc

private theorem foldl_binaryBitsStep (w : List Bool) :
    w.foldl binaryBitsStep [] = (binaryValue w).bits := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w b ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, binaryValue_snoc]
    rcases Nat.eq_zero_or_pos (binaryValue w) with h0 | hpos
    · rw [h0]
      cases b <;> rfl
    · have hne : (binaryValue w).bits ≠ [] := by
        intro h
        have hbv := binaryValue_reverse_bits (binaryValue w)
        rw [h] at hbv
        change 0 = binaryValue w at hbv
        omega
      have hemp : (binaryValue w).bits.isEmpty = false := List.isEmpty_eq_false_iff.2 hne
      have hbit : 2 * binaryValue w + b.toNat = Nat.bit b (binaryValue w) := by
        cases b <;> simp [Nat.bit_val]
      rw [hbit, Nat.bits_append_bit _ _ (by omega)]
      simp [binaryBitsStep, hemp]

/-- Decoding a most-significant-first bit string to its binary natural number (`encNat`) is
polynomial-time. -/
private theorem computableTidilyInPolyTime_binaryValue :
    ComputableTidilyInPolyTime binaryValue encBits encNat := by
  have hstep : ComputableTidilyInPolyTime
      (fun p : List Bool × Bool => binaryBitsStep p.1 p.2)
      (encPair encBits encBool) encBits := by
    unfold binaryBitsStep
    fun_prop
  have hfold := foldl_of_bounded_growth (encA := encBool) (encL := encBits) (encB := encBits)
    id' (const []) hstep (growth := 1) fun acc bit => by
      unfold binaryBitsStep
      split_ifs <;> simp
  exact hfold.of_enc_eq fun w => (foldl_binaryBitsStep w).symm

@[fun_prop]
theorem computableInPolyTime_binaryValue_comp {encIn : α ↪ List Bool} {w : α → List Bool}
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun a => binaryValue (w a)) encIn encNat := by
  have hw := hw.tidy
  exact .of_tidy (computableTidilyInPolyTime_binaryValue.comp hw)

/-- Comparing the binary values of two bit strings is polynomial-time. -/
theorem computableInPolyTime_binaryValue_le :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => decide (binaryValue p.1 ≤ binaryValue p.2))
      (encPair encBits encBits) encBool :=
  .of_tidy (binary_le.comp
    ((computableTidilyInPolyTime_binaryValue.comp (fst encBits encBits)).prod
      (computableTidilyInPolyTime_binaryValue.comp (snd encBits encBits))))

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Comparing two binary natural numbers (`encNat`) is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_nat_le :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
      (encPair encNat encNat) encBool :=
  .of_tidy (binary_le)

@[fun_prop]
theorem computableInPolyTime_nat_le' {encIn : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left encIn encNat)
    (hright : ComputableInPolyTime right encIn encNat) :
    ComputableInPolyTime (fun a => decide (left a ≤ right a)) encIn encBool :=
  computableInPolyTime_nat_le.comp (hleft.prod hright)

/-! ### `FNP` and `TFNP` membership of the family relations -/

private theorem computableTidilyInPolyTime_hasOut {enc : α ↪ List Bool} {n : α → ℕ}
    {P S : α × List Bool → List Bool} (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hP : ComputableTidilyInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableTidilyInPolyTime S (encPair enc encBits) encBits) :
    ComputableTidilyInPolyTime (fun x : α × List Bool => hasOut n P S x.1 x.2)
      (encPair enc encBits) encBool := by
  unfold hasOut
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_hasOut

@[fun_prop]
theorem computableInPolyTime_hasOut {enc : α ↪ List Bool} {n : α → ℕ}
    {P S : α × List Bool → List Bool} (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits) :
    ComputableInPolyTime (fun x : α × List Bool => hasOut n P S x.1 x.2)
      (encPair enc encBits) encBool :=
  .of_tidy (computableTidilyInPolyTime_hasOut hn.tidy hP.tidy hS.tidy)

private theorem computableTidilyInPolyTime_hasIn {enc : α ↪ List Bool} {n : α → ℕ}
    {P S : α × List Bool → List Bool} (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hP : ComputableTidilyInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableTidilyInPolyTime S (encPair enc encBits) encBits) :
    ComputableTidilyInPolyTime (fun x : α × List Bool => hasIn n P S x.1 x.2)
      (encPair enc encBits) encBool := by
  unfold hasIn
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_hasIn

attribute [local fun_prop] ComputableInPolyTime.tidy in
@[fun_prop]
theorem computableInPolyTime_hasIn {enc : α ↪ List Bool} {n : α → ℕ}
    {P S : α × List Bool → List Bool} (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits) :
    ComputableInPolyTime (fun x : α × List Bool => hasIn n P S x.1 x.2)
      (encPair enc encBits) encBool :=
  .of_tidy (computableTidilyInPolyTime_hasIn hn.tidy hP.tidy hS.tidy)

private theorem computableTidilyInPolyTime_undirectedEdge {enc : α ↪ List Bool}
    {N₁ N₂ : α × List Bool → List Bool}
    (hN₁ : ComputableTidilyInPolyTime N₁ (encPair enc encBits) encBits)
    (hN₂ : ComputableTidilyInPolyTime N₂ (encPair enc encBits) encBits)
    {u v : α × List Bool → List Bool}
    (hu : ComputableTidilyInPolyTime u (encPair enc encBits) encBits)
    (hv : ComputableTidilyInPolyTime v (encPair enc encBits) encBits) :
    ComputableTidilyInPolyTime (fun x : α × List Bool => undirectedEdge N₁ N₂ x.1 (u x) (v x))
      (encPair enc encBits) encBool := by
  unfold undirectedEdge
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_undirectedEdge

attribute [local fun_prop] ComputableInPolyTime.tidy in
@[fun_prop]
theorem computableInPolyTime_undirectedEdge {enc : α ↪ List Bool}
    {N₁ N₂ : α × List Bool → List Bool}
    (hN₁ : ComputableInPolyTime N₁ (encPair enc encBits) encBits)
    (hN₂ : ComputableInPolyTime N₂ (encPair enc encBits) encBits)
    {u v : α × List Bool → List Bool}
    (hu : ComputableInPolyTime u (encPair enc encBits) encBits)
    (hv : ComputableInPolyTime v (encPair enc encBits) encBits) :
    ComputableInPolyTime (fun x : α × List Bool => undirectedEdge N₁ N₂ x.1 (u x) (v x))
      (encPair enc encBits) encBool :=
  .of_tidy (computableTidilyInPolyTime_undirectedEdge hN₁.tidy hN₂.tidy hu.tidy hv.tidy)

@[fun_prop]
private theorem computableTidilyInPolyTime_bool_bne {encIn : α ↪ List Bool} {f g : α → Bool}
    (hf : ComputableTidilyInPolyTime f encIn encBool)
    (hg : ComputableTidilyInPolyTime g encIn encBool) :
    ComputableTidilyInPolyTime (fun a => f a != g a) encIn encBool :=
  (of_finite (fun p : Bool × Bool => p.1 != p.2)).comp (hf.prod hg)

private theorem computableTidilyInPolyTime_hasOddDegree {enc : α ↪ List Bool}
    {N₁ N₂ : α × List Bool → List Bool}
    (hN₁ : ComputableTidilyInPolyTime N₁ (encPair enc encBits) encBits)
    (hN₂ : ComputableTidilyInPolyTime N₂ (encPair enc encBits) encBits) :
    ComputableTidilyInPolyTime (fun x : α × List Bool => hasOddDegree N₁ N₂ x.1 x.2)
      (encPair enc encBits) encBool := by
  unfold hasOddDegree
  fun_prop

attribute [local fun_prop] computableTidilyInPolyTime_hasOddDegree

attribute [local fun_prop] ComputableInPolyTime.tidy in
@[fun_prop]
theorem computableInPolyTime_hasOddDegree {enc : α ↪ List Bool}
    {N₁ N₂ : α × List Bool → List Bool}
    (hN₁ : ComputableInPolyTime N₁ (encPair enc encBits) encBits)
    (hN₂ : ComputableInPolyTime N₂ (encPair enc encBits) encBits) :
    ComputableInPolyTime (fun x : α × List Bool => hasOddDegree N₁ N₂ x.1 x.2)
      (encPair enc encBits) encBool :=
  .of_tidy (computableTidilyInPolyTime_hasOddDegree hN₁.tidy hN₂.tidy)

/-- A polynomial-time local-search family defines an `FNP` relation. -/
theorem localOptRel_mem_FNP {enc : α ↪ List Bool} {n : α → ℕ}
    {N : α × List Bool → List Bool} {C : α × List Bool → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hN : ComputableInPolyTime N (encPair enc encBits) encBits)
    (hC : ComputableInPolyTime C (encPair enc encBits) encNat) :
    localOptRel n N C ∈ FNP enc := by
  have hn := hn.tidy
  have hN := hN.tidy
  have hC := hC.tidy
  obtain ⟨p, hp⟩ := hn.polyBounded.exists_polynomial
  refine ⟨⟨p, fun a u h => h.1 ▸ hp a⟩,
    fun x => decide (x.2.length = n x.1) && decide (C x ≤ C (x.1, N x)), ?_, fun a u => ?_⟩
  · fun_prop
  · simp [localOptRel]

/-- A polynomial-time length-preserving local-search family defines a `TFNP` relation. -/
theorem localOptRel_mem_TFNP {enc : α ↪ List Bool} {n : α → ℕ}
    {N : α × List Bool → List Bool} {C : α × List Bool → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hN : ComputableInPolyTime N (encPair enc encBits) encBits)
    (hC : ComputableInPolyTime C (encPair enc encBits) encNat)
    (hlen : ∀ a u, u.length = n a → (N (a, u)).length = n a) :
    localOptRel n N C ∈ TFNP enc :=
  ⟨localOptRel_mem_FNP hn hN hC, isTotalSearch_localOptRel hlen⟩

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- A polynomial-time pigeonhole family defines an `FNP` relation. -/
theorem pigeonRel_mem_FNP {enc : α ↪ List Bool} {n : α → ℕ} {F : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits) :
    pigeonRel n F ∈ FNP enc := by
  have hn := hn.tidy
  have hF := hF.tidy
  obtain ⟨p, hp⟩ := hn.polyBounded.exists_polynomial
  refine mem_FNP.mpr ⟨⟨2 * p, fun a w h => by
      simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
      have := hp a; have := h.1; omega⟩,
    fun x => decide (x.2.length = 2 * n x.1) &&
      (decide (F (x.1, x.2.take (n x.1)) = zeroVertex (n x.1)) ||
        (decide (x.2.take (n x.1) ≠ x.2.drop (n x.1)) &&
          decide (F (x.1, x.2.take (n x.1)) = F (x.1, x.2.drop (n x.1))))),
    ?_, fun a w => ?_⟩
  · have h2 : ComputableTidilyInPolyTime (fun x : α × List Bool => 2 * n x.1)
        (encPair enc encBits) encUnary :=
      unary_mul.comp ((const 2).prod (hn.comp (fst enc encBits)))
    refine .of_tidy (bool_and' (decide_eq' (length_bits.comp (snd enc encBits)) h2) ?_)
    fun_prop
  · simp [pigeonRel]

/-- A polynomial-time length-preserving pigeonhole family defines a `TFNP` relation. -/
theorem pigeonRel_mem_TFNP {enc : α ↪ List Bool} {n : α → ℕ} {F : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits)
    (hlen : ∀ a u, u.length = n a → (F (a, u)).length = n a) :
    pigeonRel n F ∈ TFNP enc :=
  ⟨pigeonRel_mem_FNP hn hF, isTotalSearch_pigeonRel hlen⟩

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- A polynomial-time directed end-of-line family defines an `FNP` relation. -/
theorem endOfLineRel_mem_FNP {enc : α ↪ List Bool} {n : α → ℕ}
    {P S : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits) :
    endOfLineRel n P S ∈ FNP enc := by
  have hn := hn.tidy
  have hP := hP.tidy
  have hS := hS.tidy
  obtain ⟨p, hp⟩ := hn.polyBounded.exists_polynomial
  refine ⟨⟨p, fun a u h => h.1 ▸ hp a⟩,
    fun x => decide (x.2.length = n x.1) &&
      ((hasIn n P S x.1 x.2 != hasOut n P S x.1 x.2) == decide (x.2 ≠ zeroVertex (n x.1))),
    ?_, fun a u => ?_⟩
  · fun_prop
  · simp [endOfLineRel]

/-- A polynomial-time length-preserving directed end-of-line family defines a `TFNP` relation. -/
theorem endOfLineRel_mem_TFNP {enc : α ↪ List Bool} {n : α → ℕ}
    {P S : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    endOfLineRel n P S ∈ TFNP enc :=
  ⟨endOfLineRel_mem_FNP hn hP hS, isTotalSearch_endOfLineRel hS_len⟩

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- A polynomial-time undirected parity family defines an `FNP` relation. -/
theorem leafRel_mem_FNP {enc : α ↪ List Bool} {n : α → ℕ}
    {N₁ N₂ : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hN₁ : ComputableInPolyTime N₁ (encPair enc encBits) encBits)
    (hN₂ : ComputableInPolyTime N₂ (encPair enc encBits) encBits) :
    leafRel n N₁ N₂ ∈ FNP enc := by
  have hn := hn.tidy
  have hN₁ := hN₁.tidy
  have hN₂ := hN₂.tidy
  obtain ⟨p, hp⟩ := hn.polyBounded.exists_polynomial
  refine ⟨⟨p, fun a u h => h.1 ▸ hp a⟩,
    fun x => decide (x.2.length = n x.1) &&
      (hasOddDegree N₁ N₂ x.1 x.2 == decide (x.2 ≠ zeroVertex (n x.1))),
    ?_, fun a u => ?_⟩
  · fun_prop
  · simp [leafRel]

/-- A polynomial-time length-preserving undirected parity family defines a `TFNP` relation. -/
theorem leafRel_mem_TFNP {enc : α ↪ List Bool} {n : α → ℕ}
    {N₁ N₂ : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hN₁ : ComputableInPolyTime N₁ (encPair enc encBits) encBits)
    (hN₂ : ComputableInPolyTime N₂ (encPair enc encBits) encBits)
    (hN₁_len : ∀ a u, u.length = n a → (N₁ (a, u)).length = n a)
    (hN₂_len : ∀ a u, u.length = n a → (N₂ (a, u)).length = n a) :
    leafRel n N₁ N₂ ∈ TFNP enc :=
  ⟨leafRel_mem_FNP hn hN₁ hN₂, isTotalSearch_leafRel hN₁_len hN₂_len⟩

/-! ### The subclasses `PLS`, `PPP`, `PPAD` and `PPA` -/

/-- **Polynomial Local Search (`PLS`)** [Johnson, Papadimitriou and
Yannakakis][JohnsonPapadimitriouYannakakis1988]: `FNP` search problems search-reducible to finding
a local minimum of a uniform polynomial-time local-search family `localOptRel n N C`. -/
def PLS (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | R ∈ FNP enc ∧ ∃ (n : α → ℕ) (N : α × List Bool → List Bool) (C : α × List Bool → ℕ),
    ComputableInPolyTime n enc encUnary ∧
    ComputableInPolyTime N (encPair enc encBits) encBits ∧
    ComputableInPolyTime C (encPair enc encBits) encNat ∧
    (∀ a u, u.length = n a → (N (a, u)).length = n a) ∧
    SearchReducible enc enc R (localOptRel n N C)}

/-- **Polynomial Pigeonhole Principle (`PPP`)** [Papadimitriou][Papadimitriou1994PPAD]: `FNP`
search problems search-reducible to finding a preimage of `0 ^ (n a)` or a collision of a uniform
polynomial-time pigeonhole family `pigeonRel n F`. -/
def PPP (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | R ∈ FNP enc ∧ ∃ (n : α → ℕ) (F : α × List Bool → List Bool),
    ComputableInPolyTime n enc encUnary ∧
    ComputableInPolyTime F (encPair enc encBits) encBits ∧
    (∀ a u, u.length = n a → (F (a, u)).length = n a) ∧
    SearchReducible enc enc R (pigeonRel n F)}

/-- **Polynomial Parity Argument on Directed graphs (`PPAD`)**
[Papadimitriou][Papadimitriou1994PPAD]: `FNP` search problems search-reducible to finding an
end-of-line vertex of a uniform polynomial-time directed path family `endOfLineRel n P S`. -/
def PPAD (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | R ∈ FNP enc ∧ ∃ (n : α → ℕ) (P S : α × List Bool → List Bool),
    ComputableInPolyTime n enc encUnary ∧
    ComputableInPolyTime P (encPair enc encBits) encBits ∧
    ComputableInPolyTime S (encPair enc encBits) encBits ∧
    (∀ a u, u.length = n a → (P (a, u)).length = n a) ∧
    (∀ a u, u.length = n a → (S (a, u)).length = n a) ∧
    SearchReducible enc enc R (endOfLineRel n P S)}

/-- **Polynomial Parity Argument (`PPA`)** [Papadimitriou][Papadimitriou1994PPAD]: `FNP` search
problems search-reducible to finding a leaf of a uniform polynomial-time degree-`≤ 2` undirected
graph family `leafRel n N₁ N₂`. -/
def PPA (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | R ∈ FNP enc ∧ ∃ (n : α → ℕ) (N₁ N₂ : α × List Bool → List Bool),
    ComputableInPolyTime n enc encUnary ∧
    ComputableInPolyTime N₁ (encPair enc encBits) encBits ∧
    ComputableInPolyTime N₂ (encPair enc encBits) encBits ∧
    (∀ a u, u.length = n a → (N₁ (a, u)).length = n a) ∧
    (∀ a u, u.length = n a → (N₂ (a, u)).length = n a) ∧
    SearchReducible enc enc R (leafRel n N₁ N₂)}

variable {enc : α ↪ List Bool} {encB : β ↪ List Bool} {R : α → List Bool → Prop}
  {T : β → List Bool → Prop}

theorem mem_PLS : R ∈ PLS enc ↔ R ∈ FNP enc ∧
    ∃ (n : α → ℕ) (N : α × List Bool → List Bool) (C : α × List Bool → ℕ),
      ComputableInPolyTime n enc encUnary ∧
      ComputableInPolyTime N (encPair enc encBits) encBits ∧
      ComputableInPolyTime C (encPair enc encBits) encNat ∧
      (∀ a u, u.length = n a → (N (a, u)).length = n a) ∧
      SearchReducible enc enc R (localOptRel n N C) :=
  Iff.rfl

theorem mem_PPP : R ∈ PPP enc ↔ R ∈ FNP enc ∧
    ∃ (n : α → ℕ) (F : α × List Bool → List Bool),
      ComputableInPolyTime n enc encUnary ∧
      ComputableInPolyTime F (encPair enc encBits) encBits ∧
      (∀ a u, u.length = n a → (F (a, u)).length = n a) ∧
      SearchReducible enc enc R (pigeonRel n F) :=
  Iff.rfl

theorem mem_PPAD : R ∈ PPAD enc ↔ R ∈ FNP enc ∧
    ∃ (n : α → ℕ) (P S : α × List Bool → List Bool),
      ComputableInPolyTime n enc encUnary ∧
      ComputableInPolyTime P (encPair enc encBits) encBits ∧
      ComputableInPolyTime S (encPair enc encBits) encBits ∧
      (∀ a u, u.length = n a → (P (a, u)).length = n a) ∧
      (∀ a u, u.length = n a → (S (a, u)).length = n a) ∧
      SearchReducible enc enc R (endOfLineRel n P S) :=
  Iff.rfl

theorem mem_PPA : R ∈ PPA enc ↔ R ∈ FNP enc ∧
    ∃ (n : α → ℕ) (N₁ N₂ : α × List Bool → List Bool),
      ComputableInPolyTime n enc encUnary ∧
      ComputableInPolyTime N₁ (encPair enc encBits) encBits ∧
      ComputableInPolyTime N₂ (encPair enc encBits) encBits ∧
      (∀ a u, u.length = n a → (N₁ (a, u)).length = n a) ∧
      (∀ a u, u.length = n a → (N₂ (a, u)).length = n a) ∧
      SearchReducible enc enc R (leafRel n N₁ N₂) :=
  Iff.rfl

/-- Every uniform polynomial-time local-search family is in `PLS`. -/
theorem localOptRel_mem_PLS {n : α → ℕ} {N : α × List Bool → List Bool} {C : α × List Bool → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hN : ComputableInPolyTime N (encPair enc encBits) encBits)
    (hC : ComputableInPolyTime C (encPair enc encBits) encNat)
    (hlen : ∀ a u, u.length = n a → (N (a, u)).length = n a) :
    localOptRel n N C ∈ PLS enc := by
  exact mem_PLS.mpr ⟨localOptRel_mem_FNP hn hN hC, n, N, C, hn, hN, hC, hlen, .refl _ _⟩

/-- Every uniform polynomial-time pigeonhole family is in `PPP`. -/
theorem pigeonRel_mem_PPP {n : α → ℕ} {F : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits)
    (hlen : ∀ a u, u.length = n a → (F (a, u)).length = n a) :
    pigeonRel n F ∈ PPP enc := by
  exact mem_PPP.mpr ⟨pigeonRel_mem_FNP hn hF, n, F, hn, hF, hlen, .refl _ _⟩

/-- Every uniform polynomial-time directed end-of-line family is in `PPAD`. -/
theorem endOfLineRel_mem_PPAD {n : α → ℕ} {P S : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hP_len : ∀ a u, u.length = n a → (P (a, u)).length = n a)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    endOfLineRel n P S ∈ PPAD enc := by
  exact mem_PPAD.mpr
    ⟨endOfLineRel_mem_FNP hn hP hS, n, P, S, hn, hP, hS, hP_len, hS_len, .refl _ _⟩

/-- Every uniform polynomial-time undirected parity family is in `PPA`. -/
theorem leafRel_mem_PPA {n : α → ℕ} {N₁ N₂ : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hN₁ : ComputableInPolyTime N₁ (encPair enc encBits) encBits)
    (hN₂ : ComputableInPolyTime N₂ (encPair enc encBits) encBits)
    (hN₁_len : ∀ a u, u.length = n a → (N₁ (a, u)).length = n a)
    (hN₂_len : ∀ a u, u.length = n a → (N₂ (a, u)).length = n a) :
    leafRel n N₁ N₂ ∈ PPA enc := by
  exact mem_PPA.mpr
    ⟨leafRel_mem_FNP hn hN₁ hN₂, n, N₁, N₂, hn, hN₁, hN₂, hN₁_len, hN₂_len, .refl _ _⟩

/-! ### Closure under search reductions -/

/-- `PLS` is closed under polynomial-time search reductions across arbitrary instance types. -/
theorem SearchReducible.mem_PLS (h : SearchReducible enc encB R T) (hR : R ∈ FNP enc)
    (hT : T ∈ PLS encB) : R ∈ PLS enc := by
  obtain ⟨-, n, N, C, hn, hN, hC, hlen, hT_red⟩ := Complexity.mem_PLS.mp hT
  obtain ⟨f, g, hf, hg, -, hsol⟩ := (h.trans hT_red)
  refine Complexity.mem_PLS.mpr ⟨hR, n ∘ f, fun p => N (f p.1, p.2), fun p => C (f p.1, p.2),
    hn.comp hf, hN.comp ((hf.comp (.fst enc encBits)).prod (.snd enc encBits)),
    hC.comp ((hf.comp (.fst enc encBits)).prod (.snd enc encBits)),
    fun a u hu => hlen (f a) u hu,
    .of_isTotalSearch (isTotalSearch_localOptRel fun a u hu => hlen (f a) u hu)
      (.of_tidy id') hg fun a w hw => hsol a w hw⟩

/-- `PPP` is closed under polynomial-time search reductions across arbitrary instance types. -/
theorem SearchReducible.mem_PPP (h : SearchReducible enc encB R T) (hR : R ∈ FNP enc)
    (hT : T ∈ PPP encB) : R ∈ PPP enc := by
  obtain ⟨-, n, F, hn, hF, hlen, hT_red⟩ := Complexity.mem_PPP.mp hT
  obtain ⟨f, g, hf, hg, -, hsol⟩ := (h.trans hT_red)
  refine Complexity.mem_PPP.mpr ⟨hR, n ∘ f, fun p => F (f p.1, p.2),
    hn.comp hf, hF.comp ((hf.comp (.fst enc encBits)).prod (.snd enc encBits)),
    fun a u hu => hlen (f a) u hu,
    .of_isTotalSearch (isTotalSearch_pigeonRel fun a u hu => hlen (f a) u hu)
      (.of_tidy id') hg fun a w hw => hsol a w hw⟩

/-- `PPAD` is closed under polynomial-time search reductions across arbitrary instance types. -/
theorem SearchReducible.mem_PPAD (h : SearchReducible enc encB R T) (hR : R ∈ FNP enc)
    (hT : T ∈ PPAD encB) : R ∈ PPAD enc := by
  obtain ⟨-, n, P, S, hn, hP, hS, hP_len, hS_len, hT_red⟩ := Complexity.mem_PPAD.mp hT
  obtain ⟨f, g, hf, hg, -, hsol⟩ := (h.trans hT_red)
  refine Complexity.mem_PPAD.mpr ⟨hR, n ∘ f, fun p => P (f p.1, p.2), fun p => S (f p.1, p.2),
    hn.comp hf, hP.comp ((hf.comp (.fst enc encBits)).prod (.snd enc encBits)),
    hS.comp ((hf.comp (.fst enc encBits)).prod (.snd enc encBits)),
    fun a u hu => hP_len (f a) u hu, fun a u hu => hS_len (f a) u hu,
    .of_isTotalSearch (isTotalSearch_endOfLineRel fun a u hu => hS_len (f a) u hu)
      (.of_tidy id') hg fun a w hw => hsol a w hw⟩

/-- `PPA` is closed under polynomial-time search reductions across arbitrary instance types. -/
theorem SearchReducible.mem_PPA (h : SearchReducible enc encB R T) (hR : R ∈ FNP enc)
    (hT : T ∈ PPA encB) : R ∈ PPA enc := by
  obtain ⟨-, n, N₁, N₂, hn, hN₁, hN₂, hN₁_len, hN₂_len, hT_red⟩ := Complexity.mem_PPA.mp hT
  obtain ⟨f, g, hf, hg, -, hsol⟩ := (h.trans hT_red)
  refine Complexity.mem_PPA.mpr ⟨hR, n ∘ f, fun p => N₁ (f p.1, p.2), fun p => N₂ (f p.1, p.2),
    hn.comp hf, hN₁.comp ((hf.comp (.fst enc encBits)).prod (.snd enc encBits)),
    hN₂.comp ((hf.comp (.fst enc encBits)).prod (.snd enc encBits)),
    fun a u hu => hN₁_len (f a) u hu, fun a u hu => hN₂_len (f a) u hu,
    .of_isTotalSearch
      (isTotalSearch_leafRel (fun a u hu => hN₁_len (f a) u hu) (fun a u hu => hN₂_len (f a) u hu))
      (.of_tidy id') hg fun a w hw => hsol a w hw⟩

/-! ### Inclusions in `TFNP` and between subclasses -/

/-- **`PLS ⊆ TFNP`**: every problem in `PLS` is total and in `FNP`. -/
theorem PLS_subset_TFNP : PLS enc ⊆ TFNP enc := by
  rintro R ⟨hR, n, N, C, -, -, -, hlen, hred⟩
  exact ⟨hR, hred.isTotalSearch (isTotalSearch_localOptRel hlen)⟩

/-- **`PPP ⊆ TFNP`**: every problem in `PPP` is total and in `FNP`. -/
theorem PPP_subset_TFNP : PPP enc ⊆ TFNP enc := by
  rintro R ⟨hR, n, F, -, -, hlen, hred⟩
  exact ⟨hR, hred.isTotalSearch (isTotalSearch_pigeonRel hlen)⟩

/-- **`PPAD ⊆ TFNP`**: every problem in `PPAD` is total and in `FNP`. -/
theorem PPAD_subset_TFNP : PPAD enc ⊆ TFNP enc := by
  rintro R ⟨hR, n, P, S, -, -, -, -, hS_len, hred⟩
  exact ⟨hR, hred.isTotalSearch (isTotalSearch_endOfLineRel hS_len)⟩

/-- **`PPA ⊆ TFNP`**: every problem in `PPA` is total and in `FNP`. -/
theorem PPA_subset_TFNP : PPA enc ⊆ TFNP enc := by
  rintro R ⟨hR, n, N₁, N₂, -, -, -, hN₁_len, hN₂_len, hred⟩
  exact ⟨hR, hred.isTotalSearch (isTotalSearch_leafRel hN₁_len hN₂_len)⟩

/-- Every directed end-of-line family search-reduces to its associated pigeonhole family. -/
private theorem endOfLineRel_searchReducible_pigeonRel {n : α → ℕ} {P S : α × List Bool → List Bool}
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hP : ComputableTidilyInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableTidilyInPolyTime S (encPair enc encBits) encBits)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    SearchReducible enc enc (endOfLineRel n P S) (pigeonRel n (ppadToPppMap n P S)) := by
  refine .of_isTotalSearch (isTotalSearch_pigeonRel fun a u hu => length_ppadToPppMap (hS_len a) hu)
    (.of_tidy id') (g := fun p => if !hasOut n P S p.1 (p.2.take (n p.1)) then p.2.take (n p.1)
      else p.2.drop (n p.1)) ?_ fun a w hw => endOfLineRel_of_pigeonRel hw
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- **`PPAD ⊆ PPP`** [Papadimitriou][Papadimitriou1994PPAD], [Beame et al.][BeameEtAl1998]: every
problem in `PPAD` is in `PPP`. -/
theorem PPAD_subset_PPP : PPAD enc ⊆ PPP enc := by
  intro R hR'
  obtain ⟨hR, n, P, S, hn, hP, hS, -, hS_len, hred⟩ := mem_PPAD.mp hR'
  have hF : ComputableTidilyInPolyTime (ppadToPppMap n P S) (encPair enc encBits) encBits := by
    unfold ppadToPppMap
    fun_prop
  exact mem_PPP.mpr ⟨hR, n, ppadToPppMap n P S, hn, (.of_tidy hF),
    fun a u hu => length_ppadToPppMap (hS_len a) hu,
    hred.trans (endOfLineRel_searchReducible_pigeonRel hn.tidy hP.tidy hS.tidy hS_len)⟩

/-- Every directed end-of-line family search-reduces to its associated bipartite undirected parity
family. -/
private theorem endOfLineRel_searchReducible_leafRel {n : α → ℕ} {P S : α × List Bool → List Bool}
    (hP_len : ∀ a u, u.length = n a → (P (a, u)).length = n a)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    SearchReducible enc enc (endOfLineRel n P S)
      (leafRel (fun a => n a + 1) (ppadToPpaN₁ n P S) (ppadToPpaN₂ n P S)) :=
  .of_isTotalSearch
    (isTotalSearch_leafRel
      (fun a _ hw => length_ppadToPpaN₁ (hP_len a) (hS_len a) hw)
      (fun _ _ hw => length_ppadToPpaN₂ hw))
    (.of_tidy id') (g := fun p => p.2.tail) (.of_tidy (bitsTail.comp (snd enc encBits)))
    fun _ _ hw => endOfLineRel_tail_of_leafRel hw

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- **`PPAD ⊆ PPA`** [Papadimitriou][Papadimitriou1994PPAD]: every problem in `PPAD` is in `PPA`. -/
theorem PPAD_subset_PPA : PPAD enc ⊆ PPA enc := by
  intro R hR'
  obtain ⟨hR, n, P, S, hn, hP, hS, hP_len, hS_len, hred⟩ := mem_PPAD.mp hR'
  have hn' : ComputableTidilyInPolyTime (fun a => n a + 1) enc encUnary := by fun_prop
  have hN₁ : ComputableTidilyInPolyTime (ppadToPpaN₁ n P S) (encPair enc encBits) encBits := by
    unfold ppadToPpaN₁
    fun_prop
  have hN₂ : ComputableTidilyInPolyTime (ppadToPpaN₂ n P S) (encPair enc encBits) encBits := by
    unfold ppadToPpaN₂ isActiveNonZero
    fun_prop
  exact mem_PPA.mpr
    ⟨hR, fun a => n a + 1, ppadToPpaN₁ n P S, ppadToPpaN₂ n P S, (.of_tidy hn'), (.of_tidy hN₁),
      (.of_tidy hN₂),
      fun a _ hw => length_ppadToPpaN₁ (hP_len a) (hS_len a) hw,
      fun _ _ hw => length_ppadToPpaN₂ hw,
      hred.trans (endOfLineRel_searchReducible_leafRel hP_len hS_len)⟩

/-! ### Evaluating circuit codes into fixed-length bit strings -/

/-- Normalize a bit string `w` to length `n` by truncating or padding with `false`. -/
def padBits (n : ℕ) (w : List Bool) : List Bool :=
  w.take n ++ zeroVertex (n - w.length)

@[simp]
theorem length_padBits (n : ℕ) (w : List Bool) : (padBits n w).length = n := by
  simp only [padBits, List.length_append, List.length_take, length_zeroVertex]
  omega

@[simp]
theorem padBits_of_length_eq {n : ℕ} {w : List Bool} (h : w.length = n) : padBits n w = w := by
  simp [padBits, h, zeroVertex]

@[fun_prop]
theorem computableInPolyTime_padBits {encIn : α ↪ List Bool} {n : α → ℕ}
    {w : α → List Bool} (hn : ComputableInPolyTime n encIn encUnary)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime (fun a => padBits (n a) (w a)) encIn encBits := by
  unfold padBits
  fun_prop

/-- The raw code of a De Morgan circuit: its gate list and output wire numbers. -/
abbrev CircuitCode : Type := List (Op × List ℕ) × List ℕ

/-- Evaluate all output wires listed in `code.2` after running the gate list `code.1` on `u`. -/
def evalCircuitOutputs (code : CircuitCode) (u : List Bool) : List Bool :=
  let vals := evalCode interpretation false u code.1
  code.2.map (fun o => vals.getD o false)

private theorem evalCircuitOutputs_eq_map (code : CircuitCode) (u : List Bool) :
    evalCircuitOutputs code u =
      code.2.map fun o => (evalCode interpretation false u code.1).getD o false :=
  rfl

/-- On the code of a De Morgan circuit, `evalCircuitOutputs` computes the list of output bits. -/
theorem evalCircuitOutputs_code {n m : ℕ} (c : Circuit signature n m) (x : Fin n → Bool) :
    evalCircuitOutputs c.code (List.ofFn x) = List.ofFn (c.eval interpretation x) := by
  rw [evalCircuitOutputs_eq_map]
  refine List.ext_getElem (by simp [Circuit.code]) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_map, Circuit.code, List.getElem_ofFn]
  exact (c.eval_eq_getD interpretation false x ⟨j, by simpa using hj₂⟩).symm

@[fun_prop]
theorem computableInPolyTime_evalCircuitOutputs {encIn : α ↪ List Bool}
    {code : α → CircuitCode} {u : α → List Bool}
    (hcode : ComputableInPolyTime code encIn encCode)
    (hu : ComputableInPolyTime u encIn encBits) :
    ComputableInPolyTime (fun a => evalCircuitOutputs (code a) (u a)) encIn encBits := by
  have hcode := hcode.tidy
  have hu := hu.tidy
  refine .of_tidy ?_
  have hvals : ComputableTidilyInPolyTime
      (fun a => evalCode interpretation false (u a) (code a).1) encIn encBits :=
    (computableInPolyTime_evalCode (.of_tidy hu) (.of_tidy hcode.fst')).tidy
  exact listToBits.comp (mapWith
    (listGetD_binary false (fst encBits encNat) (snd encBits encNat)) hvals hcode.snd')

/-- Evaluate a circuit code on `u` and normalize the output to `n` bits. -/
def evalCircuitCode (n : ℕ) (code : CircuitCode) (u : List Bool) : List Bool :=
  padBits n (evalCircuitOutputs code u)

@[simp]
theorem length_evalCircuitCode (n : ℕ) (code : CircuitCode) (u : List Bool) :
    (evalCircuitCode n code u).length = n :=
  length_padBits n _

/-- On the code of a De Morgan circuit with `n` inputs and `n` outputs, `evalCircuitCode` computes
the `n`-bit output of the circuit. -/
theorem evalCircuitCode_code {n : ℕ} (c : Circuit signature n n) (x : Fin n → Bool) :
    evalCircuitCode n c.code (List.ofFn x) = List.ofFn (c.eval interpretation x) := by
  rw [evalCircuitCode, evalCircuitOutputs_code, padBits_of_length_eq (List.length_ofFn)]

@[fun_prop]
theorem computableInPolyTime_evalCircuitCode {encIn : α ↪ List Bool}
    {n : α → ℕ} {code : α → CircuitCode} {u : α → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hcode : ComputableInPolyTime code encIn encCode)
    (hu : ComputableInPolyTime u encIn encBits) :
    ComputableInPolyTime (fun a => evalCircuitCode (n a) (code a) (u a)) encIn encBits := by
  unfold evalCircuitCode
  fun_prop

/-! ### Canonical circuit-presented problems -/

/-- Encoding of `Pigeon` instances `(n, cF)`: the bit-length `n` in unary and the circuit code
`cF`. -/
abbrev encPigeon : (ℕ × CircuitCode) ↪ List Bool := encPair encUnary encCode

/-- Encoding of `LocalOpt` instances `(n, cN, cC)`: `n` in unary, neighbor circuit `cN`, and cost
circuit `cC`. -/
abbrev encLocalOpt : (ℕ × CircuitCode × CircuitCode) ↪ List Bool :=
  encPair encUnary (encPair encCode encCode)

/-- Encoding of `EndOfLine` instances `(n, cP, cS)`: `n` in unary, predecessor circuit `cP`, and
successor circuit `cS`. -/
abbrev encEndOfLine : (ℕ × CircuitCode × CircuitCode) ↪ List Bool :=
  encPair encUnary (encPair encCode encCode)

/-- Encoding of `Leaf` instances `(n, cN₁, cN₂)`: `n` in unary and the two neighbor circuits
`cN₁, cN₂`. -/
abbrev encLeaf : (ℕ × CircuitCode × CircuitCode) ↪ List Bool :=
  encPair encUnary (encPair encCode encCode)

/-- **Circuit `LocalOpt` (`PLS`)**: given `(n, cN, cC)`, find an `n`-bit string `u` whose neighbor
`evalCircuitCode n cN u` does not have strictly smaller cost
`binaryValue (evalCircuitOutputs cC ·)`. -/
def LocalOpt : (ℕ × CircuitCode × CircuitCode) → List Bool → Prop :=
  localOptRel Prod.fst (fun p => evalCircuitCode p.1.1 p.1.2.1 p.2)
    (fun p => binaryValue (evalCircuitOutputs p.1.2.2 p.2))

/-- **Circuit `Pigeon` (`PPP`)**: given `(n, cF)`, find a `2n`-bit string encoding a preimage of
`0 ^ n` or a collision of `evalCircuitCode n cF`. -/
def Pigeon : (ℕ × CircuitCode) → List Bool → Prop :=
  pigeonRel Prod.fst (fun p => evalCircuitCode p.1.1 p.1.2 p.2)

/-- **Circuit `EndOfLine` (`PPAD`)**: given `(n, cP, cS)`, find an `n`-bit end-of-line vertex of
the directed graph presented by `evalCircuitCode n cP` and `evalCircuitCode n cS`. -/
def EndOfLine : (ℕ × CircuitCode × CircuitCode) → List Bool → Prop :=
  endOfLineRel Prod.fst (fun p => evalCircuitCode p.1.1 p.1.2.1 p.2)
    (fun p => evalCircuitCode p.1.1 p.1.2.2 p.2)

/-- **Circuit `Leaf` (`PPA`)**: given `(n, cN₁, cN₂)`, find an `n`-bit leaf vertex of the
degree-`≤ 2` undirected graph presented by `evalCircuitCode n cN₁` and `evalCircuitCode n cN₂`. -/
def Leaf : (ℕ × CircuitCode × CircuitCode) → List Bool → Prop :=
  leafRel Prod.fst (fun p => evalCircuitCode p.1.1 p.1.2.1 p.2)
    (fun p => evalCircuitCode p.1.1 p.1.2.2 p.2)

theorem isTotalSearch_LocalOpt : IsTotalSearch LocalOpt :=
  isTotalSearch_localOptRel fun _ _ _ => length_evalCircuitCode _ _ _

theorem isTotalSearch_Pigeon : IsTotalSearch Pigeon :=
  isTotalSearch_pigeonRel fun _ _ _ => length_evalCircuitCode _ _ _

theorem isTotalSearch_EndOfLine : IsTotalSearch EndOfLine :=
  isTotalSearch_endOfLineRel fun _ _ _ => length_evalCircuitCode _ _ _

theorem isTotalSearch_Leaf : IsTotalSearch Leaf :=
  isTotalSearch_leafRel (fun _ _ _ => length_evalCircuitCode _ _ _)
    (fun _ _ _ => length_evalCircuitCode _ _ _)

/-- `LocalOpt` is in `PLS`. -/
theorem LocalOpt_mem_PLS : LocalOpt ∈ PLS encLocalOpt :=
  localOptRel_mem_PLS (by fun_prop) (by fun_prop) (by fun_prop)
    fun _ _ _ => length_evalCircuitCode _ _ _

/-- `Pigeon` is in `PPP`. -/
theorem Pigeon_mem_PPP : Pigeon ∈ PPP encPigeon :=
  pigeonRel_mem_PPP (by fun_prop) (by fun_prop)
    fun _ _ _ => length_evalCircuitCode _ _ _

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- `EndOfLine` is in `PPAD`. -/
theorem EndOfLine_mem_PPAD : EndOfLine ∈ PPAD encEndOfLine :=
  endOfLineRel_mem_PPAD (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop))
    (fun _ _ _ => length_evalCircuitCode _ _ _) (fun _ _ _ => length_evalCircuitCode _ _ _)

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- `Leaf` is in `PPA`. -/
theorem Leaf_mem_PPA : Leaf ∈ PPA encLeaf :=
  leafRel_mem_PPA (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop))
    (fun _ _ _ => length_evalCircuitCode _ _ _) (fun _ _ _ => length_evalCircuitCode _ _ _)

/-- `LocalOpt` is in `TFNP`. -/
theorem LocalOpt_mem_TFNP : LocalOpt ∈ TFNP encLocalOpt :=
  PLS_subset_TFNP LocalOpt_mem_PLS

/-- `Pigeon` is in `TFNP`. -/
theorem Pigeon_mem_TFNP : Pigeon ∈ TFNP encPigeon :=
  PPP_subset_TFNP Pigeon_mem_PPP

/-- `EndOfLine` is in `TFNP`. -/
theorem EndOfLine_mem_TFNP : EndOfLine ∈ TFNP encEndOfLine :=
  PPAD_subset_TFNP EndOfLine_mem_PPAD

/-- `Leaf` is in `TFNP`. -/
theorem Leaf_mem_TFNP : Leaf ∈ TFNP encLeaf :=
  PPA_subset_TFNP Leaf_mem_PPA

/-- `EndOfLine` is in `PPP`. -/
theorem EndOfLine_mem_PPP : EndOfLine ∈ PPP encEndOfLine :=
  PPAD_subset_PPP EndOfLine_mem_PPAD

/-- `EndOfLine` is in `PPA`. -/
theorem EndOfLine_mem_PPA : EndOfLine ∈ PPA encEndOfLine :=
  PPAD_subset_PPA EndOfLine_mem_PPAD

end Cslib.Complexity
