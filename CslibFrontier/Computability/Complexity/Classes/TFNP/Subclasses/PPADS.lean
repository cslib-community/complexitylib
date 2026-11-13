/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The total search subclass `PPADS`

`PPADS` [Papadimitriou][Papadimitriou1994PPAD], [Beame, Cook, Edmonds, Impagliazzo and
Pitassi][BeameEtAl1998] is the "sink" variant of `PPAD`: in a directed graph of in-degree and
out-degree at most `1` presented by predecessor and successor maps `P, S`, if the source `0 ^ n` has
an active outgoing edge then some other vertex is a *sink*. Unlike `endOfLineRel`, proper sources
other than `0 ^ n` are not solutions.

We reuse the active-edge predicates `hasOut` and `hasIn` of the end-of-line presentation of `PPAD`
(`CslibFrontier/Computability/Complexity/Classes/TFNP/Subclasses/Principles.lean`), so a solution of
`sinkOfLineRel` is exactly a solution of `endOfLineRel` without an active outgoing edge
(`sinkOfLineRel_iff`).

## Main definitions

* `Cslib.Complexity.sinkOfLineRel`: the sink-of-line relation.
* `Cslib.Complexity.PPADS`: problems search-reducible to a uniform polynomial-time sink-of-line
  family.

## Main results

* `Cslib.Complexity.sinkOfLineRel_iff`: sink-of-line solutions are the end-of-line solutions
  without an active outgoing edge.
* `Cslib.Complexity.sinkOfLineRel_of_pigeonRel`, `Cslib.Complexity.isTotalSearch_sinkOfLineRel`:
  the pigeonhole map `ppadToPppMap` reduces sink-of-line to pigeonhole.
* `Cslib.Complexity.PPADS_subset_TFNP`, `Cslib.Complexity.PPAD_subset_PPADS`,
  `Cslib.Complexity.PPADS_subset_PPP`: `PPAD ⊆ PPADS ⊆ PPP ⊆ TFNP` [BeameEtAl1998].
* `Cslib.Complexity.PPAD_subset_PPP`, `Cslib.Complexity.EndOfLine_mem_PPP`: `PPAD ⊆ PPP`
  [Papadimitriou1994PPAD], derived through `PPADS`.

## References

* [C. H. Papadimitriou, *On the complexity of the parity argument and other inefficient proofs of
  existence*][Papadimitriou1994PPAD]
* [P. Beame, S. Cook, J. Edmonds, R. Impagliazzo, T. Pitassi, *The relative complexity of NP search
  problems*][BeameEtAl1998]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α β : Type}

/-! ### The sink-of-line principle -/

/-- The search relation of a sink-of-line family (`PPADS`): a vertex `u` of length `n a` is a
solution if it has no active outgoing edge and is either the source `0 ^ (n a)` or has an active
incoming edge. -/
def sinkOfLineRel (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α) (u : List Bool) : Prop :=
  u.length = n a ∧ hasOut n P S a u = false ∧ (u = zeroVertex (n a) ∨ hasIn n P S a u = true)

/-- A sink-of-line solution is exactly an end-of-line solution without an active outgoing edge. -/
theorem sinkOfLineRel_iff {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α} {u : List Bool} :
    sinkOfLineRel n P S a u ↔ endOfLineRel n P S a u ∧ hasOut n P S a u = false := by
  by_cases hu : u = zeroVertex (n a)
  · subst hu
    simp [sinkOfLineRel, endOfLineRel]
  · cases hin : hasIn n P S a u <;> cases hout : hasOut n P S a u <;>
      simp [sinkOfLineRel, endOfLineRel, hu, hin, hout]

theorem endOfLineRel_of_sinkOfLineRel {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α}
    {u : List Bool} (h : sinkOfLineRel n P S a u) : endOfLineRel n P S a u :=
  (sinkOfLineRel_iff.mp h).1

/-- The vertex selected from a pigeonhole solution of `ppadToPppMap n P S` has no active outgoing
edge. -/
theorem hasOut_select_eq_false_of_pigeonRel {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α}
    {w : List Bool} (h : pigeonRel n (ppadToPppMap n P S) a w) :
    hasOut n P S a
      (if !hasOut n P S a (w.take (n a)) then w.take (n a) else w.drop (n a)) = false := by
  by_cases hu : hasOut n P S a (w.take (n a)) = false
  · simp [hu]
  · simp only [Bool.not_eq_false] at hu
    simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    by_contra hv
    simp only [Bool.not_eq_false] at hv
    rcases h.2 with hz | ⟨hne, hcoll⟩
    · have hFz : S (a, w.take (n a)) = zeroVertex (n a) := by
        simpa [ppadToPppMap, hu] using hz
      simp only [hasOut, decide_eq_true_eq] at hu
      exact hu.2.2 hFz
    · have hSuv : S (a, w.take (n a)) = S (a, w.drop (n a)) := by
        simpa [ppadToPppMap, hu, hv] using hcoll
      simp only [hasOut, decide_eq_true_eq] at hu hv
      exact hne (by rw [← hu.1, hSuv, hv.1])

/-- Any solution of `pigeonRel` for `ppadToPppMap n P S` yields a solution of `sinkOfLineRel n P S`
by selecting whichever of the two `n a`-bit halves lacks an active outgoing edge. -/
theorem sinkOfLineRel_of_pigeonRel {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α}
    {w : List Bool} (h : pigeonRel n (ppadToPppMap n P S) a w) :
    sinkOfLineRel n P S a
      (if !hasOut n P S a (w.take (n a)) then w.take (n a) else w.drop (n a)) :=
  sinkOfLineRel_iff.mpr ⟨endOfLineRel_of_pigeonRel h, hasOut_select_eq_false_of_pigeonRel h⟩

/-- **Sink-of-line principle**: if `S (a, ·)` preserves length `n a`, some vertex of length `n a`
satisfies `sinkOfLineRel`. -/
theorem exists_sinkOfLine {n : α → ℕ} {P S : α × List Bool → List Bool} {a : α}
    (hS : ∀ u, u.length = n a → (S (a, u)).length = n a) :
    ∃ u, sinkOfLineRel n P S a u := by
  obtain ⟨w, hw⟩ := exists_pigeon (n := n) (F := ppadToPppMap n P S) (a := a)
    (fun u hu => length_ppadToPppMap hS hu)
  exact ⟨_, sinkOfLineRel_of_pigeonRel hw⟩

/-- `sinkOfLineRel` is total whenever the successor map preserves the vertex bit-length. -/
theorem isTotalSearch_sinkOfLineRel {n : α → ℕ} {P S : α × List Bool → List Bool}
    (hS : PreservesWidth n S) : IsTotalSearch (sinkOfLineRel n P S) :=
  fun a => exists_sinkOfLine (hS a)

/-! ### `FNP` and `TFNP` membership -/

/-- A polynomial-time sink-of-line family defines an `FNP` relation. -/
theorem sinkOfLineRel_mem_FNP {enc : α ↪ List Bool} {n : α → ℕ}
    {P S : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits) :
    sinkOfLineRel n P S ∈ FNP enc := by
  obtain ⟨p, hp⟩ := (polyBounded hn).exists_polynomial
  refine ⟨⟨p, fun a u h => h.1 ▸ hp a⟩,
    fun x => decide (x.2.length = n x.1 ∧ hasOut n P S x.1 x.2 = false ∧
      (x.2 = zeroVertex (n x.1) ∨ hasIn n P S x.1 x.2 = true)), ?_, fun a u => ?_⟩
  · fun_prop
  · simp [sinkOfLineRel]

/-- A polynomial-time length-preserving sink-of-line family defines a `TFNP` relation. -/
theorem sinkOfLineRel_mem_TFNP {enc : α ↪ List Bool} {n : α → ℕ}
    {P S : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hS_len : PreservesWidth n S) : sinkOfLineRel n P S ∈ TFNP enc :=
  ⟨sinkOfLineRel_mem_FNP hn hP hS, isTotalSearch_sinkOfLineRel hS_len⟩

/-! ### The class `PPADS` -/

/-- **Polynomial Parity Argument on Directed graphs, Sink version (`PPADS`)**
[Papadimitriou][Papadimitriou1994PPAD], [Beame et al.][BeameEtAl1998]: `FNP` search problems
search-reducible to finding a sink of a uniform polynomial-time directed path family
`sinkOfLineRel n P S`. -/
def PPADS (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | R ∈ FNP enc ∧ ∃ (n : α → ℕ) (P S : α × List Bool → List Bool),
    ComputableInPolyTime n enc encUnary ∧
    ComputableInPolyTime P (encPair enc encBits) encBits ∧
    ComputableInPolyTime S (encPair enc encBits) encBits ∧
    PreservesWidth n P ∧ PreservesWidth n S ∧
    SearchReducible enc enc R (sinkOfLineRel n P S)}

variable {enc : α ↪ List Bool} {encB : β ↪ List Bool} {R : α → List Bool → Prop}
  {T : β → List Bool → Prop}

theorem mem_PPADS : R ∈ PPADS enc ↔ R ∈ FNP enc ∧
    ∃ (n : α → ℕ) (P S : α × List Bool → List Bool),
      ComputableInPolyTime n enc encUnary ∧
      ComputableInPolyTime P (encPair enc encBits) encBits ∧
      ComputableInPolyTime S (encPair enc encBits) encBits ∧
      PreservesWidth n P ∧ PreservesWidth n S ∧
      SearchReducible enc enc R (sinkOfLineRel n P S) :=
  Iff.rfl

/-- Every uniform polynomial-time sink-of-line family is in `PPADS`. -/
theorem sinkOfLineRel_mem_PPADS {n : α → ℕ} {P S : α × List Bool → List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hP_len : PreservesWidth n P) (hS_len : PreservesWidth n S) : sinkOfLineRel n P S ∈ PPADS enc :=
  mem_PPADS.mpr ⟨sinkOfLineRel_mem_FNP hn hP hS, n, P, S, hn, hP, hS, hP_len, hS_len, .refl _ _⟩

/-- `PPADS` is closed under polynomial-time search reductions across arbitrary instance types. -/
theorem SearchReducible.mem_PPADS (h : SearchReducible enc encB R T) (hR : R ∈ FNP enc)
    (hT : T ∈ PPADS encB) : R ∈ PPADS enc := by
  obtain ⟨-, n, P, S, hn, hP, hS, hP_len, hS_len, hT⟩ := Complexity.mem_PPADS.mp hT
  obtain ⟨f, hf, h⟩ := (h.trans hT).exists_reindex
  exact Complexity.mem_PPADS.mpr ⟨hR, n ∘ f, fun p => P (f p.1, p.2), fun p => S (f p.1, p.2),
    hn.comp hf, by fun_prop, by fun_prop, fun a => hP_len (f a), fun a => hS_len (f a), h⟩

/-! ### Inclusions -/

/-- **`PPADS ⊆ TFNP`**: every problem in `PPADS` is total and in `FNP`. -/
theorem PPADS_subset_TFNP : PPADS enc ⊆ TFNP enc := by
  rintro R ⟨hR, n, P, S, -, -, -, -, hS_len, hred⟩
  exact ⟨hR, hred.isTotalSearch (isTotalSearch_sinkOfLineRel hS_len)⟩

/-- **`PPAD ⊆ PPADS`** [Beame et al.][BeameEtAl1998]: the identity is a search reduction from
end-of-line to sink-of-line, since every sink is an end of a line. -/
theorem PPAD_subset_PPADS : PPAD enc ⊆ PPADS enc := by
  intro R hR'
  obtain ⟨hR, n, P, S, hn, hP, hS, hP_len, hS_len, hred⟩ := mem_PPAD.mp hR'
  exact mem_PPADS.mpr ⟨hR, n, P, S, hn, hP, hS, hP_len, hS_len,
    hred.trans (.of_isTotalSearch (isTotalSearch_sinkOfLineRel hS_len) ComputableInPolyTime.id'
      (snd enc encBits) fun _ _ hw => endOfLineRel_of_sinkOfLineRel hw)⟩

/-- **`PPADS ⊆ PPP`** [Beame et al.][BeameEtAl1998]: the pigeonhole map `ppadToPppMap`, which
follows active outgoing edges and fixes every other vertex, reduces sink-of-line to pigeonhole. -/
theorem PPADS_subset_PPP : PPADS enc ⊆ PPP enc := by
  intro R hR'
  obtain ⟨hR, n, P, S, hn, hP, hS, -, hS_len, hred⟩ := mem_PPADS.mp hR'
  have hF : ComputableInPolyTime (ppadToPppMap n P S) (encPair enc encBits) encBits := by
    unfold ppadToPppMap
    fun_prop
  have hlen : PreservesWidth n (ppadToPppMap n P S) :=
    fun a _ hu => length_ppadToPppMap (hS_len a) hu
  refine mem_PPP.mpr ⟨hR, n, ppadToPppMap n P S, hn, hF, hlen, hred.trans ?_⟩
  refine .of_isTotalSearch (isTotalSearch_pigeonRel hlen) ComputableInPolyTime.id'
    (g := fun p => if !hasOut n P S p.1 (p.2.take (n p.1))
      then p.2.take (n p.1) else p.2.drop (n p.1)) ?_ fun a w hw => sinkOfLineRel_of_pigeonRel hw
  fun_prop

/-- **`PPAD ⊆ PPP`** [Papadimitriou][Papadimitriou1994PPAD], [Beame et al.][BeameEtAl1998]: every
problem in `PPAD` is in `PPP`, through `PPAD ⊆ PPADS ⊆ PPP`. -/
theorem PPAD_subset_PPP : PPAD enc ⊆ PPP enc :=
  fun _ h => PPADS_subset_PPP (PPAD_subset_PPADS h)

/-- `EndOfLine` is in `PPP`. -/
theorem EndOfLine_mem_PPP : EndOfLine ∈ PPP encEndOfLine :=
  PPAD_subset_PPP EndOfLine_mem_PPAD

end Cslib.Complexity
