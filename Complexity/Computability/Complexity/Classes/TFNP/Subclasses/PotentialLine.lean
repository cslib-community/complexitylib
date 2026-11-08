/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.TFNP.Subclasses.PPADS
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.Nat.Size

/-!
# The potential-line subclasses `EOPL` and `SOPL`

`EOPL` [Fearnley, Gordon, Mehta and Savani][FearnleyGordonMehtaSavani2020] is the class of total
search problems reducible to *End-of-Potential-Line*: a directed graph of in-degree and out-degree
at most `1`, presented by predecessor and successor maps `P, S`, carries a potential `V` that
strictly increases along every edge, and one must find a sink or a proper source other than the
distinguished source `0 ^ n`. `SOPL` [Göös et al.][GoosEtAl2022] is its sink-only variant,
*Sink-of-Potential-Line*.

## Presentation

We present an instance by maps `P, S : α × List Bool → List Bool` and a potential
`V : α × List Bool → ℕ` (computed in binary), and **prune** every edge along which the potential
does not strictly increase: `hasPotentialOut` and `hasPotentialIn` are the active-edge predicates
`hasOut`, `hasIn` of `PPAD` restricted to strict potential increase. The pruned graph is again an
end-of-line graph, presented by `potentialPred` and `potentialSucc`
(`hasOut_potential`, `hasIn_potential`), and potentials strictly increase along all its edges, so it
is a disjoint union of directed paths and isolated vertices, as in the structural definition of
[Göös et al., Section 1][GoosEtAl2022]. The solutions of
`endOfPotentialLineRel` (resp. `sinkOfPotentialLineRel`) are its ends (resp. sinks), with the same
convention at `0 ^ n` as `endOfLineRel`.

## Correspondence with the circuit definition of Fearnley et al.

[Fearnley, Gordon, Mehta and Savani, Definition 9][FearnleyGordonMehtaSavani2020] instead keeps the
raw maps and asks for a solution of type

* (R1) `x` with `S (P x) ≠ x ≠ 0 ^ n`, or with `P (S x) ≠ x`; or
* (R2) `x` with `x ≠ S x`, `P (S x) = x` and `V (S x) ≤ V x`,

under the syntactic promise `P (0 ^ n) = 0 ^ n ≠ S (0 ^ n)` (`LineSourcePromise`). The relation
`endOfPotentialLineViolationRel` is this definition, made total by also accepting `0 ^ n` when the
promise fails; `sinkOfPotentialLineViolationRel` drops the start-of-line clause
`S (P x) ≠ x ≠ 0 ^ n` of (R1). The two presentations define the same class:

* every violation of the pruned instance `(potentialPred, potentialSucc, V)` is an end (resp. sink)
  of the original potential line, at the same vertex
  (`endOfPotentialLineRel_of_violation`, `sinkOfPotentialLineRel_of_violation`);
* every end (resp. sink) `u` of the potential line yields the violation `potentialLineBack (a, u)`
  of the raw instance: `u` itself, its predecessor `P u` when the edge into `u` fails to increase
  the potential, or `0 ^ n` when the promise fails
  (`endOfPotentialLineViolationRel_potentialLineBack`,
  `sinkOfPotentialLineViolationRel_potentialLineBack`).

Hence `mem_EOPL_iff_violation` and `mem_SOPL_iff_violation`: a problem lies in `EOPL` (resp. `SOPL`)
iff it search-reduces to the violation relation of some uniform polynomial-time family. The
potential range `{0, …, 2 ^ m - 1}` of Definition 9 corresponds to the polynomial bit-length of the
binary output of `V` (`exists_potentialBound`).

Two syntactic conditions of Definition 9 are not imposed, exactly as `endOfLineRel` does not impose
the promise of End-of-Line: an instance violating `LineSourcePromise` has the extra solution
`0 ^ n`, and the normalization `V (0 ^ n) = 0`, which does not occur in (R1) or (R2), is omitted.
This does not change the class (informal argument, not formalized here): the instance on `n + 1`
bits with `S' (0 ^ (n + 1)) = 1 0 ^ n`, `P' (0 ^ (n + 1)) = 0 ^ (n + 1)`, `V' (0 ^ (n + 1)) = 0`,
with `S' (1 u) = 1 (potentialSucc u)`, `P' (1 u) = 1 (potentialPred u)` (except
`P' (1 0 ^ n) = 0 ^ (n + 1)`) and `V' (1 u) = V u + 1`, and with every other string isolated
satisfies both conditions, and its (R1)/(R2) solutions are exactly the strings `1 u` with `u` an end
(resp., without the start-of-line clause, a sink) of the original potential line.

## Main definitions

* `Cslib.Complexity.hasPotentialOut`, `Cslib.Complexity.hasPotentialIn`: potential-increasing active
  edges.
* `Cslib.Complexity.potentialSucc`, `Cslib.Complexity.potentialPred`: the pruned successor and
  predecessor maps.
* `Cslib.Complexity.endOfPotentialLineRel`, `Cslib.Complexity.sinkOfPotentialLineRel`.
* `Cslib.Complexity.endOfPotentialLineViolationRel`,
  `Cslib.Complexity.sinkOfPotentialLineViolationRel`: the circuit-style solution types.
* `Cslib.Complexity.EOPL`, `Cslib.Complexity.SOPL`.

## Main results

* `Cslib.Complexity.endOfPotentialLineRel_eq`, `Cslib.Complexity.sinkOfPotentialLineRel_eq`: the
  potential-line relations are the end-of-line and sink-of-line relations of the pruned maps.
* `Cslib.Complexity.mem_EOPL_iff_violation`, `Cslib.Complexity.mem_SOPL_iff_violation`.
* `Cslib.Complexity.EOPL_subset_SOPL`, `Cslib.Complexity.SOPL_subset_PPADS`,
  `Cslib.Complexity.EOPL_subset_PPAD`, `Cslib.Complexity.SOPL_subset_PLS`,
  `Cslib.Complexity.EOPL_subset_PLS`: `EOPL ⊆ SOPL ⊆ PLS ∩ PPADS` and `EOPL ⊆ PLS ∩ PPAD`
  [FearnleyGordonMehtaSavani2020], [GoosEtAl2022].

## References

* [J. Fearnley, S. Gordon, R. Mehta, R. Savani, *Unique End of Potential
  Line*][FearnleyGordonMehtaSavani2020]
* [M. Göös, A. Hollender, S. Jain, G. Maystre, W. Pires, R. Robere, R. Tao, *Further Collapses in
  TFNP*][GoosEtAl2022]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α β : Type}

/-! ### Potential-increasing active edges -/

/-- Vertex `u` has an active outgoing edge `u → S (a, u)` (`hasOut`) along which the potential
strictly increases. -/
def hasPotentialOut (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ) (a : α)
    (u : List Bool) : Bool :=
  hasOut n P S a u && decide (V (a, u) < V (a, S (a, u)))

/-- Vertex `u` has an active incoming edge `P (a, u) → u` (`hasIn`) along which the potential
strictly increases. -/
def hasPotentialIn (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ) (a : α)
    (u : List Bool) : Bool :=
  hasIn n P S a u && decide (V (a, P (a, u)) < V (a, u))

variable {n : α → ℕ} {P S : α × List Bool → List Bool} {V : α × List Bool → ℕ} {a : α}
  {u : List Bool}

theorem hasPotentialOut_eq_true_iff :
    hasPotentialOut n P S V a u = true ↔ P (a, S (a, u)) = u ∧ S (a, u) ≠ u ∧
      S (a, u) ≠ zeroVertex (n a) ∧ V (a, u) < V (a, S (a, u)) := by
  simp [hasPotentialOut, hasOut, and_assoc]

theorem hasPotentialIn_eq_true_iff :
    hasPotentialIn n P S V a u = true ↔ S (a, P (a, u)) = u ∧ P (a, u) ≠ u ∧
      u ≠ zeroVertex (n a) ∧ V (a, P (a, u)) < V (a, u) := by
  simp [hasPotentialIn, hasIn, and_assoc]

/-- A potential-increasing edge `u → S (a, u)` is the potential-increasing edge into `S (a, u)`. -/
theorem hasPotentialIn_of_hasPotentialOut (h : hasPotentialOut n P S V a u = true) :
    hasPotentialIn n P S V a (S (a, u)) = true := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hasPotentialOut_eq_true_iff.mp h
  exact hasPotentialIn_eq_true_iff.mpr ⟨by rw [h₁], by rw [h₁]; exact h₂.symm, h₃, by rwa [h₁]⟩

/-- A potential-increasing edge `P (a, u) → u` is the potential-increasing edge out of
`P (a, u)`. -/
theorem hasPotentialOut_of_hasPotentialIn (h : hasPotentialIn n P S V a u = true) :
    hasPotentialOut n P S V a (P (a, u)) = true := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hasPotentialIn_eq_true_iff.mp h
  exact hasPotentialOut_eq_true_iff.mpr
    ⟨by rw [h₁], by rw [h₁]; exact h₂.symm, by rw [h₁]; exact h₃, by rwa [h₁]⟩

@[simp]
theorem hasPotentialIn_zeroVertex (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) : hasPotentialIn n P S V a (zeroVertex (n a)) = false := by
  simp [hasPotentialIn]

/-! ### The pruned maps -/

/-- The pruned successor map: follow `S` only along potential-increasing active edges. -/
def potentialSucc (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ)
    (p : α × List Bool) : List Bool :=
  if hasPotentialOut n P S V p.1 p.2 then S p else p.2

/-- The pruned predecessor map: follow `P` only along potential-increasing active edges. -/
def potentialPred (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ)
    (p : α × List Bool) : List Bool :=
  if hasPotentialIn n P S V p.1 p.2 then P p else p.2

theorem potentialSucc_of_true (h : hasPotentialOut n P S V a u = true) :
    potentialSucc n P S V (a, u) = S (a, u) := by
  simp [potentialSucc, h]

theorem potentialSucc_of_false (h : hasPotentialOut n P S V a u = false) :
    potentialSucc n P S V (a, u) = u := by
  simp [potentialSucc, h]

theorem potentialPred_of_true (h : hasPotentialIn n P S V a u = true) :
    potentialPred n P S V (a, u) = P (a, u) := by
  simp [potentialPred, h]

theorem potentialPred_of_false (h : hasPotentialIn n P S V a u = false) :
    potentialPred n P S V (a, u) = u := by
  simp [potentialPred, h]

theorem length_potentialSucc (hS : ∀ u, u.length = n a → (S (a, u)).length = n a)
    (hu : u.length = n a) : (potentialSucc n P S V (a, u)).length = n a := by
  unfold potentialSucc
  split_ifs
  · exact hS u hu
  · exact hu

theorem length_potentialPred (hP : ∀ u, u.length = n a → (P (a, u)).length = n a)
    (hu : u.length = n a) : (potentialPred n P S V (a, u)).length = n a := by
  unfold potentialPred
  split_ifs
  · exact hP u hu
  · exact hu

/-- The active outgoing edges of the pruned maps are the potential-increasing active outgoing edges
of the original maps. -/
theorem hasOut_potential :
    hasOut n (potentialPred n P S V) (potentialSucc n P S V) a u = hasPotentialOut n P S V a u := by
  cases h : hasPotentialOut n P S V a u
  · simp [hasOut, potentialSucc_of_false h]
  · have hin := hasPotentialIn_of_hasPotentialOut h
    obtain ⟨h₁, h₂, h₃, -⟩ := hasPotentialOut_eq_true_iff.mp h
    simp only [hasOut, potentialSucc_of_true h, potentialPred_of_true hin, decide_eq_true_eq]
    exact ⟨h₁, h₂, h₃⟩

/-- The active incoming edges of the pruned maps are the potential-increasing active incoming edges
of the original maps. -/
theorem hasIn_potential :
    hasIn n (potentialPred n P S V) (potentialSucc n P S V) a u = hasPotentialIn n P S V a u := by
  cases h : hasPotentialIn n P S V a u
  · simp [hasIn, potentialPred_of_false h]
  · have hout := hasPotentialOut_of_hasPotentialIn h
    obtain ⟨h₁, h₂, h₃, -⟩ := hasPotentialIn_eq_true_iff.mp h
    simp only [hasIn, potentialPred_of_true h, potentialSucc_of_true hout, decide_eq_true_eq]
    exact ⟨h₁, h₂, h₃⟩

/-! ### End and sink of a potential line -/

/-- The search relation of an end-of-potential-line family (`EOPL`): a vertex `u` of length `n a`
is a solution if its potential-increasing incoming/outgoing parity is unbalanced relative to
`0 ^ (n a)`: either `u = 0 ^ (n a)` lacks a potential-increasing outgoing edge, or `u ≠ 0 ^ (n a)`
is a sink or a proper source of the pruned graph. -/
def endOfPotentialLineRel (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ)
    (a : α) (u : List Bool) : Prop :=
  u.length = n a ∧
    ((hasPotentialIn n P S V a u != hasPotentialOut n P S V a u) ==
      decide (u ≠ zeroVertex (n a))) = true

/-- The search relation of a sink-of-potential-line family (`SOPL`): a vertex `u` of length `n a` is
a solution if it has no potential-increasing outgoing edge and is either `0 ^ (n a)` or has a
potential-increasing incoming edge. -/
def sinkOfPotentialLineRel (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ)
    (a : α) (u : List Bool) : Prop :=
  u.length = n a ∧ hasPotentialOut n P S V a u = false ∧
    (u = zeroVertex (n a) ∨ hasPotentialIn n P S V a u = true)

/-- `endOfPotentialLineRel` is `endOfLineRel` for the pruned maps. -/
theorem endOfPotentialLineRel_eq (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) :
    endOfPotentialLineRel n P S V =
      endOfLineRel n (potentialPred n P S V) (potentialSucc n P S V) := by
  funext a u
  simp only [endOfPotentialLineRel, endOfLineRel, hasOut_potential, hasIn_potential]

/-- `sinkOfPotentialLineRel` is `sinkOfLineRel` for the pruned maps. -/
theorem sinkOfPotentialLineRel_eq (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) :
    sinkOfPotentialLineRel n P S V =
      sinkOfLineRel n (potentialPred n P S V) (potentialSucc n P S V) := by
  funext a u
  simp only [sinkOfPotentialLineRel, sinkOfLineRel, hasOut_potential, hasIn_potential]

/-- An end of a potential line is either a sink (`sinkOfPotentialLineRel`) or a proper source of the
pruned graph. -/
theorem endOfPotentialLineRel_iff :
    endOfPotentialLineRel n P S V a u ↔ sinkOfPotentialLineRel n P S V a u ∨
      (u.length = n a ∧ u ≠ zeroVertex (n a) ∧ hasPotentialIn n P S V a u = false ∧
        hasPotentialOut n P S V a u = true) := by
  by_cases hu : u = zeroVertex (n a)
  · subst hu
    cases hout : hasPotentialOut n P S V a (zeroVertex (n a)) <;>
      simp [endOfPotentialLineRel, sinkOfPotentialLineRel, hout]
  · cases hin : hasPotentialIn n P S V a u <;> cases hout : hasPotentialOut n P S V a u <;>
      simp [endOfPotentialLineRel, sinkOfPotentialLineRel, hu, hin, hout]

/-- Every sink of a potential line is an end of it. -/
theorem endOfPotentialLineRel_of_sinkOfPotentialLineRel (h : sinkOfPotentialLineRel n P S V a u) :
    endOfPotentialLineRel n P S V a u :=
  endOfPotentialLineRel_iff.mpr (.inl h)

/-- `endOfPotentialLineRel` is total whenever the successor map preserves the vertex bit-length. -/
theorem isTotalSearch_endOfPotentialLineRel (hS : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    IsTotalSearch (endOfPotentialLineRel n P S V) := by
  rw [endOfPotentialLineRel_eq]
  exact isTotalSearch_endOfLineRel fun a u hu => length_potentialSucc (hS a) hu

/-- `sinkOfPotentialLineRel` is total whenever the successor map preserves the vertex
bit-length. -/
theorem isTotalSearch_sinkOfPotentialLineRel
    (hS : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    IsTotalSearch (sinkOfPotentialLineRel n P S V) := by
  rw [sinkOfPotentialLineRel_eq]
  exact isTotalSearch_sinkOfLineRel fun a u hu => length_potentialSucc (hS a) hu

/-! ### The circuit-style solution types of Fearnley et al. -/

/-- The syntactic promise of [Fearnley et al., Definition 9][FearnleyGordonMehtaSavani2020]:
`P (0 ^ n) = 0 ^ n ≠ S (0 ^ n)`. -/
def LineSourcePromise (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α) : Prop :=
  P (a, zeroVertex (n a)) = zeroVertex (n a) ∧ S (a, zeroVertex (n a)) ≠ zeroVertex (n a)

/-- The solutions of *End-of-Potential-Line* in the form of [Fearnley et al.,
Definition 9][FearnleyGordonMehtaSavani2020], made total by also accepting `0 ^ (n a)` when the
promise `LineSourcePromise` fails: a vertex `x` of length `n a` with

* (R1) `S (P x) ≠ x ≠ 0 ^ (n a)` or `P (S x) ≠ x`; or
* (R2) `x ≠ S x`, `P (S x) = x` and `V (S x) ≤ V x`. -/
def endOfPotentialLineViolationRel (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) (x : List Bool) : Prop :=
  x.length = n a ∧
    ((x = zeroVertex (n a) ∧ ¬LineSourcePromise n P S a) ∨
      (S (a, P (a, x)) ≠ x ∧ x ≠ zeroVertex (n a)) ∨ P (a, S (a, x)) ≠ x ∨
      (x ≠ S (a, x) ∧ P (a, S (a, x)) = x ∧ V (a, S (a, x)) ≤ V (a, x)))

/-- The solutions of *Sink-of-Potential-Line* in circuit form: those of
`endOfPotentialLineViolationRel` without the start-of-line clause `S (P x) ≠ x ≠ 0 ^ (n a)`. -/
def sinkOfPotentialLineViolationRel (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) (x : List Bool) : Prop :=
  x.length = n a ∧
    ((x = zeroVertex (n a) ∧ ¬LineSourcePromise n P S a) ∨ P (a, S (a, x)) ≠ x ∨
      (x ≠ S (a, x) ∧ P (a, S (a, x)) = x ∧ V (a, S (a, x)) ≤ V (a, x)))

/-- The pruned maps satisfy the promise exactly when `0 ^ (n a)` has a potential-increasing outgoing
edge. -/
theorem lineSourcePromise_potential_iff :
    LineSourcePromise n (potentialPred n P S V) (potentialSucc n P S V) a ↔
      hasPotentialOut n P S V a (zeroVertex (n a)) = true := by
  rw [LineSourcePromise, potentialPred_of_false (hasPotentialIn_zeroVertex n P S V a)]
  cases h : hasPotentialOut n P S V a (zeroVertex (n a))
  · simp [potentialSucc_of_false h]
  · simpa [potentialSucc_of_true h] using (hasPotentialOut_eq_true_iff.mp h).2.2.1

/-- **Pruned violations are ends.** Every circuit-style violation of the pruned instance is an end
of the potential line, at the same vertex. -/
theorem endOfPotentialLineRel_of_violation {x : List Bool}
    (h : endOfPotentialLineViolationRel n (potentialPred n P S V) (potentialSucc n P S V) V a x) :
    endOfPotentialLineRel n P S V a x := by
  obtain ⟨hlen, h⟩ := h
  refine ⟨hlen, ?_⟩
  by_cases hx : x = zeroVertex (n a)
  · subst hx
    rw [lineSourcePromise_potential_iff] at h
    cases hout : hasPotentialOut n P S V a (zeroVertex (n a))
    · simp
    · exfalso
      have hin := hasPotentialIn_of_hasPotentialOut hout
      rw [potentialPred_of_false (hasPotentialIn_zeroVertex n P S V a),
        potentialSucc_of_true hout, potentialPred_of_true hin] at h
      obtain ⟨-, -, hS0, hV⟩ := hasPotentialOut_eq_true_iff.mp hout
      simp only [hout, not_true_eq_false, and_false, ne_eq, not_true_eq_false, false_or] at h
      rcases h with h | h
      · exact h (hasPotentialOut_eq_true_iff.mp hout).1
      · exact absurd h.2.2 (Nat.not_le.mpr hV)
  · cases hin : hasPotentialIn n P S V a x <;> cases hout : hasPotentialOut n P S V a x
    · exfalso
      simp only [potentialPred_of_false hin, potentialSucc_of_false hout] at h
      simp [hx] at h
    · simp [hx]
    · simp [hx]
    · exfalso
      have hin' := hasPotentialIn_of_hasPotentialOut hout
      have hout' := hasPotentialOut_of_hasPotentialIn hin
      rw [potentialPred_of_true hin, potentialSucc_of_true hout, potentialSucc_of_true hout',
        potentialPred_of_true hin'] at h
      obtain ⟨hPS, hSx, -, hV⟩ := hasPotentialOut_eq_true_iff.mp hout
      obtain ⟨hSP, -, -, -⟩ := hasPotentialIn_eq_true_iff.mp hin
      rcases h with h | h | h | h
      · exact hx h.1
      · exact h.1 hSP
      · exact h hPS
      · exact absurd h.2.2 (Nat.not_le.mpr hV)

/-- **Pruned violations are sinks.** Every circuit-style sink violation of the pruned instance is a
sink of the potential line, at the same vertex. -/
theorem sinkOfPotentialLineRel_of_violation {x : List Bool}
    (h : sinkOfPotentialLineViolationRel n (potentialPred n P S V) (potentialSucc n P S V) V a x) :
    sinkOfPotentialLineRel n P S V a x := by
  obtain ⟨hlen, h⟩ := h
  have hend : endOfPotentialLineRel n P S V a x := by
    refine endOfPotentialLineRel_of_violation ⟨hlen, ?_⟩
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h))
  rcases endOfPotentialLineRel_iff.mp hend with h' | ⟨-, hx, hin, hout⟩
  · exact h'
  · exfalso
    have hout' := hout
    obtain ⟨hPS, hSx, hS0, hV⟩ := hasPotentialOut_eq_true_iff.mp hout
    rw [potentialSucc_of_true hout',
      potentialPred_of_true (hasPotentialIn_of_hasPotentialOut hout'), hPS] at h
    rcases h with h | h | h
    · exact hx h.1
    · exact h rfl
    · exact absurd h.2.2 (Nat.not_le.mpr hV)

/-- The back-map from ends of a potential line to circuit-style violations: `0 ^ (n a)` if the
promise `LineSourcePromise` fails; otherwise the predecessor `P (a, u)` if `u` has an active
incoming edge (`hasIn`) along which the potential does not increase; otherwise `u` itself. -/
def potentialLineBack (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ)
    (p : α × List Bool) : List Bool :=
  if decide (P (p.1, zeroVertex (n p.1)) = zeroVertex (n p.1)) &&
      decide (S (p.1, zeroVertex (n p.1)) ≠ zeroVertex (n p.1)) then
    if hasIn n P S p.1 p.2 && decide (V (p.1, p.2) ≤ V (p.1, P p)) then P p else p.2
  else zeroVertex (n p.1)

theorem potentialLineBack_of_promise (h : LineSourcePromise n P S a) :
    potentialLineBack n P S V (a, u) =
      if hasIn n P S a u && decide (V (a, u) ≤ V (a, P (a, u))) then P (a, u) else u := by
  simp [potentialLineBack, h.1, h.2]

theorem potentialLineBack_of_not_promise (h : ¬LineSourcePromise n P S a) :
    potentialLineBack n P S V (a, u) = zeroVertex (n a) := by
  have h' : ¬(P (a, zeroVertex (n a)) = zeroVertex (n a) ∧
      S (a, zeroVertex (n a)) ≠ zeroVertex (n a)) := h
  simp only [potentialLineBack, Bool.and_eq_true, decide_eq_true_eq]
  rw [ite_eq_right h']

/-- Under the promise, a sink of the potential line is fixed by `potentialLineBack`. -/
private theorem potentialLineBack_eq_self (h : LineSourcePromise n P S a)
    (hu : u = zeroVertex (n a) ∨ hasPotentialIn n P S V a u = true) :
    potentialLineBack n P S V (a, u) = u := by
  rw [potentialLineBack_of_promise h, ite_eq_right]
  rcases hu with rfl | hu
  · simp
  · obtain ⟨-, -, -, hV⟩ := hasPotentialIn_eq_true_iff.mp hu
    simp [Nat.not_le.mpr hV]

/-- Under the promise, a sink of the potential line has no consistent potential-increasing outgoing
edge in the raw instance: it is an (R1) end-of-line violation or an (R2) potential violation. -/
private theorem sinkViolation_of_sinkOfPotentialLineRel (hprom : LineSourcePromise n P S a)
    (h : sinkOfPotentialLineRel n P S V a u) :
    P (a, S (a, u)) ≠ u ∨ (u ≠ S (a, u) ∧ P (a, S (a, u)) = u ∧ V (a, S (a, u)) ≤ V (a, u)) := by
  obtain ⟨-, hout, hu⟩ := h
  obtain ⟨hP0, hS0⟩ := hprom
  by_cases hPS : P (a, S (a, u)) = u
  · right
    have hSu : S (a, u) ≠ u := by
      intro hSu
      rcases hu with rfl | hin
      · exact hS0 hSu
      · obtain ⟨-, hPu, -, -⟩ := hasPotentialIn_eq_true_iff.mp hin
        rw [hSu] at hPS
        exact hPu hPS
    have hSz : S (a, u) ≠ zeroVertex (n a) := by
      intro hSz
      rw [hSz, hP0] at hPS
      rcases hu with rfl | hin
      · exact hS0 (hSz.trans hPS)
      · obtain ⟨-, -, hu0, -⟩ := hasPotentialIn_eq_true_iff.mp hin
        exact hu0 hPS.symm
    refine ⟨Ne.symm hSu, hPS, ?_⟩
    by_contra hV
    rw [Nat.not_le] at hV
    have : hasPotentialOut n P S V a u = true :=
      hasPotentialOut_eq_true_iff.mpr ⟨hPS, hSu, hSz, hV⟩
    rw [hout] at this
    exact Bool.false_ne_true this
  · exact .inl hPS

/-- **Sinks yield circuit-style sink violations.** -/
theorem sinkOfPotentialLineViolationRel_potentialLineBack
    (h : sinkOfPotentialLineRel n P S V a u) :
    sinkOfPotentialLineViolationRel n P S V a (potentialLineBack n P S V (a, u)) := by
  by_cases hprom : LineSourcePromise n P S a
  · rw [potentialLineBack_eq_self hprom h.2.2]
    exact ⟨h.1, .inr (sinkViolation_of_sinkOfPotentialLineRel hprom h)⟩
  · rw [potentialLineBack_of_not_promise hprom]
    exact ⟨length_zeroVertex _, .inl ⟨rfl, hprom⟩⟩

/-- Under the promise, a proper source `u` of the pruned graph yields a circuit-style violation at
`potentialLineBack (a, u)`: a start-of-line (R1) violation at `u`, or a potential (R2) violation at
its predecessor. -/
private theorem violation_of_properSource (hprom : LineSourcePromise n P S a)
    (hP : ∀ u, u.length = n a → (P (a, u)).length = n a) (hlen : u.length = n a)
    (hu : u ≠ zeroVertex (n a)) (hin : hasPotentialIn n P S V a u = false)
    (hout : hasPotentialOut n P S V a u = true) :
    endOfPotentialLineViolationRel n P S V a (potentialLineBack n P S V (a, u)) := by
  obtain ⟨hPS, hSu, -, -⟩ := hasPotentialOut_eq_true_iff.mp hout
  rw [potentialLineBack_of_promise hprom]
  split_ifs with hc
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hin', hV⟩ := hc
    simp only [hasIn, decide_eq_true_eq] at hin'
    obtain ⟨hSP, hPu, -⟩ := hin'
    refine ⟨hP u hlen, .inr (.inr (.inr ⟨?_, ?_, ?_⟩))⟩ <;> rw [hSP]
    · exact hPu
    · exact hV
  · refine ⟨hlen, .inr (.inl ⟨?_, hu⟩)⟩
    intro hSP
    by_cases hPu : P (a, u) = u
    · rw [hPu] at hSP
      exact hSu hSP
    · have hin' : hasIn n P S a u = true := by
        simp only [hasIn, decide_eq_true_eq]
        exact ⟨hSP, hPu, hu⟩
      have hV : V (a, P (a, u)) < V (a, u) := by
        simp only [hin', Bool.true_and, decide_eq_true_eq, Nat.not_le] at hc
        exact hc
      have : hasPotentialIn n P S V a u = true := by
        simp [hasPotentialIn, hin', hV]
      rw [hin] at this
      exact Bool.false_ne_true this

/-- **Ends yield circuit-style violations.** Every end `u` of the potential line yields the
circuit-style violation `potentialLineBack (a, u)` of the raw instance. -/
theorem endOfPotentialLineViolationRel_potentialLineBack
    (hP : ∀ u, u.length = n a → (P (a, u)).length = n a)
    (h : endOfPotentialLineRel n P S V a u) :
    endOfPotentialLineViolationRel n P S V a (potentialLineBack n P S V (a, u)) := by
  by_cases hprom : LineSourcePromise n P S a
  · rcases endOfPotentialLineRel_iff.mp h with h | ⟨hlen, hu, hin, hout⟩
    · rw [potentialLineBack_eq_self hprom h.2.2]
      rcases sinkViolation_of_sinkOfPotentialLineRel hprom h with h' | h'
      · exact ⟨h.1, .inr (.inr (.inl h'))⟩
      · exact ⟨h.1, .inr (.inr (.inr h'))⟩
    · exact violation_of_properSource hprom hP hlen hu hin hout
  · rw [potentialLineBack_of_not_promise hprom]
    exact ⟨length_zeroVertex _, .inl ⟨rfl, hprom⟩⟩

/-! ### Polynomial-time computability -/

attribute [local fun_prop] ComputableInPolyTime.bool_and' ComputableInPolyTime.binary_le'

@[fun_prop]
theorem computableInPolyTime_hasPotentialOut {enc : α ↪ List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (fun x : α × List Bool => hasPotentialOut n P S V x.1 x.2)
      (encPair enc encBits) encBool := by
  unfold hasPotentialOut
  fun_prop

@[fun_prop]
theorem computableInPolyTime_hasPotentialIn {enc : α ↪ List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (fun x : α × List Bool => hasPotentialIn n P S V x.1 x.2)
      (encPair enc encBits) encBool := by
  unfold hasPotentialIn
  fun_prop

theorem computableInPolyTime_potentialSucc {enc : α ↪ List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (potentialSucc n P S V) (encPair enc encBits) encBits := by
  unfold potentialSucc
  fun_prop

theorem computableInPolyTime_potentialPred {enc : α ↪ List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (potentialPred n P S V) (encPair enc encBits) encBits := by
  unfold potentialPred
  fun_prop

theorem computableInPolyTime_potentialLineBack {enc : α ↪ List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (potentialLineBack n P S V) (encPair enc encBits) encBits := by
  unfold potentialLineBack
  fun_prop

/-! ### `FNP` and `TFNP` membership -/

/-- A polynomial-time end-of-potential-line family defines an `FNP` relation. -/
theorem endOfPotentialLineRel_mem_FNP {enc : α ↪ List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    endOfPotentialLineRel n P S V ∈ FNP enc := by
  rw [endOfPotentialLineRel_eq]
  exact endOfLineRel_mem_FNP hn (computableInPolyTime_potentialPred hn hP hS hV)
    (computableInPolyTime_potentialSucc hn hP hS hV)

/-- A polynomial-time sink-of-potential-line family defines an `FNP` relation. -/
theorem sinkOfPotentialLineRel_mem_FNP {enc : α ↪ List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    sinkOfPotentialLineRel n P S V ∈ FNP enc := by
  rw [sinkOfPotentialLineRel_eq]
  exact sinkOfLineRel_mem_FNP hn (computableInPolyTime_potentialPred hn hP hS hV)
    (computableInPolyTime_potentialSucc hn hP hS hV)

/-- A polynomial-time family defines an `FNP` circuit-style end-of-potential-line relation. -/
theorem endOfPotentialLineViolationRel_mem_FNP {enc : α ↪ List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    endOfPotentialLineViolationRel n P S V ∈ FNP enc := by
  obtain ⟨p, hp⟩ := (polyBounded hn).exists_polynomial
  refine ⟨⟨p, fun a u h => h.1 ▸ hp a⟩,
    fun x => decide (x.2.length = n x.1 ∧
      ((x.2 = zeroVertex (n x.1) ∧ (P (x.1, zeroVertex (n x.1)) ≠ zeroVertex (n x.1) ∨
          S (x.1, zeroVertex (n x.1)) = zeroVertex (n x.1))) ∨
        (S (x.1, P x) ≠ x.2 ∧ x.2 ≠ zeroVertex (n x.1)) ∨ P (x.1, S x) ≠ x.2 ∨
        (x.2 ≠ S x ∧ P (x.1, S x) = x.2 ∧ V (x.1, S x) ≤ V x))), ?_, fun a u => ?_⟩
  · fun_prop
  · simp [endOfPotentialLineViolationRel, LineSourcePromise, imp_iff_not_or]

/-- A polynomial-time family defines an `FNP` circuit-style sink-of-potential-line relation. -/
theorem sinkOfPotentialLineViolationRel_mem_FNP {enc : α ↪ List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    sinkOfPotentialLineViolationRel n P S V ∈ FNP enc := by
  obtain ⟨p, hp⟩ := (polyBounded hn).exists_polynomial
  refine ⟨⟨p, fun a u h => h.1 ▸ hp a⟩,
    fun x => decide (x.2.length = n x.1 ∧
      ((x.2 = zeroVertex (n x.1) ∧ (P (x.1, zeroVertex (n x.1)) ≠ zeroVertex (n x.1) ∨
          S (x.1, zeroVertex (n x.1)) = zeroVertex (n x.1))) ∨ P (x.1, S x) ≠ x.2 ∨
        (x.2 ≠ S x ∧ P (x.1, S x) = x.2 ∧ V (x.1, S x) ≤ V x))), ?_, fun a u => ?_⟩
  · fun_prop
  · simp [sinkOfPotentialLineViolationRel, LineSourcePromise, imp_iff_not_or]

/-! ### The classes `EOPL` and `SOPL` -/

/-- **End of Potential Line (`EOPL`)** [Fearnley, Gordon, Mehta and
Savani][FearnleyGordonMehtaSavani2020]: `FNP` search problems search-reducible to finding an end of
a uniform polynomial-time potential-line family `endOfPotentialLineRel n P S V`. -/
def EOPL (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | R ∈ FNP enc ∧ ∃ (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
    ComputableInPolyTime n enc encUnary ∧
    ComputableInPolyTime P (encPair enc encBits) encBits ∧
    ComputableInPolyTime S (encPair enc encBits) encBits ∧
    ComputableInPolyTime V (encPair enc encBits) encNat ∧
    (∀ a u, u.length = n a → (P (a, u)).length = n a) ∧
    (∀ a u, u.length = n a → (S (a, u)).length = n a) ∧
    SearchReducible enc enc R (endOfPotentialLineRel n P S V)}

/-- **Sink of Potential Line (`SOPL`)** [Göös et al.][GoosEtAl2022]: `FNP` search problems
search-reducible to finding a sink of a uniform polynomial-time potential-line family
`sinkOfPotentialLineRel n P S V`. -/
def SOPL (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | R ∈ FNP enc ∧ ∃ (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
    ComputableInPolyTime n enc encUnary ∧
    ComputableInPolyTime P (encPair enc encBits) encBits ∧
    ComputableInPolyTime S (encPair enc encBits) encBits ∧
    ComputableInPolyTime V (encPair enc encBits) encNat ∧
    (∀ a u, u.length = n a → (P (a, u)).length = n a) ∧
    (∀ a u, u.length = n a → (S (a, u)).length = n a) ∧
    SearchReducible enc enc R (sinkOfPotentialLineRel n P S V)}

variable {enc : α ↪ List Bool} {encB : β ↪ List Bool} {R : α → List Bool → Prop}
  {T : β → List Bool → Prop}

theorem mem_EOPL : R ∈ EOPL enc ↔ R ∈ FNP enc ∧
    ∃ (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
      ComputableInPolyTime n enc encUnary ∧
      ComputableInPolyTime P (encPair enc encBits) encBits ∧
      ComputableInPolyTime S (encPair enc encBits) encBits ∧
      ComputableInPolyTime V (encPair enc encBits) encNat ∧
      (∀ a u, u.length = n a → (P (a, u)).length = n a) ∧
      (∀ a u, u.length = n a → (S (a, u)).length = n a) ∧
      SearchReducible enc enc R (endOfPotentialLineRel n P S V) :=
  Iff.rfl

theorem mem_SOPL : R ∈ SOPL enc ↔ R ∈ FNP enc ∧
    ∃ (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
      ComputableInPolyTime n enc encUnary ∧
      ComputableInPolyTime P (encPair enc encBits) encBits ∧
      ComputableInPolyTime S (encPair enc encBits) encBits ∧
      ComputableInPolyTime V (encPair enc encBits) encNat ∧
      (∀ a u, u.length = n a → (P (a, u)).length = n a) ∧
      (∀ a u, u.length = n a → (S (a, u)).length = n a) ∧
      SearchReducible enc enc R (sinkOfPotentialLineRel n P S V) :=
  Iff.rfl

/-- Every uniform polynomial-time end-of-potential-line family is in `EOPL`. -/
theorem endOfPotentialLineRel_mem_EOPL
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat)
    (hP_len : ∀ a u, u.length = n a → (P (a, u)).length = n a)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    endOfPotentialLineRel n P S V ∈ EOPL enc :=
  mem_EOPL.mpr ⟨endOfPotentialLineRel_mem_FNP hn hP hS hV, n, P, S, V, hn, hP, hS, hV, hP_len,
    hS_len, .refl _ _⟩

/-- Every uniform polynomial-time sink-of-potential-line family is in `SOPL`. -/
theorem sinkOfPotentialLineRel_mem_SOPL
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat)
    (hP_len : ∀ a u, u.length = n a → (P (a, u)).length = n a)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    sinkOfPotentialLineRel n P S V ∈ SOPL enc :=
  mem_SOPL.mpr ⟨sinkOfPotentialLineRel_mem_FNP hn hP hS hV, n, P, S, V, hn, hP, hS, hV, hP_len,
    hS_len, .refl _ _⟩

/-- `EOPL` is closed under polynomial-time search reductions across arbitrary instance types. -/
theorem SearchReducible.mem_EOPL (h : SearchReducible enc encB R T) (hR : R ∈ FNP enc)
    (hT : T ∈ EOPL encB) : R ∈ EOPL enc := by
  obtain ⟨-, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hT_red⟩ := Complexity.mem_EOPL.mp hT
  obtain ⟨f, g, hf, hg, -, hsol⟩ := (h.trans hT_red)
  have hpair := (hf.comp (.fst enc encBits)).prod (.snd enc encBits)
  refine Complexity.mem_EOPL.mpr ⟨hR, n ∘ f, fun p => P (f p.1, p.2), fun p => S (f p.1, p.2),
    fun p => V (f p.1, p.2), hn.comp hf, hP.comp hpair, hS.comp hpair, hV.comp hpair,
    fun a u hu => hP_len (f a) u hu, fun a u hu => hS_len (f a) u hu,
    .of_isTotalSearch (isTotalSearch_endOfPotentialLineRel fun a u hu => hS_len (f a) u hu)
      ComputableInPolyTime.id' hg fun a w hw => hsol a w hw⟩

/-- `SOPL` is closed under polynomial-time search reductions across arbitrary instance types. -/
theorem SearchReducible.mem_SOPL (h : SearchReducible enc encB R T) (hR : R ∈ FNP enc)
    (hT : T ∈ SOPL encB) : R ∈ SOPL enc := by
  obtain ⟨-, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hT_red⟩ := Complexity.mem_SOPL.mp hT
  obtain ⟨f, g, hf, hg, -, hsol⟩ := (h.trans hT_red)
  have hpair := (hf.comp (.fst enc encBits)).prod (.snd enc encBits)
  refine Complexity.mem_SOPL.mpr ⟨hR, n ∘ f, fun p => P (f p.1, p.2), fun p => S (f p.1, p.2),
    fun p => V (f p.1, p.2), hn.comp hf, hP.comp hpair, hS.comp hpair, hV.comp hpair,
    fun a u hu => hP_len (f a) u hu, fun a u hu => hS_len (f a) u hu,
    .of_isTotalSearch (isTotalSearch_sinkOfPotentialLineRel fun a u hu => hS_len (f a) u hu)
      ComputableInPolyTime.id' hg fun a w hw => hsol a w hw⟩

/-! ### Equivalence with the circuit-style solution types -/

/-- **`EOPL` in the form of Fearnley et al.** A problem is in `EOPL` iff it is in `FNP` and
search-reduces to the circuit-style relation `endOfPotentialLineViolationRel` of [Fearnley et al.,
Definition 9][FearnleyGordonMehtaSavani2020] for some uniform polynomial-time family. -/
theorem mem_EOPL_iff_violation : R ∈ EOPL enc ↔ R ∈ FNP enc ∧
    ∃ (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
      ComputableInPolyTime n enc encUnary ∧
      ComputableInPolyTime P (encPair enc encBits) encBits ∧
      ComputableInPolyTime S (encPair enc encBits) encBits ∧
      ComputableInPolyTime V (encPair enc encBits) encNat ∧
      (∀ a u, u.length = n a → (P (a, u)).length = n a) ∧
      (∀ a u, u.length = n a → (S (a, u)).length = n a) ∧
      SearchReducible enc enc R (endOfPotentialLineViolationRel n P S V) := by
  constructor
  · rintro ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hred⟩
    have hP' := computableInPolyTime_potentialPred hn hP hS hV
    have hS' := computableInPolyTime_potentialSucc hn hP hS hV
    have hP'_len (a : α) (u : List Bool) (hu : u.length = n a) :
        (potentialPred n P S V (a, u)).length = n a := length_potentialPred (hP_len a) hu
    have hS'_len (a : α) (u : List Bool) (hu : u.length = n a) :
        (potentialSucc n P S V (a, u)).length = n a := length_potentialSucc (hS_len a) hu
    have htot : IsTotalSearch
        (endOfPotentialLineViolationRel n (potentialPred n P S V) (potentialSucc n P S V) V) :=
      fun a =>
        let ⟨u, hu⟩ := isTotalSearch_endOfPotentialLineRel (P := potentialPred n P S V) (V := V)
          hS'_len a
        ⟨_, endOfPotentialLineViolationRel_potentialLineBack (hP'_len a) hu⟩
    exact ⟨hR, n, potentialPred n P S V, potentialSucc n P S V, V, hn, hP', hS', hV, hP'_len,
      hS'_len, hred.trans (.of_isTotalSearch htot ComputableInPolyTime.id' (snd enc encBits)
        fun _ _ hw => endOfPotentialLineRel_of_violation hw)⟩
  · rintro ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hred⟩
    exact ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len,
      hred.trans (.of_isTotalSearch (isTotalSearch_endOfPotentialLineRel hS_len)
        ComputableInPolyTime.id' (computableInPolyTime_potentialLineBack hn hP hS hV)
        fun a _ hw => endOfPotentialLineViolationRel_potentialLineBack (hP_len a) hw)⟩

/-- **`SOPL` in circuit form.** A problem is in `SOPL` iff it is in `FNP` and search-reduces to the
circuit-style relation `sinkOfPotentialLineViolationRel` for some uniform polynomial-time
family. -/
theorem mem_SOPL_iff_violation : R ∈ SOPL enc ↔ R ∈ FNP enc ∧
    ∃ (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
      ComputableInPolyTime n enc encUnary ∧
      ComputableInPolyTime P (encPair enc encBits) encBits ∧
      ComputableInPolyTime S (encPair enc encBits) encBits ∧
      ComputableInPolyTime V (encPair enc encBits) encNat ∧
      (∀ a u, u.length = n a → (P (a, u)).length = n a) ∧
      (∀ a u, u.length = n a → (S (a, u)).length = n a) ∧
      SearchReducible enc enc R (sinkOfPotentialLineViolationRel n P S V) := by
  constructor
  · rintro ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hred⟩
    have hP' := computableInPolyTime_potentialPred hn hP hS hV
    have hS' := computableInPolyTime_potentialSucc hn hP hS hV
    have hP'_len (a : α) (u : List Bool) (hu : u.length = n a) :
        (potentialPred n P S V (a, u)).length = n a := length_potentialPred (hP_len a) hu
    have hS'_len (a : α) (u : List Bool) (hu : u.length = n a) :
        (potentialSucc n P S V (a, u)).length = n a := length_potentialSucc (hS_len a) hu
    have htot : IsTotalSearch
        (sinkOfPotentialLineViolationRel n (potentialPred n P S V) (potentialSucc n P S V) V) :=
      fun a =>
        let ⟨u, hu⟩ := isTotalSearch_sinkOfPotentialLineRel (P := potentialPred n P S V) (V := V)
          hS'_len a
        ⟨_, sinkOfPotentialLineViolationRel_potentialLineBack hu⟩
    exact ⟨hR, n, potentialPred n P S V, potentialSucc n P S V, V, hn, hP', hS', hV, hP'_len,
      hS'_len, hred.trans (.of_isTotalSearch htot ComputableInPolyTime.id' (snd enc encBits)
        fun _ _ hw => sinkOfPotentialLineRel_of_violation hw)⟩
  · rintro ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hred⟩
    exact ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len,
      hred.trans (.of_isTotalSearch (isTotalSearch_sinkOfPotentialLineRel hS_len)
        ComputableInPolyTime.id' (computableInPolyTime_potentialLineBack hn hP hS hV)
        fun _ _ hw => sinkOfPotentialLineViolationRel_potentialLineBack hw)⟩

/-- **End-of-Potential-Line in the form of Fearnley et al. is in `EOPL`**: the circuit-style
relation of [Fearnley et al., Definition 9][FearnleyGordonMehtaSavani2020] for any uniform
polynomial-time family lies in `EOPL`. -/
theorem endOfPotentialLineViolationRel_mem_EOPL
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat)
    (hP_len : ∀ a u, u.length = n a → (P (a, u)).length = n a)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    endOfPotentialLineViolationRel n P S V ∈ EOPL enc :=
  mem_EOPL_iff_violation.mpr ⟨endOfPotentialLineViolationRel_mem_FNP hn hP hS hV, n, P, S, V, hn,
    hP, hS, hV, hP_len, hS_len, .refl _ _⟩

/-- The circuit-style sink-of-potential-line relation of any uniform polynomial-time family lies in
`SOPL`. -/
theorem sinkOfPotentialLineViolationRel_mem_SOPL
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat)
    (hP_len : ∀ a u, u.length = n a → (P (a, u)).length = n a)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    sinkOfPotentialLineViolationRel n P S V ∈ SOPL enc :=
  mem_SOPL_iff_violation.mpr ⟨sinkOfPotentialLineViolationRel_mem_FNP hn hP hS hV, n, P, S, V, hn,
    hP, hS, hV, hP_len, hS_len, .refl _ _⟩

/-! ### Inclusions -/

/-- **`EOPL ⊆ TFNP`**. -/
theorem EOPL_subset_TFNP : EOPL enc ⊆ TFNP enc := by
  rintro R ⟨hR, n, P, S, V, -, -, -, -, -, hS_len, hred⟩
  exact ⟨hR, hred.isTotalSearch (isTotalSearch_endOfPotentialLineRel hS_len)⟩

/-- **`SOPL ⊆ TFNP`**. -/
theorem SOPL_subset_TFNP : SOPL enc ⊆ TFNP enc := by
  rintro R ⟨hR, n, P, S, V, -, -, -, -, -, hS_len, hred⟩
  exact ⟨hR, hred.isTotalSearch (isTotalSearch_sinkOfPotentialLineRel hS_len)⟩

/-- **`EOPL ⊆ SOPL`** [Göös et al., Figure 1][GoosEtAl2022]: every sink of a potential line is an
end of it, so the identity is a search reduction. -/
theorem EOPL_subset_SOPL : EOPL enc ⊆ SOPL enc := by
  rintro R ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hred⟩
  exact ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len,
    hred.trans (.of_isTotalSearch (isTotalSearch_sinkOfPotentialLineRel hS_len)
      ComputableInPolyTime.id' (snd enc encBits)
      fun _ _ hw => endOfPotentialLineRel_of_sinkOfPotentialLineRel hw)⟩

/-- **`EOPL ⊆ PPAD`** [Fearnley et al.][FearnleyGordonMehtaSavani2020]: an end-of-potential-line
family is the end-of-line family of its pruned maps. -/
theorem EOPL_subset_PPAD : EOPL enc ⊆ PPAD enc := by
  rintro R ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hred⟩
  rw [endOfPotentialLineRel_eq] at hred
  exact ⟨hR, n, potentialPred n P S V, potentialSucc n P S V, hn,
    computableInPolyTime_potentialPred hn hP hS hV,
    computableInPolyTime_potentialSucc hn hP hS hV,
    fun a _ hu => length_potentialPred (hP_len a) hu,
    fun a _ hu => length_potentialSucc (hS_len a) hu, hred⟩

/-- **`SOPL ⊆ PPADS`** [Göös et al.][GoosEtAl2022]: a sink-of-potential-line family is the
sink-of-line family of its pruned maps. -/
theorem SOPL_subset_PPADS : SOPL enc ⊆ PPADS enc := by
  rintro R ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hred⟩
  rw [sinkOfPotentialLineRel_eq] at hred
  exact ⟨hR, n, potentialPred n P S V, potentialSucc n P S V, hn,
    computableInPolyTime_potentialPred hn hP hS hV,
    computableInPolyTime_potentialSucc hn hP hS hV,
    fun a _ hu => length_potentialPred (hP_len a) hu,
    fun a _ hu => length_potentialSucc (hS_len a) hu, hred⟩

/-! ### `SOPL ⊆ PLS` -/

/-- A polynomial-time potential is bounded on each cube `{0, 1} ^ (n a)` by a polynomial-time power
of two `B a = 2 ^ m a`, with the exponent `m a` computed in unary. This is the potential range
`{0, …, 2 ^ m - 1}` of [Fearnley et al., Definition 9][FearnleyGordonMehtaSavani2020]. -/
theorem exists_potentialBound (hn : ComputableInPolyTime n enc encUnary)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ∃ m : α → ℕ, ComputableInPolyTime m enc encUnary ∧
      ∀ a u, u.length = n a → V (a, u) < 2 ^ m a := by
  obtain ⟨c, d, hbound⟩ := hV.polyBounded_length.exists_le
  let m (a : α) := c * (2 * (enc a).length + n a + 2) ^ d
  have hm : ComputableInPolyTime m enc encUnary :=
    ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const c)
      ((ComputableInPolyTime.unary_pow d).comp
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.unary_add'
            (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2)
              (ComputableInPolyTime.encoding_length enc))
            hn)
          (ComputableInPolyTime.const 2)))
  refine ⟨m, hm, fun a u hu => ?_⟩
  have hb := hbound (a, u)
  simp only [encNat_apply, length_encPair, encBits_apply, hu] at hb
  have hbits : (V (a, u)).bits.length ≤ m a := by
    rw [show 2 * (enc a).length + 1 + n a + 1 = 2 * (enc a).length + n a + 2 by omega] at hb
    exact hb
  rw [Nat.size_eq_bits_len] at hbits
  exact (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) hbits)

/-- Whether `u` lies on a potential line: `u = 0 ^ (n a)` or `u` has a potential-increasing incoming
edge. -/
def onPotentialLine (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ)
    (p : α × List Bool) : Bool :=
  decide (p.2 = zeroVertex (n p.1)) || hasPotentialIn n P S V p.1 p.2

/-- The neighbor map of the local-search family simulating a sink-of-potential-line family: follow
the pruned successor on a potential line, and jump to `0 ^ (n a)` off it. -/
def soplNeighbor (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ)
    (p : α × List Bool) : List Bool :=
  if onPotentialLine n P S V p then potentialSucc n P S V p else zeroVertex (n p.1)

/-- The cost of the local-search family simulating a sink-of-potential-line family with potentials
below `B`: `B - V` on a potential line, and `B + 1` off it. -/
def soplCost (B : α → ℕ) (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ)
    (p : α × List Bool) : ℕ :=
  if onPotentialLine n P S V p then B p.1 - V p else B p.1 + 1

theorem length_soplNeighbor (hS : ∀ u, u.length = n a → (S (a, u)).length = n a)
    (hu : u.length = n a) : (soplNeighbor n P S V (a, u)).length = n a := by
  unfold soplNeighbor
  split_ifs
  · exact length_potentialSucc hS hu
  · exact length_zeroVertex _

/-- Local optima of the simulating local-search family are sinks of the potential line. -/
theorem sinkOfPotentialLineRel_of_localOptRel {B : α → ℕ}
    (hB : ∀ u, u.length = n a → V (a, u) < B a)
    (hS : ∀ u, u.length = n a → (S (a, u)).length = n a)
    (h : localOptRel n (soplNeighbor n P S V) (soplCost B n P S V) a u) :
    sinkOfPotentialLineRel n P S V a u := by
  obtain ⟨hlen, hle⟩ := h
  by_cases hon : onPotentialLine n P S V (a, u) = true
  · have hon' : u = zeroVertex (n a) ∨ hasPotentialIn n P S V a u = true := by
      simpa [onPotentialLine] using hon
    refine ⟨hlen, ?_, hon'⟩
    by_contra hout
    simp only [Bool.not_eq_false] at hout
    have hnext : onPotentialLine n P S V (a, S (a, u)) = true := by
      simp [onPotentialLine, hasPotentialIn_of_hasPotentialOut hout]
    have hV := (hasPotentialOut_eq_true_iff.mp hout).2.2.2
    have hBS := hB _ (hS u hlen)
    simp only [soplCost, soplNeighbor, hon, ↓reduceIte, potentialSucc_of_true hout, hnext] at hle
    omega
  · exfalso
    have hz : onPotentialLine n P S V (a, zeroVertex (n a)) = true := by
      simp [onPotentialLine]
    simp only [soplCost, soplNeighbor, hon, Bool.false_eq_true, ↓reduceIte, hz] at hle
    omega

theorem computableInPolyTime_onPotentialLine
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (onPotentialLine n P S V) (encPair enc encBits) encBool := by
  unfold onPotentialLine
  exact bool_or.comp ((ComputableInPolyTime.decide_eq' (snd enc encBits)
    (computableInPolyTime_zeroVertex_comp (hn.comp (fst enc encBits)))).prod
    (computableInPolyTime_hasPotentialIn hn hP hS hV))

/-- **`SOPL ⊆ PLS`** [Göös et al.][GoosEtAl2022]: follow the pruned successor along potential
lines, with cost `B - V` below a polynomial-time potential bound `B`, and send every vertex off the
potential lines to `0 ^ n` at the higher cost `B + 1`. Local optima are exactly the sinks. -/
theorem SOPL_subset_PLS : SOPL enc ⊆ PLS enc := by
  rintro R ⟨hR, n, P, S, V, hn, hP, hS, hV, -, hS_len, hred⟩
  obtain ⟨m, hm, hB⟩ := exists_potentialBound hn hV
  have hon := computableInPolyTime_onPotentialLine hn hP hS hV
  have hN : ComputableInPolyTime (soplNeighbor n P S V) (encPair enc encBits) encBits := by
    unfold soplNeighbor
    exact hon.ite (computableInPolyTime_potentialSucc hn hP hS hV)
      (computableInPolyTime_zeroVertex_comp (hn.comp (fst enc encBits)))
  have hBp : ComputableInPolyTime (fun p : α × List Bool => 2 ^ m p.1) (encPair enc encBits)
      encNat := ComputableInPolyTime.binary_two_pow.comp (hm.comp (fst enc encBits))
  have hC : ComputableInPolyTime (soplCost (fun a => 2 ^ m a) n P S V) (encPair enc encBits)
      encNat := by
    unfold soplCost
    exact hon.ite (binary_sub' hBp hV)
      (ComputableInPolyTime.binary_add.comp (hBp.prod (ComputableInPolyTime.const 1)))
  have hlen (a : α) (u : List Bool) (hu : u.length = n a) :
      (soplNeighbor n P S V (a, u)).length = n a := length_soplNeighbor (hS_len a) hu
  exact ⟨hR, n, soplNeighbor n P S V, soplCost (fun a => 2 ^ m a) n P S V, hn, hN, hC, hlen,
    hred.trans (.of_isTotalSearch (isTotalSearch_localOptRel hlen) ComputableInPolyTime.id'
      (snd enc encBits) fun a _ hw =>
        sinkOfPotentialLineRel_of_localOptRel (hB a) (hS_len a) hw)⟩

/-- **`EOPL ⊆ PLS`** [Fearnley et al.][FearnleyGordonMehtaSavani2020]. -/
theorem EOPL_subset_PLS : EOPL enc ⊆ PLS enc :=
  fun _ h => SOPL_subset_PLS (EOPL_subset_SOPL h)

/-- **`EOPL ⊆ PLS ∩ PPAD`** [Fearnley et al.][FearnleyGordonMehtaSavani2020]. -/
theorem EOPL_subset_PLS_inter_PPAD : EOPL enc ⊆ PLS enc ∩ PPAD enc :=
  fun _ h => ⟨EOPL_subset_PLS h, EOPL_subset_PPAD h⟩

/-- **`SOPL ⊆ PLS ∩ PPADS`** [Göös et al.][GoosEtAl2022]. -/
theorem SOPL_subset_PLS_inter_PPADS : SOPL enc ⊆ PLS enc ∩ PPADS enc :=
  fun _ h => ⟨SOPL_subset_PLS h, SOPL_subset_PPADS h⟩

end Cslib.Complexity
