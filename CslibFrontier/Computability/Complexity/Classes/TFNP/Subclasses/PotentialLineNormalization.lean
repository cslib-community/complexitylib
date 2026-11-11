/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.Nat.Size

/-!
# Promised-source normalization for `EOPL` and `SOPL`

[Fearnley, Gordon, Mehta and Savani, Definition 9][FearnleyGordonMehtaSavani2020] defines
*End-of-Potential-Line* on `{0, 1} ^ n` under two syntactic conditions at the distinguished source
`0 ^ n`:

1. `P (0 ^ n) = 0 ^ n ≠ S (0 ^ n)` (`LineSourcePromise`); and
2. `V (0 ^ n) = 0`, with potentials in `{0, …, 2 ^ m - 1}`,

asking for a vertex `x` of type

* (R1) `S (P x) ≠ x ≠ 0 ^ n` or `P (S x) ≠ x`; or
* (R2) `x ≠ S x`, `P (S x) = x` and `V (S x) ≤ V x`,

without any fallback clause at `0 ^ n` for a failed source promise.

In `CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLine`, the relations
`endOfPotentialLineViolationRel` and `sinkOfPotentialLineViolationRel` make `(R1) ∨ (R2)` total on
arbitrary raw families by also accepting `0 ^ n` when `LineSourcePromise` fails, and omit
`V (0 ^ n) = 0`. This module formalizes the uniform polynomial-time `(n + 1)`-bit normalization to
the exact promised convention (`PromisedPotentialLine`, `endOfPotentialLinePromisedRel`, and
`sinkOfPotentialLinePromisedRel`):

* On bit-width `normalizedPotentialWidth n a = n a + 1` with new distinguished source
  `0 ^ (n a + 1) = false :: 0 ^ (n a)`, the normalized family sets
  `S' (0 ^ (n a + 1)) = true :: 0 ^ (n a)`, `P' (0 ^ (n a + 1)) = 0 ^ (n a + 1)`, and
  `V' (0 ^ (n a + 1)) = 0`; embeds the pruned graph of `(n, P, S, V)` on `{true} × {0, 1} ^ (n a)`
  via `S' (true :: u) = true :: potentialSucc (a, u)`, `P' (true :: 0 ^ (n a)) = 0 ^ (n a + 1)`,
  `P' (true :: u) = true :: potentialPred (a, u)` (`u ≠ 0 ^ (n a)`), and `V' (true :: u) = V u + 1`;
  and leaves every `false :: u` with `u ≠ 0 ^ (n a)` isolated at potential `0`.
* `PromisedPotentialLine` holds unconditionally for every instance `a`, even when `(n, P, S, V)`
  violates `LineSourcePromise`, has `V (a, 0 ^ (n a)) > 0`, has equal-potential edges, or has width
  `n a = 0` (`promisedPotentialLine_normalized`).
* Binary potential values grow by at most `+ 1` (`size_normalizedPotential_le`,
  `normalizedPotential_lt_two_pow_succ`, `exists_normalizedPotentialBound`).
* Solutions `w` of `endOfPotentialLinePromisedRel` (resp. `sinkOfPotentialLinePromisedRel`) on the
  normalized family are in exact bijection `u ↔ true :: u` with ends `endOfPotentialLineRel`
  (resp. sinks `sinkOfPotentialLineRel`) of `(n, P, S, V)`
  (`endOfPotentialLinePromisedRel_normalized_iff`, `sinkOfPotentialLinePromisedRel_normalized_iff`).
* Composing `w ↦ w.tail` with `potentialLineBack` (`normalizedViolationBack`) maps normalized
  promised solutions back to raw violations of `(n, P, S, V)`, sending failed-promise instances to
  `0 ^ (n a)` (`endOfPotentialLineViolationRel_normalizedViolationBack`,
  `sinkOfPotentialLineViolationRel_normalizedViolationBack`).
* `mem_EOPL_iff_promised`, `mem_EOPL_iff_promised_bounded`, `mem_SOPL_iff_promised`, and
  `mem_SOPL_iff_promised_bounded` show that imposing `PromisedPotentialLine`, pure `(R1)/(R2)`
  solutions, and explicit unary potential bit-bounds leaves `EOPL` and `SOPL` unchanged.

Canonical Boolean-circuit completeness of *End-of-Potential-Line*, `UEOPL`, and `CLS` are not
formalized here.

## Main definitions

* `Cslib.Complexity.PromisedPotentialLine`: `LineSourcePromise n P S a ∧ V (a, 0 ^ (n a)) = 0`.
* `Cslib.Complexity.endOfPotentialLinePromisedRel`,
  `Cslib.Complexity.sinkOfPotentialLinePromisedRel`: pure `(R1) ∨ (R2)` relations without the
  failed-promise fallback at `0 ^ (n a)`.
* `Cslib.Complexity.normalizedPotentialWidth`, `Cslib.Complexity.normalizedPotentialPred`,
  `Cslib.Complexity.normalizedPotentialSucc`, `Cslib.Complexity.normalizedPotential`: the uniform
  `(n + 1)`-bit promised-source normalization.
* `Cslib.Complexity.normalizedViolationBack`: witness back-map
  `potentialLineBack n P S V (a, w.tail)` from normalized promised solutions to raw circuit-style
  violations.

## Main results

* `Cslib.Complexity.promisedPotentialLine_normalized`,
  `Cslib.Complexity.exists_normalizedPotentialBound`: unconditional source promise, zero source
  potential, and polynomial binary bit-bound on `{0, 1} ^ (n a + 1)`.
* `Cslib.Complexity.endOfPotentialLinePromisedRel_normalized_iff`,
  `Cslib.Complexity.sinkOfPotentialLinePromisedRel_normalized_iff`: exact `true :: u` solution
  characterizations.
* `Cslib.Complexity.endOfPotentialLineRel_searchReducible_promised_normalized`,
  `Cslib.Complexity.promised_normalized_searchReducible_endOfPotentialLineRel`,
  `Cslib.Complexity.endOfPotentialLineViolationRel_searchReducible_promised_normalized` (and `SOPL`
  counterparts): polynomial-time `SearchReducible` equivalences.
* `Cslib.Complexity.mem_EOPL_iff_promised`, `Cslib.Complexity.mem_EOPL_iff_promised_bounded`,
  `Cslib.Complexity.mem_SOPL_iff_promised`, `Cslib.Complexity.mem_SOPL_iff_promised_bounded`.

## References

* [J. Fearnley, S. Gordon, R. Mehta, R. Savani, *Unique End of Potential
  Line*][FearnleyGordonMehtaSavani2020], Section 2, Definition 9
* [M. Göös, A. Hollender, S. Jain, G. Maystre, W. Pires, R. Robere, R. Tao, *Further Collapses in
  TFNP*][GoosEtAl2022]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type}

/-! ### Promised convention and pure `(R1)/(R2)` solution relations -/

/-- Full syntactic source promise of [Fearnley et al., Definition 9][FearnleyGordonMehtaSavani2020]:
`P (0 ^ n) = 0 ^ n ≠ S (0 ^ n)` (`LineSourcePromise`) together with `V (0 ^ n) = 0`. -/
def PromisedPotentialLine (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) : Prop :=
  LineSourcePromise n P S a ∧ V (a, zeroVertex (n a)) = 0

/-- Exact `(R1) ∨ (R2)` solution relation of
[Fearnley et al., Definition 9][FearnleyGordonMehtaSavani2020], without the failed-promise fallback
at `0 ^ (n a)`:

* (R1) `S (P x) ≠ x ≠ 0 ^ (n a)` or `P (S x) ≠ x`; or
* (R2) `x ≠ S x`, `P (S x) = x`, and `V (S x) ≤ V x`. -/
def endOfPotentialLinePromisedRel (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) (x : List Bool) : Prop :=
  x.length = n a ∧
    ((S (a, P (a, x)) ≠ x ∧ x ≠ zeroVertex (n a)) ∨ P (a, S (a, x)) ≠ x ∨
      (x ≠ S (a, x) ∧ P (a, S (a, x)) = x ∧ V (a, S (a, x)) ≤ V (a, x)))

/-- Exact sink-only `(R1) ∨ (R2)` solution relation, dropping both the start-of-line clause
`S (P x) ≠ x ≠ 0 ^ (n a)` and the failed-promise fallback at `0 ^ (n a)`. -/
def sinkOfPotentialLinePromisedRel (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) (x : List Bool) : Prop :=
  x.length = n a ∧
    (P (a, S (a, x)) ≠ x ∨
      (x ≠ S (a, x) ∧ P (a, S (a, x)) = x ∧ V (a, S (a, x)) ≤ V (a, x)))

instance instDecidableLineSourcePromise (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α) :
    Decidable (LineSourcePromise n P S a) := by
  unfold LineSourcePromise; infer_instance

instance instDecidablePromisedPotentialLine (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) :
    Decidable (PromisedPotentialLine n P S V a) := by
  unfold PromisedPotentialLine; infer_instance

instance instDecidableEndOfPotentialLinePromisedRel (n : α → ℕ)
    (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ) (a : α) (x : List Bool) :
    Decidable (endOfPotentialLinePromisedRel n P S V a x) := by
  unfold endOfPotentialLinePromisedRel; infer_instance

instance instDecidableSinkOfPotentialLinePromisedRel (n : α → ℕ)
    (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ) (a : α) (x : List Bool) :
    Decidable (sinkOfPotentialLinePromisedRel n P S V a x) := by
  unfold sinkOfPotentialLinePromisedRel; infer_instance

section PromisedRelations

variable {n : α → ℕ} {P S : α × List Bool → List Bool} {V : α × List Bool → ℕ} {a : α}
  {x : List Bool}

theorem PromisedPotentialLine.lineSourcePromise (h : PromisedPotentialLine n P S V a) :
    LineSourcePromise n P S a :=
  h.1

theorem PromisedPotentialLine.potential_zeroVertex (h : PromisedPotentialLine n P S V a) :
    V (a, zeroVertex (n a)) = 0 :=
  h.2

theorem endOfPotentialLinePromisedRel_of_sink (h : sinkOfPotentialLinePromisedRel n P S V a x) :
    endOfPotentialLinePromisedRel n P S V a x :=
  ⟨h.1, .inr h.2⟩

theorem endOfPotentialLineViolationRel_of_promised (h : endOfPotentialLinePromisedRel n P S V a x) :
    endOfPotentialLineViolationRel n P S V a x :=
  ⟨h.1, .inr h.2⟩

theorem sinkOfPotentialLineViolationRel_of_promised
    (h : sinkOfPotentialLinePromisedRel n P S V a x) :
    sinkOfPotentialLineViolationRel n P S V a x :=
  ⟨h.1, .inr h.2⟩

/-- `endOfPotentialLineViolationRel` is `endOfPotentialLinePromisedRel` together with the fallback
witness `0 ^ (n a)` when `LineSourcePromise` fails. -/
theorem endOfPotentialLineViolationRel_iff_promised_or :
    endOfPotentialLineViolationRel n P S V a x ↔
      (x = zeroVertex (n a) ∧ ¬LineSourcePromise n P S a) ∨
        endOfPotentialLinePromisedRel n P S V a x := by
  constructor
  · rintro ⟨hx, h | h⟩
    · exact .inl h
    · exact .inr ⟨hx, h⟩
  · rintro (⟨rfl, h⟩ | ⟨hx, h⟩)
    · exact ⟨length_zeroVertex _, .inl ⟨rfl, h⟩⟩
    · exact ⟨hx, .inr h⟩

/-- `sinkOfPotentialLineViolationRel` is `sinkOfPotentialLinePromisedRel` together with the fallback
witness `0 ^ (n a)` when `LineSourcePromise` fails. -/
theorem sinkOfPotentialLineViolationRel_iff_promised_or :
    sinkOfPotentialLineViolationRel n P S V a x ↔
      (x = zeroVertex (n a) ∧ ¬LineSourcePromise n P S a) ∨
        sinkOfPotentialLinePromisedRel n P S V a x := by
  constructor
  · rintro ⟨hx, h | h⟩
    · exact .inl h
    · exact .inr ⟨hx, h⟩
  · rintro (⟨rfl, h⟩ | ⟨hx, h⟩)
    · exact ⟨length_zeroVertex _, .inl ⟨rfl, h⟩⟩
    · exact ⟨hx, .inr h⟩

/-- Under `LineSourcePromise`, the totalized violation relation coincides with the pure `(R1)/(R2)`
relation of [Fearnley et al., Definition 9][FearnleyGordonMehtaSavani2020]. -/
theorem endOfPotentialLineViolationRel_iff_promised_of_promise (h : LineSourcePromise n P S a) :
    endOfPotentialLineViolationRel n P S V a x ↔ endOfPotentialLinePromisedRel n P S V a x := by
  rw [endOfPotentialLineViolationRel_iff_promised_or]
  simp [h]

/-- Under `LineSourcePromise`, the totalized sink violation relation coincides with the pure
sink-only `(R1)/(R2)` relation. -/
theorem sinkOfPotentialLineViolationRel_iff_promised_of_promise (h : LineSourcePromise n P S a) :
    sinkOfPotentialLineViolationRel n P S V a x ↔ sinkOfPotentialLinePromisedRel n P S V a x := by
  rw [sinkOfPotentialLineViolationRel_iff_promised_or]
  simp [h]

/-- Any length-preserving family satisfying `LineSourcePromise` is total for the pure `(R1)/(R2)`
relation `endOfPotentialLinePromisedRel`. -/
theorem isTotalSearch_endOfPotentialLinePromisedRel
    (hprom : ∀ a, LineSourcePromise n P S a)
    (hP_len : ∀ a u, u.length = n a → (P (a, u)).length = n a)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    IsTotalSearch (endOfPotentialLinePromisedRel n P S V) := fun a => by
  obtain ⟨u, hu⟩ := isTotalSearch_endOfPotentialLineRel (P := P) (V := V) hS_len a
  exact ⟨potentialLineBack n P S V (a, u),
    (endOfPotentialLineViolationRel_iff_promised_of_promise (hprom a)).mp
      (endOfPotentialLineViolationRel_potentialLineBack (hP_len a) hu)⟩

/-- Any successor-length-preserving family satisfying `LineSourcePromise` is total for the pure
sink-only relation `sinkOfPotentialLinePromisedRel`. -/
theorem isTotalSearch_sinkOfPotentialLinePromisedRel
    (hprom : ∀ a, LineSourcePromise n P S a)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    IsTotalSearch (sinkOfPotentialLinePromisedRel n P S V) := fun a => by
  obtain ⟨u, hu⟩ := isTotalSearch_sinkOfPotentialLineRel (P := P) (V := V) hS_len a
  exact ⟨potentialLineBack n P S V (a, u),
    (sinkOfPotentialLineViolationRel_iff_promised_of_promise (hprom a)).mp
      (sinkOfPotentialLineViolationRel_potentialLineBack hu)⟩

end PromisedRelations

/-! ### Uniform `(n + 1)`-bit promised-source normalization -/

/-- Padded vertex bit-width `n a + 1` of the promised-source normalization. -/
def normalizedPotentialWidth (n : α → ℕ) (a : α) : ℕ := n a + 1

/-- Normalized predecessor map on `b :: u` of length `n a + 1`: fixes `false :: u` (in particular
`0 ^ (n a + 1)`), steps `true :: 0 ^ (n a)` back to `0 ^ (n a + 1)`, and follows the pruned
predecessor `true :: potentialPred n P S V (a, u)` on `true :: u` for `u ≠ 0 ^ (n a)`. -/
def normalizedPotentialPred (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (p : α × List Bool) : List Bool :=
  if p.2.headD false then
    if decide (p.2.tail = zeroVertex (n p.1)) then
      false :: zeroVertex (n p.1)
    else
      true :: potentialPred n P S V (p.1, p.2.tail)
  else
    false :: p.2.tail

/-- Normalized successor map on `b :: u` of length `n a + 1`: steps `0 ^ (n a + 1)` to
`true :: 0 ^ (n a)`, fixes every other `false :: u`, and follows the pruned successor
`true :: potentialSucc n P S V (a, u)` on `{true} × {0, 1} ^ (n a)`. -/
def normalizedPotentialSucc (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (p : α × List Bool) : List Bool :=
  if p.2.headD false then
    true :: potentialSucc n P S V (p.1, p.2.tail)
  else if decide (p.2.tail = zeroVertex (n p.1)) then
    true :: zeroVertex (n p.1)
  else
    false :: p.2.tail

/-- Normalized potential on `b :: u`: `V (a, u) + 1` on `{true} × {0, 1} ^ (n a)` and `0` on
`{false} × {0, 1} ^ (n a)` (so `V' (0 ^ (n a + 1)) = 0` and the source edge `0 ^ (n a + 1) →
true :: 0 ^ (n a)` strictly increases the potential from `0` to `V (0 ^ (n a)) + 1`). -/
def normalizedPotential (V : α × List Bool → ℕ) (p : α × List Bool) : ℕ :=
  if p.2.headD false then V (p.1, p.2.tail) + 1 else 0

/-- Witness back-map from normalized promised solutions `w` to raw circuit-style violations of
`(n, P, S, V)`: projects `w.tail` and applies `potentialLineBack` (which returns `0 ^ (n a)` when
`LineSourcePromise n P S a` fails). -/
def normalizedViolationBack (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (p : α × List Bool) : List Bool :=
  potentialLineBack n P S V (p.1, p.2.tail)

section NormalizedProperties

variable {n : α → ℕ} {P S : α × List Bool → List Bool} {V : α × List Bool → ℕ} {a : α}
  {u w : List Bool}

@[simp]
theorem normalizedPotentialWidth_apply (n : α → ℕ) (a : α) :
    normalizedPotentialWidth n a = n a + 1 :=
  rfl

@[simp]
private theorem zeroVertex_succ (k : ℕ) :
    zeroVertex (k + 1) = false :: zeroVertex k :=
  List.replicate_succ

theorem zeroVertex_normalizedPotentialWidth (n : α → ℕ) (a : α) :
    zeroVertex (normalizedPotentialWidth n a) = false :: zeroVertex (n a) :=
  List.replicate_succ

private theorem cons_eq_zeroVertex_succ_iff {k : ℕ} {b : Bool} {v : List Bool} :
    b :: v = zeroVertex (k + 1) ↔ b = false ∧ v = zeroVertex k := by
  simp

@[simp]
theorem normalizedPotentialPred_false (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) (u : List Bool) :
    normalizedPotentialPred n P S V (a, false :: u) = false :: u :=
  rfl

theorem normalizedPotentialPred_true (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) (u : List Bool) :
    normalizedPotentialPred n P S V (a, true :: u) =
      if u = zeroVertex (n a) then false :: zeroVertex (n a)
      else true :: potentialPred n P S V (a, u) := by
  by_cases h : u = zeroVertex (n a) <;> simp [normalizedPotentialPred, h]

@[simp]
theorem normalizedPotentialPred_true_zeroVertex (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) :
    normalizedPotentialPred n P S V (a, true :: zeroVertex (n a)) =
      zeroVertex (normalizedPotentialWidth n a) := by
  simp [normalizedPotentialPred]

theorem normalizedPotentialPred_true_of_ne (hu : u ≠ zeroVertex (n a)) :
    normalizedPotentialPred n P S V (a, true :: u) = true :: potentialPred n P S V (a, u) := by
  simp [normalizedPotentialPred, hu]

@[simp]
theorem normalizedPotentialSucc_true (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) (u : List Bool) :
    normalizedPotentialSucc n P S V (a, true :: u) = true :: potentialSucc n P S V (a, u) :=
  rfl

theorem normalizedPotentialSucc_false (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) (u : List Bool) :
    normalizedPotentialSucc n P S V (a, false :: u) =
      if u = zeroVertex (n a) then true :: zeroVertex (n a) else false :: u := by
  by_cases h : u = zeroVertex (n a) <;> simp [normalizedPotentialSucc, h]

theorem normalizedPotentialSucc_false_of_ne (hu : u ≠ zeroVertex (n a)) :
    normalizedPotentialSucc n P S V (a, false :: u) = false :: u := by
  simp [normalizedPotentialSucc, hu]

@[simp]
theorem normalizedPotential_false (V : α × List Bool → ℕ) (a : α) (u : List Bool) :
    normalizedPotential V (a, false :: u) = 0 :=
  rfl

@[simp]
theorem normalizedPotential_true (V : α × List Bool → ℕ) (a : α) (u : List Bool) :
    normalizedPotential V (a, true :: u) = V (a, u) + 1 :=
  rfl

@[simp]
theorem normalizedPotentialSucc_false_zeroVertex (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) :
    normalizedPotentialSucc n P S V (a, false :: zeroVertex (n a)) = true :: zeroVertex (n a) := by
  simp [normalizedPotentialSucc]

theorem normalizedPotentialPred_zeroVertex (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) :
    normalizedPotentialPred n P S V (a, zeroVertex (normalizedPotentialWidth n a)) =
      zeroVertex (normalizedPotentialWidth n a) := by
  simp

theorem normalizedPotentialSucc_zeroVertex (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) :
    normalizedPotentialSucc n P S V (a, zeroVertex (normalizedPotentialWidth n a)) =
      true :: zeroVertex (n a) := by
  simp

theorem normalizedPotential_zeroVertex (n : α → ℕ) (V : α × List Bool → ℕ) (a : α) :
    normalizedPotential V (a, zeroVertex (normalizedPotentialWidth n a)) = 0 := by
  simp

/-- The normalized family satisfies `LineSourcePromise` on every instance `a`, regardless of whether
the original family satisfies `LineSourcePromise` or has width `n a = 0`. -/
theorem lineSourcePromise_normalized (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) :
    LineSourcePromise (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V) a := by
  refine ⟨normalizedPotentialPred_zeroVertex n P S V a, ?_⟩
  simp [normalizedPotentialSucc]

/-- The normalized family satisfies the full syntactic promise `PromisedPotentialLine` of
[Fearnley et al., Definition 9][FearnleyGordonMehtaSavani2020] (`P' (0 ^ (n + 1)) = 0 ^ (n + 1) ≠
S' (0 ^ (n + 1))` and `V' (0 ^ (n + 1)) = 0`) on every instance `a`. -/
theorem promisedPotentialLine_normalized (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) :
    PromisedPotentialLine (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a :=
  ⟨lineSourcePromise_normalized n P S V a, normalizedPotential_zeroVertex n V a⟩

/-- On the normalized family, `endOfPotentialLineViolationRel` coincides with the pure `(R1)/(R2)`
relation `endOfPotentialLinePromisedRel`. -/
theorem endOfPotentialLineViolationRel_normalized_iff :
    endOfPotentialLineViolationRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a w ↔
    endOfPotentialLinePromisedRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a w :=
  endOfPotentialLineViolationRel_iff_promised_of_promise (lineSourcePromise_normalized n P S V a)

/-- On the normalized family, `sinkOfPotentialLineViolationRel` coincides with the pure sink-only
relation `sinkOfPotentialLinePromisedRel`. -/
theorem sinkOfPotentialLineViolationRel_normalized_iff :
    sinkOfPotentialLineViolationRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a w ↔
    sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a w :=
  sinkOfPotentialLineViolationRel_iff_promised_of_promise (lineSourcePromise_normalized n P S V a)

/-- `normalizedPotentialPred` preserves the vertex bit-length `n a + 1`. -/
theorem length_normalizedPotentialPred
    (hP : ∀ u, u.length = n a → (P (a, u)).length = n a)
    (hw : w.length = normalizedPotentialWidth n a) :
    (normalizedPotentialPred n P S V (a, w)).length = normalizedPotentialWidth n a := by
  cases w with
  | nil => simp [normalizedPotentialWidth] at hw
  | cons b u =>
    have hu : u.length = n a := by simpa [normalizedPotentialWidth] using hw
    cases b
    · simp [normalizedPotentialWidth, hu]
    · by_cases huz : u = zeroVertex (n a)
      · subst huz; simp [normalizedPotentialWidth]
      · simp [normalizedPotentialPred_true_of_ne huz, normalizedPotentialWidth,
          length_potentialPred hP hu]

/-- `normalizedPotentialSucc` preserves the vertex bit-length `n a + 1`. -/
theorem length_normalizedPotentialSucc
    (hS : ∀ u, u.length = n a → (S (a, u)).length = n a)
    (hw : w.length = normalizedPotentialWidth n a) :
    (normalizedPotentialSucc n P S V (a, w)).length = normalizedPotentialWidth n a := by
  cases w with
  | nil => simp [normalizedPotentialWidth] at hw
  | cons b u =>
    have hu : u.length = n a := by simpa [normalizedPotentialWidth] using hw
    cases b
    · by_cases huz : u = zeroVertex (n a)
      · subst huz; simp [normalizedPotentialSucc, normalizedPotentialWidth]
      · simp [normalizedPotentialSucc_false_of_ne huz, normalizedPotentialWidth, hu]
    · simp [normalizedPotentialWidth, length_potentialSucc hS hu]

/-- Binary length growth of `normalizedPotential`: incrementing `V (a, w.tail)` adds at most `1` bit
to its binary representation. -/
theorem size_normalizedPotential_le (V : α × List Bool → ℕ) (a : α) (w : List Bool) :
    (normalizedPotential V (a, w)).size ≤ (V (a, w.tail)).size + 1 := by
  unfold normalizedPotential
  dsimp only
  split_ifs
  · refine Nat.size_le.2 ?_
    rw [Nat.pow_succ]
    have hlt := Nat.lt_size_self (V (a, w.tail))
    omega
  · simp

/-- If `V` lies below `B` on `{0, 1} ^ (n a)`, then `normalizedPotential V` lies below `B + 1` on
`{0, 1} ^ (n a + 1)`. -/
theorem normalizedPotential_lt_succ {B : ℕ}
    (hB : ∀ u, u.length = n a → V (a, u) < B)
    (hw : w.length = normalizedPotentialWidth n a) :
    normalizedPotential V (a, w) < B + 1 := by
  cases w with
  | nil => simp [normalizedPotentialWidth] at hw
  | cons b u =>
    have hu : u.length = n a := by simpa [normalizedPotentialWidth] using hw
    cases b
    · simp
    · simpa using Nat.succ_lt_succ (hB u hu)

/-- If `V` fits in `m` bits (`< 2 ^ m`) on `{0, 1} ^ (n a)`, then `normalizedPotential V` fits in
`m + 1` bits (`< 2 ^ (m + 1)`) on `{0, 1} ^ (n a + 1)`. -/
theorem normalizedPotential_lt_two_pow_succ {m : ℕ}
    (hm : ∀ u, u.length = n a → V (a, u) < 2 ^ m)
    (hw : w.length = normalizedPotentialWidth n a) :
    normalizedPotential V (a, w) < 2 ^ (m + 1) := by
  have h := normalizedPotential_lt_succ hm hw
  have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [Nat.pow_succ]
  omega

/-! ### Active edges and exact witness bijection -/

theorem hasPotentialIn_normalized_false (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) (u : List Bool) :
    hasPotentialIn (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a (false :: u) = false := by
  simp [hasPotentialIn, hasIn]

theorem hasPotentialOut_normalized_zeroVertex (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) :
    hasPotentialOut (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a (zeroVertex (normalizedPotentialWidth n a)) = true := by
  rw [hasPotentialOut_eq_true_iff]
  simp [normalizedPotentialSucc]

theorem hasPotentialOut_normalized_false_of_ne (hu : u ≠ zeroVertex (n a)) :
    hasPotentialOut (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a (false :: u) = false := by
  simp [hasPotentialOut, hasOut, normalizedPotentialSucc_false_of_ne hu]

theorem hasPotentialOut_normalized_true (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) (u : List Bool) :
    hasPotentialOut (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a (true :: u) = hasPotentialOut n P S V a u := by
  cases hout : hasPotentialOut n P S V a u
  · simp [hasPotentialOut, hasOut, potentialSucc_of_false hout]
  · have hin := hasPotentialIn_of_hasPotentialOut hout
    obtain ⟨hPS, hSu, hS0, hV⟩ := hasPotentialOut_eq_true_iff.mp hout
    rw [hasPotentialOut_eq_true_iff]
    simp only [normalizedPotentialSucc_true, potentialSucc_of_true hout,
      normalizedPotentialPred_true_of_ne hS0, potentialPred_of_true hin, hPS, ne_eq,
      List.cons.injEq, true_and, normalizedPotentialWidth_apply, zeroVertex_succ, reduceCtorEq,
      false_and, not_false_eq_true, normalizedPotential_true]
    exact ⟨hSu, Nat.succ_lt_succ hV⟩

theorem hasPotentialIn_normalized_true_zeroVertex (n : α → ℕ) (P S : α × List Bool → List Bool)
    (V : α × List Bool → ℕ) (a : α) :
    hasPotentialIn (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a (true :: zeroVertex (n a)) = true := by
  rw [hasPotentialIn_eq_true_iff]
  simp [normalizedPotentialSucc]

theorem hasPotentialIn_normalized_true_of_ne (hu : u ≠ zeroVertex (n a)) :
    hasPotentialIn (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a (true :: u) = hasPotentialIn n P S V a u := by
  cases hin : hasPotentialIn n P S V a u
  · simp [hasPotentialIn, hasIn, normalizedPotentialPred_true_of_ne hu, potentialPred_of_false hin]
  · have hout := hasPotentialOut_of_hasPotentialIn hin
    obtain ⟨hSP, hPu, -, hV⟩ := hasPotentialIn_eq_true_iff.mp hin
    rw [hasPotentialIn_eq_true_iff]
    simp only [normalizedPotentialPred_true_of_ne hu, potentialPred_of_true hin,
      normalizedPotentialSucc_true, potentialSucc_of_true hout, hSP, ne_eq, List.cons.injEq,
      true_and, normalizedPotentialWidth_apply, zeroVertex_succ, reduceCtorEq, false_and,
      not_false_eq_true, normalizedPotential_true]
    exact ⟨hPu, Nat.succ_lt_succ hV⟩

/-- No active edge of the normalized family is pruned: `potentialPred` agrees with
`normalizedPotentialPred` on every non-empty bit string `b :: u`. -/
theorem potentialPred_normalized_cons (b : Bool) (u : List Bool) :
    potentialPred (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) (a, b :: u) =
    normalizedPotentialPred n P S V (a, b :: u) := by
  cases b
  · rw [potentialPred_of_false (hasPotentialIn_normalized_false n P S V a u)]
    rfl
  · by_cases huz : u = zeroVertex (n a)
    · subst huz
      exact potentialPred_of_true (hasPotentialIn_normalized_true_zeroVertex n P S V a)
    · cases hin : hasPotentialIn n P S V a u
      · rw [potentialPred_of_false ((hasPotentialIn_normalized_true_of_ne huz).trans hin),
          normalizedPotentialPred_true_of_ne huz, potentialPred_of_false hin]
      · exact potentialPred_of_true ((hasPotentialIn_normalized_true_of_ne huz).trans hin)

/-- No active edge of the normalized family is pruned: `potentialSucc` agrees with
`normalizedPotentialSucc` on every non-empty bit string `b :: u`. -/
theorem potentialSucc_normalized_cons (b : Bool) (u : List Bool) :
    potentialSucc (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) (a, b :: u) =
    normalizedPotentialSucc n P S V (a, b :: u) := by
  cases b
  · by_cases huz : u = zeroVertex (n a)
    · subst huz
      rw [← zeroVertex_normalizedPotentialWidth]
      exact potentialSucc_of_true (hasPotentialOut_normalized_zeroVertex n P S V a)
    · rw [potentialSucc_of_false (hasPotentialOut_normalized_false_of_ne huz),
        normalizedPotentialSucc_false_of_ne huz]
  · cases hout : hasPotentialOut n P S V a u
    · rw [potentialSucc_of_false ((hasPotentialOut_normalized_true n P S V a u).trans hout),
        normalizedPotentialSucc_true, potentialSucc_of_false hout]
    · exact potentialSucc_of_true ((hasPotentialOut_normalized_true n P S V a u).trans hout)

/-- Ends of the normalized potential line are precisely `true :: u` for ends `u` of
`(n, P, S, V)`. -/
theorem endOfPotentialLineRel_normalized_iff :
    endOfPotentialLineRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a w ↔
    ∃ u, w = true :: u ∧ endOfPotentialLineRel n P S V a u := by
  cases w with
  | nil =>
    simp [endOfPotentialLineRel, normalizedPotentialWidth]
  | cons b u =>
    cases b
    · by_cases huz : u = zeroVertex (n a)
      · subst huz
        have hout := hasPotentialOut_normalized_zeroVertex n P S V a
        rw [zeroVertex_normalizedPotentialWidth] at hout
        simp [endOfPotentialLineRel, hout, hasPotentialIn_normalized_false]
      · simp [endOfPotentialLineRel, hasPotentialIn_normalized_false,
          hasPotentialOut_normalized_false_of_ne huz, huz]
    · simp only [List.cons.injEq, true_and, exists_eq_left']
      by_cases huz : u = zeroVertex (n a)
      · subst huz
        cases hout : hasPotentialOut n P S V a (zeroVertex (n a)) <;>
          simp [endOfPotentialLineRel, hasPotentialIn_normalized_true_zeroVertex,
            hasPotentialOut_normalized_true, hout]
      · cases hin : hasPotentialIn n P S V a u <;> cases hout : hasPotentialOut n P S V a u <;>
          simp [endOfPotentialLineRel, hasPotentialIn_normalized_true_of_ne huz,
            hasPotentialOut_normalized_true, huz, hin, hout]

/-- Sinks of the normalized potential line are precisely `true :: u` for sinks `u` of
`(n, P, S, V)`. -/
theorem sinkOfPotentialLineRel_normalized_iff :
    sinkOfPotentialLineRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a w ↔
    ∃ u, w = true :: u ∧ sinkOfPotentialLineRel n P S V a u := by
  cases w with
  | nil =>
    simp [sinkOfPotentialLineRel, normalizedPotentialWidth]
  | cons b u =>
    cases b
    · by_cases huz : u = zeroVertex (n a)
      · subst huz
        have hout := hasPotentialOut_normalized_zeroVertex n P S V a
        rw [zeroVertex_normalizedPotentialWidth] at hout
        simp [sinkOfPotentialLineRel, hout]
      · simp [sinkOfPotentialLineRel, hasPotentialIn_normalized_false,
          hasPotentialOut_normalized_false_of_ne huz, huz]
    · simp only [List.cons.injEq, true_and, exists_eq_left']
      by_cases huz : u = zeroVertex (n a)
      · subst huz
        cases hout : hasPotentialOut n P S V a (zeroVertex (n a)) <;>
          simp [sinkOfPotentialLineRel, hasPotentialIn_normalized_true_zeroVertex,
            hasPotentialOut_normalized_true, hout]
      · cases hin : hasPotentialIn n P S V a u <;> cases hout : hasPotentialOut n P S V a u <;>
          simp [sinkOfPotentialLineRel, hasPotentialIn_normalized_true_of_ne huz,
            hasPotentialOut_normalized_true, huz, hin, hout]

private theorem nonEmpty_normalizedPred (b : Bool) (u : List Bool) :
    ∃ b' u', normalizedPotentialPred n P S V (a, b :: u) = b' :: u' := by
  cases b
  · exact ⟨false, u, rfl⟩
  · by_cases huz : u = zeroVertex (n a)
    · subst huz; exact ⟨false, zeroVertex (n a), by simp⟩
    · exact ⟨true, potentialPred n P S V (a, u), normalizedPotentialPred_true_of_ne huz⟩

private theorem nonEmpty_normalizedSucc (b : Bool) (u : List Bool) :
    ∃ b' u', normalizedPotentialSucc n P S V (a, b :: u) = b' :: u' := by
  cases b
  · by_cases huz : u = zeroVertex (n a)
    · subst huz; exact ⟨true, zeroVertex (n a), by simp [normalizedPotentialSucc]⟩
    · exact ⟨false, u, normalizedPotentialSucc_false_of_ne huz⟩
  · exact ⟨true, potentialSucc n P S V (a, u), rfl⟩

/-- **Exact `(R1)/(R2)` solution characterization (`EOPL`).** Pure `(R1)/(R2)` solutions of the
normalized family (with no failed-promise fallback) are precisely the strings `true :: u` with `u`
an end of `(n, P, S, V)`. -/
theorem endOfPotentialLinePromisedRel_normalized_iff :
    endOfPotentialLinePromisedRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a w ↔
    ∃ u, w = true :: u ∧ endOfPotentialLineRel n P S V a u := by
  rw [← endOfPotentialLineViolationRel_normalized_iff, ← endOfPotentialLineRel_normalized_iff]
  constructor
  · intro h
    cases w with
    | nil => simp [endOfPotentialLineViolationRel, normalizedPotentialWidth] at h
    | cons b u =>
      apply endOfPotentialLineRel_of_violation
      obtain ⟨bP, uP, hP_eq⟩ := nonEmpty_normalizedPred (n := n) (P := P) (S := S) (V := V)
        (a := a) b u
      obtain ⟨bS, uS, hS_eq⟩ := nonEmpty_normalizedSucc (n := n) (P := P) (S := S) (V := V)
        (a := a) b u
      refine ⟨h.1, ?_⟩
      rw [potentialPred_normalized_cons, potentialSucc_normalized_cons,
        show normalizedPotentialPred n P S V (a, b :: u) = bP :: uP from hP_eq,
        show normalizedPotentialSucc n P S V (a, b :: u) = bS :: uS from hS_eq,
        potentialSucc_normalized_cons, potentialPred_normalized_cons, ← hP_eq, ← hS_eq]
      rcases h.2 with ⟨hz, hnp⟩ | h₁ | h₂ | h₃
      · exact (hnp (lineSourcePromise_normalized n P S V a)).elim
      · exact .inr (.inl h₁)
      · exact .inr (.inr (.inl h₂))
      · exact .inr (.inr (.inr h₃))
  · intro h
    obtain ⟨u, rfl, hu⟩ := endOfPotentialLineRel_normalized_iff.mp h
    by_cases huz : u = zeroVertex (n a)
    · subst huz
      have hout : hasPotentialOut n P S V a (zeroVertex (n a)) = false := by
        cases h0 : hasPotentialOut n P S V a (zeroVertex (n a))
        · rfl
        · simp [endOfPotentialLineRel, h0] at hu
      refine ⟨by simp, .inr (.inr (.inl ?_))⟩
      simp [potentialSucc_of_false hout]
    · rcases endOfPotentialLineRel_iff.mp hu with ⟨hlen, hout, hin'⟩ | ⟨hlen, -, hin, hout⟩
      · have hin : hasPotentialIn n P S V a u = true := hin'.resolve_left huz
        have hPu : P (a, u) ≠ u := (hasPotentialIn_eq_true_iff.mp hin).2.1
        refine ⟨by simp [hlen], .inr (.inr (.inl ?_))⟩
        simp [potentialSucc_of_false hout, normalizedPotentialPred_true_of_ne huz,
          potentialPred_of_true hin, hPu]
      · have hSu : S (a, u) ≠ u := (hasPotentialOut_eq_true_iff.mp hout).2.1
        refine ⟨by simp [hlen], .inr (.inl ⟨?_, ?_⟩)⟩
        · simp [normalizedPotentialPred_true_of_ne huz, potentialPred_of_false hin,
            potentialSucc_of_true hout, hSu]
        · simp

/-- **Exact sink-only `(R1)/(R2)` solution characterization (`SOPL`).** Pure sink-only `(R1)/(R2)`
solutions of the normalized family are precisely the strings `true :: u` with `u` a sink of
`(n, P, S, V)`. -/
theorem sinkOfPotentialLinePromisedRel_normalized_iff :
    sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a w ↔
    ∃ u, w = true :: u ∧ sinkOfPotentialLineRel n P S V a u := by
  rw [← sinkOfPotentialLineViolationRel_normalized_iff, ← sinkOfPotentialLineRel_normalized_iff]
  constructor
  · intro h
    cases w with
    | nil => simp [sinkOfPotentialLineViolationRel, normalizedPotentialWidth] at h
    | cons b u =>
      apply sinkOfPotentialLineRel_of_violation
      obtain ⟨bS, uS, hS_eq⟩ := nonEmpty_normalizedSucc (n := n) (P := P) (S := S) (V := V)
        (a := a) b u
      refine ⟨h.1, ?_⟩
      rw [potentialSucc_normalized_cons,
        show normalizedPotentialSucc n P S V (a, b :: u) = bS :: uS from hS_eq,
        potentialPred_normalized_cons, ← hS_eq]
      rcases h.2 with ⟨_, hnp⟩ | h₁ | h₂
      · exact (hnp (lineSourcePromise_normalized n P S V a)).elim
      · exact .inr (.inl h₁)
      · exact .inr (.inr h₂)
  · intro h
    obtain ⟨u, rfl, hlen, hout, hu⟩ := sinkOfPotentialLineRel_normalized_iff.mp h
    refine ⟨by simp [hlen], .inr (.inl ?_)⟩
    rcases hu with rfl | hin
    · simp [potentialSucc_of_false hout]
    · obtain ⟨-, hPu, huz, -⟩ := hasPotentialIn_eq_true_iff.mp hin
      simp [potentialSucc_of_false hout, normalizedPotentialPred_true_of_ne huz,
        potentialPred_of_true hin, hPu]

/-- Forward witness embedding (`EOPL`): every end `u` of `(n, P, S, V)` embeds as `true :: u`. -/
theorem endOfPotentialLinePromisedRel_normalized_cons (h : endOfPotentialLineRel n P S V a u) :
    endOfPotentialLinePromisedRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a (true :: u) :=
  endOfPotentialLinePromisedRel_normalized_iff.mpr ⟨u, rfl, h⟩

/-- Backward witness projection (`EOPL`): the tail `w.tail` of any normalized promised solution `w`
is an end of `(n, P, S, V)`. -/
theorem endOfPotentialLineRel_tail_of_promised_normalized
    (h : endOfPotentialLinePromisedRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a w) :
    endOfPotentialLineRel n P S V a w.tail := by
  obtain ⟨u, rfl, hu⟩ := endOfPotentialLinePromisedRel_normalized_iff.mp h
  exact hu

/-- Forward witness embedding (`SOPL`): every sink `u` of `(n, P, S, V)` embeds as `true :: u`. -/
theorem sinkOfPotentialLinePromisedRel_normalized_cons (h : sinkOfPotentialLineRel n P S V a u) :
    sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a (true :: u) :=
  sinkOfPotentialLinePromisedRel_normalized_iff.mpr ⟨u, rfl, h⟩

/-- Backward witness projection (`SOPL`): the tail `w.tail` of any normalized promised sink solution
`w` is a sink of `(n, P, S, V)`. -/
theorem sinkOfPotentialLineRel_tail_of_promised_normalized
    (h : sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a w) :
    sinkOfPotentialLineRel n P S V a w.tail := by
  obtain ⟨u, rfl, hu⟩ := sinkOfPotentialLinePromisedRel_normalized_iff.mp h
  exact hu

/-- When `LineSourcePromise n P S a` fails, `normalizedViolationBack` returns the raw violation
witness `0 ^ (n a)`. -/
theorem normalizedViolationBack_of_not_promise (h : ¬LineSourcePromise n P S a) :
    normalizedViolationBack n P S V (a, w) = zeroVertex (n a) :=
  potentialLineBack_of_not_promise h

/-- Under `LineSourcePromise n P S a`, `normalizedViolationBack` steps back to `P (a, w.tail)` on
non-increasing incoming active edges and returns `w.tail` otherwise. -/
theorem normalizedViolationBack_of_promise (h : LineSourcePromise n P S a) :
    normalizedViolationBack n P S V (a, w) =
      if hasIn n P S a w.tail && decide (V (a, w.tail) ≤ V (a, P (a, w.tail))) then
        P (a, w.tail)
      else
        w.tail :=
  potentialLineBack_of_promise h

/-- **Normalized promised solutions map back to raw `EOPL` violations** (handling both promised and
failed-promise instances of `(n, P, S, V)`). -/
theorem endOfPotentialLineViolationRel_normalizedViolationBack
    (hP : ∀ u, u.length = n a → (P (a, u)).length = n a)
    (h : endOfPotentialLinePromisedRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a w) :
    endOfPotentialLineViolationRel n P S V a (normalizedViolationBack n P S V (a, w)) :=
  endOfPotentialLineViolationRel_potentialLineBack hP
    (endOfPotentialLineRel_tail_of_promised_normalized h)

/-- **Normalized promised sink solutions map back to raw `SOPL` violations** (handling both promised
and failed-promise instances of `(n, P, S, V)`). -/
theorem sinkOfPotentialLineViolationRel_normalizedViolationBack
    (h : sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V) a w) :
    sinkOfPotentialLineViolationRel n P S V a (normalizedViolationBack n P S V (a, w)) :=
  sinkOfPotentialLineViolationRel_potentialLineBack
    (sinkOfPotentialLineRel_tail_of_promised_normalized h)

/-- The normalized family is total for `endOfPotentialLinePromisedRel` whenever `S` preserves length
`n a` (no length hypothesis on `P` is needed because `normalizedPotentialPred` uses pruned
`potentialPred` only on active potential-increasing edges). -/
theorem isTotalSearch_endOfPotentialLinePromisedRel_normalized
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    IsTotalSearch (endOfPotentialLinePromisedRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V)) := fun a => by
  obtain ⟨u, hu⟩ := isTotalSearch_endOfPotentialLineRel (P := P) (V := V) hS_len a
  exact ⟨true :: u, endOfPotentialLinePromisedRel_normalized_cons hu⟩

/-- The normalized family is total for `sinkOfPotentialLinePromisedRel` whenever `S` preserves
length `n a`. -/
theorem isTotalSearch_sinkOfPotentialLinePromisedRel_normalized
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    IsTotalSearch (sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n)
      (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
      (normalizedPotential V)) := fun a => by
  obtain ⟨u, hu⟩ := isTotalSearch_sinkOfPotentialLineRel (P := P) (V := V) hS_len a
  exact ⟨true :: u, sinkOfPotentialLinePromisedRel_normalized_cons hu⟩

end NormalizedProperties

/-! ### Polynomial-time computability and `FNP` membership -/

section Computability

variable {enc : α ↪ List Bool} {n : α → ℕ} {P S : α × List Bool → List Bool}
  {V : α × List Bool → ℕ}

attribute [local fun_prop] ComputableInPolyTime.bool_and' ComputableInPolyTime.binary_le'

theorem endOfPotentialLinePromisedRel_mem_FNP
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    endOfPotentialLinePromisedRel n P S V ∈ FNP enc := by
  obtain ⟨p, hp⟩ := (polyBounded hn).exists_polynomial
  refine ⟨⟨p, fun a u h => h.1 ▸ hp a⟩,
    fun x => decide (x.2.length = n x.1 ∧
      ((S (x.1, P x) ≠ x.2 ∧ x.2 ≠ zeroVertex (n x.1)) ∨ P (x.1, S x) ≠ x.2 ∨
        (x.2 ≠ S x ∧ P (x.1, S x) = x.2 ∧ V (x.1, S x) ≤ V x))), ?_, fun a u => ?_⟩
  · fun_prop
  · simp [endOfPotentialLinePromisedRel]

theorem sinkOfPotentialLinePromisedRel_mem_FNP
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    sinkOfPotentialLinePromisedRel n P S V ∈ FNP enc := by
  obtain ⟨p, hp⟩ := (polyBounded hn).exists_polynomial
  refine ⟨⟨p, fun a u h => h.1 ▸ hp a⟩,
    fun x => decide (x.2.length = n x.1 ∧
      (P (x.1, S x) ≠ x.2 ∨
        (x.2 ≠ S x ∧ P (x.1, S x) = x.2 ∧ V (x.1, S x) ≤ V x))), ?_, fun a u => ?_⟩
  · fun_prop
  · simp [sinkOfPotentialLinePromisedRel]

@[fun_prop]
theorem computableInPolyTime_normalizedPotentialWidth
    (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (normalizedPotentialWidth n) enc encUnary := by
  unfold normalizedPotentialWidth
  fun_prop

theorem computableInPolyTime_normalizedPotentialPred
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (normalizedPotentialPred n P S V) (encPair enc encBits) encBits := by
  have hP' := computableInPolyTime_potentialPred hn hP hS hV
  unfold normalizedPotentialPred
  fun_prop

theorem computableInPolyTime_normalizedPotentialSucc
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (normalizedPotentialSucc n P S V) (encPair enc encBits) encBits := by
  have hS' := computableInPolyTime_potentialSucc hn hP hS hV
  unfold normalizedPotentialSucc
  fun_prop

theorem computableInPolyTime_normalizedPotential
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (normalizedPotential V) (encPair enc encBits) encNat := by
  unfold normalizedPotential
  fun_prop

theorem computableInPolyTime_normalizedViolationBack
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ComputableInPolyTime (normalizedViolationBack n P S V) (encPair enc encBits) encBits := by
  have hback := computableInPolyTime_potentialLineBack hn hP hS hV
  unfold normalizedViolationBack
  fun_prop

/-- Explicit unary bit-width bound for `normalizedPotential V`: if `V` is polynomial-time computable
in binary, some unary polynomial-time `m'` (`m a + 1`) bounds `normalizedPotential V (a, w) <
2 ^ m' a` on `{0, 1} ^ (n a + 1)`. -/
theorem exists_normalizedPotentialBound
    (hn : ComputableInPolyTime n enc encUnary)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat) :
    ∃ m' : α → ℕ, ComputableInPolyTime m' enc encUnary ∧
      ∀ a w, w.length = normalizedPotentialWidth n a →
        normalizedPotential V (a, w) < 2 ^ m' a := by
  obtain ⟨m, hm, hB⟩ := exists_potentialBound hn hV
  exact ⟨fun a => m a + 1, by fun_prop, fun a w hw => normalizedPotential_lt_two_pow_succ (hB a) hw⟩

/-! ### `SearchReducible` equivalences and `EOPL` / `SOPL` characterizations -/

/-- `endOfPotentialLineRel` search-reduces to the pure `(R1)/(R2)` relation of its promised-source
normalization via `w ↦ w.tail`. -/
theorem endOfPotentialLineRel_searchReducible_promised_normalized
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    SearchReducible enc enc (endOfPotentialLineRel n P S V)
      (endOfPotentialLinePromisedRel (normalizedPotentialWidth n)
        (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
        (normalizedPotential V)) :=
  .of_isTotalSearch (isTotalSearch_endOfPotentialLinePromisedRel_normalized hS_len)
    ComputableInPolyTime.id' (g := fun p => p.2.tail) (by fun_prop)
    fun _ _ hw => endOfPotentialLineRel_tail_of_promised_normalized hw

/-- The pure `(R1)/(R2)` relation of the promised-source normalization search-reduces back to
`endOfPotentialLineRel` via `u ↦ true :: u`. -/
theorem promised_normalized_searchReducible_endOfPotentialLineRel
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    SearchReducible enc enc
      (endOfPotentialLinePromisedRel (normalizedPotentialWidth n)
        (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
        (normalizedPotential V))
      (endOfPotentialLineRel n P S V) :=
  .of_isTotalSearch (isTotalSearch_endOfPotentialLineRel hS_len)
    ComputableInPolyTime.id' (g := fun p => true :: p.2) (by fun_prop)
    fun _ _ hu => endOfPotentialLinePromisedRel_normalized_cons hu

/-- `sinkOfPotentialLineRel` search-reduces to the pure sink-only `(R1)/(R2)` relation of its
promised-source normalization via `w ↦ w.tail`. -/
theorem sinkOfPotentialLineRel_searchReducible_promised_normalized
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    SearchReducible enc enc (sinkOfPotentialLineRel n P S V)
      (sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n)
        (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
        (normalizedPotential V)) :=
  .of_isTotalSearch (isTotalSearch_sinkOfPotentialLinePromisedRel_normalized hS_len)
    ComputableInPolyTime.id' (g := fun p => p.2.tail) (by fun_prop)
    fun _ _ hw => sinkOfPotentialLineRel_tail_of_promised_normalized hw

/-- The pure sink-only `(R1)/(R2)` relation of the promised-source normalization search-reduces back
to `sinkOfPotentialLineRel` via `u ↦ true :: u`. -/
theorem promised_normalized_searchReducible_sinkOfPotentialLineRel
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    SearchReducible enc enc
      (sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n)
        (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
        (normalizedPotential V))
      (sinkOfPotentialLineRel n P S V) :=
  .of_isTotalSearch (isTotalSearch_sinkOfPotentialLineRel hS_len)
    ComputableInPolyTime.id' (g := fun p => true :: p.2) (by fun_prop)
    fun _ _ hu => sinkOfPotentialLinePromisedRel_normalized_cons hu

/-- Any raw circuit-style `EOPL` violation family (even one violating `LineSourcePromise`)
search-reduces to the pure `(R1)/(R2)` relation of its promised-source normalization via
`normalizedViolationBack`. -/
theorem endOfPotentialLineViolationRel_searchReducible_promised_normalized
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat)
    (hP_len : ∀ a u, u.length = n a → (P (a, u)).length = n a)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    SearchReducible enc enc (endOfPotentialLineViolationRel n P S V)
      (endOfPotentialLinePromisedRel (normalizedPotentialWidth n)
        (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
        (normalizedPotential V)) :=
  .of_isTotalSearch (isTotalSearch_endOfPotentialLinePromisedRel_normalized hS_len)
    ComputableInPolyTime.id' (computableInPolyTime_normalizedViolationBack hn hP hS hV)
    fun a _ hw => endOfPotentialLineViolationRel_normalizedViolationBack (hP_len a) hw

/-- Any raw circuit-style `SOPL` violation family (even one violating `LineSourcePromise`)
search-reduces to the pure sink-only `(R1)/(R2)` relation of its promised-source normalization via
`normalizedViolationBack`. -/
theorem sinkOfPotentialLineViolationRel_searchReducible_promised_normalized
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits)
    (hV : ComputableInPolyTime V (encPair enc encBits) encNat)
    (hS_len : ∀ a u, u.length = n a → (S (a, u)).length = n a) :
    SearchReducible enc enc (sinkOfPotentialLineViolationRel n P S V)
      (sinkOfPotentialLinePromisedRel (normalizedPotentialWidth n)
        (normalizedPotentialPred n P S V) (normalizedPotentialSucc n P S V)
        (normalizedPotential V)) :=
  .of_isTotalSearch (isTotalSearch_sinkOfPotentialLinePromisedRel_normalized hS_len)
    ComputableInPolyTime.id' (computableInPolyTime_normalizedViolationBack hn hP hS hV)
    fun _ _ hw => sinkOfPotentialLineViolationRel_normalizedViolationBack hw

/-- **`EOPL` under the exact promised convention of [Fearnley et al., Definition
9][FearnleyGordonMehtaSavani2020].** A search problem `R` lies in `EOPL` iff it lies in `FNP` and
search-reduces to the pure `(R1)/(R2)` relation `endOfPotentialLinePromisedRel` of a uniform
polynomial-time family satisfying `PromisedPotentialLine` (`P (0 ^ n) = 0 ^ n ≠ S (0 ^ n)` and
`V (0 ^ n) = 0`) on every instance. -/
theorem mem_EOPL_iff_promised {R : α → List Bool → Prop} :
    R ∈ EOPL enc ↔ R ∈ FNP enc ∧
      ∃ (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
        ComputableInPolyTime n enc encUnary ∧
        ComputableInPolyTime P (encPair enc encBits) encBits ∧
        ComputableInPolyTime S (encPair enc encBits) encBits ∧
        ComputableInPolyTime V (encPair enc encBits) encNat ∧
        (∀ a u, u.length = n a → (P (a, u)).length = n a) ∧
        (∀ a u, u.length = n a → (S (a, u)).length = n a) ∧
        (∀ a, PromisedPotentialLine n P S V a) ∧
        SearchReducible enc enc R (endOfPotentialLinePromisedRel n P S V) := by
  constructor
  · rintro ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hred⟩
    exact ⟨hR, normalizedPotentialWidth n, normalizedPotentialPred n P S V,
      normalizedPotentialSucc n P S V, normalizedPotential V,
      computableInPolyTime_normalizedPotentialWidth hn,
      computableInPolyTime_normalizedPotentialPred hn hP hS hV,
      computableInPolyTime_normalizedPotentialSucc hn hP hS hV,
      computableInPolyTime_normalizedPotential hV,
      fun a _ hw => length_normalizedPotentialPred (hP_len a) hw,
      fun a _ hw => length_normalizedPotentialSucc (hS_len a) hw,
      promisedPotentialLine_normalized n P S V,
      hred.trans (endOfPotentialLineRel_searchReducible_promised_normalized hS_len)⟩
  · rintro ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hprom, hred⟩
    refine mem_EOPL_iff_violation.mpr ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len,
      hred.trans (.of_isTotalSearch ?_ ComputableInPolyTime.id' (snd enc encBits)
        fun a _ hw => (endOfPotentialLineViolationRel_iff_promised_of_promise (hprom a).1).mp hw)⟩
    intro a
    obtain ⟨u, hu⟩ := isTotalSearch_endOfPotentialLineRel (P := P) (V := V) hS_len a
    exact ⟨_, endOfPotentialLineViolationRel_potentialLineBack (hP_len a) hu⟩

/-- **`EOPL` under the promised convention with explicit unary potential bit-bound `m`.** Includes
the range bound `V (a, u) < 2 ^ m a` (`{0, …, 2 ^ m - 1}`) of
[Fearnley et al., Definition 9][FearnleyGordonMehtaSavani2020]. -/
theorem mem_EOPL_iff_promised_bounded {R : α → List Bool → Prop} :
    R ∈ EOPL enc ↔ R ∈ FNP enc ∧
      ∃ (n m : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
        ComputableInPolyTime n enc encUnary ∧
        ComputableInPolyTime m enc encUnary ∧
        ComputableInPolyTime P (encPair enc encBits) encBits ∧
        ComputableInPolyTime S (encPair enc encBits) encBits ∧
        ComputableInPolyTime V (encPair enc encBits) encNat ∧
        (∀ a u, u.length = n a → (P (a, u)).length = n a) ∧
        (∀ a u, u.length = n a → (S (a, u)).length = n a) ∧
        (∀ a u, u.length = n a → V (a, u) < 2 ^ m a) ∧
        (∀ a, PromisedPotentialLine n P S V a) ∧
        SearchReducible enc enc R (endOfPotentialLinePromisedRel n P S V) := by
  rw [mem_EOPL_iff_promised]
  constructor
  · rintro ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hprom, hred⟩
    obtain ⟨m, hm, hB⟩ := exists_potentialBound hn hV
    exact ⟨hR, n, m, P, S, V, hn, hm, hP, hS, hV, hP_len, hS_len, hB, hprom, hred⟩
  · rintro ⟨hR, n, _, P, S, V, hn, -, hP, hS, hV, hP_len, hS_len, -, hprom, hred⟩
    exact ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hprom, hred⟩

/-- **`SOPL` under the promised source convention.** A search problem `R` lies in `SOPL` iff it lies
in `FNP` and search-reduces to the pure sink-only relation `sinkOfPotentialLinePromisedRel` of a
uniform polynomial-time family satisfying `PromisedPotentialLine` on every instance. -/
theorem mem_SOPL_iff_promised {R : α → List Bool → Prop} :
    R ∈ SOPL enc ↔ R ∈ FNP enc ∧
      ∃ (n : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
        ComputableInPolyTime n enc encUnary ∧
        ComputableInPolyTime P (encPair enc encBits) encBits ∧
        ComputableInPolyTime S (encPair enc encBits) encBits ∧
        ComputableInPolyTime V (encPair enc encBits) encNat ∧
        (∀ a u, u.length = n a → (P (a, u)).length = n a) ∧
        (∀ a u, u.length = n a → (S (a, u)).length = n a) ∧
        (∀ a, PromisedPotentialLine n P S V a) ∧
        SearchReducible enc enc R (sinkOfPotentialLinePromisedRel n P S V) := by
  constructor
  · rintro ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hred⟩
    exact ⟨hR, normalizedPotentialWidth n, normalizedPotentialPred n P S V,
      normalizedPotentialSucc n P S V, normalizedPotential V,
      computableInPolyTime_normalizedPotentialWidth hn,
      computableInPolyTime_normalizedPotentialPred hn hP hS hV,
      computableInPolyTime_normalizedPotentialSucc hn hP hS hV,
      computableInPolyTime_normalizedPotential hV,
      fun a _ hw => length_normalizedPotentialPred (hP_len a) hw,
      fun a _ hw => length_normalizedPotentialSucc (hS_len a) hw,
      promisedPotentialLine_normalized n P S V,
      hred.trans (sinkOfPotentialLineRel_searchReducible_promised_normalized hS_len)⟩
  · rintro ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hprom, hred⟩
    refine mem_SOPL_iff_violation.mpr ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len,
      hred.trans (.of_isTotalSearch ?_ ComputableInPolyTime.id' (snd enc encBits)
        fun a _ hw => (sinkOfPotentialLineViolationRel_iff_promised_of_promise (hprom a).1).mp hw)⟩
    intro a
    obtain ⟨u, hu⟩ := isTotalSearch_sinkOfPotentialLineRel (P := P) (V := V) hS_len a
    exact ⟨_, sinkOfPotentialLineViolationRel_potentialLineBack hu⟩

/-- **`SOPL` under the promised convention with explicit unary potential bit-bound `m`.** -/
theorem mem_SOPL_iff_promised_bounded {R : α → List Bool → Prop} :
    R ∈ SOPL enc ↔ R ∈ FNP enc ∧
      ∃ (n m : α → ℕ) (P S : α × List Bool → List Bool) (V : α × List Bool → ℕ),
        ComputableInPolyTime n enc encUnary ∧
        ComputableInPolyTime m enc encUnary ∧
        ComputableInPolyTime P (encPair enc encBits) encBits ∧
        ComputableInPolyTime S (encPair enc encBits) encBits ∧
        ComputableInPolyTime V (encPair enc encBits) encNat ∧
        (∀ a u, u.length = n a → (P (a, u)).length = n a) ∧
        (∀ a u, u.length = n a → (S (a, u)).length = n a) ∧
        (∀ a u, u.length = n a → V (a, u) < 2 ^ m a) ∧
        (∀ a, PromisedPotentialLine n P S V a) ∧
        SearchReducible enc enc R (sinkOfPotentialLinePromisedRel n P S V) := by
  rw [mem_SOPL_iff_promised]
  constructor
  · rintro ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hprom, hred⟩
    obtain ⟨m, hm, hB⟩ := exists_potentialBound hn hV
    exact ⟨hR, n, m, P, S, V, hn, hm, hP, hS, hV, hP_len, hS_len, hB, hprom, hred⟩
  · rintro ⟨hR, n, _, P, S, V, hn, -, hP, hS, hV, hP_len, hS_len, -, hprom, hred⟩
    exact ⟨hR, n, P, S, V, hn, hP, hS, hV, hP_len, hS_len, hprom, hred⟩

end Computability

end Cslib.Complexity
