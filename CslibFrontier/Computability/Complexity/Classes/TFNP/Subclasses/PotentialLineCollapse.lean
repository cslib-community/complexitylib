/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# `EOPL = SOPL ∩ PPAD`

We prove `SOPL ∩ PPAD ⊆ EOPL` and hence, with the easy inclusions `EOPL ⊆ SOPL` and
`EOPL ⊆ PPAD`, the equality `EOPL = SOPL ∩ PPAD`. This is the reduction of
[Göös et al., Section 5, Lemma 4][GoosEtAl2022], `SoPL ⊓ bij-PHP ≤ EoPL`, where we use an
end-of-line instance in place of the bijective pigeonhole instance (the two are interreducible by
[Göös et al., Lemma 1][GoosEtAl2022]), applied directly to the two families that witness the
memberships in `SOPL` and `PPAD`.

## The construction

Fix an instance `a`. Let `(n₁, P₁, S₁, V₁)` be a sink-of-potential-line family with potentials
below `B a` on `{0, 1} ^ (n₁ a)`, and let `(n₂, P₂, S₂)` be an end-of-line family. The combined
end-of-potential-line instance lives on the strings `b :: (y ++ x)` of length `n₂ a + n₁ a + 1`
with `y ∈ {0, 1} ^ (n₂ a)` and `x ∈ {0, 1} ^ (n₁ a)`, and is defined by `soplPpadSucc`,
`soplPpadPred` and `soplPpadPotential`:

* for every `y ≠ 0 ^ (n₂ a)` there is a forward copy `{true} × {y} × {0, 1} ^ (n₁ a)` of the pruned
  graph of `(P₁, S₁, V₁)`, with potential `B a + 1 + V₁ x`, and a reversed copy
  `{false} × {y} × {0, 1} ^ (n₁ a)`, with potential `B a - V₁ x`;
* every proper source `x ≠ 0 ^ (n₁ a)` of the pruned graph gets a bridge
  `(false, y, x) → (true, y, x)` from its reversed copy, which is a sink there, to its forward copy;
* the pigeons `(false, y, 0 ^ (n₁ a))`, i.e. the reversed copies of the distinguished source, are
  sent to the holes `(true, y', 0 ^ (n₁ a))`, i.e. its forward copies, along the end-of-line graph:
  `y' = S₂ y` when `y` has an active outgoing edge, and `y' = y` when `y ≠ 0 ^ (n₂ a)` is isolated
  (this is the reduction from end-of-line to bijective pigeonhole of [Göös et al., Lemma 1]);
* the all-zero string `(false, 0 ^ (n₂ a), 0 ^ (n₁ a))` is the new distinguished source, the node
  `u` of [Göös et al.], and the remaining strings with `y = 0 ^ (n₂ a)` are isolated.

The potential strictly increases along every edge, so no edge is pruned
(`hasPotentialOut_soplPpad`, `hasPotentialIn_soplPpad`). Every end of the combined instance
decodes to a sink of `(n₁, P₁, S₁, V₁)` at `x` or to an end-of-line solution of `(n₂, P₂, S₂)` at
`y` (`soplPpad_end`). Unlike the grid presentation of [Göös et al.], we need no preprocessing that
moves all sources to the first column, because the bridges are attached at every proper source.

## Main definitions

* `Cslib.Complexity.soplPpadSucc`, `Cslib.Complexity.soplPpadPred`,
  `Cslib.Complexity.soplPpadPotential`: the combined end-of-potential-line instance.

## Main results

* `Cslib.Complexity.soplPpad_end`: ends of the combined instance decode to solutions.
* `Cslib.Complexity.mem_EOPL_of_sinkOfPotentialLine_endOfLine`: a problem that reduces, on the same
  instance, to both a sink-of-potential-line family and an end-of-line family is in `EOPL`.
* `Cslib.Complexity.SOPL_inter_PPAD_subset_EOPL`, `Cslib.Complexity.EOPL_eq_SOPL_inter_PPAD`.

The collapses `SOPL = PLS ∩ PPADS` and `EOPL = PLS ∩ PPAD` of
[Göös et al., Theorems 1–2][GoosEtAl2022] combine this reduction with `PLS ∩ PPADS ⊆ SOPL`; see
`CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.SOPLCollapse`.

## References

* [M. Göös, A. Hollender, S. Jain, G. Maystre, W. Pires, R. Robere, R. Tao, *Further Collapses in
  TFNP*][GoosEtAl2022]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type}

/-! ### The combined instance -/

/-- The successor map of the combined instance on `b :: (y ++ x)`: forward copies (`b = true`,
`y ≠ 0`) follow the pruned successor of the sink-of-potential-line family; pigeons
(`b = false`, `x = 0`) follow the end-of-line graph to a hole; reversed copies (`b = false`,
`y ≠ 0`, `x ≠ 0`) follow the pruned predecessor, and proper sources bridge to their forward copy. -/
@[expose] def soplPpadSuccCore (n₁ : α → ℕ) (P₁ S₁ : α × List Bool → List Bool)
    (V₁ : α × List Bool → ℕ) (n₂ : α → ℕ) (P₂ S₂ : α × List Bool → List Bool) (a : α) (b : Bool)
    (y x : List Bool) : List Bool :=
  if b then
    if decide (y = zeroVertex (n₂ a)) then true :: (y ++ x)
    else if hasPotentialOut n₁ P₁ S₁ V₁ a x then true :: (y ++ S₁ (a, x))
    else true :: (y ++ x)
  else if decide (x = zeroVertex (n₁ a)) then
    if hasOut n₂ P₂ S₂ a y then true :: (S₂ (a, y) ++ x)
    else if !decide (y = zeroVertex (n₂ a)) && !hasIn n₂ P₂ S₂ a y then true :: (y ++ x)
    else false :: (y ++ x)
  else if decide (y = zeroVertex (n₂ a)) then false :: (y ++ x)
  else if hasPotentialIn n₁ P₁ S₁ V₁ a x then false :: (y ++ P₁ (a, x))
  else if hasPotentialOut n₁ P₁ S₁ V₁ a x then true :: (y ++ x)
  else false :: (y ++ x)

/-- The predecessor map of the combined instance on `b :: (y ++ x)`, inverse to
`soplPpadSuccCore` on its edges. -/
@[expose] def soplPpadPredCore (n₁ : α → ℕ) (P₁ S₁ : α × List Bool → List Bool)
    (V₁ : α × List Bool → ℕ) (n₂ : α → ℕ) (P₂ S₂ : α × List Bool → List Bool) (a : α) (b : Bool)
    (y x : List Bool) : List Bool :=
  if b then
    if decide (y = zeroVertex (n₂ a)) then true :: (y ++ x)
    else if decide (x = zeroVertex (n₁ a)) then
      if hasIn n₂ P₂ S₂ a y then false :: (P₂ (a, y) ++ x)
      else if !hasOut n₂ P₂ S₂ a y then false :: (y ++ x)
      else true :: (y ++ x)
    else if hasPotentialIn n₁ P₁ S₁ V₁ a x then true :: (y ++ P₁ (a, x))
    else if hasPotentialOut n₁ P₁ S₁ V₁ a x then false :: (y ++ x)
    else true :: (y ++ x)
  else if decide (y = zeroVertex (n₂ a)) then false :: (y ++ x)
  else if hasPotentialOut n₁ P₁ S₁ V₁ a x then false :: (y ++ S₁ (a, x))
  else false :: (y ++ x)

/-- The successor map of the combined instance, reading `b`, `y` and `x` off a string of length
`n₂ a + n₁ a + 1`. -/
@[expose] def soplPpadSucc (n₁ : α → ℕ) (P₁ S₁ : α × List Bool → List Bool) (V₁ : α × List Bool → ℕ)
    (n₂ : α → ℕ) (P₂ S₂ : α × List Bool → List Bool) (p : α × List Bool) : List Bool :=
  soplPpadSuccCore n₁ P₁ S₁ V₁ n₂ P₂ S₂ p.1 (p.2.headD false) (p.2.tail.take (n₂ p.1))
    (p.2.tail.drop (n₂ p.1))

/-- The predecessor map of the combined instance, reading `b`, `y` and `x` off a string of length
`n₂ a + n₁ a + 1`. -/
@[expose] def soplPpadPred (n₁ : α → ℕ) (P₁ S₁ : α × List Bool → List Bool) (V₁ : α × List Bool → ℕ)
    (n₂ : α → ℕ) (P₂ S₂ : α × List Bool → List Bool) (p : α × List Bool) : List Bool :=
  soplPpadPredCore n₁ P₁ S₁ V₁ n₂ P₂ S₂ p.1 (p.2.headD false) (p.2.tail.take (n₂ p.1))
    (p.2.tail.drop (n₂ p.1))

/-- The potential of the combined instance: `B a + 1 + V₁ x` on forward copies and `B a - V₁ x` on
reversed copies, where `B a` bounds `V₁` on `{0, 1} ^ (n₁ a)`. -/
@[expose] def soplPpadPotential (V₁ : α × List Bool → ℕ) (n₂ B : α → ℕ) (p : α × List Bool) : ℕ :=
  if p.2.headD false then B p.1 + 1 + V₁ (p.1, p.2.tail.drop (n₂ p.1))
  else B p.1 - V₁ (p.1, p.2.tail.drop (n₂ p.1))

variable {n₁ n₂ B : α → ℕ} {P₁ S₁ P₂ S₂ : α × List Bool → List Bool} {V₁ : α × List Bool → ℕ}
  {a : α} {b : Bool} {x y : List Bool}

theorem soplPpadSucc_cons (hy : y.length = n₂ a) :
    soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, b :: (y ++ x)) =
      soplPpadSuccCore n₁ P₁ S₁ V₁ n₂ P₂ S₂ a b y x := by
  simp [soplPpadSucc, List.take_left' hy, List.drop_left' hy]

theorem soplPpadPred_cons (hy : y.length = n₂ a) :
    soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, b :: (y ++ x)) =
      soplPpadPredCore n₁ P₁ S₁ V₁ n₂ P₂ S₂ a b y x := by
  simp [soplPpadPred, List.take_left' hy, List.drop_left' hy]

theorem soplPpadPotential_cons (hy : y.length = n₂ a) :
    soplPpadPotential V₁ n₂ B (a, b :: (y ++ x)) =
      if b then B a + 1 + V₁ (a, x) else B a - V₁ (a, x) := by
  simp [soplPpadPotential, List.drop_left' hy]

private theorem zeroVertex_add_add_one (k m : ℕ) :
    zeroVertex (k + m + 1) = false :: (zeroVertex k ++ zeroVertex m) := by
  simp only [zeroVertex, List.replicate_append_replicate, List.replicate_succ]

private theorem cons_append_eq_zeroVertex_iff {k m : ℕ} (hy : y.length = k) :
    b :: (y ++ x) = zeroVertex (k + m + 1) ↔
      b = false ∧ y = zeroVertex k ∧ x = zeroVertex m := by
  rw [zeroVertex_add_add_one]
  constructor
  · intro h
    simp only [List.cons.injEq] at h
    exact ⟨h.1, List.append_inj h.2 (by simp [hy])⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem exists_cons_append {k m : ℕ} {w : List Bool} (hw : w.length = k + m + 1) :
    ∃ b y x, w = b :: (y ++ x) ∧ y.length = k ∧ x.length = m := by
  cases w with
  | nil => simp at hw
  | cons b t =>
    refine ⟨b, t.take k, t.drop k, by simp, ?_, ?_⟩ <;>
      simp only [List.length_cons, List.length_take, List.length_drop] at hw ⊢ <;> omega

/-! ### Edges of the combined instance -/

/-- The successor of a moved vertex points back, is not `0 ^ N`, and has a larger potential. -/
private theorem soplPpadSucc_spec (hy : y.length = n₂ a) (hx : x.length = n₁ a)
    (hS₂ : ∀ u, u.length = n₂ a → (S₂ (a, u)).length = n₂ a)
    (hB : ∀ u, u.length = n₁ a → V₁ (a, u) < B a)
    (h : soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, b :: (y ++ x)) ≠ b :: (y ++ x)) :
    soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, b :: (y ++ x))) =
        b :: (y ++ x) ∧
      soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, b :: (y ++ x)) ≠ zeroVertex (n₂ a + n₁ a + 1) ∧
      soplPpadPotential V₁ n₂ B (a, b :: (y ++ x)) <
        soplPpadPotential V₁ n₂ B (a, soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, b :: (y ++ x))) := by
  have hBx := hB x hx
  rw [soplPpadSucc_cons hy] at h ⊢
  rw [soplPpadPotential_cons hy]
  cases b
  · simp only [soplPpadSuccCore, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hx0 : x = zeroVertex (n₁ a)
    · have hx0' : decide (x = zeroVertex (n₁ a)) = true := decide_eq_true hx0
      simp only [hx0', ↓reduceIte] at h ⊢
      cases hout : hasOut n₂ P₂ S₂ a y
      · cases hc : (!decide (y = zeroVertex (n₂ a)) && !hasIn n₂ P₂ S₂ a y)
        · simp only [hout, hc, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false] at h
        · simp only [Bool.false_eq_true, ↓reduceIte]
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc
          refine ⟨?_, ?_, ?_⟩
          · rw [soplPpadPred_cons hy]
            simp [soplPpadPredCore, hc.1, hx0, hc.2, hout]
          · rw [ne_eq, cons_append_eq_zeroVertex_iff hy]; simp
          · rw [soplPpadPotential_cons hy]
            simp only [↓reduceIte]
            omega
      · simp only [↓reduceIte]
        obtain ⟨hPS, hSy, hS0⟩ : P₂ (a, S₂ (a, y)) = y ∧ S₂ (a, y) ≠ y ∧
            S₂ (a, y) ≠ zeroVertex (n₂ a) := by
          simpa [hasOut] using hout
        refine ⟨?_, ?_, ?_⟩
        · rw [soplPpadPred_cons (hS₂ y hy)]
          simp [soplPpadPredCore, hS0, hx0, hasIn_of_hasOut hout, hPS]
        · rw [ne_eq, cons_append_eq_zeroVertex_iff (hS₂ y hy)]; simp
        · rw [soplPpadPotential_cons (hS₂ y hy)]
          simp only [↓reduceIte]
          omega
    · have hx0' : decide (x = zeroVertex (n₁ a)) = false := decide_eq_false hx0
      simp only [hx0', Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hy0 : y = zeroVertex (n₂ a)
      · simp [hy0] at h
      · have hy0' : decide (y = zeroVertex (n₂ a)) = false := decide_eq_false hy0
        simp only [hy0', Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hpi : hasPotentialIn n₁ P₁ S₁ V₁ a x
        · cases hpo : hasPotentialOut n₁ P₁ S₁ V₁ a x
          · simp [hpi, hpo] at h
          · simp only [Bool.false_eq_true, ↓reduceIte]
            refine ⟨?_, ?_, ?_⟩
            · rw [soplPpadPred_cons hy]
              simp [soplPpadPredCore, hy0, hx0, hpi, hpo]
            · rw [ne_eq, cons_append_eq_zeroVertex_iff hy]; simp
            · rw [soplPpadPotential_cons hy]
              simp only [↓reduceIte]
              omega
        · simp only [↓reduceIte]
          obtain ⟨hSP, hPx, -, hV⟩ := hasPotentialIn_eq_true_iff.mp hpi
          refine ⟨?_, ?_, ?_⟩
          · rw [soplPpadPred_cons hy]
            simp [soplPpadPredCore, hy0, hasPotentialOut_of_hasPotentialIn hpi, hSP]
          · rw [ne_eq, cons_append_eq_zeroVertex_iff hy]; simp [hy0]
          · rw [soplPpadPotential_cons hy]
            simp only [Bool.false_eq_true, ↓reduceIte]
            omega
  · simp only [soplPpadSuccCore, ↓reduceIte] at h ⊢
    by_cases hy0 : y = zeroVertex (n₂ a)
    · simp [hy0] at h
    · have hy0' : decide (y = zeroVertex (n₂ a)) = false := decide_eq_false hy0
      simp only [hy0', Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hpo : hasPotentialOut n₁ P₁ S₁ V₁ a x
      · simp [hpo] at h
      · simp only [↓reduceIte]
        obtain ⟨hPS, hSx, hS0, hV⟩ := hasPotentialOut_eq_true_iff.mp hpo
        refine ⟨?_, ?_, ?_⟩
        · rw [soplPpadPred_cons hy]
          simp [soplPpadPredCore, hy0, hS0, hasPotentialIn_of_hasPotentialOut hpo, hPS]
        · rw [ne_eq, cons_append_eq_zeroVertex_iff hy]; simp
        · rw [soplPpadPotential_cons hy]
          simp only [↓reduceIte]
          omega

/-- The predecessor of a moved vertex points forward and has a smaller potential. -/
private theorem soplPpadPred_spec (hy : y.length = n₂ a) (hx : x.length = n₁ a)
    (hS₁ : ∀ u, u.length = n₁ a → (S₁ (a, u)).length = n₁ a)
    (hP₂ : ∀ u, u.length = n₂ a → (P₂ (a, u)).length = n₂ a)
    (hB : ∀ u, u.length = n₁ a → V₁ (a, u) < B a)
    (h : soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, b :: (y ++ x)) ≠ b :: (y ++ x)) :
    soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, b :: (y ++ x))) =
        b :: (y ++ x) ∧
      soplPpadPotential V₁ n₂ B (a, soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, b :: (y ++ x))) <
        soplPpadPotential V₁ n₂ B (a, b :: (y ++ x)) := by
  have hBx := hB x hx
  rw [soplPpadPred_cons hy] at h ⊢
  rw [soplPpadPotential_cons hy]
  cases b
  · simp only [soplPpadPredCore, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hy0 : y = zeroVertex (n₂ a)
    · simp [hy0] at h
    · have hy0' : decide (y = zeroVertex (n₂ a)) = false := decide_eq_false hy0
      simp only [hy0', Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hpo : hasPotentialOut n₁ P₁ S₁ V₁ a x
      · simp [hpo] at h
      · simp only [↓reduceIte]
        obtain ⟨hPS, hSx, hS0, hV⟩ := hasPotentialOut_eq_true_iff.mp hpo
        have hBS := hB _ (hS₁ x hx)
        refine ⟨?_, ?_⟩
        · rw [soplPpadSucc_cons hy]
          simp [soplPpadSuccCore, hy0, hS0, hasPotentialIn_of_hasPotentialOut hpo, hPS]
        · rw [soplPpadPotential_cons hy]
          simp only [Bool.false_eq_true, ↓reduceIte]
          omega
  · simp only [soplPpadPredCore, ↓reduceIte] at h ⊢
    by_cases hy0 : y = zeroVertex (n₂ a)
    · simp [hy0] at h
    · have hy0' : decide (y = zeroVertex (n₂ a)) = false := decide_eq_false hy0
      simp only [hy0', Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hx0 : x = zeroVertex (n₁ a)
      · have hx0' : decide (x = zeroVertex (n₁ a)) = true := decide_eq_true hx0
        simp only [hx0', ↓reduceIte] at h ⊢
        cases hin : hasIn n₂ P₂ S₂ a y
        · cases hout : hasOut n₂ P₂ S₂ a y
          · simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte]
            refine ⟨?_, ?_⟩
            · rw [soplPpadSucc_cons hy]
              simp [soplPpadSuccCore, hx0, hy0, hin, hout]
            · rw [soplPpadPotential_cons hy]
              simp only [Bool.false_eq_true, ↓reduceIte]
              omega
          · simp [hin, hout] at h
        · simp only [↓reduceIte]
          obtain ⟨hSP, hPy, -⟩ : S₂ (a, P₂ (a, y)) = y ∧ P₂ (a, y) ≠ y ∧
              y ≠ zeroVertex (n₂ a) := by
            simpa [hasIn] using hin
          refine ⟨?_, ?_⟩
          · rw [soplPpadSucc_cons (hP₂ y hy)]
            simp [soplPpadSuccCore, hx0, hasOut_of_hasIn hin, hSP]
          · rw [soplPpadPotential_cons (hP₂ y hy)]
            simp only [Bool.false_eq_true, ↓reduceIte]
            omega
      · have hx0' : decide (x = zeroVertex (n₁ a)) = false := decide_eq_false hx0
        simp only [hx0', Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hpi : hasPotentialIn n₁ P₁ S₁ V₁ a x
        · cases hpo : hasPotentialOut n₁ P₁ S₁ V₁ a x
          · simp [hpi, hpo] at h
          · simp only [Bool.false_eq_true, ↓reduceIte]
            refine ⟨?_, ?_⟩
            · rw [soplPpadSucc_cons hy]
              simp [soplPpadSuccCore, hy0, hx0, hpi, hpo]
            · rw [soplPpadPotential_cons hy]
              simp only [Bool.false_eq_true, ↓reduceIte]
              omega
        · simp only [↓reduceIte]
          obtain ⟨hSP, hPx, -, hV⟩ := hasPotentialIn_eq_true_iff.mp hpi
          refine ⟨?_, ?_⟩
          · rw [soplPpadSucc_cons hy]
            simp [soplPpadSuccCore, hy0, hasPotentialOut_of_hasPotentialIn hpi, hSP]
          · rw [soplPpadPotential_cons hy]
            simp only [↓reduceIte]
            omega

/-- No edge of the combined instance is pruned: a vertex has a potential-increasing outgoing edge
iff the successor map moves it. -/
theorem hasPotentialOut_soplPpad
    (hS₂ : ∀ u, u.length = n₂ a → (S₂ (a, u)).length = n₂ a)
    (hB : ∀ u, u.length = n₁ a → V₁ (a, u) < B a) {w : List Bool}
    (hw : w.length = n₂ a + n₁ a + 1) :
    hasPotentialOut (fun a => n₂ a + n₁ a + 1) (soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂)
        (soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂) (soplPpadPotential V₁ n₂ B) a w = true ↔
      soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, w) ≠ w := by
  obtain ⟨b, y, x, rfl, hy, hx⟩ := exists_cons_append hw
  rw [hasPotentialOut_eq_true_iff]
  constructor
  · exact fun h => h.2.1
  · intro h
    obtain ⟨h₁, h₂, h₃⟩ := soplPpadSucc_spec hy hx hS₂ hB h
    exact ⟨h₁, h, h₂, h₃⟩

/-- No edge of the combined instance is pruned: a vertex has a potential-increasing incoming edge
iff the predecessor map moves it. -/
theorem hasPotentialIn_soplPpad
    (hS₁ : ∀ u, u.length = n₁ a → (S₁ (a, u)).length = n₁ a)
    (hP₂ : ∀ u, u.length = n₂ a → (P₂ (a, u)).length = n₂ a)
    (hB : ∀ u, u.length = n₁ a → V₁ (a, u) < B a) {w : List Bool}
    (hw : w.length = n₂ a + n₁ a + 1) :
    hasPotentialIn (fun a => n₂ a + n₁ a + 1) (soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂)
        (soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂) (soplPpadPotential V₁ n₂ B) a w = true ↔
      soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, w) ≠ w := by
  obtain ⟨b, y, x, rfl, hy, hx⟩ := exists_cons_append hw
  rw [hasPotentialIn_eq_true_iff]
  constructor
  · exact fun h => h.2.1
  · intro h
    obtain ⟨h₁, h₂⟩ := soplPpadPred_spec hy hx hS₁ hP₂ hB h
    refine ⟨h₁, h, ?_, h₂⟩
    rw [ne_eq, cons_append_eq_zeroVertex_iff hy]
    rintro ⟨rfl, rfl, rfl⟩
    rw [soplPpadPred_cons hy] at h
    simp [soplPpadPredCore] at h

/-- **Ends of the combined instance decode to solutions** [Göös et al., Lemma 4][GoosEtAl2022]:
an end `b :: (y ++ x)` of the combined end-of-potential-line instance yields a sink of the
sink-of-potential-line family at `x` or an end-of-line solution at `y`. -/
theorem soplPpad_end
    (hS₁ : ∀ u, u.length = n₁ a → (S₁ (a, u)).length = n₁ a)
    (hP₂ : ∀ u, u.length = n₂ a → (P₂ (a, u)).length = n₂ a)
    (hS₂ : ∀ u, u.length = n₂ a → (S₂ (a, u)).length = n₂ a)
    (hB : ∀ u, u.length = n₁ a → V₁ (a, u) < B a) (hy : y.length = n₂ a) (hx : x.length = n₁ a)
    (h : endOfPotentialLineRel (fun a => n₂ a + n₁ a + 1) (soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂)
      (soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂) (soplPpadPotential V₁ n₂ B) a (b :: (y ++ x))) :
    sinkOfPotentialLineRel n₁ P₁ S₁ V₁ a x ∨ endOfLineRel n₂ P₂ S₂ a y := by
  have hw : (b :: (y ++ x)).length = n₂ a + n₁ a + 1 := by simp [hy, hx]
  have e_in : hasPotentialIn (fun a => n₂ a + n₁ a + 1) (soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂)
      (soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂) (soplPpadPotential V₁ n₂ B) a (b :: (y ++ x)) =
      decide (soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, b :: (y ++ x)) ≠ b :: (y ++ x)) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hasPotentialIn_soplPpad hS₁ hP₂ hB hw
  have e_out : hasPotentialOut (fun a => n₂ a + n₁ a + 1) (soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂)
      (soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂) (soplPpadPotential V₁ n₂ B) a (b :: (y ++ x)) =
      decide (soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, b :: (y ++ x)) ≠ b :: (y ++ x)) := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hasPotentialOut_soplPpad hS₂ hB hw
  obtain ⟨-, h⟩ := h
  rw [e_in, e_out, soplPpadPred_cons hy, soplPpadSucc_cons hy] at h
  simp only [ne_eq, cons_append_eq_zeroVertex_iff hy] at h
  have f₁ : hasPotentialOut n₁ P₁ S₁ V₁ a x = true → S₁ (a, x) ≠ x :=
    fun h => (hasPotentialOut_eq_true_iff.mp h).2.1
  have f₂ : hasPotentialIn n₁ P₁ S₁ V₁ a x = true → P₁ (a, x) ≠ x :=
    fun h => (hasPotentialIn_eq_true_iff.mp h).2.1
  have f₃ : hasOut n₂ P₂ S₂ a y = true → S₂ (a, y) ≠ y := fun h => by
    simp only [hasOut, decide_eq_true_eq] at h; exact h.2.1
  have f₄ : hasIn n₂ P₂ S₂ a y = true → P₂ (a, y) ≠ y := fun h => by
    simp only [hasIn, decide_eq_true_eq] at h; exact h.2.1
  -- The case split covers every end type. `0 ^ N` without an outgoing edge means `0 ^ (n₂ a)` has
  -- none in the end-of-line graph. A sink of a forward copy is a sink at `x`. A source of a
  -- reversed copy is a sink at `x`, since proper sources are bridged. A forward copy of the
  -- distinguished source without a pigeon is a proper source `y` of the end-of-line graph. A
  -- pigeon without a hole is a sink `y`. All other strings with `y = 0 ^ (n₂ a)` are isolated.
  unfold sinkOfPotentialLineRel endOfLineRel
  cases b <;> by_cases hy0 : y = zeroVertex (n₂ a) <;> by_cases hx0 : x = zeroVertex (n₁ a) <;>
    cases hpo : hasPotentialOut n₁ P₁ S₁ V₁ a x <;> cases hpi : hasPotentialIn n₁ P₁ S₁ V₁ a x <;>
    cases hout : hasOut n₂ P₂ S₂ a y <;> cases hin : hasIn n₂ P₂ S₂ a y <;>
    simp_all [soplPpadSuccCore, soplPpadPredCore]

/-! ### Lengths and polynomial-time computability -/

theorem length_soplPpadSucc
    (hP₁ : ∀ u, u.length = n₁ a → (P₁ (a, u)).length = n₁ a)
    (hS₁ : ∀ u, u.length = n₁ a → (S₁ (a, u)).length = n₁ a)
    (hS₂ : ∀ u, u.length = n₂ a → (S₂ (a, u)).length = n₂ a) {w : List Bool}
    (hw : w.length = n₂ a + n₁ a + 1) :
    (soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, w)).length = n₂ a + n₁ a + 1 := by
  obtain ⟨b, y, x, rfl, hy, hx⟩ := exists_cons_append hw
  rw [soplPpadSucc_cons hy]
  unfold soplPpadSuccCore
  split_ifs <;> simp [hx, hy, hP₁ x hx, hS₁ x hx, hS₂ y hy]

theorem length_soplPpadPred
    (hP₁ : ∀ u, u.length = n₁ a → (P₁ (a, u)).length = n₁ a)
    (hS₁ : ∀ u, u.length = n₁ a → (S₁ (a, u)).length = n₁ a)
    (hP₂ : ∀ u, u.length = n₂ a → (P₂ (a, u)).length = n₂ a) {w : List Bool}
    (hw : w.length = n₂ a + n₁ a + 1) :
    (soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂ (a, w)).length = n₂ a + n₁ a + 1 := by
  obtain ⟨b, y, x, rfl, hy, hx⟩ := exists_cons_append hw
  rw [soplPpadPred_cons hy]
  unfold soplPpadPredCore
  split_ifs <;> simp [hx, hy, hP₁ x hx, hS₁ x hx, hP₂ y hy]

section Computability

variable {enc : α ↪ List Bool}

attribute [local fun_prop] ComputableInPolyTime.bool_and'

theorem computableInPolyTime_soplPpadSucc
    (hn₁ : ComputableInPolyTime n₁ enc encUnary)
    (hP₁ : ComputableInPolyTime P₁ (encPair enc encBits) encBits)
    (hS₁ : ComputableInPolyTime S₁ (encPair enc encBits) encBits)
    (hV₁ : ComputableInPolyTime V₁ (encPair enc encBits) encNat)
    (hn₂ : ComputableInPolyTime n₂ enc encUnary)
    (hP₂ : ComputableInPolyTime P₂ (encPair enc encBits) encBits)
    (hS₂ : ComputableInPolyTime S₂ (encPair enc encBits) encBits) :
    ComputableInPolyTime (soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂) (encPair enc encBits) encBits := by
  unfold soplPpadSucc soplPpadSuccCore
  fun_prop

theorem computableInPolyTime_soplPpadPred
    (hn₁ : ComputableInPolyTime n₁ enc encUnary)
    (hP₁ : ComputableInPolyTime P₁ (encPair enc encBits) encBits)
    (hS₁ : ComputableInPolyTime S₁ (encPair enc encBits) encBits)
    (hV₁ : ComputableInPolyTime V₁ (encPair enc encBits) encNat)
    (hn₂ : ComputableInPolyTime n₂ enc encUnary)
    (hP₂ : ComputableInPolyTime P₂ (encPair enc encBits) encBits)
    (hS₂ : ComputableInPolyTime S₂ (encPair enc encBits) encBits) :
    ComputableInPolyTime (soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂) (encPair enc encBits) encBits := by
  unfold soplPpadPred soplPpadPredCore
  fun_prop

theorem computableInPolyTime_soplPpadPotential
    (hV₁ : ComputableInPolyTime V₁ (encPair enc encBits) encNat)
    (hn₂ : ComputableInPolyTime n₂ enc encUnary)
    (hB : ComputableInPolyTime B enc encNat) :
    ComputableInPolyTime (soplPpadPotential V₁ n₂ B) (encPair enc encBits) encNat := by
  unfold soplPpadPotential
  fun_prop

end Computability

/-! ### `SOPL ∩ PPAD ⊆ EOPL` -/

section Reduction

variable {enc : α ↪ List Bool} {R : α → List Bool → Prop}

/-- A problem in `FNP` whose solutions can be read back, on the same instance, from the sinks of a
uniform polynomial-time sink-of-potential-line family and from the solutions of a uniform
polynomial-time end-of-line family is in `EOPL` [Göös et al., Lemma 4][GoosEtAl2022]: the back-map
of the combined instance applies `g₁` to `x` if `x` is a sink, and `g₂` to `y` otherwise. -/
theorem mem_EOPL_of_sinkOfPotentialLine_endOfLine (hR : R ∈ FNP enc)
    (hn₁ : ComputableInPolyTime n₁ enc encUnary)
    (hP₁ : ComputableInPolyTime P₁ (encPair enc encBits) encBits)
    (hS₁ : ComputableInPolyTime S₁ (encPair enc encBits) encBits)
    (hV₁ : ComputableInPolyTime V₁ (encPair enc encBits) encNat)
    (hP₁_len : PreservesWidth n₁ P₁) (hS₁_len : PreservesWidth n₁ S₁)
    (hn₂ : ComputableInPolyTime n₂ enc encUnary)
    (hP₂ : ComputableInPolyTime P₂ (encPair enc encBits) encBits)
    (hS₂ : ComputableInPolyTime S₂ (encPair enc encBits) encBits)
    (hP₂_len : PreservesWidth n₂ P₂) (hS₂_len : PreservesWidth n₂ S₂)
    {g₁ g₂ : α × List Bool → List Bool}
    (hg₁ : ComputableInPolyTime g₁ (encPair enc encBits) encBits)
    (hg₂ : ComputableInPolyTime g₂ (encPair enc encBits) encBits)
    (h₁ : ∀ a w, sinkOfPotentialLineRel n₁ P₁ S₁ V₁ a w → R a (g₁ (a, w)))
    (h₂ : ∀ a w, endOfLineRel n₂ P₂ S₂ a w → R a (g₂ (a, w))) :
    R ∈ EOPL enc := by
  obtain ⟨m, hm, hB⟩ := exists_potentialBound hn₁ hV₁
  have hBpt : ComputableInPolyTime (fun a => 2 ^ m a) enc encNat :=
    ComputableInPolyTime.binary_two_pow.comp hm
  have hN : ComputableInPolyTime (fun a => n₂ a + n₁ a + 1) enc encUnary := by fun_prop
  let sinkTest (p : α × List Bool) : Bool :=
    !hasPotentialOut n₁ P₁ S₁ V₁ p.1 (p.2.tail.drop (n₂ p.1)) &&
      (decide (p.2.tail.drop (n₂ p.1) = zeroVertex (n₁ p.1)) ||
        hasPotentialIn n₁ P₁ S₁ V₁ p.1 (p.2.tail.drop (n₂ p.1)))
  let g (p : α × List Bool) : List Bool :=
    if sinkTest p then g₁ (p.1, p.2.tail.drop (n₂ p.1)) else g₂ (p.1, p.2.tail.take (n₂ p.1))
  have hg : ComputableInPolyTime g (encPair enc encBits) encBits := by
    simp only [g, sinkTest]
    fun_prop
  have hSucc_len : PreservesWidth (fun a => n₂ a + n₁ a + 1) (soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂) :=
    fun a _ hw => length_soplPpadSucc (hP₁_len a) (hS₁_len a) (hS₂_len a) hw
  have hPred_len : PreservesWidth (fun a => n₂ a + n₁ a + 1) (soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂) :=
    fun a _ hw => length_soplPpadPred (hP₁_len a) (hS₁_len a) (hP₂_len a) hw
  refine ⟨hR, fun a => n₂ a + n₁ a + 1, soplPpadPred n₁ P₁ S₁ V₁ n₂ P₂ S₂,
    soplPpadSucc n₁ P₁ S₁ V₁ n₂ P₂ S₂, soplPpadPotential V₁ n₂ (fun a => 2 ^ m a), hN,
    computableInPolyTime_soplPpadPred hn₁ hP₁ hS₁ hV₁ hn₂ hP₂ hS₂,
    computableInPolyTime_soplPpadSucc hn₁ hP₁ hS₁ hV₁ hn₂ hP₂ hS₂,
    computableInPolyTime_soplPpadPotential hV₁ hn₂ hBpt, hPred_len, hSucc_len,
    .of_isTotalSearch (isTotalSearch_endOfPotentialLineRel hSucc_len) ComputableInPolyTime.id' hg
      fun a w hw => ?_⟩
  obtain ⟨b, y, x, rfl, hy, hx⟩ := exists_cons_append hw.1
  have hend := soplPpad_end (hS₁_len a) (hP₂_len a) (hS₂_len a) (hB a) hy hx hw
  have hgx : g (a, b :: (y ++ x)) =
      if sinkTest (a, b :: (y ++ x)) then g₁ (a, x) else g₂ (a, y) := by
    simp [g, List.take_left' hy, List.drop_left' hy]
  rw [hgx]
  split_ifs with hc
  · apply h₁
    simp only [sinkTest, List.tail_cons, List.drop_left' hy, Bool.and_eq_true, Bool.not_eq_true',
      Bool.or_eq_true, decide_eq_true_eq] at hc
    exact ⟨hx, hc⟩
  · apply h₂
    refine hend.resolve_left fun hs => hc ?_
    simp only [sinkTest, List.tail_cons, List.drop_left' hy, Bool.and_eq_true, Bool.not_eq_true',
      Bool.or_eq_true, decide_eq_true_eq]
    exact hs.2

/-- **`SOPL ∩ PPAD ⊆ EOPL`** [Göös et al., Section 5][GoosEtAl2022]. -/
theorem SOPL_inter_PPAD_subset_EOPL : SOPL enc ∩ PPAD enc ⊆ EOPL enc := by
  rintro R ⟨⟨hR, n₁, P₁, S₁, V₁, hn₁, hP₁, hS₁, hV₁, hP₁_len, hS₁_len, f₁, g₁, hf₁, hg₁, -, h₁⟩,
    ⟨-, n₂, P₂, S₂, hn₂, hP₂, hS₂, hP₂_len, hS₂_len, f₂, g₂, hf₂, hg₂, -, h₂⟩⟩
  have hpair₁ := (hf₁.comp (.fst enc encBits)).prod (.snd enc encBits)
  have hpair₂ := (hf₂.comp (.fst enc encBits)).prod (.snd enc encBits)
  exact mem_EOPL_of_sinkOfPotentialLine_endOfLine (n₁ := n₁ ∘ f₁)
    (P₁ := fun p => P₁ (f₁ p.1, p.2)) (S₁ := fun p => S₁ (f₁ p.1, p.2))
    (V₁ := fun p => V₁ (f₁ p.1, p.2)) (n₂ := n₂ ∘ f₂) (P₂ := fun p => P₂ (f₂ p.1, p.2))
    (S₂ := fun p => S₂ (f₂ p.1, p.2)) hR (hn₁.comp hf₁) (hP₁.comp hpair₁) (hS₁.comp hpair₁)
    (hV₁.comp hpair₁) (fun a => hP₁_len (f₁ a)) (fun a => hS₁_len (f₁ a)) (hn₂.comp hf₂)
    (hP₂.comp hpair₂) (hS₂.comp hpair₂) (fun a => hP₂_len (f₂ a)) (fun a => hS₂_len (f₂ a)) hg₁
    hg₂ (fun a w hw => h₁ a w hw) (fun a w hw => h₂ a w hw)

/-- **`EOPL = SOPL ∩ PPAD`**: the reduction of [Göös et al., Section 5, Lemma 4][GoosEtAl2022]
(`SOPL_inter_PPAD_subset_EOPL`) together with the easy inclusions `EOPL_subset_SOPL` and
`EOPL_subset_PPAD`. -/
theorem EOPL_eq_SOPL_inter_PPAD : EOPL enc = SOPL enc ∩ PPAD enc :=
  Set.Subset.antisymm (fun _ h => ⟨EOPL_subset_SOPL h, EOPL_subset_PPAD h⟩)
    SOPL_inter_PPAD_subset_EOPL

end Reduction

end Cslib.Complexity
