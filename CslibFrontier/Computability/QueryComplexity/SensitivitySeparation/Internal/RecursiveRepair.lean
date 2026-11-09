/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveFailures
public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.RecursiveFlips

/-!
# Superquadratic sensitivity separation: recursive repair

Suppose the row clause `i` is false at `x` but becomes true after flipping the single raw bit
`((j, c), a)`. Since the flip only affects the child `(j, c)`, the clause had exactly one failed
condition and the flip repairs it: either `i` is a target candidate, `j = i`, and the flip makes the
final predicate accept the child `(i, c)`, or `i` is a gate candidate, `i → j` is an edge with
`c = label i j`, and the flip makes the gate predicate reject that child. This case analysis drives
the zero-side sensitivity bounds.

## Main results

* `repaired_target_location`: a target child rejected before a repairing flip is the flipped child.
* `repaired_gate_location`: a gate child accepted before a repairing flip is the flipped child.
* `rowClause_repair_cases`: a flip making a false row clause true repairs either its unique failed
  target or its unique failed gate.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/RecursiveRepair.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

/-- If the row clause `i` holds after flipping the bit `((j, c), a)` of `x` and the final predicate
rejects the target child `(i, c')` of `x`, then `(i, c') = (j, c)`. -/
theorem repaired_target_location {k r h : ℕ} {I : Type} [DecidableEq ((Fin k × Fin r) × I)]
    (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c c' : Fin r) (a : I)
    (hf : rowClause T label F q (BitString.flipOn {((j, c), a)} x) i = true)
    (hz : F (Fin.last h) (recursiveChild x i c') = false) : (i, c') = (j, c) := by
  by_contra hne
  have ht := ((rowClause_eq_true_iff T label F q _ i).mp hf).1 c'
  rw [recursiveChild_flip_other x j i c c' a hne, hz] at ht
  exact Bool.false_ne_true ht

/-- If the row clause `i` holds after flipping the bit `((j, c), a)` of `x` and, along an edge
`i → j'`, the gate predicate accepts the child `(j', label i j')` of `x`, then
`(j', label i j') = (j, c)`. -/
theorem repaired_gate_location {k r h : ℕ} {I : Type} [DecidableEq ((Fin k × Fin r) × I)]
    (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j j' : Fin k) (c : Fin r) (a : I)
    (hf : rowClause T label F q (BitString.flipOn {((j, c), a)} x) i = true)
    (hij' : T.Adj i j') (hon : F (gateIndex q) (recursiveChild x j' (label i j')) = true) :
    (j', label i j') = (j, c) := by
  by_contra hne
  have hg := ((rowClause_eq_true_iff T label F q _ i).mp hf).2 j' hij'
  rw [recursiveChild_flip_other x j j' c (label i j') a hne, hon] at hg
  exact Bool.false_ne_true hg.symm

open scoped Classical in
/-- If the row clause `i` is false at `x` but true after flipping `((j, c), a)`, then either `i` is
a target candidate, `j = i`, and the flip changes the final predicate on the child `(j, c)` from
`false` to `true`; or `i` is a gate candidate, `T.Adj i j`, `c = label i j`, and the flip changes
the gate predicate on the child `(j, c)` from `true` to `false`. -/
theorem rowClause_repair_cases {k r h : ℕ} {I : Type} [DecidableEq ((Fin k × Fin r) × I)]
    (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c : Fin r) (a : I)
    (hi : rowClause T label F q x i = false)
    (hf : rowClause T label F q (BitString.flipOn {((j, c), a)} x) i = true) :
    (i ∈ targetCandidates T label F q x ∧ j = i ∧
      F (Fin.last h) (recursiveChild x j c) = false ∧
      F (Fin.last h) (BitString.flipOn {a} (recursiveChild x j c)) = true) ∨
    (i ∈ gateCandidates T label F q x ∧ T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (recursiveChild x j c) = true ∧
      F (gateIndex q) (BitString.flipOn {a} (recursiveChild x j c)) = false) := by
  have hchange : rowClause T label F q (BitString.flipOn {((j, c), a)} x) i ≠
      rowClause T label F q x i := by
    simp [hi, hf]
  rcases rowClause_flip_change T label F q x i j c a hchange with
    ⟨hji, ht⟩ | ⟨hij, rfl, hg⟩
  · subst j
    have hton := ((rowClause_eq_true_iff T label F q _ i).mp hf).1 c
    rw [recursiveChild_flip_same] at hton
    have htoff : F (Fin.last h) (recursiveChild x i c) = false := by grind
    have htargets : targetFailures F x i = {c} := by
      ext c'
      simp only [targetFailures, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hfalse
        exact congrArg Prod.snd (repaired_target_location T label F q x i i c c' a hf hfalse)
      · rintro rfl
        exact htoff
    have hgates : gateFailures T label F q x i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j' hj'
      have h := (Finset.mem_filter.mp hj').2
      have heq := repaired_gate_location T label F q x i i j' c a hf h.1 h.2
      exact T.ne_of_adj h.1 (congrArg Prod.fst heq).symm
    have hmem : i ∈ targetCandidates T label F q x := by
      simp [targetCandidates, htargets, hgates]
    exact Or.inl ⟨hmem, rfl, htoff, hton⟩
  · have hgoff := ((rowClause_eq_true_iff T label F q _ i).mp hf).2 j hij
    rw [recursiveChild_flip_same] at hgoff
    have hgon : F (gateIndex q) (recursiveChild x j (label i j)) = true := by grind
    have htargets : targetFailures F x i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c' hc'
      have heq := repaired_target_location T label F q x i j (label i j) c' a hf
        (Finset.mem_filter.mp hc').2
      exact T.ne_of_adj hij (congrArg Prod.fst heq)
    have hgates : gateFailures T label F q x i = {j} := by
      ext j'
      simp only [gateFailures, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hij', hon⟩
        exact congrArg Prod.fst
          (repaired_gate_location T label F q x i j j' (label i j) a hf hij' hon)
      · rintro rfl
        exact ⟨hij, hgon⟩
    have hmem : i ∈ gateCandidates T label F q x := by
      simp [gateCandidates, htargets, hgates]
    exact Or.inr ⟨hmem, hij, rfl, hgon, hgoff⟩

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
