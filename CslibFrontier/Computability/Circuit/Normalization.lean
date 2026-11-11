/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to `Cslib/Computability/Circuit/Normalization.lean`)

public import Cslib.Computability.Circuit.Normalization

/-!
# Projection-aware deduplication

`Program.exists_irredundant_ne_input` strengthens cslib's `Program.exists_irredundant`. Besides
merging gates that compute the same function, it skips gates computing an input projection, so the
rebuilt program has one gate per distinct gate function that is not a projection. Every gate of
the rebuilt program computes the function of some gate of the original.

## Main results

* `Cslib.Circuits.Program.exists_irredundant_ne_input`: a program can be rebuilt with pairwise
  distinct gate functions, none an input projection, each computed by a gate of the original.

## References

This is the deduplication step of [Ilango, Loff and Oliveira][IlangoLoffOliveira2020],
Proposition 14 (pp. 22:21–22:22), generalized to arbitrary signatures and interpretations.

* [R. Ilango, B. Loff and I. C. Oliveira, *NP-Hardness of Circuit Minimization for Multi-Output
  Functions*][IlangoLoffOliveira2020]
-/

public section

namespace Cslib.Circuits

universe v u
variable {σ : Signature.{v}} {U : Type u} {n : ℕ}

/-- **Projection-aware deduplication**, strengthening `Program.exists_irredundant`. A program can
be rebuilt so that its gates compute pairwise distinct functions, none of which is an input
projection, while every wire keeps its value. Each new gate computes the function of some gate of
the original program. -/
theorem Program.exists_irredundant_ne_input {s : ℕ} (p : Program σ n s) (I : Interpretation σ U) :
    ∃ s' ≤ s, ∃ q : Program σ n s', ∃ ρ : Wire.Renaming n s s',
      (∀ x w, q.trace I x (ρ w) = p.trace I x w) ∧ q.Irredundant I ∧
        (∀ t i, q.gateFunction I t ≠ fun x => x i) ∧ ∀ t, ∃ t₀, ρ.gates t₀ = Wire.gate t := by
  induction p with
  | empty =>
      exact ⟨0, le_rfl, .empty, .id, by simp, fun t => t.elim0, fun t => t.elim0,
        fun t => t.elim0⟩
  | @gate s p line ih =>
      obtain ⟨s', hs', q, ρ, hρ, hq, hqin, hρsurj⟩ := ih
      let l := line.mapWires ρ
      have hl (x) : l.eval I x (q.eval I x) = line.eval I x (p.eval I x) :=
        line.eval_mapWires ρ I x x (p.eval I x) (q.eval I x) (hρ x)
      -- A gate computing an input projection, or a function already computed, is skipped.
      have hskip (w : Wire n s') (hw : ∀ x, q.trace I x w = l.eval I x (q.eval I x)) :
          ∃ s'' ≤ s + 1, ∃ q' : Program σ n s'', ∃ ρ' : Wire.Renaming n (s + 1) s'',
            (∀ x w, q'.trace I x (ρ' w) = (p.gate line).trace I x w) ∧ q'.Irredundant I ∧
              (∀ t i, q'.gateFunction I t ≠ fun x => x i) ∧
                ∀ t, ∃ t₀, ρ'.gates t₀ = Wire.gate t := by
        refine ⟨s', by omega, q, ρ.skipLast w, fun x v => ?_, hq, hqin, fun t => ?_⟩
        · refine Wire.lastCases ?_ (fun v => ?_) v
          · simpa [Program.trace] using (hw x).trans (hl x)
          · simpa using hρ x v
        · obtain ⟨t₀, ht₀⟩ := hρsurj t
          exact ⟨t₀.castSucc, by simpa [Wire.Renaming.skipLast] using ht₀⟩
      by_cases hin : ∃ i, (fun x => l.eval I x (q.eval I x)) = fun x => x i
      · obtain ⟨i, hi⟩ := hin
        exact hskip (Wire.input i) fun x => (congrFun hi x).symm
      by_cases hdup : ∃ t, q.gateFunction I t = fun x => l.eval I x (q.eval I x)
      · obtain ⟨t, ht⟩ := hdup
        exact hskip (Wire.gate t) fun x => congrFun ht x
      refine ⟨s' + 1, by omega, q.gate l, ρ.appendLast, fun x v => ?_, ?_, fun t => ?_,
        fun t => ?_⟩
      · refine Wire.lastCases ?_ (fun v => ?_) v
        · simpa [Program.trace] using hl x
        · simpa using hρ x v
      · change Function.Injective ((q.gate l).gateFunction I)
        convert Fin.snoc_injective_of_injective hq hdup using 1
        ext t x
        refine Fin.lastCases ?_ (fun t => ?_) t <;> simp
      · refine Fin.lastCases ?_ (fun t => ?_) t
        · intro i hi
          exact hin ⟨i, by simpa using hi⟩
        · simpa using hqin t
      · refine Fin.lastCases ⟨Fin.last s, by simp [Wire.Renaming.appendLast]⟩ (fun t => ?_) t
        obtain ⟨t₀, ht₀⟩ := hρsurj t
        exact ⟨t₀.castSucc, by simp [Wire.Renaming.appendLast, ht₀]⟩

end Cslib.Circuits
