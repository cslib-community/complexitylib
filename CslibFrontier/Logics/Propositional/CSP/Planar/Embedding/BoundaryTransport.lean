/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryIdentify
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryDeletion
import CslibFrontier.Foundations.Data.List.OfFnPositions

/-!
# Exact boundary-word and quotient-label transport

Positive cyclic movement swaps consecutive boundary blocks. Adjacent identification can
then be used on ordinary lists with the exact selected-pair kernel on actual labels.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL

variable {Rel V W : Type} [DecidableEq V] [DecidableEq W]

/-- Move a whole initial block to the end by positive cyclic shifts of the same body. -/
noncomputable def Witness.rotateAppend {F : CSP Rel V} {left right : List V}
    (w : Witness F (left ++ right)) (hn : (left ++ right).Nodup) :
    Witness F (right ++ left) := by
  induction left generalizing right with
  | nil => simpa only [List.nil_append, List.append_nil] using w
  | cons a left ih =>
    let wr := w.rotateCons hn
    have hn' : (left ++ (right ++ [a])).Nodup := by
      have h := hn.perm (List.perm_append_comm (l₁ := [a]) (l₂ := left ++ right))
      simpa only [List.singleton_append, List.append_assoc] using h
    let w' : Witness F (left ++ (right ++ [a])) :=
      ⟨wr.certificate, by
        have hwr : verify F ((left ++ right) ++ [a]) wr.certificate = true := wr.accepted
        rw [List.append_assoc] at hwr
        exact hwr⟩
    let h := ih w' hn'
    exact ⟨h.certificate, by
      simpa only [List.append_assoc, List.singleton_append] using h.accepted⟩

/-- Adjacent identification on a literal list boundary, retaining its mapped tail order. -/
noncomputable def Witness.identifyHead {F : CSP Rel V} {x y : V} {ports : List V}
    (w : Witness F (x :: y :: ports)) (f : V → W) (hxy : x ≠ y)
    (hk : ∀ a ∈ F.vars ++ (x :: y :: ports), ∀ b ∈ F.vars ++ (x :: y :: ports),
      f a = f b ↔ Function.update id y x a = Function.update id y x b)
    (hn : ((y :: ports).map f).Nodup) : Witness (F.relabel f) ((y :: ports).map f) := by
  let v : Fin (ports.length + 2) → V := Fin.cons x (Fin.cons y ports.get)
  have hword : List.ofFn v = x :: y :: ports := by
    rw [List.ofFn_cons, List.ofFn_cons, List.ofFn_get]
  let t : Fin (ports.length + 1) → V := Fin.cons y ports.get
  have htail : List.ofFn (fun i : Fin (ports.length + 1) => f (v i.succ)) =
      (y :: ports).map f := by
    change List.ofFn (f ∘ t) = _
    have htword : List.ofFn t = y :: ports := by
      rw [List.ofFn_cons, List.ofFn_get]
    rw [← List.map_ofFn, htword]
  let w' : Witness F (List.ofFn v) := ⟨w.certificate, by rw [hword]; exact w.accepted⟩
  have hv0 : v 0 = x := rfl
  have hv1 : v 1 = y := rfl
  let h := w'.identifyFirstTwoOfFn f (by exact hxy)
    (by rw [hword, hv0, hv1]; exact hk) (by rw [htail]; exact hn)
  exact ⟨h.certificate, by rw [← htail]; exact h.accepted⟩

end Cslib.Complexity.CSP.OrderedBoundary
