/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Cyclic
import CslibFrontier.Foundations.Data.List.OfFnPositions

/-!
# Positional deletion in the actual ordered boundary word

Cyclic probe transport moves a selected marker to the front, actual edge deletion removes
it, and inverse transport restores the inherited survivor order. The body is unchanged.
Boundary distinctness is explicit and preserved through these constructors. All steps
construct actual checked incidence tables internally; no target-embedding provider is used.
The preprocessing is finite and static, with no uniform runtime assertion.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL

variable {Rel V : Type} [DecidableEq V]

/-- Move the first distinct boundary marker to the end by a positive cyclic shift. -/
noncomputable def Witness.rotateCons {F : CSP Rel V} {p : V} {ports : List V}
    (w : Witness F (p :: ports)) (hn : (p :: ports).Nodup) : Witness F (ports ++ [p]) := by
  let v : Fin (ports.length + 1) → V := Fin.cons p ports.get
  have hword : List.ofFn v = p :: ports := by rw [List.ofFn_cons, List.ofFn_get]
  let wfn : Witness F (List.ofFn v) := ⟨w.certificate, by rw [hword]; exact w.accepted⟩
  let h := wfn.rotateOfFn (by rw [hword]; exact hn)
  have hout : List.ofFn (v ∘ finRotate (ports.length + 1)) = ports ++ [p] := by
    rw [List.ofFn_cons_finRotate, List.ofFn_get]
  refine ⟨h.certificate, ?_⟩
  rw [← hout]
  exact h.accepted

/-- Move the final distinct boundary marker to the front by the inverse cyclic shift. -/
noncomputable def Witness.unrotateSnoc {F : CSP Rel V} {p : V} {ports : List V}
    (w : Witness F (ports ++ [p])) (hn : (ports ++ [p]).Nodup) : Witness F (p :: ports) := by
  let v : Fin (ports.length + 1) → V := Fin.cons p ports.get
  let s := v ∘ finRotate (ports.length + 1)
  have hword : List.ofFn s = ports ++ [p] := by rw [List.ofFn_cons_finRotate, List.ofFn_get]
  let wfn : Witness F (List.ofFn s) := ⟨w.certificate, by rw [hword]; exact w.accepted⟩
  let h := wfn.unrotateOfFn (by rw [hword]; exact hn)
  have hc : s ∘ (finRotate (ports.length + 1)).symm = v := by
    funext j
    exact congrArg v ((finRotate (ports.length + 1)).apply_symm_apply j)
  have hout : List.ofFn (s ∘ (finRotate (ports.length + 1)).symm) = p :: ports := by
    rw [hc, List.ofFn_cons, List.ofFn_get]
  refine ⟨h.certificate, ?_⟩
  rw [← hout]
  exact h.accepted

/-- Delete any selected distinct boundary position, retaining the precise original order
of every survivor. The original body, including closed/nullary components, is unchanged.
The recursion is on the actual valid position; this is static template preprocessing. -/
noncomputable def Witness.forgetAt (k : ℕ) {F : CSP Rel V} {ports : List V}
    (w : Witness F ports) (hn : ports.Nodup) (hk : k < ports.length) :
    Witness F (ports.eraseIdx k) := by
  induction k generalizing ports with
  | zero =>
    cases ports with
    | nil => exact (Nat.not_lt_zero _ hk).elim
    | cons p ports => exact w.forgetHead hn.of_cons
  | succ k ih =>
    cases ports with
    | nil => exact (Nat.not_lt_zero _ hk).elim
    | cons p ports =>
      have hk' : k < ports.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk
      have hnr : (ports ++ [p]).Nodup :=
        hn.perm (List.perm_append_comm (l₁ := [p]) (l₂ := ports))
      let wr := w.rotateCons hn
      let h := ih wr hnr (by simp only [List.length_append, List.length_singleton]; omega)
      have hword : (ports ++ [p]).eraseIdx k = ports.eraseIdx k ++ [p] :=
        List.eraseIdx_append_of_lt_length hk' [p]
      let h' : Witness F (ports.eraseIdx k ++ [p]) :=
        ⟨h.certificate, by rw [← hword]; exact h.accepted⟩
      have hn' : (ports.eraseIdx k ++ [p]).Nodup := by
        rw [← hword]
        exact hnr.eraseIdx k
      exact h'.unrotateSnoc hn'

end Cslib.Complexity.CSP.OrderedBoundary
