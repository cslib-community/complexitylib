/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryAppend
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryTransport

/-!
# One-port attachments of actual ordered bodies

Two source bodies with disjoint variable supports meet at exactly one selected boundary
label. Actual probe corners derive the join and cofaciality conditions internally. The
body is the literal append followed by the one-name update; the boundary inserts the
remaining external ports in the selected position. This is not all-port conjunction.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL

variable {Rel V W : Type} [DecidableEq V] [DecidableEq W]

/-- Attach the final port of the external boundary at the selected body port. The original
selected name is replaced by the external name everywhere in the actual appended body.
All other external ports are inserted immediately before the shared boundary marker. -/
noncomputable def Witness.attachAt {F H : CSP Rel V} {left right extra : List V} {x y : V}
    (w : Witness F (left ++ x :: right)) (v : Witness H (extra ++ [y]))
    (f : V → W)
    (hd : List.Disjoint (F.vars ++ (left ++ x :: right)) (H.vars ++ (extra ++ [y])))
    (hn : ((left ++ x :: right) ++ (extra ++ [y])).Nodup)
    (hk : ∀ a ∈ (F.vars ++ (left ++ x :: right)) ++ (H.vars ++ (extra ++ [y])),
      ∀ b ∈ (F.vars ++ (left ++ x :: right)) ++ (H.vars ++ (extra ++ [y])),
        f a = f b ↔ Function.update id x y a = Function.update id x y b)
    (ht : ((left ++ extra ++ y :: right).map f).Nodup) :
    Witness ((F ++ H).relabel f) ((left ++ extra ++ y :: right).map f) := by
  have hnF := (List.nodup_append.mp hn).1
  let wr := w.rotateAppend hnF
  let wr' : Witness F (x :: (right ++ left)) :=
    ⟨wr.certificate, by exact wr.accepted⟩
  have hnrot : (x :: (right ++ left) ++ (extra ++ [y])).Nodup := by
    have h := hn.perm ((List.perm_append_comm (l₁ := left) (l₂ := x :: right)).append_right
      (extra ++ [y]))
    simpa only [List.cons_append, List.append_assoc] using h
  have hdrot : List.Disjoint (F.vars ++ (x :: (right ++ left))) (H.vars ++ (extra ++ [y])) := by
    apply List.disjoint_left.mpr
    intro a ha hb
    have ha' : a ∈ F.vars ++ (left ++ x :: right) := by
      simpa only [List.mem_append, List.mem_cons, or_assoc, or_left_comm, or_comm] using ha
    exact List.disjoint_left.mp hd ha' hb
  let wa := wr'.appendWords v (by simp) (by simp) hdrot hnrot
  let wa' : Witness (F ++ H) ((x :: (right ++ left ++ extra)) ++ [y]) :=
    ⟨wa.certificate, by simpa only [List.cons_append, List.append_assoc] using wa.accepted⟩
  have hna : ((x :: (right ++ left ++ extra)) ++ [y]).Nodup := by
    simpa only [List.cons_append, List.append_assoc] using hnrot
  let wu := wa'.unrotateSnoc hna
  have hnu : (y :: x :: (right ++ left ++ extra)).Nodup := by
    have h := hna.perm (List.perm_append_comm (l₁ := x :: (right ++ left ++ extra)) (l₂ := [y]))
    simpa only [List.singleton_append] using h
  have hni : (((y :: right) ++ (left ++ extra)).map f).Nodup := by
    have h := ht.perm ((List.perm_append_comm (l₁ := left ++ extra) (l₂ := y :: right)).map f)
    exact h
  have hmem (a : V) : a ∈ (F ++ H).vars ++ (y :: x :: (right ++ left ++ extra)) ↔
      a ∈ (F.vars ++ (left ++ x :: right)) ++ (H.vars ++ (extra ++ [y])) := by
    simp only [CSP.vars, List.flatMap_append, List.mem_append, List.mem_cons]
    tauto
  have hxyf : f x = f y := (hk x (by simp) y (by simp)).mpr (by
    simp [Function.update_apply])
  have hmap : (x :: (right ++ left ++ extra)).map f =
      (y :: (right ++ left ++ extra)).map f := by
    simp only [List.map_cons, hxyf]
  let wi := wu.identifyHead f (fun he => (List.nodup_cons.mp hnu).1 (he ▸ List.mem_cons_self))
    (by intro a ha b hb; exact hk a ((hmem a).mp ha) b ((hmem b).mp hb))
    (by rw [hmap]; simpa only [List.cons_append, List.append_assoc] using hni)
  let wi' : Witness ((F ++ H).relabel f)
      ((y :: right).map f ++ (left ++ extra).map f) :=
    ⟨wi.certificate, by
      have hi : verify ((F ++ H).relabel f) ((y :: (right ++ left ++ extra)).map f)
          wi.certificate = true := by rw [← hmap]; exact wi.accepted
      simpa only [List.map_append, List.map_cons, List.append_assoc, List.cons_append] using hi⟩
  let hout := wi'.rotateAppend (by simpa only [List.map_append] using hni)
  exact ⟨hout.certificate, by simpa only [List.map_append] using hout.accepted⟩

/-- Attach disjoint tagged copies of two actual source bodies at one selected port.
The separate tags derive support disjointness, including unused boundary labels. -/
noncomputable def Witness.attachDisjoint {A B : Type} [DecidableEq A] [DecidableEq B]
    {F : CSP Rel A} {H : CSP Rel B} {left right : List A} {extra : List B} {x : A} {y : B}
    (w : Witness F (left ++ x :: right)) (v : Witness H (extra ++ [y]))
    (f : A ⊕ B → W) (hnF : (left ++ x :: right).Nodup) (hnH : (extra ++ [y]).Nodup)
    (hk : ∀ a b, f a = f b ↔
      Function.update id (Sum.inl x) (Sum.inr y) a =
        Function.update id (Sum.inl x) (Sum.inr y) b)
    (ht : (((left.map Sum.inl ++ extra.map Sum.inr) ++
      Sum.inr y :: right.map Sum.inl).map f).Nodup) :
    Witness ((F.relabel Sum.inl ++ H.relabel Sum.inr).relabel f)
      (((left.map Sum.inl ++ extra.map Sum.inr) ++ Sum.inr y :: right.map Sum.inl).map f) := by
  have disjoint (l : List A) (r : List B) :
      List.Disjoint (l.map (Sum.inl : A → A ⊕ B)) (r.map Sum.inr) := by
    apply List.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
    obtain ⟨b, _, he⟩ := List.mem_map.mp hz'
    cases he
  let wtag := w.relabel (Sum.inl : A → A ⊕ B) (fun _ _ _ _ he => Sum.inl.inj he)
  let vtag := v.relabel (Sum.inr : B → A ⊕ B) (fun _ _ _ _ he => Sum.inr.inj he)
  let w' : Witness (F.relabel (Sum.inl : A → A ⊕ B))
      (left.map Sum.inl ++ Sum.inl x :: right.map Sum.inl) :=
    ⟨wtag.certificate, by simpa only [List.map_append, List.map_cons] using wtag.accepted⟩
  let v' : Witness (H.relabel (Sum.inr : B → A ⊕ B)) (extra.map Sum.inr ++ [Sum.inr y]) :=
    ⟨vtag.certificate, by simpa only [List.map_append, List.map_cons, List.map_nil] using
      vtag.accepted⟩
  apply w'.attachAt v' f
  · simpa only [CSP.vars_relabel, List.map_append, List.map_cons, List.map_nil] using
      disjoint (F.vars ++ (left ++ x :: right)) (H.vars ++ (extra ++ [y]))
  · have h := List.nodup_append.mpr
      ⟨hnF.map Sum.inl_injective, hnH.map Sum.inr_injective,
        by
          intro a ha b hb he
          subst b
          exact List.disjoint_left.mp (disjoint (left ++ x :: right) (extra ++ [y])) ha hb⟩
    simpa only [List.map_append, List.map_cons, List.map_nil] using h
  · intro a _ b _
    exact hk a b
  · exact ht

end Cslib.Complexity.CSP.OrderedBoundary
