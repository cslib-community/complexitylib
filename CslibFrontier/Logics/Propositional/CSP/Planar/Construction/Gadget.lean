/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Composition
public import CslibFrontier.Logics.Propositional.CSP.Planar.Construction

/-!
# Executing ordered relation constructions as original-language gadgets

`RelationMinor.Construction.gadget` recursively executes the recorded recipe on actual
primitive-positive bodies. Pins and disequality are interpreted from their enabling trees,
so every constraint uses an original language symbol. Conjunction has disjoint auxiliary
blocks, and projection hides exactly the selected port, preserving survivor order.

This is finite semantic interpretation. The intermediate conjunctions and free-port maps
make no planarity assertion; geometric realization and native reductions are separate.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool} {n : ℕ}

namespace PPGadget

/-- Hide one old free port as the first fresh auxiliary; survivors keep their order. -/
@[expose] def hidePort (j : Fin (n + 1)) : Fin (n + 1) → Fin n ⊕ Fin 1 :=
  j.insertNth (.inr 0) Sum.inl

private theorem hidePort_assignment (j : Fin (n + 1)) (a : Fin n → Bool)
    (z : Fin 1 → Bool) :
    Sum.elim a z ∘ hidePort j = j.insertNth (z 0) a := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩ <;>
    simp [hidePort]

/-- Existential deletion uses `Fin.insertNth`, with one fresh auxiliary before the old block. -/
@[expose] def project {R : Set (Fin (n + 1) → Bool)} (g : PPGadget arity sem R)
    (j : Fin (n + 1)) : PPGadget arity sem (RelationMinor.project R j) :=
  (g.substitute (hidePort j)).retarget fun a => by
    simp only [Set.mem_ofPred_eq, hidePort_assignment, RelationMinor.project]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨fun _ => b, hb⟩
    · rintro ⟨z, hz⟩
      exact ⟨z 0, hz⟩

/-- Identify the first two ports and drop the first, without an equality symbol. -/
@[expose] def equalDrop {R : Set (Fin (n + 2) → Bool)} (g : PPGadget arity sem R) :
    PPGadget arity sem (RelationMinor.adjacent R false) :=
  (g.relabelFree (Fin.cases 0 id)).retarget fun a => by
    change Fin.cons (a 0 ^^ false) a ∈ R ↔ (a ∘ Fin.cases 0 id) ∈ R
    simp only [Bool.xor_false]
    apply Iff.of_eq
    apply congrArg (fun x => x ∈ R)
    funext i
    cases i using Fin.cases <;> rfl

/-- Attach an interpreted disequality constraint to the first pair, then hide its first port. -/
@[expose] def differentDrop {R : Set (Fin (n + 2) → Bool)} (g : PPGadget arity sem R)
    (d : PPGadget arity sem RelationMinor.disequality) :
    PPGadget arity sem (RelationMinor.adjacent R true) :=
  ((g.conj (d.relabelFree ![0, 1])).project 0).retarget fun a => by
    change Fin.cons (a 0 ^^ true) a ∈ R ↔
      ∃ b, Fin.insertNth 0 b a ∈ R ∧
        (Fin.insertNth 0 b a ∘ ![0, 1]) ∈ RelationMinor.disequality
    simp only [Fin.insertNth_zero', RelationMinor.disequality, Set.mem_ofPred_eq,
      Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.cons_zero,
      Bool.xor_true]
    cases ha : a 0 <;> simp [ha]

/-- Attach the constructed pin at the selected coordinate, then hide that coordinate. -/
@[expose] def cofactor {R : Set (Fin (n + 1) → Bool)} (g : PPGadget arity sem R)
    (j : Fin (n + 1)) (b : Bool) (p : PPGadget arity sem (RelationMinor.pin b)) :
    PPGadget arity sem (RelationMinor.cofactor R j b) :=
  ((g.conj (p.relabelFree (fun _ => j))).project j).retarget fun a => by
    change j.insertNth b a ∈ R ↔
      ∃ v, j.insertNth v a ∈ R ∧ (j.insertNth v a ∘ (fun _ => j)) 0 = b
    simp

/-- Move the selected old coordinate to a temporary last free port; all other old ports
keep their indices, cast into the enlarged free block. -/
@[expose] def flipPort (j i : Fin n) : Fin (n + 1) :=
  if i = j then Fin.last n else i.castSucc

/-- Attach constructed disequality between the newly exposed coordinate and the old hidden
coordinate. The temporary last port is then hidden before all existing auxiliaries. -/
@[expose] def flip {R : Set (Fin n → Bool)} (g : PPGadget arity sem R) (j : Fin n)
    (d : PPGadget arity sem RelationMinor.disequality) :
    PPGadget arity sem (RelationMinor.twist R (Pi.single j true)) :=
  (((g.relabelFree (flipPort j)).conj
    (d.relabelFree ![j.castSucc, Fin.last n])).project (Fin.last n)).retarget fun a => by
    change a + Pi.single j true ∈ R ↔ ∃ b,
      (Fin.insertNth (Fin.last n) b a ∘ flipPort j) ∈ R ∧
        (Fin.insertNth (Fin.last n) b a ∘ ![j.castSucc, Fin.last n]) ∈
          RelationMinor.disequality
    have he (b : Bool) : Fin.insertNth (Fin.last n) b a ∘ flipPort j =
        Function.update a j b := by
      funext i
      by_cases hi : i = j
      · subst i
        simp [flipPort]
      · simp [flipPort, hi, Fin.insertNth_last']
    simp only [he]
    simp only [RelationMinor.disequality, Set.mem_ofPred_eq, Function.comp_def,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.insertNth_last',
      Fin.snoc_castSucc, Fin.snoc_last]
    have ht : a + Pi.single j true = Function.update a j (!(a j)) := by
      funext i
      by_cases hi : i = j
      · subst i
        simp [Bool.add_eq_xor]
      · simp [hi]
    rw [ht]
    cases a j <;> simp

end PPGadget

namespace RelationMinor

/-- Execute every node of an ordered construction on actual original-language gadget bodies.
The defining equations retain the operation recipe, including all enabling trees. -/
@[expose] def Construction.gadget {n : ℕ} {R : Set (Fin n → Bool)}
    (c : Construction arity sem R) : PPGadget arity sem R :=
  match c with
  | .atom r => PPGadget.atom r
  | .project c j => c.gadget.project j
  | .equalDrop c => c.gadget.equalDrop
  | .differentDrop c d => c.gadget.differentDrop d.gadget
  | .cofactor c j b p => c.gadget.cofactor j b p.gadget
  | .flip (n := k) (R := S) c j d =>
      (Construction.gadget (n := k) (R := S) c).flip j (Construction.gadget d)
  | .rotate (n := k) (R := S) c =>
      (Construction.gadget (n := k + 1) (R := S) c).relabelFree (fun i => i + 1)
  | .binaryMeet (R := S) (S := T) c d =>
      (Construction.gadget (n := 2) (R := S) c).conj (Construction.gadget (R := T) d)

/-- A finite construction gives an actual gadget over the original language. -/
theorem Available.nonempty_ppGadget {R : Set (Fin n → Bool)} (h : Available arity sem R) :
    Nonempty (PPGadget arity sem R) := h.map Construction.gadget

end RelationMinor
end Cslib.Logic.PL.CSP
