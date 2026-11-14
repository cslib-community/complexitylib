/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Defs

/-!
# Data invariants for pointer machines

Data predicates closed under the chosen primitive basis are preserved by execution.
This separates a general data basis from restricted instances such as equality-only symbols.
-/

public section

namespace Cslib.PointerMachine

variable {k : ℕ} {M : Model k} {L : Layout k}

/-- A family of predicates on data, closed under every successful primitive operation. -/
@[expose] def Model.Closed (M : Model k) (P : (t : Fin k) → M.Value t → Prop) : Prop :=
  ∀ {a b c} (f : M.Op a b c) {va vb v},
    P a va → P b vb → M.evalOp f va vb = some v → P c v

/-- All defined data in registers and allocated records satisfy a sort-indexed predicate. -/
@[expose] def State.DataValid (x : State M L) (P : (t : Fin k) → M.Value t → Prop) : Prop :=
  (∀ t i v, x.data t i = some v → P t v) ∧
  (∀ a, x.Allocated a → ∀ t f v, (x.heap a).data t f = some v → P t v)

private theorem data_valid_update {P : (t : Fin k) → M.Value t → Prop}
    {count : Fin k → ℕ} {bank : (t : Fin k) → Fin (count t) → Option (M.Value t)}
    (hbank : ∀ t i v, bank t i = some v → P t v) {t : Fin k} {i : Fin (count t)}
    {v : M.Value t} (hv : P t v) :
    ∀ a j w, Function.update bank t (Function.update (bank t) i (some v)) a j = some w →
      P a w := by
  intro a j w hw
  by_cases h : a = t
  · subst a
    simp only [Function.update_self, Function.update_apply] at hw
    split_ifs at hw <;> grind
  · rw [Function.update_of_ne h] at hw
    exact hbank a j w hw

/-- Closed predicates on data survive every continuing instruction, even if the input's
pointers are invalid: successful memory accesses separately check allocation. -/
theorem Instr.eval_dataValid {P : (t : Fin k) → M.Value t → Prop}
    (closed : M.Closed P) {i : Instr M L} {x y : State M L}
    (hx : x.DataValid P) (h : i.eval x = some y) : y.DataValid P := by
  cases i <;> simp only [Instr.eval, State.access] at h
  all_goals repeat' first
    | simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    | obtain ⟨v, hv, h⟩ := h
    | split at h
    | cases h
  all_goals simp only [State.DataValid, State.setData, Node.setData] at hx ⊢
  all_goals try exact hx
  all_goals constructor
  all_goals first
    | exact hx.1
    | exact hx.2
    | (apply data_valid_update hx.1
       grind [Model.Closed, State.address_eq_some, State.Allocated])
    | (intro a ha t f v hv
       simp only [Function.update_apply] at hv
       split_ifs at hv
       all_goals subst_vars
       all_goals try (simp only [Node.empty] at hv; contradiction)
       all_goals try exact hx.2 a ha t f v hv
       all_goals try
         exact data_valid_update (hx.2 a ha) (by grind) t f v hv
       all_goals apply hx.2 a _ t f v hv
       all_goals grind [State.Allocated, State.fresh, NodeId.below_succ])

/-- Data invariants are preserved through an entire run. -/
theorem Runs.dataValid {P : (t : Fin k) → M.Value t → Prop} (closed : M.Closed P)
    {code : List (Instr M L)} {x y : State M L} {n : ℕ}
    (h : Runs code x y n) (hx : x.DataValid P) : y.DataValid P := by
  induction h with
  | refl => exact hx
  | tail _ _ _ _ hxy ih =>
    obtain ⟨i, _, hi⟩ := step_eq_next_iff.mp hxy
    exact i.eval_dataValid closed ih hi

end Cslib.PointerMachine
