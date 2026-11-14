/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate (Batteries, `Batteries/Data/Except.lean`)

public import CslibFrontier.Init

/-!
# Sequencing and observing `Except`

Core and Batteries state how `<$>` acts on `Except.ok` and `Except.error`, but not `>>=`, and
nothing about `Except.toOption`, which forgets which error occurred. These equations let `simp`
evaluate `do` blocks over `Except` and compare computations up to the error they raise.

For a list of computations run from left to right, `List.mapM` and `List.filterMapM` succeed
exactly when every step does, and then return the results of the steps; when they fail, some step
failed with the same error. Batteries characterizes the successful results of `List.mapM` by
`List.Forall₂` (`List.mapM_eq_ok_iff_forall₂`); the observations here say the same through
`Except.toOption`, in a form that is stable under permutations and filters of the list.

## Main results

* `Except.ok_bind`, `Except.error_bind`: `>>=` on a result and on an error.
* `Except.bind_eq_ok`: a sequenced computation succeeds when both steps do.
* `Except.toOption_bind`, `Except.toOption_map`: observing success commutes with sequencing.
* `Except.toOption_eq_some_iff`: an observed success is a success.
* `Except.toOption_mapM`, `Except.toOption_filterMapM`: the observation of a list of
  computations.
* `Except.exists_mem_eq_error_of_mapM_eq_error`,
  `Except.exists_mem_eq_error_of_filterMapM_eq_error`: a failing list of computations has a
  failing step.
-/

public section

namespace Except

universe u v

variable {ε : Type u} {α β : Type v}

@[simp] theorem ok_bind (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

@[simp] theorem error_bind (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e := rfl

theorem bind_eq_ok {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp

@[simp] theorem toOption_ok (a : α) : (Except.ok a : Except ε α).toOption = some a := rfl

@[simp] theorem toOption_error (e : ε) : (Except.error e : Except ε α).toOption = none := rfl

theorem toOption_bind (x : Except ε α) (f : α → Except ε β) :
    (x >>= f).toOption = x.toOption.bind fun a => (f a).toOption := by
  cases x <;> rfl

theorem toOption_map (f : α → β) (x : Except ε α) : (f <$> x).toOption = f <$> x.toOption := by
  cases x <;> rfl

theorem toOption_eq_some_iff {x : Except ε α} {a : α} : x.toOption = some a ↔ x = .ok a := by
  cases x <;> simp [Except.toOption]

/-! ### Lists of computations -/

/-- `List.mapM` succeeds exactly when every step succeeds, and then returns their results. -/
theorem toOption_mapM (f : α → Except ε β) (l : List α) :
    (l.mapM f).toOption =
      if ∀ a ∈ l, (f a).toOption.isSome then some (l.filterMap fun a => (f a).toOption)
      else none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases h : f a with e | b
    · simp [h]
    · simp only [List.mapM_cons, h, ok_bind, toOption_bind, ih]
      split_ifs <;> simp_all [pure, Except.pure]

/-- `List.filterMapM` succeeds exactly when every step succeeds, and then keeps the present
results. -/
theorem toOption_filterMapM (f : α → Except ε (Option β)) (l : List α) :
    (l.filterMapM f).toOption =
      if ∀ a ∈ l, (f a).toOption.isSome then some (l.filterMap fun a => (f a).toOption.join)
      else none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases h : f a with e | (_ | b)
    · simp [h]
    · simp only [List.filterMapM_cons, h, ok_bind]
      rw [ih]
      split_ifs <;> simp_all
    · simp only [List.filterMapM_cons, h, ok_bind, toOption_bind, ih]
      split_ifs <;> simp_all [pure, Except.pure]

/-- When `List.mapM` fails, some step fails with that error. -/
theorem exists_mem_eq_error_of_mapM_eq_error {f : α → Except ε β} {l : List α} {e : ε}
    (h : l.mapM f = .error e) : ∃ a ∈ l, f a = .error e := by
  induction l with
  | nil => simp [pure, Except.pure] at h
  | cons a l ih =>
    rcases ha : f a with e' | b
    · simp only [List.mapM_cons, ha, error_bind, error.injEq] at h
      exact ⟨a, by simp, h ▸ ha⟩
    · rcases hl : l.mapM f with e' | bs
      · obtain ⟨a', ha', h'⟩ := ih (by simpa [ha, hl] using h)
        exact ⟨a', by simp [ha'], h'⟩
      · simp [ha, hl, pure, Except.pure] at h

/-- When `List.filterMapM` fails, some step fails with that error. -/
theorem exists_mem_eq_error_of_filterMapM_eq_error {f : α → Except ε (Option β)} {l : List α}
    {e : ε} (h : l.filterMapM f = .error e) : ∃ a ∈ l, f a = .error e := by
  induction l with
  | nil => simp [pure, Except.pure] at h
  | cons a l ih =>
    rcases ha : f a with e' | (_ | b)
    · simp only [List.filterMapM_cons, ha, error_bind, error.injEq] at h
      exact ⟨a, by simp, h ▸ ha⟩
    · obtain ⟨a', ha', h'⟩ := ih (by simpa [ha] using h)
      exact ⟨a', by simp [ha'], h'⟩
    · rcases hl : l.filterMapM f with e' | bs
      · obtain ⟨a', ha', h'⟩ := ih (by simpa [ha, hl] using h)
        exact ⟨a', by simp [ha'], h'⟩
      · simp [ha, hl, pure, Except.pure] at h

end Except
