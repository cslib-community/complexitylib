/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.PPZ
public import Mathlib.GroupTheory.Perm.Fin

/-!
# PPZ rounds in a lazily sampled order

A round of PPZ or PPSZ (`Cslib.Complexity.PPZ.roundWith`) processes the variables in a uniformly
random order, sampled eagerly as a permutation. An implementation samples the order lazily, as in
the Fisher–Yates shuffle: it keeps the unprocessed variables in an array, and at each step it swaps
a uniformly chosen one to the front and processes it.

`Cslib.Complexity.PPZ.roundOn O g τ` processes the variables `g 0, …, g (m - 1)` in a uniformly
random order, starting from the partial assignment `τ`. Choosing the first of them uniformly and
recursing on the others is the same random process
(`Cslib.Complexity.PPZ.roundOn_succ`): after `p` is processed, the array `g` with `g 0` and `g p`
swapped lists the remaining variables from position `1` on. This is the decomposition
`Equiv.Perm.decomposeFin` of a uniform permutation into its value at `0` and a uniform permutation
of the rest. A round is the case of all variables from the empty assignment
(`Cslib.Complexity.PPZ.roundWith_eq_roundOn`).

## Main definitions

* `Cslib.Complexity.PPZ.runList`: process a list of variables in order.
* `Cslib.Complexity.PPZ.roundOn`: process given variables in a uniformly random order.

## Main results

* `Cslib.Complexity.PPZ.runWith_eq_runList`: a run in a fixed order processes the list of its
  values.
* `Cslib.Complexity.PPZ.roundOn_succ`: the lazy, Fisher–Yates form of a uniformly random order.
* `Cslib.Complexity.PPZ.roundWith_eq_roundOn`: a round is `roundOn` on all variables.
-/

@[expose] public section

namespace Cslib.Complexity.PPZ

variable {n : ℕ} (O : (Fin n → Option Bool) → Fin n → Option Bool)

/-- Process the variables of `l` in order with the oracle `O`, starting from `τ`. -/
noncomputable def runList : List (Fin n) → (Fin n → Option Bool) → PMF (Fin n → Option Bool)
  | [], τ => PMF.pure τ
  | x :: l, τ => (stepWith O τ x).bind fun b => runList l (Function.update τ x (some b))

/-- **Process the variables `g 0, …, g (m - 1)` in a uniformly random order** with the oracle `O`,
starting from `τ`. -/
noncomputable def roundOn {m : ℕ} (g : Fin m → Fin n) (τ : Fin n → Option Bool) :
    PMF (Fin n → Option Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin m))).bind fun e =>
    runList O (List.ofFn (g ∘ e)) τ

theorem runList_nil (τ : Fin n → Option Bool) : runList O [] τ = PMF.pure τ := rfl

theorem runList_cons (x : Fin n) (l : List (Fin n)) (τ : Fin n → Option Bool) :
    runList O (x :: l) τ =
      (stepWith O τ x).bind fun b => runList O l (Function.update τ x (some b)) := rfl

/-- Processing one more variable at the end of a list. -/
theorem runList_append_singleton (l : List (Fin n)) (x : Fin n) (τ : Fin n → Option Bool) :
    runList O (l ++ [x]) τ = (runList O l τ).bind fun τ' =>
      (stepWith O τ' x).map fun b => Function.update τ' x (some b) := by
  induction l generalizing τ with
  | nil =>
    simp only [List.nil_append, runList_cons, runList_nil, PMF.pure_bind]
    rfl
  | cons y l ih =>
    simp only [List.cons_append, runList_cons, PMF.bind_bind, ih]

/-- **A run in a fixed order** processes the list of the first `i` values of the order. -/
theorem runWith_eq_runList (π : Equiv.Perm (Fin n)) :
    ∀ {i : ℕ} (hi : i ≤ n), runWith O π i =
      runList O (List.ofFn fun j : Fin i => π (Fin.castLE hi j)) fun _ => none
  | 0, _ => by simp only [runWith_zero, List.ofFn_zero, runList_nil]
  | i + 1, hi => by
    rw [runWith_succ O π (by omega), runWith_eq_runList π (by omega : i ≤ n), List.ofFn_succ',
      List.concat_eq_append, runList_append_singleton]
    rfl

/-- No variables: nothing changes. -/
theorem roundOn_zero (g : Fin 0 → Fin n) (τ : Fin n → Option Bool) :
    roundOn O g τ = PMF.pure τ := by
  simp only [roundOn, List.ofFn_zero, runList_nil, PMF.bind_const]

/-- **The lazy form of a uniformly random order.** Processing `g 0, …, g m` in a uniformly random
order is the same as choosing `p` uniformly, processing `g p`, and then processing the others in a
uniformly random order. The others are listed by `g` after swapping positions `0` and `p`, from
position `1` on. -/
theorem roundOn_succ {m : ℕ} (g : Fin (m + 1) → Fin n) (τ : Fin n → Option Bool) :
    roundOn O g τ = (Cslib.Probability.PMF.uniformOfFintype (Fin (m + 1))).bind fun p =>
      (stepWith O τ (g p)).bind fun b =>
        roundOn O (fun i : Fin m => g (Equiv.swap 0 p i.succ))
          (Function.update τ (g p) (some b)) := by
  have hunif : Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin (m + 1))) =
      (Cslib.Probability.PMF.uniformOfFintype (Fin (m + 1) × Equiv.Perm (Fin m))).map
        Equiv.Perm.decomposeFin.symm :=
    (Cslib.Probability.PMF.uniformOfFintype_map_equiv _).symm
  rw [roundOn, hunif, ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.bind_map, PMF.bind_bind]
  refine congrArg _ (funext fun p => ?_)
  simp only [PMF.bind_map, Function.comp_def, List.ofFn_succ,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    runList_cons, roundOn]
  exact PMF.bind_comm _ _ _

/-- **A round is `roundOn` on all variables** from the empty assignment. -/
theorem roundWith_eq_roundOn : roundWith O = roundOn O id fun _ => none := by
  rw [roundWith, roundOn]
  refine congrArg _ (funext fun π => ?_)
  rw [runWith_eq_runList O π le_rfl]
  rfl

end Cslib.Complexity.PPZ
