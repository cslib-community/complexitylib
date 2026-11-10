/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic

/-!
# Iterating until a test holds, within space

`Turing.MultiTapeTM.ComputableInSpace.iterate` runs a step a computed number of times, and charges
the binary counter. A simulation whose running time is not computable needs a loop that stops when
a test on the state holds instead. Such a loop is computable within the space of the start, of the
rounds and of the states, whatever the number of rounds.

The loop runs on options: a round (`Turing.MultiTapeTM.ComputableInSpace.untilStep`) takes a step
unless the test holds, and then returns `none`, whose encoding is empty. The machine is
`Turing.MultiTapeTM.iterateWhile`, which repeats a round until the empty word.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.iterateWhileSome`: iterating a round on options until it
  returns `none`.
* `Turing.MultiTapeTM.ComputableInSpace.iterateUntil`: iterating a step until a test holds, within
  the space of the start, of the rounds and of the states.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

open BigOLe

variable {α β : Type} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}

section Round

variable [Inhabited β]

/-- A round of the loop: a state that is done ends the loop, any other state takes a step. -/
private def untilStep (step : β → β) (done : β → Bool) (o : Option β) : Option β :=
  if o.isSome && !done (o.getD default) then some (step (o.getD default)) else none

private theorem untilStep_some (step : β → β) (done : β → Bool) (b : β) :
    untilStep step done (some b) = if done b then none else some (step b) := by
  cases h : done b <;> simp [untilStep, h]

private theorem untilStep_none (step : β → β) (done : β → Bool) :
    untilStep step done none = none := by
  simp [untilStep]

private theorem iterate_untilStep (step : β → β) (done : β → Bool) (b : β) {m : ℕ}
    (hm : ∀ j < m, done (step^[j] b) = false) :
    (untilStep step done)^[m] (some b) = some (step^[m] b) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih fun j hj => hm j (by omega), untilStep_some,
      hm m (by omega), Function.iterate_succ_apply']
    rfl

/-- A round of the loop is computable within the space of the step and of the test. -/
private theorem untilStep_inSpace {step : β → β} {done : β → Bool} {Ss Sd : β → ℕ}
    (hstep : ComputableInSpace step encB encB Ss)
    (hdone : ComputableInSpace done encB encBool Sd) :
    ComputableInSpace (untilStep step done) (encOption encB) (encOption encB)
      fun o => (encOption encB o).length + Ss (o.getD default) + Sd (o.getD default) := by
  have hl : (fun o => (encOption encB o).length) ≼
      fun o => (encOption encB o).length + Ss (o.getD default) + Sd (o.getD default) :=
    .of_le fun _ => by omega
  have hget := budget_optionGetD default (budget_id hl)
  have hd := budget_comp hdone hget (.of_le fun _ => by omega)
  have hs := budget_optionSome (budget_comp hstep hget (.of_le fun _ => by omega))
  have hc := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && !p.2)
    (budget_prod (budget_optionIsSome (budget_id hl)) hd)
  exact budget_ite hc hs (budget_const none hl)

end Round

/-- A tidy computation within the space `s`, whose values have length at most `L`, is a
computation within space `O(s + L)`. -/
private theorem of_tidy_space {γ δ : Type} {encC : γ ↪ List Bool} {encD : δ ↪ List Bool} {g : γ → δ}
    {t s : γ → ℕ} (h : ComputableTidilyInTimeAndSpace g encC encD t s) (L : γ → ℕ)
    (hl : ∀ a, (encD (g a)).length ≤ L a) : ComputableInSpace g encC encD fun a => s a + L a :=
  ⟨t, 1, (h.mono (fun _ => le_rfl) fun _ => by dsimp only; omega).computableInTimeAndSpace,
    fun a => (hl a).trans (by dsimp only; omega)⟩

/-- **Iterating a round on options until it returns `none`**, within the space of the start, of
the rounds and of the states. The number of rounds `r x` need not be computable. -/
theorem iterateWhileSome {f : Option β → Option β} {Sf : Option β → ℕ}
    (hf : ComputableInSpace f (encOption encB) (encOption encB) Sf) (hnone : f none = none)
    {start : α → Option β} {Si : α → ℕ}
    (hstart : ComputableInSpace start encIn (encOption encB) Si) {r Q B : α → ℕ}
    (hr : ∀ x, f^[r x + 1] (start x) = none) (hlt : ∀ x, ∀ j ≤ r x, f^[j] (start x) ≠ none)
    (hspace : ∀ x, ∀ j ≤ r x, Sf (f^[j] (start x)) ≤ Q x)
    (hstate : ∀ x, ∀ j ≤ r x, (encOption encB (f^[j] (start x))).length ≤ B x) :
    ComputableInSpace (fun x => f^[r x] (start x)) encIn (encOption encB)
      fun x => Si x + Q x + B x := by
  classical
  obtain ⟨T, c, ⟨k, St, hSt, tm, htm⟩, -⟩ := hf.tidy
  let P : Option β → Prop := fun o => ∃ m, f^[m] o = none
  have hP {o : Option β} (h : P o) : P (f o) := by
    obtain ⟨m, hm⟩ := h
    refine ⟨m, ?_⟩
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hm, hnone]
  let encP : {o // P o} ↪ List Bool := (Function.Embedding.subtype P).trans (encOption encB)
  let F : {o // P o} → {o // P o} := fun d => ⟨f d.1, hP d.2⟩
  have hF : ComputableTidilyInTimeAndSpace F encP encP (fun d => c * (T d.1 + 1))
      fun d => c * (Sf d.1 + 1) := ⟨k, St, hSt, tm, fun d => htm d.1⟩
  have hFit (m : ℕ) (d : {o // P o}) : (F^[m] d).1 = f^[m] d.1 := by
    induction m generalizing d with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
  have hex (d : {o // P o}) : ∃ n, f^[n + 1] d.1 = none := by
    obtain ⟨m, hm⟩ := d.2
    refine ⟨m, ?_⟩
    rw [Function.iterate_succ_apply', hm, hnone]
  let rd : {o // P o} → ℕ := fun d => Nat.find (hex d)
  have hrd (d : {o // P o}) : IsLeast {n | encP (F^[n + 1] d) = []} (rd d) := by
    refine ⟨?_, fun n hn => Nat.find_min' (hex d) ?_⟩
    · change encOption encB (F^[rd d + 1] d).1 = []
      rw [hFit, Nat.find_spec (hex d)]
      rfl
    · change encOption encB (F^[n + 1] d).1 = [] at hn
      rw [hFit] at hn
      exact (encOption encB).injective (hn.trans rfl)
  obtain ⟨d₀, hW⟩ := ComputableTidilyInTimeAndSpace.iterateWhile hF hrd
  have hloop := of_tidy_space hW (fun d => (Finset.Iic (rd d)).sup fun n => (encP (F^[n] d)).length)
    fun d => Finset.le_sup (f := fun n => (encP (F^[n] d)).length) (Finset.mem_Iic.mpr le_rfl)
  have hPs (x : α) : P (start x) := ⟨r x + 1, hr x⟩
  have hstart' : ComputableInSpace (fun x => (⟨start x, hPs x⟩ : {o // P o})) encIn encP Si :=
    hstart.of_enc_eq fun _ => rfl
  have hrx (x : α) : rd ⟨start x, hPs x⟩ = r x := by
    refine le_antisymm (Nat.find_min' _ (hr x)) ?_
    by_contra hlt'
    exact hlt x (rd ⟨start x, hPs x⟩ + 1) (by omega) (Nat.find_spec (hex ⟨start x, hPs x⟩))
  refine ((hloop.comp hstart').of_enc_eq (encC := encOption encB)
    (g := fun x => f^[r x] (start x)) fun x => ?_).weaken ?_
  · change _ = encOption encB (F^[_] _).1
    rw [hFit, hrx]
  refine ⟨d₀ * (c + 1) + 1, fun x => ?_⟩
  dsimp only
  rw [hrx]
  have h₁ : ((Finset.Iic (r x)).sup fun n => c * (Sf (F^[n] ⟨start x, hPs x⟩).1 + 1)) ≤
      c * (Q x + 1) :=
    Finset.sup_le fun n hn => by
      rw [hFit]
      exact Nat.mul_le_mul_left c (Nat.add_le_add_right (hspace x n (Finset.mem_Iic.mp hn)) 1)
  have h₂ : ((Finset.Iic (r x)).sup fun n => (encP (F^[n] ⟨start x, hPs x⟩)).length) ≤ B x :=
    Finset.sup_le fun n hn => by
      change (encOption encB (F^[n] ⟨start x, hPs x⟩).1).length ≤ B x
      rw [hFit]
      exact hstate x n (Finset.mem_Iic.mp hn)
  have h₃ : d₀ * (c * (Q x + 1) + B x + 1) ≤ d₀ * (c + 1) * (Si x + Q x + B x + 1) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left d₀ (by nlinarith)
  have h₄ := Nat.mul_le_mul_left d₀ (Nat.add_le_add_right (Nat.add_le_add h₁ h₂) 1)
  nlinarith

/-- **Iterating a step until a test holds**, within the space of the start, of the rounds and of
the states. The number of steps `n x`, the first at which the test holds, need not be
computable. -/
theorem iterateUntil {init : α → β} {step : β → β} {done : β → Bool} {n : α → ℕ}
    {Si Q B : α → ℕ} {Ss Sd : β → ℕ}
    (hinit : ComputableInSpace init encIn encB Si)
    (hstep : ComputableInSpace step encB encB Ss)
    (hdone : ComputableInSpace done encB encBool Sd)
    (hn : ∀ x, done (step^[n x] (init x)) = true)
    (hlt : ∀ x, ∀ j < n x, done (step^[j] (init x)) = false)
    (hspace : ∀ x, ∀ j ≤ n x, Ss (step^[j] (init x)) + Sd (step^[j] (init x)) ≤ Q x)
    (hstate : ∀ x, ∀ j ≤ n x, (encB (step^[j] (init x))).length ≤ B x) :
    ComputableInSpace (fun x => step^[n x] (init x)) encIn encB fun x => Si x + Q x + B x := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x₀⟩⟩
  · exact (hinit.of_enc_eq (g := fun x => step^[n x] (init x)) fun x => isEmptyElim x).weaken
      ⟨0, fun x => isEmptyElim x⟩
  let : Inhabited β := ⟨init x₀⟩
  have hit (x : α) {j : ℕ} (hj : j ≤ n x) :
      (untilStep step done)^[j] (some (init x)) = some (step^[j] (init x)) :=
    iterate_untilStep step done _ fun i hi => hlt x i (by omega)
  have h := iterateWhileSome (untilStep_inSpace hstep hdone) (untilStep_none step done)
    (budget_optionSome hinit) (r := n) (Q := fun x => Q x + B x + 1) (B := fun x => B x + 1)
    (fun x => by rw [Function.iterate_succ_apply', hit x le_rfl, untilStep_some, hn]; rfl)
    (fun x j hj => by rw [hit x hj]; exact Option.some_ne_none _)
    (fun x j hj => by
      rw [hit x hj]
      have := hspace x j hj
      have := hstate x j hj
      simp only [encOption_some, List.length_cons, Option.getD_some]
      omega)
    (fun x j hj => by
      rw [hit x hj]
      have := hstate x j hj
      simp only [encOption_some, List.length_cons]
      omega)
  refine ((budget_optionGetD default h).of_enc_eq (g := fun x => step^[n x] (init x))
    fun x => ?_).weaken ⟨2, fun x => ?_⟩
  · rw [hit x le_rfl]; rfl
  · dsimp only; omega

end Turing.MultiTapeTM.ComputableInSpace
