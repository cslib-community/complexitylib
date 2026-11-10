/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.IterateUntil
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitList

/-!
# Evaluating a game of single-bit moves within linear space

A game of single-bit moves is given by three tests on the list of moves played so far, most recent
first: whether the play has ended (`L`), the value of an ended play (`V`), and whether the
existential player moves next (`P`). Its value (`Cslib.Complexity.BitGame.value`) is evaluated
depth first with an explicit stack (`Cslib.Complexity.BitGame.step`): the stack is the current
list of moves, together with the value returned by the last finished subgame. A returned value
that decides the parent ends the parent; otherwise the second move is tried.

When every play ends within `m` moves, the evaluation from the root reaches the value within
`2 ^ (m + 2)` steps and its stack never holds more than `m` moves. So a multi-tape machine
evaluates the game within space linear in the instance, in `m` and in the space of the tests
(`Turing.MultiTapeTM.ComputableInSpace.bitGame_value`). It stops when the root returns, by
`Turing.MultiTapeTM.ComputableInSpace.iterateUntil`, so `m` need not be computable. This is the
evaluation behind the inclusion of alternating time in deterministic space
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Theorem 10.21][Sipser2013]. `Cslib.Complexity.GameTree` evaluates the numerical game
trees of interactive proofs instead, to a fixed depth.

## Main definitions

* `Cslib.Complexity.BitGame.value`: the value of a game, with fuel.
* `Cslib.Complexity.BitGame.step`: a step of the depth-first evaluation.

## Main results

* `Cslib.Complexity.BitGame.iterate_step_eq`: the evaluation from the root reaches the value.
* `Cslib.Complexity.BitGame.value_eq_of_le`: more fuel does not change the value once every play
  has ended.
* `Cslib.Complexity.BitGame.length_iterate_step_le`: the stack holds at most `m` moves.
* `Turing.MultiTapeTM.ComputableInSpace.bitGame_value`: a game is evaluated within space
  linear in the instance, the length of the plays and the space of the tests.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.Complexity.BitGame

variable (L V P : List Bool → Bool)

/-- The value of the game from the reversed moves `u`, with fuel `r`. -/
@[expose] def value : ℕ → List Bool → Bool
  | 0, u => V u
  | r + 1, u => if L u then V u else if P u then value r (false :: u) || value r (true :: u)
    else value r (false :: u) && value r (true :: u)

/-- One step of the depth-first evaluation. -/
def step (s : List Bool × Option Bool) : List Bool × Option Bool :=
  if s.2.isSome then
    if s.1.isEmpty then s
    else if (s.1.headD true == false) && (s.2.getD false != P s.1.tail) then
      (true :: s.1.tail, none)
    else (s.1.tail, s.2)
  else if L s.1 then (s.1, some (V s.1)) else (false :: s.1, none)

variable {L V P}

/-- From a position all of whose plays end within `r` moves, the evaluation returns its value to
the same stack within `2 ^ (r + 2) - 3` steps. -/
theorem iterate_step_value (r : ℕ) (u : List Bool)
    (hL : ∀ v : List Bool, v.length = r → L (v ++ u)) :
    ∃ k, k + 3 ≤ 2 ^ (r + 2) ∧ (step L V P)^[k] (u, none) = (u, some (value L V P r u)) := by
  induction r generalizing u with
  | zero =>
    have := hL [] rfl
    exact ⟨1, by norm_num, by simp_all [step, value]⟩
  | succ r ih =>
    by_cases hu : L u
    · exact ⟨1, by have := Nat.one_le_two_pow (n := r); rw [pow_succ, pow_succ]; omega,
        by simp [step, value, hu]⟩
    obtain ⟨k₀, hk₀, h₀⟩ := ih (false :: u) fun v hv => by
      simpa using hL (v ++ [false]) (by simp [hv])
    obtain ⟨k₁, hk₁, h₁⟩ := ih (true :: u) fun v hv => by
      simpa using hL (v ++ [true]) (by simp [hv])
    have hs : step L V P (u, none) = (false :: u, none) := by simp [step, hu]
    have hpow : 2 ^ (r + 1 + 2) = 2 * 2 ^ (r + 2) := by ring
    by_cases hv : value L V P r (false :: u) = P u
    · refine ⟨1 + (k₀ + 1), by omega, ?_⟩
      simp only [Function.iterate_add_apply, Function.iterate_one, hs, h₀]
      simp only [step, Option.isSome_some, List.isEmpty_cons, List.headD_cons, List.tail_cons,
        Option.getD_some, hv, bne_self_eq_false, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte, value, hu, Prod.mk.injEq, Option.some.injEq, true_and]
      cases P u <;> simp_all
    · refine ⟨1 + (k₁ + (1 + (k₀ + 1))), by omega, ?_⟩
      have h2 : step L V P (false :: u, some (value L V P r (false :: u))) = (true :: u, none) := by
        simp [step, hv]
      simp only [Function.iterate_add_apply, Function.iterate_one, hs, h₀, h2, h₁]
      simp only [step, Option.isSome_some, List.isEmpty_cons, List.headD_cons, List.tail_cons]
      cases hq : P u <;> cases h0 : value L V P r (false :: u) <;> simp_all [value]

/-- A finished evaluation stays finished. -/
theorem step_nil_some (v : Bool) : step L V P ([], some v) = ([], some v) := by
  simp [step]

/-- **The evaluation from the root** reaches the value of the game, and stays there. -/
theorem iterate_step_eq {m N : ℕ} (hL : ∀ v : List Bool, v.length = m → L v)
    (hN : 2 ^ (m + 2) ≤ N) : (step L V P)^[N] ([], none) = ([], some (value L V P m [])) := by
  obtain ⟨k, hk, h⟩ := iterate_step_value (L := L) (V := V) (P := P) m [] (by simpa using hL)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ N by omega)
  rw [Nat.add_comm, Function.iterate_add_apply, h]
  exact Function.iterate_fixed (step_nil_some _) j

/-- More fuel does not change the value once every play of the fuel's length ends. -/
theorem value_eq_of_le {r r' : ℕ} (hr : r ≤ r') (u : List Bool)
    (hL : ∀ v : List Bool, v.length = r → L (v ++ u)) : value L V P r' u = value L V P r u := by
  induction r generalizing r' u with
  | zero =>
    have := hL [] rfl
    cases r' <;> simp_all [value]
  | succ r ih =>
    obtain ⟨r', rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ r' by omega)
    by_cases hu : L u
    · simp [value, hu]
    have h₀ := ih (r' := r') (by omega) (false :: u) fun v hv => by
      simpa using hL (v ++ [false]) (by simp [hv])
    have h₁ := ih (r' := r') (by omega) (true :: u) fun v hv => by
      simpa using hL (v ++ [true]) (by simp [hv])
    simp only [value, hu, h₀, h₁]

/-- The stack of the evaluation never exceeds the length of the longest play. -/
theorem length_iterate_step_le {m : ℕ} (hL : ∀ v : List Bool, v.length = m → L v) (N : ℕ) :
    ((step L V P)^[N] ([], none)).1.length ≤ m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    generalize (step L V P)^[N] ([], none) = s at ih ⊢
    obtain ⟨w, o⟩ := s
    dsimp only at ih
    rcases o with _ | v
    · by_cases hw : L w
      · simpa [step, hw] using ih
      · have : w.length ≠ m := fun h => hw (hL w h)
        simp only [step, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hw,
          List.length_cons]
        omega
    · rcases w with _ | ⟨b, w⟩
      · simp [step]
      · simp only [List.length_cons] at ih
        cases b <;> cases v <;> cases hP : P w <;> simp [step, hP] <;> omega

end Cslib.Complexity.BitGame

namespace Turing.MultiTapeTM.ComputableInSpace

open Cslib.Complexity BigOLe

variable {α : Type} {encIn : α ↪ List Bool}

/-- A step of the evaluation of the game of an instance. -/
private def stepS (L V P : α × List Bool → Bool) (s : α × List Bool × Option Bool) :
    α × List Bool × Option Bool :=
  (s.1, BitGame.step (fun u => L (s.1, u)) (fun u => V (s.1, u)) (fun u => P (s.1, u)) s.2)

private theorem iterate_stepS (L V P : α × List Bool → Bool) (k : ℕ) (x : α)
    (s : List Bool × Option Bool) : (stepS L V P)^[k] (x, s) =
      (x, (BitGame.step (fun u => L (x, u)) (fun u => V (x, u)) (fun u => P (x, u)))^[k] s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]; rfl

private theorem length_encList_encBool (w : List Bool) :
    (encList encBool w).length = 3 * w.length := by
  simp [length_encList, encBool_apply, List.sum_replicate, Nat.mul_comm]

/-- A step of the evaluation is computable within the space of the state and of the tests. -/
private theorem stepS_inSpace {L V P : α × List Bool → Bool} {SL SV SP : α × List Bool → ℕ}
    (hL : ComputableInSpace L (encPair encIn encBits) encBool SL)
    (hV : ComputableInSpace V (encPair encIn encBits) encBool SV)
    (hP : ComputableInSpace P (encPair encIn encBits) encBool SP) :
    ComputableInSpace (stepS L V P) (encPair encIn (encPair (encList encBool) (encOption encBool)))
      (encPair encIn (encPair (encList encBool) (encOption encBool))) fun s =>
        (encPair encIn (encPair (encList encBool) (encOption encBool)) s).length +
          SL (s.1, s.2.1) + SV (s.1, s.2.1) + SP (s.1, s.2.1.tail) := by
  set encS := encPair encIn (encPair (encList encBool) (encOption encBool))
  have hl : (fun s => (encS s).length) ≼ fun s => (encS s).length +
      SL (s.1, s.2.1) + SV (s.1, s.2.1) + SP (s.1, s.2.1.tail) := .of_le fun _ => by omega
  have hid := budget_id hl
  have hx := hid.fst'
  have hw := hid.snd'.fst'
  have ho := hid.snd'.snd'
  have hwb := budget_comp_linear listToBits hw
  have htb := budget_comp_linear listToBits (budget_tail hw)
  have hLx := budget_comp hL (budget_prod hx hwb) (.of_le fun _ => by omega)
  have hVx := budget_comp hV (budget_prod hx hwb) (.of_le fun _ => by omega)
  have hPx := budget_comp hP (budget_prod hx htb) (.of_le fun _ => by omega)
  have hsome := budget_optionIsSome ho
  have hempty := budget_isEmpty hw
  have hhead := budget_headD true hw
  have hget := budget_optionGetD false ho
  have hc := budget_finite (encC := encBool)
    (fun p : Bool × Bool × Bool => (p.1 == false) && (p.2.1 != p.2.2))
    (budget_prod hhead (budget_prod hget hPx))
  have hpush := budget_prod (budget_cons (budget_const true hl) (budget_tail hw))
    (budget_const (encB := encOption encBool) none hl)
  have hpop := budget_prod (budget_tail hw) ho
  have hret := budget_prod hw (budget_optionSome hVx)
  have hdown := budget_prod (budget_cons (budget_const false hl) hw)
    (budget_const (encB := encOption encBool) none hl)
  have hinner := budget_ite hsome (budget_ite hempty (budget_prod hw ho)
    (budget_ite hc hpush hpop)) (budget_ite hLx hret hdown)
  exact budget_prod hx hinner

/-- **A game of single-bit moves is evaluated within linear space.** If every play of an instance
`x` ends, by the leaf test `L`, within `m x` moves, and the leaf test, the value `V` of the leaves
and the player `P` of the positions are computable within the space `Q x` on reversed move lists of
at most `m x` moves, then the value of the game is computable within the space
`O(|x| + m x + Q x)`. The bound `m x` need not be computable. -/
theorem bitGame_value {L V P : α × List Bool → Bool} {SL SV SP : α × List Bool → ℕ}
    (hL : ComputableInSpace L (encPair encIn encBits) encBool SL)
    (hV : ComputableInSpace V (encPair encIn encBits) encBool SV)
    (hP : ComputableInSpace P (encPair encIn encBits) encBool SP) {m Q : α → ℕ}
    (hleaf : ∀ x u, u.length = m x → L (x, u) = true)
    (hspace : ∀ x u, u.length ≤ m x → SL (x, u) + SV (x, u) + SP (x, u) ≤ Q x) :
    ComputableInSpace
      (fun x => BitGame.value (fun u => L (x, u)) (fun u => V (x, u)) (fun u => P (x, u))
        (m x) [])
      encIn encBool fun x => (encIn x).length + m x + Q x := by
  classical
  set encS := encPair encIn (encPair (encList encBool) (encOption encBool))
  let done : α × List Bool × Option Bool → Bool := fun s => s.2.1.isEmpty && s.2.2.isSome
  have hdone : ComputableInSpace done encS encBool fun s => (encS s).length := by
    have hid := budget_id (enc := encS) (S := fun s => (encS s).length) (.refl _)
    exact budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
      (budget_prod (budget_isEmpty hid.snd'.fst') (budget_optionIsSome hid.snd'.snd'))
  have hinit : ComputableInSpace (fun x : α => (x, ([] : List Bool), (none : Option Bool)))
      encIn encS fun x => (encIn x).length := by
    have hl : (fun x => (encIn x).length) ≼ fun x => (encIn x).length := .refl _
    exact budget_prod (budget_id hl) (budget_prod (budget_const [] hl) (budget_const none hl))
  have hN (x : α) := BitGame.iterate_step_eq (L := fun u => L (x, u))
    (V := fun u => V (x, u)) (P := fun u => P (x, u)) (fun v hv => hleaf x v hv)
    (le_refl (2 ^ (m x + 2)))
  have hdN (x : α) : done ((stepS L V P)^[2 ^ (m x + 2)] (x, [], none)) = true := by
    rw [iterate_stepS, hN x]; rfl
  have hex (x : α) : ∃ k, done ((stepS L V P)^[k] (x, [], none)) = true := ⟨_, hdN x⟩
  have hlen (x : α) (j : ℕ) : ((BitGame.step (fun u => L (x, u)) (fun u => V (x, u))
      (fun u => P (x, u)))^[j] ([], none)).1.length ≤ m x :=
    BitGame.length_iterate_step_le (fun v hv => hleaf x v hv) j
  have h := iterateUntil hinit (stepS_inSpace hL hV hP) hdone (n := fun x => Nat.find (hex x))
    (Q := fun x => 2 * (2 * (encIn x).length + 6 * m x + 4) + 2 * Q x)
    (B := fun x => 2 * (encIn x).length + 6 * m x + 4)
    (fun x => Nat.find_spec (hex x))
    (fun x j hj => Bool.eq_false_iff.mpr (Nat.find_min (hex x) hj))
    (fun x j _ => ?_) (fun x j _ => ?_)
  rotate_left
  · rw [iterate_stepS]
    have := hlen x j
    generalize (BitGame.step _ _ _)^[j] ([], none) = s at this ⊢
    obtain ⟨w, o⟩ := s
    dsimp only at this ⊢
    have h₁ := hspace x w this
    have h₂ := hspace x w.tail (by rw [List.length_tail]; omega)
    have h₃ : (encPair encIn (encPair (encList encBool) (encOption encBool)) (x, w, o)).length ≤
        2 * (encIn x).length + 6 * m x + 4 := by
      simp only [length_encPair, length_encList_encBool]
      cases o <;> simp <;> omega
    have h₄ : (encS (x, w, o)).length ≤ 2 * (encIn x).length + 6 * m x + 4 := h₃
    omega
  · rw [iterate_stepS]
    have := hlen x j
    generalize (BitGame.step _ _ _)^[j] ([], none) = s at this ⊢
    obtain ⟨w, o⟩ := s
    dsimp only at this ⊢
    simp only [encS, length_encPair, length_encList_encBool]
    cases o <;> simp <;> omega
  refine ((budget_optionGetD false h.snd'.snd').of_enc_eq fun x => ?_).weaken
    ⟨20, fun x => by dsimp only; omega⟩
  rw [iterate_stepS]
  have hd := Nat.find_spec (hex x)
  have hle : Nat.find (hex x) ≤ 2 ^ (m x + 2) := Nat.find_min' (hex x) (hdN x)
  rw [iterate_stepS] at hd
  obtain ⟨s, hs⟩ : ∃ s, (BitGame.step (fun u => L (x, u)) (fun u => V (x, u))
      (fun u => P (x, u)))^[Nat.find (hex x)] ([], none) = s := ⟨_, rfl⟩
  rw [hs] at hd ⊢
  obtain ⟨_ | ⟨b, w⟩, _ | v⟩ := s <;> simp [done] at hd
  have hfin := hN x
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
  rw [hj, Nat.add_comm, Function.iterate_add_apply, hs,
    Function.iterate_fixed (BitGame.step_nil_some _) j] at hfin
  simp only [Prod.mk.injEq, Option.some.injEq, true_and] at hfin
  rw [hfin]
  rfl

end Turing.MultiTapeTM.ComputableInSpace
