/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Malicious Ideal Wrappers

This module formalizes the malicious ideal execution with abort for general $m$-party
functionalities, generalizing the commitment-specific world from
`CslibFrontier/Crypto/Protocols/MPC/OTCommitment/World.lean`.
It proves the equivalence of explicit abort and wrapper-based abort for ideal functionalities
and formalizes the classic counterexample showing that naive without-abort composition
fails when the adversary can abort, as noted in #3673 M12 (Goldreich).

## Main definitions
* `Cslib.Crypto.Protocols.MPC.maliciousIdeal`: Ideal execution without abort where the adversary
  supplies corrupted inputs, receives their outputs, and produces a view.
* `Cslib.Crypto.Protocols.MPC.maliciousIdealWithAbort`: Ideal execution where the adversary
  supplies corrupted inputs, receives their outputs, and then decides whether to abort or release
  the honest outputs.

## Main results
* `Cslib.Crypto.Protocols.MPC.adversaryAborts_characterization`:
  The equivalence of malicious ideal execution with abort and the adversary-aborts wrapper.
* `Cslib.Crypto.Protocols.MPC.naive_without_abort_failure`: Counterexample to naive without-abort
  composition.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Probability Cslib.ProbComp

/-- Malicious ideal execution without abort. -/
@[expose] public def maliciousIdeal {m : ℕ} {In Out : Fin m → Type} {View : Type}
    (f : Functionality m In Out) (I : Finset (Fin m))
    (x : (i : Fin m) → In i)
    (S : ((i : I) → In i) → ProbComp (((i : I) → In i) × (((i : I) → Out i) → View))) :
    ProbComp (View × ((i : Fin m) → Out i)) := do
  let (x_I_prime, S_out) ← S (I.restrict x)
  let x_prime := fun i => if h : i ∈ I then x_I_prime ⟨i, h⟩ else x i
  let y ← f x_prime
  let v := S_out (I.restrict y)
  return (v, y)

/-- Malicious ideal execution with abort. The adversary `S` provides inputs for `I`,
then given the outputs for `I`, decides whether to continue (`true`) or abort (`false`),
and outputs a view. Honest parties receive `some y` if continue, or `none` if abort. -/
@[expose] public def maliciousIdealWithAbort {m : ℕ} {In Out : Fin m → Type} {View : Type}
    (f : Functionality m In Out) (I : Finset (Fin m))
    (x : (i : Fin m) → In i)
    (S : ((i : I) → In i) → ProbComp (((i : I) → In i) × (((i : I) → Out i) → Bool × View))) :
    ProbComp (View × ((i : Fin m) → Option (Out i))) := do
  let (x_I_prime, S_out) ← S (I.restrict x)
  let x_prime := fun i => if h : i ∈ I then x_I_prime ⟨i, h⟩ else x i
  let y ← f x_prime
  let (cont, v) := S_out (I.restrict y)
  let y_final := fun i => if cont || (i ∈ I) then some (y i) else none
  return (v, y_final)

/-- An adversary-aborts wrapper around a functionality, explicitly modeling the abort phase
within a standard functionality, avoiding the need for a custom ideal execution definition. -/
@[expose] public def adversaryAborts {m : ℕ} {In Out : Fin m → Type}
    (f : Functionality m In Out) (I : Finset (Fin m)) :
    Functionality m (fun i => In i × (i ∈ I → ((j : I) → Out j) → Bool))
      (fun i => Option (Out i)) :=
  fun x => do
    let y ← f (fun i => (x i).1)
    let cont := ∀ i : I, (x i.1).2 i.2 (fun j => y j.1)
    return fun i => if cont || (i ∈ I) then some (y i) else none

@[simp] private theorem fst_dite {α β} (c : Prop) [Decidable c] (t : c → α × β) (e : ¬c → α × β) :
  (if h : c then t h else e h).1 = if h : c then (t h).1 else (e h).1 := by
  split_ifs <;> rfl

@[simp] private theorem snd_dite {α β} (c : Prop) [Decidable c] (t : c → α × β) (e : ¬c → α × β) :
  (if h : c then t h else e h).2 = if h : c then (t h).2 else (e h).2 := by
  split_ifs <;> rfl

private theorem pmf_bind_congr {α β} {p q : PMF α} {f g : α → PMF β} (hpq : p = q)
    (hfg : ∀ x, f x = g x) :
  p.bind f = q.bind g := by
  cases hpq
  congr 1
  funext x
  exact hfg x

/--
The equivalence of malicious ideal execution with abort and the adversary-aborts wrapper.
## References
* Goldreich 2004 (abort equivalence concept)
-/
theorem adversaryAborts_characterization {m : ℕ} {In Out : Fin m → Type} {View : Type}
    [Inhabited View]
    (f : Functionality m In Out) (I : Finset (Fin m)) (hI : I.Nonempty)
    (x : (i : Fin m) → In i)
    (S : ((i : I) → In i) → ProbComp (((i : I) → In i) × (((i : I) → Out i) → Bool × View))) :
    ProbComp.eval (maliciousIdealWithAbort f I x S) =
      ProbComp.eval (maliciousIdeal (adversaryAborts f I) I (fun i => (x i, fun _ _ => true))
        (fun x_I => do
          let (x_I_prime, S_out) ← S (fun i => (x_I i).1)
          return (fun i => (x_I_prime i, fun _ y_I => (S_out y_I).1), fun y_I =>
            if h : ∀ i, (y_I i).isSome then
              (S_out (fun i => Option.get _ (h i))).2
            else default))) := by
  dsimp [maliciousIdealWithAbort, maliciousIdeal, adversaryAborts]
  simp only [fst_dite, eval_bind, eval_pure, PMF.bind_bind, PMF.pure_bind]
  apply pmf_bind_congr
  · rfl
  · intro ⟨x_I_prime, S_out⟩
    apply pmf_bind_congr
    · rfl
    · intro y
      congr 1
      have H_true : ∀ i : I, (decide (∀ i_1 : I,
        ((if ↑i_1 ∈ I then (x_I_prime i_1, fun x y_I => (S_out y_I).1)
          else (x ↑i_1, fun x x_1 => true)).2
          i_1.2 fun j => y ↑j) = true) || decide (↑i ∈ I)) = true := by
        intro i
        have hi := i.2
        simp [hi]
      apply Prod.ext
      · dsimp
        have H_isSome : ∀ i : I, (Finset.restrict I (fun i_1 =>
          if (decide (∀ i_1 : I, ((if ↑i_1 ∈ I then (x_I_prime i_1, fun x y_I => (S_out y_I).1)
            else (x ↑i_1, fun x x_1 => true)).2 i_1.2 fun j => y ↑j) = true)
            || decide (i_1 ∈ I)) = true
          then some (y i_1) else none) i).isSome = true := by
          intro i
          have hi := H_true i
          simp [Finset.restrict]
        simp; rfl
      · ext i
        dsimp
        have h_Sout : ∀ i_1 : I, ((if ↑i_1 ∈ I then (x_I_prime i_1, fun x y_I => (S_out y_I).1)
          else (x ↑i_1, fun x x_1 => true)).2 i_1.2 fun j => y ↑j) = (S_out (I.restrict y)).1 := by
          intro i_1
          have hi1 := i_1.2
          simp [hi1]; rfl
        simp_rw [h_Sout]
        have h_all : (∀ a : I, (S_out (I.restrict y)).1 = true) ↔
          (S_out (I.restrict y)).1 = true := by
          constructor
          · intro h
            rcases hI with ⟨x, hx⟩
            exact h ⟨x, hx⟩
          · intro h _
            exact h
        simp_rw [h_all]
        simp

/-- In the ideal model without abort, the honest party's output is independent
if the functionality provides no output to the adversary. -/
noncomputable def coinTossPrivateFunc : Functionality 2 (fun _ => Unit)
  (fun i => if i = 0 then Unit else Bool) :=
  fun _ => do
    let b ← uniform Bool
    return fun i => if h : i = 0 then cast (by simp [h]) () else cast (by simp [h]) b

/-- The set of corrupted parties containing only party 0. -/
def I0 : Finset (Fin 2) := {0}

/-- The biased coin toss distribution where party 1 aborts on false. -/
noncomputable def coinTossBiasedDist :
  ProbComp (Unit × ((i : Fin 2) → Option (if i = 0 then Unit else Bool))) := do
  let b ← uniform Bool
  if b then
    return ((), fun i => if h : i = 0 then cast (by simp [h]) (some ())
      else cast (by simp [h]) (some true))
  else
    return ((), fun i => if h : i = 0 then cast (by simp [h]) (some ()) else none)
/-- Extracts the boolean from the ideal malicious output. -/
def extractBoolFromMalicious (y : (i : Fin 2) → if i = 0 then Unit else Bool) : Bool :=
  if h : (1:Fin 2) = 0 then true else cast (by simp [h]) (y 1)
/-- Extracts the boolean from the biased output distribution. -/
def extractBoolFromBiased (y : (i : Fin 2) → Option (if i = 0 then Unit else Bool)) : Bool :=
  if h : (1:Fin 2) = 0 then true else
  match y 1 with
  | some v => cast (by simp [h]) v
  | none => true

noncomputable instance iteFintype (i : Fin 2) : Fintype (if i = 0 then Unit else Bool) := by
  split_ifs <;> infer_instance

noncomputable instance iteDecidableEq (i : Fin 2) : DecidableEq (if i = 0 then Unit else Bool) := by
  split_ifs <;> infer_instance

private theorem extractBoolFromMalicious_val (b : Bool) :
  extractBoolFromMalicious (fun i => if h : i = 0 then cast (by simp [h]) ()
    else cast (by simp [h]) b) = b := by
  cases b <;> rfl

private theorem extractBoolFromBiased_val1 :
  extractBoolFromBiased (fun i =>
    if h : i = 0 then cast (by simp [h]) (some ()) else none) = true := rfl

private theorem extractBoolFromBiased_val2 :
  extractBoolFromBiased (fun i =>
    if h : i = 0 then cast (by simp [h]) (some ())
    else cast (by simp [h]) (some true)) = true := rfl

private theorem tsum_ite_eq_and_prop {α : Type} [Fintype α] [DecidableEq α] (A : α) (P : α → Prop)
    [DecidablePred P] (c : ENNReal) :
  (∑' x, if P x then if x = A then c else 0 else 0) = if P A then c else 0 := by
  rw [tsum_fintype]
  have H : (∑ x, if P x then if x = A then c else 0 else 0) =
      ∑ x, if x = A then if P A then c else 0 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases h1 : P x <;> by_cases h2 : x = A
    · subst h2; simp [h1]
    · simp [h1, h2]
    · subst h2; simp [h1]
    · simp [h1, h2]
  rw [H, Finset.sum_ite_eq']
  have H2 : A ∈ Finset.univ := Finset.mem_univ A
  simp [H2]

private theorem ite_tsum_eq_ennreal {β : Type} (P : Prop) [Decidable P] (f : β → ENNReal) :
  (if P then ∑' x, f x else 0) = ∑' x, if P then f x else 0 := by
  split_ifs
  · rfl
  · exact tsum_zero.symm

private theorem ite_mul_eq_ennreal (P : Prop) [Decidable P] (c x : ENNReal) :
  (if P then c * x else 0) = c * (if P then x else 0) := by
  split_ifs
  · rfl
  · exact (mul_zero c).symm

private theorem sum_swap_3 {α β γ : Type} (f : α → β → γ → ENNReal) :
  (∑' (a:α), ∑' (b:β), ∑' (c:γ), f a b c) = ∑' (b:β), ∑' (a:α), ∑' (c:γ), f a b c := by
  rw [tsum_comm]

private theorem inner_sum_eval :
  (∑' (b : Bool), if true = b then (↑(Fintype.card Bool) : ENNReal)⁻¹ else 0) = 1/2 := by
  rw [tsum_fintype, Fintype.sum_bool]
  have h1 : (Fintype.card Bool : ENNReal) = 2 := rfl
  rw [h1]
  simp [one_div]

/-- Counterexample demonstrating the necessity of the abort capability. -/
theorem naive_without_abort_failure :
  ¬ (∃ (S : ((i : I0) → Unit) → ProbComp (((i : I0) → Unit) × (((i : I0) →
      (if (↑i : Fin 2) = 0 then Unit else Bool)) → Unit))),
        ProbComp.eval (do
            let (_, y) ← maliciousIdeal coinTossPrivateFunc I0 (fun _ => ()) S
            return extractBoolFromMalicious y) =
        ProbComp.eval (do
            let (_, y) ← coinTossBiasedDist
            return extractBoolFromBiased y)) := by
  intro ⟨S, h⟩
  have H := congr_arg (fun (p : PMF _) => p true) h
  have h_rhs : ProbComp.eval (do
            let (_, y) ← coinTossBiasedDist
            return extractBoolFromBiased y) true = 1 := by
    dsimp [coinTossBiasedDist]
    simp only [eval_bind, eval_uniform, PMF.bind_apply, PMF.uniformOfFintype_apply]
    simp only [apply_ite ProbComp.eval, eval_pure, tsum_fintype, Fintype.sum_bool, Fintype.card_bool, Nat.cast_ofNat]
    simp only [reduceCtorEq, ite_true, ite_false, PMF.pure_apply, mul_ite, mul_one, mul_zero]
    have h_split : ∀ a : Unit × ((i : Fin 2) → Option (if i = 0 then Unit else Bool)),
      (if true = extractBoolFromBiased a.2 then
          (if a = ((), fun i => if h : i = 0 then cast (by simp [h]) (some ()) else cast (by simp [h]) (some true))
            then (2⁻¹:ENNReal) else 0) +
          (if a = ((), fun i => if h : i = 0 then cast (by simp [h]) (some ()) else none)
            then (2⁻¹:ENNReal) else 0)
        else 0) =
      (if a = ((), fun i => if h : i = 0 then cast (by simp [h]) (some ()) else cast (by simp [h]) (some true))
        then if true = extractBoolFromBiased a.2 then (2⁻¹:ENNReal) else 0 else 0) +
      (if a = ((), fun i => if h : i = 0 then cast (by simp [h]) (some ()) else none)
        then if true = extractBoolFromBiased a.2 then (2⁻¹:ENNReal) else 0 else 0) := by
      intro a
      split_ifs
      all_goals { first | rfl | exact Eq.symm (zero_add 0) }

    simp_rw [h_split, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [extractBoolFromBiased_val1, extractBoolFromBiased_val2, ite_true]
    rw [← one_div]
    exact ENNReal.add_halves 1

  have h_lhs : ProbComp.eval (do
            let (_, y) ← maliciousIdeal coinTossPrivateFunc I0 (fun _ => ()) S
            return extractBoolFromMalicious y) true = 1/2 := by
    dsimp [maliciousIdeal, coinTossPrivateFunc]
    simp only [eval_bind, PMF.bind_apply, eval_map, PMF.map_apply, bind_pure_comp]
    simp only [eval_uniform, PMF.uniformOfFintype_apply]
    simp_rw [ite_tsum_eq_ennreal, ite_mul_eq_ennreal]
    rw [tsum_comm]
    conv_lhs =>
      congr
      intro b
      rw [ENNReal.tsum_mul_left]
      congr
      · skip
      · simp only [ite_tsum_eq_ennreal]
        rw [sum_swap_3]
        simp only [tsum_comm (f := fun _ (x : Bool) => _)]
        simp only [tsum_ite_eq_and_prop]
        simp only [extractBoolFromMalicious_val]
        rw [inner_sum_eval]
    have h_mul : (∑' b, (ProbComp.eval (S (I0.restrict fun _ => ()))) b * (1/2 : ENNReal)) =
        (∑' b, (ProbComp.eval (S (I0.restrict fun _ => ()))) b) * (1/2 : ENNReal) := by
      rw [ENNReal.tsum_mul_right]
    rw [h_mul]
    have h_sum_one : (∑' b, (ProbComp.eval (S (I0.restrict fun _ => ()))) b) = 1 := by
      exact PMF.tsum_coe (ProbComp.eval (S (I0.restrict fun _ => ())))
    rw [h_sum_one]
    exact one_mul _
  rw [h_lhs, h_rhs] at H
  revert H; norm_num
