/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Foundations.Combinatorics.Expander.KilledWalk
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Walk programs and certificates for fixed-length graph walks

An encoded graph supplies a total rotation program with the graph data as an extra input. The
programs here carry that input through each call. Their interpretation lemmas require agreement
only on encoded vertices of the mathematical graph, so malformed inputs and unused vertex names
may have any total behavior.

A rotation certificate charges the runtime input together with the vertex and label. A fixed
number of calls therefore has polynomial cost, including all intermediate vertices and the
complete returned label sequence. The walk length and killing rate are fixed parameters; these
results do not claim a bound uniform in either parameter.

## Main definitions

* `Cslib.RotationMap.walkAtWithInput`: a vertex reached along a walk.
* `Cslib.RotationMap.powRotWithInput`: a walk and its complete reversed return labels.
* `Cslib.RotationMap.killedPowRotWithInput`: a stopped walk, retaining unused labels and signals.

## Main results

* `Cslib.RotationMap.walkAtWithInput_eq`: agreement with a mathematical trajectory.
* `Cslib.RotationMap.powRotWithInput_eq`: agreement with a mathematical power rotation.
* `Cslib.RotationMap.killedPowRotWithInput_eq`: agreement with a killed power rotation.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_walkAtWithInput`:
  a vertex along a fixed walk.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_powRotWithInput`:
  a fixed power rotation.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.rotationMap_killedPowRotWithInput`:
  a fixed killed power.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [J. Radhakrishnan, *Gap amplification in PCPs using lazy random walks*][Radhakrishnan2006]
-/

@[expose] public section

namespace Cslib.RotationMap

variable {P V W D : Type*} (rotate : P × (W × D) → W × D)

/-- A power rotation carries the immutable input and reverses all return labels. -/
def powRotWithInput (T : ℕ) (p : P × (W × (Fin T → D))) : W × (Fin T → D) :=
  powRot (fun q => rotate (p.1, q)) T p.2

/-- Follow the labels, retaining the original graph input at every rotation call. After all labels
have been used, the walk stays at its endpoint. -/
def walkAtWithInput {T : ℕ} (p : P × (W × (Fin T → D))) (m : ℕ) : W :=
  (powRotWithInput rotate (min m T)
    (p.1, p.2.1, Fin.take (min m T) (Nat.min_le_right m T) p.2.2)).1

/-- A killed power reverses only the used prefix, preserving unused labels and kill signals. -/
def killedPowRotWithInput (T q : ℕ) [NeZero q]
    (p : P × (W × ((Fin T → D) × (Fin T → Fin q)))) : W × ((Fin T → D) × (Fin T → Fin q)) :=
  let stopped := powRotWithInput rotate (killTime p.2.2.2)
    (p.1, p.2.1, Fin.take _ (killTime_le p.2.2.2) p.2.2.1)
  (stopped.1, fun i => if h : i.val < killTime p.2.2.2 then stopped.2 ⟨i.val, h⟩ else p.2.2.1 i,
    p.2.2.2)

/-- Once the stopping time is known, the dependent prefix has that concrete length. -/
theorem killedPowRotWithInput_of_killTime {T q : ℕ} [NeZero q]
    (p : P × (W × ((Fin T → D) × (Fin T → Fin q)))) {n : ℕ} (hn : n ≤ T)
    (hc : killTime p.2.2.2 = n) :
    killedPowRotWithInput rotate T q p =
      let stopped := powRotWithInput rotate n (p.1, p.2.1, Fin.take n hn p.2.2.1)
      (stopped.1, fun i => if h : i.val < n then stopped.2 ⟨i.val, h⟩ else p.2.2.1 i, p.2.2.2) := by
  subst n
  rfl

variable (input : P) (G : RotationMap V D) (encode : V → W)
  (hrotate : ∀ v d, rotate (input, encode v, d) = (encode (G.rot (v, d)).1, (G.rot (v, d)).2))

include hrotate in
/-- A power program returns both the encoded endpoint and exactly the reversed mathematical
return labels. No hypothesis is needed on rotations of unused vertex names. -/
theorem powRotWithInput_eq (T : ℕ) (v : V) (k : Fin T → D) :
    powRotWithInput rotate T (input, encode v, k) =
      (encode ((G.pow T).rot (v, k)).1, ((G.pow T).rot (v, k)).2) := by
  induction T generalizing v with
  | zero => rfl
  | succ T ih =>
    simp only [powRotWithInput, pow] at ih
    simp only [powRotWithInput, hrotate, ih, pow, powRot]

include hrotate in
/-- Agreement of one rotation on encoded vertices gives agreement of every trajectory. -/
theorem walkAtWithInput_eq {T : ℕ} (v : V) (k : Fin T → D) (m : ℕ) :
    walkAtWithInput rotate (input, encode v, k) m = encode (G.walkAt (v, k) m) := by
  simp only [walkAtWithInput, powRotWithInput_eq rotate input G encode hrotate, ← neighbor_def,
    ← G.walkAt_eq_neighbor_pow (v, k) (Nat.min_le_right m T)]
  rcases Nat.le_total m T with hm | hm
  · rw [Nat.min_eq_left hm]
  · rw [Nat.min_eq_right hm, G.walkAt_of_le (v, k) hm]

include hrotate in
/-- A killed power program agrees with the mathematical stopped walk, including its unused
labels and original kill signals. -/
theorem killedPowRotWithInput_eq (T q : ℕ) [NeZero q]
    (v : V) (k : Fin T → D) (c : Fin T → Fin q) :
    killedPowRotWithInput rotate T q (input, encode v, k, c) =
      (encode ((G.killedPow T q).rot (v, k, c)).1, ((G.killedPow T q).rot (v, k, c)).2) := by
  simp only [killedPowRotWithInput, powRotWithInput_eq rotate input G encode hrotate, killedPow]

end Cslib.RotationMap

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

open Cslib

variable {P V D : Type} {input : P ↪ List Bool} {vertex : V ↪ List Bool}
  {label : D ↪ List Bool} {rotate : P × (V × D) → V × D}
  (hrotate : ComputableTidilyInPolyTime rotate
    (encPair input (encPair vertex label)) (encPair vertex label))

private theorem polytime_finTail (T : ℕ) :
    ComputableTidilyInPolyTime (@Fin.tail T (fun _ => D)) (encPi label) (encPi label) :=
  pi fun i => pi_apply label i.succ

private theorem polytime_finSnoc (T : ℕ) :
    ComputableTidilyInPolyTime (fun p : (Fin T → D) × D => Fin.snoc p.1 p.2)
      (encPair (encPi label) label) (encPi label) := by
  apply pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using snd (encPi label) label
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      (pi_apply label j).comp (fst (encPi label) label)

private theorem polytime_finTake {T n : ℕ} (hn : n ≤ T) :
    ComputableTidilyInPolyTime (Fin.take n hn (α := fun _ => D)) (encPi label) (encPi label) :=
  pi fun i => pi_apply label (i.castLE hn)

include hrotate in
/-- A fixed power reverses all return labels while charging the runtime graph at every call. -/
@[fun_prop]
theorem rotationMap_powRotWithInput (T : ℕ) :
    ComputableTidilyInPolyTime (RotationMap.powRotWithInput rotate T)
      (encPair input (encPair vertex (encPi label))) (encPair vertex (encPi label)) := by
  induction T with
  | zero => exact snd _ _
  | succ T ih =>
    have hhead : ComputableTidilyInPolyTime
        (fun p : P × (V × (Fin (T + 1) → D)) => rotate (p.1, p.2.1, p.2.2 0))
        (encPair input (encPair vertex (encPi label))) (encPair vertex label) :=
      hrotate.comp ((fst _ _).prod
        (((snd _ _).fst').prod ((pi_apply label 0).comp ((snd _ _).snd'))))
    have hrest := ih.comp ((fst _ _).prod (hhead.fst'.prod
      ((polytime_finTail (label := label) T).comp ((snd _ _).snd'))))
    exact hrest.fst'.prod ((polytime_finSnoc (label := label) T).comp (hrest.snd'.prod hhead.snd'))

include hrotate in
/-- A fixed step of a fixed-length walk uses the joint certificate for the runtime graph. -/
@[fun_prop]
theorem rotationMap_walkAtWithInput (T m : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : P × (V × (Fin T → D)) => RotationMap.walkAtWithInput rotate p m)
      (encPair input (encPair vertex (encPi label))) vertex :=
  ((rotationMap_powRotWithInput hrotate (min m T)).comp
    ((fst _ _).prod (((snd _ _).fst').prod
      ((polytime_finTake (Nat.min_le_right m T)).comp ((snd _ _).snd'))))).fst'

include hrotate in
/-- A killed power branches on the fixed finite signal sequence, computes the actual stopped
walk, and retains every unused label and every signal in the result. -/
@[fun_prop]
theorem rotationMap_killedPowRotWithInput (T q : ℕ) [NeZero q] (signal : Fin q ↪ List Bool) :
    ComputableTidilyInPolyTime
      (RotationMap.killedPowRotWithInput rotate T q)
      (encPair input (encPair vertex (encPair (encPi label) (encPi signal))))
      (encPair vertex (encPair (encPi label) (encPi signal))) := by
  have hbranch (c : Fin T → Fin q) : ComputableTidilyInPolyTime
      (fun p : P × (V × ((Fin T → D) × (Fin T → Fin q))) =>
        RotationMap.killedPowRotWithInput rotate T q (p.1, p.2.1, p.2.2.1, c))
      (encPair input (encPair vertex (encPair (encPi label) (encPi signal))))
      (encPair vertex (encPair (encPi label) (encPi signal))) := by
    have hwalk : ComputableTidilyInPolyTime
        (fun p : P × (V × ((Fin T → D) × (Fin T → Fin q))) =>
          RotationMap.powRotWithInput rotate (killTime c)
            (p.1, p.2.1, Fin.take _ (killTime_le c) p.2.2.1))
        (encPair input (encPair vertex (encPair (encPi label) (encPi signal))))
        (encPair vertex (encPi label)) :=
      (rotationMap_powRotWithInput hrotate (killTime c)).comp
        ((fst _ _).prod (((snd _ _).fst').prod
          ((polytime_finTake (killTime_le c)).comp ((snd _ _).snd'.fst'))))
    dsimp only [RotationMap.killedPowRotWithInput]
    apply hwalk.fst'.prod
    apply prod ?_ (const c)
    apply pi
    intro i
    by_cases hi : i.val < killTime c
    · simpa only [dite_eq_left hi, Function.comp_def] using
        (pi_apply label ⟨i.val, hi⟩).comp hwalk.snd'
    · simpa only [dite_eq_right hi, Function.comp_def] using
        (pi_apply label i).comp ((snd input _).snd'.fst')
  exact ((snd input (encPair vertex (encPair (encPi label) (encPi signal)))).snd'.snd').finite_cases
    hbranch

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
