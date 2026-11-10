/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
public import CslibFrontier.Computability.Circuit.Replication
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Codes of replicated circuits

`replicateCode n k code` lays out `k` disjoint copies of a raw circuit code on `n` inputs: copy `t`
reads inputs `t n, …, t n + n - 1`, its gates follow the gates of the copies before it, and the
outputs of the copies are concatenated. On the code of a typed circuit it is the code of
`Cslib.Circuits.Circuit.replicate` (`replicateCode_code`). The constructor is computable in
polynomial time with a binary input count and a unary number of copies
(`computableInPolyTime_replicateCode`).

## Main definitions

* `Cslib.Circuits.Boolean.replicateWire`: the wire numbers of one copy.
* `Cslib.Circuits.Boolean.replicateCode`: the code of disjoint copies.

## Main results

* `Cslib.Circuits.Boolean.replicateCode_code`: agreement with `Circuit.replicate`.
* `Cslib.Circuits.Boolean.length_replicateCode`: the gate count is multiplied by the number of
  copies.
* `Cslib.Circuits.Boolean.computableInPolyTime_replicateCode`: constructor efficiency.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- The number of wire `i` of a circuit with `n` inputs and `s` gates in copy `t` of `k`
disjoint copies: input `i < n` is input `t * n + i` of the replicated circuit, and gate wire
`n + g` is gate `t * s + g` of the replicated circuit. -/
def replicateWire (n s k t i : ℕ) : ℕ :=
  if i < n then t * n + i else k * n + t * s + (i - n)

/-- The code of `k` disjoint copies of the circuit with code `code` on `n` inputs. -/
def replicateCode (n k : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  ((List.range k).flatMap fun t =>
      code.1.map fun g => (g.1, g.2.map (replicateWire n code.1.length k t)),
    (List.range k).flatMap fun t => code.2.map (replicateWire n code.1.length k t))

private theorem code_wiring_cast {a b : ℕ} (h : a = b) :
    (Circuit.wiring signature (Fin.cast h)).code = ([], List.range a) := by
  simpa using Circuit.code_wiring_eq_map (σ := signature) (f := Fin.cast h) (g := id)
    fun _ => rfl

/-- Composing on the left with the identity wiring keeps a code. -/
private theorem compCode_range_left (n L : ℕ) (X : List (Op × List ℕ) × List ℕ)
    (h : X.2.length = L) : compCode n ([], List.range L) X = X := by
  subst h
  obtain ⟨gs, outs⟩ := X
  simp only [compCode, List.map_nil, List.append_nil, Prod.mk.injEq, true_and]
  apply List.ext_getElem (by simp)
  intro i hi _
  simp only [List.length_map, List.length_range] at hi
  simp [compCodeWire, hi, List.getD_eq_getElem?_getD]

/-- Composing on the right with the identity wiring keeps a code. -/
private theorem compCode_range_right (n L : ℕ) (X : List (Op × List ℕ) × List ℕ)
    (h : L = n) : compCode n X ([], List.range L) = X := by
  rw [h]
  obtain ⟨gs, outs⟩ := X
  have hw : compCodeWire n ([], List.range n) = id := by
    funext i
    by_cases hi : i < n <;> simp [compCodeWire, hi, List.getD_eq_getElem?_getD]
    omega
  simp [compCode, hw]

private theorem compCodeWire_range_map (N L : ℕ) (g : ℕ → ℕ) (i : ℕ) :
    compCodeWire N ([], (List.range L).map g) i = if i < L then g i else N + (i - L) := by
  by_cases hi : i < L <;>
    simp [compCodeWire, hi, List.getD_eq_getElem?_getD]

theorem length_replicateCode (n k : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    (replicateCode n k code).1.length = k * code.1.length := by
  simp [replicateCode, List.length_flatMap, List.sum_replicate]

/-- Replicating the code of a circuit gives the code of its disjoint copies. -/
theorem replicateCode_code {n m : ℕ} (c : Circuit signature n m) (k : ℕ) :
    replicateCode n k c.code = (c.replicate k).code := by
  induction k with
  | zero => simp [replicateCode, Circuit.replicate, Circuit.parallelFamily, Circuit.code_wiring]
  | succ k ih =>
    rw [show c.replicate (k + 1) = (Circuit.wiring signature (Fin.cast (Nat.succ_mul k m))).comp
        (((c.replicate k).parallel c).comp
          (Circuit.wiring signature (Fin.cast (Nat.succ_mul k n).symm))) from rfl,
      ← compCode_code, ← compCode_code, code_wiring_cast, code_wiring_cast,
      compCode_range_right _ _ _ (Nat.succ_mul k n).symm,
      compCode_range_left _ _ _ (by simp [Circuit.code, Nat.succ_mul]),
      Circuit.parallel, ← appendCode_code, ← compCode_code, ← compCode_code,
      Circuit.code_wiring_eq_map (σ := signature) (f := Fin.castAdd n) (g := id) (fun _ => rfl),
      Circuit.code_wiring_eq_map (σ := signature) (f := Fin.natAdd (k * n)) (g := (k * n + ·))
        (fun _ => rfl), ← ih]
    have hA : ∀ t ∈ List.range k,
        compCodeWire (k * n + n) ([], (List.range (k * n)).map id) ∘
          replicateWire n c.code.1.length k t = replicateWire n c.code.1.length (k + 1) t := by
      intro t ht
      have ht := List.mem_range.1 ht
      funext i
      simp only [Function.comp_apply, compCodeWire_range_map, replicateWire, Nat.succ_mul, id]
      have : t * n + n ≤ k * n := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right n ht
      split_ifs <;> omega
    have hB : shiftCodeWire (k * n + n) (k * c.code.1.length) ∘
        compCodeWire (k * n + n) ([], (List.range n).map (k * n + ·)) =
          replicateWire n c.code.1.length (k + 1) k := by
      funext i
      simp only [Function.comp_apply, compCodeWire_range_map, replicateWire, shiftCodeWire,
        Nat.succ_mul]
      split_ifs <;> omega
    simp only [replicateCode, appendCode, compCode, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.map_flatMap, List.map_map, List.nil_append, Prod.mk.injEq,
      List.length_flatMap, List.length_map, List.map_const', List.sum_replicate,
      List.length_range, smul_eq_mul]
    refine ⟨?_, ?_⟩
    · congr 1
      · apply List.flatMap_congr
        intro t ht
        apply List.map_congr_left
        intro g _
        simp only [Function.comp_apply, List.map_map, hA t ht]
      · apply List.map_congr_left
        intro g _
        simp only [Function.comp_apply, List.map_map, hB]
    · congr 1
      · apply List.flatMap_congr
        intro t ht
        rw [hA t ht]
      · rw [hB]

open Turing.MultiTapeTM ComputableInPolyTime

/-- Numbering a replicated wire is polynomial-time with all quantities in binary. -/
@[fun_prop]
theorem computableInPolyTime_replicateWire {α : Type} {enc : α ↪ List Bool}
    {n s k t i : α → ℕ} (hn : ComputableInPolyTime n enc encNat)
    (hs : ComputableInPolyTime s enc encNat) (hk : ComputableInPolyTime k enc encNat)
    (ht : ComputableInPolyTime t enc encNat) (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun a => replicateWire (n a) (s a) (k a) (t a) (i a)) enc encNat := by
  unfold replicateWire
  fun_prop

/-- Replicating a raw code is polynomial-time, with a binary input count and a unary number of
copies. -/
@[fun_prop]
theorem computableInPolyTime_replicateCode {α : Type} {enc : α ↪ List Bool}
    {n k : α → ℕ} {code : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat) (hk : ComputableInPolyTime k enc encUnary)
    (hcode : ComputableInPolyTime code enc encCode) :
    ComputableInPolyTime (fun a => replicateCode (n a) (k a) (code a)) enc encCode := by
  have hlen : ComputableInPolyTime (fun a => (code a).1.length) enc encNat :=
    (length_list_binary encGate).comp hcode.fst'
  have hkb : ComputableInPolyTime k enc encNat := unary_to_binary.comp hk
  have hwire : ComputableInPolyTime
      (fun p : (α × ℕ) × ℕ => replicateWire (n p.1.1) (code p.1.1).1.length (k p.1.1) p.1.2 p.2)
      (encPair (encPair enc encUnary) encNat) encNat :=
    computableInPolyTime_replicateWire (hn.comp ((fst _ _).comp (fst _ _)))
      (hlen.comp ((fst _ _).comp (fst _ _))) (hkb.comp ((fst _ _).comp (fst _ _)))
      (unary_to_binary.comp ((snd _ _).comp (fst _ _))) (snd _ _)
  have hgate : ComputableInPolyTime
      (fun p : (α × ℕ) × (Op × List ℕ) =>
        (p.2.1, p.2.2.map (replicateWire (n p.1.1) (code p.1.1).1.length (k p.1.1) p.1.2)))
      (encPair (encPair enc encUnary) encGate) encGate :=
    ((snd _ encGate).fst').prod
      (mapWithInput (snd _ encGate).snd' (hwire.comp ((fst _ _).fst'.prod (snd _ _))))
  have hgates : ComputableInPolyTime
      (fun p : α × ℕ => (code p.1).1.map fun g =>
        (g.1, g.2.map (replicateWire (n p.1) (code p.1).1.length (k p.1) p.2)))
      (encPair enc encUnary) (encList encGate) :=
    mapWithInput (hcode.fst'.comp (fst _ _)) hgate
  have houts : ComputableInPolyTime
      (fun p : α × ℕ => (code p.1).2.map (replicateWire (n p.1) (code p.1).1.length (k p.1) p.2))
      (encPair enc encUnary) (encList encNat) :=
    mapWithInput (hcode.snd'.comp (fst _ _)) hwire
  exact (flatMapWithInput (range.comp hk) hgates).prod (flatMapWithInput (range.comp hk) houts)

end Cslib.Circuits.Boolean
