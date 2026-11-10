/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Knapsack.FPTAS
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Tactic.EncLen

/-!
# The knapsack dynamic program and FPTAS run in polynomial time

The dynamic program by profit (`Cslib.Algorithms.Lean.Knapsack.profitDP`) is pseudo-polynomial:
with the profits encoded in unary, and each profit at most the length of its item's encoding, it
is computable in polynomial time (`Cslib.Algorithms.Lean.Knapsack.computableInPolyTime_profitDP`).
One step of the table maps two padded copies of the table through the choice of the lighter
entry. Every entry is `none` or a subsequence of the items, and the table has one entry per
profit up to the total profit, so the encoded table stays polynomially bounded
(`Cslib.Algorithms.Lean.Knapsack.TableSpec`). The selection scan keeps a subsequence of the items.

The FPTAS rounds the values to at most `n * k`, computed in unary from `k` in unary, so its
dynamic program runs in time polynomial in the encoded instance and `k`
(`Cslib.Algorithms.Lean.Knapsack.computableInPolyTime_fptas`). Weights, capacities and the
original values stay in binary.

## Main results

* `Cslib.Algorithms.Lean.Knapsack.computableInPolyTime_profitTable`,
  `Cslib.Algorithms.Lean.Knapsack.computableInPolyTime_profitDP`: the dynamic program by profit is
  pseudo-polynomial.
* `Cslib.Algorithms.Lean.Knapsack.computableInPolyTime_profitDP_unary`: the exact dynamic program
  on `(weight, value)` items with the values in unary is polynomial-time.
* `Cslib.Algorithms.Lean.Knapsack.computableInPolyTime_fptas`: the FPTAS is polynomial-time in
  the encoded instance and `k`.

## References

* [D. P. Williamson, D. B. Shmoys, *The Design of Approximation Algorithms*][WilliamsonShmoys2011]
-/

public section

namespace Cslib.Algorithms.Lean.Knapsack

open Turing.MultiTapeTM ComputableInPolyTime
open scoped List

variable {ι : Type} {encI : ι ↪ List Bool} {w p : ι → ℕ}

private theorem computableInPolyTime_lighter (hw : ComputableInPolyTime w encI encNat) :
    ComputableInPolyTime (fun x : Option (List ι) × Option (List ι) => lighter w x.1 x.2)
      (encPair (encOption (encList encI)) (encOption (encList encI)))
      (encOption (encList encI)) := by
  unfold lighter
  fun_prop

private theorem computableInPolyTime_profitStep (hw : ComputableInPolyTime w encI encNat)
    (hp : ComputableInPolyTime p encI encUnary) :
    ComputableInPolyTime (fun x : List (Option (List ι)) × ι => profitStep w p x.1 x.2)
      (encPair (encList (encOption (encList encI))) encI) (encList (encOption (encList encI))) := by
  have hl := computableInPolyTime_lighter hw
  have hz : ∀ (l₁ l₂ : List (Option (List ι))),
      List.zipWith (lighter w) l₁ l₂ = (l₁.zip l₂).map fun q => lighter w q.1 q.2 := by
    intro l₁ l₂
    rw [List.zip_eq_zipWith, List.map_zipWith]
  have hm : ∀ (T : List (Option (List ι))) (a : ι),
      T.map (Option.map (· ++ [a])) = T.map fun o => o.elim none fun s => some (s ++ [a]) := by
    intro T a
    congr 1 with o : 1
    cases o <;> rfl
  unfold profitStep
  simp only [hz, hm]
  fun_prop

private theorem sum_map_le_length_encList (hpl : ∀ a, p a ≤ (encI a).length) (l : List ι) :
    (l.map p).sum ≤ (encList encI l).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have := hpl a
    enc_len [List.map_cons, List.sum_cons, encList_cons]

private theorem length_encList_table_le (hpl : ∀ a, p a ≤ (encI a).length) {l : List ι}
    {T : List (Option (List ι))} (hT : TableSpec w p l T) :
    (encList (encOption (encList encI)) T).length ≤
      ((encList encI l).length + 1) * (2 * ((encList encI l).length + 1) + 1) := by
  have h := length_encList_le (encOption (encList encI)) T (b := (encList encI l).length + 1) ?_
  · rw [hT.length_eq] at h
    have := sum_map_le_length_encList hpl l
    exact h.trans (Nat.mul_le_mul_right _ (by omega))
  · intro o ho
    cases o with
    | none => simp
    | some s =>
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp ho
      have := length_encList_sublist encI (hT.sound q s hq).1
      enc_len

/-- **The profit table is pseudo-polynomial**: with the profits in unary, and each profit at most
the length of its item's encoding, it is computable in polynomial time. -/
theorem computableInPolyTime_profitTable (hw : ComputableInPolyTime w encI encNat)
    (hp : ComputableInPolyTime p encI encUnary) (hpl : ∀ a, p a ≤ (encI a).length) :
    ComputableInPolyTime (profitTable w p) (encList encI) (encList (encOption (encList encI))) := by
  have h := foldl' (encA := encI) (encL := encList encI)
    (encB := encList (encOption (encList encI)))
    (list := id) (init := fun _ => [some []]) (step := profitStep w p) id' (const _)
    (computableInPolyTime_profitStep hw hp)
    (B := fun l => ((encList encI l).length + 1) * (2 * ((encList encI l).length + 1) + 1))
    ((PolyBounded.self.add (.const 1)).mul
      (((PolyBounded.const 2).mul (PolyBounded.self.add (.const 1))).add (.const 1)))
    (fun l i _ => by
      have hT := tableSpec_nil (w := w) (p := p) |>.foldl (l.take i)
      rw [List.nil_append] at hT
      have hle := length_encList_sublist encI (List.take_sublist i l)
      refine (length_encList_table_le hpl hT).trans ?_
      apply Nat.mul_le_mul <;> omega)
  exact h

/-- **The dynamic program by profit is pseudo-polynomial**: with the profits in unary, and each
profit at most the length of its item's encoding, it is computable in polynomial time. -/
theorem computableInPolyTime_profitDP (hw : ComputableInPolyTime w encI encNat)
    (hp : ComputableInPolyTime p encI encUnary) (hpl : ∀ a, p a ≤ (encI a).length) :
    ComputableInPolyTime (fun x : ℕ × List ι => profitDP w p x.1 x.2)
      (encPair encNat (encList encI)) (encList encI) := by
  have hT := (computableInPolyTime_profitTable hw hp hpl).comp (snd encNat (encList encI))
  have hp' : ComputableInPolyTime p encI encNat :=
    ComputableInPolyTime.unary_to_binary.comp hp
  have hstep : ComputableInPolyTime
      (fun q : (ℕ × List ι) × Option (List ι) => selectStep w p q.1.1 q.1.2 q.2)
      (encPair (encPair encNat (encList encI)) (encOption (encList encI))) (encList encI) := by
    unfold selectStep
    fun_prop
  have h := foldlWith (encA := encOption (encList encI))
    (encL := encList (encOption (encList encI)))
    (encB := encList encI) (encP := encNat)
    (par := fun x : ℕ × List ι => x.1) (list := fun x => profitTable w p x.2)
    (init := fun _ => []) (step := selectStep w p) (fst _ _) hT (const _) hstep
    (B := fun x => (encPair encNat (encList encI) x).length) .self
    (fun x i _ => by
      have hsub := foldl_selectStep_sublist (w := w) (p := p) (B := x.1) (l := x.2)
        (L := (profitTable w p x.2).take i)
        (fun s hs => sublist_of_mem_profitTable (List.mem_of_mem_take hs)) (List.nil_sublist _)
      have := length_encList_sublist encI hsub
      rw [length_encPair]
      omega)
  exact h

/-- The exact dynamic program on `(weight, value)` items with the values in unary is
polynomial-time. -/
theorem computableInPolyTime_profitDP_unary :
    ComputableInPolyTime (fun x : ℕ × List (ℕ × ℕ) => profitDP Prod.fst Prod.snd x.1 x.2)
      (encPair encNat (encList (encPair encNat encUnary))) (encList (encPair encNat encUnary)) :=
  computableInPolyTime_profitDP (fst _ _) (snd _ _)
    (fun a => by simp only [length_encPair, encUnary_apply, List.length_replicate]; omega)

section FPTAS

private theorem computableInPolyTime_maxValue :
    ComputableInPolyTime maxValue (encList (encPair encNat encNat)) encNat := by
  have hm := (fst (encPair (encList (encPair encNat encNat)) encNat) (encPair encNat encNat)).snd'
  have ha := (snd (encPair (encList (encPair encNat encNat)) encNat) (encPair encNat encNat)).snd'
  have hle := binary_le' hm ha
  have hstep : ComputableInPolyTime
      (fun q : (List (ℕ × ℕ) × ℕ) × (ℕ × ℕ) => max q.1.2 q.2.2)
      (encPair (encPair (encList (encPair encNat encNat)) encNat) (encPair encNat encNat))
      encNat := by
    have h := ite hle ha hm
    simp only [decide_eq_true_eq] at h
    simpa only [max_def] using h
  have h := foldlWithInput_of_bounded_growth (encA := encPair encNat encNat)
    (encB := encNat) (encL := encList (encPair encNat encNat))
    (list := id) (init := fun _ => 0) (step := fun _ m a => max m a.2) (const _)
    ⟨id', hstep, inferInstance, inferInstance⟩
    (growth := fun l => (encList (encPair encNat encNat) l).length)
    ⟨.self, fun l m a ha => by
      have h1 := SizedListEncoding.length_elem_le (encA := encPair encNat encNat)
        (encL := encList (encPair encNat encNat)) l a ha
      rw [length_encPair] at h1
      rcases le_total m a.2 with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega⟩
  exact h

/-- **The knapsack FPTAS runs in polynomial time** in the encoded instance and `k`, given in
unary. -/
theorem computableInPolyTime_fptas :
    ComputableInPolyTime (fun x : ℕ × (List (ℕ × ℕ) × ℕ) => fptas x.1 x.2)
      (encPair encUnary (encPair (encList (encPair encNat encNat)) encNat))
      (encList (encPair encNat encNat)) := by
  have hF : ComputableInPolyTime (fun x : ℕ × (List (ℕ × ℕ) × ℕ) => fits x.2.2 x.2.1)
      (encPair encUnary (encPair (encList (encPair encNat encNat)) encNat))
      (encList (encPair encNat encNat)) := by
    unfold fits
    fun_prop
  have hN : ComputableInPolyTime
      (fun x : ℕ × (List (ℕ × ℕ) × ℕ) => (fits x.2.2 x.2.1).length * x.1)
      (encPair encUnary (encPair (encList (encPair encNat encNat)) encNat)) encUnary :=
    unary_mul' ((length_list (encPair encNat encNat)).comp hF) (fst _ _)
  have hP := computableInPolyTime_maxValue.comp hF
  have hR : ComputableInPolyTime (fun x : ℕ × (List (ℕ × ℕ) × ℕ) =>
      roundValues ((fits x.2.2 x.2.1).length * x.1) (maxValue (fits x.2.2 x.2.1))
        (fits x.2.2 x.2.1))
      (encPair encUnary (encPair (encList (encPair encNat encNat)) encNat))
      (encList (encPair (encPair encNat encNat) encUnary)) := by
    have hNq := hN.comp (fst (encPair encUnary (encPair (encList (encPair encNat encNat)) encNat))
      (encPair encNat encNat))
    have hNb := ComputableInPolyTime.unary_to_binary.comp hNq
    have hPq := hP.comp (fst (encPair encUnary (encPair (encList (encPair encNat encNat)) encNat))
      (encPair encNat encNat))
    have hv := (snd (encPair encUnary (encPair (encList (encPair encNat encNat)) encNat))
      (encPair encNat encNat)).snd'
    have hmul := binary_mul' hv hNb
    have hdiv := ComputableInPolyTime.binary_div.comp (hmul.prod hPq)
    have hbody := (snd _ _).prod (binary_min_unary' hNq hdiv)
    exact mapWithInput hF hbody
  have hDP := computableInPolyTime_profitDP (encI := encPair (encPair encNat encNat) encUnary)
    (w := fun a : (ℕ × ℕ) × ℕ => a.1.1) (p := Prod.snd) (fst _ _).fst' (snd _ _)
    (fun a => by simp only [length_encPair, encUnary_apply, List.length_replicate]; omega)
  have hS := hDP.comp
    ((snd encUnary (encPair (encList (encPair encNat encNat)) encNat)).snd'.prod hR)
  exact mapWithInput hS (snd _ _).fst'

end FPTAS

end Cslib.Algorithms.Lean.Knapsack
