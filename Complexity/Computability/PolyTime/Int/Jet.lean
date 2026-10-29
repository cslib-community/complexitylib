/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.PolyTime.ParityFactorEval
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.List.GetD

/-!
# Truncated univariate integer Taylor jet subtraction, congruences, and fold combinators

Builds on `Cslib.truncZJet`, `Cslib.polyAdd`, and `Cslib.mulZJet`
from `Complexity/Computability/PolyTime/ParityFactorEval.lean` to provide truncated length-`J`
addition, subtraction, scalar subtraction, `Polynomial.X ^ J` divisibility congruences, `foldl`
product invariants, `encIntBin` bit-length bounds, and a plain `ComputableInPolyTime` product-fold
combinator in `ℤ[z] / (z ^ J)`.

All operations (`Cslib.IntJet.add`, `Cslib.IntJet.sub`, `Cslib.IntJet.subConst`, together with
`Cslib.truncZJet` and `Cslib.mulZJet`) are total on arbitrary `List ℤ` inputs: missing entries read
as `0` via `List.getD _ 0`, entries at indices `≥ J` are truncated modulo `z ^ J`, and every output
has exact length `J`.

## Main definitions and results

* `Cslib.IntJet.add`, `Cslib.IntJet.sub`, `Cslib.IntJet.subConst`: truncated length-`J` addition
  (via `Cslib.truncZJet` and `Cslib.polyAdd`) and subtraction on `List ℤ`.
* `Cslib.IntJet.X_pow_dvd_truncZJet`, `Cslib.IntJet.X_pow_dvd_add`, `Cslib.IntJet.X_pow_dvd_sub`,
  `Cslib.IntJet.X_pow_dvd_subConst`, `Cslib.IntJet.X_pow_dvd_mulZJet`,
  `Cslib.IntJet.X_pow_dvd_foldl_mulZJet`: congruences modulo `Polynomial.X ^ J` over `ℤ[X]`.
* `Cslib.IntJet.coeffNorm1_mulZJet_le`, `Cslib.IntJet.coeffNorm1_foldl_mulZJet_le`,
  `Cslib.IntJet.length_encIntBin_getD_le_coeffNorm1`,
  `Cslib.IntJet.computableInPolyTime_foldl_mulZJet`: `Polynomial.coeffNorm1`, `encIntBin`, and plain
  `Turing.MultiTapeTM.ComputableInPolyTime` bounds and `@[fun_prop]` rules.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix B.1, B.4
  (pp. 48–51).
-/

@[expose] public section

open scoped BigOperators
open Turing.MultiTapeTM

namespace Cslib.IntJet

/-- Pointwise addition of two integer jets modulo `z ^ J` (exact length `J`), reusing
`Cslib.truncZJet` and `Cslib.polyAdd`. -/
def add (J : ℕ) (a b : List ℤ) : List ℤ := Cslib.truncZJet J (Cslib.polyAdd a b)

/-- Pointwise subtraction of two integer jets, zero-padded via `getD _ 0` to exact length `J`. -/
def sub (J : ℕ) (a b : List ℤ) : List ℤ := (List.range J).map fun k => a.getD k 0 - b.getD k 0

/-- Subtract an integer jet `a` from a scalar constant `c` modulo `z ^ J` (exact length `J`). -/
def subConst (J : ℕ) (c : ℤ) (a : List ℤ) : List ℤ := sub J [c] a

@[simp] theorem length_add (J : ℕ) (a b : List ℤ) : (add J a b).length = J :=
  Cslib.length_truncZJet J _

@[simp] theorem length_sub (J : ℕ) (a b : List ℤ) : (sub J a b).length = J := by
  simp only [sub, List.length_map, List.length_range]

@[simp] theorem length_subConst (J : ℕ) (c : ℤ) (a : List ℤ) : (subConst J c a).length = J :=
  length_sub J [c] a

/-- Folding `Cslib.mulZJet J` preserves exact length `J` whenever `acc.length = J`. -/
theorem length_foldl_mulZJet {α : Type*} (J : ℕ) (stepJet : α → List ℤ) (l : List α) {acc : List ℤ}
    (hacc : acc.length = J) :
    (l.foldl (fun s x => Cslib.mulZJet J s (stepJet x)) acc).length = J := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons _ _ ih => exact ih (Cslib.length_mulZJet J acc _)

/-- `Cslib.truncZJet J a` is congruent to `Polynomial.ofCoeffList a` modulo `X ^ J`. -/
theorem X_pow_dvd_truncZJet (J : ℕ) (a : List ℤ) :
    Polynomial.X ^ J ∣ Polynomial.ofCoeffList (Cslib.truncZJet J a) - Polynomial.ofCoeffList a :=
  Polynomial.X_pow_dvd_iff.mpr fun k hk => by
    rw [Polynomial.coeff_sub, Polynomial.coeff_ofCoeffList, Polynomial.coeff_ofCoeffList,
      Cslib.truncZJet, List.getD_map_range _ 0 hk, sub_self]

/-- `Cslib.truncZJet J [c]` is congruent to `Polynomial.C c` modulo `X ^ J`. -/
theorem X_pow_dvd_truncZJet_singleton (J : ℕ) (c : ℤ) :
    Polynomial.X ^ J ∣ Polynomial.ofCoeffList (Cslib.truncZJet J [c]) - Polynomial.C c := by
  simpa only [Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil, mul_zero, add_zero] using
    X_pow_dvd_truncZJet J [c]

theorem X_pow_dvd_add (J : ℕ) (a b : List ℤ) :
    Polynomial.X ^ J ∣
      Polynomial.ofCoeffList (add J a b) -
        (Polynomial.ofCoeffList a + Polynomial.ofCoeffList b) := by
  rw [add, ← Cslib.ofCoeffList_polyAdd]
  exact X_pow_dvd_truncZJet J _

theorem X_pow_dvd_sub (J : ℕ) (a b : List ℤ) :
    Polynomial.X ^ J ∣
      Polynomial.ofCoeffList (sub J a b) -
        (Polynomial.ofCoeffList a - Polynomial.ofCoeffList b) :=
  Polynomial.X_pow_dvd_iff.mpr fun k hk => by
    rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_ofCoeffList,
      Polynomial.coeff_ofCoeffList, Polynomial.coeff_ofCoeffList, sub,
      List.getD_map_range _ 0 hk, sub_self]

theorem X_pow_dvd_subConst (J : ℕ) (c : ℤ) (a : List ℤ) :
    Polynomial.X ^ J ∣
      Polynomial.ofCoeffList (subConst J c a) - (Polynomial.C c - Polynomial.ofCoeffList a) := by
  simpa only [subConst, Polynomial.ofCoeffList_cons, Polynomial.ofCoeffList_nil, mul_zero,
    add_zero] using X_pow_dvd_sub J [c] a

/-- `Cslib.mulZJet J a b` is congruent to `ofCoeffList a * ofCoeffList b` modulo `X ^ J`. -/
theorem X_pow_dvd_mulZJet (J : ℕ) (a b : List ℤ) :
    Polynomial.X ^ J ∣
      Polynomial.ofCoeffList (Cslib.mulZJet J a b) -
        Polynomial.ofCoeffList a * Polynomial.ofCoeffList b := by
  have htake (u : List ℤ) :
      Polynomial.X ^ J ∣ Polynomial.ofCoeffList (u.take J) - Polynomial.ofCoeffList u :=
    Cslib.ofCoeffList_truncZJet J u ▸ X_pow_dvd_truncZJet J u
  have hmul : Polynomial.X ^ J ∣
      Polynomial.ofCoeffList (Cslib.mulZJet J a b) -
        Polynomial.ofCoeffList (a.take J) * Polynomial.ofCoeffList (b.take J) :=
    Polynomial.X_pow_dvd_iff.mpr fun k hk => by
      rw [Polynomial.coeff_sub, Polynomial.coeff_ofCoeffList, Cslib.getD_mulZJet_of_lt hk a b,
        sub_self]
  convert dvd_add
    (dvd_add hmul (dvd_mul_of_dvd_left (htake a) (Polynomial.ofCoeffList (b.take J))))
    (dvd_mul_of_dvd_right (htake b) (Polynomial.ofCoeffList a)) using 1
  ring

/-- Folding `Cslib.mulZJet J` over `l` preserves congruence modulo `X ^ J`. -/
theorem X_pow_dvd_foldl_mulZJet {α : Type*} (J : ℕ) (l : List α)
    (stepJet : α → List ℤ) (stepPoly : α → Polynomial ℤ)
    (hstep : ∀ x ∈ l, Polynomial.X ^ J ∣ Polynomial.ofCoeffList (stepJet x) - stepPoly x)
    (acc : List ℤ) (accPoly : Polynomial ℤ)
    (hacc : Polynomial.X ^ J ∣ Polynomial.ofCoeffList acc - accPoly) :
    Polynomial.X ^ J ∣
      Polynomial.ofCoeffList (l.foldl (fun s x => Cslib.mulZJet J s (stepJet x)) acc) -
        accPoly * (l.map stepPoly).prod := by
  induction l generalizing acc accPoly with
  | nil => simpa only [List.foldl_nil, List.map_nil, List.prod_nil, mul_one] using hacc
  | cons x l ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    refine ih (fun y hy => hstep y (List.mem_cons_of_mem _ hy))
      (Cslib.mulZJet J acc (stepJet x)) (accPoly * stepPoly x) ?_
    convert dvd_add
      (dvd_add (X_pow_dvd_mulZJet J acc (stepJet x))
        (dvd_mul_of_dvd_left hacc (Polynomial.ofCoeffList (stepJet x))))
      (dvd_mul_of_dvd_right (hstep x List.mem_cons_self) accPoly) using 1
    ring

theorem natAbs_getD_le_coeffNorm1 (a : List ℤ) (k : ℕ) :
    (a.getD k 0).natAbs ≤ (Polynomial.ofCoeffList a).coeffNorm1 := by
  simpa only [Polynomial.coeff_ofCoeffList] using
    Polynomial.natAbs_coeff_le_coeffNorm1 (Polynomial.ofCoeffList a) k

/-- Every entry `a.getD k 0` has `encIntBin` bit-length at most `coeffNorm1.size + 1`. -/
theorem length_encIntBin_getD_le_coeffNorm1 (a : List ℤ) (k : ℕ) :
    (encIntBin (a.getD k 0)).length ≤ (Polynomial.ofCoeffList a).coeffNorm1.size + 1 := by
  rw [length_encIntBin]
  exact Nat.add_le_add_right (Nat.size_le_size (natAbs_getD_le_coeffNorm1 a k)) 1

theorem coeffNorm1_truncZJet_le (J : ℕ) (a : List ℤ) :
    (Polynomial.ofCoeffList (Cslib.truncZJet J a)).coeffNorm1 ≤
      (Polynomial.ofCoeffList a).coeffNorm1 := by
  simpa only [Cslib.ofCoeffList_truncZJet, Polynomial.coeffNorm1_ofCoeffList,
    Cslib.polyNorm1] using Cslib.polyNorm1_take_le a J

theorem coeffNorm1_truncZJet_singleton_le (J : ℕ) (c : ℤ) :
    (Polynomial.ofCoeffList (Cslib.truncZJet J [c])).coeffNorm1 ≤ c.natAbs :=
  (coeffNorm1_truncZJet_le J [c]).trans
    (by simp only [Polynomial.coeffNorm1_ofCoeffList, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, le_refl])

theorem coeffNorm1_add_le (J : ℕ) (a b : List ℤ) :
    (Polynomial.ofCoeffList (add J a b)).coeffNorm1 ≤
      (Polynomial.ofCoeffList a).coeffNorm1 + (Polynomial.ofCoeffList b).coeffNorm1 :=
  (coeffNorm1_truncZJet_le J _).trans
    (by simpa only [Polynomial.coeffNorm1_ofCoeffList, Cslib.polyNorm1] using
      Cslib.polyNorm1_polyAdd_le a b)

theorem coeffNorm1_sub_le (J : ℕ) (a b : List ℤ) :
    (Polynomial.ofCoeffList (sub J a b)).coeffNorm1 ≤
      (Polynomial.ofCoeffList a).coeffNorm1 + (Polynomial.ofCoeffList b).coeffNorm1 := by
  rw [Polynomial.coeffNorm1_ofCoeffList, sub, List.map_map, Function.comp_def,
    List.sum_map_range, Fin.sum_univ_eq_sum_range (fun k => (a.getD k 0 - b.getD k 0).natAbs)]
  have hcongr : (∑ k ∈ Finset.range J, (a.getD k 0 - b.getD k 0).natAbs) =
      ∑ k ∈ Finset.range J,
        ((Polynomial.ofCoeffList a - Polynomial.ofCoeffList b).coeff k).natAbs :=
    Finset.sum_congr rfl fun k _ => by
      rw [Polynomial.coeff_sub, Polynomial.coeff_ofCoeffList, Polynomial.coeff_ofCoeffList]
  exact (hcongr ▸ Polynomial.sum_natAbs_coeff_le_coeffNorm1 _ (Finset.range J)).trans
    (Polynomial.coeffNorm1_sub_le _ _)

theorem coeffNorm1_subConst_le (J : ℕ) (c : ℤ) (a : List ℤ) :
    (Polynomial.ofCoeffList (subConst J c a)).coeffNorm1 ≤
      c.natAbs + (Polynomial.ofCoeffList a).coeffNorm1 := by
  refine (coeffNorm1_sub_le J [c] a).trans (Nat.add_le_add_right ?_ _)
  simp only [Polynomial.coeffNorm1_ofCoeffList, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, le_refl]

/-- Submultiplicativity of `Polynomial.coeffNorm1` under `Cslib.mulZJet J`. -/
theorem coeffNorm1_mulZJet_le (J : ℕ) (a b : List ℤ) :
    (Polynomial.ofCoeffList (Cslib.mulZJet J a b)).coeffNorm1 ≤
      (Polynomial.ofCoeffList a).coeffNorm1 * (Polynomial.ofCoeffList b).coeffNorm1 := by
  simpa only [Polynomial.coeffNorm1_ofCoeffList, Cslib.polyNorm1] using
    (Cslib.polyNorm1_mulZJet_le J a b).trans
      (Nat.mul_le_mul (Cslib.polyNorm1_take_le a J) (Cslib.polyNorm1_take_le b J))

/-- Submultiplicative `Polynomial.coeffNorm1` bound across `foldl` of `Cslib.mulZJet J`. -/
theorem coeffNorm1_foldl_mulZJet_le {α : Type*} (J : ℕ) (l : List α)
    (stepJet : α → List ℤ) (bound : α → ℕ)
    (hstep : ∀ x ∈ l, (Polynomial.ofCoeffList (stepJet x)).coeffNorm1 ≤ bound x) (acc : List ℤ) :
    (Polynomial.ofCoeffList
      (l.foldl (fun s x => Cslib.mulZJet J s (stepJet x)) acc)).coeffNorm1 ≤
      (Polynomial.ofCoeffList acc).coeffNorm1 * (l.map bound).prod := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← Nat.mul_assoc]
    exact (ih (fun y hy => hstep y (List.mem_cons_of_mem _ hy))
      (Cslib.mulZJet J acc (stepJet x))).trans (Nat.mul_le_mul_right _
      ((coeffNorm1_mulZJet_le J acc (stepJet x)).trans
        (Nat.mul_le_mul_left _ (hstep x List.mem_cons_self))))

/-- Bit-size of `(ofCoeffList a).coeffNorm1` is bounded linearly in `(encList encIntBin a).length`.
-/
theorem size_coeffNorm1_le_length_encList (a : List ℤ) :
    (Polynomial.ofCoeffList a).coeffNorm1.size ≤ 2 * (encList encIntBin a).length := by
  rw [Polynomial.coeffNorm1_ofCoeffList]
  have hz : ∀ n ∈ a.map Int.natAbs, n.size ≤ (encList encIntBin a).length := fun n hn => by
    rcases List.mem_map.mp hn with ⟨z, hz, rfl⟩
    have hmem := length_le_encList_of_mem encIntBin hz
    rw [length_encIntBin] at hmem; omega
  have hsum := Nat.size_sum_le hz
  have hlen : a.length.size ≤ (encList encIntBin a).length :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (length_le_length_encList encIntBin a)
  rw [List.length_map] at hsum; exact hsum.trans (by omega)

/-- Encoded length of `a : List ℤ` is bounded by `a.length * (2 * coeffNorm1.size + 3)`. -/
theorem length_encList_encIntBin_le_of_coeffNorm1 (a : List ℤ) :
    (encList encIntBin a).length ≤
      a.length * (2 * (Polynomial.ofCoeffList a).coeffNorm1.size + 3) := by
  rw [length_encList]
  refine (List.sum_le_length_nsmul _ (2 * (Polynomial.ofCoeffList a).coeffNorm1.size + 3)
    fun n hn => ?_).trans (by simp)
  rcases List.mem_map.mp hn with ⟨z, hz, rfl⟩
  have hsz : z.natAbs.size ≤ (Polynomial.ofCoeffList a).coeffNorm1.size := by
    rw [Polynomial.coeffNorm1_ofCoeffList]
    exact Nat.size_le_size (List.le_sum_of_mem (List.mem_map_of_mem hz))
  rw [length_encIntBin]; omega

section PolyTime

local notation "encJet" => encList encIntBin

@[fun_prop] theorem computableInPolyTime_add' {γ : Type} {encIn : γ ↪ List Bool}
    {J : γ → ℕ} {a b : γ → List ℤ} (hJ : ComputableInPolyTime J encIn encUnary)
    (ha : ComputableInPolyTime a encIn encJet) (hb : ComputableInPolyTime b encIn encJet) :
    ComputableInPolyTime (fun x => add (J x) (a x) (b x)) encIn encJet := by
  unfold add; fun_prop

theorem computableInPolyTime_add :
    ComputableInPolyTime (fun p : (ℕ × List ℤ) × List ℤ => add p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encJet) encJet) encJet := by fun_prop

@[fun_prop] theorem computableInPolyTime_sub' {γ : Type} {encIn : γ ↪ List Bool}
    {J : γ → ℕ} {a b : γ → List ℤ} (hJ : ComputableInPolyTime J encIn encUnary)
    (ha : ComputableInPolyTime a encIn encJet) (hb : ComputableInPolyTime b encIn encJet) :
    ComputableInPolyTime (fun x => sub (J x) (a x) (b x)) encIn encJet :=
  have hx := ComputableInPolyTime.fst encIn encUnary
  have hk := ComputableInPolyTime.snd encIn encUnary
  ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hJ)
    (ComputableInPolyTime.intBin_sub.comp
      (((ha.comp hx).listGetDWithInput hk 0).prod ((hb.comp hx).listGetDWithInput hk 0)))

theorem computableInPolyTime_sub :
    ComputableInPolyTime (fun p : (ℕ × List ℤ) × List ℤ => sub p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encJet) encJet) encJet := by fun_prop

@[fun_prop] theorem computableInPolyTime_subConst' {γ : Type} {encIn : γ ↪ List Bool}
    {J : γ → ℕ} {c : γ → ℤ} {a : γ → List ℤ} (hJ : ComputableInPolyTime J encIn encUnary)
    (hc : ComputableInPolyTime c encIn encIntBin) (ha : ComputableInPolyTime a encIn encJet) :
    ComputableInPolyTime (fun x => subConst (J x) (c x) (a x)) encIn encJet :=
  computableInPolyTime_sub' hJ
    ((ComputableInPolyTime.snoc encIntBin).comp ((ComputableInPolyTime.const []).prod hc)) ha

theorem computableInPolyTime_subConst :
    ComputableInPolyTime (fun p : (ℕ × ℤ) × List ℤ => subConst p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encIntBin) encJet) encJet := by fun_prop

/-- Plain polynomial-time combinator for folding `Cslib.mulZJet` over `xs` from
`Cslib.truncZJet J [1]`, given a polynomial bound `K` on the bit-sizes of the step factors' `ℓ₁`
norms. -/
theorem computableInPolyTime_foldl_mulZJet {γ α : Type} {encIn : γ ↪ List Bool}
    (encA : α ↪ List Bool) {J : γ → ℕ} {δ : γ → ℤ} {xs : γ → List α}
    (factor : ℕ → ℤ → α → List ℤ)
    (hJ : ComputableInPolyTime J encIn encUnary) (hδ : ComputableInPolyTime δ encIn encIntBin)
    (hxs : ComputableInPolyTime xs encIn (encList encA))
    (hfac : ComputableInPolyTime
      (fun q : ((ℕ × ℤ) × List ℤ) × α => factor q.1.1.1 q.1.1.2 q.2)
      (encPair (encPair (encPair encUnary encIntBin) encJet) encA) encJet)
    {K : γ → ℕ} (hK : PolyBounded (fun x => (encIn x).length) K)
    (hsz : ∀ x, ∀ a ∈ xs x,
      (Polynomial.ofCoeffList (factor (J x) (δ x) a)).coeffNorm1.size ≤ K x) :
    ComputableInPolyTime
      (fun x => (xs x).foldl (fun acc a => Cslib.mulZJet (J x) acc (factor (J x) (δ x) a))
        (Cslib.truncZJet (J x) [1]))
      encIn encJet := by
  have hinit := Cslib.computableInPolyTime_truncZJet hJ (.const [1])
  have hqJ : ComputableInPolyTime (fun q : ((ℕ × ℤ) × List ℤ) × α => q.1.1.1)
      (encPair (encPair (encPair encUnary encIntBin) encJet) encA) encUnary := by fun_prop
  have hqAcc : ComputableInPolyTime (fun q : ((ℕ × ℤ) × List ℤ) × α => q.1.2)
      (encPair (encPair (encPair encUnary encIntBin) encJet) encA) encJet := by fun_prop
  have hstep := Cslib.computableInPolyTime_mulZJet hqJ hqAcc hfac
  refine ComputableInPolyTime.foldlWith (encA := encA)
    (par := fun x => (J x, δ x)) (list := xs) (init := fun x => Cslib.truncZJet (J x) [1])
    (step := fun par acc a => Cslib.mulZJet par.1 acc (factor par.1 par.2 a))
    (hJ.prod hδ) hxs hinit hstep
    (B := fun x => J x * (2 * (1 + (encList encA (xs x)).length * K x) + 3))
    (hJ.polyBounded.mul (((PolyBounded.const 2).mul
      ((PolyBounded.const 1).add (hxs.polyBounded_length.mul hK))).add (.const 3)))
    fun x i _ => ?_
  dsimp only
  have htake_len : ((xs x).take i).length ≤ (encList encA (xs x)).length :=
    (List.length_take_le' i (xs x)).trans (length_le_length_encList encA (xs x))
  have htrace : ∀ (ys : List α) (acc : List ℤ), acc.length = J x →
      (∀ a ∈ ys, (Polynomial.ofCoeffList (factor (J x) (δ x) a)).coeffNorm1.size ≤ K x) →
      let out := ys.foldl (fun s a => Cslib.mulZJet (J x) s (factor (J x) (δ x) a)) acc
      out.length = J x ∧ (Polynomial.ofCoeffList out).coeffNorm1.size ≤
        (Polynomial.ofCoeffList acc).coeffNorm1.size + ys.length * K x := by
    intro ys; induction ys with
    | nil => exact fun _ hlen _ => ⟨hlen, by simp⟩
    | cons a ys ih =>
      intro acc _ hys
      obtain ⟨hl, hs⟩ := ih (Cslib.mulZJet (J x) acc (factor (J x) (δ x) a))
        (Cslib.length_mulZJet _ _ _) (fun y hy => hys y (List.mem_cons_of_mem _ hy))
      have hm := (Nat.size_le_size (coeffNorm1_mulZJet_le (J x) acc (factor (J x) (δ x) a))).trans
        (Nat.size_mul_le _ _)
      have h0 := hys a List.mem_cons_self
      exact ⟨hl, hs.trans (by rw [List.length_cons, Nat.add_one_mul ys.length]; omega)⟩
  obtain ⟨hout_len, hout_sz⟩ := htrace ((xs x).take i) (Cslib.truncZJet (J x) [1])
    (Cslib.length_truncZJet (J x) [1]) fun a ha => hsz x a (List.mem_of_mem_take ha)
  have hinit_sz : (Polynomial.ofCoeffList (Cslib.truncZJet (J x) [1])).coeffNorm1.size ≤ 1 :=
    (Nat.size_le_size (coeffNorm1_truncZJet_singleton_le (J x) 1)).trans (by decide)
  have hbound := hout_sz.trans (Nat.add_le_add hinit_sz (Nat.mul_le_mul_right (K x) htake_len))
  refine (length_encList_encIntBin_le_of_coeffNorm1 _).trans ?_
  rw [hout_len]
  exact Nat.mul_le_mul_left (J x) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hbound) 3)

end PolyTime

end Cslib.IntJet
