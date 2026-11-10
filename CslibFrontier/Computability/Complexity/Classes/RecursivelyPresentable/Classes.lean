/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.PH
public import CslibFrontier.Computability.Complexity.Classes.RecursivelyPresentable
public import CslibFrontier.Computability.Complexity.Classes.Space
import CslibFrontier.Computability.Complexity.Classes.EXP.Decidable
import CslibFrontier.Computability.Complexity.Classes.Inclusions
import CslibFrontier.Computability.Complexity.Classes.Ladner.Density
import CslibFrontier.Computability.Complexity.Classes.Oracle.TQBF
import CslibFrontier.Computability.Complexity.Classes.PH.Closure
import CslibFrontier.Computability.Complexity.Classes.PH.Projection
import CslibFrontier.Computability.Complexity.Classes.Space.Closure
import CslibFrontier.Computability.Complexity.Problems.BoundedHalting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Unpair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec

/-!
# Recursive presentations and finite-variation closure of standard complexity classes

Schöning observed that the standard classes between `P` and `EXP` are recursively presentable and
closed under finite variations, so uniform diagonalization applies directly between any two of them
whenever they differ [Schöning][Schoening1982].

This module establishes both hypotheses for `NP`, `coNP`, each level `SigmaP k` and `PiP k` of the
polynomial hierarchy, `PH`, `PSPACE`, and `EXP`:

* **Closure under finite variations** holds on any encoded domain `enc : α ↪ List Bool`: for
  `SigmaP k`, `PiP k`, `NP`, `coNP`, `PH`, and `PSPACE` via Boolean closure with `P`
  (`Cslib.Complexity.ClosedUnderFiniteVariation.of_inter_union_mem_P`), and for `EXP` via its
  `≤ₘᵖ`-complete problem `Cslib.Complexity.BoundedHalting`.
* **Recursive presentability** holds on bit words (`encBits`): for `PSPACE` and `EXP` via their
  decidable `≤ₘᵖ`-complete problems (`encQBF '' TQBF` and `BoundedHalting`) using
  `Cslib.Complexity.PolyTimeComplete.recursivelyPresentable`; for `SigmaP k` and `PH` via a single
  computable alternating-block evaluator over clocked polynomial-time verifiers; and for `PiP k`,
  `NP`, and `coNP` by complementation (`Πₖ = coΣₖ`) and specialization at level `1`.

## Source notes

The printed theorem and example numbers in [Schöning][Schoening1982] were not consulted directly;
these presentations are stated in the library's binary-alphabet (`encBits`) and total native machine
(`Turing.MultiTapeTM`) conventions without quotation.

## Main results

* `Cslib.Complexity.closedUnderFiniteVariation_SigmaP`,
  `Cslib.Complexity.closedUnderFiniteVariation_PiP`,
  `Cslib.Complexity.closedUnderFiniteVariation_NP`,
  `Cslib.Complexity.closedUnderFiniteVariation_coNP`,
  `Cslib.Complexity.closedUnderFiniteVariation_PH`,
  `Cslib.Complexity.closedUnderFiniteVariation_PSPACE`,
  `Cslib.Complexity.closedUnderFiniteVariation_EXP`: closure under finite variations.
* `Cslib.Complexity.recursivelyPresentable_PSPACE`,
  `Cslib.Complexity.recursivelyPresentable_EXP`: presentations of `PSPACE` and `EXP` from their
  complete problems.
* `Cslib.Complexity.recursivelyPresentable_SigmaP`,
  `Cslib.Complexity.recursivelyPresentable_PiP`,
  `Cslib.Complexity.recursivelyPresentable_NP`,
  `Cslib.Complexity.recursivelyPresentable_coNP`,
  `Cslib.Complexity.recursivelyPresentable_PH`: presentations of the polynomial hierarchy and its
  levels.

## References

* [U. Schöning, *A uniform approach to obtain diagonal sets in complexity
  classes*][Schoening1982]
* [L. J. Stockmeyer, *The polynomial-time hierarchy*][Stockmeyer1976]
-/

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal ComputableInPolyTime

public section

namespace Cslib.Complexity

/-! ### Closure under finite variations -/

/-- **Each level `Σₖᵖ` is closed under finite variations.** -/
theorem closedUnderFiniteVariation_SigmaP {α : Type} (k : ℕ) (enc : α ↪ List Bool) :
    ClosedUnderFiniteVariation (SigmaP k enc) :=
  ClosedUnderFiniteVariation.of_inter_union_mem_P (enc := enc)
    (fun _ _ hL hM => inter_mem_SigmaP hL (SigmaP_mono (Nat.zero_le k) (P_subset_SigmaP_zero hM)))
    (fun _ _ hL hM => union_mem_SigmaP hL (SigmaP_mono (Nat.zero_le k) (P_subset_SigmaP_zero hM)))

/-- **Each level `Πₖᵖ` is closed under finite variations.** -/
theorem closedUnderFiniteVariation_PiP {α : Type} (k : ℕ) (enc : α ↪ List Bool) :
    ClosedUnderFiniteVariation (PiP k enc) :=
  PiP_eq_preimage_compl_SigmaP (k := k) (enc := enc) ▸
    (closedUnderFiniteVariation_SigmaP k enc).compl

/-- **`NP` is closed under finite variations.** -/
theorem closedUnderFiniteVariation_NP {α : Type} (enc : α ↪ List Bool) :
    ClosedUnderFiniteVariation (NP enc) :=
  SigmaP_one (enc := enc) ▸ closedUnderFiniteVariation_SigmaP 1 enc

/-- **`coNP` is closed under finite variations.** -/
theorem closedUnderFiniteVariation_coNP {α : Type} (enc : α ↪ List Bool) :
    ClosedUnderFiniteVariation (coNP enc) :=
  PiP_one_eq_coNP (enc := enc) ▸ closedUnderFiniteVariation_PiP 1 enc

/-- **`PH` is closed under finite variations.** -/
theorem closedUnderFiniteVariation_PH {α : Type} (enc : α ↪ List Bool) :
    ClosedUnderFiniteVariation (PH enc) :=
  ClosedUnderFiniteVariation.of_inter_union_mem_P (enc := enc)
    (fun _ _ hL hM => inter_mem_PH hL (P_subset_PH hM))
    (fun _ _ hL hM => union_mem_PH hL (P_subset_PH hM))

/-- **`PSPACE` is closed under finite variations.** -/
theorem closedUnderFiniteVariation_PSPACE {α : Type} (enc : α ↪ List Bool) :
    ClosedUnderFiniteVariation (PSPACE enc) :=
  ClosedUnderFiniteVariation.of_inter_union_mem_P (enc := enc)
    (fun _ _ hL hM => inter_mem_PSPACE hL (P_subset_PSPACE hM))
    (fun _ _ hL hM => union_mem_PSPACE hL (P_subset_PSPACE hM))

/-- **`EXP` is closed under finite variations.** -/
theorem closedUnderFiniteVariation_EXP {α : Type} (enc : α ↪ List Bool) :
    ClosedUnderFiniteVariation (EXP enc) := by
  obtain ⟨⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩⟩ := exists_notMem_and_mem_of_notMem_P BoundedHalting.notMem_P
  have heq : EXP enc = {A | PolyTimeReducible enc encBits A BoundedHalting} :=
    Set.ext fun A => ⟨fun hA => BoundedHalting.polyTimeHard_EXP enc A hA,
      fun hAB => hAB.mem_EXP BoundedHalting.mem_EXP⟩
  exact heq ▸ closedUnderFiniteVariation_polyTimeReducible_le hb₀ hb₁

/-! ### `PSPACE` and `EXP` via their `≤ₘᵖ`-complete languages -/

/-- **`PSPACE` on bit words is recursively presentable**, as the lower `≤ₘᵖ`-cone of
`encQBF '' TQBF`. -/
theorem recursivelyPresentable_PSPACE : RecursivelyPresentable encBits (PSPACE encBits) :=
  image_TQBF_pspaceComplete.recursivelyPresentable
    (isDecidable_of_mem_EXP (PSPACE_subset_EXP image_TQBF_mem_PSPACE))
    fun _ h => h.mem_PSPACE image_TQBF_mem_PSPACE

/-- **`EXP` on bit words is recursively presentable**, as the lower `≤ₘᵖ`-cone of
`BoundedHalting`. -/
theorem recursivelyPresentable_EXP : RecursivelyPresentable encBits (EXP encBits) :=
  BoundedHalting.polyTimeComplete_EXP.recursivelyPresentable BoundedHalting.isDecidable
    fun _ h => h.mem_EXP BoundedHalting.mem_EXP

/-! ### Uniform presentation of `Σₖᵖ`, `Πₖᵖ`, `NP`, `coNP`, and `PH` -/

namespace RecursivelyPresentablePH

/-- Cut consecutive blocks of uniform length `M` to lengths `p.eval n` for `p ∈ ps`. -/
private def trimUniformBlocks : List (Polynomial ℕ) → ℕ → ℕ → List Bool → List Bool
  | [], _, _, _ => []
  | p :: ps, n, M, w => w.take (p.eval n) ++ trimUniformBlocks ps n M (w.drop M)

private theorem alternation_trimUniformBlocks {ps : List (Polynomial ℕ)} {n M : ℕ}
    (hle : ∀ p ∈ ps, p.eval n ≤ M) {q : Bool} {P : List Bool → Prop} :
    Alternation q (List.replicate ps.length M) (fun w => P (trimUniformBlocks ps n M w)) ↔
      Alternation q (ps.map fun p => p.eval n) P := by
  induction ps generalizing q P with
  | nil => simp only [List.length_nil, List.replicate_zero, List.map_nil, alternation_nil,
      trimUniformBlocks]
  | cons p ps ih =>
    have hp : p.eval n ≤ M := hle p List.mem_cons_self
    have hps : ∀ r ∈ ps, r.eval n ≤ M := fun r hr => hle r (List.mem_cons_of_mem p hr)
    have hcut (w v : List Bool) (hw : w.length = M) :
        trimUniformBlocks (p :: ps) n M (w ++ v) =
          w.take (p.eval n) ++ trimUniformBlocks ps n M v :=
      by simp only [trimUniformBlocks, List.take_append_of_le_length (hw ▸ hp), List.drop_left' hw]
    have key (w : List Bool) (hw : w.length = M) {q' : Bool} :
        Alternation q' (List.replicate ps.length M)
          (fun v => P (trimUniformBlocks (p :: ps) n M (w ++ v))) ↔
        Alternation q' (ps.map fun r => r.eval n) fun v => P (w.take (p.eval n) ++ v) :=
      (alternation_congr fun v => by rw [hcut w v hw]).trans
        (ih hps (P := fun v => P (w.take (p.eval n) ++ v)))
    have hpad (w : List Bool) (hw : w.length = p.eval n) :
        (w ++ List.replicate (M - p.eval n) false).length = M := by
      rw [List.length_append, List.length_replicate, hw]
      omega
    have htake (w : List Bool) (hw : w.length = p.eval n) :
        (w ++ List.replicate (M - p.eval n) false).take (p.eval n) = w := by
      rw [← hw, List.take_left]
    have hlen (w : List Bool) (hw : w.length = M) : (w.take (p.eval n)).length = p.eval n := by
      rw [List.length_take, hw, Nat.min_eq_left hp]
    cases q
    · simp only [List.length_cons, List.replicate_succ, List.map_cons, alternation_false_cons]
      constructor
      · intro hP w hw
        have := (key _ (hpad w hw)).mp (hP _ (hpad w hw))
        rwa [htake w hw] at this
      · intro hP w hw
        exact (key w hw).mpr (hP _ (hlen w hw))
    · simp only [List.length_cons, List.replicate_succ, List.map_cons, alternation_true_cons]
      constructor
      · rintro ⟨w, hw, hP⟩
        exact ⟨_, hlen w hw, (key w hw).mp hP⟩
      · rintro ⟨w, hw, hP⟩
        refine ⟨_, hpad w hw, (key _ (hpad w hw)).mpr ?_⟩
        rwa [htake w hw]

private theorem computableInPolyTime_trimUniformBlocks (ps : List (Polynomial ℕ)) (d : ℕ) :
    ∀ {W : List Bool × List Bool → List Bool},
      ComputableInPolyTime W (encPair encBits encBits) encBits →
      ComputableInPolyTime
        (fun x : List Bool × List Bool =>
          trimUniformBlocks ps x.1.length (Ladner.clock d x.1.length) (W x))
        (encPair encBits encBits) encBits := by
  induction ps with
  | nil => intro _ _; exact .const []
  | cons p ps ih =>
    intro W hW
    have hn : ComputableInPolyTime (fun x : List Bool × List Bool => x.1.length)
        (encPair encBits encBits) encUnary := by fun_prop
    have hm : ComputableInPolyTime (fun x : List Bool × List Bool => Ladner.clock d x.1.length)
        (encPair encBits encBits) encUnary := (unary_pow d).comp (by fun_prop)
    exact bitsAppend (bitsTakeWithInput hW ((unary_eval p).comp hn))
      (ih (bitsDropWithInput hW hm))

private noncomputable def clockPoly (d : ℕ) : Polynomial ℕ := (2 * Polynomial.X + 2) ^ d

private theorem eval_clockPoly (d n : ℕ) : (clockPoly d).eval n = Ladner.clock d n := by
  simp only [clockPoly, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X, Ladner.clock]

private theorem eval_le_sum {ps : List (Polynomial ℕ)} {p : Polynomial ℕ} (hp : p ∈ ps) (n : ℕ) :
    p.eval n ≤ ps.sum.eval n := by
  induction ps with
  | nil => cases hp
  | cons q qs ih =>
    rw [List.sum_cons, Polynomial.eval_add]
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact Nat.le_add_right _ _
    · exact (ih hmem).trans (Nat.le_add_left _ _)

private theorem exists_clock_ge (ps : List (Polynomial ℕ)) :
    ∃ d : ℕ, ∀ p ∈ ps, ∀ n : ℕ, p.eval n ≤ Ladner.clock d n := by
  have hpoly : PolyBounded (fun n : ℕ => (encUnary n).length)
      (fun n : ℕ => (encUnary (ps.sum.eval n)).length) :=
    (ComputableInPolyTime.unary_eval ps.sum).polyBounded_length
  obtain ⟨c, e, hle⟩ := hpoly.exists_le
  refine ⟨c + e, fun p hp n => ?_⟩
  have hsum : ps.sum.eval n ≤ c * (n + 1) ^ e := by
    simpa only [encUnary_apply, List.length_replicate] using hle n
  calc p.eval n ≤ ps.sum.eval n := eval_le_sum hp n
    _ ≤ c * (n + 1) ^ e := hsum
    _ ≤ 2 ^ (c + e) * (n + 1) ^ (c + e) :=
        Nat.mul_le_mul ((Nat.lt_two_pow_self (n := c + e)).le.trans' (by omega))
          (Nat.pow_le_pow_right (by omega) (by omega))
    _ = Ladner.clock (c + e) n := by rw [Ladner.clock, ← mul_pow]; ring_nf

private theorem mem_SigmaP_encBits_iff {k : ℕ} {A : Set (List Bool)} :
    A ∈ SigmaP k encBits ↔
      ∃ d i : ℕ, ∀ a : List Bool, a ∈ A ↔
        Alternation true (List.replicate k (Ladner.clock d a.length))
          fun w => UniformDiagonalization.pIndexed (i, frame a ++ w) = true := by
  constructor
  · rintro ⟨ps, V, hk, hV, hA⟩
    obtain ⟨d, hd⟩ := exists_clock_ge ps
    let V' : List Bool × List Bool → Bool := fun x =>
      V (x.1, trimUniformBlocks ps x.1.length (Ladner.clock d x.1.length) x.2)
    have hV' : ComputableInPolyTime V' (encPair encBits encBits) encBool :=
      hV.comp ((ComputableInPolyTime.fst encBits encBits).prod
        (computableInPolyTime_trimUniformBlocks ps d (.snd encBits encBits)))
    have hW : {u : List Bool | V' (unframe u, dropFrame u) = true} ∈ P encBits := by
      have hunpairBits : ComputableInPolyTime (fun u : List Bool => (unframe u, dropFrame u))
          encBits (encPair encBits encBits) := by fun_prop
      exact ⟨fun u => V' (unframe u, dropFrame u), hV'.comp hunpairBits, fun _ => Iff.rfl⟩
    obtain ⟨i, -, hi⟩ := UniformDiagonalization.exists_setOf_pIndexed_eq hW 0
    refine ⟨d, i, fun a => ?_⟩
    rw [hA a, encBits_apply, ← alternation_trimUniformBlocks (fun p hp => hd p hp a.length), hk]
    refine alternation_congr fun w => ?_
    have hu := Set.ext_iff.mp hi (frame a ++ w)
    simpa only [Set.mem_ofPred_eq, unframe_frame_append, dropFrame_frame_append] using hu.symm
  · rintro ⟨d, i, h⟩
    obtain ⟨f, hf, hfi⟩ := UniformDiagonalization.setOf_pIndexed_mem_P i
    have hfeq : f = fun u => UniformDiagonalization.pIndexed (i, u) :=
      funext fun u => Bool.eq_iff_iff.mpr (hfi u).symm
    have hpair : ComputableInPolyTime (fun x : List Bool × List Bool => frame x.1 ++ x.2)
        (encPair encBits encBits) encBits := .of_eq fun _ => rfl
    refine ⟨List.replicate k (clockPoly d),
      fun x => UniformDiagonalization.pIndexed (i, frame x.1 ++ x.2),
      List.length_replicate, (hfeq ▸ hf).comp hpair, fun a => ?_⟩
    simpa only [List.map_replicate, eval_clockPoly, encBits_apply] using h a

/-! #### Truth-table folding of alternating bit blocks -/

/-- Combine consecutive bit pairs by `||` (`pol = true`) or `&&` (`pol = false`). -/
private def foldPair (pol : Bool) : List Bool → List Bool
  | b₀ :: b₁ :: rest => (if pol then b₀ || b₁ else b₀ && b₁) :: foldPair pol rest
  | _ => []

private theorem length_foldPair_le (pol : Bool) :
    ∀ l : List Bool, (foldPair pol l).length ≤ l.length
  | [] => le_rfl
  | [_] => Nat.zero_le _
  | _ :: _ :: rest => by
    simp only [foldPair, List.length_cons]
    have := length_foldPair_le pol rest
    omega

private theorem foldPair_flatMap_pair {α : Type} (pol : Bool) (xs : List α) (a b : α → Bool) :
    foldPair pol (xs.flatMap fun x => [a x, b x]) =
      xs.map fun x => if pol then a x || b x else a x && b x := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, foldPair, ih, List.map_cons]

private theorem iterate_foldPair_enumList_add (pol : Bool) (m : ℕ) :
    ∀ (n : ℕ) (g : List Bool → Bool),
      (foldPair pol)^[n] ((Cslib.BitString.enumList (m + n)).map g) =
        (Cslib.BitString.enumList m).map fun u =>
          if pol then (Cslib.BitString.enumList n).any fun v => g (v ++ u)
          else (Cslib.BitString.enumList n).all fun v => g (v ++ u)
  | 0, g => by
    simp only [Nat.add_zero, Function.iterate_zero, id_eq, Cslib.BitString.enumList_zero,
      List.any_cons, List.any_nil, Bool.or_false, List.all_cons, List.all_nil, Bool.and_true,
      List.nil_append, ite_self]
  | n + 1, g => by
    rw [show m + (n + 1) = (m + n) + 1 by omega, Function.iterate_succ_apply,
      Cslib.BitString.enumList_succ, List.map_flatMap]
    simp only [List.map_cons, List.map_nil]
    rw [foldPair_flatMap_pair, iterate_foldPair_enumList_add pol m n]
    refine List.map_congr_left fun u _ => ?_
    cases pol
    · simp only [Bool.false_eq_true, ↓reduceIte, Cslib.BitString.enumList_succ, List.all_flatMap,
        List.all_cons, List.all_nil, Bool.and_true, List.cons_append]
    · simp only [↓reduceIte, Cslib.BitString.enumList_succ, List.any_flatMap,
        List.any_cons, List.any_nil, Bool.or_false, List.cons_append]

private def initPol (q : Bool) (k : ℕ) : Bool := (!·)^[k + 1] q

private def stepBlock (M : ℕ) (s : Bool × List Bool) : Bool × List Bool :=
  (!s.1, (foldPair s.1)^[M] s.2)

open Classical in
private theorem iterate_stepBlock_enumList (M : ℕ) (f : List Bool → Bool) :
    ∀ (k : ℕ) (q : Bool) (p : ℕ),
      (stepBlock M)^[k] (initPol q k, (Cslib.BitString.enumList (p + k * M)).map fun u =>
          f u.reverse) =
        (!q, (Cslib.BitString.enumList p).map fun u =>
          decide (Alternation q (List.replicate k M) fun w => f (u.reverse ++ w) = true))
  | 0, q, p => by
    simp only [Nat.zero_mul, Nat.add_zero, Function.iterate_zero, id_eq, Prod.mk.injEq]
    refine ⟨rfl, List.map_congr_left fun u _ => ?_⟩
    apply Bool.eq_iff_iff.mpr
    simp only [List.replicate_zero, alternation_nil, List.append_nil, decide_eq_true_eq]
  | k + 1, q, p => by
    have hinit : initPol q (k + 1) = initPol (!q) k := by
      unfold initPol
      rw [Function.iterate_succ_apply]
    have hlen : p + (k + 1) * M = (p + M) + k * M := by ring
    rw [Function.iterate_succ_apply', hinit, hlen, iterate_stepBlock_enumList M f k (!q) (p + M)]
    simp only [stepBlock, Bool.not_not, Prod.mk.injEq, true_and]
    rw [iterate_foldPair_enumList_add q p M]
    refine List.map_congr_left fun u _ => ?_
    apply Bool.eq_iff_iff.mpr
    cases q
    · simp only [Bool.false_eq_true, ↓reduceIte, List.all_eq_true, Cslib.BitString.mem_enumList,
        decide_eq_true_eq, Bool.not_false, List.replicate_succ, alternation_false_cons]
      constructor
      · intro h w hw
        simpa only [List.reverse_append, List.reverse_reverse, List.append_assoc] using
          h w.reverse (by simp only [List.length_reverse, hw])
      · intro h v hv
        simpa only [List.reverse_append, List.append_assoc] using
          h v.reverse (by simp only [List.length_reverse, hv])
    · simp only [↓reduceIte, List.any_eq_true, Cslib.BitString.mem_enumList,
        decide_eq_true_eq, Bool.not_true, List.replicate_succ, alternation_true_cons]
      constructor
      · rintro ⟨v, hv, h⟩
        refine ⟨v.reverse, by simp only [List.length_reverse, hv], ?_⟩
        simpa only [List.reverse_append, List.append_assoc] using h
      · rintro ⟨w, hw, h⟩
        refine ⟨w.reverse, by simp only [List.length_reverse, hw], ?_⟩
        simpa only [List.reverse_append, List.reverse_reverse, List.append_assoc] using h

open Classical in
private theorem eval_alternation_eq_true_iff (q : Bool) (k M : ℕ) (f : List Bool → Bool) :
    ((stepBlock M)^[k] (initPol q k,
        (Cslib.BitString.enumList (k * M)).map fun u => f u.reverse)).2.headD false = true ↔
      Alternation q (List.replicate k M) fun w => f w = true := by
  have h := congrArg (fun l => l.headD false = true)
    (congrArg Prod.snd (iterate_stepBlock_enumList M f k q 0))
  rw [Nat.zero_add, Cslib.BitString.enumList_zero, List.map_cons, List.map_nil,
    List.headD_cons] at h
  rw [h, decide_eq_true_iff]
  exact alternation_congr fun w => by simp only [List.reverse_nil, List.nil_append]

/-! #### Polynomial-time certificate for capped evaluation -/

private def stepPair (pol : Bool) (acc : (Bool × Bool) × List Bool) (b : Bool) :
    (Bool × Bool) × List Bool :=
  if acc.1.1 then
    ((false, false), acc.2 ++ [if pol then acc.1.2 || b else acc.1.2 && b])
  else
    ((true, b), acc.2)

private theorem foldl_stepPair (pol : Bool) :
    ∀ (l : List Bool) (ys : List Bool),
      ((l.foldl (stepPair pol) ((false, false), ys)).2 = ys ++ foldPair pol l) ∧
      (∀ x, (l.foldl (stepPair pol) ((true, x), ys)).2 = ys ++ foldPair pol (x :: l))
  | [], ys => ⟨by simp only [List.foldl_nil, foldPair, List.append_nil],
      fun _ => by simp only [List.foldl_nil, foldPair, List.append_nil]⟩
  | b :: l, ys => by
    refine ⟨(foldl_stepPair pol l ys).2 b, fun x => ?_⟩
    simp only [List.foldl_cons, stepPair, ↓reduceIte, (foldl_stepPair pol l _).1,
      List.append_assoc, List.singleton_append, foldPair]

private theorem computableInPolyTime_foldPair :
    ComputableInPolyTime (fun p : Bool × List Bool => foldPair p.1 p.2)
      (encPair encBool encBits) encBits := by
  have hcomb : ComputableInPolyTime
      (fun q : (Bool × ((Bool × Bool) × List Bool)) × Bool =>
        if q.1.1 then q.1.2.1.2 || q.2 else q.1.2.1.2 && q.2)
      (encPair (encPair encBool (encPair (encPair encBool encBool) encBits)) encBool) encBool := by
    have hfin := ComputableInPolyTime.of_finite
      (encIn := encPair encBool (encPair encBool encBool)) (encOut := encBool)
      fun t : Bool × Bool × Bool => if t.1 then t.2.1 || t.2.2 else t.2.1 && t.2.2
    have harg : ComputableInPolyTime
        (fun q : (Bool × ((Bool × Bool) × List Bool)) × Bool => (q.1.1, q.1.2.1.2, q.2))
        (encPair (encPair encBool (encPair (encPair encBool encBool) encBits)) encBool)
        (encPair encBool (encPair encBool encBool)) := by fun_prop
    exact hfin.comp harg
  have hstep : ComputableInPolyTime
      (fun q : (Bool × ((Bool × Bool) × List Bool)) × Bool => stepPair q.1.1 q.1.2 q.2)
      (encPair (encPair encBool (encPair (encPair encBool encBool) encBits)) encBool)
      (encPair (encPair encBool encBool) encBits) := by
    unfold stepPair
    fun_prop
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encIn := encPair encBool encBits) (encP := encBool)
    (encB := encPair (encPair encBool encBool) encBits) (encA := encBool) (encL := encBits)
    (par := Prod.fst) (list := Prod.snd) (init := fun _ => ((false, false), []))
    (step := stepPair) (.fst encBool encBits) (.snd encBool encBits) (.const ((false, false), []))
    hstep (.const 1) fun _ state b _ => by
      by_cases h : state.1.1
      · simp only [stepPair, h, ↓reduceIte, length_encPair, encBool_apply, List.length_singleton,
          encBits_apply, List.length_append]
        omega
      · simp only [stepPair, h, Bool.false_eq_true, ↓reduceIte, length_encPair, encBool_apply,
          List.length_singleton, encBits_apply]
        omega
  have heq : (fun p : Bool × List Bool => foldPair p.1 p.2) =
      Prod.snd ∘ fun p : Bool × List Bool => p.2.foldl (stepPair p.1) ((false, false), []) := by
    funext ⟨pol, l⟩
    simpa only [Function.comp_apply, List.nil_append] using (foldl_stepPair pol l []).1.symm
  exact heq ▸ (ComputableInPolyTime.snd (encPair encBool encBool) encBits).comp hfold

private theorem length_iterate_foldPair_le (pol : Bool) :
    ∀ (r : ℕ) (l : List Bool), ((foldPair pol)^[r] l).length ≤ l.length
  | 0, _ => le_rfl
  | r + 1, l => by
    rw [Function.iterate_succ_apply']
    exact (length_foldPair_le pol _).trans (length_iterate_foldPair_le pol r l)

private theorem computableInPolyTime_stepBlock :
    ComputableInPolyTime (fun p : ℕ × (Bool × List Bool) => stepBlock p.1 p.2)
      (encPair encUnary (encPair encBool encBits)) (encPair encBool encBits) := by
  have hiter := ComputableInPolyTime.iterateWith
    (encIn := encPair encUnary (encPair encBool encBits))
    (encPar := encBool) (encState := encBits)
    (par := fun p => p.2.1) (count := fun p => p.1) (init := fun p => p.2.2) (step := foldPair)
    (by fun_prop) (by fun_prop) (by fun_prop) computableInPolyTime_foldPair
    (bound := fun p => (encPair encUnary (encPair encBool encBits) p).length) .self
    fun p r _ => by
      simp only [encBits_apply, length_encPair, encUnary_apply, List.length_replicate,
        encBool_apply, List.length_singleton]
      have := length_iterate_foldPair_le p.2.1 r p.2.2
      omega
  have hnot : ComputableInPolyTime (fun p : ℕ × (Bool × List Bool) => !p.2.1)
      (encPair encUnary (encPair encBool encBits)) encBool := by fun_prop
  exact hnot.prod hiter

private theorem length_iterate_stepBlock_le (M : ℕ) :
    ∀ (r : ℕ) (s : Bool × List Bool), ((stepBlock M)^[r] s).2.length ≤ s.2.length
  | 0, _ => le_rfl
  | r + 1, s => by
    rw [Function.iterate_succ_apply', stepBlock]
    exact (length_iterate_foldPair_le _ M _).trans (length_iterate_stepBlock_le M r s)

private theorem computableInPolyTime_initPol_true :
    ComputableInPolyTime (initPol true) encUnary encBool :=
  ComputableInPolyTime.iterate (encIn := encUnary) (encState := encBool)
    (count := fun k => k + 1) (init := fun _ => true) (step := Bool.not)
    (by fun_prop) (.const true) (by fun_prop) (.const 1)
    fun _ _ _ => by simp only [encBool_apply, List.length_singleton, le_rfl]

private abbrev CapInput := (((ℕ × ℕ) × List Bool) × ℕ) × ℕ

private abbrev encCapInput : CapInput ↪ List Bool :=
  encPair (encPair (encPair (encPair encUnary encUnary) encBits) encUnary) encUnary

private def capWidth (s : CapInput) : ℕ :=
  let km := s.1.1.1.1 * s.1.2
  km - (km - Nat.log 2 s.2)

private theorem capWidth_le_log (s : CapInput) : capWidth s ≤ Nat.log 2 s.2 := by
  dsimp only [capWidth]
  omega

private theorem two_pow_capWidth_budget (s : CapInput) :
    2 ^ capWidth s * (2 * capWidth s + 1) ≤
      ((encCapInput s).length + 1) * (2 * (encCapInput s).length + 1) := by
  have hle : capWidth s ≤ Nat.log 2 s.2 := capWidth_le_log s
  have hN : s.2 ≤ (encCapInput s).length := by
    simp only [encCapInput, length_encPair, encUnary_apply, List.length_replicate]
    omega
  rcases Nat.eq_zero_or_pos s.2 with hs | hs
  · have hlog0 : Nat.log 2 s.2 = 0 := by rw [hs]; simp
    have hcw : capWidth s = 0 := by
      have := capWidth_le_log s
      omega
    rw [hcw]
    simp only [Nat.pow_zero, Nat.mul_zero, Nat.zero_add, one_mul]
    exact Nat.mul_pos (by omega) (by omega)
  · have hpow : 2 ^ capWidth s ≤ s.2 :=
      (Nat.pow_le_pow_right (by decide) hle).trans (Nat.pow_log_le_self 2 (by omega))
    have hlt : capWidth s < 2 ^ capWidth s := Nat.lt_two_pow_self
    have hcw_le : capWidth s ≤ s.2 := hlt.le.trans hpow
    exact Nat.mul_le_mul (by omega) (by omega)

private def phEvalCap (s : CapInput) : Bool :=
  let k := s.1.1.1.1
  let i := s.1.1.1.2.unpair.2
  let a := s.1.1.2
  let M := s.1.2
  let P₂ := s.2
  let table := (Cslib.BitString.enumList (capWidth s)).map fun u =>
    UniformDiagonalization.pIndexedCap ((i, frame a ++ u.reverse), P₂)
  ((stepBlock M)^[k] (initPol true k, table)).2.headD false

private theorem computableInPolyTime_phEvalCap :
    ComputableInPolyTime phEvalCap encCapInput encBool := by
  let E₀ := encPair (encPair encUnary encUnary) encBits
  let E₁ := encPair E₀ encUnary
  have hs1 : ComputableInPolyTime (fun s : CapInput => s.1) encCapInput E₁ :=
    ComputableInPolyTime.fst E₁ encUnary
  have hs2 : ComputableInPolyTime (fun s : CapInput => s.2) encCapInput encUnary :=
    ComputableInPolyTime.snd E₁ encUnary
  have hp : ComputableInPolyTime (fun s : CapInput => s.1.1) encCapInput E₀ :=
    (ComputableInPolyTime.fst E₀ encUnary).comp hs1
  have hM : ComputableInPolyTime (fun s : CapInput => s.1.2) encCapInput encUnary :=
    (ComputableInPolyTime.snd E₀ encUnary).comp hs1
  have hkm_pair : ComputableInPolyTime (fun s : CapInput => s.1.1.1)
      encCapInput (encPair encUnary encUnary) :=
    (ComputableInPolyTime.fst (encPair encUnary encUnary) encBits).comp hp
  have hk : ComputableInPolyTime (fun s : CapInput => s.1.1.1.1) encCapInput encUnary :=
    (ComputableInPolyTime.fst encUnary encUnary).comp hkm_pair
  have hm : ComputableInPolyTime (fun s : CapInput => s.1.1.1.2) encCapInput encUnary :=
    (ComputableInPolyTime.snd encUnary encUnary).comp hkm_pair
  have hi : ComputableInPolyTime (fun s : CapInput => s.1.1.1.2.unpair.2) encCapInput encUnary :=
    (ComputableInPolyTime.snd encUnary encUnary).comp (ComputableInPolyTime.unary_unpair.comp hm)
  have ha : ComputableInPolyTime (fun s : CapInput => s.1.1.2) encCapInput encBits :=
    (ComputableInPolyTime.snd (encPair encUnary encUnary) encBits).comp hp
  have hkm : ComputableInPolyTime (fun s : CapInput => s.1.1.1.1 * s.1.2) encCapInput encUnary :=
    ComputableInPolyTime.unary_mul.comp (hk.prod hM)
  have hlog : ComputableInPolyTime (fun s : CapInput => Nat.log 2 s.2) encCapInput encUnary :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_log_two).comp hs2
  have hcw : ComputableInPolyTime capWidth encCapInput encUnary :=
    ComputableInPolyTime.unary_sub.comp
      (hkm.prod (ComputableInPolyTime.unary_sub.comp (hkm.prod hlog)))
  have henum : ComputableInPolyTime (fun s : CapInput => Cslib.BitString.enumList (capWidth s))
      encCapInput (encList encBits) :=
    ComputableInPolyTime.bitsEnumList hcw (size := fun L => (L + 1) * (2 * L + 1))
      (by fun_prop) two_pow_capWidth_budget
  have hcell : ComputableInPolyTime
      (fun q : CapInput × List Bool =>
        UniformDiagonalization.pIndexedCap
          ((q.1.1.1.1.2.unpair.2, frame q.1.1.1.2 ++ q.2.reverse), q.1.2))
      (encPair encCapInput encBits) encBool := by
    have hq1 : ComputableInPolyTime (fun q : CapInput × List Bool => q.1)
        (encPair encCapInput encBits) encCapInput := .fst encCapInput encBits
    have hq2 : ComputableInPolyTime (fun q : CapInput × List Bool => q.2)
        (encPair encCapInput encBits) encBits := .snd encCapInput encBits
    have hw : ComputableInPolyTime
        (fun q : CapInput × List Bool => frame q.1.1.1.2 ++ q.2.reverse)
        (encPair encCapInput encBits) encBits :=
      ComputableInPolyTime.bitsAppend (ComputableInPolyTime.frame.comp (ha.comp hq1))
        (ComputableInPolyTime.bitsReverse.comp hq2)
    have harg : ComputableInPolyTime
        (fun q : CapInput × List Bool =>
          ((q.1.1.1.1.2.unpair.2, frame q.1.1.1.2 ++ q.2.reverse), q.1.2))
        (encPair encCapInput encBits) (encPair (encPair encUnary encBits) encUnary) :=
      ((hi.comp hq1).prod hw).prod (hs2.comp hq1)
    exact UniformDiagonalization.computableInPolyTime_pIndexedCap.comp harg
  have htable : ComputableInPolyTime
      (fun s : CapInput => (Cslib.BitString.enumList (capWidth s)).map fun u =>
        UniformDiagonalization.pIndexedCap
          ((s.1.1.1.2.unpair.2, frame s.1.1.2 ++ u.reverse), s.2))
      encCapInput encBits :=
    ComputableInPolyTime.mapToBitsWithInput henum hcell
  have hpol : ComputableInPolyTime (fun s : CapInput => initPol true s.1.1.1.1)
      encCapInput encBool :=
    computableInPolyTime_initPol_true.comp hk
  have hpb : PolyBounded (fun s : CapInput => (encCapInput s).length)
      (fun s => 3 + ((encCapInput s).length + 1) * (2 * (encCapInput s).length + 1)) :=
    (PolyBounded.const 3).add
      ((PolyBounded.self.add (.const 1)).mul (((PolyBounded.const 2).mul .self).add (.const 1)))
  have hiter := ComputableInPolyTime.iterateWith
    (encIn := encCapInput) (encPar := encUnary) (encState := encPair encBool encBits)
    (par := fun s => s.1.2) (count := fun s => s.1.1.1.1)
    (init := fun s =>
      (initPol true s.1.1.1.1,
        (Cslib.BitString.enumList (capWidth s)).map fun u =>
          UniformDiagonalization.pIndexedCap
            ((s.1.1.1.2.unpair.2, frame s.1.1.2 ++ u.reverse), s.2)))
    (step := stepBlock)
    hM hk (hpol.prod htable) computableInPolyTime_stepBlock
    (bound := fun s => 3 + ((encCapInput s).length + 1) * (2 * (encCapInput s).length + 1))
    hpb
    fun s r _ => by
      have hlen := length_iterate_stepBlock_le s.1.2 r
        (initPol true s.1.1.1.1,
          (Cslib.BitString.enumList (capWidth s)).map fun u =>
            UniformDiagonalization.pIndexedCap
              ((s.1.1.1.2.unpair.2, frame s.1.1.2 ++ u.reverse), s.2))
      simp only [List.length_map, Cslib.BitString.length_enumList] at hlen
      have hbud := two_pow_capWidth_budget s
      have hpow : 2 ^ capWidth s ≤
          ((encCapInput s).length + 1) * (2 * (encCapInput s).length + 1) := by
        calc 2 ^ capWidth s ≤ 2 ^ capWidth s * (2 * capWidth s + 1) :=
              Nat.le_mul_of_pos_right _ (by omega)
          _ ≤ _ := hbud
      rw [length_encPair, encBool_apply, List.length_singleton, encBits_apply]
      omega
  have hhead : ComputableInPolyTime (fun q : Bool × List Bool => q.2.headD false)
      (encPair encBool encBits) encBool := by fun_prop
  exact hhead.comp hiter

open Classical in
private noncomputable def phPresent (p : (ℕ × ℕ) × List Bool) : Bool :=
  let k := p.1.1
  let d := p.1.2.unpair.1
  let i := p.1.2.unpair.2
  let a := p.2
  let M := Ladner.clock d a.length
  decide (Alternation true (List.replicate k M)
    fun w => UniformDiagonalization.pIndexed (i, frame a ++ w) = true)

private theorem isComputable_phPresent :
    IsComputable phPresent (encPair (encPair encUnary encUnary) encBits) encBool := by
  let E₀ := encPair (encPair encUnary encUnary) encBits
  let E₁ := encPair E₀ encUnary
  have hexp₁ : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List Bool => (p.2.length + 1) * p.1.2.unpair.1) E₀ encUnary := by
    fun_prop
  obtain ⟨_, _, hpad₁, -⟩ := hexp₁.exists_computableInO_unary_two_pow
  have hstage₁_raw := (isComputable_id E₀).prod (enc := E₁) hpad₁.isComputable
  have hclockStep : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × List Bool) × ℕ =>
        (q.1, Ladner.capPow (2 * q.1.2.length + 2) q.1.1.2.unpair.1 q.2)) E₁ E₁ := by
    fun_prop
  have hstage₁ : IsComputable
      (fun p : (ℕ × ℕ) × List Bool => (p, Ladner.clock p.1.2.unpair.1 p.2.length)) E₀ E₁ := by
    convert hclockStep.isComputable.comp hstage₁_raw using 1
    funext p
    have hc := UniformDiagonalization.clock_le_two_pow p.1.2.unpair.1 p.2.length
    rw [Ladner.clock] at hc
    simp only [Function.comp_apply, id_eq, Ladner.capPow, Ladner.clock, min_eq_left hc]
  let exp₂ : (((ℕ × ℕ) × List Bool) × ℕ) → ℕ := fun r =>
    r.1.1.1 * r.2 + (2 * r.1.2.length + 2 + r.1.1.1 * r.2) * r.1.1.2.unpair.2 + 1
  have hexp₂ : ComputableInPolyTime exp₂ E₁ encUnary := by
    unfold exp₂
    fun_prop
  obtain ⟨_, _, hpad₂, -⟩ := hexp₂.exists_computableInO_unary_two_pow
  have hstage₂ := (isComputable_id E₁).prod (enc := encCapInput) hpad₂.isComputable
  have htot := computableInPolyTime_phEvalCap.isComputable.comp (hstage₂.comp hstage₁)
  convert htot using 1
  funext p
  let M := Ladner.clock p.1.2.unpair.1 p.2.length
  let E := exp₂ (p, M)
  let s : CapInput := ((p, M), 2 ^ E)
  change phPresent p = phEvalCap s
  have hlog : Nat.log 2 (2 ^ E) = E := Nat.log_pow (by decide) E
  have hcw : capWidth s = p.1.1 * M := by
    simp only [capWidth, s, hlog, E, exp₂]
    omega
  have htable : ((Cslib.BitString.enumList (capWidth s)).map fun u =>
      UniformDiagonalization.pIndexedCap ((p.1.2.unpair.2, frame p.2 ++ u.reverse), 2 ^ E)) =
      (Cslib.BitString.enumList (p.1.1 * M)).map fun u =>
        UniformDiagonalization.pIndexed (p.1.2.unpair.2, frame p.2 ++ u.reverse) := by
    rw [hcw]
    refine List.map_congr_left fun u hu => ?_
    have hulen : u.length = p.1.1 * M := Cslib.BitString.mem_enumList.mp hu
    have hflen : (frame p.2 ++ u.reverse).length = 2 * p.2.length + 1 + p.1.1 * M := by
      rw [List.length_append, length_frame, List.length_reverse, hulen]
    have hclk : Ladner.clock p.1.2.unpair.2 (frame p.2 ++ u.reverse).length ≤ 2 ^ E := by
      have hexp_le : ((frame p.2 ++ u.reverse).length + 1) * p.1.2.unpair.2 ≤ E := by
        rw [hflen]
        have heq : 2 * p.2.length + 1 + p.1.1 * M + 1 = 2 * p.2.length + 2 + p.1.1 * M := by omega
        rw [heq]
        simp only [E, exp₂]
        omega
      exact (UniformDiagonalization.clock_le_two_pow _ _).trans
        (Nat.pow_le_pow_right (by decide) hexp_le)
    exact UniformDiagonalization.pIndexedCap_eq_pIndexed_of_le hclk
  simp only [phEvalCap, s, htable, phPresent, M]
  classical
  exact Bool.eq_iff_iff.mpr
    (decide_eq_true_iff.trans (eval_alternation_eq_true_iff true p.1.1 M
      (fun w => UniformDiagonalization.pIndexed (p.1.2.unpair.2, frame p.2 ++ w))).symm)

private theorem sigmaP_eq_range_phPresent (k : ℕ) :
    SigmaP k encBits = Set.range fun m => {a | phPresent ((k, m), a) = true} := by
  ext A
  rw [mem_SigmaP_encBits_iff]
  simp only [Set.mem_range, phPresent, decide_eq_true_eq]
  constructor
  · rintro ⟨d, i, h⟩
    refine ⟨Nat.pair d i, Set.ext fun a => ?_⟩
    simp only [Set.mem_ofPred_eq, Nat.unpair_pair, ← h a]
  · rintro ⟨m, rfl⟩
    exact ⟨m.unpair.1, m.unpair.2, fun _ => Iff.rfl⟩

end RecursivelyPresentablePH

/-- **Each level `Σₖᵖ` on bit words is recursively presentable.** -/
theorem recursivelyPresentable_SigmaP (k : ℕ) :
    RecursivelyPresentable encBits (SigmaP k encBits) := by
  have hin : ComputableInPolyTime (fun p : ℕ × List Bool => ((k, p.1), p.2))
      (encPair encUnary encBits) (encPair (encPair encUnary encUnary) encBits) := by fun_prop
  exact ⟨fun p => RecursivelyPresentablePH.phPresent ((k, p.1), p.2),
    RecursivelyPresentablePH.isComputable_phPresent.comp hin.isComputable,
    RecursivelyPresentablePH.sigmaP_eq_range_phPresent k⟩

/-- **Each level `Πₖᵖ` on bit words is recursively presentable.** -/
theorem recursivelyPresentable_PiP (k : ℕ) :
    RecursivelyPresentable encBits (PiP k encBits) :=
  PiP_eq_preimage_compl_SigmaP (k := k) (enc := encBits) ▸
    (recursivelyPresentable_SigmaP k).compl

/-- **`NP` on bit words is recursively presentable.** -/
theorem recursivelyPresentable_NP : RecursivelyPresentable encBits (NP encBits) :=
  SigmaP_one (enc := encBits) ▸ recursivelyPresentable_SigmaP 1

/-- **`coNP` on bit words is recursively presentable.** -/
theorem recursivelyPresentable_coNP : RecursivelyPresentable encBits (coNP encBits) :=
  PiP_one_eq_coNP (enc := encBits) ▸ recursivelyPresentable_PiP 1

/-- **`PH` on bit words is recursively presentable**, as the countable union of the uniformly
presented levels `Σₖᵖ`. -/
theorem recursivelyPresentable_PH : RecursivelyPresentable encBits (PH encBits) :=
  RecursivelyPresentable.iUnion_of_isComputable RecursivelyPresentablePH.isComputable_phPresent
    RecursivelyPresentablePH.sigmaP_eq_range_phPresent

end Cslib.Complexity
