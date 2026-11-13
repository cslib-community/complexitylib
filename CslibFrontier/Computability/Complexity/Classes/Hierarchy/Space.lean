/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Constructible
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.TinyDesc
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Complexity.Classes.Space.Time
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.SpaceBudget
import CslibFrontier.Computability.Complexity.Classes.Constructible.Space
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.SpaceDiagonalBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigOLe
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.SmallSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import CslibFrontier.Foundations.Data.Nat.AffineBound

/-!
# The space hierarchy theorem

`Cslib.Complexity.DSPACE` is defined in `Classes.Space.Basic`, and
`Cslib.Complexity.SpaceConstructible` in `Classes.Constructible`. Their generic APIs and
the concrete `L` and `PSPACE` characterizations do not depend on this hierarchy theorem.

## The space hierarchy theorem

`Cslib.Complexity.spaceDiagonal G` runs the machine described at the start of its input `x`, when
the description is tiny (`Cslib.Complexity.Diagonal.tinyDesc`), on `x` with the universal machine
within a space budget (`Turing.MultiTapeTM.Universal.budgetedUniversal`): for `2 ^ G n` steps, with
the configurations of the simulation encoded within `G n` bits. It negates the verdict, and answers
`false` on other inputs. The budgeted universal machine is the in-place universal run with a budget
test at the end of each pass, within space linear in the description, the budget and the lengths
of the clock and of `n` in binary (`Turing.MultiTapeTM.Universal.budgetSpace_le`).

The diagonal does not hold its input. A tiny description has at most `log₂ (log₂ n + 1)` bits, so
it is decoded in logarithmic space
(`Cslib.Complexity.Diagonal.computableInLogSpace_decodeDesc_tinyCut`), and the input of the
universal machine (the description, the symbols of `x`, the clock and the budget) is recomputed on
demand in logarithmic space from `x`, never charged. So the diagonal takes space `O(G n + log n)`
(`Cslib.Complexity.computableInTimeAndSpace_spaceDiagonal`) and decides a problem in `DSPACE G`
when `log₂ n ≤ G n` (`Cslib.Complexity.setOf_spaceDiagonal_mem_DSPACE`).

Let a machine decide the same problem within space `c₁ * f n + c₂`, where every `c * f n + c` is
eventually below `G n`, and let `4 * log₂ n ≤ G n`. It halts within its number of configurations,
`(n + 2) * 2 ^ O(f n)`, which is below the clock `2 ^ G n`. The configurations of its simulation
take `O(f n + log n)` bits, with a factor linear in its description: the overhead of the universal
machine is a constant factor for each simulated machine, eventually within the budget
(`Cslib.Complexity.Diagonal.eventually_cfgSpaceBound_le`). So on its
own description, padded to a doubly exponential length where it is tiny, the diagonal answers the
negation of its answer (`Cslib.Complexity.setOf_spaceDiagonal_notMem_DSPACE`). Hence the space
hierarchy theorem [Stearns, Hartmanis and Lewis][StearnsHartmanisLewis1965],
[Sipser, Theorem 9.3][Sipser2013], [Arora and Barak, Theorem 4.8][AroraBarak09]:

* `DSPACE f ⊂ DSPACE g` for a space-constructible `g` with `log₂ n ≤ g n`, when every
  `c * f n + c` is eventually below `g n` (`Cslib.Complexity.DSPACE_ssubset_DSPACE`);
* `L ⊂ DSPACE (log₂ n ^ 2)` (`Cslib.Complexity.L_ssubset_DSPACE_log2_sq`), and more generally
  `DSPACE (log₂ n ^ (k + 1)) ⊂ DSPACE (log₂ n ^ (k + 2))`
  (`Cslib.Complexity.DSPACE_log2_pow_ssubset_DSPACE_log2_pow_succ`);
* `DSPACE (n ^ k) ⊂ DSPACE (n ^ (k + 1))` (`Cslib.Complexity.DSPACE_pow_ssubset_DSPACE_pow_succ`);
* `L ⊂ PSPACE` (`Cslib.Complexity.L_ssubset_PSPACE`).

The gap `f = o(g)` and the lower bound `log n ≤ g n` are the textbook ones. The nondeterministic
space hierarchy, under the same hypotheses, is in
`CslibFrontier.Computability.Complexity.Classes.Hierarchy.NondeterministicSpace`.

## Main definitions

* `Cslib.Complexity.spaceDiagonal`: the diagonal within a space budget.

## Main results

* `Cslib.Complexity.spaceDiagonal_desc`: the diagonal negates the answer of a machine on its padded
  description, within the clock and the budget.
* `Cslib.Complexity.computableInTimeAndSpace_spaceDiagonal`: the diagonal within space `G` is
  computable within space `O(G n + log n)`.
* `Cslib.Complexity.setOf_spaceDiagonal_mem_DSPACE`,
  `Cslib.Complexity.setOf_spaceDiagonal_notMem_DSPACE`: the diagonal within space `G` is decidable
  within space `O(G)`, and not within space `O(f)` for `f = o(G)`.
* `Cslib.Complexity.DSPACE_ssubset_DSPACE`: the space hierarchy theorem.
* `Cslib.Complexity.L_ssubset_DSPACE_log2_sq`,
  `Cslib.Complexity.DSPACE_log2_pow_ssubset_DSPACE_log2_pow_succ`,
  `Cslib.Complexity.DSPACE_pow_ssubset_DSPACE_pow_succ`, `Cslib.Complexity.L_ssubset_PSPACE`: its
  corollaries.
* `Cslib.Complexity.eventually_mul_log2_pow_add_le`,
  `Cslib.Complexity.eventually_mul_pow_add_le_succ_pow`: the gaps between consecutive powers of
  `log₂ n` and of `n`, shared with the nondeterministic corollaries.

## References

* [R. E. Stearns, J. Hartmanis, P. M. Lewis II, *Hierarchies of memory limited
  computations*][StearnsHartmanisLewis1965]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]

The padded diagonal argument follows the time hierarchy theorem
(`CslibFrontier.Computability.Complexity.Classes.Hierarchy.Time`), here on Christian Reitwiessner's
in-place universal interpreter within a space budget.
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Filter

/-! ### The diagonal within a space budget -/

/-- **The diagonal within space `G`.** On a word `x` of length `n` whose framed description is
tiny (`Cslib.Complexity.Diagonal.tinyDesc`), run the described machine on `x`, under the coding
`Turing.MultiTapeTM.Universal.eBit` of bits, for `2 ^ G n` steps within the budget of `G n` bits
for the encoded configurations of the simulation (`Turing.MultiTapeTM.Universal.budgetedUniversal`),
and return `false` exactly when it has halted with output `[true]`; answer `false` on other
words. -/
@[expose] def spaceDiagonal (G : ℕ → ℕ) (x : List Bool) : Bool :=
  if Diagonal.tinyDesc x then
    Diagonal.verdict (budgetedUniversal (decodeDesc (unframe x), x.map eBit, 2 ^ G x.length,
      G x.length))
  else false

/-- The input of the budgeted universal machine in the diagonal within space `G`. -/
private def universalInput (G : ℕ → ℕ) (x : List Bool) : Desc × List ℕ × ℕ × ℕ :=
  (decodeDesc (Diagonal.tinyCut x), x.map eBit, 2 ^ G x.length, G x.length)

private theorem exists_space_of_bigOLe {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} {t s V : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) (hs : s ≼ V) :
    ∃ c, ComputableInTimeAndSpace f encIn encOut t fun a => c * (V a + 1) :=
  let ⟨c, hc⟩ := hs
  ⟨c, h.mono (fun _ => le_rfl) hc⟩

open Diagonal in
/-- **The diagonal within space `G` is computable within space `O(G n + log n)`**, for a
space-constructible `G`. The tiny description, decoded, and the symbols of the input are computed
in logarithmic space, and the clock `2 ^ G n` in binary and the budget `G n` in unary within space
`O(G n)`; this input of the budgeted universal machine is recomputed on demand, not stored. The
budgeted universal run takes space linear in the description, the budget and the lengths of the
clock and of `n` in binary (`Turing.MultiTapeTM.Universal.budgetSpace_le`), and the tininess test
logarithmic space. -/
theorem computableInTimeAndSpace_spaceDiagonal {G : ℕ → ℕ} (hG : SpaceConstructible G) :
    ∃ c t, ComputableInTimeAndSpace (spaceDiagonal G) encBits encBool t
      fun x => c * (G x.length + Nat.log2 x.length + 1) := by
  -- the description and the symbols of the input, in logarithmic space
  have hD : ComputableInLogSpace (fun x => decodeDesc (tinyCut x)) encBits (encFramed eDesc) :=
    (ComputableInLogSpace.of_frame (encIn := eDesc) (encOut := encFramed eDesc)
      (f := fun d => d) fun _ => rfl).comp computableInLogSpace_decodeDesc_tinyCut
  have hS : ComputableInLogSpace (fun x : List Bool => x.map eBit) encBits
      (encFramed (encList encUnary)) :=
    (ComputableInLogSpace.of_frame (encIn := encList encUnary)
      (encOut := encFramed (encList encUnary)) (f := fun l => l) fun _ => rfl).comp
      ((symbolsT.computableInLogSpace (encIn := encTrueDoubled) (encOut := encList encUnary)
        (f := fun x : List Bool => x.map eBit) fun x => (symbolsT_run x).symm).comp
        (trueDoubleT.computableInLogSpace (encIn := encBits) (encOut := encTrueDoubled)
          (f := fun x => x) fun x => (trueDoubleT_run x).symm))
  have hAB := ComputableInLogSpace.append (encOut := encBits)
    (g := fun x => frame (eDesc (decodeDesc (tinyCut x))) ++
      frame (encList encUnary (x.map eBit))) hD hS fun _ => rfl
  obtain ⟨tAB, cAB, hAB⟩ := hAB
  obtain ⟨dAB, hAB⟩ := hAB.exists_computableTidilyInTimeAndSpace
  -- the clock and the budget, within space `O(G n)`
  obtain ⟨TG, hGb⟩ := hG.computableInO
  have hGu := ComputableInO.natToUnary.comp hGb
  have hclock := ((ComputableInDegree.two_pow_length encUnary).inO_one.comp_linear
    hGu).of_enc_eq (encC := encNat) (g := fun x : List Bool => 2 ^ G x.length) fun x => by
      simp only [Function.comp_apply, encUnary_apply, List.length_replicate]
  obtain ⟨cC, hCt, -⟩ := ((hclock.prod hGu).tidy).mono (S' := fun x : List Bool => G x.length)
    (T' := fun x => TG x + (G x.length + 1) ^ 2 + (TG x + (G x.length + 1) ^ 2)) 4
    (fun x => by have := Nat.le_self_pow two_ne_zero (G x.length + 1); omega)
    (fun x => by omega)
  -- the input of the budgeted universal machine, recomputed and never charged
  obtain ⟨kF, hF⟩ := hAB.append hCt (encOut := eInS) (g := universalInput G) fun x => by
    simp only [universalInput, eInS, encPair_apply, encBits_apply, List.append_assoc]; rfl
  -- the budgeted universal run and the verdict
  obtain ⟨cV, hV, -⟩ := computableInO_verdict.comp
    computableTidilyInO_budgetedUniversal.computableInO
  obtain ⟨cU, hU⟩ := ComputableInTimeAndSpace.comp_space hF.computableInTimeAndSpace hV
  obtain ⟨dU, hU⟩ := hU.exists_computableTidilyInTimeAndSpace
  -- the test and the case distinction
  obtain ⟨tc, cc, hc⟩ := computableInLogSpace_tinyDesc
  obtain ⟨dc, hc⟩ := hc.exists_computableTidilyInTimeAndSpace
  obtain ⟨tg, cg, hg⟩ := ComputableInLogSpace.const (encIn := encBits) (encMid := encBool) false
  obtain ⟨dg, hg⟩ := hg.exists_computableTidilyInTimeAndSpace
  obtain ⟨k, h⟩ := hc.ite (hU.restrict _) (hg.restrict _)
  have e : (fun x => if tinyDesc x then ((Diagonal.verdict ∘ budgetedUniversal) ∘
      universalInput G) x else false) = spaceDiagonal G := by
    funext x
    simp only [spaceDiagonal, Function.comp_apply, universalInput]
    split_ifs with hx
    · rw [tinyCut_of_tinyDesc hx]
    · rfl
  rw [e] at h
  -- the sizes of the pieces, up to constants, in `G n + log₂ n`
  obtain ⟨cD, hcD⟩ := exists_length_eDesc_decodeDesc_tinyCut_le
  have hl : (fun x : List Bool => Nat.log2 x.length) ≼
      fun x : List Bool => G x.length + Nat.log2 x.length := .of_le fun _ => Nat.le_add_left _ _
  have hGl : (fun x : List Bool => G x.length) ≼
      fun x : List Bool => G x.length + Nat.log2 x.length := .of_le fun _ => Nat.le_add_right _ _
  have hN : (fun x : List Bool => (encNat (x.length + 1)).length) ≼
      fun x : List Bool => G x.length + Nat.log2 x.length :=
    .of_le_linear 1 2 fun x => (length_encNat_le_log2_add_two le_rfl).trans (by omega)
  have hBS : (fun x => budgetSpace (universalInput G x)) ≼
      fun x : List Bool => G x.length + Nat.log2 x.length := by
    refine .of_le_linear (60 * cD + 20) (60 * cD + 200) fun x => ?_
    have hB : budgetSpace (universalInput G x) ≤ _ :=
      budgetSpace_le (decodeDesc (tinyCut x)) (x.map eBit) (G x.length) (2 ^ G x.length)
    have hD : (eDesc (decodeDesc (tinyCut x))).length ≤ cD * (Nat.log2 x.length + 1) := hcD x
    have hclk : (encNat (2 ^ G x.length)).length = G x.length + 1 := by
      rw [encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
    have hn : (encNat ((x.map eBit).length + 1)).length ≤ Nat.log2 x.length + 2 := by
      rw [List.length_map]; exact length_encNat_le_log2_add_two le_rfl
    have hmax : (x.map eBit).foldr max 0 ≤ 1 := listMax_le fun b _ => by cases b <;> decide
    simp only [descLen] at hB
    nlinarith [Nat.zero_le (cD * G x.length)]
  have hO : (fun x => (eOut (budgetedUniversal (universalInput G x))).length) ≼
      fun x : List Bool => G x.length + Nat.log2 x.length :=
    (BigOLe.of_le fun x => length_eOut_budgetedUniversal_le (decodeDesc (tinyCut x)) (x.map eBit)
      (G x.length) (2 ^ G x.length)).trans hBS
  have hE : (fun x => (encNat ((eInS (universalInput G x)).length + 1)).length) ≼
      fun x : List Bool => G x.length + Nat.log2 x.length := by
    refine .of_le_linear (2 * cD + 4) (2 * cD + 20) fun x => ?_
    have hD : (eDesc (decodeDesc (tinyCut x))).length ≤ cD * (Nat.log2 x.length + 1) := hcD x
    have hS : (encList encUnary (x.map eBit)).length ≤ (x.map eBit).length * (2 * 1 + 1) :=
      length_encList_le _ _ fun b hb => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
        rw [encUnary_apply, List.length_replicate]
        cases c <;> decide
    have hclk : (encNat (2 ^ G x.length)).length = G x.length + 1 := by
      rw [encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
    have hlen : (eInS (universalInput G x)).length + 1 ≤
        (2 * (eDesc (decodeDesc (tinyCut x))).length + 3 * G x.length + 12) * (x.length + 1) := by
      simp only [universalInput, eInS, length_encPair, encUnary_apply, List.length_replicate, hclk,
        List.length_map] at hS ⊢
      nlinarith
    have h₁ := (length_encNat_mono hlen).trans (length_encNat_mul_le _ _)
    have h₂ := length_encNat_le_self (2 * (eDesc (decodeDesc (tinyCut x))).length +
      3 * G x.length + 12)
    have h₃ : (encNat (x.length + 1)).length ≤ Nat.log2 x.length + 2 :=
      length_encNat_le_log2_add_two le_rfl
    nlinarith [Nat.zero_le (cD * G x.length)]
  obtain ⟨K, hK⟩ := exists_space_of_bigOLe h.computableInTimeAndSpace
    (V := fun x : List Bool => G x.length + Nat.log2 x.length) (by
      simp only [encBits_apply]
      bigO)
  exact ⟨K, _, hK⟩

/-- **The diagonal within space `G` decides a problem in `DSPACE G`**, for a space-constructible
`G` with `log₂ n ≤ G n`. -/
theorem setOf_spaceDiagonal_mem_DSPACE {G : ℕ → ℕ} (hG : SpaceConstructible G)
    (hlog : ∀ n, Nat.log2 n ≤ G n) : {x | spaceDiagonal G x = true} ∈ DSPACE encBits G := by
  obtain ⟨c, t, hc⟩ := computableInTimeAndSpace_spaceDiagonal hG
  refine mem_DSPACE_iff.mpr ⟨2 * c, c, t, decidableInTimeAndSpace_iff.mpr
    ⟨spaceDiagonal G, hc.mono (fun _ => le_rfl) fun x => ?_, fun x => Iff.rfl⟩⟩
  have := hlog x.length
  simp only [encBits_apply]
  nlinarith

open Diagonal in
/-- On a tiny padded description, the diagonal within space `G` negates the answer of a machine
that halts within the clock `2 ^ G n` and whose simulated configurations fit within the budget
`G n`. -/
theorem spaceDiagonal_desc {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (pad : List Bool) (G : ℕ → ℕ) {b : Bool}
    (htiny : tinyDesc (frame (eDesc (desc eS eBit tm)) ++ pad) = true)
    (hbudget : cfgSpace (desc eS eBit tm) ((frame (eDesc (desc eS eBit tm)) ++ pad).map eBit)
      (2 ^ G (frame (eDesc (desc eS eBit tm)) ++ pad).length) ≤
      G (frame (eDesc (desc eS eBit tm)) ++ pad).length)
    (hhalt : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS eBit tm)) ++ pad))
      (2 ^ G (frame (eDesc (desc eS eBit tm)) ++ pad).length)).Halted)
    (hout : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS eBit tm)) ++ pad))
      (2 ^ G (frame (eDesc (desc eS eBit tm)) ++ pad).length)).output = [b]) :
    spaceDiagonal G (frame (eDesc (desc eS eBit tm)) ++ pad) = !b := by
  simp only [spaceDiagonal, htiny, ↓reduceIte]
  rw [decodeDesc_unframe_frame_append, budgetedUniversal_desc eS eBit tm _ _ _ hbudget]
  simp only [Cfg.Halted] at hhalt
  rw [hhalt, hout]
  cases b <;> rfl

open Diagonal in
/-- **The diagonal argument for space.** If every `c * f n + c` is eventually below `G n` and
`4 * log₂ n ≤ G n`, the problem of the diagonal within space `G` is not in `DSPACE f`. A decider
within space `O(f)` halts within its number of configurations, `(n + 2) * 2 ^ O(f n)`, which is
below the clock `2 ^ G n`, and the configurations of its simulation take `O(f n + log n)` bits,
eventually within the budget `G n`; so on its own description, padded to a tiny one beyond these
points, the diagonal answers the negation of its answer. -/
theorem setOf_spaceDiagonal_notMem_DSPACE {f G : ℕ → ℕ} (hlog : ∀ n, 4 * Nat.log2 n ≤ G n)
    (hfG : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ G n) :
    {x | spaceDiagonal G x = true} ∉ DSPACE encBits f := by
  rintro ⟨c₁, c₂, t, hA⟩
  obtain ⟨g, ⟨k, State, hfinite, tm, htm⟩, hg⟩ := decidableInTimeAndSpace_iff.mp hA
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  set D := descLen (desc eS eBit tm) with hD
  set e := storageBoundExp Bool k
  set base := storageBoundBase Bool State k
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hfG (4 * e * (c₁ + c₂) + 2 * base + 8)).and
    (eventually_cfgSpaceBound_le hlog hfG D c₁ c₂))
  -- the description, padded beyond `N` and to a length where it is tiny
  suffices ∀ pad : List Bool, N + 2 ^ 2 ^ (eDesc (desc eS eBit tm)).length ≤ pad.length → False
    from this (List.replicate _ false) (List.length_replicate ..).ge
  intro pad hpad
  have hpow := Nat.one_le_two_pow (n := 2 ^ (eDesc (desc eS eBit tm)).length)
  have hlen : (frame (eDesc (desc eS eBit tm)) ++ pad).length =
      2 * (eDesc (desc eS eBit tm)).length + 1 + pad.length := by
    rw [List.length_append, length_frame]
  have htiny : tinyDesc (frame (eDesc (desc eS eBit tm)) ++ pad) = true :=
    tinyDesc_frame_append (by omega)
  generalize hx : frame (eDesc (desc eS eBit tm)) ++ pad = x at hlen htiny
  obtain ⟨h₁, h₂⟩ := hN x.length (by omega)
  have hl := hlog x.length
  have hrun := htm x
  simp only [encBits_apply] at hrun
  set s := c₁ * f x.length + c₂ with hs
  have hsf : s ≤ (c₁ + c₂) * (f x.length + 1) := by rw [hs]; nlinarith
  -- the decider halts within the clock
  have hclock : (x.length + 2) * storageBound Bool State k s ≤ 2 ^ G x.length := by
    have hx2 : x.length + 2 ≤ 2 ^ (Nat.log2 x.length + 2) := by
      have := Nat.lt_log2_self (n := x.length)
      rw [pow_add]
      omega
    have hb : base ≤ 2 ^ base := Nat.lt_two_pow_self.le
    have hes : 4 * (e * s) ≤ 4 * e * (c₁ + c₂) * f x.length + 4 * e * (c₁ + c₂) := by
      have := Nat.mul_le_mul_left (4 * e) hsf
      have e₁ : 4 * e * ((c₁ + c₂) * (f x.length + 1)) =
          4 * e * (c₁ + c₂) * f x.length + 4 * e * (c₁ + c₂) := by ring
      have e₂ : 4 * (e * s) = 4 * e * s := by ring
      omega
    have hy : 4 * e * (c₁ + c₂) * f x.length ≤
        (4 * e * (c₁ + c₂) + 2 * base + 8) * f x.length := Nat.mul_le_mul_right _ (by omega)
    calc (x.length + 2) * storageBound Bool State k s
        ≤ 2 ^ (Nat.log2 x.length + 2) * (base * 2 ^ (e * s)) :=
          Nat.mul_le_mul hx2 (storageBound_le_base_mul_pow s)
      _ ≤ 2 ^ (Nat.log2 x.length + 2) * (2 ^ base * 2 ^ (e * s)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hb)
      _ = 2 ^ (Nat.log2 x.length + 2 + base + e * s) := by rw [pow_add, pow_add, pow_add]; ring
      _ ≤ 2 ^ G x.length := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hhalt, hout⟩ := hrun.of_card.runFrom_of_le hclock
  -- the configurations of the simulation fit within the budget
  have hbudget : cfgSpace (desc eS eBit tm) (x.map eBit) (2 ^ G x.length) ≤ G x.length := by
    have hsp : simSpace (desc eS eBit tm) (x.map eBit) (2 ^ G x.length) ≤ s := by
      rw [simSpace_desc]
      exact space_le_of_runsInSpace hrun.2.2 _
    have hk : (desc eS eBit tm).tapes ≤ D := tapes_le _
    refine le_trans ?_ (h₂ _ hk)
    simp only [cfgSpace, cfgSpaceBound, List.length_map, ← hD]
    gcongr
  -- so the diagonal negates the answer of the decider
  have hd : spaceDiagonal G x = !g x := by
    subst hx
    exact spaceDiagonal_desc eS tm pad G htiny hbudget hhalt hout
  have hgx := hg x
  simp only [Set.mem_ofPred_eq, hd] at hgx
  revert hgx
  cases g x <;> decide

/-! ### The space hierarchy theorem -/

/-- **The space hierarchy theorem.** If `g` is space-constructible, `log₂ n ≤ g n`, and every
`c * f n + c` is eventually below `g n`, then `DSPACE f` is strictly contained in `DSPACE g`
[Sipser, Theorem 9.3 and Corollary 9.4][Sipser2013], [Arora and Barak, Theorem 4.8][AroraBarak09].
The universal machine simulates within a budget with a constant overhead for each simulated
machine, and the diagonal reads its input in place, so both the gap `f = o(g)` and the lower bound
`log n ≤ g n` are the textbook ones. The diagonal within space `4 * g` separates the classes. -/
theorem DSPACE_ssubset_DSPACE {f g : ℕ → ℕ} (hg : SpaceConstructible g)
    (hlog : ∀ n, Nat.log2 n ≤ g n) (hfg : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ g n) :
    DSPACE encBits f ⊂ DSPACE encBits g := by
  have hsub : DSPACE encBits f ⊆ DSPACE encBits g := DSPACE_mono_of_eventually_le <| by
    filter_upwards [hfg 1] with n h
    omega
  refine (Set.ssubset_iff_of_subset hsub).mpr ⟨_, DSPACE_mono_of_le_mul_add (C := 4)
    (fun n => Nat.le_add_right _ _) (setOf_spaceDiagonal_mem_DSPACE (hg.const_mul 4)
      fun n => (hlog n).trans (Nat.le_mul_of_pos_left _ (by norm_num))),
    setOf_spaceDiagonal_notMem_DSPACE (fun n => Nat.mul_le_mul_left 4 (hlog n)) fun c => ?_⟩
  filter_upwards [hfg c] with n h
  omega

/-- `⌊log₂ n⌋ ^ (k + 1)` eventually dominates every `c * ⌊log₂ n⌋ ^ k + c`. -/
theorem eventually_mul_log2_pow_add_le (k c : ℕ) :
    ∀ᶠ n in atTop, c * Nat.log2 n ^ k + c ≤ Nat.log2 n ^ (k + 1) := by
  filter_upwards [eventually_ge_atTop (2 ^ (2 * c + 1))] with n hn
  have hl : 2 * c + 1 ≤ Nat.log2 n :=
    (Nat.le_log2 (by have := Nat.one_le_two_pow (n := 2 * c + 1); omega)).mpr hn
  have h₁ : 1 ≤ Nat.log2 n ^ k := Nat.one_le_pow _ _ (by omega)
  have h₂ := Nat.mul_le_mul_right (Nat.log2 n ^ k) hl
  have h₃ := Nat.mul_le_mul_left c h₁
  rw [pow_succ]
  nlinarith

/-- **Polylogarithmic space has a strict hierarchy**:
`DSPACE (log₂ n ^ (k + 1)) ⊂ DSPACE (log₂ n ^ (k + 2))`. -/
theorem DSPACE_log2_pow_ssubset_DSPACE_log2_pow_succ (k : ℕ) :
    DSPACE encBits (Nat.log2 · ^ (k + 1)) ⊂ DSPACE encBits (Nat.log2 · ^ (k + 2)) :=
  DSPACE_ssubset_DSPACE (spaceConstructible_log2_pow (k + 1))
    (fun n => Nat.le_self_pow (by omega) _) fun c => eventually_mul_log2_pow_add_le (k + 1) c

/-- **Logarithmic space is strictly within space `log² n`**: `L = DSPACE (log₂ n)`, and the
diagonal within space `4 * log₂ n ^ 2` separates them [Sipser, Corollary 9.4][Sipser2013]. -/
theorem L_ssubset_DSPACE_log2_sq : L encBits ⊂ DSPACE encBits (Nat.log2 · ^ 2) := by
  rw [show L encBits = DSPACE encBits Nat.log2 from Set.ext fun _ => mem_L_iff_mem_DSPACE]
  refine DSPACE_ssubset_DSPACE (spaceConstructible_log2_pow 1)
    (fun n => Nat.le_self_pow (by omega) _) fun c => ?_
  simpa using eventually_mul_log2_pow_add_le 1 c

/-- **Logarithmic space is strictly within polynomial space**: `L ⊂ DSPACE (log₂ n ^ 2)`, which is
within `PSPACE`. This is the deterministic part of [Sipser, Corollary 9.6][Sipser2013], which
separates `NL` from `PSPACE`. -/
theorem L_ssubset_PSPACE : L encBits ⊂ PSPACE encBits :=
  L_ssubset_DSPACE_log2_sq.trans_subset <|
    (DSPACE_mono (s₂ := fun n => (n + 1) ^ 2) fun n =>
      Nat.pow_le_pow_left ((Nat.log2_le_self n).trans (Nat.le_succ n)) 2).trans
    (DSPACE_subset_PSPACE (by fun_prop))

/-- `(n + 1) ^ (k + 1)` eventually dominates every `c * n ^ k + c`. -/
theorem eventually_mul_pow_add_le_succ_pow (k c : ℕ) :
    ∀ᶠ n in atTop, c * n ^ k + c ≤ (n + 1) ^ (k + 1) := by
  filter_upwards [eventually_ge_atTop (2 * c)] with n hc
  have h₁ : n ^ k ≤ (n + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ n) k
  have h₂ : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have e : (n + 1) ^ (k + 1) = (n + 1) ^ k * (n + 1) := pow_succ ..
  nlinarith

/-- **Polynomial space has a strict hierarchy**: `DSPACE (n ^ k) ⊂ DSPACE (n ^ (k + 1))`
[Sipser, Corollary 9.5][Sipser2013]. The diagonal within space `4 * (n + 1) ^ (k + 1)` separates
them. -/
theorem DSPACE_pow_ssubset_DSPACE_pow_succ (k : ℕ) :
    DSPACE encBits (· ^ k) ⊂ DSPACE encBits (· ^ (k + 1)) :=
  (DSPACE_ssubset_DSPACE (g := fun n => (n + 1) ^ (k + 1))
    (spaceConstructible_succ_pow (k + 1))
    (fun n => (Nat.log2_le_self n).trans ((Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)))
    (eventually_mul_pow_add_le_succ_pow k)).trans_subset
      (DSPACE_mono_of_le_mul_add (Nat.add_one_pow_le_two_pow_mul_add (k + 1)))

end Cslib.Complexity
