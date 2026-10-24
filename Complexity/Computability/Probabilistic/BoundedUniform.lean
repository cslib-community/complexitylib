/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.BoundedUniform
public import Complexity.Computability.Probabilistic.UniformNat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Probabilistic.Repeat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Tactic.PPT

/-!
# Strict fair-bit implementations of bounded sampling

Every attempt is sampled and stored before searching, and all coordinates and output framing
are charged. The unary certificates charge the numerical bound, radius, dimension and attempt
count. They do not imply polynomial dependence on the logarithm of a cryptographic modulus.
Failure remains in the certified program's output.

## Main results

* `Cslib.Probability.isPPTOn_sampleUniformInterval`: unary-bound interval sampling.
* `Cslib.Probability.isPPTOn_sampleUniformInterval_binary`: binary bounds with an efficient unary
  sampling width and attempt budget, including exponentially large interval bounds.
* `Cslib.Probability.isPPTOn_sampleIntegerBox`: unary-radius runtime-dimensional boxes.
* `Cslib.Probability.length_enc_sampleIntegerBox`: a bound for the complete framed output.
-/

@[expose] public section

namespace Cslib.Probability

open ProbComp Turing.MultiTapeTM

/-- Unary bounds and attempt counts give a uniform strict PPT sampler, including its failure
result and every stored attempt. -/
@[program_certificate]
theorem isPPTOn_sampleUniformInterval {α : Type} {input : α ↪ List Bool}
    {bound attempts : α → ℕ}
    (hbound : ComputableInPolyTime bound input encUnary)
    (hattempts : ComputableInPolyTime attempts input encUnary) :
    IsPPTOn input (encOption encUnary)
      (fun a => sampleUniformInterval (bound a) (attempts a)) := by
  have hb := hbound.tidy
  have ha := hattempts.tidy
  have hs := (isPPTOn_sampleBoundedIndex hb).replicate ha
  have hfind : ComputableTidilyInPolyTime
      (fun p : α × List ℕ => p.2.find? (fun value => decide (value < bound p.1)))
      (encPair input (encList encUnary)) (encOption encUnary) := by fun_prop
  exact hs.map_with (.of_tidy hfind)

/-- Binary bounds need only a unary sampling width and attempt count. The width is the existing
sampler's computed `log₂ bound + 1`, not a unary copy of `bound`; exponential cryptographic
bounds are therefore permitted when these binary/unary parameter functions are efficient. -/
@[program_certificate]
theorem isPPTOn_sampleUniformInterval_binary {α : Type} {input : α ↪ List Bool}
    {bound width attempts : α → ℕ}
    (hbound : ComputableInPolyTime bound input encNat)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hattempts : ComputableInPolyTime attempts input encUnary)
    (hwidth_eq : ∀ a, width a = Nat.log 2 (bound a) + 1) :
    IsPPTOn input (encOption encNat)
      (fun a => sampleUniformInterval (bound a) (attempts a)) := by
  have hb := hbound.tidy
  have hw := hwidth.tidy
  have ha := hattempts.tidy
  have hleft := hb.comp (ComputableTidilyInPolyTime.fst input encNat)
  have hright := ComputableTidilyInPolyTime.snd input encNat
  have hmin : ComputableTidilyInPolyTime (fun p : α × ℕ => min (bound p.1) p.2)
      (encPair input encNat) encNat := by
    have hle := ComputableTidilyInPolyTime.binary_le.comp (hleft.prod hright)
    convert hle.cond hleft hright using 1
    funext p
    simp only [min_def, Function.comp_def, decide_eq_true_eq]
  have hs : IsPPTOn input encNat (fun a => sampleBoundedIndex (bound a)) := by
    apply ((isPPTOn_sampleBinaryNat.preprocess (ComputableInPolyTime.of_tidy hw)).map_with
      (f := fun a value => min (bound a) value) (.of_tidy hmin)).congr
    intro a
    rw [sampleBoundedIndex_eq_binary, ← hwidth_eq a]
  have hfind : ComputableTidilyInPolyTime
      (fun p : α × List ℕ => p.2.find? (fun value => decide (value < bound p.1)))
      (encPair input (encList encNat)) (encOption encNat) := by
    apply ComputableTidilyInPolyTime.findWithInput (by fun_prop)
    exact ComputableTidilyInPolyTime.binary_lt.comp
      ((ComputableTidilyInPolyTime.snd _ _).prod (by fun_prop))
  exact (hs.replicate ha).map_with (.of_tidy hfind)

/-- A runtime-varying integer box is sampled in uniform strict PPT when the numerical radius,
dimension and per-coordinate attempt budget are efficiently supplied in unary. The full
optional, framed list output and all attempted coordinates are charged. -/
@[program_certificate]
theorem isPPTOn_sampleIntegerBox {α : Type} {input : α ↪ List Bool}
    {radius dimension attempts : α → ℕ}
    (hradius : ComputableInPolyTime radius input encUnary)
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hattempts : ComputableInPolyTime attempts input encUnary) :
    IsPPTOn input (encOption (encList encInt))
      (fun a => sampleIntegerBox (radius a) (dimension a) (attempts a)) := by
  have hr := hradius.tidy
  have hd := hdimension.tidy
  have hb : ComputableInPolyTime (fun a => 2 * radius a + 1) input encUnary :=
    .of_tidy (by fun_prop)
  have hs := isPPTOn_sampleUniformInterval hb hattempts
  have hcoordinate : ComputableTidilyInPolyTime
      (fun p : α × Option ℕ => p.2.elim none (fun (i : ℕ) => some ((i : ℤ) - radius p.1)))
      (encPair input (encOption encUnary)) (encOption encInt) := by
    apply ComputableTidilyInPolyTime.optionElimWithInput (by fun_prop) (by fun_prop)
    have hrad : ComputableTidilyInPolyTime
        (fun p : (α × Option ℕ) × ℕ => radius p.1.1)
        (encPair (encPair input (encOption encUnary)) encUnary) encUnary := by
      fun_prop
    have hz := ComputableTidilyInPolyTime.int_natCast_sub.comp
      ((ComputableTidilyInPolyTime.snd _ _).prod hrad)
    exact (ComputableTidilyInPolyTime.optionSome encInt).comp hz
  have hcollect : ComputableTidilyInPolyTime collectBox
      (encList (encOption encInt)) (encOption (encList encInt)) := by
    unfold collectBox
    fun_prop
  exact (((hs.map_with (.of_tidy hcoordinate)).replicate hd).map hcollect)

/-- The complete framed optional output has a direct linear bound in dimension and unary
radius; failure encodes as the empty word. -/
theorem length_enc_sampleIntegerBox {radius dimension attempts : ℕ}
    {result : Option (List ℤ)}
    (h : result ∈ (ProbComp.eval (sampleIntegerBox radius dimension attempts)).support) :
    (encOption (encList encInt) result).length ≤ dimension * (2 * radius + 3) + 1 := by
  cases result with
  | none => simp
  | some out =>
    obtain ⟨hlen, hbox⟩ := sampleIntegerBox_support h
    have heach (z : ℤ) (hz : z ∈ out) : (encInt z).length ≤ radius + 1 := by
      obtain ⟨hlo, hhi⟩ := hbox z hz
      rw [length_encInt]
      split_ifs <;> omega
    have hlist := length_encList_le encInt out heach
    rw [hlen] at hlist
    simp only [encOption_some, List.length_cons]
    have harith : 2 * (radius + 1) + 1 = 2 * radius + 3 := by omega
    rw [harith] at hlist
    omega

end Cslib.Probability
