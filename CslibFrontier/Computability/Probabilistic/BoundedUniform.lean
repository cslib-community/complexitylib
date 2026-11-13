/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.BoundedUniform
public import CslibFrontier.Computability.Probabilistic.UniformNat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Retry
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Strict fair-bit implementations of bounded sampling

Except in the early-stopping sampler, every attempt is sampled and stored before searching, and
all coordinates and output framing are charged. The unary certificates charge the numerical
bound, radius, dimension and attempt count. They do not imply polynomial dependence on the
logarithm of a cryptographic modulus. Failure remains in the certified program's output.

## Main results

* `Cslib.Probability.isPPTOn_sampleUniformInterval`: unary-bound interval sampling.
* `Cslib.Probability.isPPTOn_sampleUniformInterval_binary`: binary bounds with an efficient unary
  attempt budget, including exponentially large interval bounds.
* `Cslib.Probability.isPPTOn_sampleUniformIntervalRetry`: the early-stopping sampler, with binary
  bounds and a unary attempt budget.
* `Cslib.Probability.isPPTOn_sampleIntegerBox`: unary-radius runtime-dimensional boxes.
* `Cslib.Probability.length_enc_sampleIntegerBox`: a bound for the complete framed output.
-/

public section

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
      (fun a => sampleUniformInterval (bound a) (attempts a)) :=
  let e1 := encPair input (encList encUnary)
  ((isPPTOn_sampleBoundedIndex hbound).replicate hattempts).map_with
    (ComputableInPolyTime.findWithInput (.snd input (encList encUnary))
      (ComputableInPolyTime.unary_lt' (.snd e1 encUnary)
        (((ComputableInPolyTime.fst e1 encUnary).trans (.fst input (encList encUnary))).trans
          hbound)))

/-- Binary bounds need only a unary attempt count. The sampler draws `log₂ bound + 1` bits, a
width computed in polynomial time from the binary bound, not a unary copy of `bound`; exponential
cryptographic bounds are therefore permitted when the bound and attempt count are efficient. -/
@[program_certificate]
theorem isPPTOn_sampleUniformInterval_binary {α : Type} {input : α ↪ List Bool}
    {bound attempts : α → ℕ}
    (hbound : ComputableInPolyTime bound input encNat)
    (hattempts : ComputableInPolyTime attempts input encUnary) :
    IsPPTOn input (encOption encNat)
      (fun a => sampleUniformInterval (bound a) (attempts a)) := by
  have hwidth : ComputableInPolyTime (fun a => Nat.log 2 (bound a) + 1) input encUnary :=
    (hbound.trans ComputableInPolyTime.binary_log_two).unary_add' (.const 1)
  have hleft := (ComputableInPolyTime.fst input encNat).trans hbound
  have hright := ComputableInPolyTime.snd input encNat
  have hmin : ComputableInPolyTime (fun p : α × ℕ => min (bound p.1) p.2)
      (encPair input encNat) encNat :=
    ((ComputableInPolyTime.binary_le' hleft hright).ite hleft hright).of_enc_eq fun _ => by
      simp only [min_def, decide_eq_true_eq]
  have hs : IsPPTOn input encNat (fun a => sampleBoundedIndex (bound a)) :=
    ((isPPTOn_sampleBinaryNat.preprocess hwidth).map_with hmin).congr fun a => by
      rw [sampleBoundedIndex_eq_binary]
  let e1 := encPair input (encList encNat)
  exact (hs.replicate hattempts).map_with
    (ComputableInPolyTime.findWithInput (.snd input (encList encNat))
      (ComputableInPolyTime.binary_lt' (.snd e1 encNat)
        (((ComputableInPolyTime.fst e1 encNat).trans (.fst input (encList encNat))).trans hbound)))

open ComputableInPolyTime in
/-- Early stopping is strict PPT for binary bounds and a unary attempt budget. Each attempt draws
`bound.size` bits, a width computed in polynomial time from the binary bound. -/
@[program_certificate]
theorem isPPTOn_sampleUniformIntervalRetry {α : Type} {input : α ↪ List Bool}
    {bound attempts : α → ℕ}
    (hbound : ComputableInPolyTime bound input encNat)
    (hattempts : ComputableInPolyTime attempts input encUnary) :
    IsPPTOn input (encOption encNat)
      (fun a => sampleUniformIntervalRetry (bound a) (attempts a)) := by
  have hattempt : IsPPTOn input (encOption encNat)
      (fun a => sampleUniformIntervalAttempt (bound a)) := by
    have hdraw := ComputableInPolyTime.sampleBinaryNat (binary_size.comp hbound)
    have hcheck : ComputableInPolyTime
        (fun p : α × ℕ => if p.2 < bound p.1 then some p.2 else none)
        (encPair input encNat) (encOption encNat) := by
      have hcond := binary_lt' (snd input encNat) (hbound.comp (fst input encNat))
      have hyes : ComputableInPolyTime (fun p : α × ℕ => (some p.2 : Option ℕ))
          (encPair input encNat) (encOption encNat) := by fun_prop
      exact (ComputableInPolyTime.ite' hcond hyes (const none)).of_enc_eq fun p => by
        by_cases h : p.2 < bound p.1 <;> simp [h]
    exact hdraw.map_with hcheck
  have hgood : ComputableInPolyTime (fun o : Option ℕ => o.isSome) (encOption encNat) encBool := by
    fun_prop
  have hjoin : ComputableInPolyTime (Option.join (α := ℕ))
      (encOption (encOption encNat)) (encOption encNat) :=
    ((ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.optionGetD (encOption encNat))).comp
        (id'.prod (const none))).of_enc_eq fun oo => by cases oo <;> rfl
  exact (IsPPTOn.retry hattempt hgood hattempts).map hjoin

/-- A runtime-varying integer box is sampled in uniform strict PPT when the numerical radius,
dimension and per-coordinate attempt budget are efficiently supplied in unary. The full
optional, framed list output and all attempted coordinates are charged. -/
@[program_certificate]
theorem isPPTOn_sampleIntegerBox {α : Type} {input : α ↪ List Bool}
    {radius dimension attempts : α → ℕ}
    (hradius : ComputableInPolyTime radius input encUnary)
    (hdimension : ComputableInPolyTime dimension input encUnary)
    (hattempts : ComputableInPolyTime attempts input encUnary) :
    IsPPTOn input (encOption (encList encIntUnary))
      (fun a => sampleIntegerBox (radius a) (dimension a) (attempts a)) :=
  let e1 := encPair input (encOption encUnary)
  let e2 := encOption encIntUnary
  let hb := ((ComputableInPolyTime.const 2).unary_mul' hradius).unary_add' (.const 1)
  let hcoord := ComputableInPolyTime.optionElimWithInput
    (body := fun (p : α × Option ℕ) (i : ℕ) => some ((i : ℤ) - radius p.1))
    (.snd input (encOption encUnary)) (.const none)
    (((ComputableInPolyTime.snd e1 encUnary).prod
      (((ComputableInPolyTime.fst e1 encUnary).trans (.fst input (encOption encUnary))).trans
        hradius)).trans (ComputableInPolyTime.int_natCast_sub.trans (.optionSome encIntUnary)))
  let e3 := encList e2; let p2 := ComputableInPolyTime.snd e3 e2
  let hcollect : ComputableInPolyTime collectBox e3 (encOption (encList encIntUnary)) :=
    (ComputableInPolyTime.allWithInput .id' p2.optionIsSome).ite
      ((ComputableInPolyTime.mapWithInput .id' (p2.optionGetDWithInput (.const 0))).trans
        (.optionSome (encList encIntUnary))) (.const none)
  (((isPPTOn_sampleUniformInterval hb hattempts).map_with hcoord).replicate
    hdimension).map hcollect

/-- The complete framed optional output has a direct linear bound in dimension and unary
radius; failure encodes as the empty word. -/
theorem length_enc_sampleIntegerBox {radius dimension attempts : ℕ}
    {result : Option (List ℤ)}
    (h : result ∈ (ProbComp.eval (sampleIntegerBox radius dimension attempts)).support) :
    (encOption (encList encIntUnary) result).length ≤ dimension * (2 * radius + 3) + 1 := by
  cases result with
  | none => simp
  | some out =>
    obtain ⟨hlen, hbox⟩ := sampleIntegerBox_support h
    have hlist := length_encList_le (b := radius + 1) encIntUnary out fun z hz => by
      obtain ⟨_, _⟩ := hbox z hz; rw [length_encIntUnary]; split_ifs <;> omega
    rw [hlen, show 2 * (radius + 1) + 1 = 2 * radius + 3 by omega] at hlist
    simp only [encOption_some, List.length_cons]; omega

end Cslib.Probability
