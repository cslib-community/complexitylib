/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SuccinctVerifier.Encoding
public import CslibFrontier.Computability.Complexity.Classes.Time.Verifier
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.NondeterministicExponentialTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds

/-!
# From SAT algorithms to lower bounds for witness circuits

The verification step of Williams's algorithmic method is an actual native nondeterministic
simulation here. Given a family of succinct 3-CNF decoders `D` and a gate budget `s`, guess a
bounded circuit description, construct the violated-clause circuit, run a deterministic SAT
algorithm, and accept precisely when it answers **unsatisfiable**.

`smallWitnessLanguage_mem_NTIME` charges the input, computation of the certificate length,
construction of the query circuit, and the SAT computation on that actual circuit. The
certificate has exactly `Boolean.certLength r s` bits, at most `3 * (r + s + 1) ^ 2`.
`certificateQuery` retains the decoder's clause-index input width `q`, and its gate count is
at most `D.size + 3 * s + 17`, including on malformed certificates. No step enumerates the
exponentially long assignment or assumes that a guessed circuit computes the canonical witness.
`computableInPolyTime_certificateQuery` supplies the native compiler from polynomial-time
decoder construction. `smallWitnessLanguage_mem_NTIME_of_polyTime` then derives a polynomial
preprocessing bound and adds only the SAT time on queries with the stated width and gate bound.

`exists_hard_satisfyingAssignment_of_notMem_NTIME` turns this simulation into a lower bound:
if satisfiability of the decoder family is outside the supplied nondeterministic time class,
some satisfiable member has no satisfying assignment of circuit complexity at most `s`.
`exists_hard_satisfyingAssignment_of_expLazyDiagonal` discharges the hardness premise using
the library's explicit exponential-time diagonal language, while retaining the hypotheses
on the supplied succinct reduction and algorithms.

## Scope and source mapping

This is a modular version of the violated-clause verification in [Williams2010], proof of
Theorem 3.2, printed p. 10 in the author's May 4, 2010 version. The decoder is a De Morgan
circuit with `q` inputs and three blocks of `r` address bits followed by a sign bit. The
witness is a De Morgan circuit on `r` bits. Circuit size counts gates, including constants.
The uniform computations use binary multitape machines, `ComputableInO`, and the explicit
encodings in the theorem statements; time is preserved up to constant factors.

The certificate format uses unary wire fields and has quadratic length in `r + s`, rather
than the `O(s log s)` circuit description in the source. This still gives polynomial overhead
for polynomial witness budgets; sharper or superpolynomial budgets must account for this
encoding explicitly. The SAT query itself uses the library's binary wire-number encoding.

The simulation is proved, not assumed. The explicit-cost form takes native certificates for
computing the length and the specific circuit constructor, a deterministic SAT algorithm, and
the displayed sum of their resource bounds. The polynomial-preprocessing form derives the
first two computations from a uniformly constructible decoder family and unary parameters.
The lower-bound theorems concern satisfying-assignment functions of a supplied decoder
family. They do **not** assert `NEXP ⊄ P/poly`, `E ^ NP ⊄ SIZE(s)`, or an infinitely-often
bound. A full Williams theorem additionally needs the appropriate uniform succinct reduction,
an easy-witness theorem (for NEXP), and a sufficiently fine time hierarchy. In particular,
`O(n)` clause-index bits cannot replace `n + O(log n)` bits when using only polynomial
savings over exhaustive search. The final corollary uses the existing *coarse* exponential
hierarchy and makes no stronger hierarchy claim.

## Main definitions

* `Cslib.Complexity.AlgorithmsToLowerBounds.certificateQuery`: the total SAT instance built from
  an input and a guessed bounded witness circuit; malformed certificates give a satisfiable query.
* `Cslib.Complexity.AlgorithmsToLowerBounds.smallWitnessLanguage`: inputs whose decoded formula
  has a satisfying assignment represented by a circuit within the gate budget.

## Main results

* `Cslib.Complexity.AlgorithmsToLowerBounds.smallWitnessLanguage_mem_NTIME`: the charged native
  guess-and-verify simulation from a deterministic SAT algorithm.
* `Cslib.Complexity.AlgorithmsToLowerBounds.computableInPolyTime_certificateQuery`: the native
  polynomial-time SAT-query compiler for a uniformly constructible decoder family.
* `Cslib.Complexity.AlgorithmsToLowerBounds.smallWitnessLanguage_mem_NTIME_of_polyTime`:
  the simulation with derived polynomial preprocessing overhead plus the SAT time.
* `Cslib.Complexity.AlgorithmsToLowerBounds.exists_hard_satisfyingAssignment_of_notMem_NTIME`:
  a hard succinct satisfiability family forces a satisfying-assignment circuit lower bound.
* `Cslib.Complexity.AlgorithmsToLowerBounds.exists_hard_satisfyingAssignment_of_expLazyDiagonal`:
  the same transfer with hardness supplied by the native nondeterministic exponential hierarchy.

## References

* [R. Williams, *Improving Exhaustive Search Implies Superpolynomial Lower Bounds*][Williams2010],
  author's May 4, 2010 version, proof of Theorem 3.2, p. 10.
-/

public section

namespace Cslib.Complexity.AlgorithmsToLowerBounds

open Circuits Circuits.Boolean Circuits.Boolean.SuccinctVerifier Turing.MultiTapeTM

variable {α : Type} {q r : α → ℕ}

/-- The actual SAT query: check a bounded circuit certificate against the succinct formula.
The number of inputs is exactly the clause-index width, including for malformed certificates. -/
@[expose] def certificateQuery (D : ∀ x, Circuit signature (q x) (3 * (r x + 1)))
    (s : α → ℕ) (p : α × List Bool) : Σ n, Circuit signature n 1 :=
  ⟨q p.1, certificateCircuit (D p.1) (s p.1) p.2⟩

/-- The language of formulas having a satisfying circuit within the specified gate budget. -/
@[expose] def smallWitnessLanguage (D : ∀ x, Circuit signature (q x) (3 * (r x + 1)))
    (s : α → ℕ) : Set α :=
  {x | ∃ W : Circuit signature (r x) 1, W.size ≤ s x ∧
    (toCNF (D x)).eval (fun y => W.eval interpretation y 0) = true}

/-- The SAT query uses the decoder once and at most three copies of the guessed witness. -/
theorem size_certificateQuery_le (D : ∀ x, Circuit signature (q x) (3 * (r x + 1)))
    (s : α → ℕ) (p : α × List Bool) :
    (certificateQuery D s p).2.size ≤ (D p.1).size + 3 * s p.1 + 17 :=
  size_certificateCircuit_le (D p.1) (s p.1) p.2

/-- A polynomial-time decoder constructor gives a polynomial-time SAT-query constructor.
The widths and gate budget are computed in unary; the decoder uses the existing `encCode`
encoding with binary wire numbers. Guessing the certificate remains a separate operation. -/
theorem computableInPolyTime_certificateQuery
    {D : ∀ x, Circuit signature (q x) (3 * (r x + 1))} {s : α → ℕ}
    {enc : α ↪ List Bool}
    (hq : ComputableInPolyTime q enc encUnary)
    (hr : ComputableInPolyTime r enc encUnary)
    (hs : ComputableInPolyTime s enc encUnary)
    (hD : ComputableInPolyTime (fun x => (D x).code) enc encCode) :
    ComputableInPolyTime (certificateQuery D s) (encPair enc encBits) (encCircuit 1) :=
  computableInPolyTime_certificateCircuit
    (hq.comp (.fst enc encBits)) (hr.comp (.fst enc encBits))
    (hs.comp (.fst enc encBits)) (hD.comp (.fst enc encBits)) (.snd enc encBits)

/-- **SAT algorithms give a native simulation of small witness circuits.** The bound charges
input access, the unary certificate-length computation (hence writing and guessing its bits),
the circuit constructor, and SAT on the circuit actually constructed. All branches halt within
the bound, including those carrying invalid circuit descriptions. -/
theorem smallWitnessLanguage_mem_NTIME
    {D : ∀ x, Circuit signature (q x) (3 * (r x + 1))} {s : α → ℕ}
    {enc : α ↪ List Bool} {t : ℕ → ℕ}
    {Tℓ Sℓ : α → ℕ} {TB SB : α × List Bool → ℕ}
    {sat : (Σ n, Circuit signature n 1) → Bool}
    {TS SS : (Σ n, Circuit signature n 1) → ℕ} {C : ℕ}
    (hℓ : ComputableInO (fun x => certLength (r x) (s x)) enc encUnary Tℓ Sℓ)
    (hbuild : ComputableInO (certificateQuery D s) (encPair enc encBits) (encCircuit 1) TB SB)
    (hsat : ComputableInO sat (encCircuit 1) encBool TS SS)
    (hspec : ∀ c, sat c = true ↔ c ∈ CircuitSAT)
    (ht : ∀ x w, w.length = certLength (r x) (s x) →
      (enc x).length + Tℓ x + (TB (x, w) + TS (certificateQuery D s (x, w))) ≤
        C * t (enc x).length + C) :
    smallWitnessLanguage D s ∈ NTIME enc t := by
  have hV := (hsat.comp hbuild).not'
  have hsim := setOf_exists_mem_NTIME hℓ hV ht
  have heq : smallWitnessLanguage D s =
      {x | ∃ w : List Bool, w.length = certLength (r x) (s x) ∧
        !sat (certificateQuery D s (x, w)) = true} := by
    ext x
    rw [show x ∈ smallWitnessLanguage D s ↔
      ∃ w : List Bool, w.length = certLength (r x) (s x) ∧
        certificateQuery D s (x, w) ∉ CircuitSAT from
      (exists_not_mem_CircuitSAT_certificateCircuit_iff (D x) (s x)).symm]
    apply exists_congr
    intro w
    apply and_congr_right
    intro _
    rw [← hspec]
    cases sat (certificateQuery D s (x, w)) <;> simp
  rw [heq]
  exact hsim

/-- **Polynomial preprocessing plus the SAT time.** For a uniformly polynomial-time decoder
family, widths, and witness gate budget, the small-witness language is in nondeterministic time
`p(n) + t(n)` for some polynomially bounded `p`, whenever the SAT algorithm takes at most `t(n)`
on every query of the displayed input width and gate bound. The polynomial overhead is derived
from the actual compiler and certificate encoding, rather than assumed as a simulation. -/
theorem smallWitnessLanguage_mem_NTIME_of_polyTime
    {D : ∀ x, Circuit signature (q x) (3 * (r x + 1))} {s : α → ℕ}
    {enc : α ↪ List Bool} {t : ℕ → ℕ}
    {sat : (Σ n, Circuit signature n 1) → Bool}
    {TS SS : (Σ n, Circuit signature n 1) → ℕ}
    (hq : ComputableInPolyTime q enc encUnary)
    (hr : ComputableInPolyTime r enc encUnary)
    (hs : ComputableInPolyTime s enc encUnary)
    (hD : ComputableInPolyTime (fun x => (D x).code) enc encCode)
    (hsat : ComputableInO sat (encCircuit 1) encBool TS SS)
    (hspec : ∀ c, sat c = true ↔ c ∈ CircuitSAT)
    (ht : ∀ x (c : Σ n, Circuit signature n 1), c.1 = q x →
      c.2.size ≤ (D x).size + 3 * s x + 17 → TS c ≤ t (enc x).length) :
    ∃ p : ℕ → ℕ, PolynomiallyBounded p ∧
      smallWitnessLanguage D s ∈ NTIME enc (fun n => p n + t n) := by
  have hℓpoly : ComputableInPolyTime (fun x => certLength (r x) (s x)) enc encUnary := by
    unfold certLength
    fun_prop
  obtain ⟨dℓ, eℓ, hℓ⟩ := hℓpoly.exists_degree
  obtain ⟨cℓ, hlen⟩ := hℓ.2
  obtain ⟨dB, _, hbuild⟩ := (computableInPolyTime_certificateQuery hq hr hs hD).exists_degree
  let p : ℕ → ℕ := fun n => n + (n + 1) ^ dℓ +
    (2 * n + cℓ * (n + 1) ^ eℓ + 2) ^ dB
  refine ⟨p, by dsimp [p]; fun_prop, ?_⟩
  apply smallWitnessLanguage_mem_NTIME (C := 1) hℓ.inO hbuild.inO hsat hspec
  intro x w hw
  have hlength : certLength (r x) (s x) ≤ cℓ * ((enc x).length + 1) ^ eℓ := by
    simpa only [encUnary_apply, List.length_replicate] using hlen x
  have hpair : (encPair enc encBits (x, w)).length + 1 ≤
      2 * (enc x).length + cℓ * ((enc x).length + 1) ^ eℓ + 2 := by
    simp only [length_encPair, encBits_apply, hw]
    omega
  have hbuildTime := Nat.pow_le_pow_left hpair dB
  have hsatTime := ht x (certificateQuery D s (x, w)) rfl
    (size_certificateQuery_le D s (x, w))
  dsimp [p]
  omega

/-- **Algorithms-to-witness-circuit-lower-bounds transfer.** If the succinct satisfiability
language cannot be decided in the time of the preceding simulation, a satisfiable formula in
the family has no small satisfying assignment. The lower bound concerns every satisfying
assignment of that member, not merely a chosen canonical one. -/
theorem exists_hard_satisfyingAssignment_of_notMem_NTIME
    {D : ∀ x, Circuit signature (q x) (3 * (r x + 1))} {s : α → ℕ}
    {enc : α ↪ List Bool} {t : ℕ → ℕ}
    {Tℓ Sℓ : α → ℕ} {TB SB : α × List Bool → ℕ}
    {sat : (Σ n, Circuit signature n 1) → Bool}
    {TS SS : (Σ n, Circuit signature n 1) → ℕ} {C : ℕ}
    (hhard : {x | (toCNF (D x)).Satisfiable} ∉ NTIME enc t)
    (hℓ : ComputableInO (fun x => certLength (r x) (s x)) enc encUnary Tℓ Sℓ)
    (hbuild : ComputableInO (certificateQuery D s) (encPair enc encBits) (encCircuit 1) TB SB)
    (hsat : ComputableInO sat (encCircuit 1) encBool TS SS)
    (hspec : ∀ c, sat c = true ↔ c ∈ CircuitSAT)
    (ht : ∀ x w, w.length = certLength (r x) (s x) →
      (enc x).length + Tℓ x + (TB (x, w) + TS (certificateQuery D s (x, w))) ≤
        C * t (enc x).length + C) :
    ∃ x, (toCNF (D x)).Satisfiable ∧
      ∀ a : BitString (r x) → Bool, (toCNF (D x)).eval a = true →
        s x < complexity interpretation (single a) := by
  classical
  have hsim := smallWitnessLanguage_mem_NTIME hℓ hbuild hsat hspec ht
  by_contra! h
  apply hhard
  have heq : {x | (toCNF (D x)).Satisfiable} = smallWitnessLanguage D s := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, hsize⟩ := h x hx
      obtain ⟨W, hW, hWsize⟩ := complexity_le_iff.mp hsize
      refine ⟨W, hWsize, ?_⟩
      have heval : (fun y => W.eval interpretation y 0) = a :=
        funext (Circuit.computes_single_iff.mp hW)
      rw [heval]
      exact ha
    · rintro ⟨W, _, hW⟩
      exact ⟨_, hW⟩
  rw [heq]
  exact hsim

/-- A supplied uniform succinct reduction of the explicit exponential diagonal gives the
preceding witness-circuit lower bound with the hardness premise proved by the native hierarchy.
The sum of the actual costs must fit `O(2 ^ (k * n))`; the reduction and this cost inequality
remain explicit hypotheses. This does not use or assert a fine polynomial-savings hierarchy. -/
theorem exists_hard_satisfyingAssignment_of_expLazyDiagonal
    {q r : List Bool → ℕ}
    {D : ∀ x, Circuit signature (q x) (3 * (r x + 1))} {s : List Bool → ℕ}
    {k : ℕ} {Tℓ Sℓ : List Bool → ℕ} {TB SB : List Bool × List Bool → ℕ}
    {sat : (Σ n, Circuit signature n 1) → Bool}
    {TS SS : (Σ n, Circuit signature n 1) → ℕ} {C : ℕ}
    (hred : ∀ x, (toCNF (D x)).Satisfiable ↔ x ∈ expLazyDiagonal k)
    (hℓ : ComputableInO (fun x => certLength (r x) (s x)) encBits encUnary Tℓ Sℓ)
    (hbuild : ComputableInO (certificateQuery D s) (encPair encBits encBits) (encCircuit 1) TB SB)
    (hsat : ComputableInO sat (encCircuit 1) encBool TS SS)
    (hspec : ∀ c, sat c = true ↔ c ∈ CircuitSAT)
    (ht : ∀ x w, w.length = certLength (r x) (s x) →
      x.length + Tℓ x + (TB (x, w) + TS (certificateQuery D s (x, w))) ≤
        C * 2 ^ (k * x.length) + C) :
    ∃ x, (toCNF (D x)).Satisfiable ∧
      ∀ a : BitString (r x) → Bool, (toCNF (D x)).eval a = true →
        s x < complexity interpretation (single a) := by
  apply exists_hard_satisfyingAssignment_of_notMem_NTIME
    (t := fun n => 2 ^ (k * n)) ?_ hℓ hbuild hsat hspec
    (by simpa only [encBits_apply] using ht)
  have heq : {x | (toCNF (D x)).Satisfiable} = expLazyDiagonal k := Set.ext hred
  rw [heq]
  exact expLazyDiagonal_notMem_NTIME k

end Cslib.Complexity.AlgorithmsToLowerBounds
