/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import CslibFrontier.Computability.Circuit.Boolean.PPoly.Closure
public import CslibFrontier.Computability.Complexity.Classes.NP.SelfReduction
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
import CslibFrontier.Computability.Circuit.Boolean.Advice
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# The Karp–Lipton theorem

If `SAT` has circuits of polynomial size, the polynomial hierarchy collapses to its second level
[Karp and Lipton][KarpLipton1980], [Arora and Barak, Theorem 6.19][AroraBarak09]. The hypothesis is
that some language `L ∈ P/poly` contains exactly the encodings `encCNF φ` of the satisfiable
formulas; it follows from `NP ⊆ P/poly`, for problems with any encoding of their instances.

The proof shows `Π₂ ⊆ Σ₂` (`Cslib.Complexity.PiP_two_subset_SigmaP_two_of_SAT`). Let
`a ∈ A ↔ ∀ u, ∃ v, V (a, u ++ v)`. The pairs `(a, u)` for which some `v` is accepted form a
problem in `NP` by the witness API (`Cslib.Complexity.mem_NP_setOf_exists_append`), which the
Cook–Levin reduction `f` maps to `SAT`. A `Σ₂` verifier guesses circuits for `SAT` on all the
lengths the self-reduction (`Cslib.Complexity.SAT.search`) of a formula `f (a, u)` asks about, then
checks,
for every `u`, that the self-reduction answered by the guessed circuits finds a satisfying
assignment of `f (a, u)`. A satisfying assignment proves `(a, u)` in the problem whatever circuits
were guessed, and correct circuits always find one when there is one. Since `Π₂ ⊆ Σ₂` holds for
every encoding of instances, the hierarchy collapses to `Σ₂`
(`Cslib.Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`).

The guessed circuits are listed in an advice string (`Cslib.Circuits.Boolean.familyAdvice`,
`Cslib.Circuits.Boolean.PPoly.exists_evalAdvice`): the circuits `C 0, …, C N`, each in the
certificate format of `Cslib.Circuits.Boolean.readCertificate`, padded to a common length. The
circuit for an input `x` is read from the block at position `x.length` and evaluated on `x`
(`Cslib.Circuits.Boolean.evalAdvice`), in polynomial time.

The same advice-string mechanism eliminates alternating quantifiers nonuniformly under
`NP ⊆ P/poly`. `CslibFrontier.Computability.Circuit.Boolean.PPoly.Closure` proves this
(`Cslib.Complexity.PPolyOn.exists_of_computableInPolyTime_length`) together with closure of `P/poly`
preimages under polynomial-time many-one reductions
(`Cslib.Complexity.PolyTimeReducible.mem_PPolyOn`). This module re-exports that file.
Together with closure of `P/poly` under complement (`Cslib.Circuits.Boolean.PPolyOn.compl`) and
`P ⊆ P/poly` (`Cslib.Circuits.Boolean.P_subset_PPolyOn`), induction on `k` gives `Σₖ ⊆ P/poly`,
`Πₖ ⊆ P/poly`, and `PH ⊆ P/poly`
(`Cslib.Complexity.SigmaP_subset_PPolyOn_of_NP_subset_PPoly`,
`Cslib.Complexity.PiP_subset_PPolyOn_of_NP_subset_PPoly`,
`Cslib.Complexity.PH_subset_PPolyOn_of_NP_subset_PPoly`)
[Karp and Lipton, Section 3][KarpLipton1980], [Arora and Barak, Section 6.4][AroraBarak09].
With closure under reductions, `NP encBits ⊆ PPolyOn encBits` is equivalent to
`SAT ∈ PPolyOn encCNF` (`Cslib.Complexity.NP_subset_PPolyOn_iff_SAT`).

## Main results

* `Cslib.Complexity.PiP_two_subset_SigmaP_two_of_SAT`: if `SAT` has circuits of polynomial size,
  then `Π₂ ⊆ Σ₂`.
* `Cslib.Complexity.PiP_two_eq_SigmaP_two_of_SAT`: under the same hypothesis, `Π₂ = Σ₂`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_SAT`: **the Karp–Lipton theorem**, if `SAT` has circuits
  of polynomial size, then `PH = Σ₂`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly`: if `NP ⊆ P/poly`, then `PH = Σ₂`.
* `Cslib.Complexity.SigmaP_subset_PPolyOn_of_NP_subset_PPoly`,
  `Cslib.Complexity.PiP_subset_PPolyOn_of_NP_subset_PPoly`,
  `Cslib.Complexity.PH_subset_PPolyOn_of_NP_subset_PPoly`: if `NP ⊆ P/poly`, then `Σₖ ⊆ P/poly`,
  `Πₖ ⊆ P/poly`, and `PH ⊆ P/poly`.
* `Cslib.Complexity.NP_subset_PPolyOn_iff_SAT`: equivalence of `NP encBits ⊆ PPolyOn encBits` and
  `SAT ∈ PPolyOn encCNF`.

## References

* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.4][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Circuits Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

/-! ### The Karp–Lipton verifier -/

namespace KarpLipton

/-- The `Σ₂` verifier of Karp and Lipton for the reduction `f` to `SAT`. On `(a, w₁ ++ u)`, where
`w₁` has `P (enc a).length` bits, it runs the self-reduction of `f (a, u)` with the circuits read
from the advice string `w₁` (with at most `S (enc a).length` gates, in blocks of
`W (enc a).length` bits), and checks the assignment it finds. -/
private def verifier (enc : α ↪ List Bool) (f : α × List Bool → CNF ℕ) (S W P : Polynomial ℕ)
    (x : α × List Bool) : Bool :=
  SAT.verifier (f (x.1, x.2.drop (P.eval (enc x.1).length)),
    SAT.search (fun ψ => evalAdvice (S.eval (enc x.1).length) (W.eval (enc x.1).length)
      (x.2.take (P.eval (enc x.1).length)) (encCNF ψ))
      (f (x.1, x.2.drop (P.eval (enc x.1).length))))

private theorem verifier_append {f : α × List Bool → CNF ℕ} {S W P : Polynomial ℕ} (a : α)
    {w₁ : List Bool} (hw₁ : w₁.length = P.eval (enc a).length) (u : List Bool) :
    verifier enc f S W P (a, w₁ ++ u) = SAT.verifier (f (a, u),
      SAT.search (fun ψ => evalAdvice (S.eval (enc a).length) (W.eval (enc a).length) w₁
        (encCNF ψ)) (f (a, u))) := by
  rw [verifier, ← hw₁, List.drop_left, List.take_left]

private theorem computableInPolyTime_verifier {f : α × List Bool → CNF ℕ}
    (hf : ComputableInPolyTime f (encPair enc encBits) encCNF) (S W P : Polynomial ℕ) :
    ComputableInPolyTime (verifier enc f S W P) (encPair enc encBits) encBool := by
  have hn : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary := by fun_prop
  have hφ : ComputableInPolyTime (fun x : α × List Bool =>
      f (x.1, x.2.drop (P.eval (enc x.1).length))) (encPair enc encBits) encCNF := by fun_prop
  have hD : ComputableInPolyTime (fun p : (α × List Bool) × CNF ℕ =>
      evalAdvice (S.eval (enc p.1.1).length) (W.eval (enc p.1.1).length)
        (p.1.2.take (P.eval (enc p.1.1).length)) (encCNF p.2))
      (encPair (encPair enc encBits) encCNF) encBool := by fun_prop
  exact SAT.computableInPolyTime_verifier.comp (hφ.prod (SAT.computableInPolyTime_search hD hφ))

end KarpLipton

/-! ### `Π₂ ⊆ Σ₂` -/

/-- **Karp–Lipton, `Π₂ ⊆ Σ₂`.** If some language in `P/poly` contains exactly the encodings of the
satisfiable formulas, then `Π₂ ⊆ Σ₂`, for every encoding of instances. -/
theorem PiP_two_subset_SigmaP_two_of_SAT (hSAT : SAT ∈ PPolyOn encCNF)
    (enc : α ↪ List Bool) : PiP 2 enc ⊆ SigmaP 2 enc := by
  rintro A ⟨ps, V, hlen, hV, hA⟩
  obtain ⟨p, q, rfl⟩ := List.length_eq_two.1 hlen
  obtain ⟨f, hf, hfB⟩ := CookLevin.SAT_npHard _ _ (mem_NP_setOf_exists_append hV q)
  obtain ⟨L, hL, hSAT⟩ := hSAT
  obtain ⟨c', d', hf'⟩ := hf.polyBounded_length.exists_le
  -- a bound on the length of the formulas `f (a, u)`
  let F : Polynomial ℕ := Polynomial.C c' * (2 * Polynomial.X + 2 + p) ^ d'
  -- a bound on the length of the queries
  let N : Polynomial ℕ := F + (F + 1) * (8 * F + 11)
  obtain ⟨S, W, P, α_adv, hlen_α, -, h_eval⟩ := PPoly.exists_evalAdvice hL N
  have hF (a : α) (u : List Bool) (hu : u.length = p.eval (enc a).length) :
      (encCNF (f (a, u))).length ≤ F.eval (enc a).length := by
    refine (hf' (a, u)).trans (le_of_eq ?_)
    simp only [length_encPair, encBits_apply, hu, F, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    ring
  have hN (n : ℕ) : N.eval n = SAT.queryBound (F.eval n) := by
    simp [N, SAT.queryBound, Polynomial.eval_add, Polynomial.eval_mul]
  refine ⟨[P, p], KarpLipton.verifier enc f S W P, rfl,
    KarpLipton.computableInPolyTime_verifier hf S W P, fun a => ?_⟩
  set n := (enc a).length
  -- membership in `A` through `SAT`
  have hA' : a ∈ A ↔ ∀ u : List Bool, u.length = p.eval n → f (a, u) ∈ SAT := by
    rw [hA a]
    simp only [List.map_cons, List.map_nil, alternation_false_cons, alternation_true_cons,
      alternation_nil, List.append_nil]
    exact forall₂_congr fun u _ => hfB (a, u)
  rw [hA']
  simp only [List.map_cons, List.map_nil, alternation_true_cons, alternation_false_cons,
    alternation_nil, List.append_nil]
  constructor
  · intro h
    refine ⟨α_adv n, hlen_α n, fun u hu => ?_⟩
    rw [KarpLipton.verifier_append a (hlen_α n)]
    refine SAT.verifier_search (fun ψ hψ => ?_) (h u hu)
    have hlen : (encCNF ψ).length ≤ N.eval n := by
      rw [hN]
      exact hψ.trans (SAT.queryBound_mono (hF a u hu))
    exact (h_eval n (encCNF ψ) hlen).trans (hSAT ψ).symm
  · rintro ⟨w₁, hw₁, h⟩ u hu
    have := h u hu
    rw [KarpLipton.verifier_append a hw₁] at this
    exact ⟨_, this⟩

/-- **Karp–Lipton, `Π₂ = Σ₂`.** If some language in `P/poly` contains exactly the encodings of the
satisfiable formulas, then `Π₂ = Σ₂`, for every encoding of instances. -/
theorem PiP_two_eq_SigmaP_two_of_SAT (hSAT : SAT ∈ PPolyOn encCNF)
    (enc : α ↪ List Bool) : PiP 2 enc = SigmaP 2 enc :=
  PiP_eq_SigmaP_of_PiP_subset_SigmaP (PiP_two_subset_SigmaP_two_of_SAT hSAT enc)

/-! ### The collapse -/

/-- **The Karp–Lipton theorem.** If some language in `P/poly` contains exactly the encodings of the
satisfiable formulas, then the polynomial hierarchy collapses to its second level: `PH = Σ₂`, for
every encoding of instances. -/
theorem PH_eq_SigmaP_two_of_SAT (hSAT : SAT ∈ PPolyOn encCNF) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP (by norm_num) fun encB =>
    PiP_two_subset_SigmaP_two_of_SAT hSAT encB

/-- **The Karp–Lipton theorem, `NP ⊆ P/poly ⇒ PH = Σ₂`.** If every problem in `NP`, with any
encoding of its instances, is the preimage of a language in `P/poly`, then `PH = Σ₂`, for every
encoding of instances. -/
theorem PH_eq_SigmaP_two_of_NP_subset_PPoly
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ PPolyOn encB) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_SAT (h encCNF SAT.mem_NP)

/-! ### `PH ⊆ P/poly` under `NP ⊆ P/poly` -/

/-- **Karp–Lipton, `NP ⊆ P/poly ⇒ Σₖ ⊆ P/poly`.** If `NP ⊆ P/poly` over bitstrings, then every
level `Σₖ` of the polynomial hierarchy, with any encoding of its instances, is in `P/poly`
[Karp and Lipton, Section 3][KarpLipton1980], [Arora and Barak, Section 6.4][AroraBarak09]. -/
theorem SigmaP_subset_PPolyOn_of_NP_subset_PPoly
    (hNP : NP encBits ⊆ PPolyOn encBits) (k : ℕ) : SigmaP k enc ⊆ PPolyOn enc := by
  induction k generalizing α with
  | zero =>
    intro A hA
    rw [SigmaP_zero] at hA
    exact P_subset_PPolyOn hA
  | succ k ih =>
    intro A hA
    obtain ⟨p, B, hB, rfl⟩ := mem_SigmaP_succ_iff.mp hA
    have hB_PPoly : B ∈ PPolyOn (encPair enc encBits) := by
      simpa using PPolyOn.compl (ih (compl_mem_SigmaP_of_mem_PiP hB))
    have hN : ComputableInPolyTime (fun a : α => p.eval (enc a).length) enc encUnary := by fun_prop
    exact PPolyOn.exists_of_computableInPolyTime_length hNP hN hB_PPoly

/-- **Karp–Lipton, `NP ⊆ P/poly ⇒ Πₖ ⊆ P/poly`.** If `NP ⊆ P/poly` over bitstrings, then every
level `Πₖ` of the polynomial hierarchy, with any encoding of its instances, is in `P/poly`. -/
theorem PiP_subset_PPolyOn_of_NP_subset_PPoly
    (hNP : NP encBits ⊆ PPolyOn encBits) (k : ℕ) : PiP k enc ⊆ PPolyOn enc :=
  fun _ hA => by
    simpa using PPolyOn.compl (SigmaP_subset_PPolyOn_of_NP_subset_PPoly hNP k
      (compl_mem_SigmaP_of_mem_PiP hA))

/-- **Karp–Lipton, `NP ⊆ P/poly ⇒ PH ⊆ P/poly`.** If `NP ⊆ P/poly` over bitstrings, then the
entire polynomial hierarchy, with any encoding of its instances, is in `P/poly`
[Karp and Lipton, Section 3][KarpLipton1980], [Arora and Barak, Section 6.4][AroraBarak09]. -/
theorem PH_subset_PPolyOn_of_NP_subset_PPoly
    (hNP : NP encBits ⊆ PPolyOn encBits) : PH enc ⊆ PPolyOn enc :=
  Set.iUnion_subset (SigmaP_subset_PPolyOn_of_NP_subset_PPoly hNP)

/-- **Equivalence of `NP ⊆ P/poly` over bitstrings and `SAT ∈ P/poly`.** Having polynomial-size
circuits for every problem in `NP encBits` is equivalent to `SAT` having circuits of polynomial
size. -/
theorem NP_subset_PPolyOn_iff_SAT :
    NP encBits ⊆ PPolyOn encBits ↔ SAT ∈ PPolyOn encCNF :=
  ⟨fun hNP => SigmaP_subset_PPolyOn_of_NP_subset_PPoly hNP 1 (SigmaP_one ▸ SAT.mem_NP),
    fun hSAT _ hB => (CookLevin.SAT_npHard encBits _ hB).mem_PPolyOn hSAT⟩

end Cslib.Complexity
