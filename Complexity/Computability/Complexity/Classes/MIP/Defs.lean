/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Classes.IP
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Probabilistic.Oracle.SingleOracle
import Complexity.Computability.Probabilistic.Oracle.Composition

/-!
# Multiprover interactive proofs (`MIP₂` and `MIP`)

In a multiprover interactive proof system [Ben-Or et al.][BenOrGoldwasserKilianWigderson1988],
[Babai, Fortnow and Lund][BabaiFortnowLund1991], [Arora and Barak, Section 8.5][AroraBarak09],
a probabilistic polynomial-time verifier exchanges messages with $k$ all-powerful provers that
**cannot communicate** with one another during the protocol: when the verifier sends a message $m$
to prover $i$, only prover $i$ sees $m$ and updates its internal state, while every other prover
$j \ne i$ keeps its state unchanged (`Cslib.Complexity.Prover.independent`,
`Cslib.Complexity.Prover.independent_state_eq_of_ne`).

A verifier with prover index type `ι` is a program `α → WordOracleComp ι Bool`, realized with a
strict polynomial clock against every stateful oracle (`Cslib.Probability.IsOraclePPTOn`). Each
external call `ProbOracleComp.query (i, message)` addresses one named prover `i : ι`. The classes
`Cslib.Complexity.MIP₂` (two non-communicating provers, `Fin 2`) and `Cslib.Complexity.MIP`
(finitely many non-communicating provers, `Fin p` for some `p : ℕ`) use completeness `2 / 3` and
soundness `1 / 3` against all independent prover families `P : ι → Prover Unit`.

The number of provers is constant for each language: `p` is chosen once, before the input.
The model uses classical provers with independent private randomness and permits coordinated
deterministic strategies through the choice of the family. It does not model entangled provers.

Embedding a single-prover verifier on one selected channel preserves `IsOraclePPTOn` and
acceptance probabilities against `Prover.independent P`, giving `IP ⊆ MIP₂ ⊆ MIP`.

## Main definitions

* `Cslib.Complexity.Prover.independent`: combine a family of non-communicating provers
  `ι → Prover Unit` into a `Prover ι` with product state `∀ i, (P i).State`.
* `Cslib.Complexity.IsMultiproverProof`: completeness and soundness against independent prover
  families `ι → Prover Unit`.
* `Cslib.Complexity.MIP₂`: two-prover interactive proofs with completeness `2 / 3` and soundness
  `1 / 3`.
* `Cslib.Complexity.MIP`: multiprover interactive proofs over `Fin p` provers.

## Main results

* `Cslib.Complexity.Prover.independent_state_eq_of_ne`: querying prover `i` leaves every other
  prover's state unchanged.
* `Cslib.Complexity.IP_subset_MIP₂`, `Cslib.Complexity.MIP₂_subset_MIP`:
  single-prover interactive proofs embed into `MIP₂` and `MIP`.
* `Cslib.Complexity.PolyTimeReducible.mem_MIP₂`, `Cslib.Complexity.PolyTimeReducible.mem_MIP`:
  closure under polynomial-time reductions.

## References

* [M. Ben-Or, S. Goldwasser, J. Kilian, A. Wigderson, *Multi-prover interactive proofs: How to
  remove intractability assumptions*][BenOrGoldwasserKilianWigderson1988]
* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 8.5][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

variable {ι α β : Type} [DecidableEq ι]

/-! ### Non-communicating prover families -/

namespace Prover

/-- Combine a family of individual provers `P : ι → Prover Unit` into a non-communicating
multiprover strategy `Prover ι`: each prover `i` keeps its own private state `(P i).State`, and a
query `(i, msg)` updates only prover `i`'s state while leaving every other prover's state
unchanged. -/
noncomputable abbrev independent (P : ι → Prover Unit) : Prover ι where
  State := ∀ i, (P i).State
  init i := (P i).init
  respond q := StateT.mk fun s =>
    (((P q.1).respond ((), q.2)).run (s q.1)).map fun x =>
      (x.1, Function.update s q.1 x.2)

@[simp]
theorem independent_init (P : ι → Prover Unit) (i : ι) :
    (independent P).init i = (P i).init := rfl

/-- **Non-communication (state isolation)**: when prover `q.1` responds to query `q`, the state of
every other prover `j ≠ q.1` is unchanged in every supported transition. -/
theorem independent_state_eq_of_ne (P : ι → Prover Unit) (q : ι × List Bool)
    (s s' : (independent P).State) (reply : List Bool) {j : ι} (hne : j ≠ q.1)
    (hmem : (reply, s') ∈ (((independent P).respond q).run s).support) :
    s' j = s j := by
  change (reply, s') ∈ ((((P q.1).respond ((), q.2)).run (s q.1)).map fun x =>
    (x.1, Function.update s q.1 x.2)).support at hmem
  obtain ⟨⟨r, si'⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
  have hs' : Function.update s q.1 si' = s' := (Prod.mk.inj heq).2
  exact (congrFun hs' j).symm.trans (Function.update_of_ne hne si' s)

/-- Projecting the joint state of `independent P` onto coordinate `i₀` commutes with running a
program that only queries prover `i₀`. -/
theorem run_singleOracle_independent (P : ι → Prover Unit) (i₀ : ι)
    (p : WordOracleComp Unit α) (s : ∀ i, (P i).State) :
    ((independent P).run (WordOracleComp.singleOracle i₀ p) s).map
      (Prod.map id (fun s' => s' i₀)) =
      (P i₀).run p (s i₀) := by
  rw [Prover.run, WordOracleComp.run_interpret_singleOracle, Prover.run]
  induction p using PFunctor.FreeM.induction generalizing s with
  | pure a =>
    simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.pure_map, Prod.map_apply, id_eq]
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.map_bind]
    cases q with
    | inl n =>
      change ((ProbComp.unifOracle n).map (·, s)).bind _ =
        ((ProbComp.unifOracle n).map (·, s i₀)).bind _
      rw [PMF.bind_map, PMF.bind_map]
      congr 1
      funext bit
      exact ih bit s
    | inr q =>
      obtain ⟨⟨⟩, msg⟩ := q
      change (((P i₀).respond ((), msg) (s i₀)).map
          (fun x => (x.1, Function.update s i₀ x.2))).bind _ =
        (((P i₀).respond ((), msg) (s i₀))).bind _
      rw [PMF.bind_map]
      congr 1
      funext x
      simpa only [Function.comp_apply, Function.update_self] using
        ih x.1 (Function.update s i₀ x.2)

/-- A single-channel verifier routed to prover `i₀` has the exact same acceptance probability
against `independent P` as the original verifier against `P i₀`. -/
theorem acceptProb_singleOracle_independent (P : ι → Prover Unit) (i₀ : ι)
    (p : WordOracleComp Unit Bool) :
    acceptProb (WordOracleComp.singleOracle i₀ p) (independent P) =
      acceptProb p (P i₀) := by
  have h := congrArg (PMF.map Prod.fst)
    (run_singleOracle_independent P i₀ p (independent P).init)
  have hcomp : Prod.fst ∘ Prod.map (id : Bool → Bool) (fun s' : (independent P).State => s' i₀) =
      Prod.fst := rfl
  simp only [PMF.map_comp, hcomp] at h
  exact congrFun (congrArg DFunLike.coe h) true

end Prover

/-! ### Multiprover interactive proofs and the classes `MIP₂` and `MIP` -/

/-- `verifier` is a multiprover interactive proof for `A` with completeness `c` and soundness `s`
over prover index type `ι` when on every member of `A` some independent prover family is accepted
with probability at least `c`, and on every non-member no independent prover family is accepted
with probability more than `s` [Babai, Fortnow and Lund][BabaiFortnowLund1991],
[Arora and Barak, Section 8.5][AroraBarak09]. -/
structure IsMultiproverProof (verifier : α → WordOracleComp ι Bool) (A : Set α)
    (completeness soundness : ℝ≥0∞) : Prop where
  /-- On every member of `A`, some family of non-communicating provers is accepted with
  probability at least `completeness`. -/
  complete : ∀ a ∈ A, ∃ P : ι → Prover Unit,
    completeness ≤ acceptProb (verifier a) (Prover.independent P)
  /-- On every non-member of `A`, every family of non-communicating provers is accepted with
  probability at most `soundness`. -/
  sound : ∀ a ∉ A, ∀ P : ι → Prover Unit,
    acceptProb (verifier a) (Prover.independent P) ≤ soundness

namespace IsMultiproverProof

variable {verifier : α → WordOracleComp ι Bool} {A : Set α} {B : Set β} {c c' s s' : ℝ≥0∞}

theorem mono (h : IsMultiproverProof verifier A c s) (hc : c' ≤ c) (hs : s ≤ s') :
    IsMultiproverProof verifier A c' s' where
  complete a ha :=
    let ⟨P, hP⟩ := h.complete a ha
    ⟨P, hc.trans hP⟩
  sound a ha P := (h.sound a ha P).trans hs

/-- Pull a multiprover interactive proof back along a reduction. -/
theorem comp {verifier : β → WordOracleComp ι Bool} (h : IsMultiproverProof verifier B c s)
    {f : α → β} (hf : ∀ a, a ∈ A ↔ f a ∈ B) :
    IsMultiproverProof (fun a => verifier (f a)) A c s where
  complete a ha := h.complete (f a) ((hf a).1 ha)
  sound a ha := h.sound (f a) fun hb => ha ((hf a).2 hb)

end IsMultiproverProof

/-- Embedding a single-prover interactive proof on channel `i₀ : ι` yields a multiprover
interactive proof with the same completeness and soundness. -/
theorem IsInteractiveProof.isMultiproverProof_singleOracle (i₀ : ι)
    {verifier : α → WordOracleComp Unit Bool} {A : Set α} {c s : ℝ≥0∞}
    (h : IsInteractiveProof verifier A c s) :
    IsMultiproverProof (fun a => WordOracleComp.singleOracle i₀ (verifier a)) A c s where
  complete a ha := by
    obtain ⟨P₀, hP₀⟩ := h.complete a ha
    refine ⟨fun _ => P₀, ?_⟩
    rwa [Prover.acceptProb_singleOracle_independent]
  sound a ha P := by
    rw [Prover.acceptProb_singleOracle_independent]
    exact h.sound a ha (P i₀)

/-- **Two-prover interactive proofs (`MIP₂`)**, with respect to the encoding `enc` of instances:
the problems with a two-prover interactive proof (`Fin 2`) whose verifier is strict oracle PPT
(`Cslib.Probability.IsOraclePPTOn`), with completeness `2 / 3` and soundness `1 / 3`
[Babai, Fortnow and Lund][BabaiFortnowLund1991]. -/
def MIP₂ (enc : α ↪ List Bool) : Set (Set α) :=
  {A : Set α | ∃ verifier : α → WordOracleComp (Fin 2) Bool,
    IsOraclePPTOn enc encBool verifier ∧
    IsMultiproverProof verifier A (2 / 3) (1 / 3)}

/-- **Multiprover interactive proofs (`MIP`)**, with respect to the encoding `enc` of instances:
the problems with a constant number `p` of provers (`Fin p`, chosen once per language) whose
verifier is strict oracle PPT, with completeness `2 / 3` and soundness `1 / 3`
[Ben-Or, Goldwasser, Kilian and Wigderson][BenOrGoldwasserKilianWigderson1988],
[Babai, Fortnow and Lund][BabaiFortnowLund1991],
[Arora and Barak, Section 8.5][AroraBarak09]. -/
def MIP (enc : α ↪ List Bool) : Set (Set α) :=
  {A : Set α | ∃ (p : ℕ) (verifier : α → WordOracleComp (Fin p) Bool),
    IsOraclePPTOn enc encBool verifier ∧
    IsMultiproverProof verifier A (2 / 3) (1 / 3)}

/-! ### Closure under reductions and basic inclusions -/

/-- **`MIP₂` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_MIP₂ {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hred : PolyTimeReducible encA encB A B) (hB : B ∈ MIP₂ encB) :
    A ∈ MIP₂ encA := by
  obtain ⟨f, hf, hAB⟩ := hred
  obtain ⟨V, hV, hproof⟩ := hB
  exact ⟨fun a => V (f a), hV.preprocess' hf, hproof.comp hAB⟩

/-- **`MIP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_MIP {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hred : PolyTimeReducible encA encB A B) (hB : B ∈ MIP encB) :
    A ∈ MIP encA := by
  obtain ⟨f, hf, hAB⟩ := hred
  obtain ⟨p, V, hV, hproof⟩ := hB
  exact ⟨p, fun a => V (f a), hV.preprocess' hf, hproof.comp hAB⟩

/-- **`IP ⊆ MIP₂`**: a single-prover interactive proof uses the first of two provers (`0 : Fin 2`)
and ignores the second. -/
theorem IP_subset_MIP₂ (enc : α ↪ List Bool) : IP enc ⊆ MIP₂ enc := by
  rintro A ⟨V, hV, hA⟩
  exact ⟨fun a => WordOracleComp.singleOracle (0 : Fin 2) (V a),
    hV.singleOracle 0, hA.isMultiproverProof_singleOracle 0⟩

/-- **`MIP₂ ⊆ MIP`**: a two-prover interactive proof is a `p`-prover interactive proof with
`p = 2`. -/
theorem MIP₂_subset_MIP (enc : α ↪ List Bool) : MIP₂ enc ⊆ MIP enc := by
  rintro A ⟨V, hV, hA⟩
  exact ⟨2, V, hV, hA⟩

end Cslib.Complexity
