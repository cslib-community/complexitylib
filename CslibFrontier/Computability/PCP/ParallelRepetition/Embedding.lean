/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.ParallelRepetition.CoordinateModel
public import CslibFrontier.Probability.CorrelatedSampling.Embeddability
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Filter
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.ProductConditioning

/-!
# The first stage of Holenstein's embedding lemma

The proof of Holenstein's Lemma 6.4 [Holenstein, Lemma 6.4][Holenstein2009] embeds the questions
of a game `G` in the `n`-fold repetition conditioned on the event `W_C` that strategies `ha` and
`hb` win every coordinate in `C`, at a free coordinate `j ∉ C`. It has two stages. The first,
built here, embeds the questions in `((X̃_j, Ỹ_j), (S̃, S̃))`: Alice and Bob, from the questions
`(x, y)` of `G`, produce one common value of the variable `S = (T^{(\j)}, V)` of
[Holenstein, (6.11)][Holenstein2009], so that `((x, y), S)` is close to the law of
`((x_j, y_j), S)` under `W_C`. The second stage, which adds the remaining questions through
Lemma 5.4, is not part of this file.

Every law is an image of `condLaw` of
`CslibFrontier/Computability/PCP/ParallelRepetition/CoordinateModel.lean`, and the chain starts from
its bound (6.5), `sum_dist_condLaw_le`. Write `E := √(#Cᶜ (#C ln (|A| |B|) + ln (1 / Pr[W_C])) / 2)`
for that bound.

* **(6.7)–(6.12)** (`sum_dist_map_condLaw_shared_le`). Conditioning both laws of (6.5) on the bit
  `D_j = b`, an event of probability `1 / 2` under both, at most doubles their distance
  (Claim 6.1, `dist_filter_le_two_mul`). Then forget the bit: under `D_j = b` the revealed half at
  `j` is `reveal b (x_j, y_j)`, and `S` and the pair at `j` ignore `D_j`, so the condition drops
  (`map_filter_condLaw_bit`). The result is
  `∑_{j ∉ C} ‖P_{X̃_j Ỹ_j S̃} - P_{R̃_j S̃} P_{X_j Y_j | R_j}‖ ≤ 2 E`, where `R_j` is Bob's question
  `y_j` for `b = false`, as in (6.12), and Alice's `x_j` for `b = true`.
* **(6.14)** (`sum_dist_map_condLaw_pair_le`). Raz's lemma (Lemma 4.1,
  `sq_sum_dist_map_filter_pi_le`) applied to the `n` independent question pairs, summed over the
  free coordinates by Cauchy–Schwarz: `∑_{j ∉ C} ‖P_{X̃_j Ỹ_j} - P_{XY}‖ ≤
  √(#Cᶜ ln (1 / Pr[W_C]) / 2) ≤ E`. Holenstein states it for `Ỹ_j`; the pair bounds both halves.
* **(6.15) and (6.16)** (`sum_dist_condLaw_withKernel_condY_le`,
  `sum_dist_condLaw_withKernel_condX_le`). The triangle inequality
  (`dist_withKernel_condY_le`, `dist_withKernel_condX_le`) with `P_Y P_{X | Y} = P_{XY}`
  (`bind_pairGiven_inr`, `bind_pairGiven_inl`) gives
  `∑_{j ∉ C} ‖P_{X̃_j Ỹ_j S̃} - P_{XY} P_{S̃ | Ỹ_j}‖ ≤ 3 E`, and the same for `X̃_j`.
* **Stage 1** (`exists_isEmbeddable_condLaw_shared`). Corollary 5.3
  (`isEmbeddable_diag_of_dist_le`), with `J` the law of `((X̃_j, Ỹ_j), S̃)` and `P₀ = G.questions`,
  embeds the questions with error `ε_j = 7 ε₁ + 2 ε₂`, where `ε₁` and `ε₂` are the distances of
  (6.16) and (6.15). Summing, `∑_{j ∉ C} ε_j ≤ 7 · 3 E + 2 · 3 E = 27 E`, that is
  `27 / √2 · √(#Cᶜ (#C ln (|A| |B|) + ln (1 / Pr[W_C])))`.

Holenstein's constant is `15 = 3 · 3 + 2 · 3`, from his Corollary 5.3 constant `3 ε₁ + 2 ε₂`; the
library's Corollary 5.3 has `7 ε₁ + 2 ε₂`, hence `27`. His `ε_Tot` of (6.6) is in bits and has no
factor `1 / 2`; here the logarithms are natural, with the `1 / 2` of Pinsker's inequality, hence
`27 / √2 ≈ 19.09`. The sharpened recursion of Lemma 7.1
(`CslibFrontier/Computability/PCP/ParallelRepetition/Recursion.lean`) accepts any constant up to
`21`.

## Main results

* `Cslib.PCP.ParallelRepetition.sum_dist_map_condLaw_shared_le`: Holenstein's (6.7)–(6.12).
* `Cslib.PCP.ParallelRepetition.sum_dist_map_condLaw_pair_le`: Holenstein's (6.14).
* `Cslib.PCP.ParallelRepetition.sum_dist_condLaw_withKernel_condY_le`,
  `Cslib.PCP.ParallelRepetition.sum_dist_condLaw_withKernel_condX_le`: Holenstein's (6.15) and
  (6.16).
* `Cslib.PCP.ParallelRepetition.exists_isEmbeddable_condLaw_shared`: the first stage of the
  embedding of Lemma 6.4.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

public section

namespace Cslib.PCP.ParallelRepetition

open Finset
open Cslib.Probability.PMF (pi conditionalSnd dist_map_le)
open Cslib.Probability.CorrelatedSampling
open scoped Cslib.Probability.PMF

variable {X Y A B : Type*} [Fintype X] [Fintype Y] {G : TwoProverGame X Y A B} {n : ℕ}
  {C : Finset (Fin n)} {ha : (Fin n → X) → Fin n → A} {hb : (Fin n → Y) → Fin n → B}

/-- **Holenstein's (6.14)** [Holenstein, proof of Lemma 6.4, (6.14)][Holenstein2009]: under `W_C`,
the question pairs at the free coordinates are close to `G.questions` on average:
`∑_{j ∉ C} ‖P_{X̃_j Ỹ_j} - P_{XY}‖ ≤ √(#Cᶜ ln (1 / Pr[W_C]) / 2)`. This is Raz's lemma for the `n`
independent pairs, summed over the free coordinates by Cauchy–Schwarz. Holenstein states it for
Bob's question `Ỹ_j`; the bound for the pair implies it. -/
theorem sum_dist_map_condLaw_pair_le
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    ∑ j : {i // i ∉ C}, dist ((condLaw G C ha hb hC).map fun ω => ω.2 j) G.questions ≤
      Real.sqrt (#Cᶜ * Real.log (1 / G.winProbOn ha hb C) / 2) := by
  classical
  have h := Cslib.Probability.PMF.sq_sum_dist_map_filter_pi_le (fun _ : Fin n => G.questions)
    (winsOnPairs G C ha hb) (exists_mem_winsOnPairs_support hC) Cᶜ
  rw [toOuterMeasure_pi_winsOnPairs] at h
  have hmap (i : Fin n) : (condLaw G C ha hb hC).map (fun ω => ω.2 i) =
      ((pi fun _ : Fin n => G.questions).filter (winsOnPairs G C ha hb)
        (exists_mem_winsOnPairs_support hC)).map fun u => u i := by
    rw [← map_snd_condLaw hC, PMF.map_comp]
    rfl
  -- The free coordinates as a subtype and as `Cᶜ`.
  have hsum := Finset.sum_subtype Cᶜ (p := (· ∉ C)) (F := inferInstance)
    (fun i => Finset.mem_compl) fun i =>
      dist ((condLaw G C ha hb hC).map fun ω => ω.2 i) G.questions
  rw [← hsum]
  simp only [hmap]
  exact Real.le_sqrt_of_sq_le h

variable [Fintype A] [Fintype B]

/-- Holenstein's (6.7)–(6.12) at one free coordinate `j`, with the bit `D_j = b`: conditioning
both laws of (6.5) on `D_j = b` and forgetting `D_j` at most doubles their distance. -/
private theorem dist_map_condLaw_shared_le
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) (j : {i // i ∉ C})
    (b : Bool) :
    dist ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω))
        (((condLaw G C ha hb hC).map fun ω => (reveal b (ω.2 j), shared ha hb j ω)).bind
          fun (r, s) => (pairGiven G r).map (·, s)) ≤
      2 * dist ((condLaw G C ha hb hC).map fun ω => ((revealed C ω, answers C ha hb ω.2), ω.2 j))
        (((condLaw G C ha hb hC).map fun ω => (revealed C ω, answers C ha hb ω.2)).bind
          fun s => (pairGiven G (s.1.halves j)).map (s, ·)) := by
  classical
  set P := condLaw G C ha hb hC
  set TV : Sample X Y C → Revealed X Y C × (C → A × B) :=
    fun ω => (revealed C ω, answers C ha hb ω.2)
  set κ : Revealed X Y C × (C → A × B) → PMF ((Revealed X Y C × (C → A × B)) × (X × Y)) :=
    fun s => (pairGiven G (s.1.halves j)).map (s, ·)
  -- The event `D_j = b`, read off `T` and off the sample.
  set Eμ : Set (Revealed X Y C × (C → A × B)) := {s | s.1.bit j = b}
  set ES : Set (Sample X Y C) := {ω | ω.1 j = b}
  have hTV : TV ⁻¹' Eμ = ES := by
    ext ω
    simp only [TV, Eμ, ES, Set.mem_preimage, Set.mem_ofPred_eq, bit_revealed]
  have hF : (fun ω => (TV ω, ω.2 j)) ⁻¹' (Prod.fst ⁻¹' Eμ) = ES := hTV
  -- (6.7): `D_j = b` has probability `1 / 2` on both sides, so Claim 6.1 applies.
  have hhalf : (P.toOuterMeasure ES).toReal = 1 / 2 := toOuterMeasure_condLaw_bit hC j b
  have hES : ∃ ω ∈ ES, ω ∈ P.support :=
    (Cslib.Probability.PMF.toOuterMeasure_toReal_pos_iff _ _).mp (by rw [hhalf]; norm_num)
  have hp : ((P.map fun ω => (TV ω, ω.2 j)).toOuterMeasure (Prod.fst ⁻¹' Eμ)).toReal = 1 / 2 := by
    rw [PMF.toOuterMeasure_map_apply, hF, hhalf]
  have hq : (((P.map TV).bind κ).toOuterMeasure (Prod.fst ⁻¹' Eμ)).toReal = 1 / 2 := by
    rw [← PMF.toOuterMeasure_map_apply, Cslib.Probability.PMF.map_fst_bind_pair,
      PMF.toOuterMeasure_map_apply, hTV, hhalf]
  have hpE := (Cslib.Probability.PMF.toOuterMeasure_toReal_pos_iff _ _).mp
    (by rw [hp]; norm_num)
  have hqE := (Cslib.Probability.PMF.toOuterMeasure_toReal_pos_iff _ _).mp
    (by rw [hq]; norm_num)
  have hμE : ∃ s ∈ Eμ, s ∈ (P.map TV).support := by
    obtain ⟨ω, hω, hsupp⟩ := hES
    exact ⟨TV ω, (Set.ext_iff.mp hTV ω).mpr hω,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨ω, hsupp, rfl⟩⟩
  have h61 := dist_filter_le_two_mul _ _ _ hp hq hpE hqE
  -- Both conditioned laws are images of `P` conditioned on `D_j = b`.
  have hleft : (P.map fun ω => (TV ω, ω.2 j)).filter (Prod.fst ⁻¹' Eμ) hpE =
      (P.filter ES hES).map fun ω => (TV ω, ω.2 j) := by
    rw [Cslib.Probability.PMF.filter_map _ _ _ _ (hF ▸ hES)]
    simp only [hF]
  have hright : ((P.map TV).bind κ).filter (Prod.fst ⁻¹' Eμ) hqE =
      ((P.filter ES hES).map TV).bind κ := by
    rw [Cslib.Probability.PMF.filter_bind_pair _ _ _ _ hμE,
      Cslib.Probability.PMF.filter_map _ _ _ _ (hTV ▸ hES)]
    simp only [hTV]
    rfl
  -- (6.9): regroup `((T, V), U_j)` as `(U_j, S)`, forgetting the revealed half at `j`.
  set Φ : (Revealed X Y C × (C → A × B)) × (X × Y) → (X × Y) × Shared X Y A B C j :=
    fun ((t, v), u) => (u, Shared.ofRevealed j t v)
  have h1 := (dist_map_le _ _ Φ).trans h61
  rw [hleft, hright] at h1
  -- (6.10): `S` and the pair at `j` ignore `D_j`, so the condition drops.
  have hL : ((P.filter ES hES).map fun ω => (TV ω, ω.2 j)).map Φ =
      P.map fun ω => (ω.2 j, shared ha hb j ω) := by
    have hΦF : (Φ ∘ fun ω => (TV ω, ω.2 j)) = fun ω => (ω.2 j, shared ha hb j ω) := rfl
    rw [PMF.map_comp, hΦF]
    exact map_filter_condLaw_bit hC j b _ (fun d c q => by simp only [shared_update]) hES
  -- Under `D_j = b`, the revealed half at `j` is `reveal b` of the pair.
  have hsupp : (P.filter ES hES).map (fun ω => ((revealed C ω).halves j, shared ha hb j ω)) =
      (P.filter ES hES).map (fun ω => (reveal b (ω.2 j), shared ha hb j ω)) := by
    refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun ω hω => ?_
    rw [PMF.support_filter] at hω
    have hb : ω.1 j = b := hω.1
    simp only [revealed, hb]
  have hR : (((P.filter ES hES).map TV).bind κ).map Φ =
      (P.map fun ω => (reveal b (ω.2 j), shared ha hb j ω)).bind
        fun (r, s) => (pairGiven G r).map (·, s) := by
    calc _ = ((P.filter ES hES).map (fun ω => ((revealed C ω).halves j, shared ha hb j ω))).bind
          fun (r, s) => (pairGiven G r).map (·, s) := by
          simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, κ, TV, Φ]
          rfl
      _ = _ := by
          rw [hsupp, map_filter_condLaw_bit hC j b _
            (fun d c q => by simp only [shared_update]) hES]
  rw [hL, hR] at h1
  exact h1

/-- **Holenstein's (6.7)–(6.12)** [Holenstein, proof of Lemma 6.4, (6.7)–(6.12)][Holenstein2009]:
under `W_C`, drawing the pair at `j` given only `S` and the half `R_j = reveal b (x_j, y_j)`
revealed by the bit `b` changes the law of `((x_j, y_j), S)` little on average:
`∑_{j ∉ C} ‖P_{X̃_j Ỹ_j S̃} - P_{R̃_j S̃} P_{X_j Y_j | R_j}‖ ≤ 2 E`, with `E` the bound of
(6.5). For `b = false`, `R_j` is Bob's question `y_j` and this is (6.12); `b = true` gives the
symmetric statement for Alice's question. -/
theorem sum_dist_map_condLaw_shared_le
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) (b : Bool) :
    ∑ j : {i // i ∉ C}, dist ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω))
        (((condLaw G C ha hb hC).map fun ω => (reveal b (ω.2 j), shared ha hb j ω)).bind
          fun (r, s) => (pairGiven G r).map (·, s)) ≤
      2 * Real.sqrt (#Cᶜ * (#C * Real.log (Fintype.card A * Fintype.card B) +
        Real.log (1 / G.winProbOn ha hb C)) / 2) := by
  refine (Finset.sum_le_sum fun j _ => dist_map_condLaw_shared_le hC j b).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_dist_condLaw_le hC) zero_le_two

/-- The bound of (6.14) is at most the bound `E` of (6.5). -/
private theorem sqrt_log_le_sqrt (p : ℝ) :
    Real.sqrt (#Cᶜ * Real.log (1 / p) / 2) ≤
      Real.sqrt (#Cᶜ * (#C * Real.log (Fintype.card A * Fintype.card B) +
        Real.log (1 / p)) / 2) := by
  refine Real.sqrt_le_sqrt ?_
  have hL := Real.log_natCast_nonneg (Fintype.card A * Fintype.card B)
  push_cast at hL
  have : (0 : ℝ) ≤ #Cᶜ * (#C * Real.log (Fintype.card A * Fintype.card B)) := by positivity
  linarith

/-- (6.13)–(6.15) at one free coordinate `j`: the triangle inequality through the law that keeps
`(y_j, S)` and redraws `x_j` given `y_j`. -/
private theorem dist_condLaw_withKernel_condY_le
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) (j : {i // i ∉ C}) :
    dist ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω))
        (withKernel G.questions fun xy =>
          condY ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω)) xy.2) ≤
      dist ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω))
          (((condLaw G C ha hb hC).map fun ω => (reveal false (ω.2 j), shared ha hb j ω)).bind
            fun (r, s) => (pairGiven G r).map (·, s)) +
        dist ((condLaw G C ha hb hC).map fun ω => ω.2 j) G.questions := by
  set J := (condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω)
  have h := dist_withKernel_condY_le J G.questions
    (fun y => conditionalSnd (G.questions.map Prod.swap) y) (bind_pairGiven_inr G)
  have hR : ((J.map (Prod.map Prod.snd id)).bind fun (y, s) =>
        (conditionalSnd (G.questions.map Prod.swap) y).map fun x => ((x, y), s)) =
      ((condLaw G C ha hb hC).map fun ω => (reveal false (ω.2 j), shared ha hb j ω)).bind
        fun (r, s) => (pairGiven G r).map (·, s) := by
    simp only [J, PMF.map_comp, PMF.bind_map, Function.comp_def, reveal_false, pairGiven]
    rfl
  have hJ : J.map Prod.fst = (condLaw G C ha hb hC).map fun ω => ω.2 j := by
    rw [PMF.map_comp]
    rfl
  rw [hR, hJ] at h
  exact h.trans (add_le_add_right (dist_map_le _ _ _) _)

/-- (6.16) at one free coordinate `j`: the triangle inequality through the law that keeps
`(x_j, S)` and redraws `y_j` given `x_j`. -/
private theorem dist_condLaw_withKernel_condX_le
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) (j : {i // i ∉ C}) :
    dist ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω))
        (withKernel G.questions fun xy =>
          condX ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω)) xy.1) ≤
      dist ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω))
          (((condLaw G C ha hb hC).map fun ω => (reveal true (ω.2 j), shared ha hb j ω)).bind
            fun (r, s) => (pairGiven G r).map (·, s)) +
        dist ((condLaw G C ha hb hC).map fun ω => ω.2 j) G.questions := by
  set J := (condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω)
  have h := dist_withKernel_condX_le J G.questions
    (fun x => conditionalSnd G.questions x) (bind_pairGiven_inl G)
  have hR : ((J.map (Prod.map Prod.fst id)).bind fun (x, s) =>
        (conditionalSnd G.questions x).map fun y => ((x, y), s)) =
      ((condLaw G C ha hb hC).map fun ω => (reveal true (ω.2 j), shared ha hb j ω)).bind
        fun (r, s) => (pairGiven G r).map (·, s) := by
    simp only [J, PMF.map_comp, PMF.bind_map, Function.comp_def, reveal_true, pairGiven]
    rfl
  have hJ : J.map Prod.fst = (condLaw G C ha hb hC).map fun ω => ω.2 j := by
    rw [PMF.map_comp]
    rfl
  rw [hR, hJ] at h
  exact h.trans (add_le_add_right (dist_map_le _ _ _) _)

/-- **Holenstein's (6.15)** [Holenstein, proof of Lemma 6.4, (6.13)–(6.15)][Holenstein2009]:
under `W_C`, the law of `((x_j, y_j), S)` is close on average to drawing the pair from
`G.questions` and then `S` given Bob's question:
`∑_{j ∉ C} ‖P_{X̃_j Ỹ_j S̃} - P_{XY} P_{S̃ | Ỹ_j}‖ ≤ 3 E`, with `E` the bound of (6.5). This is the
second hypothesis of Corollary 5.3. -/
theorem sum_dist_condLaw_withKernel_condY_le
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    ∑ j : {i // i ∉ C}, dist ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω))
        (withKernel G.questions fun xy =>
          condY ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω)) xy.2) ≤
      3 * Real.sqrt (#Cᶜ * (#C * Real.log (Fintype.card A * Fintype.card B) +
        Real.log (1 / G.winProbOn ha hb C)) / 2) := by
  have h1 := sum_dist_map_condLaw_shared_le hC false
  have h2 := (sum_dist_map_condLaw_pair_le hC).trans (sqrt_log_le_sqrt (A := A) (B := B) _)
  refine (Finset.sum_le_sum fun j _ => dist_condLaw_withKernel_condY_le hC j).trans ?_
  rw [Finset.sum_add_distrib]
  linarith

/-- **Holenstein's (6.16)** [Holenstein, proof of Lemma 6.4, (6.16)][Holenstein2009]: the mirror
image of (6.15), with `S` drawn given Alice's question:
`∑_{j ∉ C} ‖P_{X̃_j Ỹ_j S̃} - P_{XY} P_{S̃ | X̃_j}‖ ≤ 3 E`, with `E` the bound of (6.5). This is the
first hypothesis of Corollary 5.3. -/
theorem sum_dist_condLaw_withKernel_condX_le
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    ∑ j : {i // i ∉ C}, dist ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω))
        (withKernel G.questions fun xy =>
          condX ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω)) xy.1) ≤
      3 * Real.sqrt (#Cᶜ * (#C * Real.log (Fintype.card A * Fintype.card B) +
        Real.log (1 / G.winProbOn ha hb C)) / 2) := by
  have h1 := sum_dist_map_condLaw_shared_le hC true
  have h2 := (sum_dist_map_condLaw_pair_le hC).trans (sqrt_log_le_sqrt (A := A) (B := B) _)
  refine (Finset.sum_le_sum fun j _ => dist_condLaw_withKernel_condX_le hC j).trans ?_
  rw [Finset.sum_add_distrib]
  linarith

/-- **The first stage of Holenstein's Lemma 6.4** [Holenstein, proof of Lemma 6.4, p. 157, from
(6.15) and (6.16) by Corollary 5.3][Holenstein2009]. At each free coordinate `j`, the questions of
`G` embed in the law of `((x_j, y_j), (S, S))` under `W_C`, where `S = (T^{(\j)}, V)` is `shared`:
from their questions, Alice and Bob produce the same value of `S` with error `ε_j`. The errors
satisfy `∑_{j ∉ C} ε_j ≤ 27 / √2 · √(#Cᶜ (#C ln (|A| |B|) + ln (1 / Pr[W_C])))`.

Holenstein's bound is `15 √k √((n - k) log (|A| |B|) + log (1 / Pr[W]))` in bits, with `k = #Cᶜ`
and `n - k = #C`. Here the constant is `27 = 7 · 3 + 2 · 3` from the library's Corollary 5.3, and
the logarithms are natural, with the factor `1 / √2` of Pinsker's inequality. -/
theorem exists_isEmbeddable_condLaw_shared
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) :
    ∃ ε : {i // i ∉ C} → ℝ,
      (∀ j, IsEmbeddable G.questions
        ((condLaw G C ha hb hC).map fun ω => (ω.2 j, (shared ha hb j ω, shared ha hb j ω)))
        (ε j)) ∧
      ∑ j, ε j ≤ 27 / Real.sqrt 2 *
        Real.sqrt (#Cᶜ * (#C * Real.log (Fintype.card A * Fintype.card B) +
          Real.log (1 / G.winProbOn ha hb C))) := by
  set J := fun j : {i // i ∉ C} => (condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω)
  refine ⟨fun j => 7 * dist (J j) (withKernel G.questions fun xy => condX (J j) xy.1) +
    2 * dist (J j) (withKernel G.questions fun xy => condY (J j) xy.2), fun j => ?_, ?_⟩
  · have h := isEmbeddable_diag_of_dist_le (J j) G.questions le_rfl le_rfl
    rwa [PMF.map_comp] at h
  · have hX := sum_dist_condLaw_withKernel_condX_le hC
    have hY := sum_dist_condLaw_withKernel_condY_le hC
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Real.sqrt_div' _ zero_le_two] at *
    calc _ ≤ 7 * (3 * _) + 2 * (3 * _) :=
          add_le_add (mul_le_mul_of_nonneg_left hX (by norm_num))
            (mul_le_mul_of_nonneg_left hY (by norm_num))
      _ = _ := by ring

end Cslib.PCP.ParallelRepetition
