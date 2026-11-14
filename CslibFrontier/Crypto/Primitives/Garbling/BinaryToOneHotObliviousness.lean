/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.BinaryToOneHot
public import CslibFrontier.Crypto.Primitives.Garbling.CircularCorrelationRobust
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Uniform
import Mathlib.Tactic.Abel

/-!
# Obliviousness of the garbled binary-to-one-hot conversion

The evaluator of the binary-to-one-hot conversion `bin-to-hot` of Heath [Heath2024] (§4.1, p. 14),
used for one-hot garbling in `logrow` [HeathKolesnikovNg2024], sees a `OneHotView`: one label on
each of the `n + 1` input wires and the `n` ciphertexts. Its index `x` is public. The simulator
`simulate` samples all of these uniformly, from `n` alone. A simulator that sees neither the input
nor an output is *obliviousness* in the sense of Bellare, Hoang and Rogaway
[BellareHoangRogaway2012], the notion of [HeathKolesnikovNg2024], Theorem 3, whose proof simulates
the one-hot rows (`n` here, the paper's `n - 1`) by uniform strings and refers to
[HeathKolesnikov2021] for this. The argument of [HeathKolesnikov2021] is for its own GGM-tree
construction, and [Heath2024] obtains obliviousness from its general switch-system theorem
(Theorem 4). The reduction below is original to this file: an exact finite reduction from the
single-ciphertext construction to the tweaked circular correlation robustness game.

Security rests on circular correlation robustness [ChoiKatzKumaresanZhou2012], in the tweaked form
of [HeathKolesnikovNg2024], Definition 1, which follows [ZahurRosulekEvans2015] (see also
[GuoKatzWangYu2020] on tweakable variants). It is the instance `Cslib.Crypto.Garbling.CCR` with
both offsets `δ k`: for an offset `Δ` drawn from a key, the oracle `CCR.oracle H Δ Δ` answers
`(X, τ, b)` with `H (X + Δ) τ + bitOffset Δ b`; Definition 1 draws `Δ` with its least significant
bit fixed to one, which a suitable key map `δ` expresses. The main theorem
`advantage_realGame_simGame_eq` states that for every distinguisher `D`, the advantage between the
real view and the simulated view equals the circular correlation robustness advantage
`CCR.advantage H δ δ` of an explicit reduction `reduction H tw n x D`. It needs only that
different doubling steps use different tweaks.

The reduction samples the input labels uniformly and evaluates the gadget step by step. At step
`t` it needs the hash of the zero-label at the hot position, which is its own label there plus
`Δ`, so it makes one query, at its label, at the tweak of the hot position and the new input bit.
With the keyed oracle the answer is that hash plus the new bit's offset, which gives the
ciphertext exactly (`realGame_reduction`). With a uniformly random function every query is at a
fresh tweak, so every ciphertext is uniform given what came before (`idealGame_reduction`). The
random-function side resamples the function at a query point that the function itself chooses,
using `Cslib.Probability.PMF.uniformOfFintype_bind_bind_adaptiveUpdate`.

The reduction makes `n` queries (`isQueryBounded_reduction`) at pairwise distinct tweaks
(`isTweakUnique_reduction`). In particular it never asks the same `(X, τ)` with both bits, which
Definition 1 forbids as illegal: against such a query pair the keyed oracle is trivially
distinguishable, so the bound is meaningful for the reductions of this file and not for arbitrary
adversaries of `CCR.advantage`. This is the
single-instance form: the index, tweaks and distinguisher are fixed, and running time is not
tracked. Obliviousness, privacy and authenticity of the full `logrow` gate are not formalized here.

## Main definitions

* `Cslib.Crypto.Garbling.BinaryToOneHot.OneHotView`: what the evaluator sees.
* `Cslib.Crypto.Garbling.BinaryToOneHot.simulate`: the simulator.
* `Cslib.Crypto.Garbling.BinaryToOneHot.realGame`, `.simGame`: the obliviousness experiments.
* `Cslib.Crypto.Garbling.BinaryToOneHot.reduction`: the circular correlation robustness adversary.

## Main results

* `Cslib.Crypto.Garbling.BinaryToOneHot.isQueryBounded_reduction`: one query per step.
* `Cslib.Crypto.Garbling.BinaryToOneHot.isTweakUnique_reduction`: at most one query per tweak when
  different steps use different tweaks (`CCR.IsTweakUnique`).
* `Cslib.Crypto.Garbling.BinaryToOneHot.realGame_reduction`: the keyed oracle gives the real view.
* `Cslib.Crypto.Garbling.BinaryToOneHot.idealGame_reduction`: a random function gives the
  simulated view.
* `Cslib.Crypto.Garbling.BinaryToOneHot.advantage_realGame_simGame_eq`: obliviousness.

## References

* [D. Heath, *Efficient Arithmetic in Garbled Circuits*][Heath2024]
* [D. Heath, V. Kolesnikov, *One Hot Garbling*][HeathKolesnikov2021]
* [D. Heath, V. Kolesnikov, L. K. L. Ng, *Garbled Circuit Lookup Tables with Logarithmic Number
  of Ciphertexts*][HeathKolesnikovNg2024]
* [S. G. Choi, J. Katz, R. Kumaresan, H.-S. Zhou, *On the Security of the "Free-XOR"
  Technique*][ChoiKatzKumaresanZhou2012]
* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits Using Half Gates*][ZahurRosulekEvans2015]
* [C. Guo, J. Katz, X. Wang, Y. Yu, *Efficient and Secure Multiparty Computation from Fixed-Key
  Block Ciphers*][GuoKatzWangYu2020]
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling.BinaryToOneHot

open Probability

variable {L T Key : Type} [AddCommGroup L]

/-- What the evaluator of the gadget with `n` doubling steps sees: one label on each input wire
and the ciphertexts. Its index is public and is not part of the view. -/
abbrev OneHotView (L : Type) (n : ℕ) : Type := (Fin (n + 1) → L) × (Fin n → L)

/-- The reduction's evaluation, against oracle `O`: the ciphertexts of the gadget whose evaluator
holds the labels `A`, and the evaluator's one-hot labels. Step `t` asks `O` once, at the label at
the hot position, the tweak of that position and the new input bit. -/
def oracleSteps (H : L → T → L) (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) :
    (n : ℕ) → (Fin (n + 1) → Bool) → (Fin (n + 1) → L) →
      ProbOracleComp (fun _ : CCR.Query L T => L) ((Fin n → L) × ((Fin (n + 1) → Bool) → L))
  | 0, _, A => pure (Fin.elim0, fun _ => A 0)
  | n + 1, x, A => do
    let prev ← oracleSteps H tw n (Fin.init x) (Fin.init A)
    let r ← ProbOracleComp.query ⟨prev.2 (Fin.init x), tw n (Fin.init x), x (Fin.last (n + 1))⟩
    let ct := A (Fin.last (n + 1)) + r +
      ∑ j ∈ Finset.univ.erase (Fin.init x), H (prev.2 j) (tw n j)
    return (Fin.snoc prev.1 ct,
      evalStep (hashAt H tw n) (Fin.init x) (A (Fin.last (n + 1))) ct prev.2)

/-- The same evaluation against a fixed function `f`. -/
private def runSteps (H : L → T → L) (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T)
    (f : CCR.Query L T → L) :
    (n : ℕ) → (Fin (n + 1) → Bool) → (Fin (n + 1) → L) →
      (Fin n → L) × ((Fin (n + 1) → Bool) → L)
  | 0, _, A => (Fin.elim0, fun _ => A 0)
  | n + 1, x, A =>
    let prev := runSteps H tw f n (Fin.init x) (Fin.init A)
    let ct := A (Fin.last (n + 1)) + f ⟨prev.2 (Fin.init x), tw n (Fin.init x),
      x (Fin.last (n + 1))⟩ + ∑ j ∈ Finset.univ.erase (Fin.init x), H (prev.2 j) (tw n j)
    (Fin.snoc prev.1 ct, evalStep (hashAt H tw n) (Fin.init x) (A (Fin.last (n + 1))) ct prev.2)

/-- Against a fixed function, the reduction's evaluation is `runSteps`. -/
private theorem interpret_oracleSteps {m : Type → Type*} [Monad m] [LawfulMonad m]
    (random : (k : ℕ) → m (Fin (k + 1))) (H : L → T → L)
    (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (f : CCR.Query L T → L) (n : ℕ)
    (x : Fin (n + 1) → Bool) (A : Fin (n + 1) → L) :
    OracleComp.interpret (OracleComp.sumHandler random fun q => pure (f q))
        (oracleSteps H tw n x A) = pure (runSteps H tw f n x A) := by
  induction n with
  | zero => simp only [oracleSteps, OracleComp.interpret_pure, runSteps]
  | succ n ih =>
    simp only [oracleSteps, OracleComp.interpret_bind, ih, ProbOracleComp.interpret_query,
      OracleComp.interpret_pure, pure_bind]
    rfl

/-- The reduction's evaluation reads `f` only at the tweaks of the steps it runs. -/
private theorem runSteps_congr (H : L → T → L) (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T)
    (f f' : CCR.Query L T → L) (n : ℕ) (x : Fin (n + 1) → Bool) (A : Fin (n + 1) → L)
    (h : ∀ q : CCR.Query L T, (∃ t < n, ∃ j, q.tweak = tw t j) → f q = f' q) :
    runSteps H tw f n x A = runSteps H tw f' n x A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev := ih (Fin.init x) (Fin.init A) fun q ⟨t, ht, j, hj⟩ => h q ⟨t, by omega, j, hj⟩
    simp only [runSteps]
    rw [hprev, h _ ⟨n, by omega, Fin.init x, rfl⟩]

/-- The reduction's evaluation makes one oracle query per doubling step. -/
private theorem isQueryBounded_oracleSteps (H : L → T → L)
    (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (n : ℕ) (x : Fin (n + 1) → Bool)
    (A : Fin (n + 1) → L) : (oracleSteps H tw n x A).IsQueryBounded n := by
  induction n with
  | zero => exact OracleComp.IsCostBounded.pure _ 0
  | succ n ih =>
    exact (ih (Fin.init x) (Fin.init A)).bind fun prev =>
      (ProbOracleComp.IsQueryBounded.query (spec := fun _ : CCR.Query L T => L)
        ⟨prev.2 (Fin.init x), tw n (Fin.init x), x (Fin.last (n + 1))⟩).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

/-- When different steps use different tweaks, the reduction's evaluation makes at most one query
with each tweak. -/
private theorem isCostBounded_oracleSteps_tweak [DecidableEq T] (H : L → T → L)
    (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (n : ℕ)
    (htw : ∀ t t' j j', t < n → t' < n → tw t j = tw t' j' → t = t')
    (x : Fin (n + 1) → Bool) (A : Fin (n + 1) → L) (τ : T) :
    OracleComp.IsCostBounded
      (Sum.elim (fun _ => 0) fun q : CCR.Query L T => if q.tweak = τ then 1 else 0)
      (oracleSteps H tw n x A)
      (if ∃ s < n, ∃ j, tw s j = τ then 1 else 0) := by
  classical
  induction n with
  | zero => exact OracleComp.IsCostBounded.pure _ _
  | succ n ih =>
    have htw' : ∀ t t' j j', t < n → t' < n → tw t j = tw t' j' → t = t' :=
      fun t t' j j' ht ht' => htw t t' j j' (by omega) (by omega)
    refine OracleComp.IsCostBounded.mono
      (n := (if ∃ s < n, ∃ j, tw s j = τ then 1 else 0) +
        ((if tw n (Fin.init x) = τ then 1 else 0) + 0)) ?_ ?_
    · exact (ih htw' (Fin.init x) (Fin.init A)).bind fun prev =>
        (ProbOracleComp.isCostBounded_query (spec := fun _ : CCR.Query L T => L)
          (fun q : CCR.Query L T => if q.tweak = τ then 1 else 0)
          ⟨prev.2 (Fin.init x), tw n (Fin.init x), x (Fin.last (n + 1))⟩).bind fun _ =>
        OracleComp.IsCostBounded.pure _ 0
    · by_cases h1 : ∃ s < n, ∃ j, tw s j = τ
      · obtain ⟨s, hs, j, hst⟩ := h1
        have h1' : ∃ s < n, ∃ j, tw s j = τ := ⟨s, hs, j, hst⟩
        have h2 : ¬ tw n (Fin.init x) = τ := fun h2 => by
          have := htw s n j (Fin.init x) (by omega) (by omega) (hst.trans h2.symm)
          omega
        have h3 : ∃ s < n + 1, ∃ j, tw s j = τ := ⟨s, by omega, j, hst⟩
        simp only [h1', h2, h3, ↓reduceIte, Nat.add_zero, le_refl]
      · by_cases h2 : tw n (Fin.init x) = τ
        · have h3 : ∃ s < n + 1, ∃ j, tw s j = τ := ⟨n, by omega, Fin.init x, h2⟩
          simp only [h1, h2, h3, ↓reduceIte, Nat.add_zero, zero_add, le_refl]
        · simp only [h1, h2, ↓reduceIte, Nat.add_zero, Nat.zero_le]

/-- Against the keyed oracle with offset `Δ`, on the labels of the bits of `x` with zero-labels
`X`, the reduction's evaluation gives the garbled ciphertexts and the one-hot labels. -/
private theorem runSteps_oracle [Module (ZMod 2) L] (H : L → T → L)
    (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (Δ : L)
    (n : ℕ) (x : Fin (n + 1) → Bool) (X : Fin (n + 1) → L) :
    runSteps H tw (CCR.oracle H Δ Δ) n x (fun t => X t + bitOffset Δ (x t)) =
      ((garble H tw Δ n X).2, fun j => (garble H tw Δ n X).1 j + bitOffset Δ (oneHot x j)) := by
  induction n with
  | zero =>
    refine Prod.ext (funext fun i => i.elim0) ?_
    have h := evaluate_garble H tw Δ 0 X x
    simp only [evaluate] at h
    exact h
  | succ n ih =>
    have hA : (Fin.init fun t => X t + bitOffset Δ (x t)) =
        fun t => Fin.init X t + bitOffset Δ (Fin.init x t) := rfl
    have hct : ∀ G : (Fin (n + 1) → Bool) → L,
        X (Fin.last (n + 1)) + bitOffset Δ (x (Fin.last (n + 1))) +
          CCR.oracle H Δ Δ ⟨G (Fin.init x) + bitOffset Δ (oneHot (Fin.init x) (Fin.init x)),
            tw n (Fin.init x), x (Fin.last (n + 1))⟩ +
          ∑ j ∈ Finset.univ.erase (Fin.init x),
            H (G j + bitOffset Δ (oneHot (Fin.init x) j)) (tw n j) =
        (garbleStep (hashAt H tw n) (X (Fin.last (n + 1))) G).2 := by
      intro G
      have hrest : ∑ j ∈ Finset.univ.erase (Fin.init x),
          H (G j + bitOffset Δ (oneHot (Fin.init x) j)) (tw n j) =
          ∑ j ∈ Finset.univ.erase (Fin.init x), H (G j) (tw n j) :=
        Finset.sum_congr rfl fun j hj => by
          rw [oneHot_of_ne (Finset.ne_of_mem_erase hj), bitOffset_false, add_zero]
      simp only [CCR.oracle_apply, oneHot_self, bitOffset_true, garbleStep, hashAt, hrest]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Fin.init x)), add_assoc (G _),
        ZModModule.add_self, add_zero]
      rw [show X (Fin.last (n + 1)) + bitOffset Δ (x (Fin.last (n + 1))) +
          (H (G (Fin.init x)) (tw n (Fin.init x)) + bitOffset Δ (x (Fin.last (n + 1)))) +
          ∑ j ∈ Finset.univ.erase (Fin.init x), H (G j) (tw n j) =
          X (Fin.last (n + 1)) + (H (G (Fin.init x)) (tw n (Fin.init x)) +
            ∑ j ∈ Finset.univ.erase (Fin.init x), H (G j) (tw n j)) +
          (bitOffset Δ (x (Fin.last (n + 1))) + bitOffset Δ (x (Fin.last (n + 1)))) by abel,
        ZModModule.add_self, add_zero]
    simp only [runSteps]
    rw [hA, ih (Fin.init x) (Fin.init X), hct]
    refine Prod.ext rfl ?_
    simp only
    rw [evalStep_garbleStep, Fin.snoc_init_self]
    rfl

variable [Fintype L]

/-- The simulator: uniform input labels and uniform ciphertexts. It sees only `n`. -/
noncomputable def simulate (n : ℕ) : ProbComp (OneHotView L n) := do
  let A ← ProbComp.uniform (Fin (n + 1) → L)
  let ct ← ProbComp.uniform (Fin n → L)
  return (A, ct)

/-- The real obliviousness experiment: draw a key and uniform input zero-labels, garble, and run `D`
on the labels of the bits of `x` and the ciphertexts. -/
@[expose] noncomputable def realGame [Fintype Key] [Nonempty Key] (H : L → T → L)
    (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (δ : Key → L) (n : ℕ) (x : Fin (n + 1) → Bool)
    (D : OneHotView L n → ProbComp Bool) : Game :=
  ProbComp.eval do
    let k ← ProbComp.uniform Key
    let X ← ProbComp.uniform (Fin (n + 1) → L)
    D (fun t => X t + bitOffset (δ k) (x t), (garble H tw (δ k) n X).2)

/-- The simulated obliviousness experiment: run `D` on a simulated view. -/
@[expose] noncomputable def simGame (n : ℕ) (D : OneHotView L n → ProbComp Bool) : Game :=
  ProbComp.eval do
    let V ← simulate n
    D V

/-- The circular correlation robustness adversary: sample the input labels uniformly, compute the
ciphertexts with one oracle query per step, and run `D` on the labels and ciphertexts. -/
noncomputable def reduction (H : L → T → L) (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (n : ℕ)
    (x : Fin (n + 1) → Bool) (D : OneHotView L n → ProbComp Bool) :
    ProbOracleComp (fun _ : CCR.Query L T => L) Bool := do
  let A ← ProbOracleComp.sample (ProbComp.uniform (Fin (n + 1) → L))
  let steps ← oracleSteps H tw n x A
  ProbOracleComp.sample (D (A, steps.1))

/-- The reduction makes one oracle query per doubling step. -/
theorem isQueryBounded_reduction (H : L → T → L) (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T)
    (n : ℕ) (x : Fin (n + 1) → Bool) (D : OneHotView L n → ProbComp Bool) :
    (reduction H tw n x D).IsQueryBounded n := by
  have h := (ProbOracleComp.IsQueryBounded.sample (spec := fun _ : CCR.Query L T => L)
    (ProbComp.uniform (Fin (n + 1) → L))).bind fun A =>
    (isQueryBounded_oracleSteps H tw n x A).bind fun steps =>
    ProbOracleComp.IsQueryBounded.sample (spec := fun _ : CCR.Query L T => L) (D (A, steps.1))
  simpa only [reduction, Nat.zero_add, Nat.add_zero] using h

/-- When different steps use different tweaks, the reduction makes at most one query with each
tweak. -/
theorem isTweakUnique_reduction [DecidableEq T] (H : L → T → L)
    (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (n : ℕ)
    (htw : ∀ t t' j j', t < n → t' < n → tw t j = tw t' j' → t = t')
    (x : Fin (n + 1) → Bool) (D : OneHotView L n → ProbComp Bool) :
    CCR.IsTweakUnique (reduction H tw n x D) := by
  classical
  intro τ
  refine ((ProbOracleComp.isCostBounded_sample _
    (ProbComp.uniform (Fin (n + 1) → L))).bind fun A =>
    (isCostBounded_oracleSteps_tweak H tw n htw x A τ).bind fun steps =>
    ProbOracleComp.isCostBounded_sample _ (D (A, steps.1))).mono ?_
  split_ifs <;> omega

/-- Against a fixed function the reduction runs `D` on uniform labels and the ciphertexts of
`runSteps`. -/
private theorem eval_run_reduction (H : L → T → L)
    (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (n : ℕ) (x : Fin (n + 1) → Bool)
    (D : OneHotView L n → ProbComp Bool) (f : CCR.Query L T → L) :
    ProbComp.eval ((reduction H tw n x D).run fun q => pure (f q)) =
      (PMF.uniformOfFintype (Fin (n + 1) → L)).bind fun A =>
        ProbComp.eval (D (A, (runSteps H tw f n x A).1)) := by
  simp only [ProbOracleComp.run, reduction, OracleComp.interpret_bind,
    ProbOracleComp.interpret_sample, ProbComp.interpret_unifFin, interpret_oracleSteps, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_uniform]

/-- **Real side**: against the keyed oracle, the reduction plays the real experiment. -/
theorem realGame_reduction [Module (ZMod 2) L] [Fintype Key] [Nonempty Key] (H : L → T → L)
    (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (δ : Key → L) (n : ℕ) (x : Fin (n + 1) → Bool)
    (D : OneHotView L n → ProbComp Bool) :
    ProbComp.eval (PRF.realExperiment (CCR.keyed H δ δ) (reduction H tw n x D)) =
      realGame H tw δ n x D := by
  simp only [PRF.realExperiment, realGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_run_reduction]
  congr 1 with k : 1
  -- The input labels are the zero-labels shifted by the offsets of the bits of `x`.
  let e : (Fin (n + 1) → L) ≃ (Fin (n + 1) → L) :=
    Equiv.addRight fun t => bitOffset (δ k) (x t)
  conv_lhs => rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv e, PMF.bind_map]
  congr 1 with X : 1
  have hX : e X = fun t => X t + bitOffset (δ k) (x t) := rfl
  simp only [Function.comp_apply, hX, CCR.keyed, runSteps_oracle]

variable [DecidableEq L] [Fintype T] [DecidableEq T]

/-- With a uniformly random function, the reduction's ciphertexts are uniform, when different
steps use different tweaks. -/
private theorem uniformOfFintype_bind_runSteps {β : Type} (H : L → T → L)
    (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (n : ℕ)
    (htw : ∀ t t' j j', t < n → t' < n → tw t j = tw t' j' → t = t')
    (x : Fin (n + 1) → Bool) (A : Fin (n + 1) → L) (g : (Fin n → L) → PMF β) :
    ((PMF.uniformOfFintype (CCR.Query L T → L)).bind fun f => g (runSteps H tw f n x A).1) =
      (PMF.uniformOfFintype (Fin n → L)).bind g := by
  induction n generalizing β with
  | zero =>
    have hg : ∀ f : CCR.Query L T → L, g (runSteps H tw f 0 x A).1 = g Fin.elim0 :=
      fun _ => congrArg g (funext fun i => i.elim0)
    have hu : ∀ c : Fin 0 → L, g c = g Fin.elim0 := fun c => congrArg g (funext fun i => i.elim0)
    simp only [hg, PMF.bind_const]
    rw [show (PMF.uniformOfFintype (Fin 0 → L)).bind g =
        (PMF.uniformOfFintype (Fin 0 → L)).bind fun _ => g Fin.elim0 from congrArg _ (funext hu),
      PMF.bind_const]
  | succ n ih =>
    have htw' : ∀ t t' j j', t < n → t' < n → tw t j = tw t' j' → t = t' :=
      fun t t' j j' ht ht' => htw t t' j j' (by omega) (by omega)
    let prev : (CCR.Query L T → L) → (Fin n → L) × ((Fin (n + 1) → Bool) → L) := fun f =>
      runSteps H tw f n (Fin.init x) (Fin.init A)
    -- The query of the last step.
    let p : (CCR.Query L T → L) → CCR.Query L T := fun f =>
      ⟨(prev f).2 (Fin.init x), tw n (Fin.init x), x (Fin.last (n + 1))⟩
    let s : (CCR.Query L T → L) → L := fun f => A (Fin.last (n + 1)) +
      ∑ j ∈ Finset.univ.erase (Fin.init x), H ((prev f).2 j) (tw n j)
    have hprev : ∀ f v, prev (Function.update f (p f) v) = prev f := fun f v =>
      runSteps_congr H tw _ _ n _ _ fun q ⟨t, ht, j, hj⟩ => Function.update_of_ne (fun hq => by
        have := htw t n j (Fin.init x) (by omega) (by omega)
          (hj.symm.trans (congrArg CCR.Query.tweak hq))
        omega) _ _
    have hp : ∀ f v, p (Function.update f (p f) v) = p f := fun f v => by
      simp only [p, hprev]
    have hs : ∀ f v, s (Function.update f (p f) v) = s f := fun f v => by
      simp only [s, hprev]
    have hrun : ∀ f, (runSteps H tw f (n + 1) x A).1 = Fin.snoc (prev f).1 (s f + f (p f)) :=
      fun f => by
        simp only [runSteps, prev, s, p]
        congr 1
        abel
    calc ((PMF.uniformOfFintype (CCR.Query L T → L)).bind fun f =>
          g (runSteps H tw f (n + 1) x A).1)
        = (PMF.uniformOfFintype (CCR.Query L T → L)).bind fun f =>
            (PMF.uniformOfFintype L).bind fun v =>
              g (Fin.snoc (prev f).1 (s f + v)) := by
          rw [← Cslib.Probability.PMF.uniformOfFintype_bind_bind_adaptiveUpdate p hp]
          refine congrArg _ (funext fun f => congrArg _ (funext fun v => ?_))
          rw [hrun, hprev, hs, hp, Function.update_self]
      _ = (PMF.uniformOfFintype (CCR.Query L T → L)).bind fun f =>
            (PMF.uniformOfFintype L).bind fun c => g (Fin.snoc (prev f).1 c) := by
          refine congrArg _ (funext fun f => ?_)
          conv_rhs => rw [← Cslib.Probability.PMF.uniformOfFintype_map_equiv (Equiv.addLeft (s f)),
            PMF.bind_map]
          rfl
      _ = (PMF.uniformOfFintype (Fin n → L)).bind fun ct =>
            (PMF.uniformOfFintype L).bind fun c => g (Fin.snoc ct c) :=
          ih htw' (Fin.init x) (Fin.init A) fun ct =>
            (PMF.uniformOfFintype L).bind fun c => g (Fin.snoc ct c)
      _ = (PMF.uniformOfFintype (Fin (n + 1) → L)).bind g := by
          let e : (Fin n → L) × L ≃ (Fin (n + 1) → L) × Unit :=
            ((Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ => L)).trans
              (Equiv.prodPUnit _).symm
          exact Cslib.Probability.PMF.uniformOfFintype_bind_bind_fst_equiv e g

/-- **Ideal side**: against a uniformly random function, the reduction plays the simulated
experiment, when different doubling steps use different tweaks. -/
theorem idealGame_reduction (H : L → T → L) (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (n : ℕ)
    (htw : ∀ t t' j j', t < n → t' < n → tw t j = tw t' j' → t = t')
    (x : Fin (n + 1) → Bool) (D : OneHotView L n → ProbComp Bool) :
    ProbComp.eval (PRF.idealExperiment (reduction H tw n x D)) = simGame n D := by
  simp only [PRF.idealExperiment, simGame, simulate, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_run_reduction, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun A => ?_)
  exact uniformOfFintype_bind_runSteps H tw n htw x A fun ct => ProbComp.eval (D (A, ct))

/-- **Obliviousness of the binary-to-one-hot gadget**: for every distinguisher `D`, the advantage
between the real view of the garbled gadget on index `x` and the simulated view equals the
advantage of `reduction H tw n x D` against the circular correlation robust oracle, when different
doubling steps use different tweaks. The proof uses that each query is at a fresh tweak; only the
tweaks at the hot positions need to differ across steps, so `htw` is stronger than necessary. -/
theorem advantage_realGame_simGame_eq [Module (ZMod 2) L] [Fintype Key] [Nonempty Key]
    (H : L → T → L)
    (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (δ : Key → L) (n : ℕ)
    (htw : ∀ t t' j j', t < n → t' < n → tw t j = tw t' j' → t = t')
    (x : Fin (n + 1) → Bool) (D : OneHotView L n → ProbComp Bool) :
    Game.advantage (realGame H tw δ n x D) (simGame n D) =
      CCR.advantage H δ δ (reduction H tw n x D) := by
  rw [CCR.advantage, PRF.advantage, realGame_reduction, idealGame_reduction H tw n htw]

end Cslib.Crypto.Garbling.BinaryToOneHot
