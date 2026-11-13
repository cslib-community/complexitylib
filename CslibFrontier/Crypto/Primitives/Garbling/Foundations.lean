/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Games
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PMFSwap

/-!
# Indistinguishability and simulation security of garbling schemes

The relations between the indistinguishability and the simulation notions of privacy and
obliviousness of [BellareHoangRogaway2012], Section 4, by explicit reductions at a fixed security
parameter.

* Simulation security implies indistinguishability security with a factor of two: from a
  `prv.ind` adversary `A` the reduction `prvIndToSim` builds a `prv.sim` adversary that picks a
  hidden bit `c`, submits the query `c` of the pair of `A` and checks whether `A` recovers `c`.
  Against the real garbling it plays the bit-guessing form `Experiment.guessBit` of `PrvInd` with
  `A`; against any simulator its view does not depend on `c`, as the simulator only sees `Φ(f_c)`
  and `ev(f_c, x_c)`, which a valid pair makes the same for both values of `c`, so it outputs a fair
  coin. Hence `Adv^prv.ind(A) = 2 · Adv^prv.sim(prvIndToSim A)` against every simulator.
* Indistinguishability security implies simulation security when the side information is
  efficiently invertible: an `ev`-inverter `M` for `Φ` yields a simulator `prvSimFromInverter`
  that garbles the query `M(Φ(f), ev(f, x))`, and against it the `prv.sim` game on `B` is the
  `prv.ind` game on the adversary `prvSimToInd` that queries the pair of `M(Φ(f), ev(f, x))` and
  `(f, x)`.

The same reductions, without the output `ev(f, x)` and the decoding information `d`, relate
`obv.ind` and `obv.sim`, with an inverter of `Φ` in place of an `ev`-inverter. Both notions use the
generic reductions `indToSim` and `simToInd`, which take the view type and the validity predicate
as parameters, and the two arguments above are proved once for both.

## Main definitions

* `Cslib.Crypto.Garbling.indToSim`, `Cslib.Crypto.Garbling.simToInd`: the generic reductions
  between indistinguishability and simulation adversaries.
* `Cslib.Crypto.Garbling.prvIndToSim`, `Cslib.Crypto.Garbling.obvIndToSim`: the reductions from
  indistinguishability to simulation adversaries.
* `Cslib.Crypto.Garbling.prvSimFromInverter`, `Cslib.Crypto.Garbling.obvSimFromInverter`: the
  simulators built from inverters, and `Cslib.Crypto.Garbling.prvSimToInd`,
  `Cslib.Crypto.Garbling.obvSimToInd`, the corresponding reductions from simulation to
  indistinguishability adversaries.

## Main results

* `Cslib.Crypto.Garbling.prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim`,
  `Cslib.Crypto.Garbling.obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim`: the
  indistinguishability advantage is twice the simulation advantage of the reduction, against
  every simulator ([BellareHoangRogaway2012], Propositions 2 and 3).
* `Cslib.Crypto.Garbling.prvSimAdvantage_prvSimFromInverter_eq`,
  `Cslib.Crypto.Garbling.obvSimAdvantage_obvSimFromInverter_eq`: against the simulator built from
  an inverter, the simulation advantage is the indistinguishability advantage of the reduction
  ([BellareHoangRogaway2012], Propositions 2 and 3).

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling

open Probability
open scoped NNReal

variable {Fn Λ σ : Type}

/-! ## The reductions -/

/-- The state of the reductions from indistinguishability to simulation adversaries: the state
of the indistinguishability adversary, the hidden bit chosen by the reduction and the pair of
queries of the adversary. -/
structure IndToSimState (Fn σ : Type) where
  /-- The state of the indistinguishability adversary. -/
  state : σ
  /-- The hidden bit chosen by the reduction. -/
  bit : Bool
  /-- The pair of queries of the indistinguishability adversary. -/
  pair : MessagePair (Query Fn)

/-- The simulation adversary built from an indistinguishability adversary `A` with views in `V`
whose pairs are checked by `valid`: it picks a hidden bit `c`, submits the query `c` of the pair of
`A` when the pair is valid and the query `0` otherwise, and outputs whether `A` recovers `c`. `A`
receives `⊥` when its pair is invalid. -/
noncomputable def indToSim {V : Type} (valid : MessagePair (Query Fn) → Prop)
    [DecidablePred valid] (A : TwoStage Unit (MessagePair (Query Fn)) (Option V) Bool σ) :
    TwoStage Unit (Query Fn) (Option V) Bool (IndToSimState Fn σ) where
  choose _ := do
    let (pair, st) ← A.choose ()
    let c ← ProbComp.uniform Bool
    pure (if valid pair then pair.select c else pair.msg₀, ⟨st, c, pair⟩)
  guess s view := do
    let guess ← A.guess s.state (if valid s.pair then view else none)
    pure (guess == s.bit)

/-- The indistinguishability adversary built from a simulation adversary `B` with views in `V` and
a map `inv` on queries: it queries the pair of `inv q` and the query `q` of `B`, and guesses as `B`
does. -/
def simToInd {V : Type} (inv : Query Fn → Query Fn)
    (B : TwoStage Unit (Query Fn) (Option V) Bool σ) :
    TwoStage Unit (MessagePair (Query Fn)) (Option V) Bool σ where
  choose _ := do
    let (q, st) ← B.choose ()
    pure (⟨inv q, q⟩, st)
  guess := B.guess

/-- The `prv.sim` adversary built from a `prv.ind` adversary `A` ([BellareHoangRogaway2012],
Proposition 2): it picks a hidden bit `c`, submits the query `c` of the pair of `A` when the pair is
valid and the query `0` otherwise, and outputs whether `A` recovers `c`. -/
noncomputable def prvIndToSim [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (A : PrvIndAdversary Fn σ) : PrvSimAdversary Fn (IndToSimState Fn σ) :=
  indToSim (prvIndValid G Φ) A

/-- The `prv.sim` simulator built from an `ev`-inverter `M` for the side information
([BellareHoangRogaway2012], Section 4.2): the real view of the query that `M` produces from
`ev(f, x)` and `Φ(f)`. -/
noncomputable def prvSimFromInverter (G : Scheme Fn) (k : ℕ) (M : Λ → List Bool → Query Fn) :
    PrvSimulator Λ :=
  fun y φ => G.prvView k (M φ y)

/-- The `prv.ind` adversary built from a `prv.sim` adversary `B` and an `ev`-inverter `M`
([BellareHoangRogaway2012], Proposition 2): it queries the pair of `M(Φ(f), ev(f, x))` and the
query `(f, x)` of `B`, and guesses as `B` does. -/
def prvSimToInd (G : Scheme Fn) (Φ : SideInfo Fn Λ) (M : Λ → List Bool → Query Fn)
    (B : PrvSimAdversary Fn σ) : PrvIndAdversary Fn σ :=
  simToInd (fun q => M (Φ.phi q.fn) (G.ev q.fn q.input)) B

/-- The `obv.sim` adversary built from an `obv.ind` adversary `A` ([BellareHoangRogaway2012],
Proposition 3): it picks a hidden bit `c`, submits the query `c` of the pair of `A` when the pair is
valid and the query `0` otherwise, and outputs whether `A` recovers `c`. -/
noncomputable def obvIndToSim [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (A : ObvIndAdversary Fn σ) : ObvSimAdversary Fn (IndToSimState Fn σ) :=
  indToSim (obvIndValid G Φ) A

/-- The query that the `obv.sim` simulator built from an inverter `M` garbles: the function that
`M` produces from `φ`, on the all-zero input. -/
def obvInverterQuery (G : Scheme Fn) (M : Λ → Fn) (φ : Λ) : Query Fn :=
  ⟨M φ, List.replicate (G.inLen (M φ)) false⟩

/-- The `obv.sim` simulator built from an inverter `M` of the side information
([BellareHoangRogaway2012], Section 4.3): the real view of the function that `M` produces from
`Φ(f)` on the all-zero input. -/
noncomputable def obvSimFromInverter (G : Scheme Fn) (k : ℕ) (M : Λ → Fn) : ObvSimulator Λ :=
  fun φ => G.obvView k (obvInverterQuery G M φ)

/-- The `obv.ind` adversary built from an `obv.sim` adversary `B` and an inverter `M` of the
side information ([BellareHoangRogaway2012], Proposition 3): it queries the pair of `M(Φ(f))` on
the all-zero input and the query `(f, x)` of `B`, and guesses as `B` does. -/
def obvSimToInd (G : Scheme Fn) (Φ : SideInfo Fn Λ) (M : Λ → Fn) (B : ObvSimAdversary Fn σ) :
    ObvIndAdversary Fn σ :=
  simToInd (fun q => obvInverterQuery G M (Φ.phi q.fn)) B

/-! ## The shared analysis

The experiments of `PrvInd` and `ObvInd`, and of `PrvSim` and `ObvSim`, differ only in the view
type, the validity predicate of the pairs, the real view of a query and the simulated view of a
query. The experiments `indExperiment` and `simExperiment` take these as parameters, and each
`prv` and `obv` experiment unfolds to one of them, so the reductions are analysed once. -/

section Shared

variable {V : Type} (G : Scheme Fn) (valid : MessagePair (Query Fn) → Prop) [DecidablePred valid]
  (real : Query Fn → ProbComp V)

/-- The indistinguishability experiment `b` with validity predicate `valid` and real view `real`:
the shape of `prvIndExperiment` and `obvIndExperiment`. -/
private noncomputable def indExperiment
    (A : TwoStage Unit (MessagePair (Query Fn)) (Option V) Bool σ) (b : Bool) : Experiment := do
  let (pair, st) ← A.choose ()
  if valid pair then
    let view ← real (pair.select b)
    A.guess st (some view)
  else
    A.guess st none

/-- The simulation experiment `b` with real view `real` and simulated view `sim`: the shape of
`prvSimExperiment` and `obvSimExperiment`. -/
private noncomputable def simExperiment (sim : Query Fn → ProbComp V)
    (B : TwoStage Unit (Query Fn) (Option V) Bool σ) (b : Bool) : Experiment := do
  let (q, st) ← B.choose ()
  if q.input.length = G.inLen q.fn then
    let view ← if b then real q else sim q
    B.guess st (some view)
  else
    B.guess st none

/-- Against a simulated view that is the same for both queries of a valid pair, the reduction
`indToSim` outputs a fair coin. -/
private theorem eval_simExperiment_false_indToSim (sim : Query Fn → ProbComp V)
    (hvalid : ∀ pair, valid pair → pair.msg₀.input.length = G.inLen pair.msg₀.fn ∧
      pair.msg₁.input.length = G.inLen pair.msg₁.fn ∧ sim pair.msg₀ = sim pair.msg₁)
    (A : TwoStage Unit (MessagePair (Query Fn)) (Option V) Bool σ) :
    ProbComp.eval (simExperiment G real sim (indToSim valid A) false) =
      PMF.uniformOfFintype Bool := by
  simp only [simExperiment, indToSim, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine ((PMF.bind_const (ProbComp.eval (A.choose ())) _).symm.trans ?_).symm
  congr 1 with ⟨pair, st⟩ : 1
  by_cases hV : valid pair
  · obtain ⟨hx₀, hx₁, hsim⟩ := hvalid pair hV
    refine (Game.uniform_bool_bind_map_beq_const ((ProbComp.eval (sim pair.msg₁)).bind
      fun view => ProbComp.eval (A.guess st (some view)))).symm.trans ?_
    congr 1 with c : 1
    cases c <;> simp [hV, hx₀, hx₁, hsim, ProbComp.eval_bind, PMF.map, Function.comp_def]
  · refine (Game.uniform_bool_bind_map_beq_const (ProbComp.eval (A.guess st none))).symm.trans ?_
    congr 1 with c : 1
    by_cases hx₀ : pair.msg₀.input.length = G.inLen pair.msg₀.fn <;>
      simp [hV, hx₀, ProbComp.eval_bind, PMF.bind_const, PMF.map, Function.comp_def]

/-- Against the real view, the reduction `indToSim` plays the bit-guessing form of the
indistinguishability experiment with `A`. -/
private theorem eval_simExperiment_true_indToSim (sim : Query Fn → ProbComp V)
    (hvalid : ∀ pair, valid pair → pair.msg₀.input.length = G.inLen pair.msg₀.fn ∧
      pair.msg₁.input.length = G.inLen pair.msg₁.fn ∧ sim pair.msg₀ = sim pair.msg₁)
    (A : TwoStage Unit (MessagePair (Query Fn)) (Option V) Bool σ) :
    ProbComp.eval (simExperiment G real sim (indToSim valid A) true) =
      ProbComp.eval (Experiment.guessBit (indExperiment valid real A)) := by
  rw [Experiment.eval_guessBit]
  simp only [simExperiment, indToSim, indExperiment, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind]
  pmf_swap with c
  congr 1 with ⟨pair, st⟩ : 1
  by_cases hV : valid pair
  · obtain ⟨hx₀, hx₁, -⟩ := hvalid pair hV
    cases c <;> simp [hV, hx₀, hx₁, ProbComp.eval_bind, PMF.map, Function.comp_def]
  · by_cases hx₀ : pair.msg₀.input.length = G.inLen pair.msg₀.fn <;>
      simp [hV, hx₀, ProbComp.eval_bind, PMF.bind_const, PMF.map, Function.comp_def]

/-- The indistinguishability advantage of `A` is twice the simulation advantage of `indToSim A`
against a simulated view that is the same for both queries of a valid pair. -/
private theorem advantage_indExperiment_eq_two_mul_advantage_simExperiment_indToSim
    (sim : Query Fn → ProbComp V)
    (hvalid : ∀ pair, valid pair → pair.msg₀.input.length = G.inLen pair.msg₀.fn ∧
      pair.msg₁.input.length = G.inLen pair.msg₁.fn ∧ sim pair.msg₀ = sim pair.msg₁)
    (A : TwoStage Unit (MessagePair (Query Fn)) (Option V) Bool σ) :
    Experiment.advantage (indExperiment valid real A false) (indExperiment valid real A true) =
      2 * Experiment.advantage (simExperiment G real sim (indToSim valid A) false)
        (simExperiment G real sim (indToSim valid A) true) := by
  rw [Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit (indExperiment valid real A),
    Experiment.advantage, eval_simExperiment_false_indToSim G valid real sim hvalid A,
    eval_simExperiment_true_indToSim G valid real sim hvalid A, Game.advantage_comm]

/-- Against the simulated view that is the real view of `inv q`, the simulation experiment on `B`
is the indistinguishability experiment on `simToInd inv B`, when the pair of `inv q` and `q` is
valid exactly when `q` has the right input length. -/
private theorem eval_simExperiment_eq_eval_indExperiment_simToInd (inv : Query Fn → Query Fn)
    (hvalid : ∀ q, valid ⟨inv q, q⟩ ↔ q.input.length = G.inLen q.fn)
    (B : TwoStage Unit (Query Fn) (Option V) Bool σ) (b : Bool) :
    ProbComp.eval (simExperiment G real (fun q => real (inv q)) B b) =
      ProbComp.eval (indExperiment valid real (simToInd inv B) b) := by
  simp only [simExperiment, indExperiment, simToInd, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.bind_bind, PMF.pure_bind]
  congr 1 with ⟨q, st⟩ : 1
  by_cases hx : q.input.length = G.inLen q.fn
  · cases b <;> simp [hx, (hvalid q).mpr hx]
  · simp [hx, mt (hvalid q).mp hx]

end Shared

/-! ## Privacy -/

section Privacy

variable (G : Scheme Fn) (Φ : SideInfo Fn Λ) [DecidableEq Λ]

/-- The `prv.ind` advantage of `A` is twice the `prv.sim` advantage of the reduction
`prvIndToSim` against every simulator ([BellareHoangRogaway2012], Proposition 2). -/
theorem prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim (hCompat : Φ.Compatible G) (k : ℕ)
    (S : PrvSimulator Λ) (A : PrvIndAdversary Fn σ) :
    prvIndAdvantage G Φ k A = 2 * prvSimAdvantage G Φ k S (prvIndToSim G Φ A) :=
  advantage_indExperiment_eq_two_mul_advantage_simExperiment_indToSim G (prvIndValid G Φ)
    (G.prvView k) (fun q => S (G.ev q.fn q.input) (Φ.phi q.fn))
    (fun _ ⟨hphi, hx₀, hx₁, hev⟩ =>
      ⟨hx₀, hx₁.trans (hCompat.inLen_eq hphi), by simp only [hev, hphi]⟩) A

/-- Simulation privacy implies indistinguishability privacy with a factor of two
([BellareHoangRogaway2012], Proposition 2). -/
theorem prvIndAdvantage_le_two_mul_prvSimAdvantage_prvIndToSim (hCompat : Φ.Compatible G) (k : ℕ)
    (S : PrvSimulator Λ) (A : PrvIndAdversary Fn σ) :
    prvIndAdvantage G Φ k A ≤ 2 * prvSimAdvantage G Φ k S (prvIndToSim G Φ A) :=
  (prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim G Φ hCompat k S A).le

/-- Against the simulator built from an `ev`-inverter `M`, the `prv.sim` game on `B` is the
`prv.ind` game on the reduction `prvSimToInd`. -/
theorem eval_prvSimExperiment_prvSimFromInverter (hCompat : Φ.Compatible G)
    {M : Λ → List Bool → Query Fn} (hInv : Φ.IsEvInverter G M) (k : ℕ) (B : PrvSimAdversary Fn σ)
    (b : Bool) :
    ProbComp.eval (prvSimExperiment G Φ k (prvSimFromInverter G k M) B b) =
      ProbComp.eval (prvIndExperiment G Φ k (prvSimToInd G Φ M B) b) :=
  eval_simExperiment_eq_eval_indExperiment_simToInd G (prvIndValid G Φ) (G.prvView k)
    (fun q => M (Φ.phi q.fn) (G.ev q.fn q.input)) (fun q => by
      constructor
      · rintro ⟨hphi, -, hx, -⟩
        exact hx.trans (hCompat.inLen_eq hphi)
      · intro hx
        obtain ⟨hphi, hx₀, hev⟩ := hInv q.fn q.input hx
        exact ⟨hphi, hx₀, hx.trans (hCompat.inLen_eq hphi.symm), hev⟩) B b

/-- Against the simulator built from an `ev`-inverter `M`, the `prv.sim` advantage of `B` is the
`prv.ind` advantage of the reduction `prvSimToInd` ([BellareHoangRogaway2012],
Proposition 2). -/
theorem prvSimAdvantage_prvSimFromInverter_eq (hCompat : Φ.Compatible G)
    {M : Λ → List Bool → Query Fn} (hInv : Φ.IsEvInverter G M) (k : ℕ)
    (B : PrvSimAdversary Fn σ) :
    prvSimAdvantage G Φ k (prvSimFromInverter G k M) B =
      prvIndAdvantage G Φ k (prvSimToInd G Φ M B) := by
  simp only [prvSimAdvantage, prvIndAdvantage, Experiment.advantage,
    eval_prvSimExperiment_prvSimFromInverter G Φ hCompat hInv]

/-- Indistinguishability privacy implies simulation privacy for side information with an
`ev`-inverter ([BellareHoangRogaway2012], Proposition 2). -/
theorem prvSimAdvantage_prvSimFromInverter_le (hCompat : Φ.Compatible G)
    {M : Λ → List Bool → Query Fn} (hInv : Φ.IsEvInverter G M) (k : ℕ)
    (B : PrvSimAdversary Fn σ) :
    prvSimAdvantage G Φ k (prvSimFromInverter G k M) B ≤
      prvIndAdvantage G Φ k (prvSimToInd G Φ M B) :=
  (prvSimAdvantage_prvSimFromInverter_eq G Φ hCompat hInv k B).le

end Privacy

/-! ## Obliviousness -/

section Obliviousness

variable (G : Scheme Fn) (Φ : SideInfo Fn Λ) [DecidableEq Λ]

/-- The `obv.ind` advantage of `A` is twice the `obv.sim` advantage of the reduction
`obvIndToSim` against every simulator ([BellareHoangRogaway2012], Proposition 3). -/
theorem obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim (hCompat : Φ.Compatible G) (k : ℕ)
    (S : ObvSimulator Λ) (A : ObvIndAdversary Fn σ) :
    obvIndAdvantage G Φ k A = 2 * obvSimAdvantage G Φ k S (obvIndToSim G Φ A) :=
  advantage_indExperiment_eq_two_mul_advantage_simExperiment_indToSim G (obvIndValid G Φ)
    (G.obvView k) (fun q => S (Φ.phi q.fn))
    (fun _ ⟨hphi, hx₀, hx₁⟩ => ⟨hx₀, hx₁.trans (hCompat.inLen_eq hphi), by simp only [hphi]⟩) A

/-- Simulation obliviousness implies indistinguishability obliviousness with a factor of two
([BellareHoangRogaway2012], Proposition 3). -/
theorem obvIndAdvantage_le_two_mul_obvSimAdvantage_obvIndToSim (hCompat : Φ.Compatible G) (k : ℕ)
    (S : ObvSimulator Λ) (A : ObvIndAdversary Fn σ) :
    obvIndAdvantage G Φ k A ≤ 2 * obvSimAdvantage G Φ k S (obvIndToSim G Φ A) :=
  (obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim G Φ hCompat k S A).le

/-- Against the simulator built from an inverter `M` of the side information, the `obv.sim`
game on `B` is the `obv.ind` game on the reduction `obvSimToInd`. -/
theorem eval_obvSimExperiment_obvSimFromInverter (hCompat : Φ.Compatible G) {M : Λ → Fn}
    (hInv : Φ.IsInverter M) (k : ℕ) (B : ObvSimAdversary Fn σ) (b : Bool) :
    ProbComp.eval (obvSimExperiment G Φ k (obvSimFromInverter G k M) B b) =
      ProbComp.eval (obvIndExperiment G Φ k (obvSimToInd G Φ M B) b) :=
  eval_simExperiment_eq_eval_indExperiment_simToInd G (obvIndValid G Φ) (G.obvView k)
    (fun q => obvInverterQuery G M (Φ.phi q.fn)) (fun q => by
      constructor
      · rintro ⟨hphi, -, hx⟩
        exact hx.trans (hCompat.inLen_eq hphi)
      · intro hx
        exact ⟨hInv q.fn, List.length_replicate, hx.trans (hCompat.inLen_eq (hInv q.fn).symm)⟩)
    B b

/-- Against the simulator built from an inverter `M` of the side information, the `obv.sim`
advantage of `B` is the `obv.ind` advantage of the reduction `obvSimToInd`
([BellareHoangRogaway2012], Proposition 3). -/
theorem obvSimAdvantage_obvSimFromInverter_eq (hCompat : Φ.Compatible G) {M : Λ → Fn}
    (hInv : Φ.IsInverter M) (k : ℕ) (B : ObvSimAdversary Fn σ) :
    obvSimAdvantage G Φ k (obvSimFromInverter G k M) B =
      obvIndAdvantage G Φ k (obvSimToInd G Φ M B) := by
  simp only [obvSimAdvantage, obvIndAdvantage, Experiment.advantage,
    eval_obvSimExperiment_obvSimFromInverter G Φ hCompat hInv]

/-- Indistinguishability obliviousness implies simulation obliviousness for invertible side
information ([BellareHoangRogaway2012], Proposition 3). -/
theorem obvSimAdvantage_obvSimFromInverter_le (hCompat : Φ.Compatible G) {M : Λ → Fn}
    (hInv : Φ.IsInverter M) (k : ℕ) (B : ObvSimAdversary Fn σ) :
    obvSimAdvantage G Φ k (obvSimFromInverter G k M) B ≤
      obvIndAdvantage G Φ k (obvSimToInd G Φ M B) :=
  (obvSimAdvantage_obvSimFromInverter_eq G Φ hCompat hInv k B).le

end Obliviousness

end Cslib.Crypto.Garbling
