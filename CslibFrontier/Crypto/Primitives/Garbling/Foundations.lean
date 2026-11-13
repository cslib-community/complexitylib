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
`obv.ind` and `obv.sim`, with an inverter of `Φ` in place of an `ev`-inverter.

## Main definitions

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

/-- The `prv.sim` adversary built from a `prv.ind` adversary `A` ([BellareHoangRogaway2012],
Proposition 2): it picks a hidden bit `c`, submits the query `c` of the pair of `A` when the pair is
valid and the query `0` otherwise, and outputs whether `A` recovers `c`. -/
noncomputable def prvIndToSim [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (A : PrvIndAdversary Fn σ) : PrvSimAdversary Fn (IndToSimState Fn σ) where
  choose _ := do
    let (pair, st) ← A.choose ()
    let c ← ProbComp.uniform Bool
    pure (if prvIndValid G Φ pair then pair.select c else pair.msg₀, ⟨st, c, pair⟩)
  guess s view := do
    let guess ← A.guess s.state (if prvIndValid G Φ s.pair then view else none)
    pure (guess == s.bit)

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
    (B : PrvSimAdversary Fn σ) : PrvIndAdversary Fn σ where
  choose _ := do
    let (q, st) ← B.choose ()
    pure (⟨M (Φ.phi q.fn) (G.ev q.fn q.input), q⟩, st)
  guess := B.guess

/-- The `obv.sim` adversary built from an `obv.ind` adversary `A` ([BellareHoangRogaway2012],
Proposition 3): it picks a hidden bit `c`, submits the query `c` of the pair of `A` when the pair is
valid and the query `0` otherwise, and outputs whether `A` recovers `c`. -/
noncomputable def obvIndToSim [DecidableEq Λ] (G : Scheme Fn) (Φ : SideInfo Fn Λ)
    (A : ObvIndAdversary Fn σ) : ObvSimAdversary Fn (IndToSimState Fn σ) where
  choose _ := do
    let (pair, st) ← A.choose ()
    let c ← ProbComp.uniform Bool
    pure (if obvIndValid G Φ pair then pair.select c else pair.msg₀, ⟨st, c, pair⟩)
  guess s view := do
    let guess ← A.guess s.state (if obvIndValid G Φ s.pair then view else none)
    pure (guess == s.bit)

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
    ObvIndAdversary Fn σ where
  choose _ := do
    let (q, st) ← B.choose ()
    pure (⟨obvInverterQuery G M (Φ.phi q.fn), q⟩, st)
  guess := B.guess

/-! ## Privacy -/

section Privacy

variable (G : Scheme Fn) (Φ : SideInfo Fn Λ) [DecidableEq Λ]

/-- Against any simulator, the reduction `prvIndToSim` outputs a fair coin: the simulator's view
does not depend on the hidden bit. -/
private theorem eval_prvSimExperiment_false_prvIndToSim (hCompat : Φ.Compatible G) (k : ℕ)
    (S : PrvSimulator Λ) (A : PrvIndAdversary Fn σ) :
    ProbComp.eval (prvSimExperiment G Φ k S (prvIndToSim G Φ A) false) =
      PMF.uniformOfFintype Bool := by
  simp only [prvSimExperiment, prvIndToSim, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine ((PMF.bind_const (ProbComp.eval (A.choose ())) _).symm.trans ?_).symm
  congr 1 with ⟨pair, st⟩ : 1
  by_cases hV : prvIndValid G Φ pair
  · have ⟨hphi, hx₀, hx₁, hev⟩ := hV
    have hlen₁ : pair.msg₁.input.length = G.inLen pair.msg₁.fn :=
      hx₁.trans (hCompat.inLen_eq hphi)
    refine (Game.uniform_bool_bind_map_beq_const ((ProbComp.eval (S (G.ev pair.msg₁.fn
      pair.msg₁.input) (Φ.phi pair.msg₁.fn))).bind fun view =>
        ProbComp.eval (A.guess st (some view)))).symm.trans ?_
    congr 1 with c : 1
    cases c <;> simp [hV, hx₀, hlen₁, hphi, hev, ProbComp.eval_bind, PMF.map,
      Function.comp_def]
  · refine (Game.uniform_bool_bind_map_beq_const (ProbComp.eval (A.guess st none))).symm.trans ?_
    congr 1 with c : 1
    by_cases hx₀ : pair.msg₀.input.length = G.inLen pair.msg₀.fn <;>
      simp [hV, hx₀, ProbComp.eval_bind, PMF.bind_const, PMF.map, Function.comp_def]

/-- Against the real garbling, the reduction `prvIndToSim` plays the bit-guessing form of
`PrvInd` with `A`. -/
private theorem eval_prvSimExperiment_true_prvIndToSim (hCompat : Φ.Compatible G) (k : ℕ)
    (S : PrvSimulator Λ) (A : PrvIndAdversary Fn σ) :
    ProbComp.eval (prvSimExperiment G Φ k S (prvIndToSim G Φ A) true) =
      ProbComp.eval (Experiment.guessBit (prvIndExperiment G Φ k A)) := by
  rw [Experiment.eval_guessBit]
  simp only [prvSimExperiment, prvIndToSim, prvIndExperiment, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind]
  pmf_swap with c
  congr 1 with ⟨pair, st⟩ : 1
  by_cases hV : prvIndValid G Φ pair
  · have ⟨hphi, hx₀, hx₁, hev⟩ := hV
    have hlen₁ : pair.msg₁.input.length = G.inLen pair.msg₁.fn :=
      hx₁.trans (hCompat.inLen_eq hphi)
    cases c <;> simp [hV, hx₀, hlen₁, ProbComp.eval_bind, PMF.map,
      Function.comp_def]
  · by_cases hx₀ : pair.msg₀.input.length = G.inLen pair.msg₀.fn <;>
      simp [hV, hx₀, ProbComp.eval_bind, PMF.bind_const, PMF.map, Function.comp_def]

/-- The `prv.ind` advantage of `A` is twice the `prv.sim` advantage of the reduction
`prvIndToSim` against every simulator ([BellareHoangRogaway2012], Proposition 2). -/
theorem prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim (hCompat : Φ.Compatible G) (k : ℕ)
    (S : PrvSimulator Λ) (A : PrvIndAdversary Fn σ) :
    prvIndAdvantage G Φ k A = 2 * prvSimAdvantage G Φ k S (prvIndToSim G Φ A) := by
  rw [prvIndAdvantage_eq_two_mul_guessingAdvantage, prvSimAdvantage, Experiment.advantage,
    eval_prvSimExperiment_false_prvIndToSim G Φ hCompat k S A,
    eval_prvSimExperiment_true_prvIndToSim G Φ hCompat k S A, Game.advantage_comm]

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
      ProbComp.eval (prvIndExperiment G Φ k (prvSimToInd G Φ M B) b) := by
  simp only [prvSimExperiment, prvIndExperiment, prvSimFromInverter, prvSimToInd,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1 with ⟨q, st⟩ : 1
  have hvalid_iff :
      prvIndValid G Φ ⟨M (Φ.phi q.fn) (G.ev q.fn q.input), q⟩ ↔ q.input.length = G.inLen q.fn := by
    constructor
    · rintro ⟨hphi, -, hx, -⟩
      exact hx.trans (hCompat.inLen_eq hphi)
    · intro hx
      obtain ⟨hphi, hx₀, hev⟩ := hInv q.fn q.input hx
      exact ⟨hphi, hx₀, hx.trans (hCompat.inLen_eq hphi.symm), hev⟩
  by_cases hx : q.input.length = G.inLen q.fn
  · cases b <;> simp [hx, hvalid_iff.mpr hx]
  · simp [hx, mt hvalid_iff.mp hx]

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

/-- Against any simulator, the reduction `obvIndToSim` outputs a fair coin: the simulator's view
does not depend on the hidden bit. -/
private theorem eval_obvSimExperiment_false_obvIndToSim (hCompat : Φ.Compatible G) (k : ℕ)
    (S : ObvSimulator Λ) (A : ObvIndAdversary Fn σ) :
    ProbComp.eval (obvSimExperiment G Φ k S (obvIndToSim G Φ A) false) =
      PMF.uniformOfFintype Bool := by
  simp only [obvSimExperiment, obvIndToSim, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  refine ((PMF.bind_const (ProbComp.eval (A.choose ())) _).symm.trans ?_).symm
  congr 1 with ⟨pair, st⟩ : 1
  by_cases hV : obvIndValid G Φ pair
  · have ⟨hphi, hx₀, hx₁⟩ := hV
    have hlen₁ : pair.msg₁.input.length = G.inLen pair.msg₁.fn :=
      hx₁.trans (hCompat.inLen_eq hphi)
    refine (Game.uniform_bool_bind_map_beq_const ((ProbComp.eval (S (Φ.phi pair.msg₁.fn))).bind
      fun view => ProbComp.eval (A.guess st (some view)))).symm.trans ?_
    congr 1 with c : 1
    cases c <;> simp [hV, hx₀, hlen₁, hphi, ProbComp.eval_bind, PMF.map,
      Function.comp_def]
  · refine (Game.uniform_bool_bind_map_beq_const (ProbComp.eval (A.guess st none))).symm.trans ?_
    congr 1 with c : 1
    by_cases hx₀ : pair.msg₀.input.length = G.inLen pair.msg₀.fn <;>
      simp [hV, hx₀, ProbComp.eval_bind, PMF.bind_const, PMF.map, Function.comp_def]

/-- Against the real garbling, the reduction `obvIndToSim` plays the bit-guessing form of
`ObvInd` with `A`. -/
private theorem eval_obvSimExperiment_true_obvIndToSim (hCompat : Φ.Compatible G) (k : ℕ)
    (S : ObvSimulator Λ) (A : ObvIndAdversary Fn σ) :
    ProbComp.eval (obvSimExperiment G Φ k S (obvIndToSim G Φ A) true) =
      ProbComp.eval (Experiment.guessBit (obvIndExperiment G Φ k A)) := by
  rw [Experiment.eval_guessBit]
  simp only [obvSimExperiment, obvIndToSim, obvIndExperiment, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind]
  pmf_swap with c
  congr 1 with ⟨pair, st⟩ : 1
  by_cases hV : obvIndValid G Φ pair
  · have ⟨hphi, hx₀, hx₁⟩ := hV
    have hlen₁ : pair.msg₁.input.length = G.inLen pair.msg₁.fn :=
      hx₁.trans (hCompat.inLen_eq hphi)
    cases c <;> simp [hV, hx₀, hlen₁, ProbComp.eval_bind, PMF.map,
      Function.comp_def]
  · by_cases hx₀ : pair.msg₀.input.length = G.inLen pair.msg₀.fn <;>
      simp [hV, hx₀, ProbComp.eval_bind, PMF.bind_const, PMF.map, Function.comp_def]

/-- The `obv.ind` advantage of `A` is twice the `obv.sim` advantage of the reduction
`obvIndToSim` against every simulator ([BellareHoangRogaway2012], Proposition 3). -/
theorem obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim (hCompat : Φ.Compatible G) (k : ℕ)
    (S : ObvSimulator Λ) (A : ObvIndAdversary Fn σ) :
    obvIndAdvantage G Φ k A = 2 * obvSimAdvantage G Φ k S (obvIndToSim G Φ A) := by
  rw [obvIndAdvantage, Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit
      (obvIndExperiment G Φ k A), obvSimAdvantage, Experiment.advantage,
    eval_obvSimExperiment_false_obvIndToSim G Φ hCompat k S A,
    eval_obvSimExperiment_true_obvIndToSim G Φ hCompat k S A, Game.advantage_comm]

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
      ProbComp.eval (obvIndExperiment G Φ k (obvSimToInd G Φ M B) b) := by
  simp only [obvSimExperiment, obvIndExperiment, obvSimFromInverter, obvSimToInd,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  congr 1 with ⟨q, st⟩ : 1
  have hvalid_iff :
      obvIndValid G Φ ⟨obvInverterQuery G M (Φ.phi q.fn), q⟩ ↔ q.input.length = G.inLen q.fn := by
    constructor
    · rintro ⟨hphi, -, hx⟩
      exact hx.trans (hCompat.inLen_eq hphi)
    · intro hx
      exact ⟨hInv q.fn, List.length_replicate, hx.trans (hCompat.inLen_eq (hInv q.fn).symm)⟩
  by_cases hx : q.input.length = G.inLen q.fn
  · cases b <;> simp [hx, hvalid_iff.mpr hx]
  · simp [hx, mt hvalid_iff.mp hx]

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
