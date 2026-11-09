/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game
public import Complexity.Crypto.Primitives.Garbling.Switch.Garble
public import Complexity.Languages.Probabilistic.Oracle.QueryCount

/-!
# Obliviousness of garbled switch systems from circular correlation robustness

The evaluator of a garbled switch system (`Garbling.Switch.Garble`) sees a `SwitchView`: the gate
material and the input labels. Heath [Heath2024] proves this view simulatable from circular
correlation robustness of the hash. This file proves the core of that argument: the view on an
input reveals nothing beyond the *control bits*, whether each switch is open. The simulator
`simulate` receives the system and one control bit per gate (`SwitchSystem.controls`), samples
uniform input labels, and recomputes the labels gate by gate: affine gates and closed switches as
the evaluator would, and the output of each open switch as its source label plus a fresh uniform
label. It never uses the input, the affine constants or the offset `Δ`.

**Circular correlation robustness** (`CCR`), in the style of Choi et al.
[ChoiKatzKumaresanZhou2012]: the oracle keyed by a uniform offset `Δ` of colour `1` answers
`(k, t, s)` with `H (k - Δ) t + s • Δ` (`CCR.oracle`). It must be indistinguishable from an
oracle answering every query with a fresh uniform label, for adversaries that never repeat a
tweak (`CCR.IsTweakUnique`); for such adversaries the fresh oracle is, by inspection, a random
function of the query (this equivalence is not formalized).

This is an arithmetic variant of the assumption Heath uses, which is the Boolean circular
correlation robustness of Zahur, Rosulek and Evans [ZahurRosulekEvans2015]: there labels are bit
strings, the oracle answers `H (k ⊕ Δ) t ⊕ b • Δ` for a bit `b`, and the adversary must not ask
the same `(k, t)` with different bits. Here labels lie in an `R`-module, the shift `s` ranges
over `R`, and the adversary must not repeat a tweak at all; no implication in either direction
between the two assumptions is formalized. Control wires are `R`-valued with full-width labels,
whereas Heath's control wires carry `ℤ_2` values with Boolean labels.

**Main theorem** (`advantage_realGame_simGame`). For a well-formed system `S`, an assignment `σ`
satisfying `S` on input `x`, and every distinguisher `D` of views, the advantage of `D` between the
real view and the simulated view with the control bits of `σ` *equals* the CCR advantage of the
explicit reduction `reduction S H col σ D`, which never repeats a tweak
(`isTweakUnique_reduction`). The reduction knows `σ`. It samples uniform input labels for the
values of `σ` and, gate by gate, computes the active label of each wire, the label of its value
under `σ`. A closed switch has control label `K ctrl`, so the reduction hashes it directly. An open
switch has control label `K ctrl + Δ`, and its source and output labels differ by
`H (K ctrl) i + (σ out - σ src) • Δ`, the oracle's answer to
`(control label, i, σ out - σ src)`.
With the keyed oracle the reduction outputs the real view exactly; with the fresh oracle it
outputs the simulated view.

This is the single-instance form: the system, input and distinguisher are fixed and the simulator
is given the control bits. Heath's obliviousness theorem also simulates the control bits, for
randomized switch systems whose control bits are close to a fixed distribution, and adds the
statistical distance of that simulation; that step, and the transfer to adversaries choosing the
system and input, are not formalized here. Running time is not tracked.

## Main definitions

* `Cslib.Crypto.Garbling.CCR.oracle`, `Cslib.Crypto.Garbling.CCR.advantage`: circular
  correlation robustness.
* `Cslib.Crypto.Garbling.Switch.SwitchView`: what the evaluator sees.
* `Cslib.Crypto.Garbling.Switch.simulate`: the simulator from control bits.
* `Cslib.Crypto.Garbling.Switch.reduction`: the CCR adversary.

## Main results

* `Cslib.Crypto.Garbling.Switch.isTweakUnique_reduction`: the reduction never repeats a tweak.
* `Cslib.Crypto.Garbling.Switch.advantage_realGame_simGame`: the view is simulatable from the
  control bits, with advantage the CCR advantage of the reduction.

## References

* [D. Heath, *Efficient Arithmetic in Garbled Circuits*][Heath2024]
* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole*][ZahurRosulekEvans2015]
* [S. G. Choi, J. Katz, R. Kumaresan, H.-S. Zhou, *On the Security of the "Free-XOR"
  Technique*][ChoiKatzKumaresanZhou2012]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling

open SwitchGate Probability

variable {n m N : ℕ} {R L : Type} [CommRing R] [AddCommGroup L] [Module R L]

/-! ### Circular correlation robustness -/

namespace CCR

/-- The oracle keyed by the offset `Δ`: query `(k, t, s)` is answered by
`H (k - Δ) t + s • Δ`. -/
def oracle (H : L → ℕ → L) (Δ : L) (q : L × ℕ × R) : L :=
  H (q.1 - Δ) q.2.1 + q.2.2 • Δ

/-- A CCR adversary: a test with private coins and oracle access to queries `(k, t, s)`. -/
abbrev Adversary (R L : Type) := ProbOracleComp (fun _ : L × ℕ × R => L) Bool

/-- The keyed experiment: sample a uniform offset of colour `1` and answer with `oracle`. -/
noncomputable def realGame (H : L → ℕ → L) (col : L →+ ZMod 2) [Fintype L]
    [Nonempty {Δ : L // col Δ = 1}] (adversary : Adversary R L) : Game :=
  ProbComp.eval do
    let Δ ← ProbComp.uniform {Δ : L // col Δ = 1}
    OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifFin fun q => pure (oracle H Δ.1 q)) adversary

/-- The ideal experiment: answer every query with a fresh uniform label. -/
noncomputable def idealGame [Fintype L] (adversary : Adversary R L) : Game :=
  ProbComp.eval
    (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin fun _ => ProbComp.uniform L)
      adversary)

/-- The CCR advantage of `adversary` against `H`. The assumption that it is small is meant only for
adversaries that never repeat a tweak (`IsTweakUnique`): repeating a query distinguishes the fresh
oracle from the keyed one. -/
noncomputable abbrev advantage (H : L → ℕ → L) (col : L →+ ZMod 2) [Fintype L]
    [Nonempty {Δ : L // col Δ = 1}] (adversary : Adversary R L) : NNReal :=
  Game.advantage (realGame H col adversary) (idealGame adversary)

/-- The adversary never repeats a tweak: on every path it makes at most one query with each
tweak `t`. -/
def IsTweakUnique (adversary : Adversary R L) : Prop :=
  ∀ t : ℕ, OracleComp.IsCostBounded
    (Sum.elim (fun _ => 0) fun q : L × ℕ × R => if q.2.1 = t then 1 else 0) adversary 1

end CCR

namespace Switch

/-! ### Views, the real game and the simulator -/

/-- What the evaluator of a garbled switch system sees: the gate material and the input
labels. -/
structure SwitchView (L : Type) (n : ℕ) where
  /-- The material of each gate, in order. -/
  material : List (Material L)
  /-- The label of each input wire. -/
  input : Fin n → L

/-- The real experiment: garble `S`, give `D` the material and the input labels of `x`. -/
noncomputable def realGame (S : SwitchSystem n m N R) (H : L → ℕ → L) (col : L →+ ZMod 2)
    [Fintype L] [Nonempty {Δ : L // col Δ = 1}] (x : Fin n → R)
    (D : SwitchView L n → ProbComp Bool) : Game :=
  ProbComp.eval do
    let G ← garble S H col
    D ⟨G.material, G.encode x⟩

/-- Simulate the gate at position `i` with control bit `b`, given the labels so far. -/
noncomputable def simGate [Fintype L] (H : L → ℕ → L) (col : L →+ ZMod 2) (i : ℕ)
    (A : Fin n ⊕ Fin N → L) : SwitchGate n N R → Bool →
      ProbComp (Material L × (Fin n ⊕ Fin N → L))
  | affine terms _ y, _ => pure (.none, Function.update A (.inr y) (termSum A terms))
  | switch x y c, false =>
    pure (.colour (col (A c)), Function.update A (.inr y) (A x + H (A c) i))
  | switch x y c, true => do
    let r ← ProbComp.uniform L
    return (.colour (col (A c) + 1), Function.update A (.inr y) (A x + r))
  | join x y, _ => pure (.shift (A y - A x), A)

/-- Simulate the gates `gs` with their control bits, the first at position `i`. -/
noncomputable def simGates [Fintype L] (H : L → ℕ → L) (col : L →+ ZMod 2) :
    ℕ → List (SwitchGate n N R) → List Bool → (Fin n ⊕ Fin N → L) →
      ProbComp (List (Material L))
  | i, g :: gs, b :: bs, A => do
    let p ← simGate H col i A g b
    let μs ← simGates H col (i + 1) gs bs p.2
    return p.1 :: μs
  | _, _, _, _ => pure []

/-- The simulator: sample uniform input labels and simulate the gates with the control bits
`ctrl`. -/
noncomputable def simulate [Fintype L] (S : SwitchSystem n m N R) (H : L → ℕ → L)
    (col : L →+ ZMod 2) (ctrl : List Bool) : ProbComp (SwitchView L n) := do
  let X ← ProbComp.uniform (Fin n → L)
  let μs ← simGates H col 0 S.gates ctrl (Sum.elim X 0)
  return ⟨μs, X⟩

/-- The simulated experiment with control bits `ctrl`. -/
noncomputable def simGame [Fintype L] (S : SwitchSystem n m N R) (H : L → ℕ → L)
    (col : L →+ ZMod 2) (ctrl : List Bool) (D : SwitchView L n → ProbComp Bool) : Game :=
  ProbComp.eval do
    let V ← simulate S H col ctrl
    D V

/-! ### The reduction -/

/-- The reduction's step at gate position `i`, given the active labels so far: an open switch
asks the oracle for the difference of its source and output labels. -/
def reduceGate [DecidableEq R] (H : L → ℕ → L) (col : L →+ ZMod 2)
    (σ : Fin n ⊕ Fin N → R) (i : ℕ) (A : Fin n ⊕ Fin N → L) : SwitchGate n N R →
      ProbOracleComp (fun _ : L × ℕ × R => L) (Material L × (Fin n ⊕ Fin N → L))
  | affine terms _ y => pure (.none, Function.update A (.inr y) (termSum A terms))
  | switch x y c =>
    if σ c = 0 then pure (.colour (col (A c)), Function.update A (.inr y) (A x + H (A c) i))
    else do
      let r ← ProbOracleComp.query (A c, i, σ (.inr y) - σ x)
      return (.colour (col (A c) + 1), Function.update A (.inr y) (A x + r))
  | join x y => pure (.shift (A y - A x), A)

/-- The reduction's steps through the gates `gs`, the first at position `i`. -/
def reduceGates [DecidableEq R] (H : L → ℕ → L) (col : L →+ ZMod 2)
    (σ : Fin n ⊕ Fin N → R) :
    ℕ → List (SwitchGate n N R) → (Fin n ⊕ Fin N → L) →
      ProbOracleComp (fun _ : L × ℕ × R => L) (List (Material L))
  | _, [], _ => pure []
  | i, g :: gs, A => do
    let p ← reduceGate H col σ i A g
    let μs ← reduceGates H col σ (i + 1) gs p.2
    return p.1 :: μs

/-- The CCR adversary built from a distinguisher `D` of views: sample uniform input labels,
compute the material gate by gate with the oracle's help at open switches, and run `D`. -/
noncomputable def reduction [DecidableEq R] [Fintype L] (S : SwitchSystem n m N R)
    (H : L → ℕ → L) (col : L →+ ZMod 2) (σ : Fin n ⊕ Fin N → R)
    (D : SwitchView L n → ProbComp Bool) : ProbOracleComp (fun _ : L × ℕ × R => L) Bool := do
  let X ← ProbOracleComp.sample (ProbComp.uniform (Fin n → L))
  let μs ← reduceGates H col σ 0 S.gates (Sum.elim X 0)
  ProbOracleComp.sample (D ⟨μs, X⟩)

/-! ### Tweak uniqueness -/

private theorem isCostBounded_reduceGate [DecidableEq R] (H : L → ℕ → L) (col : L →+ ZMod 2)
    (σ : Fin n ⊕ Fin N → R) (i t : ℕ) (A : Fin n ⊕ Fin N → L) (g : SwitchGate n N R) :
    OracleComp.IsCostBounded
      (Sum.elim (fun _ => 0) fun q : L × ℕ × R => if q.2.1 = t then 1 else 0)
      (reduceGate H col σ i A g) (if i = t then 1 else 0) := by
  cases g with
  | affine terms b y => exact .pure _ _
  | switch x y c =>
    by_cases hc : σ c = 0
    · simp only [reduceGate, hc, ite_true]
      exact .pure _ _
    · simp only [reduceGate, hc, ite_false]
      refine ((ProbOracleComp.isCostBounded_query (spec := fun _ : L × ℕ × R => L) _
        (A c, i, σ (.inr y) - σ x)).bind (m := 0) fun r => OracleComp.IsCostBounded.pure _ 0).mono
        ?_
      simp
  | join x y => exact .pure _ _

private theorem isCostBounded_reduceGates [DecidableEq R] (H : L → ℕ → L)
    (col : L →+ ZMod 2) (σ : Fin n ⊕ Fin N → R) (t : ℕ) :
    ∀ (i : ℕ) (gs : List (SwitchGate n N R)) (A : Fin n ⊕ Fin N → L),
      OracleComp.IsCostBounded
        (Sum.elim (fun _ => 0) fun q : L × ℕ × R => if q.2.1 = t then 1 else 0)
        (reduceGates H col σ i gs A) (if i ≤ t then 1 else 0)
  | _, [], _ => .pure _ _
  | i, g :: gs, A => by
    refine ((isCostBounded_reduceGate H col σ i t A g).bind fun p =>
      (isCostBounded_reduceGates H col σ t (i + 1) gs p.2).bind fun μs =>
        .pure (p.1 :: μs) 0).mono ?_
    split_ifs <;> omega

/-- The reduction makes at most one query with each tweak: its query at gate position `i` has
tweak `i`. -/
theorem isTweakUnique_reduction [DecidableEq R] [Fintype L] (S : SwitchSystem n m N R)
    (H : L → ℕ → L) (col : L →+ ZMod 2) (σ : Fin n ⊕ Fin N → R)
    (D : SwitchView L n → ProbComp Bool) : CCR.IsTweakUnique (reduction S H col σ D) := by
  intro t
  refine ((ProbOracleComp.isCostBounded_sample _ _).bind fun X =>
    (isCostBounded_reduceGates H col σ t 0 S.gates (Sum.elim X 0)).bind fun μs =>
      ProbOracleComp.isCostBounded_sample _ (D ⟨μs, X⟩)).mono ?_
  split_ifs <;> omega

/-! ### The ideal side -/

private theorem interpret_reduceGate_ideal [DecidableEq R] [Fintype L] (H : L → ℕ → L)
    (col : L →+ ZMod 2) (σ : Fin n ⊕ Fin N → R) (i : ℕ) (A : Fin n ⊕ Fin N → L)
    (g : SwitchGate n N R) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin fun _ => ProbComp.uniform L)
      (reduceGate H col σ i A g) = simGate H col i A g (g.isOpen σ) := by
  cases g with
  | affine terms b y => rfl
  | switch x y c =>
    by_cases hc : σ c = 0
    · simp only [reduceGate, SwitchGate.isOpen, hc, ite_true, ne_eq, not_true_eq_false,
        decide_false, simGate]
      rfl
    · simp only [reduceGate, SwitchGate.isOpen, hc, ite_false, ne_eq, not_false_eq_true,
        decide_true, simGate, OracleComp.interpret_bind, ProbOracleComp.interpret_query]
      rfl
  | join x y => rfl

private theorem interpret_reduceGates_ideal [DecidableEq R] [Fintype L] (H : L → ℕ → L)
    (col : L →+ ZMod 2) (σ : Fin n ⊕ Fin N → R) :
    ∀ (i : ℕ) (gs : List (SwitchGate n N R)) (A : Fin n ⊕ Fin N → L),
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin fun _ => ProbComp.uniform L)
        (reduceGates H col σ i gs A) = simGates H col i gs (gs.map (SwitchGate.isOpen σ)) A
  | _, [], _ => rfl
  | i, g :: gs, A => by
    simp only [reduceGates, simGates, List.map_cons, OracleComp.interpret_bind,
      interpret_reduceGate_ideal, interpret_reduceGates_ideal, OracleComp.interpret_pure]

/-- With the fresh oracle the reduction runs `D` on the simulated view. -/
private theorem idealGame_reduction [DecidableEq R] [Fintype L] (S : SwitchSystem n m N R)
    (H : L → ℕ → L) (col : L →+ ZMod 2) (σ : Fin n ⊕ Fin N → R)
    (D : SwitchView L n → ProbComp Bool) :
    CCR.idealGame (reduction S H col σ D) = simGame S H col (S.controls σ) D := by
  have hself : ∀ {α : Type} (p : ProbComp α), OracleComp.interpret ProbComp.unifFin p = p :=
    fun p => OracleComp.interpret_query_eq_self p
  simp only [CCR.idealGame, simGame, simulate, reduction, SwitchSystem.controls,
    OracleComp.interpret_bind, ProbOracleComp.interpret_sample, hself,
    interpret_reduceGates_ideal, bind_assoc, pure_bind]

/-! ### The real side -/

private theorem termSum_wireLabel (Δ : L) (K : Fin n ⊕ Fin N → L)
    (σ : Fin n ⊕ Fin N → R) :
    ∀ terms : List ((Fin n ⊕ Fin N) × R),
      termSum (fun w => wireLabel Δ (K w) (σ w)) terms = termSum K terms + termSum σ terms • Δ
  | [] => by simp [termSum]
  | (w, c) :: ts => by
    have ih := termSum_wireLabel Δ K σ ts
    simp only [termSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, wireLabel, smul_eq_mul, add_smul, mul_smul, smul_add]
    abel

/-- With the keyed oracle, one step of the reduction from labels that are the active labels of
`σ` on the defined wires produces the garbler's material, and the new labels are again active on
the wires defined after the gate. -/
private theorem interpret_reduceGate_real [DecidableEq R] (H : L → ℕ → L)
    (col : L →+ ZMod 2) {Δ : L} (hΔ : col Δ = 1) {σ : Fin n ⊕ Fin N → R} (i : ℕ)
    {D : Set (Fin n ⊕ Fin N)}
    (K A : Fin n ⊕ Fin N → L) (hA : ∀ w ∈ D, A w = wireLabel Δ (K w) (σ w))
    {g : SwitchGate n N R} (hg : g.WellPlaced D) (hσ : g.Holds σ) :
    ∃ A', OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifFin fun q => pure (CCR.oracle H Δ q))
        (reduceGate H col σ i A g) = pure ((garbleGate H col Δ i K g).1, A') ∧
      ∀ w ∈ g.define D, A' w = wireLabel Δ ((garbleGate H col Δ i K g).2 w) (σ w) := by
  -- Away from a newly written wire, both label maps are unchanged.
  have hkeep : ∀ (y : Fin N) (a k : L), Sum.inr y ∉ D →
      ∀ w ∈ D, Function.update A (.inr y) a w =
        wireLabel Δ (Function.update K (.inr y) k w) (σ w) := by
    intro y a k hy w hw
    have hne : w ≠ .inr y := fun h => hy (h ▸ hw)
    rw [Function.update_of_ne hne, Function.update_of_ne hne]
    exact hA w hw
  have hnew : ∀ (y : Fin N) (a k : L), a = wireLabel Δ k (σ (.inr y)) → Sum.inr y ∉ D →
      ∀ w ∈ insert (Sum.inr y) D, Function.update A (.inr y) a w =
        wireLabel Δ (Function.update K (.inr y) k w) (σ w) := by
    intro y a k ha hy w hw
    rcases hw with rfl | hw
    · rw [Function.update_self, Function.update_self, ha]
    · exact hkeep y a k hy w hw
  cases g with
  | affine terms b y =>
    refine ⟨_, rfl, hnew y _ _ ?_ hg.2⟩
    have hsum : termSum A terms = termSum (fun w => wireLabel Δ (K w) (σ w)) terms := by
      simp only [termSum]
      congr 1
      exact List.map_congr_left fun p hp => by rw [hA p.1 (hg.1 p hp)]
    rw [hsum, termSum_wireLabel, wireLabel, hσ, add_smul]
    abel
  | switch x y c =>
    have hx := hA x hg.1
    have hc := hA c hg.2.1
    by_cases hc0 : σ c = 0
    · have hxy := hσ.2 hc0
      have hAc : A c = K c := by rw [hc, hc0, wireLabel, zero_smul, add_zero]
      refine ⟨Function.update A (.inr y) (A x + H (K c) i), by simp only [reduceGate, hc0,
        ite_true, OracleComp.interpret_pure, garbleGate, hAc], hnew y _ _ ?_ hg.2.2⟩
      rw [hx, wireLabel, wireLabel, hxy]
      abel
    · have hc1 : σ c = 1 := hσ.1.resolve_left hc0
      have hAc : A c - Δ = K c := by rw [hc, hc1, wireLabel, one_smul, add_sub_cancel_right]
      have hcol : col (A c) + 1 = col (K c) := by
        rw [hc, hc1, wireLabel, one_smul, map_add, hΔ, add_assoc, CharTwo.add_self_eq_zero,
          add_zero]
      refine ⟨Function.update A (.inr y) (A x + CCR.oracle H Δ (A c, i, σ (.inr y) - σ x)),
        by simp only [reduceGate, hc0, ite_false, OracleComp.interpret_bind,
          ProbOracleComp.interpret_query, pure_bind, OracleComp.interpret_pure, garbleGate, hcol],
        hnew y _ _ ?_ hg.2.2⟩
      rw [CCR.oracle, hAc, hx, wireLabel, wireLabel, sub_smul]
      abel
  | join x y =>
    refine ⟨A, ?_, hA⟩
    simp only [reduceGate, OracleComp.interpret_pure, garbleGate]
    rw [hA x hg.1, hA y hg.2, wireLabel, wireLabel, hσ]
    congr 3
    abel

private theorem interpret_reduceGates_real [DecidableEq R] (H : L → ℕ → L)
    (col : L →+ ZMod 2) {Δ : L} (hΔ : col Δ = 1) {σ : Fin n ⊕ Fin N → R} :
    ∀ (i : ℕ) (gs : List (SwitchGate n N R)) (D : Set (Fin n ⊕ Fin N))
      (K A : Fin n ⊕ Fin N → L), (∀ w ∈ D, A w = wireLabel Δ (K w) (σ w)) →
      SwitchSystem.WellFormedFrom D gs → (∀ g ∈ gs, g.Holds σ) →
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifFin fun q => pure (CCR.oracle H Δ q))
        (reduceGates H col σ i gs A) = pure (garbleGates H col Δ i gs K).1
  | _, [], _, _, _, _, _, _ => rfl
  | i, g :: gs, D, K, A, hA, ⟨hg, hgs⟩, hσ => by
    obtain ⟨A', hstep, hA'⟩ :=
      interpret_reduceGate_real H col hΔ i K A hA hg (hσ g List.mem_cons_self)
    simp only [reduceGates, garbleGates, OracleComp.interpret_bind, hstep, pure_bind,
      interpret_reduceGates_real H col hΔ (i + 1) gs (g.define D) _ A' hA' hgs
        (fun g' hg' => hσ g' (List.mem_cons_of_mem _ hg')), OracleComp.interpret_pure]

/-- With the keyed oracle the reduction runs `D` on the real view. -/
private theorem realGame_reduction [DecidableEq R] [Fintype L] {S : SwitchSystem n m N R}
    (hS : S.WellFormed) {x : Fin n → R} {σ : Fin n ⊕ Fin N → R} (hσ : S.Satisfies x σ)
    (H : L → ℕ → L) (col : L →+ ZMod 2) [Nonempty {Δ : L // col Δ = 1}]
    (D : SwitchView L n → ProbComp Bool) :
    CCR.realGame H col (reduction S H col σ D) = realGame S H col x D := by
  -- For each offset, the reduction from input labels `X` gives the material of the garbling
  -- with input zero labels `X - x • Δ`.
  have hmat : ∀ (Δ : {Δ : L // col Δ = 1}) (X : Fin n → L),
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifFin fun q => pure (CCR.oracle H Δ.1 q))
        (reduceGates H col σ 0 S.gates (Sum.elim X 0)) =
      pure (garbleWith S H col Δ.1 fun i => X i - x i • Δ.1).material := by
    intro Δ X
    refine interpret_reduceGates_real H col Δ.2 0 S.gates _ _ _ ?_ hS hσ.2
    rintro _ ⟨i, rfl⟩
    simp only [Sum.elim_inl, wireLabel, hσ.1 i, sub_add_cancel]
  -- Shifting uniform input labels by `x • Δ` is a bijection.
  have hshift : ∀ Δ : L, (PMF.uniformOfFintype (Fin n → L)).map (fun K i => K i + x i • Δ) =
      PMF.uniformOfFintype (Fin n → L) := fun Δ =>
    PMF.uniformOfFintype_map_equiv (Equiv.addRight fun i => x i • Δ)
  have hself : ∀ {α : Type} (p : ProbComp α), OracleComp.interpret ProbComp.unifFin p = p :=
    fun p => OracleComp.interpret_query_eq_self p
  simp only [CCR.realGame, realGame, garble, reduction, OracleComp.interpret_bind,
    ProbOracleComp.interpret_sample, hself, hmat, pure_bind, bind_assoc, ProbComp.eval_bind,
    ProbComp.eval_uniform]
  congr 1
  funext Δ
  conv_lhs => rw [← hshift Δ.1]
  rw [PMF.bind_map]
  congr 1
  funext K
  simp only [Function.comp_apply, add_sub_cancel_right, garbleWith]
  rfl

/-! ### The main theorem -/

/-- **Obliviousness from circular correlation robustness.** For a well-formed switch system `S`,
an assignment `σ` satisfying `S` on input `x`, and every distinguisher `D` of views, the advantage
of `D` between the real view of the garbling and the simulated view from the control bits of `σ`
equals the CCR advantage of the tweak-unique reduction `reduction S H col σ D`. -/
theorem advantage_realGame_simGame [DecidableEq R] [Fintype L] {S : SwitchSystem n m N R}
    (hS : S.WellFormed) {x : Fin n → R} {σ : Fin n ⊕ Fin N → R} (hσ : S.Satisfies x σ)
    (H : L → ℕ → L) (col : L →+ ZMod 2) [Nonempty {Δ : L // col Δ = 1}]
    (D : SwitchView L n → ProbComp Bool) :
    Game.advantage (realGame S H col x D) (simGame S H col (S.controls σ) D) =
      CCR.advantage H col (reduction S H col σ D) := by
  rw [CCR.advantage, realGame_reduction hS hσ H col D, idealGame_reduction S H col σ D]

end Switch

end Cslib.Crypto.Garbling
