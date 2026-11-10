/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (local addition beside the vendored `Turing.MultiTapeTM.Universal` files)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Configuration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Correct
public import Mathlib.Logic.Relation

/-!
# Descriptions of nondeterministic machines

A description `d` (`Turing.MultiTapeTM.Universal.Desc`) lists transitions as pairs of a key and an
action. The simulation of `d` fires the first entry whose key matches the configuration and halts
when there is none. Read nondeterministically, any matching entry may fire, and a running
configuration that matches no entry is stuck (`Turing.MultiTapeTM.Universal.NStep`).

A nondeterministic machine with finitely many states and symbols, renamed into `ℕ`, has a
description listing every permitted transition (`Turing.MultiTapeTM.Universal.descN`). Its steps
are the renamed steps of the machine, in both directions, so the machine accepts exactly when its
description reaches a halted configuration with the output `[1]`.

## Main definitions

* `Turing.MultiTapeTM.Universal.NStep`: a step of a description read nondeterministically.
* `Turing.MultiTapeTM.Universal.descN`: the description of a nondeterministic machine.

## Main results

* `Turing.MultiTapeTM.Universal.mem_descN`: the entries of the description are the permitted
  transitions, renamed.
* `Turing.MultiTapeTM.Universal.exists_nStep_of_step`,
  `Turing.MultiTapeTM.Universal.exists_step_of_nStep`: steps of the machine and of its
  description correspond.
* `Turing.MultiTapeTM.Universal.accepts_iff_reflTransGen_nStep`: the machine accepts exactly when
  its description reaches a halted configuration with the output `[1]`.
-/

namespace Turing.MultiTapeTM.Universal

variable {k : ℕ} {x : List ℕ}

/-- **A step of the description `d`, read nondeterministically**, on the input `x`, with the output
so far: a running configuration fires any entry of `d` whose key matches it. -/
@[expose] public def NStep (d : Desc) (x : List ℕ) (p p' : SCfg × List ℕ) : Prop :=
  ∃ q, p.1.state = some q ∧ ∃ e ∈ d.table, e.1 = p.1.key x q ∧
    p' = (e.2.apply x p.1, p.2 ++ e.2.output.toList)

/-! ### Descriptions of nondeterministic machines -/

variable {Symbol State : Type} [Finite State] [Finite Symbol]
  (eS : State ↪ ℕ) (eY : Symbol ↪ ℕ) (ntm : MultiTapeNTM k Symbol State)

/-- The description of a nondeterministic machine with finitely many states and symbols, renamed
into `ℕ` by `eS` and `eY`: an entry for every permitted transition. -/
public noncomputable def descN : Desc :=
  ⟨k, eS ntm.q₀, (Set.toFinite {e : State × Option Symbol × (Fin k → Option Symbol) ×
      Action k Symbol State | ntm.Tr e.1 e.2.1 e.2.2.1 e.2.2.2}).toFinset.toList.map
    fun e => (key (eS e.1) (e.2.1.map eY) (Option.map eY ∘ e.2.2.1),
      .ofAction (e.2.2.2.map eS eY))⟩

@[simp]
public lemma descN_tapes : (descN eS eY ntm).tapes = k := by
  rw [descN]

@[simp]
public lemma descN_q₀ : (descN eS eY ntm).q₀ = eS ntm.q₀ := by
  rw [descN]

/-- The entries of the description are the permitted transitions, renamed. -/
public theorem mem_descN {e : Key × Act} :
    e ∈ (descN eS eY ntm).table ↔ ∃ q i w a, ntm.Tr q i w a ∧
      e = (key (eS q) (i.map eY) (Option.map eY ∘ w), .ofAction (a.map eS eY)) := by
  simp only [descN, List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    Prod.exists]
  constructor
  · rintro ⟨q, i, w, a, h, rfl⟩
    exact ⟨q, i, w, a, h, rfl⟩
  · rintro ⟨q, i, w, a, h, rfl⟩
    exact ⟨q, i, w, a, h, rfl⟩

omit [Finite State] [Finite Symbol] in
/-- A key of the description determines the state and the read symbols. -/
lemma key_eq_key_iff {q q' : State} {i i' : Option Symbol} {w w' : Fin k → Option Symbol} :
    key (eS q) (i.map eY) (Option.map eY ∘ w) = key (eS q') (i'.map eY) (Option.map eY ∘ w') ↔
      q = q' ∧ i = i' ∧ w = w' := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩
  cases key_injective eS eY (a₁ := (q, i, w)) (a₂ := (q', i', w')) h
  exact ⟨rfl, rfl, rfl⟩

/-- **A step of the machine is a step of its description**: from a well-shaped configuration of
the simulation representing a running configuration, the description can take the renamed step. -/
public theorem exists_nStep_of_step {input : List Symbol} {c c' : Cfg k Symbol State input}
    (hc : ¬c.Halted) (h : ntm.Step c c') {s : SCfg} {out : List ℕ}
    (hs : s.WellShaped k (input.map eY)) (hsc : s.toCfg k (input.map eY) out = c.map eS eY) :
    ∃ s', NStep (descN eS eY ntm) (input.map eY) (s, out) (s', out ++ (c'.map eS eY).output.drop
        out.length) ∧ s'.WellShaped k (input.map eY) ∧
      s'.toCfg k (input.map eY) (out ++ (c'.map eS eY).output.drop out.length) = c'.map eS eY := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  simp only [MultiTapeNTM.Step, hq] at h
  obtain ⟨a, ha, rfl⟩ := h
  have hout : out = c.output.map eY := congrArg Cfg.output hsc
  have hstate : s.state = some (eS q) := by simpa [SCfg.toCfg, hq] using congrArg Cfg.state hsc
  obtain ⟨happ, hshape⟩ := toCfg_apply hs hstate out (a.map eS eY)
  have hdrop : out ++ ((a.apply c).map eS eY).output.drop out.length =
      out ++ (a.map eS eY).output.toList := by
    simp [hout, Action.apply, Option.toList_map]
  refine ⟨_, ⟨eS q, hstate, _, (mem_descN eS eY ntm).mpr ⟨q, _, _, a, ha, rfl⟩, ?_, ?_⟩,
    hshape, ?_⟩
  · rw [key_toCfg hs out, hsc, Cfg.inputSymbol_map]
    rfl
  · rw [hdrop]
    rfl
  · rw [hdrop]
    exact happ.trans (by rw [hsc, Action.apply_map])

/-- **A step of the description is a step of the machine**: from a well-shaped configuration of the
simulation representing a configuration of the machine, a step of the description represents a
step of the machine. -/
public theorem exists_step_of_nStep {input : List Symbol} {c : Cfg k Symbol State input}
    {s s' : SCfg} {out out' : List ℕ} (hs : s.WellShaped k (input.map eY))
    (hsc : s.toCfg k (input.map eY) out = c.map eS eY)
    (h : NStep (descN eS eY ntm) (input.map eY) (s, out) (s', out')) :
    ∃ c', ntm.Step c c' ∧ s'.WellShaped k (input.map eY) ∧
      s'.toCfg k (input.map eY) out' = c'.map eS eY := by
  obtain ⟨q', hq', e, he, hkey, heq⟩ := h
  obtain ⟨p, i, w, a, ha, rfl⟩ := (mem_descN eS eY ntm).mp he
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hstate : (c.map eS eY).state = some q' := by
    rw [← hsc]
    exact hq'
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hstate
  rw [key_toCfg hs out, hsc, Cfg.inputSymbol_map] at hkey
  obtain ⟨rfl, rfl, rfl⟩ := (key_eq_key_iff eS eY).mp hkey
  obtain ⟨happ, hshape⟩ := toCfg_apply hs hq' out (a.map eS eY)
  refine ⟨a.apply c, ?_, hshape, happ.trans (by rw [hsc, Action.apply_map])⟩
  simp only [MultiTapeNTM.Step, hq]
  exact ⟨a, ha, rfl⟩

/-! ### Computations -/

/-- **The configurations the description reaches** represent the last configurations of
computation paths of the machine. -/
public theorem exists_computationPath_of_reflTransGen {input : List Symbol} {p : SCfg × List ℕ}
    (h : Relation.ReflTransGen (NStep (descN eS eY ntm) (input.map eY))
      (init (descN eS eY ntm), []) p) :
    ∃ π : ntm.ComputationPath input, p.1.WellShaped k (input.map eY) ∧
      p.1.toCfg k (input.map eY) p.2 = π.last.map eS eY := by
  induction h with
  | refl =>
    obtain ⟨hinit, hshape⟩ := toCfg_init (x := input.map eY) (descN_tapes eS eY ntm)
    refine ⟨⟨RelSeries.singleton _ (ntm.initCfg input), rfl⟩, hshape, ?_⟩
    rw [hinit, descN_q₀]
    exact (Cfg.map_init eS eY ntm.q₀).symm
  | tail _ hstep ih =>
    obtain ⟨π, hshape, hπ⟩ := ih
    obtain ⟨c', hc', hshape', hc''⟩ := exists_step_of_nStep eS eY ntm hshape hπ hstep
    obtain ⟨π', -, hlast⟩ := π.exists_snoc hc'
    exact ⟨π', hshape', hlast ▸ hc''⟩

/-- **The last configuration of every computation path of the machine** is represented by a
configuration the description reaches. -/
public theorem exists_reflTransGen_of_computationPath {input : List Symbol}
    (π : ntm.ComputationPath input) :
    ∃ s, Relation.ReflTransGen (NStep (descN eS eY ntm) (input.map eY))
        (init (descN eS eY ntm), []) (s, π.last.output.map eY) ∧
      s.WellShaped k (input.map eY) ∧
      s.toCfg k (input.map eY) (π.last.output.map eY) = π.last.map eS eY := by
  obtain ⟨π, hπ⟩ := π
  induction π using RelSeries.inductionOn' with
  | singleton c =>
    obtain ⟨hinit, hshape⟩ := toCfg_init (x := input.map eY) (descN_tapes eS eY ntm)
    simp only [RelSeries.head_singleton] at hπ
    subst hπ
    refine ⟨_, .refl, hshape, hinit.trans ?_⟩
    rw [descN_q₀]
    exact (Cfg.map_init eS eY ntm.q₀).symm
  | snoc π c hc ih =>
    obtain ⟨s, hreach, hshape, hs⟩ := ih (by simpa using hπ)
    simp only [RelSeries.last_snoc]
    change ntm.Step π.last c at hc
    by_cases hhalt : π.last.Halted
    · rw [(MultiTapeNTM.step_of_halt hhalt).mp hc]
      exact ⟨s, hreach, hshape, hs⟩
    · have hout : π.last.output.map eY ++ (c.map eS eY).output.drop
          (π.last.output.map eY).length = c.output.map eY := by
        obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hhalt
        simp only [MultiTapeNTM.Step, hq] at hc
        obtain ⟨a, -, rfl⟩ := hc
        simp [Action.apply]
      obtain ⟨s', hstep, hshape', hs'⟩ :=
        exists_nStep_of_step eS eY ntm hhalt hc hshape hs
      rw [hout] at hstep hs'
      exact ⟨s', hreach.tail hstep, hshape', hs'⟩

/-- **A machine accepts exactly when its description reaches a halted configuration with the output
`[1]`.** -/
public theorem accepts_iff_reflTransGen_nStep (ntm : MultiTapeNTM k Bool State)
    (input : List Bool) :
    ntm.Accepts input ↔ ∃ s, s.state = none ∧
      Relation.ReflTransGen (NStep (descN eS eBit ntm) (input.map eBit))
        (init (descN eS eBit ntm), []) (s, [eBit true]) := by
  constructor
  · rintro ⟨π, hhalt, hout⟩
    obtain ⟨s, hreach, -, hs⟩ := exists_reflTransGen_of_computationPath eS eBit ntm π
    refine ⟨s, ?_, by simpa [hout] using hreach⟩
    simpa [SCfg.toCfg, hhalt] using congrArg Cfg.state hs
  · rintro ⟨s, hs, hreach⟩
    obtain ⟨π, -, hπ⟩ := exists_computationPath_of_reflTransGen eS eBit ntm hreach
    refine ⟨π, ?_, ?_⟩
    · simpa [SCfg.toCfg, hs] using (congrArg Cfg.state hπ).symm
    · have := congrArg Cfg.output hπ
      simp only [SCfg.toCfg, Cfg.map_output] at this
      exact List.map_injective_iff.mpr eBit.injective (by simpa using this.symm)

end Turing.MultiTapeTM.Universal
