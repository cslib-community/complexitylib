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
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Space
public import Mathlib.Logic.Relation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Space
import Mathlib.Data.List.GetD

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

Along a computation path of the machine within `S` cells, the description's run stays within
`cfgSpaceBound (descLen d) n k S` bits, for inputs of length `n` and `k` work tapes. The zippers
of the run hold only cells that the machine's heads have visited, so this bound holds at every
configuration the run steps to.

## Main definitions

* `Turing.MultiTapeTM.Universal.NStep`: a step of a description read nondeterministically.
* `Turing.MultiTapeTM.Universal.descN`: the description of a nondeterministic machine.

## Main results

* `Turing.MultiTapeTM.Universal.mem_descN`: the entries of the description are the permitted
  transitions, renamed.
* `Turing.MultiTapeTM.Universal.exists_nStep_of_step`,
  `Turing.MultiTapeTM.Universal.exists_step_of_nStep`: steps of the machine and of its
  description correspond.
* `Turing.MultiTapeTM.Universal.exists_computationPath_of_reflTransGen`,
  `Turing.MultiTapeTM.Universal.exists_reflTransGen_of_computationPath`: so do computation paths
  of the machine and runs of its description.
* `Turing.MultiTapeTM.Universal.exists_reflTransGen_fits_of_computationPath`: a computation path
  within `S` cells is represented by a run of the description within the space bound.
* `Turing.MultiTapeTM.Universal.accepts_iff_reflTransGen_nStep`: the machine accepts exactly when
  its description reaches a halted configuration with the output `[1]`.
* `Turing.MultiTapeTM.Universal.accepts_iff_reflTransGen_nStep_fits`: for a machine within `S`
  cells, the same within the space bound.
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

/-- **A step of the machine is a step of its description**: from a well-shaped configuration of
the simulation representing a running configuration, the description can take the renamed step. -/
public theorem exists_nStep_of_step {input : List Symbol} {c c' : Cfg k Symbol State input}
    (hc : ¬c.Halted) (h : ntm.Step c c') {s : SCfg} {out : List ℕ}
    (hs : s.WellShaped k (input.map eY)) (hsc : s.toCfg k (input.map eY) out = c.map eS eY) :
    ∃ s', NStep (descN eS eY ntm) (input.map eY) (s, out) (s', (c'.map eS eY).output) ∧
      s'.WellShaped k (input.map eY) ∧
      s'.toCfg k (input.map eY) (c'.map eS eY).output = c'.map eS eY := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  simp only [MultiTapeNTM.Step, hq] at h
  obtain ⟨a, ha, rfl⟩ := h
  have hout : out = c.output.map eY := congrArg Cfg.output hsc
  have hstate : s.state = some (eS q) := by simpa [SCfg.toCfg, hq] using congrArg Cfg.state hsc
  obtain ⟨happ, hshape⟩ := toCfg_apply hs hstate out (a.map eS eY)
  have hout' : ((a.apply c).map eS eY).output = out ++ (a.map eS eY).output.toList := by
    simp [hout, Action.apply, Option.toList_map]
  refine ⟨_, ⟨eS q, hstate, _, (mem_descN eS eY ntm).mpr ⟨q, _, _, a, ha, rfl⟩, ?_, ?_⟩,
    hshape, ?_⟩
  · rw [key_toCfg hs out, hsc, Cfg.inputSymbol_map]
    rfl
  · rw [hout']
    rfl
  · rw [hout']
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
  cases key_injective eS eY (a₁ := (p, i, w)) (a₂ := (q, c.inputSymbol, c.workTapeSymbols)) hkey
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

/-! ### Runs within the space of the machine -/

omit [Finite State] [Finite Symbol] in
lemma workTapePos_toCfg {input : List Symbol} {s : SCfg} {out : List ℕ}
    {c : Cfg k Symbol State input} (hsc : s.toCfg k (input.map eY) out = c.map eS eY) (i : Fin k) :
    (s.workTapes.getD i .blank).head = c.workTapePos i :=
  congrArg (·.workTapePos i) hsc

omit [Finite State] [Finite Symbol] in
/-- A configuration of the simulation that represents the end of a run path from the initial
configuration, and whose zippers hold only cells the heads of the path visited, is within the
space bound of the path. -/
lemma length_eCfg_le_of_toCfg {input : List Symbol} {π : ntm.RunPath input}
    (hπ : π.head = ntm.initCfg input) {s : SCfg} {out : List ℕ} {D j : ℕ}
    (hs : s.WellShaped k (input.map eY)) (hsc : s.toCfg k (input.map eY) out = π.last.map eS eY)
    (hinv : Inv D (input.map eY).length j s)
    (hcov : ∀ i : Fin k, (s.workTapes.getD i .blank).Covered (π.visitedByTapeHead i)) :
    (eCfg s).length ≤ cfgSpaceBound D input.length k π.space := by
  let V : ℕ → Finset ℤ := fun i => if hi : i < k then π.visitedByTapeHead ⟨i, hi⟩ else ∅
  have hV (i : Fin k) : V i = π.visitedByTapeHead i := by simp [V]
  have hS : ∑ i ∈ Finset.range k, (V i).card ≤ π.space := by
    rw [Finset.sum_range (fun i => (V i).card)]
    simp only [hV, MultiTapeNTM.RunPath.space, MultiTapeNTM.RunPath.spaceUsedByTape, le_refl]
  have := length_eCfg_le_of_covered (V := V) hinv hs.length_workTapes
    (fun i hi => hV ⟨i, hi⟩ ▸ hcov ⟨i, hi⟩) (fun i hi => ?_) hS
  · rwa [List.length_map] at this
  · rw [hV ⟨i, hi⟩, workTapePos_toCfg eS eY hsc ⟨i, hi⟩]
    exact (π.natAbs_lt_spaceUsedByTape (by simp [hπ]) (by simp [hπ]) ⟨i, hi⟩).1

omit [Finite State] [Finite Symbol] in
lemma getD_workTapes_init (d : Desc) (i : ℕ) : (init d).workTapes.getD i .blank = .blank := by
  rcases Nat.lt_or_ge i d.tapes with h | h <;>
    simp [init, List.getD_eq_getElem?_getD, h, Tape.blank]

/-- The run of the description that represents a run path from the initial configuration, along
with the invariants that bound its configurations. -/
lemma exists_reflTransGen_fits_aux {input : List Symbol} (π : ntm.RunPath input)
    (hπ : π.head = ntm.initCfg input) {S : ℕ} (hS : π.space ≤ S) :
    ∃ s, Relation.ReflTransGen (fun p p' => NStep (descN eS eY ntm) (input.map eY) p p' ∧
        (eCfg p'.1).length ≤ cfgSpaceBound (descLen (descN eS eY ntm)) input.length k S)
        (init (descN eS eY ntm), []) (s, π.last.output.map eY) ∧
      s.WellShaped k (input.map eY) ∧
      s.toCfg k (input.map eY) (π.last.output.map eY) = π.last.map eS eY ∧
      (∃ j, Inv (descLen (descN eS eY ntm)) (input.map eY).length j s) ∧
      ∀ i : Fin k, (s.workTapes.getD i .blank).Covered (π.visitedByTapeHead i) := by
  induction π using RelSeries.inductionOn' with
  | singleton c =>
    obtain ⟨hinit, hshape⟩ := toCfg_init (x := input.map eY) (descN_tapes eS eY ntm)
    simp only [RelSeries.head_singleton] at hπ
    subst hπ
    refine ⟨_, .refl, hshape, hinit.trans ?_, ⟨0, inv_init _ _⟩, fun i => ?_⟩
    · rw [descN_q₀]
      exact (Cfg.map_init eS eY ntm.q₀).symm
    · rw [getD_workTapes_init]
      exact ⟨fun _ h => by simp [Tape.blank] at h, fun _ h => by simp [Tape.blank] at h⟩
  | snoc π c hc ih =>
    simp only [RelSeries.head_snoc] at hπ
    have hsub : ∀ c' ∈ π, c' ∈ π.snoc c hc := fun c' h => RelSeries.mem_snoc.mpr (.inl h)
    obtain ⟨s, hreach, hshape, hs, ⟨j, hinv⟩, hcov⟩ :=
      ih hπ ((MultiTapeNTM.RunPath.space_le_of_subset hsub).trans hS)
    have hvis (i : Fin k) : MultiTapeNTM.RunPath.visitedByTapeHead π i ⊆
        MultiTapeNTM.RunPath.visitedByTapeHead (π.snoc c hc) i := by
      rw [MultiTapeNTM.RunPath.visitedByTapeHead_snoc]
      exact Finset.subset_insert _ _
    have hlast (i : Fin k) :
        π.last.workTapePos i ∈ MultiTapeNTM.RunPath.visitedByTapeHead (π.snoc c hc) i :=
      hvis i ((MultiTapeNTM.RunPath.mem_visitedByTapeHead π).mpr ⟨π.last, π.last_mem, rfl⟩)
    have hnew (i : Fin k) :
        c.workTapePos i ∈ MultiTapeNTM.RunPath.visitedByTapeHead (π.snoc c hc) i := by
      rw [MultiTapeNTM.RunPath.visitedByTapeHead_snoc]
      exact Finset.mem_insert_self _ _
    change ntm.Step π.last c at hc
    simp only [RelSeries.last_snoc]
    by_cases hhalt : π.last.Halted
    · obtain rfl := (MultiTapeNTM.step_of_halt hhalt).mp hc
      exact ⟨s, hreach, hshape, hs, ⟨j, hinv⟩,
        fun i => (hcov i).mono (Finset.coe_subset.mpr (hvis i))⟩
    obtain ⟨s', hstep, hshape', hs'⟩ := exists_nStep_of_step eS eY ntm hhalt hc hshape hs
    obtain ⟨q, hq, e, he, hkey, heq⟩ := hstep
    have hs'eq : s' = e.2.apply (input.map eY) s := congrArg Prod.fst heq
    have hcov' (i : Fin k) :
        (s'.workTapes.getD i .blank).Covered
          (MultiTapeNTM.RunPath.visitedByTapeHead (π.snoc c hc) i) := by
      obtain ⟨ta, hta⟩ := Act.apply_tape e.2 (input.map eY) s i
      have hhead := workTapePos_toCfg eS eY hs' i
      rw [hs'eq, hta] at hhead ⊢
      refine ((hcov i).mono (Finset.coe_subset.mpr (hvis i))).apply ?_ ta (hhead ▸ hnew i)
      rw [workTapePos_toCfg eS eY hs i]
      exact hlast i
    have hfits := length_eCfg_le_of_toCfg eS eY ntm (π := π.snoc c hc)
      (by rw [RelSeries.head_snoc]; exact hπ) hshape' (by rw [RelSeries.last_snoc]; exact hs')
      (hs'eq ▸ hinv.apply he) hcov'
    refine ⟨s', hreach.tail ⟨⟨q, hq, e, he, hkey, heq⟩, hfits.trans ?_⟩, hshape', hs',
      ⟨j + 1, hs'eq ▸ hinv.apply he⟩, hcov'⟩
    simp only [cfgSpaceBound]
    have := Nat.mul_le_mul_left (3 * (2 * descLen (descN eS eY ntm) + 5) * 2) hS
    omega

/-- **A computation path of the machine within `S` cells is represented by a run of its
description within the space bound**: every configuration the run steps to is at most
`cfgSpaceBound (descLen d) n k S` bits long. -/
public theorem exists_reflTransGen_fits_of_computationPath {input : List Symbol}
    (π : ntm.ComputationPath input) {S : ℕ} (hS : π.space ≤ S) :
    ∃ s, Relation.ReflTransGen (fun p p' => NStep (descN eS eY ntm) (input.map eY) p p' ∧
        (eCfg p'.1).length ≤ cfgSpaceBound (descLen (descN eS eY ntm)) input.length k S)
        (init (descN eS eY ntm), []) (s, π.last.output.map eY) ∧
      s.WellShaped k (input.map eY) ∧
      s.toCfg k (input.map eY) (π.last.output.map eY) = π.last.map eS eY := by
  obtain ⟨s, hreach, hshape, hs, -⟩ :=
    exists_reflTransGen_fits_aux eS eY ntm π.toRunPath π.head_eq hS
  exact ⟨s, hreach, hshape, hs⟩

/-- **The last configuration of every computation path of the machine** is represented by a
configuration the description reaches. -/
public theorem exists_reflTransGen_of_computationPath {input : List Symbol}
    (π : ntm.ComputationPath input) :
    ∃ s, Relation.ReflTransGen (NStep (descN eS eY ntm) (input.map eY))
        (init (descN eS eY ntm), []) (s, π.last.output.map eY) ∧
      s.WellShaped k (input.map eY) ∧
      s.toCfg k (input.map eY) (π.last.output.map eY) = π.last.map eS eY := by
  obtain ⟨s, hreach, hshape, hs⟩ := exists_reflTransGen_fits_of_computationPath eS eY ntm π le_rfl
  exact ⟨s, hreach.lift id fun _ _ h => h.1, hshape, hs⟩

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

/-- **A machine within `S` cells accepts exactly when its description reaches a halted
configuration with the output `[1]` within the space bound.** -/
public theorem accepts_iff_reflTransGen_nStep_fits (ntm : MultiTapeNTM k Bool State)
    (input : List Bool) {S : ℕ} (hS : ntm.RunsInSpace input S) :
    ntm.Accepts input ↔ ∃ s, s.state = none ∧
      Relation.ReflTransGen (fun p p' => NStep (descN eS eBit ntm) (input.map eBit) p p' ∧
          (eCfg p'.1).length ≤ cfgSpaceBound (descLen (descN eS eBit ntm)) input.length k S)
        (init (descN eS eBit ntm), []) (s, [eBit true]) := by
  constructor
  · rintro ⟨π, hhalt, hout⟩
    obtain ⟨s, hreach, -, hs⟩ := exists_reflTransGen_fits_of_computationPath eS eBit ntm π (hS π)
    refine ⟨s, ?_, by simpa [hout] using hreach⟩
    simpa [SCfg.toCfg, hhalt] using congrArg Cfg.state hs
  · rintro ⟨s, hs, hreach⟩
    exact (accepts_iff_reflTransGen_nStep eS ntm input).mpr
      ⟨s, hs, hreach.lift id fun _ _ h => h.1⟩

end Turing.MultiTapeTM.Universal
