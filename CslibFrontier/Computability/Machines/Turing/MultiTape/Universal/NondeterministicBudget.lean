/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Compiler
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.SpaceBudget
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# The nondeterministic universal machine within a space budget

A description `d` (`Turing.MultiTapeTM.Universal.Desc`), read nondeterministically
(`Turing.MultiTapeTM.Universal.NStep`), *accepts `x` within the budget `b`*
(`Turing.MultiTapeTM.Universal.BAccepts`) when some computation of it on `x` halts with the output
`[1]` and every configuration of the simulation it reaches after the first is encoded within `b`
bits (`Turing.MultiTapeTM.Universal.BStep`).

The universal recognizer `Turing.MultiTapeTM.Universal.budgetedNUniversal` decides this by guessing
the computation one transition at a time, as a nondeterministic query machine
(`Turing.NondeterministicQueryMachine`): its state holds the table of `d`, a cursor into the table,
the budget, the configuration of the simulation and the first two symbols of the output, and it
reads the input in place, at the simulated input head. A choice `false` moves the cursor to the
next entry; a choice `true` fires the entry under the cursor, if its key matches the
configuration, and returns the cursor to the start of the table. A branch rejects when the cursor
runs off the table, when the entry under the cursor does not match, or when the configuration
leaves the budget. So the machine accepts exactly when `d` accepts within the budget
(`Turing.MultiTapeTM.Universal.budgetedNUniversal_accepts_iff`).

Its state takes space linear in the description, the budget and the configuration, so the native
compiler of query machines gives a nondeterministic recognizer within space `O(S)` for any `S`
that bounds the description, the budget and `log₂ n`
(`Turing.MultiTapeTM.Universal.exists_recognizesInSpace_bAccepts`). Unlike the deterministic
`Turing.MultiTapeTM.Universal.budgetedUniversal`, the input is never copied and no clock is kept:
a recognizer may run forever.

## Main definitions

* `Turing.MultiTapeTM.Universal.BStep`, `Turing.MultiTapeTM.Universal.BAccepts`: the steps and the
  acceptance of a description read nondeterministically, within a budget.
* `Turing.MultiTapeTM.Universal.budgetedNUniversal`: the universal recognizer within a budget.

## Main results

* `Turing.MultiTapeTM.Universal.BAccepts.mono`,
  `Turing.MultiTapeTM.Universal.BAccepts.exists_reflTransGen_nStep`: a larger budget accepts more,
  and acceptance within a budget is acceptance.
* `Turing.MultiTapeTM.Universal.budgetedNUniversal_accepts_iff`: the recognizer accepts exactly
  when the description accepts within the budget.
* `Turing.MultiTapeTM.Universal.exists_recognizesInSpace_bAccepts`: a native recognizer within
  space `O(S)`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 9.3][Sipser2013]: the
  simulation within a space budget in the proof of the space hierarchy theorem.
-/

namespace Turing.MultiTapeTM.Universal

open ComputableInSpace

/-! ### Acceptance within a budget -/

/-- **A step of the description `d` within the budget `b`**, read nondeterministically, on the
input `x`: a step (`Turing.MultiTapeTM.Universal.NStep`) to a configuration encoded within `b`
bits. -/
@[expose] public def BStep (d : Desc) (x : List ℕ) (b : ℕ) (p p' : SCfg × List ℕ) : Prop :=
  NStep d x p p' ∧ (eCfg p'.1).length ≤ b

/-- **The description `d` accepts `x` within the budget `b`**: from the initial configuration, steps
within the budget reach a halted configuration with the output `[1]`. -/
@[expose] public def BAccepts (d : Desc) (x : List ℕ) (b : ℕ) : Prop :=
  ∃ s, s.state = none ∧ Relation.ReflTransGen (BStep d x b) (init d, []) (s, [eBit true])

/-- A larger budget accepts more. -/
public theorem BAccepts.mono {d : Desc} {x : List ℕ} {b b' : ℕ} (h : BAccepts d x b)
    (hb : b ≤ b') : BAccepts d x b' :=
  let ⟨s, hs, hr⟩ := h
  ⟨s, hs, hr.lift id fun _ _ h => ⟨h.1, h.2.trans hb⟩⟩

/-- Acceptance within a budget is acceptance: forgetting the budget, the description reaches a
halted configuration with the output `[1]`. -/
public theorem BAccepts.exists_reflTransGen_nStep {d : Desc} {x : List ℕ} {b : ℕ}
    (h : BAccepts d x b) :
    ∃ s, s.state = none ∧ Relation.ReflTransGen (NStep d x) (init d, []) (s, [eBit true]) :=
  let ⟨s, hs, hr⟩ := h
  ⟨s, hs, hr.lift id fun _ _ h => h.1⟩

/-! ### The universal recognizer -/

/-- The state of the universal recognizer: the table of the description, the entries from the
cursor on, the budget, the configuration of the simulation and the first two symbols of the
output. -/
public structure NUState where
  /-- The table of the description. -/
  table : List (Key × Act)
  /-- The entries of the table from the cursor on. -/
  rest : List (Key × Act)
  /-- The budget. -/
  budget : ℕ
  /-- The configuration of the simulation. -/
  cfg : SCfg
  /-- The first two symbols of the output. -/
  out : List ℕ

/-- States of the universal recognizer, as their fields, the budget in unary. -/
enc_structure eNU : NUState where
  table : (encList (encPair eKey eAct)), rest : (encList (encPair eKey eAct)), budget : encUnary,
  cfg : eCfg, out : (encList encUnary)

/-- The rejecting state: halted, with an empty output. -/
def nuReject : NUState := ⟨[], [], 0, ⟨none, 0, []⟩, []⟩

/-- The symbol under the simulated input head at the position `p`, given the answer `a` to the
query of the position `p - 1`: blank at position `0`. -/
def nuSym (p : ℕ) (a : Option Bool) : Option ℕ :=
  if p = 0 then none else a.map eBit

/-- The key of the transition to take in the configuration `c`, reading `a` on the input. -/
def nuKey (c : SCfg) (a : Option ℕ) : Key :=
  ⟨c.state.getD 0, a, c.workTapes.map Tape.read⟩

/-- The configuration after the action `e` in the configuration `c`, reading `a` on the input. -/
def nuApply (e : Act) (c : SCfg) (a : Option ℕ) : SCfg :=
  ⟨e.state, moveInput c.inputPos a e.inputTape, applyTapes c.workTapes e.workTapes⟩

/-- The next state of the universal recognizer, on the answer `p.2.1` to its query and the choice
`p.2.2`. -/
def nuNext (p : NUState × Option Bool × Bool) : NUState :=
  if p.1.rest.isEmpty then nuReject
  else if !p.2.2 then { p.1 with rest := p.1.rest.tail }
  else if decide ((p.1.rest.headD default).1 =
      nuKey p.1.cfg (nuSym p.1.cfg.inputPos p.2.1)) then
    if decide ((eCfg (nuApply (p.1.rest.headD default).2 p.1.cfg
        (nuSym p.1.cfg.inputPos p.2.1))).length ≤ p.1.budget) then
      { p.1 with
        rest := p.1.table
        cfg := nuApply (p.1.rest.headD default).2 p.1.cfg (nuSym p.1.cfg.inputPos p.2.1)
        out := (p.1.out ++ (p.1.rest.headD default).2.output.toList).take 2 }
    else nuReject
  else nuReject

/-- **The universal recognizer within a budget**, as a nondeterministic query machine: it queries
the input under the simulated input head, guesses the transitions one entry of the table at a
time, halts with the simulation and accepts on the output `[1]`.
Its initial state is irrelevant: it is started at `Turing.MultiTapeTM.Universal.nuStart` with
`Turing.NondeterministicQueryMachine.withInit`. -/
public def budgetedNUniversal : NondeterministicQueryMachine NUState where
  init := nuReject
  query s := s.cfg.inputPos - 1
  next := nuNext
  halted s := !s.cfg.state.isSome
  accept s := decide (s.out = [eBit true])

/-- The start of the universal recognizer on the description `d` within the budget `b`. -/
public def nuStart (d : Desc) (b : ℕ) : NUState := ⟨d.table, d.table, b, init d, []⟩

/-! ### Correctness -/

section Correct

variable {d : Desc} {x : List Bool} {b : ℕ}

/-- The symbol the recognizer reads is the symbol under the simulated input head. -/
lemma nuSym_read (s : NUState) :
    nuSym s.cfg.inputPos (budgetedNUniversal.read x s) =
      inputSymbol (x.map eBit) s.cfg.inputPos := by
  simp only [nuSym, NondeterministicQueryMachine.read, budgetedNUniversal, inputSymbol]
  split_ifs with h
  · rfl
  · rw [← List.map_drop, List.head?_map, List.head?_drop]

/-- The states the recognizer reaches from `nuStart d b`: the rejecting state, or the table and the
budget of the start, a cursor into the table, and a configuration that steps within the budget
reach, with the first two symbols of their output. -/
def NUInv (d : Desc) (x : List Bool) (b : ℕ) (s : NUState) : Prop :=
  s = nuReject ∨ s.table = d.table ∧ s.rest <:+ d.table ∧ s.budget = b ∧
    ∃ o, Relation.ReflTransGen (BStep d (x.map eBit) b) (init d, []) (s.cfg, o) ∧ s.out = o.take 2

lemma nuInv_start : NUInv d x b (nuStart d b) :=
  .inr ⟨rfl, List.suffix_refl _, rfl, [], .refl, rfl⟩

lemma NUInv.step {s : NUState} (h : NUInv d x b s) (choice : Bool) :
    NUInv d x b (budgetedNUniversal.step x s choice) := by
  unfold NondeterministicQueryMachine.step
  split_ifs with hh
  · exact h
  rcases h with rfl | ⟨htab, hrest, hbud, o, hreach, hout⟩
  · exact absurd rfl hh
  obtain ⟨q, hq⟩ : ∃ q, s.cfg.state = some q :=
    Option.ne_none_iff_exists'.mp (by simpa [budgetedNUniversal] using hh)
  change NUInv d x b (nuNext (s, budgetedNUniversal.read x s, choice))
  unfold nuNext
  simp only
  split_ifs with h₁ h₂ h₃ h₄
  · exact .inl rfl
  · exact .inr ⟨htab, (List.tail_suffix _).trans hrest, hbud, o, hreach, hout⟩
  · obtain ⟨e, r, he⟩ := List.exists_cons_of_ne_nil (List.isEmpty_eq_false_iff.mp
      (Bool.eq_false_iff.mpr h₁))
    rw [he, List.headD_cons] at h₃ h₄ ⊢
    rw [nuSym_read] at h₃ h₄ ⊢
    have hmem : e ∈ d.table := hrest.subset (he ▸ List.mem_cons_self ..)
    have hkey : e.1 = s.cfg.key (x.map eBit) q := by
      simpa [nuKey, hq, SCfg.key] using h₃
    have happ : nuApply e.2 s.cfg (inputSymbol (x.map eBit) s.cfg.inputPos) =
        e.2.apply (x.map eBit) s.cfg := rfl
    refine .inr ⟨htab, by simp [htab], hbud,
      o ++ e.2.output.toList, hreach.tail ⟨⟨q, hq, e, hmem, hkey, rfl⟩, ?_⟩, ?_⟩
    · exact hbud ▸ decide_eq_true_iff.mp h₄
    · simp only [hout]
      exact take_two_append_take_two o e.2.output.toList
  · exact .inl rfl
  · exact .inl rfl

lemma nuInv_replay {s : NUState} (h : NUInv d x b s) (choices : List Bool) :
    NUInv d x b (budgetedNUniversal.replay x choices s) := by
  induction choices generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih (h.step c)

/-- Choices `false` move the cursor of a running state. -/
lemma replay_skip {T r : List (Key × Act)} {B q : ℕ} {c : SCfg} {o : List ℕ}
    (hq : c.state = some q) (n : ℕ) (hn : n ≤ r.length) :
    budgetedNUniversal.replay x (List.replicate n false) ⟨T, r, B, c, o⟩ =
      ⟨T, r.drop n, B, c, o⟩ := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    obtain ⟨e, r, rfl⟩ := List.exists_cons_of_length_pos (show 0 < r.length by omega)
    have hstep : budgetedNUniversal.step x ⟨T, e :: r, B, c, o⟩ false = ⟨T, r, B, c, o⟩ := by
      simp [NondeterministicQueryMachine.step, budgetedNUniversal, hq, nuNext]
    rw [List.replicate_succ, NondeterministicQueryMachine.replay_cons, hstep,
      ih (by simp only [List.length_cons] at hn; omega), List.drop_succ_cons]

/-- A choice `true` fires the entry under the cursor when its key matches and the configuration it
reaches is within the budget. -/
lemma step_fire {T r : List (Key × Act)} {B q : ℕ} {c : SCfg} {o : List ℕ} {e : Key × Act}
    (hq : c.state = some q) (hkey : e.1 = c.key (x.map eBit) q)
    (hb : (eCfg (e.2.apply (x.map eBit) c)).length ≤ B) :
    budgetedNUniversal.step x ⟨T, e :: r, B, c, o⟩ true =
      ⟨T, T, B, e.2.apply (x.map eBit) c, (o ++ e.2.output.toList).take 2⟩ := by
  have hh : budgetedNUniversal.halted (⟨T, e :: r, B, c, o⟩ : NUState) = false := by
    simp [budgetedNUniversal, hq]
  have hr := nuSym_read (x := x) ⟨T, e :: r, B, c, o⟩
  simp only at hr
  have hk : e.1 = nuKey c (inputSymbol (x.map eBit) c.inputPos) := by
    rw [hkey]
    simp [nuKey, SCfg.key, hq]
  have ha : nuApply e.2 c (inputSymbol (x.map eBit) c.inputPos) = e.2.apply (x.map eBit) c := rfl
  simp only [NondeterministicQueryMachine.step, hh, Bool.false_eq_true, ↓reduceIte]
  change nuNext (⟨T, e :: r, B, c, o⟩, budgetedNUniversal.read x ⟨T, e :: r, B, c, o⟩, true) = _
  simp only [nuNext, hr, List.isEmpty_cons, List.headD_cons, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, ← hk, decide_true, ha, hb]

/-- A configuration stepping within the budget from the initial configuration is reached by the
recognizer from `nuStart d b`, with the cursor at the start of the table. -/
lemma exists_replay {c : SCfg} {o : List ℕ}
    (h : Relation.ReflTransGen (BStep d (x.map eBit) b) (init d, []) (c, o)) :
    ∃ choices, budgetedNUniversal.replay x choices (nuStart d b) =
      ⟨d.table, d.table, b, c, o.take 2⟩ := by
  suffices ∀ p, Relation.ReflTransGen (BStep d (x.map eBit) b) (init d, []) p →
      ∃ choices, budgetedNUniversal.replay x choices (nuStart d b) =
        ⟨d.table, d.table, b, p.1, p.2.take 2⟩ from this _ h
  intro p hp
  induction hp with
  | refl => exact ⟨[], rfl⟩
  | @tail p p' _ hstep ih =>
    obtain ⟨choices, hch⟩ := ih
    obtain ⟨⟨q, hq, e, he, hkey, rfl⟩, hb⟩ := hstep
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    refine ⟨choices ++ List.replicate i false ++ [true], ?_⟩
    rw [NondeterministicQueryMachine.replay_append, NondeterministicQueryMachine.replay_append,
      hch, replay_skip hq i hi.le, List.drop_eq_getElem_cons hi,
      NondeterministicQueryMachine.replay_cons, NondeterministicQueryMachine.replay_nil,
      step_fire hq hkey hb, take_two_append_take_two]

end Correct

/-- **The universal recognizer accepts exactly when the description accepts within the budget.** -/
public theorem budgetedNUniversal_accepts_iff (d : Desc) (x : List Bool) (b : ℕ) :
    (budgetedNUniversal.withInit (nuStart d b)).Accepts x ↔ BAccepts d (x.map eBit) b := by
  constructor
  · rintro ⟨choices, hh, ha⟩
    rw [NondeterministicQueryMachine.run_withInit] at hh ha
    rcases nuInv_replay nuInv_start choices with h | ⟨-, -, -, o, hreach, hout⟩
    · rw [h] at ha
      simp [NondeterministicQueryMachine.withInit, budgetedNUniversal, nuReject] at ha
    · set s := budgetedNUniversal.replay x choices (nuStart d b)
      have hs : s.out = [eBit true] := by
        simpa [NondeterministicQueryMachine.withInit, budgetedNUniversal] using ha
      have ho : o = [eBit true] := by
        rw [hout] at hs
        rcases o with _ | ⟨a, _ | ⟨a', o⟩⟩ <;> simp_all
      refine ⟨s.cfg, ?_, ho ▸ hreach⟩
      simpa [NondeterministicQueryMachine.withInit, budgetedNUniversal] using hh
  · rintro ⟨c, hc, hreach⟩
    obtain ⟨choices, hch⟩ := exists_replay hreach
    refine ⟨choices, ?_, ?_⟩ <;>
      rw [NondeterministicQueryMachine.run_withInit, hch] <;>
      simp [NondeterministicQueryMachine.withInit, budgetedNUniversal, hc]

/-! ### Space certificates -/

section Certificates

variable {γ : Type} {encIn : γ ↪ List Bool} {Bs : γ → ℕ}

private lemma nuSym_budget {p : γ → ℕ} {a : γ → Option Bool}
    (hp : ComputableInSpace p encIn encNat Bs)
    (ha : ComputableInSpace a encIn (encOption encBool) Bs) :
    ComputableInSpace (fun x => nuSym (p x) (a x)) encIn eSym Bs :=
  (budget_finite (encC := eSym) (fun q : Bool × Option Bool => if q.1 then none else q.2.map eBit)
    (budget_prod (budget_natIsZero hp) ha)).of_enc_eq fun x => by
      by_cases h : p x = 0 <;> simp [nuSym, h]

private lemma nuKey_budget {c : γ → SCfg} {a : γ → Option ℕ}
    (hc : ComputableInSpace c encIn eCfg Bs) (ha : ComputableInSpace a encIn eSym Bs) :
    ComputableInSpace (fun x => nuKey (c x) (a x)) encIn eKey Bs :=
  eKey_mk_budget (budget_optionGetD 0 (eCfg_state_budget hc)) ha
    (budget_comp_linear (of_inO reads_inO) (eCfg_workTapes_budget hc))

private lemma nuApply_budget {e : γ → Act} {c : γ → SCfg} {a : γ → Option ℕ}
    (he : ComputableInSpace e encIn eAct Bs) (hc : ComputableInSpace c encIn eCfg Bs)
    (ha : ComputableInSpace a encIn eSym Bs) :
    ComputableInSpace (fun x => nuApply (e x) (c x) (a x)) encIn eCfg Bs :=
  eCfg_mk_budget (eAct_state_budget he)
    (budget_comp_lin (of_inO moveInput_inO) linear_succ
      (budget_prod (eCfg_inputPos_budget hc) (budget_prod ha (eAct_inputTape_budget he))))
    (budget_comp_linear (of_inO applyTapes_inO)
      (budget_prod (eCfg_workTapes_budget hc) (eAct_workTapes_budget he)))

private lemma fits_budget {c : γ → SCfg} {b : γ → ℕ}
    (hc : ComputableInSpace c encIn eCfg Bs) (hb : ComputableInSpace b encIn encUnary Bs) :
    ComputableInSpace (fun x => decide ((eCfg (c x)).length ≤ b x)) encIn encBool Bs := by
  have hlen : ComputableInSpace (fun c : SCfg => (eCfg c).length) eCfg encUnary
      fun c => (eCfg c).length := of_inO (ComputableInO.lengthUnary.comp_enc eCfg)
  have hle : ComputableInSpace (fun q : ℕ × ℕ => decide (q.1 ≤ q.2)) (encPair encUnary encUnary)
      encBool fun q => (encPair encUnary encUnary q).length :=
    (of_inO ComputableInO.unaryLe).weaken linear_succ
  exact budget_comp_linear hle (budget_prod (budget_comp_linear hlen hc) hb)

private lemma keepTwo_budget {o : γ → List ℕ} {a : γ → Option ℕ}
    (ho : ComputableInSpace o encIn (encList encUnary) Bs)
    (ha : ComputableInSpace a encIn eSym Bs) :
    ComputableInSpace (fun x => (o x ++ (a x).toList).take 2) encIn (encList encUnary) Bs := by
  have hk : ComputableInSpace (fun q : List ℕ × Option ℕ => (q.1 ++ q.2.toList).take 2)
      (encPair (encList encUnary) eSym) (encList encUnary)
      fun q => (encPair (encList encUnary) eSym q).length :=
    of_inO (.of_tidy keepTwo_deg.inO_one)
  exact budget_comp_linear (f := fun x => (o x, a x)) hk (budget_prod ho ha)

private lemma nuNext_budget {p : γ → NUState × Option Bool × Bool}
    (hp : ComputableInSpace p encIn (encPair eNU (encPair (encOption encBool) encBool)) Bs)
    (hin : (fun x => (encIn x).length) ≼ Bs) :
    ComputableInSpace (fun x => nuNext (p x)) encIn eNU Bs := by
  have hs := hp.fst'
  have hans := hp.snd'.fst'
  have hch := hp.snd'.snd'
  have hT := eNU_table_budget hs
  have hR := eNU_rest_budget hs
  have hB := eNU_budget_budget hs
  have hC := eNU_cfg_budget hs
  have hO := eNU_out_budget hs
  have hsym := nuSym_budget (eCfg_inputPos_budget hC) hans
  have hE := budget_headD default hR
  have hfire : ComputableInSpace (fun x => ({ (p x).1 with
      rest := (p x).1.table
      cfg := nuApply ((p x).1.rest.headD default).2 (p x).1.cfg
        (nuSym (p x).1.cfg.inputPos (p x).2.1)
      out := ((p x).1.out ++ ((p x).1.rest.headD default).2.output.toList).take 2 } : NUState))
      encIn eNU Bs :=
    eNU_mk_budget hT hT hB (nuApply_budget hE.snd' hC hsym)
      (keepTwo_budget hO (eAct_output_budget hE.snd'))
  have hskip : ComputableInSpace (fun x => ({ (p x).1 with rest := (p x).1.rest.tail } : NUState))
      encIn eNU Bs :=
    eNU_mk_budget hT (budget_tail hR) hB hC hO
  have heq : ComputableInSpace (fun q : Key × Key => decide (q.1 = q.2)) (encPair eKey eKey)
      encBool fun q => (encPair eKey eKey q).length := of_inO (ComputableInO.eq eKey)
  have hmatch := budget_comp_linear heq (budget_prod hE.fst' (nuKey_budget hC hsym))
  have hfits := fits_budget (nuApply_budget hE.snd' hC hsym) hB
  have hrej := budget_const (encB := eNU) nuReject hin
  exact (budget_ite (budget_isEmpty hR) hrej
    (budget_ite (budget_finite (encC := encBool) Bool.not hch) hskip
      (budget_ite hmatch (budget_ite hfits hfire hrej) hrej))).of_enc_eq fun _ => rfl

private lemma nu_id : ComputableInSpace (fun s : NUState => s) eNU eNU fun s => (eNU s).length :=
  of_inO (ComputableInO.of_eq fun _ => rfl)

private lemma query_inSpace :
    ComputableInSpace budgetedNUniversal.query eNU encNat fun s => (eNU s).length :=
  budget_natPred (eCfg_inputPos_budget (eNU_cfg_budget nu_id))

private lemma next_inSpace :
    ComputableInSpace budgetedNUniversal.next (encPair eNU (encPair (encOption encBool) encBool))
      eNU fun p => (encPair eNU (encPair (encOption encBool) encBool) p).length :=
  nuNext_budget (of_inO (ComputableInO.of_eq fun _ => rfl)) (.refl _)

private lemma halted_inSpace :
    ComputableInSpace budgetedNUniversal.halted eNU encBool fun s => (eNU s).length :=
  (budget_finite (encC := encBool) Bool.not
    (budget_optionIsSome (eCfg_state_budget (eNU_cfg_budget nu_id)))).of_enc_eq fun _ => rfl

private lemma accept_inSpace :
    ComputableInSpace budgetedNUniversal.accept eNU encBool fun s => (eNU s).length := by
  have heq : ComputableInSpace (fun q : List ℕ × List ℕ => decide (q.1 = q.2))
      (encPair (encList encUnary) (encList encUnary)) encBool
      fun q => (encPair (encList encUnary) (encList encUnary) q).length :=
    of_inO (ComputableInO.eq (encList encUnary))
  exact (budget_comp_linear (f := fun s : NUState => (s.out, [eBit true])) heq
    (budget_prod (eNU_out_budget nu_id) (budget_const [eBit true] (.refl _)))).of_enc_eq
    fun _ => rfl

end Certificates

/-! ### The size of the reachable states -/

section Size

variable {d : Desc} {x : List Bool} {b : ℕ}

/-- The symbols output by steps from the initial configuration are within the description. -/
lemma output_le_of_reach {c : SCfg} {o : List ℕ}
    (h : Relation.ReflTransGen (BStep d (x.map eBit) b) (init d, []) (c, o)) :
    ∀ a ∈ o, a ≤ descLen d := by
  suffices ∀ p, Relation.ReflTransGen (BStep d (x.map eBit) b) (init d, []) p →
      ∀ a ∈ p.2, a ≤ descLen d from this _ h
  intro p hp
  induction hp with
  | refl => simp
  | @tail p p' _ hstep ih =>
    obtain ⟨⟨q, -, e, he, -, rfl⟩, -⟩ := hstep
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ih a ha
    · have : e.2.output = some a := by simpa using ha
      simpa [this] using output_le he

/-- A configuration reached by steps within the budget is encoded within the initial
configuration or the budget. -/
lemma length_eCfg_of_reach {c : SCfg} {o : List ℕ}
    (h : Relation.ReflTransGen (BStep d (x.map eBit) b) (init d, []) (c, o)) :
    (eCfg c).length ≤ 11 * descLen d + 6 + b := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨_, -, -, hb⟩
  · cases h
    have := length_eCfg_init_le d
    omega
  · have : (eCfg c).length ≤ b := hb
    omega

lemma length_take_two_le {o : List ℕ} {D : ℕ} (h : ∀ a ∈ o, a ≤ D) :
    (encList encUnary (o.take 2)).length ≤ 4 * D + 2 := by
  rcases o with _ | ⟨a, _ | ⟨a', o⟩⟩
  · simp
  · have := h a (by simp)
    simp
    omega
  · have := h a (by simp)
    have := h a' (by simp)
    simp
    omega

lemma length_rest_le {r : List (Key × Act)} (h : r <:+ d.table) :
    (encList (encPair eKey eAct) r).length ≤ descLen d := by
  obtain ⟨l, hl⟩ := h
  have h₁ := SizedListEncoding.length_drop_le (encA := encPair eKey eAct)
    (encL := encList (encPair eKey eAct)) d.table l.length
  have h₂ : (encList (encPair eKey eAct) d.table).length ≤ descLen d := by
    simp only [descLen, eDesc_apply, length_encPair]
    omega
  rw [← hl, List.drop_left] at h₁
  rw [hl] at h₁
  omega

/-- **The states of the recognizer are encoded within linear space** in the description and the
budget. -/
lemma length_eNU_le {s : NUState} (h : NUInv d x b s) :
    (eNU s).length ≤ 40 * descLen d + 4 * b + 40 := by
  rcases h with rfl | ⟨htab, hrest, rfl, o, hreach, hout⟩
  · simp [nuReject, eNU_apply, eCfg_apply]
  · obtain ⟨T, r, B, c, out⟩ := s
    simp only at htab hrest hout hreach ⊢
    subst htab hout
    have h₁ := length_rest_le hrest
    have h₂ := length_rest_le (d := d) (List.suffix_refl d.table)
    have h₃ := length_eCfg_of_reach hreach
    have h₄ := length_take_two_le (output_le_of_reach hreach)
    simp only [eNU_apply, length_encPair, encUnary_apply, List.length_replicate] at *
    omega

end Size

/-! ### The compiled recognizer -/

/-- **A native nondeterministic recognizer of acceptance within a budget**, in space `O(S)`: for a
description `D a` and a budget `B a` computed from the input `a` within the space `S a ≥ log₂ |a|`,
the inputs `a` on which `D a` accepts `a` within the budget `B a`. -/
public theorem exists_recognizesInSpace_bAccepts {α : Type} (enc : α ↪ List Bool) (D : α → Desc)
    (B : α → ℕ) (S : α → ℕ) (hD : ComputableInSpace D enc eDesc S)
    (hB : ComputableInSpace B enc encUnary S) (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
      ntm.RecognizesInSpace enc {a | BAccepts (D a) ((enc a).map eBit) (B a)}
        (fun a => c * S a) := by
  have hT := eDesc_table_budget hD
  have hI : ComputableInSpace (fun a => init (D a)) enc eCfg S :=
    budget_comp_lin (of_inO init_inO.computableInO) linear_succ hD
  have hO : ComputableInSpace (fun _ : α => ([] : List ℕ)) enc (encList encUnary) S :=
    (constZero []).mono_le fun _ => Nat.zero_le _
  have hstart : ComputableInSpace (fun a => nuStart (D a) (B a)) enc eNU S :=
    eNU_mk_budget hT hT hB hI hO
  obtain ⟨cD, hcD⟩ := hD.length_le
  obtain ⟨cB, hcB⟩ := hB.length_le
  refine NondeterministicQueryMachine.exists_recognizesInSpace budgetedNUniversal query_inSpace
    next_inSpace halted_inSpace accept_inSpace (fun a => nuStart (D a) (B a))
    (fun a => (budgetedNUniversal_accepts_iff _ _ _).symm) S hlog hstart
    ⟨40 * 2 * cD + 4 * 2 * cB + 80, fun a choices => ?_⟩
  rw [NondeterministicQueryMachine.run_withInit]
  have h := length_eNU_le (nuInv_replay (x := enc a) (nuInv_start (d := D a) (b := B a)) choices)
  have h₁ := hcD a
  have h₂ := hcB a
  have h₃ := hlog a
  simp only [descLen, encUnary_apply, List.length_replicate] at h h₁ h₂
  nlinarith


end Turing.MultiTapeTM.Universal
