/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.ReadMachine.VirtualWord.Simulation
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bit
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative

/-!
# Streaming native configurations as query states

The existing universal simulator already represents native work tapes by finite zippers and
keeps the shifted input-head address in binary. This adapter reuses that representation and its
native step certificate. Output history is never part of the saved query state. Position zero
is the left boundary blank; a read at that position is ignored, and rightward movement from it
is allowed. At the right boundary, the optional read stops further rightward movement.

## Main definitions

* `machine`: a streaming query adapter for a native machine description.
* `budget`: saved configuration storage extracted from native workspace.

## Main results

* `configuration_native`: full native configuration correspondence, with output held externally.
* `components_inSpace`: all five native component certificates.
* `length_native_run_le_of_space`: saved-state bound from the original workspace certificate.
* `computableInSpace_of_computes`: substitution from ordinary computation/workspace certificates.
* `of_logSpace`: substitution from the unchanged ordinary logspace predicate.

This is an original infrastructure construction towards the recomputation argument on printed
page 6 of expanded ECCC TR13-047 [GlasserNguyenReitwiessnerSelmanWitek2013], not Lemma 3.3.
-/

public section

namespace Turing.VirtualWord.Native

open MultiTapeTM MultiTapeTM.Universal ComputableInSpace

/-- A numbered binary output symbol, with a total default on nonbinary descriptions. -/
@[expose] def outputBit (n : ℕ) : Bool := n != 0

/-- Suppress the fetched bit at the native left boundary. -/
@[expose] def input (s : SCfg) (b : Option Bool) : Option ℕ :=
  if s.inputPos = 0 then none else b.map eBit

/-- Arbitrary machine descriptions, with streaming output and no output history in `SCfg`. -/
@[expose] def machine (d : Desc) : QueryMachine SCfg where
  init := init d
  query s := s.inputPos - 1
  next p := (stepWith d p.1 (input p.1 p.2)).1
  emit p := ((stepWith d p.1 (input p.1 p.2)).2.map outputBit).toList
  halted s := s.state.isNone
  finish _ := []

/-- The optional query read is exactly the native shifted-head read, including both blanks. -/
theorem input_read (d : Desc) (x : List Bool) (s : SCfg) :
    input s ((machine d).read x s) = inputSymbol (x.map eBit) s.inputPos := by
  simp only [input, QueryMachine.read, machine, inputSymbol]
  split_ifs
  · rfl
  · rw [List.head?_drop, List.getElem?_map]

/-- One query step is the existing streaming native step, even on halted configurations. -/
theorem step_eq (d : Desc) (x : List Bool) (s : SCfg) :
    (machine d).step x s = (step d (x.map eBit) s).1 := by
  change (if s.state.isNone then s else
    (stepWith d s (input s ((machine d).read x s))).1) = _
  rw [input_read, step_eq_stepWith]
  cases hs : s.state <;> simp only [hs, Option.isNone_none, Option.isNone_some,
    Bool.false_eq_true, ↓reduceIte, stepWith]

/-- The saved query state is precisely the universal simulator's native work configuration. -/
theorem run_eq (d : Desc) (x : List Bool) (t : ℕ) :
    (machine d).run x t = run d (x.map eBit) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.run_succ, ih, step_eq]
    simp only [run, Function.iterate_succ_apply', stepOut]

/-- Emission is the native step's output symbol, without retaining earlier output. -/
theorem emit_eq (d : Desc) (x : List Bool) (s : SCfg) :
    (machine d).emit (s, (machine d).read x s) =
      ((step d (x.map eBit) s).2.map outputBit).toList := by
  rw [step_eq_stepWith, ← input_read d x s]
  rfl

/-- Streaming output agrees with the existing simulator's accumulated output at every clock. -/
theorem output_eq (d : Desc) (x : List Bool) (t : ℕ) :
    (machine d).output x t =
      (((stepOut d (x.map eBit))^[t] (init d, [])).2.map outputBit) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he : (if (machine d).halted ((machine d).run x t) then [] else
        (machine d).emit ((machine d).run x t, (machine d).read x ((machine d).run x t))) =
        ((step d (x.map eBit) ((machine d).run x t)).2.map outputBit).toList := by
      rw [emit_eq]
      change (if ((machine d).run x t).state.isNone then [] else _) = _
      cases hs : ((machine d).run x t).state <;> simp [hs, MultiTapeTM.Universal.step]
    simp only [QueryMachine.output, show (machine d).finish = fun _ => [] from rfl,
      List.append_nil] at ih ⊢
    rw [List.range_succ, List.map_append, List.flatten_append]
    simp only [List.map_singleton, List.flatten_singleton]
    change _ ++ (if _ then [] else _) = _
    rw [he, ih, Function.iterate_succ_apply']
    simp only [stepOut, List.map_append, Option.toList_map, run_eq, run]

/-- The configuration field view reuses the existing encoding byte for byte. -/
private theorem fields_inSpace : ComputableInSpace
    (fun s : SCfg => (s.state, s.inputPos, s.workTapes)) eCfg eCfgFields
    (fun s => (eCfg s).length) :=
  of_inO (.of_eq fun _ => rfl)

/-- All five components of an arbitrary fixed description have native certificates. The
transition table is a fixed machine constant; it is not an oracle or a substitution premise. -/
theorem components_inSpace (d : Desc) :
    ComputableInSpace (machine d).query eCfg encNat (fun s => (eCfg s).length) ∧
    ComputableInSpace (machine d).next (encPair eCfg (encOption encBool)) eCfg
      (fun p => (encPair eCfg (encOption encBool) p).length) ∧
    ComputableInSpace (machine d).emit (encPair eCfg (encOption encBool)) encBits
      (fun p => (encPair eCfg (encOption encBool) p).length) ∧
    ComputableInSpace (machine d).halted eCfg encBool (fun s => (eCfg s).length) ∧
    ComputableInSpace (machine d).finish eCfg encBits (fun s => (eCfg s).length) := by
  have hpos := fields_inSpace.snd'.fst'
  have hp := fst eCfg (encOption encBool)
  have hb := snd eCfg (encOption encBool)
  have hzero := budget_natIsZero (budget_comp_linear hpos hp)
  have hsym := budget_finite (encC := eSym) (Option.map eBit) hb
  have hin : ComputableInSpace (fun p : SCfg × Option Bool => input p.1 p.2)
      (encPair eCfg (encOption encBool)) eSym
      (fun p => (encPair eCfg (encOption encBool) p).length) := by
    simpa only [input, decide_eq_true_eq] using
      budget_ite hzero (budget_const none (.refl _)) hsym
  have hctx := budget_prod (budget_prod (budget_const (encB := eDesc) d (.refl _)) hp) hin
  have hstep := budget_comp_linear (of_inO stepWith_inO) hctx
  have hsome : ComputableInSpace Option.isSome eSym encBool
      (fun s => (eSym s).length) := of_inO (ComputableInDegree.isSome encUnary).inO_one
  have hget : ComputableInSpace (fun s : Option ℕ => s.getD 0) eSym encUnary
      (fun s => (eSym s).length) :=
    of_inO (ComputableInDegree.getD (enc₁ := encUnary) 0).inO_one
  have hunary : ComputableInSpace (fun n : ℕ => encUnary n) encUnary encBits
      (fun n => (encUnary n).length) :=
    of_inO (.of_eq fun _ => rfl)
  have hempty := budget_comp_linear
    (of_inO (ComputableInDegree.isEmpty (enc₁ := encBool) (enc := encBits)).inO_one) hunary
  have hbit : ComputableInSpace outputBit encUnary encBool
      (fun n => (encUnary n).length) := by
    refine (budget_finite (encC := encBool) Bool.not hempty).of_enc_eq ?_
    intro n
    cases n <;> simp [outputBit, encUnary_apply]
  have hemit := budget_ite (budget_comp_linear hsome hstep.snd')
    (budget_finite (encC := encBits) (fun b : Bool => [b])
      (budget_comp_linear hbit (budget_comp_linear hget hstep.snd')))
    (budget_const [] (.refl _))
  have hhalt := budget_finite (encC := encBool) Bool.not
    (budget_comp_linear hsome fields_inSpace.fst')
  refine ⟨budget_natPred hpos, hstep.fst', hemit.of_enc_eq ?_,
    hhalt.of_enc_eq ?_, budget_const [] (.refl _)⟩
  · intro p
    change encBits (((stepWith d p.1 (input p.1 p.2)).2.map outputBit).toList) =
      encBits (if _ then _ else _)
    cases (stepWith d p.1 (input p.1 p.2)).2 <;> rfl
  · intro s
    change encBool s.state.isNone = encBool (!s.state.isSome)
    cases s.state <;> rfl

/-- Input-head storage is charged by the actual bounded native input convention, independently
of runtime. This estimate does not assume a free bounded head or alter logspace predicates. -/
theorem length_run_le (d : Desc) (x : List Bool) (t : ℕ) :
    (eCfg ((machine d).run x t)).length ≤
      2 * descLen d + 3 + 2 * (encNat (x.length + 1)).length + 1 +
        3 * (2 * descLen d + 5) * 2 * simSpace d (x.map eBit) t + d.tapes := by
  rw [run_eq]
  simpa only [List.length_map] using length_eCfg_le_space d (x.map eBit) t

/-- On a description of an existing native machine, the workspace term is its own visited-cell
space, rather than a stronger resource premise built into a class definition. -/
theorem length_native_run_le {k : ℕ} {S : Type} [Fintype S]
    (eS : S ↪ ℕ) (tm : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ) :
    (eCfg ((machine (desc eS eBit tm)).run x t)).length ≤
      2 * descLen (desc eS eBit tm) + 3 + 2 * (encNat (x.length + 1)).length + 1 +
        3 * (2 * descLen (desc eS eBit tm) + 5) * 2 *
          (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg x) t).space + k := by
  have h := length_run_le (desc eS eBit tm) x t
  rw [simSpace_desc] at h
  exact h

/-- On an existing binary native machine, output is preserved at every clock. -/
theorem output_native {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ)
    (tm : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ) :
    (machine (desc eS eBit tm)).output x t =
      (tm.runFrom (tm.initCfg x) t).output := by
  have h := simulate_desc eS eBit tm x t
  have ho := congrArg Prod.fst h
  rw [output_eq, show ((stepOut (desc eS eBit tm) (x.map eBit))^[t]
    (init (desc eS eBit tm), [])).2 =
      (tm.runFrom (tm.initCfg x) t).output.map eBit from ho]
  rw [List.map_map]
  have hb : outputBit ∘ eBit = id := by funext b; cases b <;> rfl
  rw [hb, List.map_id]

/-- The complete native configuration is recovered from the saved state and the external
output stream: finite control, input position, work tapes and work-head positions all agree. -/
theorem configuration_native {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ)
    (tm : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ) :
    (tm.runFrom (tm.initCfg x) t).map eS eBit =
      ((machine (desc eS eBit tm)).run x t).toCfg k (x.map eBit)
        (((machine (desc eS eBit tm)).output x t).map eBit) := by
  rw [run_eq, output_native]
  have ho := congrArg Prod.fst (simulate_desc eS eBit tm x t)
  dsimp only [Prod.fst] at ho
  rw [← ho]
  exact (toCfg_iterate eS eBit tm x t).1

/-- The extracted halted flag agrees with native control, at every clock. -/
theorem halted_native {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ)
    (tm : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ) :
    (machine (desc eS eBit tm)).halted ((machine (desc eS eBit tm)).run x t) =
      (tm.runFrom (tm.initCfg x) t).state.isNone := by
  have h := congrArg Prod.snd (simulate_desc eS eBit tm x t)
  change ((machine (desc eS eBit tm)).run x t).state.isNone = _
  rw [run_eq]
  exact h

/-- An ordinary native workspace certificate bounds the saved encoding, with the input head
charged separately. No bound on the size of the output is needed. -/
theorem length_native_run_le_of_space {k : ℕ} {S : Type} [Fintype S]
    (eS : S ↪ ℕ) (tm : MultiTapeTM k Bool S) (x : List Bool) (t s : ℕ)
    (hs : tm.RunsInSpace x s) :
    (eCfg ((machine (desc eS eBit tm)).run x t)).length ≤
      2 * descLen (desc eS eBit tm) + 3 + 2 * (encNat (x.length + 1)).length + 1 +
        3 * (2 * descLen (desc eS eBit tm) + 5) * 2 * s + k := by
  have h := length_native_run_le eS tm x t
  have hb := hs (MultiTapeNTM.ComputationPath.ofDeterministic tm x t)
  change (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg x) t).space ≤ s at hb
  exact h.trans (by gcongr)

/-- The explicit saved-configuration budget extracted from native workspace. -/
noncomputable def budget {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ)
    (tm : MultiTapeTM k Bool S) (n s : ℕ) : ℕ :=
  2 * descLen (desc eS eBit tm) + 3 + 2 * (encNat (n + 1)).length + 1 +
    3 * (2 * descLen (desc eS eBit tm) + 5) * 2 * s + k

/-- Native virtual-input substitution from an existing machine's own first-halt, output and
workspace certificates. The five component certificates and saved-state encoding bound are
derived here, not assumed. Constants are uniform across supplied runtime headers and inputs. -/
theorem computableInSpace {k : ℕ} {S β : Type} [Fintype S] (eS : S ↪ ℕ)
    (tm : MultiTapeTM k Bool S) (encOut : β ↪ List Bool) (f : Simulation.Input → β)
    (T W : Simulation.Input → ℕ)
    (hhalt : ∀ p, (tm.runFrom (tm.initCfg (word p.val.2 p.val.1.1 p.val.1.2.1))
      (T p)).state = none)
    (hpre : ∀ p, ∀ j < T p, (tm.runFrom
      (tm.initCfg (word p.val.2 p.val.1.1 p.val.1.2.1)) j).state ≠ none)
    (hout : ∀ p, encOut (f p) = (tm.runFrom
      (tm.initCfg (word p.val.2 p.val.1.1 p.val.1.2.1)) (T p)).output)
    (hspace : ∀ p, tm.RunsInSpace (word p.val.2 p.val.1.1 p.val.1.2.1) (W p)) :
    ∃ time c, ComputableInTimeAndSpace f Simulation.encInput encOut time
      (fun p => c * (budget eS tm (word p.val.2 p.val.1.1 p.val.1.2.1).length (W p) +
        (encData p.val.1).length + Nat.log2 (Simulation.encInput p).length + 1)) := by
  obtain ⟨hq, hn, he, hh, hf⟩ := components_inSpace (desc eS eBit tm)
  apply Simulation.computableInSpace (machine (desc eS eBit tm)) eCfg
    hq hn he hh hf encOut f T (fun p =>
      budget eS tm (word p.val.2 p.val.1.1 p.val.1.2.1).length (W p))
  · intro p
    rw [halted_native, hhalt]
    rfl
  · intro p j hj
    rw [halted_native]
    have h := hpre p j hj
    generalize (tm.runFrom (tm.initCfg (word p.val.2 p.val.1.1 p.val.1.2.1)) j).state = q at *
    cases q <;> simp_all only [Option.isNone_some, ne_eq, not_true_eq_false]
  · intro p
    rw [output_native]
    exact hout p
  · intro p j _
    exact length_native_run_le_of_space eS tm _ j (W p) (hspace p)

/-- Plain native computation and workspace certificates suffice: the first-halt clock is
selected internally. No time bound, output-length bound or substitution certificate is assumed. -/
theorem computableInSpace_of_computes {k : ℕ} {S β : Type} [Fintype S] (eS : S ↪ ℕ)
    (tm : MultiTapeTM k Bool S) (encOut : β ↪ List Bool) (f : Simulation.Input → β)
    (W : Simulation.Input → ℕ)
    (hcomp : ∀ p, tm.Computes (word p.val.2 p.val.1.1 p.val.1.2.1) (encOut (f p)))
    (hspace : ∀ p, tm.RunsInSpace (word p.val.2 p.val.1.1 p.val.1.2.1) (W p)) :
    ∃ time c, ComputableInTimeAndSpace f Simulation.encInput encOut time
      (fun p => c * (budget eS tm (word p.val.2 p.val.1.1 p.val.1.2.1).length (W p) +
        (encData p.val.1).length + Nat.log2 (Simulation.encInput p).length + 1)) := by
  classical
  have hex (p : Simulation.Input) : ∃ t, (tm.runFrom
      (tm.initCfg (word p.val.2 p.val.1.1 p.val.1.2.1)) t).state = none := by
    obtain ⟨t, ht, _⟩ := hcomp p
    exact ⟨t, ht⟩
  apply computableInSpace eS tm encOut f (fun p => Nat.find (hex p)) W
    (fun p => Nat.find_spec (hex p))
    (fun p j hj => Nat.find_min (hex p) hj) ?_ hspace
  intro p
  obtain ⟨t, ht, ho⟩ := hcomp p
  have hle : Nat.find (hex p) ≤ t := Nat.find_min' (hex p) ht
  rw [tm.runFrom_eq_of_halt _ hle (Nat.find_spec (hex p))] at ho
  exact ho.symm

/-- For each fixed native machine, its budget is linear in workspace plus logarithmic input
length. The bounded input-head convention makes a polynomial-time premise unnecessary. -/
theorem budget_le {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ)
    (tm : MultiTapeTM k Bool S) :
    ∃ C, ∀ n s, budget eS tm n s ≤ C * (s + Nat.log2 n + 1) := by
  refine ⟨2 * descLen (desc eS eBit tm) + 8 + k +
    6 * (2 * descLen (desc eS eBit tm) + 5), fun n s => ?_⟩
  have h := length_encNat_le_log2_add_two (j := n + 1) (N := n) le_rfl
  unfold budget
  nlinarith

/-- Every ordinary native logspace word function admits virtual-input substitution. This
extracts its actual machine without strengthening `ComputableInLogSpace`. The saved-state
budget is linear in its original logarithmic workspace plus the binary input-head cost,
by `budget_le`. Runtime header preparation is still a separate obligation. -/
theorem of_logSpace {β : Type} {f : List Bool → β} {encOut : β ↪ List Bool}
    (hf : ComputableInLogSpace f encBits encOut) :
    ∃ time c a C, ComputableInTimeAndSpace
      (fun p : Simulation.Input => f (word p.val.2 p.val.1.1 p.val.1.2.1))
      Simulation.encInput encOut time
      (fun p => c * (C * (a * (Nat.log2 (word p.val.2 p.val.1.1 p.val.1.2.1).length + 1) +
        Nat.log2 (word p.val.2 p.val.1.1 p.val.1.2.1).length + 1) +
        (encData p.val.1).length + Nat.log2 (Simulation.encInput p).length + 1)) := by
  classical
  obtain ⟨_, a, k, S, _, tm, htm⟩ := hf
  let : Fintype S := Fintype.ofFinite S
  let eS : S ↪ ℕ := (Fintype.equivFin S).toEmbedding.trans Fin.valEmbedding
  obtain ⟨time, c, hc⟩ := computableInSpace_of_computes eS tm encOut
    (fun p : Simulation.Input => f (word p.val.2 p.val.1.1 p.val.1.2.1))
    (fun p => a * (Nat.log2 (word p.val.2 p.val.1.1 p.val.1.2.1).length + 1))
    (fun p => (htm _).1) (fun p => (htm _).2.2)
  obtain ⟨C, hC⟩ := budget_le eS tm
  refine ⟨time, c, a, C, hc.mono (fun _ => le_rfl) fun p => ?_⟩
  apply Nat.mul_le_mul_left
  have h := hC (word p.val.2 p.val.1.1 p.val.1.2.1).length
    (a * (Nat.log2 (word p.val.2 p.val.1.1 p.val.1.2.1).length + 1))
  omega

end Turing.VirtualWord.Native
