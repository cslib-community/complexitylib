/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.Selector
public import CslibFrontier.Computability.Probabilistic.NativeUnboundedExecution
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.SelfDelimiting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Native processing of actual raw concurrent reports

The local algorithm scans the source's self-delimiting concurrent report, skips
canceled calls and arbitrary invoice metadata, and feeds completed candidate masks
into the existing rational retention algorithm. The whole raw report remains
available separately to scheduling code. The native computation ignores supplied
decoded proposals and receives no validity table or desired cover.

The streaming parser is total on raw words. Its agreement with the original
validated parser is established on actual canonical source replies and rejection
packets; no semantic source-validity contract is supplied by a caller.

This is a concrete raw-history local-processing connection for [Wang2027],
Theorem 5(1), PDF p. 12 and Appendix A.5 p. 16 (source interface pp. 4--6).
`Work` uses finite incidence lists, binary rational certificates, a unary number of
opportunities and unbounded raw response words. Native local time/space are
polynomial in these encoded bytes; local instructions do not charge the external
oracle bill or physical duration. `run_native_law` preserves the actual guarded
source law, with arbitrary hidden-state correlation and closed private scheduling.

The input tape still starts with `encWork`. Preparing that input from the live
reader buffer, realizing the scheduler and repeating the native query/stop/output
loop remain open; the native quantitative upper endpoint is not claimed here.
No raw-program termination or divergent-path cost result is strengthened by this
local terminating phase.

## Main results

* `computable_decision`: native compilation of parsing plus rational retention.
* `assemble_run`: equality with actual guarded-program histories, without validity premises.
* `terminal_run`: actual native output/stopping and unchanged full source memory.
* `run_native_law`: joint law of actual raw execution followed by native local processing.
-/

public section
namespace Cslib.Probability.StochasticOracle.NativeRetention.Packets
open ConcurrentBatch Kolmogorov Turing Turing.MultiTapeTM
open Turing.MultiTapeTM.ComputableInPolyTime

/-- Runtime cursor and completed raw response words, newest first. -/
structure Stream where
  /-- Unconsumed packet suffix. -/
  remaining : Word
  /-- Completed response words, excluding canceled and inactive opportunities. -/
  completed : List Word
  deriving DecidableEq

/-- Frame the current suffix and all previously completed raw response words. -/
@[expose] def encStream : Stream ↪ List Bool :=
  ⟨fun s => encPair encBits (encList encBits) (s.remaining, s.completed), by
    intro a b h
    have he := (encPair encBits (encList encBits)).injective h
    cases a
    cases b
    cases he
    rfl⟩

/-- One opportunity slot: skip inactivity, or consume one self-delimited call
report. A completed call contributes its full decoded response, not its invoice. -/
@[expose] def step (s : Stream) : Stream :=
  if s.remaining.headD false then
    let split := decodeSelfDelimiting s.remaining.tail
    ⟨split.2, if split.1.headD false then
      (decodeSelfDelimiting split.1.tail).1 :: s.completed else s.completed⟩
  else ⟨s.remaining.tail, s.completed⟩

/-- Scan the runtime opportunity count, without a fixed response alphabet or
any unary expansion of the reported token counts. -/
@[expose] def scan (n : ℕ) (s : Stream) : Stream :=
  (List.replicate n false).foldl (fun state _ => step state) s

/-- Completed call words in source opportunity order. Rejection packets return none. -/
@[expose] def words (n : ℕ) (packet : Word) : List Word :=
  if packet.headD false then (scan n ⟨packet.tail, []⟩).completed.reverse else []

/-- Enumerate precisely the true membership bits of a runtime candidate mask. -/
@[expose] def indices (m : ℕ) (word : Word) : List ℕ :=
  (List.range m).filter fun j => word[j]?.getD false

/-- Keep only full masks in the original candidate-family representation. -/
@[expose] def families (n m : ℕ) (packet : Word) : List (List ℕ) :=
  (words n packet).flatMap fun word => if decide (word.length = m) then [indices m word] else []

private def fromSlot : Option Word → List Word
  | none => []
  | some call => if call.headD false then [(decodeSelfDelimiting call.tail).1] else []

private theorem scan_slots (n : ℕ) (slots : Fin n → Option Word) (suffix : Word)
    (acc : List Word) :
    scan n ⟨encodeSlots n slots ++ suffix, acc⟩ =
      ⟨suffix, ((List.ofFn slots).flatMap fromSlot).reverse ++ acc⟩ := by
  induction n generalizing suffix acc with
  | zero => simp [scan, encodeSlots]
  | succ n ih =>
    change scan n (step ⟨encodeSlots (n + 1) slots ++ suffix, acc⟩) = _
    cases hs : slots 0 with
    | none =>
      simpa only [encodeSlots, hs, List.cons_append, step, List.headD_cons,
        List.tail_cons, Bool.false_eq_true, ite_false, List.ofFn_succ, List.flatMap_cons,
        fromSlot, List.nil_append] using ih (fun i => slots i.succ) suffix acc
    | some call =>
      simp only [encodeSlots, hs, List.cons_append, step, List.headD_cons,
        List.tail_cons, List.append_assoc, decodeSelfDelimiting_selfDelimitingCode_append,
        List.ofFn_succ, List.flatMap_cons, fromSlot, ite_true]
      split_ifs
      · simpa only [List.singleton_append, List.reverse_cons, List.append_assoc,
          List.singleton_append] using ih (fun i => slots i.succ) suffix
            ((decodeSelfDelimiting call.tail).1 :: acc)
      · simpa only [List.nil_append] using ih (fun i => slots i.succ) suffix acc

private theorem fromSlot_call (report : Option CallReport) :
    fromSlot (report.map encodeCall) = (report.bind fun r => r.1).toList := by
  rcases report with _ | ⟨response, tokens⟩
  · rfl
  · cases response <;> simp [fromSlot, encodeCall]

/-- On every actual canonical report, the native scan recovers all and only the
completed response words, in opportunity order, regardless of invoice lengths. -/
theorem words_report {n : ℕ} (report : Report n) :
    words n (encodeReport report) =
      (List.ofFn report).flatMap (fun r => (r.bind fun receipt => receipt.1).toList) := by
  simp only [words, encodeReport, List.headD_cons, List.tail_cons, ite_true]
  rw [show encodeSlots n (fun i => (report i).map encodeCall) =
    encodeSlots n (fun i => (report i).map encodeCall) ++ [] from (List.append_nil _).symm,
    scan_slots]
  simp only [List.append_nil, List.reverse_reverse]
  rw [show (List.ofFn fun i => (report i).map encodeCall) =
    (List.ofFn report).map (Option.map encodeCall) from
      (List.map_ofFn (f := report) (g := Option.map encodeCall)).symm,
    List.flatMap_map]
  simp only [fromSlot_call]

/-- The guarded source rejection packet contributes no proposed response. -/
theorem words_rejected (n : ℕ) : words n rejection.word = [] := rfl

private theorem indices_mask (m : ℕ) (word : Word) :
    indices m word =
      sourceIndices (Finset.univ.filter fun i : Fin m => word[i.val]?.getD false) := by
  unfold indices sourceIndices
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  rw [← List.filterMap_eq_map, List.filterMap_filter]
  apply List.filterMap_congr
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases hb : word[i.val]?.getD false <;> simp [hb]

private theorem family_word (m : ℕ) (word : Word) :
    (if decide (word.length = m) then [indices m word] else []) =
      ((decodeFamily m word).toList.map sourceIndices) := by
  by_cases h : word.length = m
  · simpa [decodeFamily, h] using congrArg (fun l => [l]) (indices_mask m word)
  · simp [decodeFamily, h]

/-- Original candidate-family decoding and the native index lists agree on every
canonical report, including empty masks, cancellations and arbitrary invoice words. -/
theorem families_report {n m : ℕ} (report : Report n) :
    families n m (encodeReport report) = (proposals m report).map sourceIndices := by
  rw [families, words_report]
  unfold proposals
  rw [show (List.ofFn fun i => (report i).bind
      (fun receipt => receipt.1.bind (decodeFamily m))) =
      (List.ofFn report).map (fun r => r.bind (fun receipt => receipt.1.bind (decodeFamily m))) from
        (List.map_ofFn (f := report)
          (g := fun r => r.bind (fun receipt => receipt.1.bind (decodeFamily m)))).symm]
  rw [List.filterMap_map, List.map_filterMap, List.filterMap_eq_flatMap_toList,
    List.flatMap_assoc]
  apply congrArg (List.flatMap · (List.ofFn report))
  funext receipt
  cases receipt with
  | none => rfl
  | some receipt =>
    obtain ⟨response, tokens⟩ := receipt
    cases response with
    | none => rfl
    | some word => simpa [Option.toList_map] using family_word m word

/-- Rejected requests introduce no candidate family, including zero candidates. -/
theorem families_rejected (n m : ℕ) : families n m rejection.word = [] := rfl

private theorem pack_computable : ComputableInPolyTime
    (fun p : Word × List Word => Stream.mk p.1 p.2)
    (encPair encBits (encList encBits)) encStream := .of_eq fun _ => rfl

private theorem fields_computable : ComputableInPolyTime
    (fun s : Stream => (s.remaining, s.completed)) encStream
    (encPair encBits (encList encBits)) := .of_eq fun _ => rfl

private theorem remaining_computable : ComputableInPolyTime Stream.remaining encStream encBits :=
  fields_computable.fst'
private theorem completed_computable : ComputableInPolyTime Stream.completed encStream
    (encList encBits) := fields_computable.snd'
attribute [local fun_prop] remaining_computable completed_computable

private theorem step_computable : ComputableInPolyTime step encStream encStream := by
  unfold step
  apply ComputableInPolyTime.ite (by fun_prop)
  · have hl : ComputableInPolyTime
        (fun s : Stream => (decodeSelfDelimiting s.remaining.tail).2) encStream encBits := by
      fun_prop
    have hr : ComputableInPolyTime (fun s : Stream =>
        if (decodeSelfDelimiting s.remaining.tail).1.headD false then
          (decodeSelfDelimiting (decodeSelfDelimiting s.remaining.tail).1.tail).1 :: s.completed
        else s.completed) encStream (encList encBits) := by
      apply ComputableInPolyTime.ite (by fun_prop) <;> fun_prop
    exact pack_computable.comp (hl.prod hr)
  · have ht : ComputableInPolyTime (fun s : Stream => s.remaining.tail) encStream encBits := by
      fun_prop
    exact pack_computable.comp (ht.prod completed_computable)

private theorem step_size (s : Stream) :
    (encStream (step s)).length ≤ (encStream s).length + 1 := by
  have hs := decodeSelfDelimiting_length_le s.remaining.tail
  have hc := decodeSelfDelimiting_length_le (decodeSelfDelimiting s.remaining.tail).1.tail
  simp only [List.length_tail] at hs hc
  change (encPair encBits (encList encBits) ((step s).remaining, (step s).completed)).length ≤
    (encPair encBits (encList encBits) (s.remaining, s.completed)).length + 1
  simp only [length_encPair, encBits_apply]
  by_cases htop : s.remaining.head?.getD false = true <;>
    by_cases hcall : (decodeSelfDelimiting s.remaining.tail).1.head?.getD false = true <;>
    simp [step, List.headD_eq_head?_getD, htop, hcall, encList_cons, length_frame] <;> omega

/-- The complete streaming scan has a derived native polynomial local time/space
certificate on its entire encoded runtime data; no accumulator bound is supplied. -/
theorem computable_scan : ComputableInPolyTime
    (fun ((n, s) : ℕ × Stream) => scan n s) (encPair encUnary encStream) encStream := by
  unfold scan
  have hl : ComputableInPolyTime (fun p : ℕ × Stream => List.replicate p.1 false)
      (encPair encUnary encStream) (encList encBool) := by fun_prop
  have hi : ComputableInPolyTime (fun p : ℕ × Stream => p.2)
      (encPair encUnary encStream) encStream := by fun_prop
  have ht : ComputableInPolyTime (fun p : ((ℕ × Stream) × Stream) × Bool => step p.1.2)
      (encPair (encPair (encPair encUnary encStream) encStream) encBool) encStream :=
    step_computable.comp (by fun_prop)
  exact foldlWithInput_of_bounded_growth hi
    ⟨hl, ht, inferInstance, inferInstance⟩
    (growth := fun _ => 1) ⟨.const 1, fun _ s _ _ => step_size s⟩

private theorem words_computable : ComputableInPolyTime
    (fun ((n, packet) : ℕ × Word) => words n packet) (encPair encUnary encBits)
    (encList encBits) := by
  unfold words
  apply ComputableInPolyTime.ite (by fun_prop)
  · have hp : ComputableInPolyTime (fun p : ℕ × Word => (p.2.tail, ([] : List Word)))
        (encPair encUnary encBits) (encPair encBits (encList encBits)) := by fun_prop
    have hs := computable_scan.comp
      ((ComputableInPolyTime.fst encUnary encBits).prod (pack_computable.comp hp))
    exact listReverseWithInput (completed_computable.comp hs)
  · fun_prop

private theorem indices_computable : ComputableInPolyTime
    (fun ((m, word) : ℕ × Word) => indices m word) (encPair encUnary encBits)
    (encList encUnary) := by
  unfold indices
  apply filterWithInput (by fun_prop)
  fun_prop

/-- Parse runtime opportunity/candidate counts and a raw concurrent packet using
one uniform native polynomial-time local algorithm. -/
theorem computable_families : ComputableInPolyTime
    (fun ((n, m, packet) : ℕ × ℕ × Word) => families n m packet)
    (encPair encUnary (encPair encUnary encBits)) (encList (encList encUnary)) := by
  unfold families
  have hw : ComputableInPolyTime (fun p : ℕ × ℕ × Word => words p.1 p.2.2)
      (encPair encUnary (encPair encUnary encBits)) (encList encBits) :=
    words_computable.comp ((by fun_prop : ComputableInPolyTime
      (fun p : ℕ × ℕ × Word => p.1) _ encUnary).prod (by fun_prop))
  apply flatMapWithInput hw
  apply ComputableInPolyTime.ite (by fun_prop)
  · have hi := indices_computable.comp (show ComputableInPolyTime
        (fun p : (ℕ × ℕ × Word) × Word => (p.1.2.1, p.2))
        (encPair (encPair encUnary (encPair encUnary encBits)) encBits)
        (encPair encUnary encBits) from by fun_prop)
    fun_prop
  · fun_prop

/-- On every actually supported reply of the original guarded source handler,
the runtime native parser agrees with its validated candidate-family decoder.
Source validity is derived by cases on the actual guard and joint response law. -/
theorem serve_families {n : ℕ} {Private : Type} (limits : Limits n)
    (sample : Sampler n Private) (request : Word) (state : ServerState n Private)
    (reply : NativeOpenExecution.Reply) (next : ServerState n Private)
    (hs : (reply, next) ∈ (serve limits sample request state).support) (m : ℕ) :
    families n m reply.word = (parseProposals n m reply.word).map sourceIndices := by
  cases ha : admit limits state request with
  | none =>
    rw [serve_rejected _ _ _ _ ha, PMF.mem_support_pure_iff, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    rfl
  | some batch =>
    rw [serve_accepted _ _ _ _ _ ha, PMF.mem_support_map_iff] at hs
    obtain ⟨⟨paths, privateState⟩, _, he⟩ := hs
    cases he
    exact (families_report _).trans (by rw [replyOf, parseProposals_report])

/-- Runtime original instance and raw response history. No decoded family,
local acceptance table or desired completion flag is part of this input. -/
structure Work where
  /-- Original rational data; its supplied proposal list is ignored. -/
  system : NativeRetention.Input
  /-- Number of source call opportunities. -/
  opportunities : ℕ
  /-- Actual raw responses, newest first, including rejection packets. -/
  history : List Word
  deriving DecidableEq

/-- The complete local-processing ABI: framed original instance, unary opportunity
count and framed list of full raw response words. -/
@[expose] def encWork : Work ↪ List Bool :=
  ⟨fun w => encPair encInput (encPair encUnary (encList encBits))
      (w.system, w.opportunities, w.history), by
    intro a b h
    have he := (encPair encInput (encPair encUnary (encList encBits))).injective h
    cases a
    cases b
    cases he
    rfl⟩

/-- Construct retention input from the original rows and chronologically parsed
raw packets, ignoring any caller-provided decoded proposals. -/
@[expose] def assemble (w : Work) : NativeRetention.Input :=
  { w.system with proposals :=
      w.history.reverse.flatMap (families w.opportunities w.system.rows.length) }

/-- The complete runtime local decision: exact rational retention, original-mask
output and a completion flag computed from original coverage. -/
@[expose] def decision (w : Work) : Bool × Word :=
  (complete (assemble w), output (assemble w))

/-- The stored original input, opportunity count and raw history can be read uniformly
from the runtime work encoding, without recompiling them as fixed context. -/
theorem work_fields : ComputableInPolyTime
    (fun w : Work => (w.system, w.opportunities, w.history)) encWork
    (encPair encInput (encPair encUnary (encList encBits))) := .of_eq fun _ => rfl
private theorem system_computable : ComputableInPolyTime Work.system encWork encInput :=
  work_fields.fst'
private theorem opportunities_computable : ComputableInPolyTime Work.opportunities encWork
    encUnary := work_fields.snd'.fst'
private theorem history_computable : ComputableInPolyTime Work.history encWork
    (encList encBits) := work_fields.snd'.snd'
attribute [local fun_prop] system_computable opportunities_computable history_computable

private theorem original_fields : ComputableInPolyTime (fun w : Work =>
    (w.system.rows, w.system.weights, w.system.dual, w.system.rho, w.system.proposals)) encWork
    (encPair (encList (encList encUnary)) (encPair (encList encRatBin)
      (encPair (encList encRatBin) (encPair encRatBin (encList (encList encUnary)))))) :=
  (ComputableInPolyTime.of_eq (f := fun x : NativeRetention.Input =>
    (x.rows, x.weights, x.dual, x.rho, x.proposals)) (encIn := encInput) (encOut :=
      encPair (encList (encList encUnary)) (encPair (encList encRatBin)
        (encPair (encList encRatBin) (encPair encRatBin (encList (encList encUnary))))))
      (fun _ => rfl)).comp system_computable

/-- The raw-packet preparation is itself compiled native code, including parsing
all runtime opportunity slots and formatting the original retention input. -/
theorem computable_assemble : ComputableInPolyTime assemble encWork encInput := by
  have hr := original_fields.fst'
  have hw := original_fields.snd'.fst'
  have hd := original_fields.snd'.snd'.fst'
  have hf := original_fields.snd'.snd'.snd'.fst'
  have hp : ComputableInPolyTime
      (fun w : Work => w.history.reverse.flatMap (families w.opportunities w.system.rows.length))
      encWork (encList (encList encUnary)) := by
    apply flatMapWithInput (listReverseWithInput history_computable)
    have hn := opportunities_computable.comp (ComputableInPolyTime.fst encWork encBits)
    have hrows := hr.comp (ComputableInPolyTime.fst encWork encBits)
    have hm : ComputableInPolyTime (fun p : Work × Word => p.1.system.rows.length)
        (encPair encWork encBits) encUnary := by fun_prop
    exact computable_families.comp
      (hn.prod (hm.prod (ComputableInPolyTime.snd encWork encBits)))
  have hpack : ComputableInPolyTime
      (fun p : List (List ℕ) × List ℚ × List ℚ × ℚ × List (List ℕ) =>
        let (rows, weights, dual, rho, proposals) := p
        NativeRetention.Input.mk rows weights dual rho proposals)
      (encPair (encList (encList encUnary)) (encPair (encList encRatBin)
        (encPair (encList encRatBin) (encPair encRatBin (encList (encList encUnary))))))
      encInput := .of_eq fun _ => rfl
  exact hpack.comp (hr.prod (hw.prod (hd.prod (hf.prod hp))))

/-- One uniform actual native computation processes full raw concurrent packets,
performs rational retention and emits the completion flag/source mask. Polynomial
local time and space are derived in all encoded runtime bytes. -/
theorem computable_decision : ComputableInPolyTime decision encWork (encPair encBool encBits) :=
  NativeRetention.computable_decision.comp computable_assemble

/-- Actual native code compiled for the raw-history decision ABI. Its certificate
is constructed from `computable_decision`, rather than supplied by a caller. -/
structure Compiled where
  /-- Number of native work tapes. -/
  tapes : ℕ
  /-- Native finite control type. -/
  Control : Type
  /-- Finiteness of the control, with unbounded runtime histories. -/
  finiteControl : Finite Control
  /-- Actual deterministic binary multitape code. -/
  machine : Turing.MultiTapeTM tapes Bool Control
  /-- Uniform local instruction bound. -/
  time : ℕ → ℕ
  /-- Uniform local workspace bound. -/
  space : ℕ → ℕ
  /-- Derived polynomial time bound. -/
  time_polynomial : Cslib.PolynomiallyBounded time
  /-- Derived polynomial workspace bound. -/
  space_polynomial : Cslib.PolynomiallyBounded space
  /-- Exact raw-history decision on every runtime input. -/
  correct : machine.ComputesFunInTimeAndSpace encWork (encPair encBool encBits) decision
    (fun w => time (encWork w).length) (fun w => space (encWork w).length)

private theorem compiled_exists : Nonempty Compiled := by
  obtain ⟨t, s, ht, hs, k, S, hS, M, hM⟩ := computable_decision
  exact ⟨⟨k, S, hS, M, t, s, ht, hs, hM⟩⟩

/-- One fixed native code witness extracted from the proved compilation. -/
noncomputable def compiled : Compiled := Classical.choice compiled_exists

noncomputable section
open NativeOpenExecution

/-- Every actual reply in a supported raw program history is parsed identically
by the native runtime algorithm and the original validated source decoder. The
statement quantifies arbitrary private randomized scheduling and hidden state. -/
theorem run_packets {n : ℕ} {Private : Type} (limits : Limits n)
    (sample : Sampler n Private) (choose : Selector.Scheduler n) (x : NativeRetention.Input)
    (budget : ℕ) (seed : Private) (s : Selector.State)
    (memory : Memory Unit (ServerState n Private))
    (hs : (s, memory) ∈ (Selector.execute (environment limits sample)
      (Selector.run choose x budget) ⟨ConcurrentBatch.initial seed, []⟩).support) :
    ∀ packet ∈ s.history,
      families n x.rows.length packet =
        (parseProposals n x.rows.length packet).map sourceIndices := by
  let good : Memory Unit (ServerState n Private) → Prop := fun state =>
    ∀ event ∈ state.events, families n x.rows.length event.reply.word =
      (parseProposals n x.rows.length event.reply.word).map sourceIndices
  have hg : good memory := by
    apply ProbOracleComp.run_interpret_invariant (handler (environment limits sample))
      good ?_ (Selector.run choose x budget) _ ?_ s memory hs
    · intro q state hi word next ht
      obtain ⟨⟨reply, privateState⟩, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
      cases he
      intro event hevent
      rcases List.mem_cons.mp hevent with rfl | hevent
      · exact serve_families limits sample q.2 state.privateState reply privateState hr _
      · exact hi event hevent
    · intro event hevent
      cases hevent
  have hc := (Selector.run_invariant limits sample choose x budget seed s memory hs).2
  intro packet hp
  rw [hc.1, List.mem_map] at hp
  obtain ⟨event, he, rfl⟩ := hp
  exact hg event he

/-- The computed raw-packet retention input agrees with the complete actual raw
selector program, at every supported stopping or intermediate budget. Initial
proposal data cannot introduce families absent from the oracle history. -/
theorem assemble_run {n : ℕ} {Private : Type} (limits : Limits n)
    (sample : Sampler n Private) (choose : Selector.Scheduler n) (x : NativeRetention.Input)
    (budget : ℕ) (seed : Private) (s : Selector.State)
    (memory : Memory Unit (ServerState n Private))
    (hs : (s, memory) ∈ (Selector.execute (environment limits sample)
      (Selector.run choose x budget) ⟨ConcurrentBatch.initial seed, []⟩).support) :
    assemble ⟨x, n, s.history⟩ = Selector.data n x s := by
  have hp := run_packets limits sample choose x budget seed s memory hs
  have he : s.history.reverse.flatMap (families n x.rows.length) =
      s.history.reverse.flatMap (fun packet =>
        (parseProposals n x.rows.length packet).map sourceIndices) := by
    apply List.flatMap_congr
    intro packet hpacket
    exact hp packet (List.mem_reverse.mp hpacket)
  simp only [assemble, Selector.data, he, List.map_flatMap]

/-- The compiled raw-history decision is an ordinary open native machine. -/
def native : MultiTapePTM compiled.tapes Bool compiled.Control Unit :=
  MultiTapePTM.ofDeterministic compiled.machine

/-- Native local entry ABI, preserving all existing oracle memory. This entry
still needs to be prepared by the online reply-buffer/query loop. -/
@[expose] def start {Private : Type} (w : Work) (memory : Memory Unit Private) :
    World compiled.tapes compiled.Control Unit Private (encWork w) :=
  ⟨native.initialConfig (encWork w), memory⟩

/-- Actual clocked native configuration, with unchanged external memory. -/
@[expose] def done {Private : Type} (w : Work) (memory : Memory Unit Private) (t : ℕ) :
    World compiled.tapes compiled.Control Unit Private (encWork w) :=
  ⟨{ (start w memory).config with
      tapes := compiled.machine.runFrom (compiled.machine.initCfg (encWork w)) t }, memory⟩

/-- All runtime packet parsing and rational retention execute silently on the
actual native code; the same hidden memory, invoices and physical duration persist. -/
theorem execute_decision {Private : Type} (env : Environment Unit Private)
    (w : Work) (memory : Memory Unit Private) (t : ℕ) :
    execute native env t (start w memory) = PMF.pure (done w memory t) := by
  unfold execute
  change ((OracleComp.interpret
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (handler env))
    ((MultiTapePTM.ofDeterministic compiled.machine).runOracleConfigFrom t
      (start w memory).config)).run memory).map _ = _
  rw [MultiTapePTM.run_interpret_runOracleConfigFrom_ofDeterministic, PMF.pure_map]
  rfl

/-- Actual unbounded execution of the native raw-history decision terminates
with exactly the computed flag and mask. There is no local divergent mass and
no assumed native realization or resource conclusion. -/
theorem terminal_decision {Private : Type} (env : Environment Unit Private)
    (w : Work) (memory : Memory Unit Private) :
    ∃ t, NativeUnboundedExecution.terminal native env (start w memory) =
        PMF.pure (some (done w memory t)) ∧
      (done w memory t).config.tapes.output = (encPair encBool encBits) (decision w) := by
  obtain ⟨t, ht, ho⟩ := (compiled.correct w).1
  refine ⟨t, ?_, ho⟩
  have hh : NativeUnboundedExecution.halted (done w memory t) := ht
  have hm : 1 ≤ NativeUnboundedExecution.terminal native env (start w memory)
      (some (done w memory t)) := by
    change 1 ≤ ⨆ fuel, StoppedProcess.stopped (NativeOpenExecution.step native env)
      NativeUnboundedExecution.halted fuel (start w memory) (done w memory t)
    apply le_iSup_of_le t
    simp only [StoppedProcess.stopped, hh, ite_true, ← execute_eq_stateLaw,
      execute_decision, PMF.pure_apply, le_refl]
  have hm' := le_antisymm (PMF.coe_le_one _ _) hm
  have hs := (PMF.apply_eq_one_iff _ _).mp hm'
  ext result
  by_cases hz : result = some (done w memory t)
  · subst result
    simp [hm', PMF.pure_apply]
  · have hzero : NativeUnboundedExecution.terminal native env (start w memory) result = 0 :=
      (PMF.apply_eq_zero_iff _ _).mpr (by rw [hs]; simpa using hz)
    simp [hzero, PMF.pure_apply, hz]

/-- Integrated actual-source/raw-history/native-local endpoint, for arbitrary
private adaptive scheduling and correlated source responses. The native code
computes the program's own stopping flag and output; its external ledgers and
hidden state are unchanged. This does not compile the online scheduling loop. -/
theorem terminal_run {n : ℕ} {Private : Type} (limits : Limits n)
    (sample : Sampler n Private) (choose : Selector.Scheduler n) (x : NativeRetention.Input)
    (budget : ℕ) (seed : Private) (s : Selector.State)
    (memory : Memory Unit (ServerState n Private))
    (hs : (s, memory) ∈ (Selector.execute (environment limits sample)
      (Selector.run choose x budget) ⟨ConcurrentBatch.initial seed, []⟩).support) :
    let w : Work := ⟨x, n, s.history⟩
    ∃ t, NativeUnboundedExecution.terminal native (environment limits sample) (start w memory) =
        PMF.pure (some (done w memory t)) ∧
      (done w memory t).config.tapes.output = (encPair encBool encBits)
        (complete (Selector.data n x s), output (Selector.data n x s)) ∧
      (done w memory t).memory = memory := by
  obtain ⟨t, ht, ho⟩ := terminal_decision (environment limits sample) ⟨x, n, s.history⟩ memory
  refine ⟨t, ht, ?_, rfl⟩
  simpa only [decision, assemble_run limits sample choose x budget seed s memory hs] using ho

/-- Observe actual native local stopping, its emitted word and the entire
unchanged oracle state. `none` retains its usual meaning of native divergence. -/
@[expose] def process {Private : Type} (env : Environment Unit Private)
    (w : Work) (memory : Memory Unit Private) : PMF (Option (Word × Memory Unit Private)) :=
  (NativeUnboundedExecution.terminal native env (start w memory)).map
    (Option.map fun final => (final.config.tapes.output, final.memory))

/-- The native processor has the exact joint word/memory law, not merely a
correct-output predicate on supported paths. -/
theorem process_eq {Private : Type} (env : Environment Unit Private)
    (w : Work) (memory : Memory Unit Private) :
    process env w memory = PMF.pure (some ((encPair encBool encBits) (decision w), memory)) := by
  obtain ⟨t, ht, ho⟩ := terminal_decision env w memory
  simp only [process, ht, PMF.pure_map, Option.map_some, ho]
  rfl

/-- Exact whole-law connection between the actual adaptive raw program and its
native raw-history decision processor. This is composition of the two execution
laws, not a theorem that a single native online loop implements their composition.
The full raw client state is retained in the joint law as context, including its
private word and requests. This does not place that state on native work tapes.
Correlated source state and joint resources remain in the same oracle memory;
no finite response alphabet is imposed. -/
theorem run_native_law {n : ℕ} {Private : Type} (limits : Limits n)
    (sample : Sampler n Private) (choose : Selector.Scheduler n) (x : NativeRetention.Input)
    (budget : ℕ) (seed : Private) :
    (Selector.execute (environment limits sample) (Selector.run choose x budget)
      ⟨ConcurrentBatch.initial seed, []⟩).bind (fun (s, memory) =>
        (process (environment limits sample) ⟨x, n, s.history⟩ memory).map (s, ·)) =
      (Selector.execute (environment limits sample) (Selector.run choose x budget)
        ⟨ConcurrentBatch.initial seed, []⟩).map (fun (s, memory) =>
          (s, some ((encPair encBool encBits)
            (complete (Selector.data n x s), output (Selector.data n x s)), memory))) := by
  rw [PMF.map]
  apply PMF.bind_congr_on_support
  intro pair hs
  obtain ⟨s, memory⟩ := pair
  change (process (environment limits sample) ⟨x, n, s.history⟩ memory).map (s, ·) =
    PMF.pure (s, some ((encPair encBool encBits)
      (complete (Selector.data n x s), output (Selector.data n x s)), memory))
  rw [process_eq, PMF.pure_map]
  congr 1
  simp only [decision, assemble_run limits sample choose x budget seed s memory hs]

end
end Cslib.Probability.StochasticOracle.NativeRetention.Packets
