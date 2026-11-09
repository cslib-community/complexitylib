/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.ReadMachine.VirtualWord.Runtime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible

/-!
# Native repeated evaluation of a virtual input

A Boolean-state consumer scans the whole virtual word twice, retaining its state across reads
and across the pass boundary. The length is unbounded. Each outer address is translated to an
original-tail address and the runtime accessor selects its prefix/suffix bit before resuming the
consumer. Only the runtime header, its offset, a binary scan counter and one Boolean are stored.
The virtual word is a specification, never a workspace object. Constants are independent of
runtime cut, suffix and address. The supplied header's address field is ignored by the consumer.

This original implementation supports the QUERY-GENERATOR/EVALUATOR recomputation in the proof
of Lemma 3.3, expanded ECCC TR13-047, printed page 6
[GlasserNguyenReitwiessnerSelmanWitek2013]. Definitions 3.1–3.2 concern general logspace
transducers; this module handles only a two-pass Boolean-state evaluator. Generic native
predicate substitution, preparing the supplied header from a generator, regenerating answers,
the resource-certified suffix loop and adaptive-to-tt conversion remain unproved here.
-/

public section

namespace Turing.VirtualWord.Evaluator

open MultiTapeTM ComputableInSpace

/-- The declared virtual length; for valid cuts this is the reconstructed word's length. -/
@[expose] def width (d : Data) : ℕ := d.1 + d.2.1.length

/-- Runtime accessor state, binary consumer position, and saved Boolean evaluator state. -/
abbrev State := Runtime.State × ℕ × Bool

/-- Charge all retained data, including the suspended consumer state. -/
abbrev encState : State ↪ List Bool :=
  encPair Runtime.encState (encPair encNat encBool)

/-- Runtime data recovered from the retained small header. -/
@[expose] def data (s : State) : Data := Runtime.decode s.1.header.reverse

/-- The outer read address, reset at each pass boundary. -/
@[expose] def address (s : State) : ℕ := s.2.1 % width (data s)

/-- One translated read, using exactly the runtime accessor's selector. -/
@[expose] def bit (s : State) (b : Option Bool) : Bool :=
  answer ((data s).1, (data s).2.1, address s) (b.getD false)

/-- A fixed consumer; its transition table is finite and independent of runtime parameters.
The accessor's initialization read is retained, then every evaluation read resumes the saved
Boolean state. A zero-width word halts immediately after initialization. -/
@[expose] def machine (δ : Bool × Bool → Bool) : QueryMachine State where
  init := (Runtime.machine.init, 0, false)
  query s := if Runtime.machine.halted s.1 then s.1.cursor + address s
    else Runtime.machine.query s.1
  next p := if Runtime.machine.halted p.1.1 then
      (p.1.1, p.1.2.1 + 1, δ (p.1.2.2, bit p.1 p.2))
    else (Runtime.machine.next (p.1.1, p.2), p.1.2)
  emit _ := []
  halted s := Runtime.machine.halted s.1 && !(decide (s.2.1 < 2 * width (data s)))
  finish s := [s.2.2]

/-- Reference evaluation, defined by successive reads rather than constructing the word. -/
@[expose] def value (δ : Bool × Bool → Bool) (p : Runtime.Input) : ℕ → Bool
  | 0 => false
  | k + 1 => δ (value δ p k,
      answer (p.1.1, p.1.2.1, k % width p.1) (p.2.getD (k % width p.1) false))

/-- The finite evaluator's result after two complete passes. -/
@[expose] def evaluate (δ : Bool × Bool → Bool) (p : Runtime.Input) : Bool :=
  value δ p (2 * width p.1)

/-- The initialized accessor is held fixed while the consumer runs. -/
@[expose] def loaded (p : Runtime.Input) : Runtime.State :=
  (((encData p.1).reverse, 2 * (encData p.1).length + 1), false, true,
    some (p.2.getD p.1.address false))

/-- Initialization has exactly the accessor's states, with a constant suspended consumer. -/
theorem run_initializing (δ : Bool × Bool → Bool) (p : Runtime.Input) {t : ℕ}
    (ht : t ≤ 2 * (encData p.1).length + 2) :
    (machine δ).run (Runtime.encInput p) t =
      (Runtime.machine.run (Runtime.encInput p) t, 0, false) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.run_succ, ih (by omega)]
    have h := (Runtime.first_halt p).2 t (by omega)
    simp only [QueryMachine.step, machine, h, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, QueryMachine.read, QueryMachine.run_succ]

/-- Every consumer read is redirected to the original read-only tail. -/
theorem read_loaded (δ : Bool × Bool → Bool) (p : Runtime.Input) (k : ℕ) (a : Bool) :
    (machine δ).read (Runtime.encInput p) (loaded p, k, a) =
      p.2[k % width p.1]? := by
  change (frame (encData p.1) ++ p.2)[(machine δ).query (loaded p, k, a)]? = _
  simp only [machine, loaded, Runtime.machine, Runtime.State.bit, Option.isSome_some,
    ↓reduceIte, Runtime.State.cursor, address, data, Runtime.State.header,
    List.reverse_reverse, Runtime.decode_encData]
  rw [List.getElem?_append_right (by simp)]
  simp

/-- The unbounded read-loop invariant: exactly one finite transition per virtual bit. -/
theorem run_scanning (δ : Bool × Bool → Bool) (p : Runtime.Input) {k : ℕ}
    (hk : k ≤ 2 * width p.1) :
    (machine δ).run (Runtime.encInput p) (2 * (encData p.1).length + 2 + k) =
      (loaded p, k, value δ p k) := by
  induction k with
  | zero => rw [Nat.add_zero, run_initializing δ p le_rfl, Runtime.run_halted]; rfl
  | succ k ih =>
    rw [show 2 * (encData p.1).length + 2 + (k + 1) =
      (2 * (encData p.1).length + 2 + k) + 1 by omega,
      QueryMachine.run_succ, ih (by omega)]
    have hlt : k < 2 * width p.1 := by omega
    have hd : data (loaded p, k, value δ p k) = p.1 := by
      simp only [data, loaded, Runtime.State.header, List.reverse_reverse, Runtime.decode_encData]
    have hh : (machine δ).halted (loaded p, k, value δ p k) = false := by
      simp only [machine, hd]
      have hr : Runtime.machine.halted (loaded p) = true := rfl
      rw [hr]
      simp only [hlt, decide_true, Bool.not_true, Bool.true_and]
    rw [QueryMachine.step, hh]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [read_loaded]
    simp only [machine, loaded, Runtime.machine, Runtime.State.bit, Option.isSome_some,
      ↓reduceIte, bit, address, data, Runtime.State.header, List.reverse_reverse,
      Runtime.decode_encData, value, List.getD_eq_getElem?_getD]

/-- Exact first halt, including the empty virtual word. -/
theorem first_halt (δ : Bool × Bool → Bool) (p : Runtime.Input) :
    let T := 2 * (encData p.1).length + 2 + 2 * width p.1
    (machine δ).halted ((machine δ).run (Runtime.encInput p) T) = true ∧
      ∀ t < T, (machine δ).halted ((machine δ).run (Runtime.encInput p) t) = false := by
  dsimp only
  constructor
  · rw [run_scanning δ p le_rfl]
    simp only [machine, loaded, data, Runtime.machine, Runtime.State.bit,
      Runtime.State.header, List.reverse_reverse, Runtime.decode_encData, Option.isSome_some,
      lt_self_iff_false, decide_false, Bool.not_false, Bool.and_self]
  · intro t ht
    by_cases hi : t < 2 * (encData p.1).length + 2
    · rw [run_initializing δ p (by omega)]
      simp only [machine, (Runtime.first_halt p).2 t hi, Bool.false_and]
    · rw [show t = 2 * (encData p.1).length + 2 +
        (t - (2 * (encData p.1).length + 2)) by omega, run_scanning δ p (by omega)]
      simp only [machine, loaded, data, Runtime.machine, Runtime.State.bit,
        Runtime.State.header, List.reverse_reverse, Runtime.decode_encData, Option.isSome_some,
        show t - (2 * (encData p.1).length + 2) < 2 * width p.1 by omega,
        decide_true, Bool.not_true, Bool.true_and]

/-- The actual machine emits the evaluator result, without accumulating a virtual input. -/
theorem output (δ : Bool × Bool → Bool) (p : Runtime.Input) :
    (machine δ).output (Runtime.encInput p)
      (2 * (encData p.1).length + 2 + 2 * width p.1) = [evaluate δ p] := by
  unfold QueryMachine.output
  simp only [show (machine δ).emit = fun _ => [] from rfl, ite_self, List.map_const',
    List.flatten_replicate_nil, List.nil_append]
  rw [run_scanning δ p le_rfl]
  rfl

/-- For valid cuts the consumer transition reads exactly the reconstructed virtual word.
The modulo counter scans each address once per pass when the word is nonempty. -/
theorem value_word (δ : Bool × Bool → Bool) (cut : ℕ) (suffix x : List Bool)
    (hc : cut ≤ x.length) (k : ℕ) :
    value δ ((cut, suffix, 0), x) (k + 1) =
      δ (value δ ((cut, suffix, 0), x) k,
        (word x cut suffix).getD (k % (word x cut suffix).length) false) := by
  rw [value, answer_eq_getD x cut suffix _ hc, length_word x cut suffix hc]
  rfl

/-- Header decoding is native in the charged consumer state. -/
theorem data_inSpace : ComputableInSpace data encState encData
    (fun s => (encState s).length) := by
  have hr : ComputableInSpace List.reverse encBits encBits (fun w => w.length) :=
    of_inO ComputableInDegree.bitsReverse.inO_one
  unfold data
  exact budget_comp_linear Runtime.decode_inSpace
    (budget_comp_linear hr (fst _ _).fst'.fst')

/-- The virtual length is computed from binary cut and the stored suffix only. -/
theorem width_inSpace : ComputableInSpace (fun s => width (data s)) encState encNat
    (fun s => (encState s).length) := by
  have hl : ComputableInSpace List.length encBits encNat (fun w => w.length) :=
    (of_inO ComputableInO.lengthNat).weaken (.of_le_linear 1 1 fun _ => by omega)
  exact budget_natAdd data_inSpace.fst'
    (budget_comp_linear hl data_inSpace.snd'.fst')

/-- The outer scan address is binary, even for unbounded virtual lengths. -/
theorem address_inSpace : ComputableInSpace address encState encNat
    (fun s => (encState s).length) := budget_natMod (snd _ _).fst' width_inSpace

/-- All five consumer components have actual native linear-space realizations. -/
theorem components_inSpace (δ : Bool × Bool → Bool) :
    ComputableInSpace (machine δ).query encState encNat (fun s => (encState s).length) ∧
    ComputableInSpace (machine δ).next (encPair encState (encOption encBool)) encState
      (fun p => (encPair encState (encOption encBool) p).length) ∧
    ComputableInSpace (machine δ).emit (encPair encState (encOption encBool)) encBits
      (fun p => (encPair encState (encOption encBool) p).length) ∧
    ComputableInSpace (machine δ).halted encState encBool (fun s => (encState s).length) ∧
    ComputableInSpace (machine δ).finish encState encBits (fun s => (encState s).length) := by
  have hs := fst Runtime.encState (encPair encNat encBool)
  have hh := budget_comp_linear Runtime.halted_inSpace hs
  have hq := budget_ite hh (budget_natAdd hs.fst'.snd' address_inSpace)
    (budget_comp_linear Runtime.query_inSpace hs)
  have hn := budget_natLt (snd _ _).fst' (budget_natAdd width_inSpace width_inSpace)
  have hhalt := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && !p.2)
    (budget_prod hh hn)
  have hfinish := budget_finite (encC := encBits) (fun b => [b])
    (snd Runtime.encState (encPair encNat encBool)).snd'
  have hp := fst encState (encOption encBool)
  have hd := budget_comp_linear data_inSpace hp
  have ha := budget_comp_linear address_inSpace hp
  have hb := budget_finite (encC := encBool) (fun b : Option Bool => b.getD false)
    (snd encState (encOption encBool))
  have hbit := budget_comp_linear answer_inSpace
    (budget_prod (budget_prod hd.fst' (budget_prod hd.snd'.fst' ha)) hb)
  have hδ := budget_finite (encC := encBool) δ (budget_prod hp.snd'.snd' hbit)
  have hready := budget_comp_linear Runtime.halted_inSpace hp.fst'
  have hnext := budget_ite hready
    (budget_prod hp.fst' (budget_prod (budget_natSucc hp.snd'.fst') hδ))
    (budget_prod (budget_comp_linear Runtime.next_inSpace
      (budget_prod hp.fst' (snd encState (encOption encBool)))) hp.snd')
  refine ⟨hq, hnext, budget_const [] (.refl _), ?_, hfinish⟩
  simpa only [machine, two_mul] using hhalt

/-- Explicit encoding cost: saved accessor state, binary loop counter and one bit. -/
theorem length_encState (s : State) :
    (encState s).length = 2 * (Runtime.encState s.1).length +
      2 * (encNat s.2.1).length + 3 := by
  simp only [encState, length_encPair, encBool_apply, List.length_singleton]
  omega

/-- All live states fit a uniform budget; oversized cuts cost binary bits, not unary storage. -/
theorem length_run_le (δ : Bool × Bool → Bool) (p : Runtime.Input) {t : ℕ}
    (ht : t ≤ 2 * (encData p.1).length + 2 + 2 * width p.1) :
    (encState ((machine δ).run (Runtime.encInput p) t)).length ≤
      48 * ((encData p.1).length + Nat.log2 (Runtime.encInput p).length + 1) := by
  have hcounter : ∀ k ≤ 2 * width p.1, (encNat k).length ≤ 4 * ((encData p.1).length + 1) := by
    intro k hk
    have hc := length_encNat_le_self p.1.2.1.length
    have hcut : p.1.1 < 2 ^ (encNat p.1.1).length := by
      rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.lt_size_self _
    have hsuffix : p.1.2.1.length < 2 ^ (encNat p.1.2.1.length).length := by
      rw [encNat_apply, Nat.size_eq_bits_len]; exact Nat.lt_size_self _
    have hc' : (encNat p.1.1).length ≤ (encData p.1).length := by
      simp only [encData, length_encPair]; omega
    have hs' : (encNat p.1.2.1.length).length ≤ (encData p.1).length + 1 := by
      simp only [encData, length_encPair, encBits_apply]; omega
    have hpow : width p.1 < 2 ^ ((encData p.1).length + 2) := by
      have h₁ := hcut.trans_le (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hc')
      have h₂ := hsuffix.trans_le (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hs')
      dsimp only [width]
      rw [pow_succ, pow_succ]
      omega
    have hkpow : k < 2 ^ ((encData p.1).length + 3) := by grind
    have := length_encNat_le_of_lt_two_pow hkpow
    omega
  by_cases hi : t ≤ 2 * (encData p.1).length + 2
  · rw [run_initializing δ p hi, length_encState]
    have h := Runtime.length_run_le p hi
    have hz : (encNat 0).length = 0 := rfl
    simp only [hz]
    omega
  · have hk : t - (2 * (encData p.1).length + 2) ≤ 2 * width p.1 := by omega
    rw [show t = 2 * (encData p.1).length + 2 +
      (t - (2 * (encData p.1).length + 2)) by omega, run_scanning δ p hk, length_encState]
    have h := Runtime.length_run_le p (t := 2 * (encData p.1).length + 2) le_rfl
    rw [Runtime.run_halted] at h
    have hn := hcounter _ hk
    change 2 * (Runtime.encState (loaded p)).length + 2 *
      (encNat (t - (2 * (encData p.1).length + 2))).length + 3 ≤ _
    change (Runtime.encState (loaded p)).length ≤ _ at h
    omega

/-- One actual native evaluator handles all runtime inputs with shared constants. -/
theorem evaluate_inSpace (δ : Bool × Bool → Bool) :
    ∃ time c, ComputableInTimeAndSpace (evaluate δ) Runtime.encInput encBool time
      (fun p => c * ((encData p.1).length + Nat.log2 (Runtime.encInput p).length + 1)) := by
  obtain ⟨hq, hn, he, hh, hf⟩ := components_inSpace δ
  exact (machine δ).computableInSpace (encS := encState) (f := evaluate δ) hq hn he hh hf
    (fun p => 2 * (encData p.1).length + 2 + 2 * width p.1)
    (fun p => (first_halt δ p).1) (fun p => (first_halt δ p).2)
    (fun p => (output δ p).symm)
    (fun p => (encData p.1).length + Nat.log2 (Runtime.encInput p).length + 1)
    (fun p => by omega) ⟨48, fun p t ht => length_run_le δ p ht⟩

/-- Physical consumer states are logarithmic in the original word, with honest header bounds. -/
theorem length_run_le_original_log (δ : Bool × Bool → Bool) (p : Runtime.Input)
    (hp : Runtime.Admissible p) {t : ℕ}
    (ht : t ≤ 2 * (encData p.1).length + 2 + 2 * width p.1) :
    (encState ((machine δ).run (Runtime.encInput p) t)).length ≤
      816 * (Nat.log2 p.2.length + 1) := by
  exact ((length_run_le δ p ht).trans
    (Nat.mul_le_mul_left 48 (Runtime.budget_le_original_log p hp))).trans_eq
      (by rw [← Nat.mul_assoc])

/-- The native certificate measures workspace against the original length, uniformly over
runtime parameters. Only size admissibility is assumed, never a final transfer certificate. -/
theorem evaluate_inOriginalLogSpace (δ : Bool × Bool → Bool) :
    ∃ time c, ComputableInTimeAndSpace
      (fun p : {p : Runtime.Input // Runtime.Admissible p} => evaluate δ p.val)
      ((Function.Embedding.subtype Runtime.Admissible).trans Runtime.encInput) encBool time
      (fun p => c * (Nat.log2 p.val.2.length + 1)) := by
  let enc := (Function.Embedding.subtype Runtime.Admissible).trans Runtime.encInput
  obtain ⟨hq, hn, he, hh, hf⟩ := components_inSpace δ
  obtain ⟨time, c, h⟩ := (machine δ).computableInSpace (encS := encState) (enc := enc)
    (encOut := encBool)
    (f := fun p : {p : Runtime.Input // Runtime.Admissible p} => evaluate δ p.val)
    hq hn he hh hf
    (fun p => 2 * (encData p.val.1).length + 2 + 2 * width p.val.1)
    (fun p => (first_halt δ p.val).1) (fun p => (first_halt δ p.val).2)
    (fun p => (output δ p.val).symm)
    (fun p => 17 * (Nat.log2 p.val.2.length + 1))
    (fun p => by
      change Nat.log2 (Runtime.encInput p.val).length + 1 ≤ _
      have := Runtime.budget_le_original_log p.val p.property
      omega)
    ⟨48, fun p t ht => (length_run_le δ p.val ht).trans
      (Nat.mul_le_mul_left 48 (Runtime.budget_le_original_log p.val p.property))⟩
  refine ⟨time, c * 17, h.mono (fun _ => le_rfl) (fun p => ?_)⟩
  exact (Nat.mul_assoc c 17 _).symm.le

/-- The semantic specification is an ordinary finite-state fold of the actual virtual reads.
This list describes output semantics only; the native machine stores just one Boolean. -/
theorem value_eq_fold (δ : Bool × Bool → Bool) (cut : ℕ) (suffix x : List Bool)
    (hc : cut ≤ x.length) (k : ℕ) :
    value δ ((cut, suffix, 0), x) k =
      ((List.range k).map fun j =>
        (word x cut suffix).getD (j % (word x cut suffix).length) false).foldl
          (fun a b => δ (a, b)) false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [value_word δ cut suffix x hc k, ih]
    simp only [List.range_succ, List.map_append, List.map_singleton, List.foldl_append,
      List.foldl_cons, List.foldl_nil]

/-- Conventional semantics: the native result is the finite-state fold of two copies of the
virtual word. These copies occur only in the specification, never in the machine's state. -/
theorem evaluate_word (δ : Bool × Bool → Bool) (cut : ℕ) (suffix x : List Bool)
    (hc : cut ≤ x.length) :
    evaluate δ ((cut, suffix, 0), x) =
      (word x cut suffix ++ word x cut suffix).foldl (fun a b => δ (a, b)) false := by
  unfold evaluate
  rw [value_eq_fold δ cut suffix x hc]
  rw [show width (cut, suffix, 0) = (word x cut suffix).length from
    (length_word x cut suffix hc).symm]
  let w := word x cut suffix
  have hm : ((List.range w.length).map fun j => w.getD (j % w.length) false) = w := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp only [List.getElem_map, List.getElem_range, Nat.mod_eq_of_lt hi',
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  have hs : ((List.range w.length).map fun j =>
      w.getD ((w.length + j) % w.length) false) = w := by
    simpa only [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod] using hm
  change ((List.range (2 * w.length)).map fun j => w.getD (j % w.length) false).foldl
    (fun a b => δ (a, b)) false = _
  rw [two_mul, List.range_add, List.map_append, List.map_map, hm]
  change (w ++ (List.range w.length).map (fun j =>
    w.getD ((w.length + j) % w.length) false)).foldl (fun a b => δ (a, b)) false = _
  rw [hs]

end Turing.VirtualWord.Evaluator
