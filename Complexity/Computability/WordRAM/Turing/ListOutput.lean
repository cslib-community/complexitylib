/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Turing
public import Complexity.Computability.WordRAM.ListOutput
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Word-RAM list outputs give Turing-machine polynomial time

A fixed word-RAM program that returns a list (`Program.ComputesListInTime`: `halt` returns the
address of a length-prefixed array) within polynomially many instructions gives a multi-tape
Turing machine computing the same list-valued function in polynomial time, with output
`encList encNat`. This extends `Complexity.Computability.WordRAM.Turing` from word outputs to
list outputs.

## Construction

The simulating machine runs the parked program `p.parkHalts` for its full step budget with the
clocked finite-state simulator `FiniteState.run`, whose native certificate is polynomial by
`Cslib.GenericRAM.FiniteState.runCertificateOf_isPolynomial`. Since the parked program never
halts, the run ends in a continuing state holding the memory just before `p` halted, and its
control label `p.length + i` records the output register `i` (`ExecutesList.runs_parkHalts`). The
machine then selects that register by comparing labels (`parkedRegister`), reads the array length
`L` at the returned address and iterates `L` single-cell reads (`readRound`), each a scan of the
sparse memory. Everything is charged: the step budget, word size, input words and initial memory
as in the word-output simulation, then the run, the selection and the `L` reads.

## Conventions and limits

The cost model, input convention and word-size choice are those of
`Complexity.Computability.WordRAM.Turing`. The output length must be polynomially bounded in the
encoded input length (`hlen`). This hypothesis is necessary, since a polynomial-time machine
writes polynomially many output bits, and it does not follow from the instruction bound: the
returned array may consist of cells that are never written and read as `0`, so its length is
bounded only by `2 ^ w`.

## Main definitions

* `Cslib.WordRAM.parkedRegister`, `Cslib.WordRAM.parkedOutput`: the output register and the
  output list of a parked finite state.
* `Cslib.WordRAM.readRound`: one round of reading consecutive memory cells.
* `Cslib.WordRAM.parkedOutputCertificate`: the native reader of a parked state.

## Main results

* `Cslib.WordRAM.Program.ComputesListInTime.turingComputableInPolyTime_of_width`: the simulation at
  a supplied polynomial-time width schedule.
* `Cslib.WordRAM.Program.ComputesListInTime.turingComputableInPolyTime`,
  `Cslib.WordRAM.UniformComputableListInPolyTime.turingComputableInPolyTime`: polynomial word-RAM
  time with a list output gives `Turing.MultiTapeTM.ComputableInPolyTime` with output
  `encList encNat`.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
-/

@[expose] public section

namespace Cslib.WordRAM

open Turing.MultiTapeTM Cslib.GenericRAM NativeCertificate

/-! ## Reading the output of a parked state -/

section Read

open GenericRAM.FiniteState GenericRAM.FiniteState.Native

variable {B : Basis} {r : ℕ}

/-- The register recorded by a parked control label: register `i` at label `L + i`, the first
match among `l`, or `0` if none matches. -/
def parkedRegister (L : ℕ) (s : FiniteState B.genericModel r) : List (Fin r) → ℕ
  | [] => 0
  | i :: l => if s.pc = L + i then s.regs i else parkedRegister L s l

theorem parkedRegister_eq {L : ℕ} {s : FiniteState B.genericModel r} {i : Fin r}
    (hpc : s.pc = L + i) : ∀ {l : List (Fin r)}, i ∈ l → parkedRegister L s l = s.regs i
  | j :: l, h => by
    unfold parkedRegister
    split
    · next hj =>
      have hji : j = i := Fin.ext (by omega)
      rw [hji]
    · next hj =>
      have hij : i ≠ j := fun e => hj (e ▸ hpc)
      exact parkedRegister_eq hpc ((List.mem_cons.mp h).resolve_left hij)

theorem parkedRegister_lt {L w : ℕ} {s : FiniteState B.genericModel r}
    (hs : ∀ i, s.regs i < 2 ^ w) : ∀ l, parkedRegister L s l < 2 ^ w
  | [] => Nat.two_pow_pos w
  | i :: l => by
    unfold parkedRegister
    split
    · exact hs i
    · exact parkedRegister_lt hs l

/-- The output list of a parked finite state of a program of length `L`: the array at the address
in the register recorded by the control label. -/
def parkedOutput (L : ℕ) (s : FiniteState B.genericModel r) : List ℕ :=
  outputList (fun a => SparseMemory.read s.default a s.memory)
    (parkedRegister L s (List.finRange r))

/-- A parked state at label `L + i` outputs the array at the address in register `i`. -/
theorem parkedOutput_eq {L : ℕ} {s : FiniteState B.genericModel r} {i : Fin r}
    (hpc : s.pc = L + i) :
    parkedOutput L s = outputList (fun a => SparseMemory.read s.default a s.memory) (s.regs i) := by
  rw [parkedOutput, parkedRegister_eq hpc (List.mem_finRange i)]

/-- One round of reading consecutive memory cells: on `((fill, memory), (address, values))`, where
`fill` is the value of unwritten cells, append the cell at `address` to `values` and advance
`address`. -/
def readRound : (ℕ × SparseMemory ℕ ℕ) × (ℕ × List ℕ) → (ℕ × SparseMemory ℕ ℕ) × (ℕ × List ℕ)
  | ((fill, memory), (address, values)) =>
    ((fill, memory), (address + 1, values ++ [SparseMemory.read fill address memory]))

/-- `j` reading rounds append the `j` cells from `address` on. -/
theorem iterate_readRound (j fill : ℕ) (memory : SparseMemory ℕ ℕ) (address : ℕ)
    (values : List ℕ) :
    readRound^[j] ((fill, memory), (address, values)) =
      ((fill, memory), (address + j,
        values ++ (List.range j).map fun i => SparseMemory.read fill (address + i) memory)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [readRound, List.range_succ, Nat.add_assoc]

/-- The encoding of the reading loop state. -/
abbrev readLoopEncoding : ((ℕ × SparseMemory ℕ ℕ) × (ℕ × List ℕ)) ↪ List Bool :=
  encPair (encPair encNat (SparseMemory.encoding encNat encNat)) (encPair encNat (encList encNat))

/-- One reading round is cubic, with linear output: one sparse-memory scan and linear copying. -/
theorem readRound_degree : ComputableInDegree readRound readLoopEncoding readLoopEncoding 3 1 := by
  have hread : ComputableInDegree
      (fun q : (ℕ × SparseMemory ℕ ℕ) × ℕ => SparseMemory.read q.2 q.1.1 q.1.2)
      (SparseMemory.readEncoding encNat encNat) encNat 3 1 :=
    (SparseMemory.read_inO_cube encNat encNat).computableInDegree ⟨1, fun q => by simp⟩
      ⟨1, fun q => by simp⟩ (by norm_num)
  have harg : ComputableInDegree
      (fun q : (ℕ × SparseMemory ℕ ℕ) × (ℕ × List ℕ) => ((q.2.1, q.1.2), q.1.1))
      readLoopEncoding (SparseMemory.readEncoding encNat encNat) 1 1 :=
    ((((ComputableInDegree.fst _ _).comp (ComputableInDegree.snd _ _)).prod
      ((ComputableInDegree.snd _ _).comp (ComputableInDegree.fst _ _))).prod
      ((ComputableInDegree.fst _ _).comp (ComputableInDegree.fst _ _))).mono
  have hacc : ComputableInDegree (fun q : (ℕ × SparseMemory ℕ ℕ) × (ℕ × List ℕ) => q.2.2)
      readLoopEncoding (encList encNat) 1 1 :=
    ((ComputableInDegree.snd _ _).comp (ComputableInDegree.snd _ _)).mono
  have hsnoc : ComputableInDegree
      (fun q : (ℕ × SparseMemory ℕ ℕ) × (ℕ × List ℕ) =>
        q.2.2 ++ [SparseMemory.read q.1.1 q.2.1 q.1.2])
      readLoopEncoding (encList encNat) 3 1 :=
    ((ComputableInDegree.snoc encNat).comp (hacc.prod (hread.comp harg))).mono
  have hsucc : ComputableInDegree (fun q : (ℕ × SparseMemory ℕ ℕ) × (ℕ × List ℕ) => q.2.1 + 1)
      readLoopEncoding encNat 1 1 :=
    (ComputableInDegree.natSucc.comp
      ((ComputableInDegree.fst _ _).comp (ComputableInDegree.snd _ _))).mono
  exact ((ComputableInDegree.fst _ _).prod (hsucc.prod hsnoc)).mono

/-- The native certificate of one reading round, cubic in the encoded loop state. -/
def readRoundCertificate : NativeCertificate readRound readLoopEncoding readLoopEncoding :=
  ⟨fun q => ((readLoopEncoding q).length + 1) ^ 3, fun q => ((readLoopEncoding q).length + 1) ^ 3,
    readRound_degree.inO⟩

theorem readRoundCertificate_isPolynomial : readRoundCertificate.IsPolynomial :=
  ⟨.of_forall_le 1 3 (by simp [readRoundCertificate]),
    .of_forall_le 1 3 (by simp [readRoundCertificate])⟩

variable {α : Type} {encIn : α ↪ List Bool} {s : α → FiniteState B.genericModel r}

/-- Select the register recorded by the control label among `l`, by label comparisons. -/
noncomputable def parkedRegisterCertificate (L : ℕ)
    (c : NativeCertificate s encIn (FiniteState.encoding B.encoding)) :
    (l : List (Fin r)) → NativeCertificate (fun a => parkedRegister L (s a) l) encIn encNat
  | [] => const 0
  | i :: l => congr (branch (pcEquals B.encoding c (L + i)) (register B.encoding c i)
      (parkedRegisterCertificate L c l)) fun a => by
        simp only [parkedRegister, decide_eq_true_eq]

theorem parkedRegisterCertificate_isPolynomial (L : ℕ)
    (c : NativeCertificate s encIn (FiniteState.encoding B.encoding)) (hc : c.IsPolynomial) :
    ∀ l, (parkedRegisterCertificate L c l).IsPolynomial
  | [] => const_isPolynomial 0
  | i :: l => congr_isPolynomial _ _ (branch_isPolynomial _ _ _
      (pcEquals_isPolynomial _ c _ hc) (register_isPolynomial _ c i hc)
      (parkedRegisterCertificate_isPolynomial L c hc l))

/-- The initial reading loop state `((default, memory), (v + 1, []))` for the output address
`v`. -/
noncomputable def readInitCertificate (L : ℕ)
    (c : NativeCertificate s encIn (FiniteState.encoding B.encoding)) :
    NativeCertificate (fun a => (((s a).default, (s a).memory),
      (parkedRegister L (s a) (List.finRange r) + 1, ([] : List ℕ)))) encIn readLoopEncoding :=
  prod (prod (fst (snd (snd (fields B.encoding c)))) (snd (snd (snd (fields B.encoding c)))))
    (prod (post (parkedRegisterCertificate L c (List.finRange r))
      ComputableInDegree.natSucc.inO_one) (const []))

/-- **The reader of a parked state**: select the output register, read the array length `L'` at
its address, then read `L'` consecutive cells. -/
noncomputable def parkedOutputCertificate (L : ℕ)
    (c : NativeCertificate s encIn (FiniteState.encoding B.encoding)) :
    NativeCertificate (fun a => parkedOutput L (s a)) encIn (encList encNat) :=
  congr (snd (snd (iterate (readCertificate B.encoding c
      (parkedRegisterCertificate L c (List.finRange r)))
    (readInitCertificate L c) readRoundCertificate))) fun a => by
      rw [iterate_readRound]
      simp [parkedOutput, outputList]

/-- The reader is polynomial when its input state is, its states hold `W`-bit words with `W`
polynomially bounded, and the output length is polynomially bounded. -/
theorem parkedOutputCertificate_isPolynomial (L : ℕ)
    (c : NativeCertificate s encIn (FiniteState.encoding B.encoding)) (hc : c.IsPolynomial)
    {W : α → ℕ} (hW : PolyBounded (fun a => (encIn a).length) W)
    (hs : ∀ a, WordBounded (W a) (s a))
    (hlen : PolyBounded (fun a => (encIn a).length) (fun a => (parkedOutput L (s a)).length)) :
    (parkedOutputCertificate L c).IsPolynomial := by
  have hv := parkedRegisterCertificate_isPolynomial L c hc (List.finRange r)
  have hS : PolyBounded (fun a => (encIn a).length)
      (fun a => (FiniteState.encoding B.encoding (s a)).length) :=
    (c.polyTime hc).polyBounded_length
  let bound : α → ℕ := fun a =>
    6 * (FiniteState.encoding B.encoding (s a)).length + 2 * W a + 4 +
      (parkedOutput L (s a)).length * (2 * W a + 1)
  have hB : PolyBounded (fun a => (encIn a).length) bound :=
    ((((PolyBounded.const 6).mul hS).add ((PolyBounded.const 2).mul hW)).add (.const 4)).add
      (hlen.mul (((PolyBounded.const 2).mul hW).add (.const 1)))
  refine congr_isPolynomial _ _ (snd_isPolynomial _ (snd_isPolynomial _
    (iterate_isPolynomial _ _ _ (readCertificate_isPolynomial _ c _ hc hv)
      (prod_isPolynomial _ _ (prod_isPolynomial _ _ hc hc)
        (prod_isPolynomial _ _ hv (const_isPolynomial _)))
      readRoundCertificate_isPolynomial ?_ hB ?_)))
  · refine hlen.mono fun a => ?_
    simp [parkedOutput]
  · intro a j hj
    rw [iterate_readRound]
    have hsa := hs a
    set v := parkedRegister L (s a) (List.finRange r) with hv_def
    have hvlt : v < 2 ^ W a := parkedRegister_lt hsa.regs_lt _
    have hlenEq : (parkedOutput L (s a)).length =
        SparseMemory.read (s a).default v (s a).memory := by
      simp [parkedOutput, ← hv_def]
    have hjlt : j < 2 ^ W a := lt_of_le_of_lt (hj.trans_eq rfl) (hsa.read_lt v)
    have haddr : (encNat (v + 1 + j)).length ≤ W a + 1 :=
      length_encNat_le_of_lt_two_pow (by rw [Nat.pow_succ]; omega)
    have hd : (encNat (s a).default).length ≤ W a := length_encNat_le_of_lt_two_pow hsa.default_lt
    have hacc : (encList encNat ((List.range j).map fun i =>
        SparseMemory.read (s a).default (v + 1 + i) (s a).memory)).length ≤ j * (2 * W a + 1) := by
      rw [length_encList]
      calc (((List.range j).map fun i =>
              SparseMemory.read (s a).default (v + 1 + i) (s a).memory).map
              fun x => 2 * (encNat x).length + 1).sum
          ≤ (((List.range j).map fun i =>
              SparseMemory.read (s a).default (v + 1 + i) (s a).memory).map
              fun _ => 2 * W a + 1).sum :=
            List.sum_le_sum fun x hx => by
              obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
              have := length_encNat_le_of_lt_two_pow (hsa.read_lt (v + 1 + i))
              omega
        _ = j * (2 * W a + 1) := by simp [Function.comp_def]
    have hmem : 2 * (encNat (s a).default).length +
        (SparseMemory.encoding encNat encNat (s a).memory).length + 3 ≤
          (FiniteState.encoding B.encoding (s a)).length := by
      have := FiniteState.length_encoding B.encoding (s a)
      change _ = 2 * (encNat (s a).pc).length + 2 * (encPi encNat (s a).regs).length +
        2 * (encNat (s a).default).length +
        (SparseMemory.encoding encNat encNat (s a).memory).length + 3 at this
      omega
    have hjL : j * (2 * W a + 1) ≤ (parkedOutput L (s a)).length * (2 * W a + 1) :=
      Nat.mul_le_mul_right _ (by rw [hlenEq]; exact hj)
    simp only [length_encPair, List.nil_append, bound]
    omega

end Read

/-! ## Word RAM with list outputs ⇒ Turing machine -/

section Main

open GenericRAM.FiniteState

variable {B : Basis} {r : ℕ} {α : Type} {encIn : α ↪ List Bool}

/-- **Word-RAM time with a list output, at a polynomial-time width schedule, gives
Turing-machine polynomial time.**

Let `p` be a fixed program over a basis whose checked operations are polynomial-time on a unary
width and binary operands. Suppose `width a` is computable in unary in polynomial time, is an
admitted width for `a`, and the word list `encode (width a) a` fits it and is computable in
polynomial time from `encIn a`. If `p` returns the list `f a` (`Program.ComputesListInTime`)
within a time bound at `width a` polynomial in `|encIn a|`, and the length of `f a` is
polynomially bounded in `|encIn a|`, then `f` is computable in polynomial time with output
`encList encNat`. -/
theorem Program.ComputesListInTime.turingComputableInPolyTime_of_width
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat))
    {p : Program B r} {encode : ℕ → α → List ℕ} {time : α → ℕ → ℕ}
    {allowed : α → ℕ → Prop} {f : α → List ℕ}
    (h : p.ComputesListInTime encode time allowed f) {width : α → ℕ}
    (hwidth : Turing.MultiTapeTM.ComputableInPolyTime width encIn encUnary)
    (hallowed : ∀ a, allowed a (width a))
    (hfits : ∀ a, InputFits (width a) (encode (width a) a))
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime (fun a => encode (width a) a) encIn
      (encList encNat))
    (htime : PolyBounded (fun a => (encIn a).length) (fun a => time a (width a)))
    (hlen : PolyBounded (fun a => (encIn a).length) (fun a => (f a).length)) :
    Turing.MultiTapeTM.ComputableInPolyTime f encIn (encList encNat) := by
  -- The step budget: a polynomial of the input length, computed in unary.
  obtain ⟨steps, hstepsU, hsteps⟩ := exists_unary_majorant htime
  have hstepsT : Turing.MultiTapeTM.ComputableInPolyTime steps encIn encNat :=
    Turing.MultiTapeTM.ComputableInPolyTime.unary_to_binary.comp hstepsU
  -- Initialization: the memory `0 ↦ n, i + 1 ↦ xᵢ`, zero registers and default.
  have hmem : Turing.MultiTapeTM.ComputableInPolyTime
      (fun a => initMemory (encode (width a) a)) encIn (SparseMemory.encoding encNat encNat) :=
    initMemory_polyTime.comp hencode
  let cInit := FiniteState.initConstCertificate (r := r) B.encoding
    (NativeCertificate.const (ei := encIn) 0) (NativeCertificate.const 0) (ofPolyTime hmem)
  have hInit : cInit.IsPolynomial :=
    FiniteState.initConstCertificate_isPolynomial _ _ _ _ (const_isPolynomial 0)
      (const_isPolynomial 0) (ofPolyTime_isPolynomial hmem)
  -- The clocked run of the parked program, and its final state.
  let q := p.parkHalts.toGeneric
  let cRun := runCertificateOf B.encoding (B.nativePrimitivesOfPolyTime hop) q
    (ofPolyTime hstepsT) (ofPolyTime hwidth) cInit
  let final : α → FiniteState B.genericModel r := fun a =>
    (continuing (FiniteState.run (width a) q (steps a)
      (initState B r (encode (width a) a)))).getD (initState B r [])
  let cFinal : NativeCertificate final encIn (FiniteState.encoding B.encoding) :=
    post (post cRun (continuingCertificate B.encoding).computes)
      (ComputableInDegree.getD (enc₁ := FiniteState.encoding B.encoding)
        (enc := encOption (FiniteState.encoding B.encoding)) (initState B r [])).inO_one
  -- The run ends in the parked pre-halt state, which holds the output.
  have hfinal (a : α) :
      WordBounded (width a) (final a) ∧ f a = parkedOutput p.length (final a) := by
    obtain ⟨m, hm, hle⟩ := h a (width a) (hallowed a) (hfits a)
    obtain ⟨i, x, hruns, hout⟩ := hm.runs_parkHalts (hle.trans (hsteps a))
    have hg := runs_toGeneric_iff.2 hruns
    rw [← denote_initState] at hg
    obtain ⟨t, hrun, hden⟩ := exists_run_eq_inl_of_runs hg
    have hfa : final a = t := by simp only [final, q, hrun]; rfl
    have hwb := ((wordBounded_initState (B := B) (r := r) (hfits a)).run (p := q) (by simp)
      (steps a)).1 t hrun
    refine ⟨hfa ▸ hwb.1, ?_⟩
    rw [hfa, ← hout]
    have hpc : t.pc = p.length + i := congrArg GenericRAM.State.pc hden
    have hregs : t.regs = x.regs := congrArg (fun g => g.data.regs) hden
    have hmem : (fun a => SparseMemory.read t.default a t.memory) = x.mem :=
      congrArg (fun g => g.data.mem) hden
    rw [parkedOutput_eq hpc, hregs, hmem]
  -- Every simulated outcome is bounded by a polynomial in the input length.
  let bound : α → ℕ := fun a => stateBound r (labelBound q) (width a)
    ((encode (width a) a).length + 1 + steps a)
  have hbound : PolyBounded (fun a => (encIn a).length) bound := by
    have hw := hwidth.polyBounded
    have hE : PolyBounded (fun a => (encIn a).length)
        (fun a => (encode (width a) a).length + 1 + steps a) :=
      ((hencode.polyBounded_length.mono fun a =>
        length_le_length_encList encNat (encode (width a) a)).add (.const 1)).add
          hstepsU.polyBounded
    exact (((((PolyBounded.const _).add ((PolyBounded.const (2 * r)).mul
      (((PolyBounded.const 2).mul hw).add (.const 1)))).add ((PolyBounded.const 2).mul hw)).add
      (hE.mul (((PolyBounded.const 6).mul hw).add (.const 3)))).add hw).add (.const 5)
  have hOutLen (a : α) (j : ℕ) (hj : j ≤ steps a) :
      (FiniteState.resultEncoding B.encoding (FiniteState.run (width a) q j
        (initState B r (encode (width a) a)))).length ≤ bound a := by
    have hrun := (wordBounded_initState (B := B) (r := r) (hfits a)).length_resultEncoding_run_le
      (p := q) (by simp) j
    rw [length_entries_initState] at hrun
    refine hrun.trans ?_
    simp only [bound, stateBound]
    have := Nat.mul_le_mul_right (6 * width a + 3)
      (show (encode (width a) a).length + 1 + j ≤ (encode (width a) a).length + 1 + steps a by
        omega)
    omega
  have hRun : cRun.IsPolynomial :=
    runCertificateOf_isPolynomial _ _ _ _ _ _ (B.nativePrimitivesOfPolyTime_isPolynomial hop)
      (ofPolyTime_isPolynomial hstepsT) (ofPolyTime_isPolynomial hwidth) hInit
      hstepsU.polyBounded hbound hOutLen
  have hFinal : cFinal.IsPolynomial := hRun
  have hOut := parkedOutputCertificate_isPolynomial p.length cFinal hFinal hwidth.polyBounded
    (fun a => (hfinal a).1) (hlen.mono fun a => by rw [(hfinal a).2])
  exact ((parkedOutputCertificate p.length cFinal).congr fun a => ((hfinal a).2).symm).polyTime
    (congr_isPolynomial _ _ hOut)

/-- **Polynomial word-RAM time with a list output gives Turing-machine polynomial time** for a
fixed program.

Let `p` be a fixed program over a basis whose checked operations are polynomial-time on a unary
width and binary operands. Suppose that on every input `a` whose words fit, at every word size of
at least `logWidth k (size a)`, `p` returns the list `f a` from `State.init (encode a)` within
`T (size a)` instructions, where `T` is polynomially bounded. If the word list `encode a` is
computable in polynomial time from the bit string `encIn a`, and `size a` and the length of
`f a` are polynomially bounded in `|encIn a|`, then `f` is computable in polynomial time with
output `encList encNat`. -/
theorem Program.ComputesListInTime.turingComputableInPolyTime
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat))
    {p : Program B r} {encode : α → List ℕ} {size : α → ℕ} {f : α → List ℕ} {T : ℕ → ℕ}
    {k : ℕ} (hT : PolynomiallyBounded T) (hsize : PolyBounded (fun a => (encIn a).length) size)
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime encode encIn (encList encNat))
    (hlen : PolyBounded (fun a => (encIn a).length) (fun a => (f a).length))
    (h : p.ComputesListInTime (fun _ => encode) (fun a _ => T (size a))
      (fun a w => logWidth k (size a) ≤ w) f) :
    Turing.MultiTapeTM.ComputableInPolyTime f encIn (encList encNat) := by
  have hlog : PolyBounded (fun a => (encIn a).length) (fun a => logWidth k (size a)) :=
    ((PolyBounded.const k).mul (hsize.add (.const 1))).mono fun a =>
      Nat.mul_le_mul_left k (Nat.add_le_add_right (Nat.log_le_self 2 (size a)) 1)
  obtain ⟨width, hwidth, hge⟩ := exists_unary_majorant
    (hlog.add (hencode.polyBounded_length (encMid := encList encNat)))
  exact h.turingComputableInPolyTime_of_width hop hwidth (fun a => by have := hge a; omega)
    (fun a => inputFits_of_length_encList_le (by have := hge a; omega)) hencode
    ((PolyBounded.of_polynomiallyBounded id hT).comp hsize) hlen

/-- **Uniform polynomial word-RAM time with a list output gives Turing-machine polynomial time**,
for a width-independent word encoding computable in polynomial time, a size measure and an output
length polynomially bounded in the encoded input length. -/
theorem UniformComputableListInPolyTime.turingComputableInPolyTime
    (hop : ∀ op : B.Op, Turing.MultiTapeTM.ComputableInPolyTime (B.genericModel.checkedOp op)
      (encPair encUnary (encPi encNat)) (encOption encNat))
    {encode : α → List ℕ} {size : α → ℕ} {f : α → List ℕ}
    (h : UniformComputableListInPolyTime B f (fun _ => encode) size)
    (hsize : PolyBounded (fun a => (encIn a).length) size)
    (hencode : Turing.MultiTapeTM.ComputableInPolyTime encode encIn (encList encNat))
    (hlen : PolyBounded (fun a => (encIn a).length) (fun a => (f a).length)) :
    Turing.MultiTapeTM.ComputableInPolyTime f encIn (encList encNat) := by
  obtain ⟨T, hT, k, -, r, p, hp⟩ := h
  exact hp.turingComputableInPolyTime hop hT hsize hencode hlen

end Main

end Cslib.WordRAM
