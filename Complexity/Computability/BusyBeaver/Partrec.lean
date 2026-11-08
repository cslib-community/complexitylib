/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.BlumComplexity.Fuel
public import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Computability.Halting
import Mathlib.Tactic.Linarith

/-!
# Radó's busy beaver functions for partial recursive codes

Radó's busy beaver function `Σ(n)` is the largest number of ones that a halting `n`-state Turing
machine leaves on a blank tape, and his shift function `S(n)` is the largest number of steps such a
machine takes [Radó, *On non-computable functions*, Sections V and VI][Rado1962]. Each eventually
exceeds every computable function, so neither is computable.

This file formalizes the two functions for Mathlib's acceptable numbering `Nat.Partrec.Code`,
started on the input `0` (the analogue of the blank tape). The *size* of a code `c` is its Gödel
number `encode c` under Mathlib's `Denumerable Code` instance. Since `encode` is a bijection onto
`ℕ`, exactly `n + 1` codes have size at most `n`, so the maxima below range over finite sets.

* `bbOutput n` is the largest output `c.eval 0` of a code `c` with `encode c ≤ n` that halts on `0`.
* `bbFuel n` is the largest fuel `evalnFuel c 0` (the least fuel with which Mathlib's clocked
  evaluator `Code.evaln` succeeds, see `Complexity.Computability.BlumComplexity.Fuel`) of such a
  code. The fuel is the cost measure of `evaln`, not the step count of a machine.

Both maxima are attained, because the code `Code.zero` (of size `0`) halts.

For a computable `f`, let `H m = ∑_{i < m} f i`. The domination proof adapts Radó's argument: `H`
plays the role of his majorant `F`, and the recursion theorem replaces his double application
`F(F(x))` and machine chaining to absorb the program's own size. By the recursion theorem
(`Nat.Partrec.Code.fixed_point₂`) there is a code `G` that, on input `k`, outputs
`H (encode (w (k + 1)))`, where `w k` is the code `succ ∘ G ∘ const k`. The code `w k` halts on `0`
with output `H (encode (w (k + 1))) + 1`, which exceeds `f n` whenever `n < encode (w (k + 1))`,
and it needs at least as much fuel as its output. Since `encode (w k)` grows without bound, every
large `n` satisfies `encode (w k) ≤ n < encode (w (k + 1))` for some `k`, so
`f n < bbOutput (encode (w k)) ≤ bbOutput n`, and likewise for `bbFuel`.

Independently, fuel `bbFuel n` suffices for every halting code of size at most `n`, so a
computable upper bound on `bbFuel` would decide the halting problem
(`not_exists_computable_bbFuel_le`). This is the unrelativized corollary of
[Aaronson, Proposition 1][Aaronson2020], which solves the halting problem with oracle access to
any upper bound on the shift function. The two functions bound each other up to computable changes
of size: `bbOutput n < bbFuel (4 * n ^ 2 + 14)`, and `bbFuel n ≤ bbOutput (h n)` for a computable
`h`. So a computable upper bound on `bbOutput` would also decide the halting problem.

The model differs from Radó's: programs are partial recursive codes measured by Gödel number, not
Turing machines measured by their number of states, and the output is a number rather than a count
of ones. The closest analogues in the literature are Aaronson's busy beaver functions for an
arbitrary programming language `L` whose programs are bit strings
[Aaronson, Section 1][Aaronson2020]: `BB_L(n)` is the largest number of steps of a halting program
of at most `n` bits, and a variant defined through Kolmogorov complexity is the largest `m` with
`K_L(m) ≤ n`, that is, the largest output of such a program. Aaronson states Propositions 1 and 2
for Turing machines, noting in Section 2 that they hold for any universal model of computation. The
results transfer to Turing machines only through a translation between the two program classes,
which this file does not provide. Within the model, coarser size measures are covered: whenever
`n ≤ σ n`, the function `n ↦ bbOutput (σ n)` still dominates every computable function
(`eventually_lt_bbOutput_comp`). For example, `Nat.size (encode c) ≤ ℓ` exactly when
`encode c ≤ 2 ^ ℓ - 1`, so the busy beaver function indexed by bit length is
`ℓ ↦ bbOutput (2 ^ ℓ - 1)`.

## Main definitions

* `Cslib.BusyBeaver.bbOutput`: the busy beaver function, output version.
* `Cslib.BusyBeaver.bbFuel`: the busy beaver function, fuel version.

## Main results

* `Cslib.BusyBeaver.le_bbOutput`, `Cslib.BusyBeaver.exists_mem_eval_bbOutput`,
  `Cslib.BusyBeaver.le_bbFuel`, `Cslib.BusyBeaver.exists_mem_evalnFuel_bbFuel`: the functions
  are the maxima of finite nonempty sets.
* `Cslib.BusyBeaver.monotone_bbOutput`, `Cslib.BusyBeaver.monotone_bbFuel`: monotonicity.
* `Cslib.BusyBeaver.eventually_lt_bbOutput`, `Cslib.BusyBeaver.eventually_lt_bbFuel`:
  **domination**, every computable function is eventually below both functions [Rado1962].
* `Cslib.BusyBeaver.not_computable_bbOutput`, `Cslib.BusyBeaver.not_computable_bbFuel`: neither
  function is computable.
* `Cslib.BusyBeaver.dom_eval_iff_isSome_evaln_bbFuel`: a code of size at most `n` halts on `0`
  exactly when `evaln` succeeds with fuel `bbFuel n`.
* `Cslib.BusyBeaver.computablePred_dom_eval_of_bbFuel_le`,
  `Cslib.BusyBeaver.not_exists_computable_bbFuel_le`: a computable upper bound on `bbFuel` decides
  halting, so none exists.
* `Cslib.BusyBeaver.bbOutput_lt_bbFuel`, `Cslib.BusyBeaver.exists_computable_bbFuel_le_bbOutput`:
  the two functions bound each other up to computable changes of size.
* `Cslib.BusyBeaver.not_exists_computable_bbOutput_le`: no computable function bounds `bbOutput`.

## References

* [T. Radó, *On non-computable functions*][Rado1962], Sections V (Theorem) and VI
* [S. Aaronson, *The Busy Beaver Frontier*][Aaronson2020], Section 1 (`BB_L`), Section 2,
  Propositions 1 and 2
* [G. Boolos, J. Burgess, R. Jeffrey, *Computability and Logic*][BoolosBurgessJeffrey2007],
  Section 4.2, "The Productivity Function", a textbook treatment for Turing machines (locator from
  the table of contents; the text was not checked)
-/

public section

namespace Cslib.BusyBeaver

open Encodable Denumerable Nat.Partrec Filter Cslib.BlumComplexity

/-- The largest value of `v c` over the codes `c` with `encode c ≤ n` at which `v c` is defined. -/
private noncomputable def bbOf (v : Code → Part ℕ) (n : ℕ) : ℕ :=
  sSup {x | ∃ c : Code, encode c ≤ n ∧ x ∈ v c}

private theorem finite_setOf (v : Code → Part ℕ) (n : ℕ) :
    {x | ∃ c : Code, encode c ≤ n ∧ x ∈ v c}.Finite := by
  refine ((Finset.range (n + 1)).finite_toSet.biUnion fun i _ =>
    (v (ofNat Code i)).subsingleton.finite).subset ?_
  rintro x ⟨c, hc, hx⟩
  exact Set.mem_biUnion (x := encode c) (Finset.mem_coe.2 (Finset.mem_range.2 (by omega)))
    (by rwa [ofNat_encode])

private theorem le_bbOf {v : Code → Part ℕ} {n : ℕ} {c : Code} (hc : encode c ≤ n) {x : ℕ}
    (hx : x ∈ v c) : x ≤ bbOf v n :=
  le_csSup (finite_setOf v n).bddAbove ⟨c, hc, hx⟩

private theorem bbOf_mem {v : Code → Part ℕ} (h0 : (v Code.zero).Dom) (n : ℕ) :
    ∃ c : Code, encode c ≤ n ∧ bbOf v n ∈ v c :=
  Nat.sSup_mem (s := {x | ∃ c : Code, encode c ≤ n ∧ x ∈ v c})
    ⟨_, Code.zero, Nat.zero_le n, Part.get_mem h0⟩ (finite_setOf v n).bddAbove

private theorem monotone_bbOf (v : Code → Part ℕ) (h0 : (v Code.zero).Dom) : Monotone (bbOf v) :=
  fun m n hmn => by
    obtain ⟨c, hc, hx⟩ := bbOf_mem h0 m
    exact le_bbOf (hc.trans hmn) hx

/-- **Busy beaver, output version** [Rado1962]: the largest output on input `0` of a code with
Gödel number at most `n` that halts on `0`. -/
noncomputable def bbOutput (n : ℕ) : ℕ :=
  sSup {x | ∃ c : Code, encode c ≤ n ∧ x ∈ c.eval 0}

/-- **Busy beaver, fuel version** [Rado1962]: the largest fuel `evalnFuel c 0` needed by a code
`c` with Gödel number at most `n` that halts on `0`. This is the analogue of Radó's shift function
for the evaluator `Code.evaln`; the fuel is not the step count of a machine. -/
noncomputable def bbFuel (n : ℕ) : ℕ :=
  sSup {k | ∃ c : Code, encode c ≤ n ∧ k ∈ evalnFuel c 0}

private theorem bbOutput_eq : bbOutput = bbOf fun c => c.eval 0 := rfl

private theorem bbFuel_eq : bbFuel = bbOf fun c => evalnFuel c 0 := rfl

private theorem dom_eval_zero : (Code.zero.eval 0).Dom := by
  simp [Code.eval, pure, PFun.pure]

private theorem dom_evalnFuel_zero : (evalnFuel Code.zero 0).Dom :=
  (dom_evalnFuel_iff _ _).2 dom_eval_zero

/-- Every output of a halting code of size at most `n` is at most `bbOutput n`. -/
theorem le_bbOutput {n : ℕ} {c : Code} (hc : encode c ≤ n) {x : ℕ} (hx : x ∈ c.eval 0) :
    x ≤ bbOutput n :=
  le_bbOf hc hx

/-- Some code of size at most `n` outputs `bbOutput n` on input `0`. -/
theorem exists_mem_eval_bbOutput (n : ℕ) : ∃ c : Code, encode c ≤ n ∧ bbOutput n ∈ c.eval 0 :=
  bbOf_mem dom_eval_zero n

theorem monotone_bbOutput : Monotone bbOutput :=
  monotone_bbOf _ dom_eval_zero

/-- The fuel needed by a halting code of size at most `n` is at most `bbFuel n`. -/
theorem le_bbFuel {n : ℕ} {c : Code} (hc : encode c ≤ n) {k : ℕ} (hk : k ∈ evalnFuel c 0) :
    k ≤ bbFuel n :=
  le_bbOf hc hk

/-- Some code of size at most `n` needs fuel exactly `bbFuel n` on input `0`. -/
theorem exists_mem_evalnFuel_bbFuel (n : ℕ) :
    ∃ c : Code, encode c ≤ n ∧ bbFuel n ∈ evalnFuel c 0 :=
  bbOf_mem dom_evalnFuel_zero n

theorem monotone_bbFuel : Monotone bbFuel :=
  monotone_bbOf _ dom_evalnFuel_zero

/-- The output of `succ ∘ c` is at most the fuel with which `evaln` computes it. -/
private theorem le_of_mem_evaln_comp_succ {k : ℕ} {c : Code} {n x : ℕ}
    (h : x ∈ Code.evaln k (Code.comp Code.succ c) n) : x ≤ k := by
  cases k with
  | zero => simp [Code.evaln] at h
  | succ k =>
    simp only [Code.evaln, Option.bind_eq_bind, Option.mem_def, Option.bind_eq_some_iff,
      Option.guard_eq_some', Option.pure_def, Option.some.injEq] at h
    obtain ⟨-, -, y, -, -, hyk, rfl⟩ := h
    omega

/-- The output of `succ ∘ c` is at most its fuel. -/
private theorem le_of_mem_evalnFuel_comp_succ {c : Code} {n x k : ℕ}
    (hx : x ∈ (Code.comp Code.succ c).eval n) (hk : k ∈ evalnFuel (Code.comp Code.succ c) n) :
    x ≤ k := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (mem_evalnFuel_iff.1 hk).1
  rw [Part.mem_unique hx (Code.evaln_sound hy)]
  exact le_of_mem_evaln_comp_succ hy

private theorem exists_mem_evalnFuel {c : Code} {n x : ℕ} (hx : x ∈ c.eval n) :
    ∃ k, k ∈ evalnFuel c n :=
  Part.dom_iff_mem.1 ((dom_evalnFuel_iff c n).2 (Part.dom_iff_mem.2 ⟨x, hx⟩))

private theorem le_encode_const (k : ℕ) : k ≤ encode (Code.const k) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => exact Nat.succ_le_of_lt (ih.trans_lt (Code.encode_lt_comp _ _).2)

/-- The partial sums of a computable function are computable. -/
private theorem computable_sum_range {f : ℕ → ℕ} (hf : Computable f) :
    Computable fun m => ∑ i ∈ Finset.range m, f i := by
  refine (Computable.nat_rec (f := fun m : ℕ => m) (g := fun _ => 0)
    (h := fun _ p => p.2 + f p.1) Computable.id (Computable.const 0)
    ((Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.snd))).to₂)).of_eq fun m => ?_
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ← ih]

/-- **Domination** for both functions at once. -/
private theorem eventually_lt_bbOutput_and_bbFuel {f : ℕ → ℕ} (hf : Computable f) :
    ∀ᶠ n in atTop, f n < bbOutput n ∧ f n < bbFuel n := by
  -- `H m` bounds `f` below `m`.
  let H : ℕ → ℕ := fun m => ∑ i ∈ Finset.range m, f i
  have hH : Computable H := computable_sum_range hf
  have hfH {n m : ℕ} (h : n < m) : f n ≤ H m :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (f i)) (Finset.mem_range.2 h)
  -- The codes `w c k = succ ∘ c ∘ const k`.
  let w : Code → ℕ → Code := fun c k => Code.comp Code.succ (Code.comp c (Code.const k))
  have hw : Computable₂ w :=
    (Code.primrec₂_comp.comp (Primrec.const Code.succ)
      (Code.primrec₂_comp.comp Primrec.fst (Code.primrec_const.comp Primrec.snd))).to_comp
  -- By the recursion theorem, a code `G` outputs `H (encode (w G (k + 1)))` on `k`.
  obtain ⟨G, hG⟩ := Code.fixed_point₂ (f := fun c k => Part.some (H (encode (w c (k + 1)))))
    (hH.comp (Computable.encode.comp (hw.comp Computable.fst
      (Computable.succ.comp Computable.snd)))).partrec.to₂
  let e : ℕ → ℕ := fun k => encode (w G k)
  have heval (k : ℕ) : H (e (k + 1)) + 1 ∈ (w G k).eval 0 :=
    Part.mem_bind (Part.mem_bind (by rw [Code.eval_const]; exact Part.mem_some k)
      (by rw [hG]; exact Part.mem_some _)) (Part.mem_some _)
  have hke (k : ℕ) : k < e k :=
    (le_encode_const k).trans_lt <| (Code.encode_lt_comp _ _).2.trans (Code.encode_lt_comp _ _).2
  refine eventually_atTop.2 ⟨e 0, fun n hn => ?_⟩
  -- Choose `k` with `e k ≤ n < e (k + 1)`.
  have hex : ∃ k, n < e (k + 1) := ⟨n, (Nat.lt_succ_self n).trans (hke (n + 1))⟩
  set k := Nat.find hex with hk
  have hnk : n < e (k + 1) := Nat.find_spec hex
  have hkn : e k ≤ n := by
    cases hk' : k with
    | zero => exact hn
    | succ j => exact not_lt.1 (Nat.find_min hex (by omega : j < k))
  have hfn : f n < H (e (k + 1)) + 1 := Nat.lt_succ_of_le (hfH hnk)
  refine ⟨hfn.trans_le ((le_bbOutput le_rfl (heval k)).trans (monotone_bbOutput hkn)), ?_⟩
  obtain ⟨K, hK⟩ := exists_mem_evalnFuel (heval k)
  exact hfn.trans_le ((le_of_mem_evalnFuel_comp_succ (heval k) hK).trans
    ((le_bbFuel le_rfl hK).trans (monotone_bbFuel hkn)))

/-- **Radó's theorem** for partial recursive codes [Rado1962] [Aaronson2020]: every computable
function is eventually below `bbOutput`. -/
theorem eventually_lt_bbOutput {f : ℕ → ℕ} (hf : Computable f) :
    ∀ᶠ n in atTop, f n < bbOutput n :=
  (eventually_lt_bbOutput_and_bbFuel hf).mono fun _ h => h.1

/-- **Radó's theorem** for the fuel version [Rado1962]: every computable function is eventually
below `bbFuel`. -/
theorem eventually_lt_bbFuel {f : ℕ → ℕ} (hf : Computable f) :
    ∀ᶠ n in atTop, f n < bbFuel n :=
  (eventually_lt_bbOutput_and_bbFuel hf).mono fun _ h => h.2

/-- Domination survives any reindexing `σ` of sizes with `n ≤ σ n`, computable or not. For
`σ ℓ = 2 ^ ℓ - 1` this is domination for the busy beaver function indexed by bit length. -/
theorem eventually_lt_bbOutput_comp {f : ℕ → ℕ} (hf : Computable f) {σ : ℕ → ℕ}
    (hσ : ∀ n, n ≤ σ n) : ∀ᶠ n in atTop, f n < bbOutput (σ n) :=
  (eventually_lt_bbOutput hf).mono fun n h => h.trans_le (monotone_bbOutput (hσ n))

/-- `bbOutput` is not computable [Rado1962]. -/
theorem not_computable_bbOutput : ¬ Computable bbOutput := fun h =>
  (eventually_lt_bbOutput h).exists.elim fun _ hn => lt_irrefl _ hn

/-- `bbFuel` is not computable [Rado1962]. -/
theorem not_computable_bbFuel : ¬ Computable bbFuel := fun h =>
  (eventually_lt_bbFuel h).exists.elim fun _ hn => lt_irrefl _ hn

/-- Fuel `bbFuel n` suffices for every halting code of size at most `n`: such a code halts on `0`
exactly when `evaln` succeeds with fuel `bbFuel n`. -/
theorem dom_eval_iff_isSome_evaln_bbFuel {n : ℕ} {c : Code} (hc : encode c ≤ n) :
    (c.eval 0).Dom ↔ (Code.evaln (bbFuel n) c 0).isSome := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Part.dom_iff_mem.1 ((dom_evalnFuel_iff c 0).2 h)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (mem_evalnFuel_iff.1 hk).1
    rw [Code.evaln_mono (le_bbFuel hc hk) hx]
    rfl
  · intro h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
    exact Part.dom_iff_mem.2 ⟨x, Code.evaln_sound hx⟩

/-- A computable upper bound on `bbFuel` decides whether a code halts on `0`. This is the
unrelativized corollary of [Aaronson, Proposition 1][Aaronson2020], which solves the halting
problem with oracle access to any upper bound. -/
theorem computablePred_dom_eval_of_bbFuel_le {g : ℕ → ℕ} (hg : Computable g)
    (hle : ∀ n, bbFuel n ≤ g n) : ComputablePred fun c : Code => (c.eval 0).Dom := by
  refine ComputablePred.computable_iff.2
    ⟨fun c => (Code.evaln (g (encode c)) c 0).isSome, ?_, funext fun c => propext ?_⟩
  · exact Primrec.option_isSome.to_comp.comp (Code.primrec_evaln.to_comp.comp
      (((hg.comp Computable.encode).pair Computable.id).pair (Computable.const 0)))
  · dsimp only
    constructor
    · intro h
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ((dom_eval_iff_isSome_evaln_bbFuel le_rfl).1 h)
      rw [Code.evaln_mono (hle _) hx]
      rfl
    · intro h
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
      exact Part.dom_iff_mem.2 ⟨x, Code.evaln_sound hx⟩

/-- No computable function bounds `bbFuel` from above, since it would decide the halting problem
(`ComputablePred.halting_problem`). This is a second proof that `bbFuel` is not computable. -/
theorem not_exists_computable_bbFuel_le :
    ¬ ∃ g : ℕ → ℕ, Computable g ∧ ∀ n, bbFuel n ≤ g n :=
  fun ⟨_, hg, hle⟩ =>
    ComputablePred.halting_problem 0 (computablePred_dom_eval_of_bbFuel_le hg hle)

private theorem encode_comp_succ_le (c : Code) :
    encode (Code.comp Code.succ c) ≤ 4 * encode c ^ 2 + 14 := by
  simp only [Code.encodeCode_eq, Code.encodeCode]
  have : Nat.pair 1 c.encodeCode ≤ c.encodeCode ^ 2 + 2 := by
    unfold Nat.pair
    split_ifs <;> nlinarith
  linarith

/-- The fuel version outgrows the output version, up to the size overhead `4 * n ^ 2 + 14` of
composing a code with `succ`. -/
theorem bbOutput_lt_bbFuel (n : ℕ) : bbOutput n < bbFuel (4 * n ^ 2 + 14) := by
  obtain ⟨c, hc, hx⟩ := exists_mem_eval_bbOutput n
  have hx' : bbOutput n + 1 ∈ (Code.comp Code.succ c).eval 0 :=
    Part.mem_bind hx (Part.mem_some _)
  obtain ⟨K, hK⟩ := exists_mem_evalnFuel hx'
  refine Nat.lt_of_succ_le ((le_of_mem_evalnFuel_comp_succ hx' hK).trans
    ((le_bbFuel le_rfl hK).trans (monotone_bbFuel ?_)))
  exact (encode_comp_succ_le c).trans (by gcongr)

private theorem strictMono_encode_const : StrictMono fun k => encode (Code.const k) :=
  strictMono_nat_of_lt_succ fun _ => (Code.encode_lt_comp _ _).2

private theorem strictMono_encode_curry (d : Code) :
    StrictMono fun k => encode (Code.curry d k) := by
  intro a b hab
  have h1 := strictMono_encode_const hab
  simp only [Code.curry, Code.encodeCode_eq, Code.encodeCode] at h1 ⊢
  have h2 := Nat.pair_lt_pair_left (Code.encodeCode Code.id) h1
  have h3 := Nat.pair_lt_pair_right d.encodeCode
    (show 2 * (2 * Nat.pair (Code.const a).encodeCode Code.id.encodeCode) + 4 <
      2 * (2 * Nat.pair (Code.const b).encodeCode Code.id.encodeCode) + 4 by omega)
  omega

/-- A family of codes `t c` that output the fuel of `c` on `0`, with sizes bounded by a computable
function of the size of `c`. -/
private theorem exists_code_evalnFuel :
    ∃ t : Code → Code, (∀ c, (t c).eval 0 = evalnFuel c 0) ∧
      ∃ h : ℕ → ℕ, Computable h ∧ ∀ n c, encode c ≤ n → encode (t c) ≤ h n := by
  have hp : Nat.Partrec fun p : ℕ => evalnFuel (ofNat Code p.unpair.1) 0 :=
    Partrec.nat_iff.1 (fuelMeasure.partrec_cost.comp
      ((Computable.ofNat Code).comp (Computable.fst.comp Computable.unpair))
      (Computable.const 0))
  obtain ⟨d, hd⟩ := Code.exists_code.1 hp
  refine ⟨fun c => Code.curry d (encode c), fun c => ?_, fun n => encode (Code.curry d n), ?_,
    fun n c hc => (strictMono_encode_curry d).monotone hc⟩
  · rw [Code.eval_curry, hd]
    simp only [Nat.unpair_pair, ofNat_encode]
  · exact Computable.encode.comp
      (Code.primrec₂_curry.to_comp.comp (Computable.const d) Computable.id)

/-- `bbFuel` is bounded by `bbOutput` after a computable change of size: the fuel of a code is
the output of another code, of computably bounded size. -/
theorem exists_computable_bbFuel_le_bbOutput :
    ∃ h : ℕ → ℕ, Computable h ∧ ∀ n, bbFuel n ≤ bbOutput (h n) := by
  obtain ⟨t, ht, h, hh, hle⟩ := exists_code_evalnFuel
  refine ⟨h, hh, fun n => ?_⟩
  obtain ⟨c, hc, hk⟩ := exists_mem_evalnFuel_bbFuel n
  exact le_bbOutput (hle n c hc) (by rw [ht]; exact hk)

/-- A computable upper bound on `bbOutput` decides whether a code halts on `0`, through
`exists_computable_bbFuel_le_bbOutput` and `computablePred_dom_eval_of_bbFuel_le`. -/
theorem computablePred_dom_eval_of_bbOutput_le {g : ℕ → ℕ} (hg : Computable g)
    (hle : ∀ n, bbOutput n ≤ g n) : ComputablePred fun c : Code => (c.eval 0).Dom := by
  obtain ⟨h, hh, hsteps⟩ := exists_computable_bbFuel_le_bbOutput
  exact computablePred_dom_eval_of_bbFuel_le (hg.comp hh) fun n => (hsteps n).trans (hle _)

/-- No computable function bounds `bbOutput` from above, since it would decide the halting problem.
This is a second proof that `bbOutput` is not computable. -/
theorem not_exists_computable_bbOutput_le :
    ¬ ∃ g : ℕ → ℕ, Computable g ∧ ∀ n, bbOutput n ≤ g n :=
  fun ⟨_, hg, hle⟩ =>
    ComputablePred.halting_problem 0 (computablePred_dom_eval_of_bbOutput_le hg hle)

end Cslib.BusyBeaver
